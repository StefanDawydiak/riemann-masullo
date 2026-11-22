module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # Trace formula: the Main Theorem

Masullo, §12.5, pp. 519–520. Zeros of the completed Hecke L-functions are listed
through a norm section, as in Theorem B.4.4.7: a quasi-character c = χ|·|^s with
χ trivial on the section has abscissa σ(c) = Re s.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " c ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val c
local notation "twist(" χ ", " s ")" => ideleClassNormTwist (F := F) χ s
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "interiorZeros(" τ ", " α ")" =>
  {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ |z.2.re - 1 / 2| < α}
local notation "zeroTerm(" φ ", " z ")" =>
  ((ord((z).val.1.val, (z).val.2) : ℤ) : ℂ) * M(φ, twist((z).val.1.val, (z).val.2 - 1 / 2))
local notation "classVolume" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) / finiteVolume(v) : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 b

-- TODO(paper-gap): The proof on p. 520 lets S contain the places at which "the
-- character χ" ramifies. No character occurs in the statement of Theorem 12.5.1.1.

-- TODO(paper-gap): The introduction on p. 519 assumes φ(1) = 0, the statement
-- assumes φ(C_F¹) = 0. The Lean below follows the statement.

-- TODO(paper-gap): The proof on p. 520 identifies the S-part of the global diagonal
-- with Theorem 12.4.1.1. That needs the missing §12.3 comparison (ERRATA M25),
-- drops the factor 1/μ̄_{S,1}(J¹_{F,S}) of that theorem (ERRATA R4), and asserts
-- without computation that the result is the left side less the two pole terms.
-- It also uses Theorem 11.3.2.1 for every prime outside S (ERRATA I292).

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Let φ be a compactly supported Bruhat test
on C_F that vanishes on C_F¹, and let α > 0. Restrict φ to each local multiplicative
group. Then μ̄(C_F¹) times the sum of the local principal values of (12.5.1.1)–(12.5.1.2)
equals M(φ)(|·|^{1/2}) + M(φ)(|·|^{−1/2}) minus the sum of N(c)·M(φ)(c|·|^{−1/2})
over the zeros c of the completed Hecke L-function with |σ(c) − 1/2| < α.
The finite-place series and the zero series converge.
Deviation: The interval I, free in the statement, is [−α, α] as in the proof, and
α > 0. For α = 0 the identity is false (`Printed.traceFormula_false`). The left
side is multiplied by μ̄(C_F¹), the factor that the proof drops from Theorem
12.4.1.1 (ERRATA R4); `idelicExplicitFormula` has the same normalization. A norm
section lists each quasi-character c = χ|·|^s once, N(c) is the order of the
completed L-function of χ at s, and c|·|^{−1/2} = χ|·|^{s−1/2}. The archimedean
principal values of Appendix B.4 already contain the factors 1/2 and 1/(2π). -/
theorem traceFormula (τ : ℝ≥0ˣ →ₜ* C𝔽) (_hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0) {α : ℝ} (_hα : 0 < α) :
    ∃ (a : archTest) (b : finiteTest),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ), (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : V) (u : (v.adicCompletion F)ˣ), (b v).val u = φ.val (finiteClass(v) u)) ∧
      Summable (fun v : V ↦ finiteTerm(v, b v)) ∧
      HasSum (fun z : interiorZeros(τ, α) ↦ zeroTerm(φ, z))
        (M(φ, twist(1, 1 / 2)) + M(φ, twist(1, -1 / 2)) -
          classVolume * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
            ∑' v : V, finiteTerm(v, b v))) := by sorry

-- With `idelicExplicitFormula`, the case of every α > 0 says that the zeros with
-- |σ(c) − 1/2| ≥ α contribute nothing to the zero sum of any test vanishing on C_F¹.
-- Chapter 13 means to deduce the location of the zeros from it.

section SmoothenedDiagonal

local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs₁(hs)))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripTensorExists(" hα ", " hs ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K =
    (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs₀(hs) φ).comp
      (spectralProjection (F := F) (1 / 2) hα hs₀(hs)))

-- TODO(paper-gap): (12.5.1.4) is justified "by design of the global geometric kernel"
-- and Theorem 10.4.2.8. That theorem compares cutoff traces. It says nothing about
-- the diagonal of the smoothened strip kernel in the order A(φ)∘P (ERRATA I341, I351).
-- Theorem 10.3.2.1 also counts the zeros on the lines σ = 1/2 ± α, with truncated
-- multiplicity, while (12.5.1.4) keeps only the interior zeros.

/-- Paper: (12.5.1.4), p. 520. Let φ vanish on C_F¹, let α > 0 and s ≥ 3, and assume
the strip kernel of Definition 10.4.3.7 exists at twist 1/2. Smoothen the global
geometric kernel along a Borel D′-sequence. Its diagonal is Haar-integrable, and the
integral is minus the sum of N(c)·M(φ)(c|·|^{−1/2}) over the zeros with |σ(c) − 1/2| < α.
Deviation: α > 0 as in `traceFormula`. At α = 0 the interior is empty, while Theorems
10.3.2.1 and 12.1.1.2(1) would give minus the sum over the zeros on the critical line,
with truncated multiplicity. The kernel is `globalStripGeometricKernel`, which
requires the tensor. -/
theorem integral_smoothenedStripGeometricKernel_diagonal (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ g : C₁, φ.val g = 0) {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s)
    (hK : stripTensorExists(hα.le, hs, φ))
    (U : ℕ → Set C𝔽) (_hU : IsDPrimeSequence μ𝔽 U) (_hBorel : ∀ n, MeasurableSet (U n)) :
    let k := dSequenceKernelSmoothening μ𝔽 U
      (globalStripGeometricKernel (F := F) (1 / 2) hα.le hs₁(hs) φ hK)
    Integrable (fun x ↦ k (x, x)) μ𝔽 ∧
      HasSum (fun z : interiorZeros(τ, α) ↦ zeroTerm(φ, z)) (-∫ x, k (x, x) ∂μ𝔽) := by sorry

end SmoothenedDiagonal

end RiemannMasullo
