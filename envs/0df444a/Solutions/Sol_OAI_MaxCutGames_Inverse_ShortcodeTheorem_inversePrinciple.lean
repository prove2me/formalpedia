-- Prove2me | solution 1 for OAI.MaxCutGames.Inverse.ShortcodeTheorem.inversePrinciple
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:05:30.243227+00:00
-- url     : https://prove2.me/submissions/b2b82b26-1c40-45a6-afb3-4d90ec413e53

import Mathlib
import Definitions.Def_OAIQ087A032
import Theorems.Thm_OAI_MaxCutGames_Inverse_KMSMomentTheorem_lifted_fourth_moment_bound

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixCharacters
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace characters on actual finite binary matrix spaces. -/

noncomputable section

namespace MaxCutGames.Fourier.MatrixCharacters

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem linearTracePair_add_right (X : E →ₗ[F2] F) (S T : F →ₗ[F2] E) :
    linearTracePair X (S + T) = linearTracePair X S + linearTracePair X T := by
  simp [linearTracePair, LinearMap.comp_add]

theorem linearTraceCharacter_add (S T : F →ₗ[F2] E) :
    linearTraceCharacter (S + T) = linearTraceCharacter S + linearTraceCharacter T := by
  ext X
  simp only [linearTraceCharacter_apply, linearTracePair_add_right, binarySign_add,
    AddChar.add_apply]

end MaxCutGames.Fourier.MatrixCharacters
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixFourier
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace MaxCutGames.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open MaxCutGames.Fourier.MatrixCharacters

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [Fintype (F →ₗ[F2] E)] in
theorem linear_complexCoeff_character (S T : F →ₗ[F2] E) :
    fourierCoeff (linearTraceCharacter S : (E →ₗ[F2] F) → ℂ)
      (linearTraceCharacter T) = if T = S then 1 else 0 := by
  classical
  simp only [fourierCoeff, linearTraceCharacter_star, ← AddChar.add_apply,
    ← linearTraceCharacter_add, Fintype.expect_eq_sum_div_card,
    sum_linearTraceCharacter, linearMap_add_eq_zero_iff]
  by_cases h : S = T
  · subst T
    simp
  · simp [h, Ne.symm h]

theorem linear_fourier_inversion (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re = f X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          fourierCoeff (fun Y => (f Y : ℂ)) (linearTraceCharacter S) *
            linearTraceCharacter S X := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E,
        linearCoeff f S * (linearTraceCharacter S X).re) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      change ((linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) = _
      rw [Complex.ofReal_mul, linearCoeff_complex, linearTraceCharacter_real]
    _ = (f X : ℂ) := linear_complex_inversion _ X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_sum {J : Type*} (s : Finset J)
    (f : J → (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (∑ j ∈ s, f j) S = ∑ j ∈ s, linearCoeff (f j) S := by
  simp only [linearCoeff, Finset.sum_apply, Finset.sum_mul]
  exact Finset.expect_sum_comm _ _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_smul (c : ℝ) (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (c • f) S = c * linearCoeff f S := by
  simp only [linearCoeff, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact Finset.mul_expect _ _ _ |>.symm

omit [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_character (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => (linearTraceCharacter S X).re) T =
      if T = S then 1 else 0 := by
  classical
  apply Complex.ofReal_injective
  rw [linearCoeff_complex]
  simp only [linearTraceCharacter_real, linear_complexCoeff_character]
  split_ifs <;> simp

end MaxCutGames.Fourier.MatrixFourier
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_MatrixParity
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual binary matrix and linear-map parity used in Lemma 5.3. -/

noncomputable section

namespace MaxCutGames.Fourier.MatrixParity

open MaxCutGames.Integration.BinaryLinear
open scoped Matrix BigOperators Classical

section LinearMaps

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

/-- Generic trace pairing of a rank-one color shift. -/
theorem trace_smulRight_comp [FiniteDimensional F2 C]
    (τ : E →ₗ[F2] F2) (c : C) (S : C →ₗ[F2] E) :
    LinearMap.trace F2 C ((τ.smulRight c).comp S) = τ (S c) := by
  have heq : (τ.smulRight c).comp S = (τ.comp S).smulRight c := by
    ext x
    rfl
  rw [heq, LinearMap.trace_smulRight, LinearMap.comp_apply]

end LinearMaps

open MatrixCharacters hiding F2

end MaxCutGames.Fourier.MatrixParity
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixNoise
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rank-one averaging operator on finite binary matrix spaces.
The outer weights describe any finite law for `v`; the functional `ℓ` is
uniform. Normalization is needed for eigenvalue bounds, not diagonalization. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace MaxCutGames.Fourier.MatrixNoise

open scoped BigOperators Matrix
open MaxCutGames.Integration.BinaryLinear (Vector)
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem evaluationCharacter_eq_zero_iff (w : E) :
    evaluationCharacter w = 0 ↔ w = 0 := by
  constructor
  · intro h
    apply (Module.forall_dual_apply_eq_zero_iff F2 w).mp
    intro ℓ
    apply binarySign_injective
    have hx := congrArg (fun ψ : AddChar (E →ₗ[F2] F2) ℂ => ψ ℓ) h
    simpa using hx
  · rintro rfl
    ext ℓ
    simp

theorem average_evaluationCharacter [Fintype (E →ₗ[F2] F2)] (w : E) :
    (𝔼 ℓ : E →ₗ[F2] F2, binarySign (ℓ w)) =
      if w = 0 then (1 : ℂ) else 0 := by
  classical
  change (𝔼 ℓ, evaluationCharacter w ℓ) = _
  rw [Fintype.expect_eq_sum_div_card, AddChar.sum_eq_ite]
  simp only [evaluationCharacter_eq_zero_iff]
  split_ifs <;> simp

/-- Basis-independent uniform-functional cancellation in Lemma 5.1. -/
theorem average_smulRight_character [FiniteDimensional F2 F]
    [Fintype (E →ₗ[F2] F2)] (S : F →ₗ[F2] E) (v : F) :
    (𝔼 ℓ : E →ₗ[F2] F2, linearTraceCharacter S (ℓ.smulRight v)) =
      if S v = 0 then (1 : ℂ) else 0 := by
  simp only [linearTraceCharacter_apply, linearTracePair,
    MatrixParity.trace_smulRight_comp]
  exact average_evaluationCharacter _

/-- Equation (5.3), without a choice of bases. -/
theorem linearNoiseOperator_character [FiniteDimensional F2 F]
    [Fintype F] [Fintype (E →ₗ[F2] F2)] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearNoiseOperator weight (linearTraceCharacter S) X =
      (linearNoiseEigenvalue weight S : ℂ) * linearTraceCharacter S X := by
  classical
  unfold linearNoiseOperator linearNoiseEigenvalue
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_expect, average_smulRight_character]
  change _ = Complex.ofRealHom (∑ v, weight v * if S v = 0 then 1 else 0) * _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp [mul_comm]

theorem linearRealNoiseOperator_complex [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    (linearRealNoiseOperator weight f X : ℂ) =
      linearNoiseOperator weight (fun Y => (f Y : ℂ)) X := by
  unfold linearRealNoiseOperator linearNoiseOperator
  change Complex.ofRealHom (∑ v, weight v * _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  change ((weight v * (𝔼 ℓ : E →ₗ[F2] F2, f (X + ℓ.smulRight v)) : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul, complex_ofReal_expect]

theorem linearRealNoiseOperator_sum [Fintype F] [Fintype (E →ₗ[F2] F2)]
    {I : Type*} [Fintype I] (weight : F → ℝ)
    (f : I → (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight (fun Y => ∑ i, f i Y) X =
      ∑ i, linearRealNoiseOperator weight (f i) X := by
  unfold linearRealNoiseOperator
  simp_rw [Finset.expect_sum_comm, Finset.mul_sum]
  exact Finset.sum_comm

theorem linearRealNoiseOperator_smul [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (c : ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight (fun Y => c * f Y) X =
      c * linearRealNoiseOperator weight f X := by
  unfold linearRealNoiseOperator
  simp_rw [← Finset.mul_expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ac_rfl

theorem linearRealNoiseOperator_character [FiniteDimensional F2 F]
    [Fintype F] [Fintype (E →ₗ[F2] F2)] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight (fun Y => (linearTraceCharacter S Y).re) X =
      linearNoiseEigenvalue weight S * (linearTraceCharacter S X).re := by
  apply Complex.ofReal_injective
  rw [linearRealNoiseOperator_complex]
  simpa only [Complex.ofReal_mul, linearTraceCharacter_real] using
    (linearNoiseOperator_character weight S X)

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Fourier expansion of the actual noise operator on every real function. -/
theorem linearRealNoiseOperator_expansion (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight f X =
      ∑ S : F →ₗ[F2] E, linearNoiseEigenvalue weight S * linearCoeff f S *
        (linearTraceCharacter S X).re := by
  classical
  calc
    linearRealNoiseOperator weight f X = linearRealNoiseOperator weight
        (fun Y => ∑ S : F →ₗ[F2] E,
          linearCoeff f S * (linearTraceCharacter S Y).re) X := by
      congr 1
      funext Y
      exact (linear_fourier_inversion f Y).symm
    _ = ∑ S : F →ₗ[F2] E,
        linearCoeff f S * linearRealNoiseOperator weight
          (fun Y => (linearTraceCharacter S Y).re) X := by
      rw [linearRealNoiseOperator_sum]
      simp_rw [linearRealNoiseOperator_smul]
    _ = _ := by
      simp_rw [linearRealNoiseOperator_character]
      apply Finset.sum_congr rfl
      intro S _
      ac_rfl

/-- Exact spectral pairing identity for the actual operator. -/
theorem linearRealNoiseOperator_pairing (weight : F → ℝ)
    (f g : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * linearRealNoiseOperator weight g X) =
      ∑ S : F →ₗ[F2] E,
        linearNoiseEigenvalue weight S * linearCoeff f S * linearCoeff g S := by
  simp_rw [linearRealNoiseOperator_expansion, Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  calc
    (𝔼 X, f X * (linearNoiseEigenvalue weight S * linearCoeff g S *
        (linearTraceCharacter S X).re)) =
        linearNoiseEigenvalue weight S * linearCoeff g S *
          (𝔼 X, f X * (linearTraceCharacter S X).re) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro X _
      ac_rfl
    _ = _ := by unfold linearCoeff; ring

/-- The actual operator's quadratic form is precisely its weighted Fourier mass. -/
theorem linearRealNoiseOperator_energy (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * linearRealNoiseOperator weight f X) =
      ∑ S : F →ₗ[F2] E, linearNoiseEigenvalue weight S * linearCoeff f S ^ 2 := by
  rw [linearRealNoiseOperator_pairing]
  simp only [pow_two, mul_assoc]

end MaxCutGames.Fourier.MatrixNoise
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_PartnerProjection
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite cardinality of the concrete projection kernel. This packages the explicit
bit parametrization of Lemma 6.1 as a genuine equivalence, then counts its points.
No vector-space dimension formula is assumed.
-/

/-!
# Exact kernel counts for binary linear maps

The last paragraph of Theorem 3.4 uses the fact that a uniform vector in a
binary vector space lands in the kernel of a rank-k map with probability
2⁻ᵏ. These theorems prove its exact integer-count form from mathlib's
rank-nullity and finite-vector-space cardinality theorems. The target space
does not have to be finite, and no injectivity of any factor map is assumed.
-/

namespace MaxCutGames.Gadget.LinearKernelCount

universe u v

variable {V : Type u} {P : Type v}
variable [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable [AddCommGroup P] [Module (ZMod 2) P]

/-- A finite-dimensional binary vector space has `2^dimension` vectors. -/
theorem card_binary_space : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp

/-- Exact cross-multiplied uniform kernel probability: `|ker f| * 2^rank f = |V|`. -/
theorem kernel_card_mul_pow_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card f.ker * 2 ^ Module.finrank (ZMod 2) f.range = Nat.card V := by
  rw [card_binary_space (V := f.ker), card_binary_space (V := V), ← pow_add]
  congr 1
  rw [Nat.add_comm]
  exact f.finrank_range_add_finrank_ker

/-- The kernel formula expressed directly as the cardinality of the zero event. -/
theorem zero_event_card_mul_pow_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card {x : V // f x = 0} * 2 ^ Module.finrank (ZMod 2) f.range = Nat.card V :=
  kernel_card_mul_pow_rank f

/-- The same exact probability identity for a direct count over a finite universe. -/
theorem zero_event_finset_count_mul_pow_rank [Fintype V] [DecidableEq P]
    (f : V →ₗ[ZMod 2] P) :
    (Finset.univ.filter (fun x : V => f x = 0)).card *
      2 ^ Module.finrank (ZMod 2) f.range = Fintype.card V := by
  have h := zero_event_card_mul_pow_rank f
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

end MaxCutGames.Gadget.LinearKernelCount

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_PositiveMultiplier
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier
open MatrixCharacters MatrixFourier MatrixNoise MatrixEnergy

namespace MaxCutGames.Decoder.PositiveMultiplier

section UniformSubspace

variable {K V E : Type*}
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K] [Fintype K]
  [AddCommGroup V] [Module F2 V] [Fintype V]
  [AddCommGroup E] [Module F2 E]

omit [FiniteDimensional F2 K] in
theorem subspaceLaw_sum (ι : K →ₗ[F2] V) (f : V → ℝ) :
    (∑ v, subspaceLaw ι v * f v) = (Fintype.card K : ℝ)⁻¹ * ∑ k, f (ι k) := by
  classical
  unfold subspaceLaw
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  exact (Finset.mul_sum _ _ _).symm

theorem subspaceLaw_eigenvalue (ι : K →ₗ[F2] V) (S : V →ₗ[F2] E) :
    linearNoiseEigenvalue (subspaceLaw ι) S =
      ((2 : ℝ) ^ Module.finrank F2 (S.comp ι).range)⁻¹ := by
  classical
  let k := (Finset.univ.filter fun x : K => S (ι x) = 0).card
  have hs : (∑ x : K, if S (ι x) = 0 then (1 : ℝ) else 0) = (k : ℝ) := by
    rw [← Finset.sum_filter]
    simp [k]
  have hc : (k : ℝ) * (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range =
      (Fintype.card K : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (MaxCutGames.Gadget.LinearKernelCount.zero_event_finset_count_mul_pow_rank (S.comp ι))
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, LinearMap.comp_apply] using h
  have hn : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range ≠ 0 := pow_ne_zero _ two_ne_zero
  unfold linearNoiseEigenvalue
  rw [subspaceLaw_sum, hs]
  apply mul_right_cancel₀ hp
  calc
    ((Fintype.card K : ℝ)⁻¹ * (k : ℝ)) * (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range =
        (Fintype.card K : ℝ)⁻¹ * ((k : ℝ) * (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range) :=
      mul_assoc _ _ _
    _ = (Fintype.card K : ℝ)⁻¹ * (Fintype.card K : ℝ) := by rw [hc]
    _ = 1 := inv_mul_cancel₀ hn
    _ = ((2 : ℝ) ^ Module.finrank F2 (S.comp ι).range)⁻¹ *
        (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range := (inv_mul_cancel₀ hp).symm

end UniformSubspace

end MaxCutGames.Decoder.PositiveMultiplier
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Derivatives
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Actual Hybrid derivative energy in product coordinates

Parseval and affine restriction merge the selected Fourier coefficients over
each actual compressed frequency. For a product splitting, explicit linear
equivalences identify the quotient by the first factor with the second factor,
and the first-factor subspace with its original space. Reindexing the frequency
sum therefore introduces no multiplicity or normalization factor.
-/

/-!
# Actual Fourier components for the KMS analytic argument

All coefficients use normalized expectation on the primal matrix space; sums
over frequencies are unnormalized. These identities use only the common
trace-character Fourier identities.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter)
open MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

@[simp] theorem coeff_synthesis (a : (F →ₗ[F2] E) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (synthesis a) T = a T := by
  unfold synthesis
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

/-- Exact squared norm, used for every restricted KMS component. -/
theorem synthesis_energy (a : (F →ₗ[F2] E) → ℝ) :
    (𝔼 X, synthesis a X ^ 2) = ∑ T, a T ^ 2 := by
  rw [← linear_parseval]
  simp

@[simp] theorem coeff_component (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (component P f) T = if P T then linearCoeff f T else 0 := by
  exact coeff_synthesis _ _

theorem component_energy (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X ^ 2) = ∑ T with P T, linearCoeff f T ^ 2 := by
  rw [component, synthesis_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

theorem component_inner_self (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X * f X) = 𝔼 X, component P f X ^ 2 := by
  rw [← linear_parseval_inner, component_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  rw [coeff_component]
  split_ifs <;> simp [pow_two]

theorem rankComponent_energy (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankComponent i f X ^ 2) =
      ∑ T with Module.finrank F2 T.range = i, linearCoeff f T ^ 2 := by
  unfold rankComponent
  rw [component_energy]
  apply Finset.sum_congr
  · ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro T _
    rfl

end MaxCutGames.Inverse.KMSAnalytic

/-!
# Exact rank support of actual hybrid derivatives

The actual Hybrid selector loses exactly `dim A + codim B` in rank.
Consequently a pure rank component has derivative coefficients supported at
that exact remaining rank. Orders above the original rank give zero.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticHybridEnergyImageSplit
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Partition frequencies by their actual image

A map with image `W` is uniquely a surjection onto `W`, followed by the
subspace inclusion. Consequently a sum over rank-`q` frequencies splits
exactly over dimension-`q` image subspaces and surjections onto each image.
The identities hold for arbitrary real weights and use no analytic estimate.
-/

/-!
# The actual hybrid selector in compressed-fiber coordinates

When the prescribed compression is onto `W`, the hybrid image and preimage
conditions are equivalent to injectivity of the complementary target map
and surjectivity of the remaining coordinate map. These are conditions on
the actual assembled linear map, with no rank or analytic hypothesis.
-/

/-! The exact injection/surjection factorization of the adapted coordinates. -/

/-! The actual hybrid compressed fiber, with no coordinate multiplicity. -/

/-!
# The actual small-space Fourier component

An injection from the small domain into the large domain lifts dual
frequencies by composition. Only surjective small-space frequencies are
retained. The identities below use the actual trace-character coefficients
and normalized primal expectation; no fourth-moment estimate is assumed.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
@[simp] theorem coeff_smallComponent (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (smallComponent ι f) T = smallCoeff ι f T :=
  coeff_synthesis _ _

end
end MaxCutGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSMomentConstants
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit dimension-independent constants for the new KMS mixed-energy
argument and the generic A5 aggregation. The eventual expansion theorem only
uses positivity and finiteness of these constants, so no rank cutoff exception
or comparison with an earlier rank-level constant is needed. -/

namespace MaxCutGames.Inverse.KMSMomentConstants
noncomputable section
open KMSFourthMoment

theorem fourthMomentConstant_pos (r : ℕ) : 0 < fourthMomentConstant r := by
  unfold fourthMomentConstant
  positivity

theorem fourthMomentConstant_nonneg (r : ℕ) : 0 ≤ fourthMomentConstant r :=
  (fourthMomentConstant_pos r).le

end
end MaxCutGames.Inverse.KMSMomentConstants

namespace MaxCutGames.Inverse.KMS

noncomputable section
open scoped BigOperators Classical

section FiniteDensity

variable {Ω : Type*} [DecidableEq Ω]

/-- Restricting the denominator to a chart containing the set preserves the
numerator. This is the exact finite-set step used after Grassmann expansion. -/
theorem inter_chart_eq (S I C : Finset Ω) (hSC : S ⊆ C) :
    S ∩ (I ∩ C) = S ∩ I := by
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hS, hI, _⟩
    exact ⟨hS, hI⟩
  · rintro ⟨hS, hI⟩
    exact ⟨hS, hI, hSC hS⟩

/-- A nonempty part of the set in an interval witnesses that the chart and
interval meet. No positive denominator is silently assumed. -/
theorem chart_inter_nonempty (S I C : Finset Ω) (hSC : S ⊆ C)
    (hSI : (S ∩ I).Nonempty) : (I ∩ C).Nonempty := by
  obtain ⟨x, hx⟩ := hSI
  exact ⟨x, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hx).2, hSC (Finset.mem_inter.mp hx).1⟩⟩

/-- Intersecting a nonempty conditioning interval with a chart containing the
set can only increase its relative density. -/
theorem relativeDensity_le_chart (S I C : Finset Ω) (hSC : S ⊆ C)
    (hIC : (I ∩ C).Nonempty) :
    relativeDensity S I ≤ relativeDensity S (I ∩ C) := by
  unfold relativeDensity
  rw [inter_chart_eq S I C hSC]
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
  · exact Nat.cast_pos.mpr (Finset.card_pos.mpr hIC)
  · exact Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)

/-- The quantitative density conclusion passes to the matrix chart without
losing any factor. -/
theorem density_bound_passes_to_chart (S I C : Finset Ω) (hSC : S ⊆ C)
    (hSI : (S ∩ I).Nonempty) {α : ℝ} (hα : α ≤ relativeDensity S I) :
    (I ∩ C).Nonempty ∧ α ≤ relativeDensity S (I ∩ C) := by
  have hIC := chart_inter_nonempty S I C hSC hSI
  exact ⟨hIC, hα.trans (relativeDensity_le_chart S I C hSC hIC)⟩

end FiniteDensity

end
end MaxCutGames.Inverse.KMS

/-!
# The ordered-basis lift of a Grassmann set

The ambient sample space contains every linear map, including singular maps.
The lift accepts exactly maps whose range is one of the specified
`ell`-dimensional subspaces. Thus dependence is rejected, rather than silently
conditioning the ambient uniform distribution on independence.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

theorem liftedIndicator_nonneg {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : 0 ≤ liftedIndicator S X := by
  unfold liftedIndicator
  split <;> norm_num

theorem liftedIndicator_le_one {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : liftedIndicator S X ≤ 1 := by
  unfold liftedIndicator
  split <;> norm_num

end
end MaxCutGames.Inverse.KMSBasisComparison

/-! Exact finite counting for the restricted-basis lift.  In particular, failed
independent completions contribute zero rather than an additive error. -/

namespace MaxCutGames.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Decompose a finite domain by its exact fibers. -/
theorem nat_card_eq_sum_fibers (f : X → Y) :
    Nat.card X = ∑ y : Y, Nat.card {x : X // f x = y} := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]

/-- The event count is the sum of the same fibers over the event. -/
theorem nat_card_event_eq_sum_fibers (f : X → Y) (p : Y → Prop) :
    Nat.card {x : X // p (f x)} =
      ∑ y : {y : Y // p y}, Nat.card {x : X // f x = y.val} := by
  let e : (Σ y : {y : Y // p y}, {x : X // f x = y.val}) ≃
      {x : X // p (f x)} :=
    { toFun := fun a => ⟨a.2.val, a.2.property.symm ▸ a.1.property⟩
      invFun := fun a => ⟨⟨f a.val, a.property⟩, ⟨a.val, rfl⟩⟩
      left_inv := by rintro ⟨⟨y, hy⟩, ⟨x, hx⟩⟩; cases hx; rfl
      right_inv := by intro a; rfl }
  rw [← Nat.card_congr e, Nat.card_sigma]

/-- Constant fibers give an exact density identity, including an empty target.
The nonzero fiber size is established geometrically for restricted bases. -/
theorem uniformFiber_card_ratio (f : X → Y) (p : Y → Prop)
    (c : ℕ) (hc : 0 < c)
    (hf : ∀ y, Nat.card {x : X // f x = y} = c) :
    (Nat.card {x : X // p (f x)} : ℝ) / Nat.card X =
      (Nat.card {y : Y // p y} : ℝ) / Nat.card Y := by
  have hX : Nat.card X = Nat.card Y * c := by
    rw [nat_card_eq_sum_fibers f]
    simp only [hf]
    simp [Nat.card_eq_fintype_card]
  have hE : Nat.card {x : X // p (f x)} = Nat.card {y : Y // p y} * c := by
    rw [nat_card_event_eq_sum_fibers f p]
    simp only [hf]
    simp [Nat.card_eq_fintype_card]
  rw [hE, hX, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (ne_of_gt (Nat.cast_pos.mpr hc))

/-- Sampling from a larger finite space and accepting only a subset never
increases the density of an event within that subset. Empty subsets are handled
explicitly, so this statement makes no hidden nonemptiness assumption. -/
theorem subtype_event_ratio_le {Z : Type*} [Fintype Z] (D : Z → Prop)
    (p : {z : Z // D z} → Prop) :
    (Nat.card {z : {z : Z // D z} // p z} : ℝ) / Nat.card Z ≤
      (Nat.card {z : {z : Z // D z} // p z} : ℝ) / Nat.card {z : Z // D z} := by
  by_cases hD : Nat.card {z : Z // D z} = 0
  · have hE : Nat.card {z : {z : Z // D z} // p z} = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← hD]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    rw [hE]
    simp
  · apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD)
    · exact Nat.cast_le.mpr
        (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

end

/-!
An independent frame inside `L` can be completed using vectors from `W` whenever
`L` lies in the sum of the frame's span and `W`.
-/

noncomputable section
open scoped Classical
open MaxCutGames.Inverse.KMS

/-- Restricted completion of an independent frame. The original vectors need
not belong to `W`; only the newly chosen vectors are required to do so. -/
theorem exists_restricted_completion {n q t : ℕ}
    (Q : Fin q → Ambient n) (W L : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q)
    (hQL : Submodule.span F2 (Set.range Q) ≤ L)
    (hLW : L ≤ Submodule.span F2 (Set.range Q) ⊔ W)
    (hL : Module.finrank F2 L = q + t) :
    ∃ z : Fin t → W,
      LinearIndependent F2 (Sum.elim Q (fun i => (z i : Ambient n))) ∧
        Submodule.span F2
          (Set.range (Sum.elim Q (fun i => (z i : Ambient n)))) = L := by
  classical
  let T : Set (Ambient n) := Set.range Q ∪ (W ⊓ L : Submodule F2 (Ambient n))
  have hQT : Set.range Q ⊆ T := Set.subset_union_left
  have hTspan : Submodule.span F2 T = L := by
    change Submodule.span F2
      (Set.range Q ∪ ((W ⊓ L : Submodule F2 (Ambient n)) : Set (Ambient n))) = L
    rw [Submodule.span_union, Submodule.span_eq,
      ← sup_inf_assoc_of_le W hQL, inf_eq_right.mpr hLW]
  obtain ⟨B, hBT, hQB, hTB, hB⟩ :=
    exists_linearIndepOn_id_extension hQ.linearIndepOn_id hQT
  have hBspan : Submodule.span F2 B = L := by
    rw [← hTspan]
    exact le_antisymm (Submodule.span_mono hBT) (Submodule.span_le.mpr hTB)
  let D : Set (Ambient n) := B \ Set.range Q
  let f : Fin q ⊕ D → Ambient n := Sum.elim Q Subtype.val
  have hf_inj : Function.Injective f := by
    apply Sum.elim_injective.mpr
    refine ⟨hQ.injective, Subtype.val_injective, ?_⟩
    intro i d hid
    exact d.property.2 ⟨i, hid⟩
  have hf_range : Set.range f = B := by
    ext x
    constructor
    · rintro ⟨i | d, rfl⟩
      · exact hQB (Set.mem_range_self i)
      · exact d.property.1
    · intro hx
      by_cases hxQ : x ∈ Set.range Q
      · obtain ⟨i, rfl⟩ := hxQ
        exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr ⟨x, hx, hxQ⟩, rfl⟩
  have hf : LinearIndependent F2 f := by
    apply (linearIndepOn_id_range_iff hf_inj).mp
    rw [hf_range]
    exact hB
  have hcard := finrank_span_eq_card hf
  rw [hf_range, hBspan, hL] at hcard
  have hDcard : Fintype.card D = t := by
    apply Nat.add_left_cancel (n := q)
    simpa using hcard.symm
  let e : Fin t ≃ D := (Fintype.equivFinOfCardEq hDcard).symm
  let z : Fin t → W := fun i =>
    ⟨(e i).val, ((hBT (e i).property.1).resolve_left (e i).property.2).1⟩
  let g : (Fin q ⊕ Fin t) ≃ (Fin q ⊕ D) := Equiv.sumCongr (Equiv.refl _) e
  have hz : Sum.elim Q (fun i => (z i : Ambient n)) = f ∘ g := by
    funext i
    cases i <;> rfl
  refine ⟨z, ?_, ?_⟩
  · rw [hz]
    exact hf.comp g g.injective
  · rw [hz, g.surjective.range_comp, hf_range, hBspan]

end

/-!
# Equal fibers for restricted basis completion

A fixed independent tuple may have vectors outside the restricting submodule.
Nevertheless, any two nonempty fibers of independent completions inside that
submodule are equivalent. The change of basis fixes the fixed tuple, and its
difference from the identity has image in the restricting submodule.
-/

noncomputable section
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {q t : ℕ}

variable {Q : Fin q → V} {W L M N : Submodule K V}

/-- Equal fiber cardinality follows from the explicit completion equivalence. -/
theorem restrictedCompletionCard_eq
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    Nat.card (RestrictedCompletion (t := t) Q W L) =
      Nat.card (RestrictedCompletion (t := t) Q W M) :=
  Nat.card_congr (restrictedCompletionEquiv x y)

end

/-!
# Restricted densities in the ordered-basis lift

The prefix vectors are arbitrary: they may be dependent, and they need not lie
in the subspace from which the remaining vectors are sampled. The relevant
Grassmann interval has lower endpoint `span Q` and upper endpoint `span Q ⊔ W`.
-/

noncomputable section
open scoped BigOperators Classical
open KMS

variable {n q t : ℕ}

theorem prefix_independent (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) : LinearIndependent F2 Q :=
  z.property.comp Sum.inl Sum.inl_injective

/-- The restriction's Grassmann interval satisfies the same total complexity
budget. This uses only `W ≤ span Q ⊔ W`, never the false assumption `Q ⊆ W`. -/
theorem interval_complexity_le (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q) :
    Module.finrank F2 (prefixSpan Q) +
      (n - Module.finrank F2 ↥(prefixSpan Q ⊔ W : Submodule F2 (Ambient n))) ≤
        q + (n - Module.finrank F2 W) := by
  have hA : Module.finrank F2 (prefixSpan Q) = q := by
    change Module.finrank F2 ↥(Submodule.span F2 (Set.range Q)) = q
    exact (finrank_span_eq_card hQ).trans (Fintype.card_fin q)
  have hW : Module.finrank F2 W ≤
      Module.finrank F2 ↥(prefixSpan Q ⊔ W : Submodule F2 (Ambient n)) :=
    Submodule.finrank_mono le_sup_right
  rw [hA]
  omega

theorem restrictedLiftDensity_eq_zero_of_dependent (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hQ : ¬ LinearIndependent F2 Q) : restrictedLiftDensity S Q W = 0 := by
  have hE : IsEmpty {z : Fin t → W // completionEvent S Q W z} := by
    refine ⟨fun z => ?_⟩
    obtain ⟨h, _⟩ := z.property
    exact hQ (prefix_independent Q W ⟨z.val, h⟩)
  let := hE
  simp [restrictedLiftDensity]

theorem interval_completion_nonempty (Q : Fin q → Ambient n)
    (W : Submodule F2 (Ambient n)) (hQ : LinearIndependent F2 Q)
    (L : IntervalVertex (t := t) Q W) :
    Nonempty (RestrictedCompletion (t := t) Q W L.val.val) := by
  have hL := (Finset.mem_filter.mp L.property).2
  obtain ⟨z, hz, hspan⟩ := exists_restricted_completion Q W L.val.val hQ
    hL.1 hL.2 L.val.property
  exact ⟨⟨z, hz, hspan⟩⟩

/-- The uniform law on successful completions is exactly the uniform
Grassmann interval law, even when the fixed prefix is not contained in W. -/
theorem independent_density_eq_interval (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q)
    (z₀ : IndependentCompletion (t := t) Q W) :
    (Nat.card {z : IndependentCompletion (t := t) Q W // completionVertex Q W z ∈ S} : ℝ) /
      Nat.card (IndependentCompletion (t := t) Q W) =
        relativeDensity S (interval (prefixSpan Q) (prefixSpan Q ⊔ W)) := by
  let f := completionIntervalVertex (t := t) Q W
  let c := Nat.card {z : IndependentCompletion (t := t) Q W // f z = f z₀}
  have hc : 0 < c := by
    let : Nonempty {z : IndependentCompletion (t := t) Q W // f z = f z₀} :=
      ⟨⟨z₀, rfl⟩⟩
    exact Nat.card_pos
  have hf (L : IntervalVertex (t := t) Q W) :
      Nat.card {z : IndependentCompletion (t := t) Q W // f z = L} = c := by
    obtain ⟨a⟩ := interval_completion_nonempty Q W hQ L
    obtain ⟨b⟩ := interval_completion_nonempty Q W hQ (f z₀)
    exact (Nat.card_congr (completionFiberEquiv Q W L)).trans
      ((restrictedCompletionCard_eq a b).trans
        (Nat.card_congr (completionFiberEquiv Q W (f z₀))).symm)
  have he := uniformFiber_card_ratio f (fun L => L.val ∈ S) c hc hf
  change (Nat.card {z : IndependentCompletion (t := t) Q W // completionVertex Q W z ∈ S} : ℝ) /
      Nat.card (IndependentCompletion (t := t) Q W) =
    (Nat.card {L : IntervalVertex (t := t) Q W // L.val ∈ S} : ℝ) /
      Nat.card (IntervalVertex (t := t) Q W) at he
  rw [he, Nat.card_congr (intervalEventEquiv S Q W)]
  simp only [IntervalVertex, Nat.card_eq_finsetCard, relativeDensity]

/-- The unconditioned restricted lift has density at most that of its exact
Grassmann interval. Unlike a union-bound argument, no independence-error term
is needed because dependent tuples are rejected by the lift. -/
theorem restrictedLiftDensity_le_interval (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q) :
    restrictedLiftDensity S Q W ≤
      relativeDensity S (interval (prefixSpan Q) (prefixSpan Q ⊔ W)) := by
  unfold restrictedLiftDensity
  rw [Nat.card_congr (completionEventEquiv S Q W)]
  by_cases h : Nonempty (IndependentCompletion (t := t) Q W)
  · obtain ⟨z₀⟩ := h
    exact (subtype_event_ratio_le
      (fun z : Fin t → W => LinearIndependent F2 (joinedTuple Q W z))
      (fun z => completionVertex Q W z ∈ S)).trans
        (le_of_eq (independent_density_eq_interval S Q W hQ z₀))
  · let : IsEmpty (IndependentCompletion (t := t) Q W) := not_nonempty_iff.mp h
    simp only [Nat.card_of_isEmpty, Nat.cast_zero, zero_div]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The full KMS restriction transfer, with the stronger exact ε bound. -/
theorem grassmann_pseudorandom_restricted {r : ℕ} {ε : ℝ}
    (S : Finset (Vertex n (q + t))) (hS : GrassmannPseudorandom S r ε)
    (hε : 0 ≤ ε) (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    restrictedLiftDensity S Q W ≤ ε := by
  by_cases hQ : LinearIndependent F2 Q
  · exact (restrictedLiftDensity_le_interval S Q W hQ).trans
      (hS (prefixSpan Q) (prefixSpan Q ⊔ W) le_sup_left
        ((interval_complexity_le Q W hQ).trans hbudget))
  · rw [restrictedLiftDensity_eq_zero_of_dependent S Q W hQ]
    exact hε

theorem grassmann_pseudorandom_lift {ell r : ℕ} {ε : ℝ}
    (S : Finset (Vertex n ell)) (hS : GrassmannPseudorandom S r ε)
    (hε : 0 ≤ ε) : TuplePseudorandom S r ε := by
  intro q t h Q W hb
  subst ell
  exact grassmann_pseudorandom_restricted S hS hε Q W hb

end
end MaxCutGames.Inverse.KMSBasisComparisonPseudorandom

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSMomentTheorem
attribute [-instance] _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual upper fourth-moment theorem for the full-rank lift of a
Grassmann set. Its hypotheses are literal tuple probabilities. The affine
sampling law, mixed estimate and hybrid derivative estimate are all discharged
by proved lemmas; there is no analytic estimate among the hypotheses. -/

namespace MaxCutGames.Inverse.KMSMomentScalar

noncomputable section
open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem boolean_nonneg {f : X → ℝ} (hf : IsBoolean f) (x : X) : 0 ≤ f x := by
  rcases hf x with h | h <;> simp [h]

omit [Fintype X] in
theorem boolean_sq {f : X → ℝ} (hf : IsBoolean f) (x : X) : f x ^ 2 = f x := by
  rcases hf x with h | h <;> simp [h]

theorem boolean_average_nonneg {f : X → ℝ} (hf : IsBoolean f) : 0 ≤ 𝔼 x, f x :=
  Finset.expect_nonneg fun x _ => boolean_nonneg hf x

theorem boolean_squared_average {f : X → ℝ} (hf : IsBoolean f) :
    (𝔼 x, f x ^ 2) = 𝔼 x, f x := by
  apply Finset.expect_congr rfl
  intro x _
  exact boolean_sq hf x

/-- Two finite Cauchy–Schwarz steps, with the Boolean support kept explicitly. -/
theorem boolean_fourth_holder {f : X → ℝ} (hf : IsBoolean f) (g : X → ℝ) :
    (𝔼 x, g x * f x) ^ 4 ≤ (𝔼 x, g x ^ 4) * (𝔼 x, f x) ^ 3 := by
  have h₁ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => g x * f x) f
  have hleft : (𝔼 x, (g x * f x) * f x) = 𝔼 x, g x * f x := by
    apply Finset.expect_congr rfl
    intro x _
    calc
      _ = g x * f x ^ 2 := by ring
      _ = _ := by rw [boolean_sq hf]
  have hright : (𝔼 x, (g x * f x) ^ 2) = 𝔼 x, g x ^ 2 * f x := by
    apply Finset.expect_congr rfl
    intro x _
    rw [mul_pow, boolean_sq hf]
  rw [hleft, hright, boolean_squared_average hf] at h₁
  have h₂ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (fun x => g x ^ 2) f
  have hpow : (𝔼 x, (g x ^ 2) ^ 2) = 𝔼 x, g x ^ 4 := by
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [hpow, boolean_squared_average hf] at h₂
  have hδ := boolean_average_nonneg hf
  have hweighted : 0 ≤ 𝔼 x, g x ^ 2 * f x :=
    Finset.expect_nonneg fun x _ => mul_nonneg (sq_nonneg _) (boolean_nonneg hf x)
  have hsquare := mul_self_le_mul_self (sq_nonneg (𝔼 x, g x * f x)) h₁
  have hscaled := mul_le_mul_of_nonneg_right h₂ (sq_nonneg (𝔼 x, f x))
  nlinarith only [hsquare, hscaled]

/-- The squared norm of an orthogonal component is bounded by the Boolean
function's density. The projection identity is the only needed property. -/
theorem projection_energy_le_density {f : X → ℝ} (hf : IsBoolean f) (g : X → ℝ)
    (hprojection : (𝔼 x, g x ^ 2) = 𝔼 x, g x * f x) :
    (𝔼 x, g x ^ 2) ≤ 𝔼 x, f x := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ g f
  rw [← hprojection, boolean_squared_average hf] at h
  have hη : 0 ≤ 𝔼 x, g x ^ 2 := Finset.expect_nonneg fun x _ => sq_nonneg _
  have hδ := boolean_average_nonneg hf
  nlinarith

/-- A stronger lower fourth-moment estimate than KMS Lemma 2.14, avoiding
division by the density and remaining valid at density zero. -/
theorem projection_fifth_le_density_fourth_moment {f : X → ℝ} (hf : IsBoolean f)
    (g : X → ℝ) (hprojection : (𝔼 x, g x ^ 2) = 𝔼 x, g x * f x) :
    (𝔼 x, g x ^ 2) ^ 5 ≤ (𝔼 x, f x) ^ 4 * (𝔼 x, g x ^ 4) := by
  have hholder := boolean_fourth_holder hf g
  rw [← hprojection] at hholder
  have hηδ := projection_energy_le_density hf g hprojection
  have hδ := boolean_average_nonneg hf
  have hη : 0 ≤ 𝔼 x, g x ^ 2 := Finset.expect_nonneg fun x _ => sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hηδ (pow_nonneg hη 4)
  have hscale := mul_le_mul_of_nonneg_right hholder hδ
  calc
    _ ≤ (𝔼 x, g x ^ 2) ^ 4 * (𝔼 x, f x) := by nlinarith only [hmul]
    _ ≤ ((𝔼 x, g x ^ 4) * (𝔼 x, f x) ^ 3) * (𝔼 x, f x) := hscale
    _ = _ := by ring

theorem fourth_root_power {ε : ℝ} (hε : 0 ≤ ε) :
    (ε ^ ((1 : ℝ) / 4)) ^ 4 = ε := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hε]
  norm_num

theorem le_of_fourth_power_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 4 ≤ b ^ 4) : a ≤ b := by
  by_contra hle
  have hlt : b < a := lt_of_not_ge hle
  have := pow_lt_pow_left₀ hlt hb (by decide : (4 : ℕ) ≠ 0)
  exact (not_lt_of_ge h) this

end
end MaxCutGames.Inverse.KMSMomentScalar

/-!
The spectral cutoff step of KMS on the actual full uniform rank-one noise.
The low-level fourth-moment estimate remains an explicit input to the last
combining lemma; none of these statements asserts that estimate or expansion.
The multiplier is reused from the proved uniform-subspace kernel count.
-/

namespace MaxCutGames.Inverse.KMSLowLevel
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixNoise
open MaxCutGames.Decoder.PositiveMultiplier
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Inverse.KMSMomentScalar

section FiniteCutoff
variable {I : Type*} [Fintype I]

theorem sum_rankEnergy (rank : I → ℕ) (a : I → ℝ) (r : ℕ) :
    (∑ i ∈ Finset.range (r + 1), rankEnergy rank a i) =
      ∑ s, if rank s ≤ r then a s ^ 2 else 0 := by
  unfold rankEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : rank s ≤ r
  · simp [eq_comm, Finset.mem_range, hs]
  · simp [eq_comm, Finset.mem_range, hs]

/-- Exact rank multiplier cutoff, without dimension-dependent constants. -/
theorem spectral_cutoff (rank : I → ℕ) (a : I → ℝ) (r : ℕ) :
    (∑ s, ((2 : ℝ) ^ rank s)⁻¹ * a s ^ 2) ≤
      (∑ i ∈ Finset.range (r + 1), rankEnergy rank a i) +
        ((2 : ℝ) ^ (r + 1))⁻¹ * ∑ s, a s ^ 2 := by
  rw [sum_rankEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  have ht : 0 ≤ ((2 : ℝ) ^ (r + 1))⁻¹ * a s ^ 2 := by positivity
  by_cases hs : rank s ≤ r
  · rw [ite_eq_left hs]
    have hinv : ((2 : ℝ) ^ rank s)⁻¹ ≤ 1 := by
      rw [← one_div]
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    have hm := mul_le_mul_of_nonneg_right hinv (sq_nonneg (a s))
    nlinarith
  · rw [ite_eq_right hs, zero_add]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg (a s))
    rw [← one_div, ← one_div]
    apply one_div_le_one_div_of_le (pow_pos (by norm_num) _)
    exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem spectral_cutoff_of_level_bounds (rank : I → ℕ) (a : I → ℝ)
    (r : ℕ) (C δ : ℝ) (htotal : (∑ s, a s ^ 2) = δ)
    (hlevels : ∀ i ≤ r, rankEnergy rank a i ≤ C * δ) :
    (∑ s, ((2 : ℝ) ^ rank s)⁻¹ * a s ^ 2) ≤
      ((r + 1 : ℕ) * C + ((2 : ℝ) ^ (r + 1))⁻¹) * δ := by
  have hsum : (∑ i ∈ Finset.range (r + 1), rankEnergy rank a i) ≤
      (r + 1 : ℕ) * C * δ := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (r + 1), C * δ := by
        apply Finset.sum_le_sum
        intro i hi
        exact hlevels i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      _ = _ := by simp; ring
  have hcut := spectral_cutoff rank a r
  rw [htotal] at hcut
  nlinarith only [hcut, hsum]
end FiniteCutoff

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem uniformNoise_apply (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    uniformNoise f X = 𝔼 v : F, 𝔼 l : E →ₗ[F2] F2, f (X + l.smulRight v) := by
  unfold uniformNoise linearRealNoiseOperator
  rw [subspaceLaw_sum]
  simp only [LinearMap.id_apply, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  ring

theorem uniformNoise_energy (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * uniformNoise f X) =
      ∑ S : F →ₗ[F2] E, ((2 : ℝ) ^ Module.finrank F2 S.range)⁻¹ *
        linearCoeff f S ^ 2 := by
  unfold uniformNoise
  rw [linearRealNoiseOperator_energy]
  apply Finset.sum_congr rfl
  intro S _
  rw [subspaceLaw_eigenvalue, LinearMap.comp_id]

omit [Fintype F] [Fintype (E →ₗ[F2] F2)] in
theorem rankEnergy_eq (f : (E →ₗ[F2] F) → ℝ) (i : ℕ) :
    rankEnergy (fun S : F →ₗ[F2] E => Module.finrank F2 S.range)
      (linearCoeff f) i = 𝔼 X, rankComponent i f X ^ 2 := by
  rw [rankComponent_energy, Finset.sum_filter]
  rfl

end
end MaxCutGames.Inverse.KMSLowLevel

/-!
The KMS scalar and spectral conclusion with an arbitrary dimension-independent
upper-moment constant. This accommodates quantitative proofs with coarser
constants without changing the order of any dimension choices.
-/

namespace MaxCutGames.Inverse.KMSLowLevel
noncomputable section
open scoped BigOperators Classical
open KMSMomentScalar KMSAnalytic
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

/-- No particular polynomial in the cutoff is required for the scalar step. -/
theorem projection_bound_of_general_fourthMoment {X : Type*} [Fintype X]
    {f : X → ℝ} (hf : IsBoolean f) (g : X → ℝ)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hprojection : (𝔼 x, g x ^ 2) = 𝔼 x, g x * f x)
    (hupper : (𝔼 x, g x ^ 4) ≤ C * (𝔼 x, g x ^ 2) * ε) :
    (𝔼 x, g x ^ 2) ≤ (C + 1) * ε ^ ((1 : ℝ) / 4) * (𝔼 x, f x) := by
  let η : ℝ := 𝔼 x, g x ^ 2
  let δ : ℝ := 𝔼 x, f x
  have hη : 0 ≤ η := Finset.expect_nonneg fun x _ => sq_nonneg _
  have hδ : 0 ≤ δ := boolean_average_nonneg hf
  have hlow := projection_fifth_le_density_fourth_moment hf g hprojection
  change η ^ 5 ≤ δ ^ 4 * (𝔼 x, g x ^ 4) at hlow
  have hupper' := mul_le_mul_of_nonneg_left hupper (pow_nonneg hδ 4)
  have hsmall : η ^ 4 ≤ C * ε * δ ^ 4 := by
    by_cases hz : η = 0
    · simpa only [hz, zero_pow (by decide : (4 : ℕ) ≠ 0)] using
        mul_nonneg (mul_nonneg hC hε) (pow_nonneg hδ 4)
    · have hηpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hηpos).mp
      nlinarith only [hlow, hupper']
  have hconstant : C ≤ (C + 1) ^ 4 := by
    nlinarith [sq_nonneg C, pow_nonneg hC 3, pow_nonneg hC 4]
  apply le_of_fourth_power_le hη (by positivity)
  calc
    η ^ 4 ≤ C * ε * δ ^ 4 := hsmall
    _ ≤ (C + 1) ^ 4 * ε * δ ^ 4 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconstant hε) (pow_nonneg hδ 4)
    _ = _ := by rw [mul_pow, mul_pow, fourth_root_power hε]

section ActualFourier
variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual full-uniform rank-one correlation, with a general moment constant. -/
theorem uniformNoise_bound_of_general_fourthMoments
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (r : ℕ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hupper : ∀ i ≤ r, (𝔼 X, rankComponent i f X ^ 4) ≤
      C * (𝔼 X, rankComponent i f X ^ 2) * ε) :
    (𝔼 X, f X * uniformNoise f X) ≤
      ((r + 1 : ℕ) * ((C + 1) * ε ^ ((1 : ℝ) / 4)) +
        ((2 : ℝ) ^ (r + 1))⁻¹) * (𝔼 X, f X) := by
  rw [uniformNoise_energy]
  apply spectral_cutoff_of_level_bounds
  · rw [linear_parseval, boolean_squared_average hf]
  · intro i hi
    rw [rankEnergy_eq]
    apply projection_bound_of_general_fourthMoment hf (rankComponent i f)
      C ε hC hε _ (hupper i hi)
    exact (component_inner_self _ f).symm
end ActualFourier

/-- Even an arbitrarily large constant depending on r alone permits the
cutoff and tolerance to be chosen before both dimensions. -/
theorem exists_general_cutoff_parameters (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      (r + 1 : ℕ) * ((C r + 1) * ε ^ ((1 : ℝ) / 4)) +
        ((2 : ℝ) ^ (r + 1))⁻¹ ≤ ζ / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < ζ / 4 by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  let r := max 1 N
  let D : ℝ := C r + 1
  let t : ℝ := min 1 (ζ / (4 * (r + 1 : ℕ) * D))
  let ε : ℝ := t ^ 4
  have hD : 0 < D := by dsimp [D]; linarith [hC r]
  have hr : 1 ≤ r := le_max_left _ _
  have hden : 0 < 4 * (r + 1 : ℕ) * D := by positivity
  have ht : 0 < t := lt_min (by norm_num) (div_pos hζ hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hε : 0 < ε := pow_pos ht _
  have hε1 : ε ≤ 1 := pow_le_one₀ ht.le ht1
  have hroot : ε ^ ((1 : ℝ) / 4) = t := by
    have hpow : (ε ^ ((1 : ℝ) / 4)) ^ 4 = t ^ 4 := fourth_root_power hε.le
    have hn : 0 ≤ ε ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hε.le _
    exact le_antisymm (le_of_fourth_power_le hn ht.le hpow.le)
      (le_of_fourth_power_le ht.le hn hpow.symm.le)
  have hlow : (r + 1 : ℕ) * (D * ε ^ ((1 : ℝ) / 4)) ≤ ζ / 4 := by
    rw [hroot]
    have ht' : t ≤ ζ / (4 * (r + 1 : ℕ) * D) := min_le_right _ _
    have hm := (le_div_iff₀ hden).mp ht'
    nlinarith only [hm]
  have htail : ((2 : ℝ) ^ (r + 1))⁻¹ < ζ / 4 := by
    have hmon : (1 / 2 : ℝ) ^ (r + 1) ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (le_trans (le_max_right 1 N) (Nat.le_succ r))
    simpa only [one_div, inv_pow] using hmon.trans_lt hN
  refine ⟨r, hr, ε, hε, hε1, ?_⟩
  change (r + 1 : ℕ) * (D * ε ^ ((1 : ℝ) / 4)) + _ ≤ ζ / 2
  linarith

end
end MaxCutGames.Inverse.KMSLowLevel

/-! Exact finite conditioning error for bounded functions. These identities
keep the rejected mass visible when comparing all maps with independent bases.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
/-- Finset conditioning and uniform sampling from its membership subtype are
the same normalized finite sum, including the empty event. -/
theorem expect_coe_eq (s : Finset Ω) (f : Ω → ℝ) :
    (𝔼 x : s, f x.val) = s.expect f := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_coe, Finset.sum_coe_sort]

omit [Fintype Ω] in
theorem expect_unit_interval (s : Finset Ω) (f : Ω → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    0 ≤ s.expect f ∧ s.expect f ≤ 1 := by
  refine ⟨Finset.expect_nonneg (fun x _ => hf0 x), ?_⟩
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · exact Finset.expect_le hs (fun x _ => hf1 x)

/-- The weighted conditional expectation is the unnormalized sum divided by
the ambient cardinality, also for an empty conditioning event. -/
theorem mass_mul_expect (s : Finset Ω) (f : Ω → ℝ) :
    (s.card : ℝ) / Fintype.card Ω * s.expect f =
      (∑ x ∈ s, f x) / Fintype.card Ω := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [Finset.expect_eq_sum_div_card]
    have hn : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_ne_zero
    by_cases hN : (Fintype.card Ω : ℝ) = 0
    · simp [hN]
    · field_simp

/-- Exact two-event total expectation, with the same zero convention on both
conditional expectations as mathlib's finite expectation. -/
theorem expect_partition (s : Finset Ω) (f : Ω → ℝ) :
    (𝔼 x, f x) =
      (s.card : ℝ) / Fintype.card Ω * s.expect f +
      ((Finset.univ \ s).card : ℝ) / Fintype.card Ω *
        (Finset.univ \ s).expect f := by
  rw [mass_mul_expect, mass_mul_expect, ← add_div, Fintype.expect_eq_sum_div_card]
  congr 1
  exact (Finset.sum_sdiff (Finset.subset_univ s)).symm.trans (add_comm _ _)

/-- Conditioning a bounded function changes its expectation by at most the
discarded probability mass. No independence assumption is used here. -/
theorem abs_expect_sub_restrict_le [Nonempty Ω] (s : Finset Ω) (f : Ω → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |(𝔼 x, f x) - s.expect f| ≤
      ((Finset.univ \ s).card : ℝ) / Fintype.card Ω := by
  have hB := expect_unit_interval s f hf0 hf1
  have hC := expect_unit_interval (Finset.univ \ s) f hf0 hf1
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (s.card : ℝ) / Fintype.card Ω +
      ((Finset.univ \ s).card : ℝ) / Fintype.card Ω = 1 := by
    rw [← add_div]
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
    have hcast : ((Finset.univ \ s).card : ℝ) + (s.card : ℝ) =
        Fintype.card Ω := by exact_mod_cast hc.trans (Finset.card_univ)
    rw [add_comm, hcast, div_self hN]
  have hq : 0 ≤ ((Finset.univ \ s).card : ℝ) / Fintype.card Ω := by positivity
  have hp : (s.card : ℝ) / Fintype.card Ω =
      1 - ((Finset.univ \ s).card : ℝ) / Fintype.card Ω := by linarith
  rw [expect_partition]
  rw [hp]
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hq hB.1, mul_nonneg hq hC.1,
      mul_nonneg hq (sub_nonneg.mpr hB.2)]
  · nlinarith [mul_nonneg hq hB.1, mul_nonneg hq hC.1,
      mul_nonneg hq (sub_nonneg.mpr hC.2)]

end
end MaxCutGames.Inverse.KMSBasisComparison

/-!
The good event for an ordered-basis rank-one update is that its functional
is nonzero and its direction lies outside the starting range. Its exact
finite cardinality gives the exceptional-mass bound without conditioning
either factor of the original uniform experiment.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

theorem card_functional (ell : ℕ) : Fintype.card (Functional ell) = 2 ^ ell := by
  rw [Module.card_eq_pow_finrank (K := KMS.F2)]
  change Fintype.card (ZMod 2) ^ Module.finrank KMS.F2 (Module.Dual KMS.F2
    (KMS.Ambient ell)) = _
  rw [Subspace.dual_finrank_eq]
  simp [KMS.Ambient, KMS.F2]

theorem card_ambient (n : ℕ) : Fintype.card (KMS.Ambient n) = 2 ^ n := by
  simp [KMS.Ambient, KMS.F2]

theorem card_range {n ell : ℕ} (X : BasisMap n ell) (hX : Function.Injective X) :
    Fintype.card X.range = 2 ^ ell := by
  rw [Module.card_eq_pow_finrank (K := KMS.F2), LinearMap.finrank_range_of_inj hX]
  simp [KMS.Ambient, KMS.F2]

/-- The exact good-event count, including the zero-dimensional boundary. -/
theorem card_goodParameters {n ell : ℕ} (X : BasisMap n ell)
    (hX : Function.Injective X) :
    (goodParameters X).card = (2 ^ ell - 1) * (2 ^ n - 2 ^ ell) := by
  rw [goodParameters, Finset.card_product]
  have ha : (Finset.univ.filter (fun a : Functional ell => a ≠ 0)).card =
      2 ^ ell - 1 := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl, card_functional]
    simp
  have hy : (Finset.univ.filter (fun y : KMS.Ambient n => y ∉ X.range)).card =
      2 ^ n - 2 ^ ell := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl, card_ambient]
    rw [card_range X hX]
  rw [ha, hy]

/-- Exceptional mass is bounded by the sum of the two factor exceptions. -/
theorem badParameters_mass_le {n ell : ℕ} (X : BasisMap n ell)
    (hX : Function.Injective X) :
    1 - ((goodParameters X).card : ℝ) /
        Fintype.card (Functional ell × KMS.Ambient n) ≤
      ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  have hcard : 2 ^ ell ≤ 2 ^ n := by
    rw [← card_ambient ell, ← card_ambient n]
    exact Fintype.card_le_of_injective X hX
  have hone : 1 ≤ 2 ^ ell := Nat.one_le_pow ell 2 (by decide)
  rw [card_goodParameters X hX, Fintype.card_prod, card_functional, card_ambient]
  push_cast [Nat.cast_sub hone, Nat.cast_sub hcard]
  have he : (0 : ℝ) < 2 ^ ell := pow_pos (by norm_num) _
  have hn : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) _
  field_simp
  nlinarith

/-- The same estimate in the complement-cardinality form used for deleting
the bad event from a finite expectation. -/
theorem badParameters_mass_le_compl {n ell : ℕ} (X : BasisMap n ell)
    (hX : Function.Injective X) :
    (((Finset.univ \ goodParameters X).card : ℕ) : ℝ) /
        Fintype.card (Functional ell × KMS.Ambient n) ≤
      ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  have ht : (0 : ℝ) < Fintype.card (Functional ell × KMS.Ambient n) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsub := Finset.card_le_card (Finset.subset_univ (goodParameters X))
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Nat.cast_sub hsub,
    Finset.card_univ, sub_div, div_self (ne_of_gt ht)]
  exact badParameters_mass_le X hX

end
end MaxCutGames.Inverse.KMSBasisComparison

/-!
Exact finite counts for the Grassmann graph comparison in Section 4.
The quotient-line parametrization is independent of any expansion theorem.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem card_lines_binary [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E] :
    Nat.card (Lines (ZMod 2) E) = 2 ^ finrank (ZMod 2) E - 1 := by
  classical
  let spanMap : {v : E // v ≠ 0} → Lines (ZMod 2) E := fun v =>
    ⟨Submodule.span (ZMod 2) {v.val}, finrank_span_singleton v.property⟩
  have hinj : Function.Injective spanMap := by
    intro v w h
    have hv : v.val ∈ Submodule.span (ZMod 2) {w.val} := by
      have hs : Submodule.span (ZMod 2) {v.val} =
          Submodule.span (ZMod 2) {w.val} := congrArg Subtype.val h
      rw [← hs]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hcases c with hc0 | hc1
    · exact False.elim (v.property (by simpa [hc0] using hc.symm))
    · exact Subtype.ext (by simpa [hc1] using hc.symm)
  have hsurj : Function.Surjective spanMap := by
    intro L
    obtain ⟨v, hv0, _⟩ := (finrank_eq_one_iff').mp L.property
    have hv : (v : E) ≠ 0 := fun h => hv0 (Subtype.ext h)
    refine ⟨⟨v.val, hv⟩, Subtype.ext ?_⟩
    exact (eq_span_singleton_of_mem_of_finrank_eq_one L.property v.property hv).symm
  let e : {v : E // v ≠ 0} ≃ Lines (ZMod 2) E := Equiv.ofBijective spanMap ⟨hinj, hsurj⟩
  let coords : E ≃ₗ[ZMod 2] (Fin (finrank (ZMod 2) E) → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  let : Finite E := Finite.of_equiv _ coords.symm.toEquiv
  let : Fintype E := Fintype.ofFinite E
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, Module.card_eq_pow_finrank (K := ZMod 2)]
  simp

theorem card_hyperplanes_binary [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] :
    Nat.card (Hyperplanes (ZMod 2) E) = 2 ^ finrank (ZMod 2) E - 1 := by
  rw [Nat.card_congr (hyperplanesEquivDualLines (K := ZMod 2) (E := E)),
    card_lines_binary, Subspace.dual_finrank_eq]

theorem card_extensions_binary [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (H : Submodule (ZMod 2) E) :
    Nat.card (Extensions H) = 2 ^ finrank (ZMod 2) (E ⧸ H) - 1 := by
  rw [Nat.card_congr (extensionsEquivLines H), card_lines_binary]

end MaxCutGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixChartDegreeNeighbors
attribute [-instance] _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The full Grassmann degree, by choosing the intersection hyperplane and a
different one-dimensional extension. No graph regularity is assumed.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem card_other_extensions_binary [Module (ZMod 2) E] [Finite E]
    [FiniteDimensional (ZMod 2) E] (L : Submodule (ZMod 2) E)
    (H : HyperplanesBelow L) :
    Nat.card {W : Extensions H.val // W.val ≠ L} =
      2 ^ finrank (ZMod 2) (E ⧸ H.val) - 2 := by
  classical
  let : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun H : Submodule (ZMod 2) E => (H : Set E))
      SetLike.coe_injective
  let base : Extensions H.val := ⟨L, H.property.1, H.property.2.symm⟩
  let : Fintype (Extensions H.val) := Fintype.ofFinite _
  have heq : (fun W : Extensions H.val => W.val ≠ L) = (fun W => W ≠ base) := by
    funext W
    apply propext
    apply not_congr
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  rw [heq]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
    card_extensions_binary]
  omega

theorem card_grassmann_neighbors_binary [Module (ZMod 2) E] [Finite E]
    [FiniteDimensional (ZMod 2) E] (L : Submodule (ZMod 2) E) (m : ℕ)
    (hE : finrank (ZMod 2) E = finrank (ZMod 2) L + m) :
    Nat.card (GrassmannNeighbors L) =
      (2 ^ finrank (ZMod 2) L - 1) * (2 ^ (m + 1) - 2) := by
  classical
  let : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun H : Submodule (ZMod 2) E => (H : Set E))
      SetLike.coe_injective
  let : Fintype (HyperplanesBelow L) := Fintype.ofFinite _
  rw [Nat.card_congr (neighborsEquivExtensionData L), Nat.card_sigma]
  have hterm (H : HyperplanesBelow L) :
      Nat.card {W : Extensions H.val // W.val ≠ L} = 2 ^ (m + 1) - 2 := by
    rw [card_other_extensions_binary]
    have h := H.val.finrank_quotient_add_finrank
    have hH := H.property.2
    congr 2
    omega
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card,
    Nat.card_congr (hyperplanesBelowEquiv L), card_hyperplanes_binary]

end MaxCutGames.Inverse.MatrixChart

/-!
The local neighbor law for the ordered-basis lift used in KMS Lemma 2.7.
The map is an arbitrary injective linear map, not a matrix graph chart.
An update in a direction outside its image stays injective, and its image
intersects the original image in exactly the transported functional kernel.
-/

/-! Every full Grassmann neighbor is reached by an outside rank-one update.
The proof works over every field and never selects a graph chart. -/

namespace MaxCutGames.Inverse.KMSBasisComparison

open Module

variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]

/-- A codimension-one subspace is the kernel of a nonzero functional. -/
theorem exists_functional_ker_eq (H : Submodule K E)
    (hH : finrank K H + 1 = finrank K E) :
    ∃ a : E →ₗ[K] K, a ≠ 0 ∧ LinearMap.ker a = H := by
  have hproper : H < ⊤ := lt_top_iff_ne_top.mpr (by
    intro h
    rw [h, finrank_top] at hH
    omega)
  obtain ⟨a, ha, hle⟩ := H.exists_le_ker_of_lt_top hproper
  refine ⟨a, ha, (Submodule.eq_of_le_of_finrank_eq hle ?_).symm⟩
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero ha
  omega

/-- An arbitrary Grassmann neighbor is the range of one of the actual
rank-one updates used by the ordered-basis test. -/
theorem exists_rankOneUpdate_range_eq (X : E →ₗ[K] F)
    (hX : Function.Injective X)
    (W : MatrixChart.GrassmannNeighbors (LinearMap.range X)) :
    ∃ (a : E →ₗ[K] K) (y : F), a ≠ 0 ∧ y ∉ LinearMap.range X ∧
      LinearMap.range (rankOneUpdate X a y) = W.val := by
  let H : Submodule K E := W.val.comap X
  have hmap : H.map X = LinearMap.range X ⊓ W.val := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨LinearMap.mem_range_self X x, hx⟩
    · rintro ⟨⟨x, hx⟩, hz⟩
      exact ⟨x, by change X x ∈ W.val; rw [hx]; exact hz, hx⟩
  have hH : finrank K H + 1 = finrank K E := by
    rw [(Submodule.equivMapOfInjective X hX H).finrank_eq, hmap]
    exact W.property.2.trans (LinearMap.finrank_range_of_inj hX)
  obtain ⟨a, ha, hker⟩ := exists_functional_ker_eq H hH
  obtain ⟨x₀, hx₀⟩ := LinearMap.surjective ha (1 : K)
  have hnotle : ¬ W.val ≤ LinearMap.range X := by
    intro hle
    have heq := Submodule.eq_of_le_of_finrank_eq hle W.property.1
    have hd := W.property.2
    rw [heq, inf_idem] at hd
    omega
  obtain ⟨w, hwW, hwX⟩ := SetLike.not_le_iff_exists.mp hnotle
  let y := w - X x₀
  have hy : y ∉ LinearMap.range X := by
    intro hy
    apply hwX
    have h := (LinearMap.range X).add_mem hy (LinearMap.mem_range_self X x₀)
    simpa only [y, sub_add_cancel] using h
  refine ⟨a, y, ha, hy, ?_⟩
  have hle : LinearMap.range (rankOneUpdate X a y) ≤ W.val := by
    rintro z ⟨x, rfl⟩
    have hxker : x - a x • x₀ ∈ LinearMap.ker a := by
      change a (x - a x • x₀) = 0
      simp only [map_sub, map_smul, hx₀, smul_eq_mul, mul_one, sub_self]
    have hxW : X (x - a x • x₀) ∈ W.val := by
      have hxH : x - a x • x₀ ∈ H := by rwa [← hker]
      exact hxH
    have heq : rankOneUpdate X a y x = X (x - a x • x₀) + a x • w := by
      simp only [rankOneUpdate_apply, y, map_sub, map_smul, smul_sub]
      abel
    rw [heq]
    exact W.val.add_mem hxW (W.val.smul_mem _ hwW)
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj (injective_rankOneUpdate X hX a hy),
    W.property.1, LinearMap.finrank_range_of_inj hX]

end MaxCutGames.Inverse.KMSBasisComparison

namespace MaxCutGames.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem lowerRows_le_graph_iff {ι : Type*} (d : ι → X) (s : ι → Y)
    (T : X →ₗ[K] Y) :
    lowerRows d s ≤ T.graph ↔ ∀ i, T (d i) = s i := by
  rw [lowerRows, Submodule.span_le]
  constructor
  · intro h i
    exact (h ⟨i, rfl⟩).symm
  · rintro h _ ⟨i, rfl⟩
    exact (h i).symm

theorem graph_le_upperColumns_iff {ι : Type*}
    (t : ι → X →ₗ[K] K) (q : ι → Y →ₗ[K] K) (T : X →ₗ[K] Y) :
    T.graph ≤ upperColumns t q ↔ ∀ i, (q i).comp T = t i := by
  constructor
  · intro h i
    apply LinearMap.ext
    intro x
    have hx := h (show (x, T x) ∈ T.graph from rfl)
    have hi := ((Submodule.mem_iInf _).mp hx) i
    exact sub_eq_zero.mp hi
  · intro h x hx
    apply (Submodule.mem_iInf _).mpr
    intro i
    change q i x.2 - t i x.1 = 0
    rw [hx]
    exact sub_eq_zero.mpr (congrArg (fun f : X →ₗ[K] K => f x.1) (h i))

/-- Exact translation of a Grassmann interval into simultaneous row and
column constraints, retaining their inhomogeneous right-hand sides. -/
theorem interval_iff_slice {ι κ : Type*} (d : ι → X) (s : ι → Y)
    (t : κ → X →ₗ[K] K) (q : κ → Y →ₗ[K] K) (T : X →ₗ[K] Y) :
    lowerRows d s ≤ T.graph ∧ T.graph ≤ upperColumns t q ↔
      (∀ i, T (d i) = s i) ∧ (∀ j, (q j).comp T = t j) := by
  rw [lowerRows_le_graph_iff, graph_le_upperColumns_iff]

end MaxCutGames.Inverse.MatrixChart

/-!
Exact rank-one sampling in the binary matrix chart. Nonzero pairs of a
functional and a vector represent rank-one maps uniquely over `ZMod 2`.
Thus uniform nonzero factors give uniform rank-one maps. Zero factors are
excluded explicitly; no conditioned/unconditioned sampling is identified.
-/

/-!
For a fixed nonzero binary functional, all updates with a prescribed image
form one affine coset of the image of its kernel. This is an exact fiber
equivalence, so it retains the multiplicities needed for uniform sampling.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

theorem card_fixedFunctionalNeighborFiber (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Nat.card (FixedFunctionalNeighborFiber X a y₀) = Nat.card a.ker :=
  (Nat.card_congr (fixedFunctionalNeighborFiberEquiv X hX a ha hy₀)).symm

theorem card_fixedFunctionalNeighborFiber_pow [Fintype E]
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Nat.card (FixedFunctionalNeighborFiber X a y₀) =
      2 ^ (Module.finrank (ZMod 2) E - 1) := by
  classical
  rw [card_fixedFunctionalNeighborFiber X hX a ha hy₀, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2) (V := a.ker), ZMod.card]
  congr 1
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero ha
  omega

end
end MaxCutGames.Inverse.KMSBasisComparison

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSBasisComparisonNeighborsFiberFunctional
attribute [-instance] _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Binary linear functionals are determined by their kernels. The statement
includes the zero functional; no choice of a nonzero normalization is needed.
Injective linear images retain the same uniqueness property.
-/

/-!
The complete pair fiber of the ordered-basis neighbor sampler. Equal updated
images determine the binary functional exactly. The remaining ambiguity is
the affine kernel coset, of cardinality `2 ^ (dim E - 1)`.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

theorem card_outsideNeighborPairFiber [Fintype E]
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Nat.card (OutsideNeighborPairFiber X a y₀) =
      2 ^ (Module.finrank (ZMod 2) E - 1) := by
  rw [← Nat.card_congr (fixedFunctionalEquivPairFiber X hX a ha hy₀)]
  exact card_fixedFunctionalNeighborFiber_pow X hX a ha hy₀

end

/-!
# Constant ordered-basis fibers

An injective linear map with a fixed range is exactly an ordered basis of that
range. Choosing one such basis identifies this fiber with the automorphisms of
the domain. The generic finite-fiber lemma below proves uniformity, including
the complete normalization in the rational density identity.
-/

noncomputable section
open scoped BigOperators Classical

section UniformFibers

variable {X Y G : Type*}

/-- Uniform sampling pushes forward to uniform sampling whenever every fiber
is equivalent to the same nonempty finite type. This applies to real and
rational expectations alike. -/
theorem expect_eq_of_uniform_fibers [Fintype X] [Fintype Y] [Fintype G]
    [Nonempty G] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (f : X → Y) (e : ∀ y, {x : X // f x = y} ≃ G) (g : Y → M) :
    (𝔼 x, g (f x)) = 𝔼 y, g y := by
  calc
    _ = 𝔼 z : Y × G, g z.1 :=
      Fintype.expect_equiv (fiberProductEquiv f e) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset Y) (Finset.univ : Finset G)
          (fun z : Y × G => g z.1))

end UniformFibers

theorem lift_nonempty_iff {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    (lift S).Nonempty ↔ S.Nonempty := by
  constructor
  · rintro ⟨X, hX⟩
    obtain ⟨L, hL, _⟩ := (mem_lift S X).mp hX
    exact ⟨L, hL⟩
  · rintro ⟨L, hL⟩
    let X := (rangeFiberEquiv L.val).symm (vertexBasis L)
    refine ⟨X.val, (mem_lift S X.val).mpr ?_⟩
    exact ⟨L, hL, X.property.2⟩

end
end MaxCutGames.Inverse.KMSBasisComparison

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]
  [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) F]

/-- Every full Grassmann neighbor has exactly the same number of original
factor pairs. The number is the size of one codimension-one kernel. -/
theorem card_outsideNeighborSample_fiber [Fintype E]
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (W : MatrixChart.GrassmannNeighbors X.range) :
    Nat.card {p : OutsideNeighborFactors X // outsideNeighborSample X hX p = W} =
      2 ^ (Module.finrank (ZMod 2) E - 1) := by
  obtain ⟨a, y, ha, hy, hW⟩ := exists_rankOneUpdate_range_eq X hX W
  let e : {p : OutsideNeighborFactors X // outsideNeighborSample X hX p = W} ≃
      OutsideNeighborPairFiber X a y := Equiv.subtypeEquivRight (fun p => by
    constructor
    · intro h
      exact (congrArg Subtype.val h).trans hW.symm
    · intro h
      exact Subtype.ext (h.trans hW))
  rw [Nat.card_congr e]
  exact card_outsideNeighborPairFiber X hX a ha hy

/-- Uniform neighbor law for any real observable. There is no chart
restriction, hidden conditioning, or additional loss in this identity. -/
theorem expect_outsideNeighborSample [Fintype E] [Fintype F]
    [Fintype (E →ₗ[ZMod 2] ZMod 2)]
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    [Fintype (MatrixChart.GrassmannNeighbors X.range)]
    (g : MatrixChart.GrassmannNeighbors X.range → ℝ) :
    (𝔼 p : OutsideNeighborFactors X, g (outsideNeighborSample X hX p)) =
      𝔼 W : MatrixChart.GrassmannNeighbors X.range, g W := by
  let G := Fin (2 ^ (Module.finrank (ZMod 2) E - 1))
  let : Nonempty G := ⟨⟨0, by positivity⟩⟩
  let e : ∀ W : MatrixChart.GrassmannNeighbors X.range,
      {p : OutsideNeighborFactors X // outsideNeighborSample X hX p = W} ≃ G :=
    fun W => Finite.equivFinOfCardEq (card_outsideNeighborSample_fiber X hX W)
  exact expect_eq_of_uniform_fibers (outsideNeighborSample X hX) e g

end
end MaxCutGames.Inverse.KMSBasisComparison

/-!
Rank-one differences parametrize the actual Grassmann neighbors that remain
in the matrix chart. The equivalences retain the graph subspaces themselves,
so cardinalities and uniform sampling can be transported to the graph.
-/

/-! Exact chart-to-Grassmann degree comparison over the binary field. -/

namespace MaxCutGames.Inverse.MatrixChart

open Module

variable {ell m : ℕ}

theorem card_grassmann_neighbors_graph (T : CoordinateMatrix ell m) :
    Nat.card (GrassmannNeighbors T.graph) =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
  have h := card_grassmann_neighbors_binary T.graph m (by
    rw [finrank_graph, Module.finrank_prod]
    simp)
  simpa only [finrank_graph, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using h

end MaxCutGames.Inverse.MatrixChart

/-! Concrete matrix coordinates for the graph chart. In particular the upper
interval equations become `M q = t`, while the lower equations become `dᵀ M = sᵀ`.
The right-hand sides are retained; none of these slices is required to be linear.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

/-- Transposing the chart map sends a column specification to its dot functional. -/
theorem dotFunctional_comp_vecMulLinear (M : Matrix ι κ K) (q : κ → K) :
    (dotFunctional q).comp M.vecMulLinear = dotFunctional (M *ᵥ q) := by
  apply LinearMap.ext
  intro x
  change q ⬝ᵥ (x ᵥ* M) = (M *ᵥ q) ⬝ᵥ x
  rw [← Matrix.mulVec_transpose, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

theorem column_equation_iff (M : Matrix ι κ K) (q : κ → K) (t : ι → K) :
    (dotFunctional q).comp M.vecMulLinear = dotFunctional t ↔ M *ᵥ q = t := by
  rw [dotFunctional_comp_vecMulLinear]
  exact dotFunctional_injective.eq_iff

end MaxCutGames.Inverse.MatrixChart

/-! Transport the product-coordinate chart into the actual Grassmann vertices
used by the KMS boundary. The transport is a proved ambient linear equivalence.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RowErasure
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
`InversePrinciple` concerns an arbitrary table function, full uniform factor
sampling, and an affine intercept.
-/

namespace MaxCutGames.Inverse.Shortcode

open scoped BigOperators Classical

/-- The fiber/Grassmann route produces the constant affine target `0,u`.
Keeping `u` is essential: this result does not claim a homogeneous target. -/
theorem Slice.constantAgreement_eq_affine {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (u : Vector ell) :
    S.constantAgreement f u = S.affineAgreement f 0 u := by
  simp [Slice.constantAgreement, Slice.affineAgreement]

theorem hasAffineSlice_of_constant {ell m : ℕ} (f : Mat ell m → Vector ell)
    (α : ℝ) (r : ℕ) (S : Slice ell m) (hrows : S.rows ≤ r)
    (hcolumns : S.columns ≤ r) (hne : S.points.Nonempty) (u : Vector ell)
    (h : α ≤ S.constantAgreement f u) : HasAffineSlice f α r := by
  exact ⟨S, hrows, hcolumns, hne, 0, u, by
    simpa only [S.constantAgreement_eq_affine f u] using h⟩

end MaxCutGames.Inverse.Shortcode

/-!
Fixed-length descriptions for the row-erasure union bound. Row and column
equation lists are padded with zero equations. Targets retain both the linear
coefficient and the affine intercept. Thus the finite description count is
exactly `2^((2r+1)(ell+m))`, including descriptions with empty solution sets.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixChartKMSNeighbors
attribute [-instance] _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-neighbor count in the KMS vertex representation. -/

namespace MaxCutGames.Inverse.MatrixChart

open Module

theorem card_full_neighbors {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    (KMS.neighbors (matrixVertex M)).card =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
  classical
  have h : Nat.card {W : KMS.Vertex (ell + m) ell //
      KMS.Adjacent (matrixVertex M) W} =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
    rw [← Nat.card_congr (kmsNeighborsEquiv (matrixVertex M))]
    change Nat.card (GrassmannNeighbors
      ((matrixGraph M).map (coordinateJoin (ZMod 2) ell m).toLinearMap)) = _
    rw [← Nat.card_congr (grassmannNeighborsMapEquiv
      (coordinateJoin (ZMod 2) ell m) (matrixGraph M))]
    exact card_grassmann_neighbors_graph M.vecMulLinear
  simpa only [Nat.card_eq_fintype_card, KMS.neighbors, Fintype.card_subtype] using h

/-- Exactly two full Grassmann neighbors for every nonzero factor pair. -/
theorem card_full_neighbors_twice {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    (KMS.neighbors (matrixVertex M)).card =
      2 * ((2 ^ ell - 1) * (2 ^ m - 1)) := by
  rw [card_full_neighbors]
  have hpow : 2 ^ (m + 1) - 2 = 2 * (2 ^ m - 1) := by
    rw [pow_succ, Nat.mul_sub_left_distrib]
    simp [Nat.mul_comm]
  rw [hpow]
  ac_rfl

end MaxCutGames.Inverse.MatrixChart

/-! Local ordered-basis retention in the precise KMS vertex representation. -/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

private theorem relativeDensity_eq_expect_subtype_inline_KMSBasisComparisonNeighborsRetention {Ω : Type*} [Fintype Ω]
    (S : Finset Ω) (P : Ω → Prop) :
    KMS.relativeDensity S (Finset.univ.filter P) =
      𝔼 x : {x : Ω // P x}, if x.val ∈ S then (1 : ℝ) else 0 := by
  unfold KMS.relativeDensity
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
    (fun x => if x ∈ S then (1 : ℝ) else 0)]
  rw [Finset.sum_boole, Fintype.card_subtype]
  have hsets : S ∩ Finset.univ.filter P =
      (Finset.univ.filter P).filter (fun x => x ∈ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hsets]

/-- The ordered-basis test conditioned on its good event samples every full
Grassmann neighbor uniformly. The target observable is the original lifted
indicator, so this identity directly feeds the matrix-test retention bound. -/
theorem outsideNeighbor_retention {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    (𝔼 p : OutsideNeighborFactors X,
      liftedIndicator S (rankOneUpdate X p.1.val p.2.val)) =
        KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX)) := by
  let e : MatrixChart.GrassmannNeighbors X.range ≃
      {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W} :=
    MatrixChart.kmsNeighborsEquiv (rangeVertex X hX)
  let : Fintype (MatrixChart.GrassmannNeighbors X.range) :=
    Fintype.ofEquiv {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W} e.symm
  let g : MatrixChart.GrassmannNeighbors X.range → ℝ :=
    fun W => if (e W).val ∈ S then 1 else 0
  calc
    _ = 𝔼 p : OutsideNeighborFactors X, g (outsideNeighborSample X hX p) := by
      apply Finset.expect_congr rfl
      intro p _
      unfold liftedIndicator
      rw [inLift_iff_rangeVertex_mem S _
        (injective_rankOneUpdate X hX p.1.val p.2.property)]
      have hv : rangeVertex (rankOneUpdate X p.1.val p.2.val)
          (injective_rankOneUpdate X hX p.1.val p.2.property) =
            (e (outsideNeighborSample X hX p)).val := by
        apply Subtype.ext
        rfl
      rw [hv]
      by_cases hp : (e (outsideNeighborSample X hX p)).val ∈ S <;> simp [g, hp]
    _ = 𝔼 W : MatrixChart.GrassmannNeighbors X.range, g W :=
      expect_outsideNeighborSample X hX g
    _ = 𝔼 W : {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W},
        if W.val ∈ S then (1 : ℝ) else 0 :=
      Fintype.expect_equiv e _ _ (fun _ => rfl)
    _ = _ := (relativeDensity_eq_expect_subtype_inline_KMSBasisComparisonNeighborsRetention S
      (KMS.Adjacent (rangeVertex X hX))).symm

end
end MaxCutGames.Inverse.KMSBasisComparison

/-!
# Ordered-basis retention versus Grassmann retention

This is the sampling comparison in KMS Lemma 2.7. The original experiment
uses all functionals and all directions, including zero. Its good event
induces exactly the full Grassmann-neighbor law; all other outcomes contribute
at most their explicit probability mass. Initial bases push forward uniformly
to the original Grassmann set.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

/-- Good-event conditioning is the exact full-neighbor Grassmann retention. -/
theorem goodParameters_expect {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    (goodParameters X).expect
      (fun p => liftedIndicator S (rankOneUpdate X p.1 p.2)) =
        KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX)) := by
  rw [← expect_coe_eq]
  calc
    _ = 𝔼 p : OutsideNeighborFactors X,
        liftedIndicator S (rankOneUpdate X p.1.val p.2.val) :=
      Fintype.expect_equiv (goodParametersEquiv X) _ _ (fun _ => rfl)
    _ = _ := outsideNeighbor_retention S X hX

/-- Quantitative local comparison, with a slightly smaller exceptional-mass
bound than the stated KMS Lemma 2.7. -/
theorem fullStepRetention_compare {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    |fullStepRetention S X -
      KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX))| ≤
        ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  rw [← goodParameters_expect S X hX]
  apply (abs_expect_sub_restrict_le (goodParameters X)
    (fun p => liftedIndicator S (rankOneUpdate X p.1 p.2))
    (fun p => liftedIndicator_nonneg S _) (fun p => liftedIndicator_le_one S _)).trans
  simpa only [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] using
    (badParameters_mass_le_compl X hX)

/-- Choosing a uniform accepted ordered basis chooses a uniform element of
the original Grassmann set. -/
theorem liftRange_retention_expect {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    (𝔼 X : lift S,
      KMS.relativeDensity S (KMS.neighbors (liftRange S X).val)) = KMS.retention S := by
  let : Nonempty (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
    ⟨LinearEquiv.refl _ _⟩
  rw [expect_eq_of_uniform_fibers (liftRange S) (liftRangeFiberAut S)
    (fun L : S => KMS.relativeDensity S (KMS.neighbors L.val))]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_coe, KMS.retention]
  congr 1
  exact (Finset.sum_subtype S (fun _ => Iff.rfl)
    (fun L => KMS.relativeDensity S (KMS.neighbors L))).symm

/-- The actual full sampling-law comparison for the lifted Grassmann set. -/
theorem liftRetention_compare {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (hS : S.Nonempty) :
    |liftRetention S - KMS.retention S| ≤
      ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  have hLift := (lift_nonempty_iff S).mpr hS
  let : Nonempty (lift S) := ⟨⟨hLift.choose, hLift.choose_spec⟩⟩
  rw [liftRetention, ← liftRange_retention_expect S,
    ← Finset.expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro X _
  exact fullStepRetention_compare S X.val
    (injective_of_inLift ((mem_lift S X.val).mp X.property))

theorem liftDensity_eq_card {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    liftDensity S = ((lift S).card : ℝ) / Fintype.card (BasisMap n ell) := by
  simp only [liftDensity, liftedIndicator, Fintype.expect_eq_sum_div_card,
    Finset.sum_boole, lift]

theorem liftDensity_pos {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (hS : S.Nonempty) : 0 < liftDensity S := by
  rw [liftDensity_eq_card]
  apply div_pos
  · exact Nat.cast_pos.mpr ((lift_nonempty_iff S).mpr hS).card_pos
  · exact Nat.cast_pos.mpr Fintype.card_pos

/-- Fourier correlation uses the full ambient space. This identity is the
exact conversion to the conditional-start retention and preserves density. -/
theorem liftDensity_mul_retention {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    liftDensity S * liftRetention S =
      𝔼 X : BasisMap n ell, liftedIndicator S X * fullStepRetention S X := by
  rw [liftDensity_eq_card, liftRetention, expect_coe_eq, mass_mul_expect,
    Fintype.expect_eq_sum_div_card]
  congr 1
  simp only [liftedIndicator, ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  rfl

/-- Swapping the independent factors matches the Fourier noise convention
of first choosing a direction, then a functional, including both zero cases. -/
theorem fullStepRetention_eq_noise {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) :
    fullStepRetention S X =
      𝔼 y : KMS.Ambient n, 𝔼 a : Functional ell,
        liftedIndicator S (X + a.smulRight y) := by
  unfold fullStepRetention
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact Finset.expect_comm _ _ _

/-- A proved ambient correlation bound converts directly to the conditional
retention bound; positive density follows from the actual nonempty lift. -/
theorem liftRetention_le_of_correlation_le {n ell : ℕ}
    (S : Finset (KMS.Vertex n ell)) (hS : S.Nonempty) (ζ : ℝ)
    (hc : (𝔼 X : BasisMap n ell,
      liftedIndicator S X * fullStepRetention S X) ≤ ζ * liftDensity S) :
    liftRetention S ≤ ζ := by
  rw [← liftDensity_mul_retention S, mul_comm ζ (liftDensity S)] at hc
  exact le_of_mul_le_mul_left hc (liftDensity_pos S hS)

end
end MaxCutGames.Inverse.KMSBasisComparison

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical
open KMSBasisComparisonPseudorandom

/-- Elementary eventual decay, using Archimedean unboundedness of powers.
No dimensional rate is hidden in a limit or a filter assumption. -/
theorem exists_binary_ratio_threshold (c ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → c / (2 : ℝ) ^ n ≤ ε := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (c / ε) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨k, fun n hn => ?_⟩
  have hp : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hn
  have hcp : c / ε ≤ (2 : ℝ) ^ n := hk.le.trans hp
  have hc : c ≤ (2 : ℝ) ^ n * ε := (div_le_iff₀ hε).mp hcp
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
  simpa only [mul_comm] using hc

/-- Positive relative density implies a nonempty intersection, even though
relative density itself is defined to be zero on empty intervals. -/
theorem nonempty_of_relativeDensity_pos {Ω : Type*} [DecidableEq Ω]
    (S I : Finset Ω) (h : 0 < KMS.relativeDensity S I) : (S ∩ I).Nonempty := by
  by_contra hn
  have he : S ∩ I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp [KMS.relativeDensity, he] at h

/-- The complete inverse implication from the explicit analytic lift theorem
to the dimension-uniform Grassmann theorem required by the v2 inverse. -/
theorem expansion_of_liftExpansion (h : LiftExpansionPrinciple) :
    KMS.ExpansionPrinciple := by
  intro ζ hζ hζ1
  obtain ⟨ε, hε, hε1, r, ellA, hA⟩ :=
    h (ζ / 2) (by positivity) (by linarith)
  obtain ⟨ellE, hEllE⟩ := exists_binary_ratio_threshold 1 (ζ / 8) (by positivity)
  refine ⟨ε, hε, hε1, max r 1, le_max_right _ _, max ellA ellE, ?_⟩
  intro ell hEll
  obtain ⟨nA, hnA⟩ := hA ell ((le_max_left _ _).trans hEll)
  obtain ⟨nE, hnE⟩ := exists_binary_ratio_threshold ((2 : ℝ) ^ ell)
    (ζ / 8) (by positivity)
  refine ⟨max nA nE, ?_⟩
  intro n hn S hS hret
  have hError : ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n ≤ ζ / 4 := by
    have he := hEllE ell ((le_max_right _ _).trans hEll)
    have hn' := hnE n ((le_max_right _ _).trans hn)
    rw [one_div] at he
    linarith
  by_contra hNo
  have hPseudo : GrassmannPseudorandom S r ε := by
    intro A B hAB hbudget
    by_contra hd
    have hd' : ε < KMS.relativeDensity S (KMS.interval A B) := lt_of_not_ge hd
    apply hNo
    exact ⟨A, B, hAB, hbudget.trans (le_max_left _ _),
      nonempty_of_relativeDensity_pos S _ (hε.trans hd'), hd'.le⟩
  have hLift : liftRetention S ≤ ζ / 2 :=
    hnA n ((le_max_left _ _).trans hn) S hS
      (grassmann_pseudorandom_lift S hPseudo hε.le)
  have hCmp := (abs_le.mp ((liftRetention_compare S hS).trans hError)).1
  linarith

end
end MaxCutGames.Inverse.KMSBasisComparison

namespace MaxCutGames.Inverse.KMSMomentToExpansion
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSMomentScalar KMSAnalytic KMSLowLevel

/-- Any proved dimension-independent upper moment with a finite local budget
supplies the exact ordered-basis expansion interface. -/
theorem liftExpansion_of_upperMoments
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (R ellMin : ℕ → ℕ)
    (hupper : ∀ r : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ ell : ℕ, ellMin r ≤ ell → ∀ n : ℕ,
      ∀ S : Finset (Vertex n ell), TuplePseudorandom S (R r) ε →
      ∀ i : ℕ, i ≤ r →
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
          C r * (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε) :
    LiftExpansionPrinciple := by
  intro ζ hζ _hζ1
  obtain ⟨r, _hr, ε, hε, hε1, hcut⟩ := exists_general_cutoff_parameters C hC hζ
  refine ⟨ε, hε, hε1, R r, ellMin r, ?_⟩
  intro ell hell
  refine ⟨0, ?_⟩
  intro n _hn S hS hPseudo
  have hf : IsBoolean (liftedIndicator S) := by
    intro X
    unfold liftedIndicator
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hδ : 0 ≤ liftDensity S := boolean_average_nonneg hf
  have hc := uniformNoise_bound_of_general_fourthMoments (liftedIndicator S) hf
    r (C r) ε (hC r) hε.le (hupper r ε hε.le hε1 ell hell n S hPseudo)
  have heq : (𝔼 X : BasisMap n ell,
      liftedIndicator S X * fullStepRetention S X) =
      𝔼 X : BasisMap n ell, liftedIndicator S X * uniformNoise (liftedIndicator S) X := by
    apply Finset.expect_congr rfl
    intro X _
    congr 1
    rw [fullStepRetention_eq_noise, uniformNoise_apply]
  apply liftRetention_le_of_correlation_le S hS ζ
  rw [heq]
  apply hc.trans
  change ((r + 1 : ℕ) * ((C r + 1) * ε ^ ((1 : ℝ) / 4)) +
    ((2 : ℝ) ^ (r + 1))⁻¹) * liftDensity S ≤ ζ * liftDensity S
  apply mul_le_mul_of_nonneg_right _ hδ
  exact hcut.trans (by linarith)

/-- Checked finite bridges and parameter choices reduce the full KMS expansion
principle to the displayed actual upper-moment estimate, and nothing weaker. -/
theorem expansion_of_upperMoments
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (R ellMin : ℕ → ℕ)
    (hupper : ∀ r : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ ell : ℕ, ellMin r ≤ ell → ∀ n : ℕ,
      ∀ S : Finset (Vertex n ell), TuplePseudorandom S (R r) ε →
      ∀ i : ℕ, i ≤ r →
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
          C r * (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε) :
    KMS.ExpansionPrinciple :=
  expansion_of_liftExpansion (liftExpansion_of_upperMoments C hC R ellMin hupper)

end
end MaxCutGames.Inverse.KMSMomentToExpansion

/-! The proved KMS Grassmann expansion principle. Its quantitative analytic
input is the actual basis-invariant fourth-moment theorem, whose proof uses
fixed-character and fixed-point inductions. No expansion, inverse,
rank-level, or missing-moment premise occurs in this theorem. -/

namespace MaxCutGames.Inverse.KMSExpansion
noncomputable section

/-- The KMS expansion theorem with constants independent of both dimensions
and with the ambient threshold chosen after the plane dimension. -/
theorem kms_expansion : KMS.ExpansionPrinciple := by
  apply KMSMomentToExpansion.expansion_of_upperMoments
    KMSMomentConstants.fourthMomentConstant
    KMSMomentConstants.fourthMomentConstant_nonneg
    (fun r => 2 * r) (fun r => r)
  intro r ε hε _hε1 ell hell n S hS i hi
  exact KMSMomentTheorem.lifted_fourth_moment_bound r ε hε ell hell n S hS i hi

end
end MaxCutGames.Inverse.KMSExpansion

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

theorem liftedFiber_subset_chart {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    liftedFiber f y ⊆ matrixChart ell m := by
  intro L hL
  obtain ⟨M, _, rfl⟩ := Finset.mem_image.mp hL
  exact (mem_matrixChart _).mpr ⟨M, rfl⟩

/-- The slice and the interval intersected with the chart correspond exactly.
The hypothesis states equality of the actual membership predicates. -/
theorem image_slice_points {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I) :
    S.points.image matrixVertex = I ∩ matrixChart ell m := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_inter.mpr ⟨(hS M).mp (Finset.mem_filter.mp hM).2,
      (mem_matrixChart _).mpr ⟨M, rfl⟩⟩
  · intro h
    obtain ⟨hI, hC⟩ := Finset.mem_inter.mp h
    obtain ⟨M, rfl⟩ := (mem_matrixChart _).mp hC
    exact Finset.mem_image.mpr ⟨M,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hS M).mpr hI⟩, rfl⟩

theorem image_slice_fiber {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    (S.points.filter fun M => f M = y).image matrixVertex =
      liftedFiber f y ∩ (I ∩ matrixChart ell m) := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hpoints, hfy⟩ := Finset.mem_filter.mp hM
    refine Finset.mem_inter.mpr ⟨(matrixVertex_mem_liftedFiber f y M).mpr hfy, ?_⟩
    rw [← image_slice_points S I hS]
    exact Finset.mem_image.mpr ⟨M, hpoints, rfl⟩
  · intro h
    obtain ⟨hf, hIC⟩ := Finset.mem_inter.mp h
    rw [← image_slice_points S I hS] at hIC
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hIC
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr
      ⟨hM, (matrixVertex_mem_liftedFiber f y M).mp hf⟩, rfl⟩

/-- Uniform agreement on a slice is the actual Grassmann fiber density in the
chart-intersected interval.  Empty sets are allowed on both sides of this
identity, with the standard zero-denominator convention. -/
theorem constantAgreement_eq_chart_density {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    S.constantAgreement f y =
      KMS.relativeDensity (liftedFiber f y) (I ∩ matrixChart ell m) := by
  unfold Slice.constantAgreement KMS.relativeDensity
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole]
  rw [← image_slice_fiber S I hS f y, ← image_slice_points S I hS]
  simp only [Finset.card_image_of_injective _ matrixVertex_injective]

theorem hasAffineSlice_of_dense_interval {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (S : Slice ell m) (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    {α : ℝ} {r : ℕ} (hrows : S.rows ≤ r) (hcolumns : S.columns ≤ r)
    (hne : (liftedFiber f y ∩ I).Nonempty)
    (hdense : α ≤ KMS.relativeDensity (liftedFiber f y) I) :
    HasAffineSlice f α r := by
  obtain ⟨hIC, hα⟩ := KMS.density_bound_passes_to_chart
    (liftedFiber f y) I (matrixChart ell m)
    (liftedFiber_subset_chart f y) hne hdense
  have hpoints : S.points.Nonempty := by
    rw [← image_slice_points S I hS] at hIC
    exact Finset.image_nonempty.mp hIC
  apply hasAffineSlice_of_constant f α r S hrows hcolumns hpoints y
  rw [constantAgreement_eq_chart_density S I hS f y]
  exact hα

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

/-! Every Grassmann interval has a chart description with exactly `dim A`
lower equations and `codim B` upper equations. This supplies the quantitative
row/column budget used when the expansion theorem selects an interval.
-/

namespace MaxCutGames.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem span_basis_values {ι : Type*} (A : Submodule K (X × Y))
    (b : Module.Basis ι K A) :
    Submodule.span K (Set.range fun i => (b i).val) = A := by
  have h := congrArg (Submodule.map A.subtype) b.span_eq
  simpa only [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
    ← Set.range_comp', Submodule.coe_subtype] using h

theorem lowerRows_basis {ι : Type*} (A : Submodule K (X × Y))
    (b : Module.Basis ι K A) :
    lowerRows (fun i => (b i).val.1) (fun i => (b i).val.2) = A := by
  exact span_basis_values A b

/-- Checking an annihilator basis suffices to test membership in a subspace. -/
theorem mem_iff_annihilator_basis {ι : Type*} (B : Submodule K (X × Y))
    (b : Module.Basis ι K B.dualAnnihilator) (x : X × Y) :
    x ∈ B ↔ ∀ i, (b i).val x = 0 := by
  constructor
  · intro hx i
    exact (Submodule.mem_dualAnnihilator (b i).val).mp (b i).property x hx
  · intro h
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff B x).mp
    intro φ hφ
    let ev : B.dualAnnihilator →ₗ[K] K :=
      (Module.Dual.eval K (X × Y) x).comp B.dualAnnihilator.subtype
    have hev : ev = 0 := b.ext (fun i => h i)
    exact congrArg (fun f : B.dualAnnihilator →ₗ[K] K => f ⟨φ, hφ⟩) hev

/-- Split a product functional into its two coordinate functionals. -/
theorem functional_coordinate_decomposition (φ : (X × Y) →ₗ[K] K) (x : X) (y : Y) :
    φ (x, y) = φ (x, 0) + φ (0, y) := by
  have h : (x, y) = (x, 0) + (0, y) := by simp
  rw [h, map_add]

theorem upperColumns_annihilator_basis {ι : Type*} (B : Submodule K (X × Y))
    (b : Module.Basis ι K B.dualAnnihilator) :
    upperColumns
      (fun i => -((b i).val.comp (LinearMap.inl K X Y)))
      (fun i => (b i).val.comp (LinearMap.inr K X Y)) = B := by
  ext x
  rw [mem_iff_annihilator_basis B b]
  simp only [upperColumns, Submodule.mem_iInf]
  change (∀ i, x ∈ LinearMap.ker
    (((b i).val.comp (LinearMap.inr K X Y)).comp (LinearMap.snd K X Y) -
      (-((b i).val.comp (LinearMap.inl K X Y))).comp (LinearMap.fst K X Y))) ↔ _
  constructor <;> intro h i
  · have hi := h i
    change (b i).val (0, x.2) - -(b i).val (x.1, 0) = 0 at hi
    rw [functional_coordinate_decomposition]
    simpa only [sub_neg_eq_add, add_comm] using hi
  · change (b i).val (0, x.2) - -(b i).val (x.1, 0) = 0
    have hi := h i
    rw [functional_coordinate_decomposition] at hi
    simpa only [sub_neg_eq_add, add_comm] using hi

/-- Coordinates for an arbitrary interval. There are exactly `dim A` rows and
`codim B` columns, so an interval order bound gives the required slice bound. -/
theorem exists_interval_coordinates [FiniteDimensional K X] [FiniteDimensional K Y]
    (A B : Submodule K (X × Y)) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → X) (s : Fin n_r → Y)
      (t : Fin n_c → X →ₗ[K] K) (q : Fin n_c → Y →ₗ[K] K),
      n_r = Module.finrank K A ∧ n_c = Module.finrank K ((X × Y) ⧸ B) ∧
      ∀ T : X →ₗ[K] Y,
        (A ≤ T.graph ∧ T.graph ≤ B) ↔
          ((∀ i, T (d i) = s i) ∧ (∀ j, (q j).comp T = t j)) := by
  let a := Module.finBasis K A
  let : Module.Free K B.dualAnnihilator := Module.Free.of_divisionRing K B.dualAnnihilator
  let b := Module.finBasis K B.dualAnnihilator
  refine ⟨Module.finrank K A, Module.finrank K B.dualAnnihilator,
    (fun i => (a i).val.1), (fun i => (a i).val.2),
    (fun i => -((b i).val.comp (LinearMap.inl K X Y))),
    (fun i => (b i).val.comp (LinearMap.inr K X Y)), rfl, ?_, ?_⟩
  · exact (Subspace.quotEquivAnnihilator B).finrank_eq.symm
  · intro T
    have h := interval_iff_slice (fun i => (a i).val.1) (fun i => (a i).val.2)
      (fun i => -((b i).val.comp (LinearMap.inl K X Y)))
      (fun i => (b i).val.comp (LinearMap.inr K X Y)) T
    simpa only [lowerRows_basis A a, upperColumns_annihilator_basis B b] using h

end MaxCutGames.Inverse.MatrixChart

/-! Extract actual vector-valued row/column data from an arbitrary interval.
The equation counts are the dimension/codimension of that interval, and no
homogeneity is imposed on the equation right-hand sides.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

theorem exists_matrix_interval_slice (A B : Submodule K ((ι → K) × (κ → K))) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → ι → K) (s : Fin n_r → κ → K)
      (t : Fin n_c → ι → K) (q : Fin n_c → κ → K),
      n_r = Module.finrank K A ∧
      n_c = Module.finrank K (((ι → K) × (κ → K)) ⧸ B) ∧
      ∀ M : Matrix ι κ K,
        (A ≤ matrixGraph M ∧ matrixGraph M ≤ B) ↔
          ((∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j)) := by
  classical
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_interval_coordinates A B
  choose tv htv using (fun j => dotFunctional_surjective (t j))
  choose qv hqv using (fun j => dotFunctional_surjective (q j))
  refine ⟨nr, nc, d, s, tv, qv, hnr, hnc, ?_⟩
  intro M
  rw [h M.vecMulLinear]
  have hj (j : Fin nc) : (q j).comp M.vecMulLinear = t j ↔ M *ᵥ qv j = tv j := by
    rw [← hqv j, ← htv j]
    exact column_equation_iff M (qv j) (tv j)
  simp only [Matrix.vecMulLinear_apply, hj]

end MaxCutGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixChartShortcode
attribute [-instance] _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete interface consumed by the shortcode assembly: an arbitrary
KMS interval becomes a `Shortcode.Slice`, with exact equation counts.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix

theorem exists_shortcode_slice {ell m : Nat}
    (A B : Submodule (ZMod 2) (KMS.Ambient (ell + m))) :
    ∃ S : Shortcode.Slice ell m,
      S.rows = Module.finrank (ZMod 2) A ∧
      S.columns = (ell + m) - Module.finrank (ZMod 2) B ∧
      ∀ M : Shortcode.Mat ell m,
        S.Contains M ↔ A ≤ (matrixVertex M).val ∧ (matrixVertex M).val ≤ B := by
  classical
  let e := coordinateJoin (ZMod 2) ell m
  let A' := A.comap e.toLinearMap
  let B' := B.comap e.toLinearMap
  have hA : Module.finrank (ZMod 2) A' = Module.finrank (ZMod 2) A := by
    rw [show A' = A.map e.symm.toLinearMap from
      Submodule.comap_equiv_eq_map_symm e A]
    exact e.symm.finrank_map_eq A
  have hB : Module.finrank (ZMod 2) B' = Module.finrank (ZMod 2) B := by
    rw [show B' = B.map e.symm.toLinearMap from
      Submodule.comap_equiv_eq_map_symm e B]
    exact e.symm.finrank_map_eq B
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_matrix_interval_slice A' B'
  have hE : Module.finrank (ZMod 2)
      ((Fin ell → ZMod 2) × (Fin m → ZMod 2)) = ell + m := by simp
  have hnc' : nc = (ell + m) - Module.finrank (ZMod 2) B := by
    simpa only [Submodule.finrank_quotient, hE, hB] using hnc
  let S : Shortcode.Slice ell m := ⟨nr, nc, d, s, q, t⟩
  refine ⟨S, hnr.trans hA, hnc', ?_⟩
  intro M
  have hcontains : S.Contains M ↔
      (∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j) := by
    constructor
    · rintro ⟨hr, hc⟩
      exact ⟨fun i => funext (hr i), hc⟩
    · rintro ⟨hr, hc⟩
      exact ⟨fun i j => congrFun (hr i) j, hc⟩
  rw [hcontains, ← h M]
  have hlow : A' ≤ matrixGraph M ↔ A ≤ (matrixVertex M).val := by
    change A.comap e.toLinearMap ≤ matrixGraph M ↔
      A ≤ (matrixGraph M).map e.toLinearMap
    have hh := Submodule.comap_le_comap_iff_of_surjective
      (f := e.toLinearMap) e.surjective (p := A)
      (q := (matrixGraph M).map e.toLinearMap)
    simpa only [Submodule.comap_map_eq_of_injective e.injective] using hh
  have hupp : matrixGraph M ≤ B' ↔ (matrixVertex M).val ≤ B :=
    Submodule.map_le_iff_le_comap.symm
  exact and_congr hlow hupp

end MaxCutGames.Inverse.MatrixChart

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped Classical
open Shortcode MatrixChart

/-- A common lower bound on both dimensions makes the zero-factor probability
as small as required. This threshold depends only on the acceptance parameter.
-/
theorem exists_zeroFactorMass_threshold {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ ell m : ℕ, N ≤ ell → N ≤ m → zeroFactorMass ell m ≤ η / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < η / 4 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨N, ?_⟩
  intro ell m hell hm
  have hpow (n : ℕ) (hn : N ≤ n) : ((2 : ℝ) ^ n)⁻¹ ≤ η / 4 := by
    have hmon : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    simpa only [one_div, inv_pow] using hmon.trans hN.le
  have hell' := hpow ell hell
  have hm' := hpow m hm
  have hnonneg : 0 ≤ ((2 : ℝ) ^ (ell + m))⁻¹ := by positivity
  unfold zeroFactorMass
  linarith

theorem inversePrinciple_of_expansion_and_chart
    (hKMS : KMS.ExpansionPrinciple) (hChart : ChartFiberRetention) :
    InversePrinciple := by
  intro η hη hη1
  obtain ⟨α, hαpos, hαone, r, hr, ellKMS, hKMSell⟩ :=
    hKMS (η / 4) (by positivity) (by linarith)
  obtain ⟨N, hN⟩ := exists_zeroFactorMass_threshold hη
  refine ⟨α, hαpos, hαone, r, hr, max ellKMS (max 1 N), ?_⟩
  intro ell hell
  have hellKMS : ellKMS ≤ ell := (le_max_left _ _).trans hell
  have hellone : 1 ≤ ell := (le_max_left 1 N).trans ((le_max_right _ _).trans hell)
  have hellN : N ≤ ell := (le_max_right 1 N).trans ((le_max_right _ _).trans hell)
  obtain ⟨nKMS, hKMSn⟩ := hKMSell ell hellKMS
  refine ⟨max nKMS (max 1 N), ?_⟩
  intro m hm f haccept
  have hmKMS : nKMS ≤ m := (le_max_left _ _).trans hm
  have hmone : 1 ≤ m := (le_max_left 1 N).trans ((le_max_right _ _).trans hm)
  have hmN : N ≤ m := (le_max_right 1 N).trans ((le_max_right _ _).trans hm)
  obtain ⟨y, hnonempty, hretention⟩ :=
    hChart hellone hmone η hη hη1 (hN ell m hellN hmN) f haccept
  obtain ⟨A, B, _hAB, hbudget, hintersection, hdense⟩ :=
    hKMSn (ell + m) (by omega) (liftedFiber f y) hnonempty hretention
  change Module.finrank (ZMod 2) A +
    ((ell + m) - Module.finrank (ZMod 2) B) ≤ r at hbudget
  obtain ⟨S, hrows, hcolumns, hcontains⟩ := exists_shortcode_slice A B
  apply hasAffineSlice_of_dense_interval f y (KMS.interval A B) S
  · intro M
    simpa only [KMS.interval, Finset.mem_filter, Finset.mem_univ, true_and]
      using hcontains M
  · omega
  · omega
  · exact hintersection
  · exact hdense

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

/-!
The exact sampling bridge from the vector factors in the shortcode test
to actual KMS Grassmann vertices. Every nonzero vector pair is sent to the
matrix `M + rankOne a l`, and this is a bijection onto the chart neighbors.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix
open Shortcode (Vector Mat rankOne)

variable {ell m : ℕ}

/-- The chart degree in the actual KMS vertex type. -/
theorem card_matrixVertexChartNeighbors (M : Mat ell m) :
    Nat.card (MatrixVertexChartNeighbors M) = (2 ^ ell - 1) * (2 ^ m - 1) := by
  classical
  rw [← Nat.card_congr (vectorFactorsEquivMatrixVertexChartNeighbors M)]
  simp only [NonzeroVectorFactors, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Shortcode.Vector, Fintype.card_fun, ZMod.card, Fintype.card_fin]

end MaxCutGames.Inverse.MatrixChart

/-!
The exact finite sampling conversion in the shortcode proof. Independent
nonzero binary vector factors parametrize chart neighbors bijectively; the full
Grassmann degree is twice the chart degree. These identities imply the exact
factor one half, including its averaging over a nonempty output fiber.
-/

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

/-- Relative density is uniform expectation on the predicate subtype. -/
theorem relativeDensity_filter_eq_expect {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : Finset Ω) (P : Ω → Prop) [DecidablePred P] :
    KMS.relativeDensity S (Finset.univ.filter P) =
      𝔼 x : {x : Ω // P x}, if x.val ∈ S then (1 : ℝ) else 0 := by
  unfold KMS.relativeDensity
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
    (fun x => if x ∈ S then (1 : ℝ) else 0)]
  rw [Finset.sum_boole, Fintype.card_subtype]
  have hsets : S ∩ Finset.univ.filter P =
      (Finset.univ.filter P).filter (fun x => x ∈ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hsets]

/-- Lifting a finite set along an injection preserves its uniform starting
law. No regularity or nonempty-neighbor hypothesis is needed for this step. -/
theorem retention_image {X : Type*} [DecidableEq X] {n ell : ℕ}
    (S : Finset X) (e : X → KMS.Vertex n ell) (he : Function.Injective e) :
    KMS.retention (S.image e) =
      S.expect fun x => KMS.relativeDensity (S.image e) (KMS.neighbors (e x)) := by
  have h : KMS.retention (S.image e) =
      (S.image e).expect fun L => KMS.relativeDensity (S.image e) (KMS.neighbors L) := by
    rw [Finset.expect_eq_sum_div_card]
    rfl
  rw [h]
  exact Finset.expect_image he.injOn

/-- At every starting matrix the full-neighbor retention is half the uniform
nonzero-factor retention. This follows from exact finite bijections and degree
counts; the zero-factor law is handled separately before this theorem. -/
theorem relativeDensity_neighbors_eq_nonzero_average_half {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) (M : Mat ell m) :
    KMS.relativeDensity (liftedFiber f y) (KMS.neighbors (matrixVertex M)) =
      (𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) / 2 := by
  let C := KMS.neighbors (matrixVertex M) ∩ matrixChart ell m
  have hC : C = Finset.univ.filter (fun L : KMS.Vertex (ell + m) ell =>
      KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m) := by
    ext L
    simp [C, KMS.neighbors]
  have hcardC : C.card = (2 ^ ell - 1) * (2 ^ m - 1) := by
    rw [hC]
    have h := card_matrixVertexChartNeighbors M
    simpa only [MatrixVertexChartNeighbors, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using h
  have hcard : (KMS.neighbors (matrixVertex M)).card = 2 * C.card := by
    rw [hcardC]
    exact card_full_neighbors_twice M
  have hnumerator : liftedFiber f y ∩ C =
      liftedFiber f y ∩ KMS.neighbors (matrixVertex M) :=
    KMS.inter_chart_eq _ _ _ (liftedFiber_subset_chart f y)
  have hhalf : KMS.relativeDensity (liftedFiber f y)
      (KMS.neighbors (matrixVertex M)) =
        KMS.relativeDensity (liftedFiber f y) C / 2 := by
    unfold KMS.relativeDensity
    rw [hcard, ← hnumerator, Nat.cast_mul, Nat.cast_ofNat,
      mul_comm (2 : ℝ), div_mul_eq_div_div]
  rw [hhalf]
  congr 1
  rw [hC]
  trans (𝔼 L : MatrixVertexChartNeighbors M,
    if L.val ∈ liftedFiber f y then (1 : ℝ) else 0)
  · exact relativeDensity_filter_eq_expect (liftedFiber f y)
      (fun L => KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m)
  symm
  apply Fintype.expect_equiv (vectorFactorsEquivMatrixVertexChartNeighbors M)
  intro p
  simp only [vectorFactorsEquivMatrixVertexChartNeighbors_apply,
    matrixVertex_mem_liftedFiber]

/-- The exact Grassmann retention of an output fiber is half its retention
under independent uniform nonzero vector factors. Empty fibers and degenerate
dimensions also satisfy this identity with zero-expectation conventions. -/
theorem liftedFiber_retention_eq_half {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    KMS.retention (liftedFiber f y) =
      (𝔼 M ∈ matrixFiber f y, 𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) / 2 := by
  unfold liftedFiber
  rw [retention_image _ _ matrixVertex_injective]
  change (𝔼 M ∈ matrixFiber f y,
    KMS.relativeDensity (liftedFiber f y) (KMS.neighbors (matrixVertex M))) = _
  simp_rw [relativeDensity_neighbors_eq_nonzero_average_half]
  exact (Finset.expect_div _ _ _).symm

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

/-!
Finite equality-fiber extraction for the Grassmann-to-matrix route.

These elementary results do not assume a shortcode inverse theorem.  They
separate the equality test, the retention of a nonempty output fiber, and the
subsequent removal of zero perturbation factors.  The dimension-uniform
Grassmann expansion theorem remains a separate mathematical obligation.
-/

namespace MaxCutGames.Inverse.EqualityFiber

noncomputable section

open scoped BigOperators Classical
open MaxCutGames.Foundations.Information

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem sum_fiberMass (p : X → ℝ) (f : X → Y) :
    ∑ y, fiberMass p f y = ∑ x, p x := by
  classical
  unfold fiberMass
  rw [Finset.sum_comm]
  simp

omit [Fintype Y] in
theorem fiberMass_nonneg (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : X → Y) (y : Y) : 0 ≤ fiberMass p f y := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split
  · exact hp x
  · exact le_rfl

omit [Fintype Y] in
theorem fiberFlow_nonneg (p : X → ℝ) (k : X → X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hk : ∀ x x', 0 ≤ k x x')
    (f : X → Y) (y : Y) : 0 ≤ fiberFlow p k f y := by
  classical
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (hp x)
  apply Finset.sum_nonneg
  intro x' _
  apply mul_nonneg (hk x x')
  split <;> norm_num

omit [Fintype Y] in
theorem fiberFlow_le_mass (p : X → ℝ) (k : X → X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hk : ∀ x, IsProbability (k x))
    (f : X → Y) (y : Y) : fiberFlow p k f y ≤ fiberMass p f y := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases h : f x = y
  · simp only [h, true_and, ite_true, if_true]
    have hinner : (∑ x', k x x' * if f x' = y then 1 else 0) ≤ 1 := by
      calc
        _ ≤ ∑ x', k x x' := by
          apply Finset.sum_le_sum
          intro x' _
          split <;> simp [(hk x).1 x']
        _ = 1 := (hk x).2
    simpa using mul_le_mul_of_nonneg_left hinner (hp x)
  · simp [h]

private theorem sum_sameFiber_indicator_inline_EqualityFiber (a b : Y) :
    (∑ y, if a = y ∧ b = y then (1 : ℝ) else 0) =
      if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro y _
    have h' : ¬ (a = y ∧ b = y) := fun hy => h (hy.1.trans hy.2.symm)
    simp [h']

theorem sum_fiberFlow (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) :
    ∑ y, fiberFlow p k f y = equalityAcceptance p k f := by
  classical
  unfold fiberFlow equalityAcceptance
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x' _
  rw [← Finset.mul_sum, sum_sameFiber_indicator_inline_EqualityFiber]

/-- A probability-weighted average at least `η` contains a positive-weight
fiber whose unnormalized flow is at least `η` times its mass. -/
theorem exists_positive_mass_le_flow (mass flow : Y → ℝ)
    (hmass : IsProbability mass) (_hflow : ∀ y, 0 ≤ flow y)
    (hzero : ∀ y, mass y = 0 → flow y = 0)
    {η : ℝ} (haccept : η ≤ ∑ y, flow y) :
    ∃ y, 0 < mass y ∧ η * mass y ≤ flow y := by
  classical
  by_contra hnone
  have hless (y : Y) (hy : 0 < mass y) : flow y < η * mass y := by
    apply lt_of_not_ge
    intro h
    exact hnone ⟨y, hy, h⟩
  have hle (y : Y) : flow y ≤ η * mass y := by
    rcases eq_or_lt_of_le (hmass.1 y) with hz | hz
    · simp [← hz, hzero y hz.symm]
    · exact (hless y hz).le
  have hex : ∃ y, 0 < mass y := by
    by_contra hn
    have hall (y : Y) : mass y = 0 := le_antisymm (le_of_not_gt (fun hy => hn ⟨y, hy⟩))
      (hmass.1 y)
    have := hmass.2
    simp [hall] at this
  obtain ⟨y, hy⟩ := hex
  have hstrict : (∑ y, flow y) < ∑ y, η * mass y := by
    exact Finset.sum_lt_sum (fun y _ => hle y) ⟨y, Finset.mem_univ y, hless y hy⟩
  rw [← Finset.mul_sum, hmass.2, mul_one] at hstrict
  exact (not_lt_of_ge haccept) hstrict

/-- Equality acceptance supplies a nonempty output fiber with the claimed
retention.  The kernel is the actual sampling kernel; no conditioned sampling
law is silently substituted. -/
theorem exists_fiber_retention (p : X → ℝ) (k : X → X → ℝ)
    (hp : IsProbability p) (hk : ∀ x, IsProbability (k x))
    (f : X → Y) {η : ℝ} (haccept : η ≤ equalityAcceptance p k f) :
    ∃ y, 0 < fiberMass p f y ∧ η ≤ fiberFlow p k f y / fiberMass p f y := by
  have hmass : IsProbability (fiberMass p f) :=
    ⟨fiberMass_nonneg p hp.1 f, (sum_fiberMass p f).trans hp.2⟩
  have hflow := fiberFlow_nonneg p k hp.1 (fun x => (hk x).1) f
  have hzero (y : Y) (hy : fiberMass p f y = 0) : fiberFlow p k f y = 0 := by
    apply le_antisymm _ (hflow y)
    simpa [hy] using fiberFlow_le_mass p k hp.1 hk f y
  obtain ⟨y, hy, hret⟩ := exists_positive_mass_le_flow (fiberMass p f)
    (fiberFlow p k f) hmass hflow hzero (by simpa [sum_fiberFlow] using haccept)
  exact ⟨y, hy, (le_div_iff₀ hy).2 hret⟩

/-- Removing a self-loop mass `p₀ ≤ η/2` leaves retention at least `η/2`.
This is the precise algebra needed when one or both rank-one factors may be
zero in the unconditioned test. -/
theorem nonzero_retention_ge_half {η p₀ R : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hp₀ : 0 ≤ p₀) (hp₀η : p₀ ≤ η / 2)
    (haccept : η ≤ p₀ + (1 - p₀) * R) : η / 2 ≤ R := by
  have hp₀1 : p₀ < 1 := by linarith
  have hden : 0 < 1 - p₀ := by linarith
  have hprod : η / 2 * (1 - p₀) ≤ (1 - p₀) * R := by nlinarith
  nlinarith

end
end MaxCutGames.Inverse.EqualityFiber

/-! The actual uniform matrix test supplies a positive-mass output fiber with
large retention. The transition kernel averages independent full vectors,
including zero, exactly as in the shortcode theorem. -/

namespace MaxCutGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Foundations.Information

theorem matrixWeight_probability (ell m : ℕ) :
    IsProbability (matrixWeight (ell := ell) (m := m)) := by
  constructor
  · intro M
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · have hcard : (Fintype.card (Mat ell m) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [matrixWeight, hcard]

theorem matrixKernel_nonneg {ell m : ℕ} (M N : Mat ell m) :
    0 ≤ matrixKernel M N := by
  apply Finset.expect_nonneg
  intro a _
  apply Finset.expect_nonneg
  intro l _
  split <;> norm_num

theorem matrixKernel_probability {ell m : ℕ} (M : Mat ell m) :
    IsProbability (matrixKernel M) := by
  refine ⟨matrixKernel_nonneg M, ?_⟩
  unfold matrixKernel
  rw [← Finset.expect_sum_comm]
  have hpoint (a : Vector ell) :
      (∑ N : Mat ell m, 𝔼 l : Vector m,
        if N = M + rankOne a l then (1 : ℝ) else 0) = 1 := by
    rw [← Finset.expect_sum_comm]
    simp
  simp only [hpoint]
  simp

theorem matrixKernel_equality {ell m : ℕ} (f : Mat ell m → Vector ell)
    (M : Mat ell m) :
    (∑ N, matrixKernel M N * if f M = f N then (1 : ℝ) else 0) =
      𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then 1 else 0 := by
  simp only [matrixKernel, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro a _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro l _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

theorem equalityAcceptance_eq_kernel {ell m : ℕ} (f : Mat ell m → Vector ell) :
    equalityAcceptance f = EqualityFiber.equalityAcceptance matrixWeight matrixKernel f := by
  calc
    equalityAcceptance f = ∑ M, matrixWeight M *
        (𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then (1 : ℝ) else 0) := by
      unfold equalityAcceptance matrixWeight
      rw [Fintype.expect_eq_sum_div_card]
      simp only [div_eq_mul_inv, ← Finset.mul_sum, mul_comm]
    _ = EqualityFiber.equalityAcceptance matrixWeight matrixKernel f := by
      unfold EqualityFiber.equalityAcceptance
      apply Finset.sum_congr rfl
      intro M _
      congr 1
      convert (matrixKernel_equality f M).symm using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro N _
      by_cases h : f M = f N <;> simp [h]

/-- Positive-mass fibers, with their actual transition flow, are obtained from
the full uniform factor law. This is the first step before conditioning both
factors to be nonzero and passing to Grassmann neighbors. -/
theorem exists_output_fiber {ell m : ℕ} (f : Mat ell m → Vector ell)
    {η : ℝ} (haccept : η ≤ equalityAcceptance f) :
    ∃ y : Vector ell, 0 < EqualityFiber.fiberMass matrixWeight f y ∧
      η ≤ EqualityFiber.fiberFlow matrixWeight matrixKernel f y /
        EqualityFiber.fiberMass matrixWeight f y := by
  apply EqualityFiber.exists_fiber_retention matrixWeight matrixKernel
    (matrixWeight_probability ell m) matrixKernel_probability f
  rwa [← equalityAcceptance_eq_kernel]

end
end MaxCutGames.Inverse.Shortcode

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_ShortcodeFiberSampling
attribute [-instance] _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite output-fiber sampling identities. These connect the weighted
kernel extraction to uniform sampling of a matrix in the actual output fiber.
-/

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MaxCutGames.Foundations.Information

theorem matrixKernel_average {ell m : ℕ} (M : Mat ell m) (g : Mat ell m → ℝ) :
    (∑ N, matrixKernel M N * g N) = 𝔼 a, 𝔼 l, g (M + rankOne a l) := by
  simp only [matrixKernel, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro a _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro l _
  simp [ite_mul]

theorem fiberMass_eq_card {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    EqualityFiber.fiberMass matrixWeight f y =
      ((matrixFiber f y).card : ℝ) / Fintype.card (Mat ell m) := by
  unfold EqualityFiber.fiberMass
  calc
    _ = ∑ M ∈ matrixFiber f y, matrixWeight M := by
      rw [matrixFiber, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro M _
      by_cases h : f M = y <;> simp [h]
    _ = _ := by simp [matrixWeight, div_eq_mul_inv]

theorem fiberMass_pos_iff {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    0 < EqualityFiber.fiberMass matrixWeight f y ↔ (matrixFiber f y).Nonempty := by
  rw [fiberMass_eq_card]
  have hcard : (0 : ℝ) < Fintype.card (Mat ell m) := by
    exact_mod_cast Fintype.card_pos
  rw [div_pos_iff_of_pos_right hcard, Nat.cast_pos, Finset.card_pos]

theorem fiberFlow_eq {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    EqualityFiber.fiberFlow matrixWeight matrixKernel f y =
      (∑ M ∈ matrixFiber f y,
        𝔼 a, 𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) /
        Fintype.card (Mat ell m) := by
  unfold EqualityFiber.fiberFlow
  simp_rw [matrixKernel_average]
  rw [div_eq_mul_inv, Finset.sum_mul]
  rw [matrixFiber, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h : f M = y
  · simp [h, matrixWeight, mul_comm]
  · simp [h]

theorem fiber_retention_eq_factor_average {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    EqualityFiber.fiberFlow matrixWeight matrixKernel f y /
      EqualityFiber.fiberMass matrixWeight f y =
        𝔼 a, 𝔼 l, fiberFactorRetention f y a l := by
  rw [fiberFlow_eq, fiberMass_eq_card]
  have hcard : (Fintype.card (Mat ell m) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hswap : (𝔼 a, 𝔼 l, fiberFactorRetention f y a l) =
      (matrixFiber f y).expect (fun M =>
        𝔼 a, 𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) := by
    unfold fiberFactorRetention
    calc
      _ = 𝔼 a, (matrixFiber f y).expect (fun M =>
          𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) := by
        apply Finset.expect_congr rfl
        intro a _
        rw [Finset.expect_comm]
      _ = _ := Finset.expect_comm _ _ _
  rw [hswap, Finset.expect_eq_sum_div_card]
  simp [div_div_div_cancel_right₀ hcard]

theorem fiberFactorRetention_zero_left {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (hne : (matrixFiber f y).Nonempty) (l : Vector m) :
    fiberFactorRetention f y 0 l = 1 := by
  unfold fiberFactorRetention
  have hpoint (M : Mat ell m) (hM : M ∈ matrixFiber f y) :
      (if f (M + rankOne (0 : Vector ell) l) = y then (1 : ℝ) else 0) = 1 := by
    have hy := (Finset.mem_filter.mp hM).2
    simp [hy]
  rw [Finset.expect_congr rfl hpoint, Finset.expect_const hne]

theorem fiberFactorRetention_zero_right {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (hne : (matrixFiber f y).Nonempty) (a : Vector ell) :
    fiberFactorRetention f y a 0 = 1 := by
  unfold fiberFactorRetention
  have hpoint (M : Mat ell m) (hM : M ∈ matrixFiber f y) :
      (if f (M + rankOne a (0 : Vector m)) = y then (1 : ℝ) else 0) = 1 := by
    have hy := (Finset.mem_filter.mp hM).2
    simp [hy]
  rw [Finset.expect_congr rfl hpoint, Finset.expect_const hne]

/-- A nonempty actual output fiber whose retention under the full factor law
is at least the original equality acceptance threshold. -/
theorem exists_output_fiber_factor_retention {ell m : ℕ}
    (f : Mat ell m → Vector ell) {η : ℝ} (haccept : η ≤ equalityAcceptance f) :
    ∃ y, (matrixFiber f y).Nonempty ∧ η ≤ 𝔼 a, 𝔼 l, fiberFactorRetention f y a l := by
  obtain ⟨y, hy, hret⟩ := Shortcode.exists_output_fiber f haccept
  exact ⟨y, (fiberMass_pos_iff f y).mp hy,
    by simpa only [fiber_retention_eq_factor_average] using hret⟩

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode

/-- Exact decomposition of a uniform two-factor law with a self-loop on either
zero factor. No nonemptiness is required of the nonzero subtypes. -/
theorem uniform_pair_mixture {A B : Type*} [Fintype A] [Fintype B]
    [Zero A] [Zero B] (h : A → B → ℝ)
    (hleft : ∀ b, h 0 b = 1) (hright : ∀ a, h a 0 = 1) :
    (𝔼 a, 𝔼 b, h a b) =
      (Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹ +
      (1 - ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹)) *
        (𝔼 p : {a : A // a ≠ 0} × {b : B // b ≠ 0}, h p.1.val p.2.val) := by
  let R : ℝ := 𝔼 p : {a : A // a ≠ 0} × {b : B // b ≠ 0},
    h p.1.val p.2.val
  have : Nonempty A := ⟨0⟩
  have : Nonempty B := ⟨0⟩
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hNA : (Fintype.card {a : A // a ≠ 0} : ℝ) =
      (Fintype.card A : ℝ) - 1 := by
    have hs := Fintype.sum_eq_add_sum_subtype_ne (fun _ : A => (1 : ℝ)) 0
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
    linarith
  have hNB : (Fintype.card {b : B // b ≠ 0} : ℝ) =
      (Fintype.card B : ℝ) - 1 := by
    have hs := Fintype.sum_eq_add_sum_subtype_ne (fun _ : B => (1 : ℝ)) 0
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
    linarith
  have hNZ : (∑ a : {a : A // a ≠ 0}, ∑ b : {b : B // b ≠ 0}, h a.val b.val) =
      (Fintype.card {a : A // a ≠ 0} : ℝ) *
        (Fintype.card {b : B // b ≠ 0} : ℝ) * R := by
    simpa only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type] using
      (Fintype.card_mul_expect
        (fun p : {a : A // a ≠ 0} × {b : B // b ≠ 0} => h p.1.val p.2.val)).symm
  have hinner (a : A) : (∑ b : B, h a b) =
      1 + ∑ b : {b : B // b ≠ 0}, h a b.val := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 0, hright]
  have hsum : (∑ a : A, ∑ b : B, h a b) =
      (Fintype.card B : ℝ) + (Fintype.card {a : A // a ≠ 0} : ℝ) +
        (Fintype.card {a : A // a ≠ 0} : ℝ) *
          (Fintype.card {b : B // b ≠ 0} : ℝ) * R := by
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun a : A => ∑ b : B, h a b) 0]
    simp only [hleft, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp_rw [hinner]
    rw [Finset.sum_add_distrib, hNZ]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  have hfull : (Fintype.card A : ℝ) * (Fintype.card B : ℝ) *
      (𝔼 a, 𝔼 b, h a b) = ∑ a, ∑ b, h a b := by
    calc
      _ = (Fintype.card B : ℝ) *
          ((Fintype.card A : ℝ) * (𝔼 a, 𝔼 b, h a b)) := by ring
      _ = (Fintype.card B : ℝ) * (∑ a, 𝔼 b, h a b) := by
        rw [Fintype.card_mul_expect]
      _ = _ := by
        rw [Finset.mul_sum]
        simp_rw [Fintype.card_mul_expect]
  have hbalance : (Fintype.card A : ℝ) * (Fintype.card B : ℝ) *
      (𝔼 a, 𝔼 b, h a b) =
      (Fintype.card A : ℝ) + (Fintype.card B : ℝ) - 1 +
        ((Fintype.card A : ℝ) - 1) * ((Fintype.card B : ℝ) - 1) * R := by
    rw [hfull, hsum, hNA, hNB]
    ring
  apply mul_left_cancel₀ (mul_ne_zero hA hB)
  rw [hbalance]
  change _ = (Fintype.card A : ℝ) * (Fintype.card B : ℝ) *
    ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
      (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹ +
      (1 - ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹)) * R)
  field_simp [hA, hB]
  ring

private theorem vector_card_real_inline_ShortcodeFiberConditioning (n : ℕ) :
    (Fintype.card (Vector n) : ℝ) = (2 : ℝ) ^ n := by
  simp [Shortcode.Vector, F2]

private theorem binary_zero_mass_nonneg_inline_ShortcodeFiberConditioning (ell m : ℕ) :
    0 ≤ ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ -
      ((2 : ℝ) ^ (ell + m))⁻¹ := by
  have ha : 0 ≤ ((2 : ℝ) ^ ell)⁻¹ := by positivity
  have hb : 0 ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
  have hb1 : ((2 : ℝ) ^ m)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [pow_add, mul_inv]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hb1)]

/-- The actual equality test has a nonempty output fiber retaining at least
`η/2` after both factors are conditioned to be nonzero. The displayed order
samples a uniform matrix in that fiber first, as required by the Grassmann
neighbor correspondence. -/
theorem conditioned_output_fiber {ell m : ℕ}
    (f : Mat ell m → Vector ell) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hzero : ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ -
      ((2 : ℝ) ^ (ell + m))⁻¹ ≤ η / 2)
    (haccept : η ≤ equalityAcceptance f) :
    ∃ y, (matrixFiber f y).Nonempty ∧
      η / 2 ≤ (matrixFiber f y).expect (fun M =>
        𝔼 p : {a : Vector ell // a ≠ 0} × {l : Vector m // l ≠ 0},
          if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) := by
  obtain ⟨y, hy, hret⟩ := exists_output_fiber_factor_retention f haccept
  refine ⟨y, hy, ?_⟩
  have hmix := uniform_pair_mixture (fiberFactorRetention f y)
    (fiberFactorRetention_zero_left f y hy) (fiberFactorRetention_zero_right f y hy)
  simp only [vector_card_real_inline_ShortcodeFiberConditioning, ← mul_inv, ← pow_add] at hmix
  have hconditioned := EqualityFiber.nonzero_retention_ge_half hη hη1
    (binary_zero_mass_nonneg_inline_ShortcodeFiberConditioning ell m) hzero (hmix ▸ hret)
  apply hconditioned.trans
  apply le_of_eq
  unfold fiberFactorRetention
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro M _
  apply Finset.expect_congr (by ext p; simp)
  intro p _
  rfl

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

/-- The finite sampling bridge has no expansion or inverse premise. -/
theorem chartFiberRetention : ChartFiberRetention := by
  intro ell m _hell _hm η hη hη1 hzero f haccept
  obtain ⟨y, hnonempty, hretention⟩ :=
    conditioned_output_fiber f hη hη1 hzero haccept
  refine ⟨y, ?_, ?_⟩
  · exact Finset.image_nonempty.mpr hnonempty
  · rw [liftedFiber_retention_eq_half]
    have h : η / 2 ≤ (𝔼 M ∈ matrixFiber f y, 𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) := hretention
    linarith

/-- Conditional Grassmann-to-matrix implication, preserving all quantifiers
and the affine target. KMS expansion is the sole remaining displayed premise.
-/
theorem inversePrinciple_of_expansion (hKMS : KMS.ExpansionPrinciple) :
    Shortcode.InversePrinciple :=
  inversePrinciple_of_expansion_and_chart hKMS chartFiberRetention

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

/-! The unconditional affine matrix inverse theorem. The Grassmann theorem,
chart retention, zero-factor correction, output-fiber extraction, and affine
row/column slice construction are all proved in its dependency chain. -/

namespace MaxCutGames.Inverse.ShortcodeTheorem
noncomputable section

/-- Full-factor sampling includes zero. The conclusion retains an affine
intercept and applies to arbitrary matrix labelings without a folding premise. -/
theorem inversePrinciple_oai : Shortcode.InversePrinciple :=
  ShortcodeFromGrassmann.inversePrinciple_of_expansion KMSExpansion.kms_expansion

end
end MaxCutGames.Inverse.ShortcodeTheorem

end OAI
end

theorem solution : type_of% @OAI.MaxCutGames.Inverse.ShortcodeTheorem.inversePrinciple_oai := @OAI.MaxCutGames.Inverse.ShortcodeTheorem.inversePrinciple_oai
