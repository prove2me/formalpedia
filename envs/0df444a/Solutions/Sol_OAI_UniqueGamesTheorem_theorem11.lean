-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.theorem11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:10:20.015229+00:00
-- url     : https://prove2.me/submissions/87b1639c-4214-48c1-9e7b-dc2a8ec849bc

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U012
import Theorems.Thm_OAI_UniqueGamesTheorem_Decoder_ActualMatrixContradiction_contradiction
import Theorems.Thm_OAI_UniqueGamesTheorem_Inverse_ShortcodeTheorem_inversePrinciple

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_ParityLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual splitting of linear-map questions and their uniform laws. -/

noncomputable section

open scoped BigOperators

namespace UniqueGamesTheorem.Fourier.SplitMaps

variable {K E C D : Type*} [CommSemiring K]
    [AddCommMonoid E] [Module K E]
    [AddCommMonoid C] [Module K C]
    [AddCommMonoid D] [Module K D]

theorem expect_codomain_product
    [Fintype (E →ₗ[K] C × D)] [Fintype (E →ₗ[K] C)] [Fintype (E →ₗ[K] D)]
    {A : Type*} [AddCommMonoid A] [Module ℚ≥0 A]
    (f : (E →ₗ[K] C × D) → A) :
    (𝔼 X, f X) = 𝔼 (X : E →ₗ[K] C), 𝔼 (Z : E →ₗ[K] D), f (X.prod Z) := by
  classical
  rw [Fintype.expect_equiv codomainSplit.toEquiv f
    (fun p => f (p.1.prod p.2)) (by intro X; rfl)]
  rw [← Finset.univ_product_univ, Finset.expect_product]

end UniqueGamesTheorem.Fourier.SplitMaps

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_BinaryLinear
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact transport from XOR bit vectors to vector spaces over `ZMod 2`. -/
namespace UniqueGamesTheorem.Integration.BinaryLinear

open BinaryCoordinates

theorem finrank_vector (n : Nat) : Module.finrank F2 (Vector n) = n := by
  simp [Vector]

end UniqueGamesTheorem.Integration.BinaryLinear

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixCharactersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open UniqueGamesTheorem.Fourier.MatrixCharacters

section LinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

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

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixFourier

end

end

section

/-! Actual binary matrix and linear-map parity used in Lemma 5.3. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixParity

open UniqueGamesTheorem.Integration.BinaryLinear
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

end UniqueGamesTheorem.Fourier.MatrixParity

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixEnergy
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Fourier.MatrixEnergy

open scoped BigOperators

variable {Q : Type*} {I : Q → Type*} [Fintype Q] [∀ q, Fintype (I q)]

section LinearMaps

open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem colorIndicator_partition {X Y : Type*} [Fintype Y]
    (label : X → Y) (x : X) : ∑ y, colorIndicator label y x ^ 2 = 1 := by
  classical
  simp [colorIndicator, eq_comm]

/-- Parseval for all color indicators sums to exactly one, with the correct
uniform primal normalization and counting measure on Fourier indices. -/
theorem colorIndicator_parseval {Y : Type*} [Fintype Y]
    (label : (E →ₗ[F2] F) → Y) :
    (∑ y, ∑ S : F →ₗ[F2] E, linearCoeff (colorIndicator label y) S ^ 2) = 1 := by
  simp_rw [linear_parseval]
  rw [← Finset.expect_sum_comm]
  simp_rw [colorIndicator_partition]
  exact Fintype.expect_const 1

theorem labelingCoeff_energy_one {Y : Type*} [Fintype Y]
    (weight : Q → ℝ) (label : Q → (E →ₗ[F2] F) → Y)
    (hnorm : ∑ q, weight q = 1) :
    energy (fun qy : Q × Y => weight qy.1) (labelingCoeff label) = 1 := by
  classical
  calc
    energy (fun qy : Q × Y => weight qy.1) (labelingCoeff label) =
        ∑ q, weight q * (∑ y, ∑ S : F →ₗ[F2] E,
          linearCoeff (colorIndicator (label q) y) S ^ 2) := by
      simp only [energy, labelingCoeff, Fintype.sum_prod_type, Finset.mul_sum]
    _ = ∑ q, weight q := by simp only [colorIndicator_parseval, mul_one]
    _ = 1 := hnorm

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixEnergy

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixNoiseLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual rank-one averaging operator on finite binary matrix spaces.
The outer weights describe any finite law for `v`; the functional `ℓ` is
uniform. Normalization is needed for eigenvalue bounds, not diagonalization. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace UniqueGamesTheorem.Fourier.MatrixNoise

open scoped BigOperators Matrix
open UniqueGamesTheorem.Integration.BinaryLinear (Vector)
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

section LinearMaps

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

theorem linearNoiseEigenvalue_nonneg [Fintype F] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (hw : ∀ v, 0 ≤ weight v) :
    0 ≤ linearNoiseEigenvalue weight S := by
  unfold linearNoiseEigenvalue
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> simp [hw]

theorem linearNoiseEigenvalue_le_one [Fintype F] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (hw : ∀ v, 0 ≤ weight v)
    (hnorm : ∑ v, weight v = 1) : linearNoiseEigenvalue weight S ≤ 1 := by
  unfold linearNoiseEigenvalue
  calc
    (∑ v, weight v * if S v = 0 then 1 else 0) ≤ ∑ v, weight v := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> simp [hw]
    _ = 1 := hnorm

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
    _ = _ := mul_right_comm _ _ _

/-- The actual operator's quadratic form is precisely its weighted Fourier mass. -/
theorem linearRealNoiseOperator_energy (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * linearRealNoiseOperator weight f X) =
      ∑ S : F →ₗ[F2] E, linearNoiseEigenvalue weight S * linearCoeff f S ^ 2 := by
  rw [linearRealNoiseOperator_pairing]
  simp only [pow_two, mul_assoc]

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixNoise

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_ConcatenationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Gadget.EmbeddedConditional

open scoped BigOperators

variable {k P R B Z M : Type*} [Ring k]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup B] [Module k B] [Fintype B]
variable [AddCommMonoid M] [Module ℚ≥0 M]

/-- Exact conditional uniformity for an embedded carrier of logical shifts.
No injectivity of the embedding is needed for this averaging statement. -/
theorem expect_uniform_output_embedded (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (D : P → Z) (hD : ∀ u h, D (u + e h) = D u)
    (f : B → Z → M) :
    (𝔼 u, f (C u) (D u)) = 𝔼 u, 𝔼 b : B, f b (D u) := by
  classical
  have hs (b : B) :
      (𝔼 u, f (C u + b) (D u)) = 𝔼 u, f (C u) (D u) := by
    obtain ⟨h, rfl⟩ := hlam b
    apply Fintype.expect_equiv (Equiv.addRight (e h))
    intro u
    simp only [Equiv.coe_addRight, hC, hD]
  calc
    (𝔼 u, f (C u) (D u)) = 𝔼 b : B, 𝔼 u, f (C u + b) (D u) := by
      simp only [hs, Fintype.expect_const]
    _ = 𝔼 u, 𝔼 b : B, f (C u + b) (D u) := Finset.expect_comm _ _ _
    _ = 𝔼 u, 𝔼 b : B, f b (D u) := by
      apply Finset.expect_congr rfl
      intro u _
      apply Fintype.expect_equiv (Equiv.addLeft (C u))
      intro b
      rfl

/-- Unconditional uniformity is the constant-observable instance. -/
theorem expect_equivariant_output (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h) (f : B → M) :
    (𝔼 u, f (C u)) = 𝔼 b : B, f b := by
  have he := expect_uniform_output_embedded e lam hlam C hC
    (fun _ => ()) (fun _ _ => rfl) (fun b _ => f b)
  simpa only [Fintype.expect_const] using he

/-- Surjective linear maps send uniform finite input to uniform output. -/
theorem expect_linear_surjective (f : P →ₗ[k] B) (hf : Function.Surjective f)
    (test : B → M) : (𝔼 u, test (f u)) = 𝔼 b : B, test b := by
  apply expect_equivariant_output (LinearMap.id : P →ₗ[k] P) f hf f
  intro u h
  exact f.map_add u h

end UniqueGamesTheorem.Gadget.EmbeddedConditional

end

section

namespace UniqueGamesTheorem.Gadget.Enlargement

open scoped BigOperators Classical

noncomputable section

/-- A union bound without independence assumptions. -/
theorem probability_exists_le_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (p : I → Ω → Prop) :
    probability (fun x => ∃ i, p i x) ≤ ∑ i, probability (p i) := by
  classical
  have heq : (Finset.univ.filter fun x => ∃ i, p i x) =
      Finset.univ.biUnion (fun i => Finset.univ.filter (p i)) := by
    ext x
    simp
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [heq, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_biUnion_le (s := (Finset.univ : Finset I))
    (t := fun i => Finset.univ.filter (p i)))

/-- Equal-size fibers determine the exact probability of every target event. -/
theorem probability_preimage_of_fibers {Ω T : Type*} [Fintype Ω] [Fintype T]
    [Nonempty Ω] [Nonempty T] (f : Ω → T)
    (hf : ∀ x y : T, Nat.card {a : Ω // f a = x} = Nat.card {a : Ω // f a = y})
    (p : T → Prop) : probability (fun a => p (f a)) = probability p := by
  classical
  let t₀ : T := Classical.choice inferInstance
  let c := (Finset.univ.filter fun a => f a = t₀).card
  have hfc (x : T) : (Finset.univ.filter fun a => f a = x).card = c := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hf x t₀
  have hΩ : Fintype.card Ω = Fintype.card T * c := by
    calc
      Fintype.card Ω = ∑ t : T, (Finset.univ.filter fun a => f a = t).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ = Fintype.card T * c := by simp_rw [hfc]; simp
  have hp : (Finset.univ.filter fun a => p (f a)).card =
      (Finset.univ.filter p).card * c := by
    calc
      _ = ∑ t ∈ Finset.univ.filter p,
          (Finset.univ.filter fun a => f a = t).card := by
        symm
        simpa using Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset Ω) (Finset.univ.filter p) f
      _ = _ := by simp_rw [hfc]; simp
  have hc : (c : ℚ) ≠ 0 := by
    have : c ≠ 0 := by
      intro hc
      have := Fintype.card_pos (α := Ω)
      simp [hc] at hΩ
    exact_mod_cast this
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hp, hΩ]
  push_cast
  exact mul_div_mul_right _ _ hc

/-- Updating only one copy changes the output by its relabeled base-output
difference. This identity retains all summands and does not assume they are
independent. -/
theorem enlargedOutput_update {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [Fintype (LinearInjection F B K)] (C : V → B)
    (x : LinearInjection F B K → V) (L : LinearInjection F B K) (y : V) :
    enlargedOutput C (Function.update x L y) =
      enlargedOutput C x + L.1 (C y - C (x L)) := by
  classical
  have hfun : (fun J => J.1 (C (Function.update x L y J))) =
      Function.update (fun J : LinearInjection F B K => J.1 (C (x J))) L (L.1 (C y)) := by
    funext J
    by_cases h : J = L
    · subst J
      simp
    · simp [h]
  unfold enlargedOutput
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ L)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ L)]
  rw [map_sub]
  abel

/-- Injectivity of the selected relabeling makes the enlargement output
change exactly when that copy's base output changes. -/
theorem enlargedOutput_update_ne_iff {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [Fintype (LinearInjection F B K)] (C : V → B)
    (x : LinearInjection F B K → V) (L : LinearInjection F B K) (y : V) :
    enlargedOutput C (Function.update x L y) ≠ enlargedOutput C x ↔ C y ≠ C (x L) := by
  rw [enlargedOutput_update, ne_eq, add_eq_left, map_eq_zero_iff _ L.2,
    sub_eq_zero, ne_eq]

theorem injection_eval_uniform {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [AddCommGroup K] [Module F K]
    [Fintype K] [Fintype (LinearInjection F B K)]
    [Nonempty (LinearInjection F B K)] (b : B) (hb : b ≠ 0)
    (p : {x : K // x ≠ 0} → Prop) :
    probability (fun L : LinearInjection F B K =>
      p ⟨L.1 b, injection_eval_ne_zero L hb⟩) = probability p := by
  classical
  let : Nonempty {x : K // x ≠ 0} :=
    ⟨⟨(Classical.choice inferInstance : LinearInjection F B K).1 b,
      injection_eval_ne_zero _ hb⟩⟩
  let f : LinearInjection F B K → {x : K // x ≠ 0} :=
    fun L => ⟨L.1 b, injection_eval_ne_zero L hb⟩
  apply probability_preimage_of_fibers f
  intro x y
  obtain ⟨e, he⟩ := exists_equiv_map_nonzero (F := F) x.1 y.1 x.2 y.2
  let ee : {L : LinearInjection F B K // f L = x} ≃
      {L : LinearInjection F B K // f L = y} :=
    (postcompose e).subtypeEquiv (fun L => by
      change f L = x ↔ f (postcompose e L) = y
      constructor
      · intro h
        apply Subtype.ext
        change e (L.1 b) = y.1
        rw [show L.1 b = x.1 from congrArg Subtype.val h, he]
      · intro h
        apply Subtype.ext
        apply e.injective
        exact (congrArg Subtype.val h).trans he.symm)
  exact Nat.card_congr ee

/-- Failure of the pullback family to span the full dual has a nonzero vector
witness in its common annihilator. -/
theorem pullback_ne_top_iff {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [FiniteDimensional F B] [AddCommGroup K] [Module F K]
    (L : B →ₗ[F] K) (S : Submodule F (Module.Dual F K)) :
    S.map L.dualMap ≠ ⊤ ↔ ∃ b : B, b ≠ 0 ∧ L b ∈ S.dualCoannihilator := by
  let W := S.map L.dualMap
  have hann : W.dualCoannihilator = S.dualCoannihilator.comap L := by
    ext b
    simp only [Submodule.mem_dualCoannihilator, Submodule.mem_comap]
    constructor
    · intro h z hz
      exact h (z.comp L) ⟨z, hz, rfl⟩
    · intro h z ⟨w, hw, hwz⟩
      subst z
      exact h w hw
  constructor
  · intro hW
    have hn : W.dualCoannihilator ≠ ⊥ := by
      intro hz
      have hh := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)
      rw [hz, Submodule.dualAnnihilator_bot] at hh
      exact hW hh.symm
    obtain ⟨b, hb, hb0⟩ := (Submodule.ne_bot_iff _).1 hn
    exact ⟨b, hb0, by simpa [hann] using hb⟩
  · rintro ⟨b, hb0, hb⟩ htop
    have hz : b ∈ W.dualCoannihilator := by simpa [hann] using hb
    change b ∈ (S.map L.dualMap).dualCoannihilator at hz
    rw [htop] at hz
    have hall : ∀ z : Module.Dual F B, z b = 0 := by
      simpa only [Submodule.mem_dualCoannihilator, Submodule.mem_top,
        forall_true_left] using hz
    obtain ⟨z, hz'⟩ := Module.Projective.exists_dual_ne_zero F hb0
    exact hz' (hall z)

/-- The nonzero part of a codimension-`r` subspace has density at most `2⁻ʳ`
among all nonzero ambient vectors. The dimensions are written additively to
avoid truncated subtraction. -/
theorem nonzero_density_le (d r : ℕ) (h : 0 < d + r) :
    ((2 : ℚ) ^ d - 1) / ((2 : ℚ) ^ (d + r) - 1) ≤ 1 / (2 : ℚ) ^ r := by
  have hpow : 1 < (2 : ℚ) ^ (d + r) := one_lt_pow₀ (by norm_num) (by omega)
  have hr : (1 : ℚ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  rw [pow_add]
  nlinarith

/-- Cardinality of all nonzero vectors in a finite binary vector space. -/
theorem card_nonzero_binary (K : Type*) [AddCommGroup K] [Module (ZMod 2) K]
    [Fintype K] :
    Nat.card {x : K // x ≠ 0} = 2 ^ Module.finrank (ZMod 2) K - 1 := by
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : K => x = 0), Fintype.card_subtype_eq]
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- Exact density of the nonzero part of a binary subspace. -/
theorem probability_nonzero_subspace (K : Type*) [AddCommGroup K]
    [Module (ZMod 2) K] [Fintype K] (W : Submodule (ZMod 2) K) :
    probability (fun x : {x : K // x ≠ 0} => x.1 ∈ W) =
      ((2 : ℚ) ^ Module.finrank (ZMod 2) W - 1) /
        ((2 : ℚ) ^ Module.finrank (ZMod 2) K - 1) := by
  classical
  let : Fintype W := Fintype.ofFinite _
  let e : {x : {x : K // x ≠ 0} // x.1 ∈ W} ≃ {x : W // x ≠ 0} :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, by
        intro h
        exact x.1.2 (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨⟨x.1.1, by
        intro h
        apply x.2
        exact Subtype.ext h⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold probability
  rw [Nat.card_congr e,
    card_nonzero_binary W, card_nonzero_binary K]
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)),
    Nat.cast_sub (Nat.one_le_pow _ _ (by decide))]
  push_cast
  rfl

/-- The annihilator dimension identity gives precisely the exponent needed
by the enlargement, without any loss depending on the ambient dimension. -/
theorem probability_annihilator_le (K : Type*) [AddCommGroup K]
    [Module (ZMod 2) K] [Fintype K] [FiniteDimensional (ZMod 2) K]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hK : 0 < Module.finrank (ZMod 2) K) :
    probability (fun x : {x : K // x ≠ 0} => x.1 ∈ S.dualCoannihilator) ≤
      1 / (2 : ℚ) ^ Module.finrank (ZMod 2) S := by
  rw [probability_nonzero_subspace]
  have hr := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  rw [← hr, add_comm (Module.finrank (ZMod 2) S)]
  apply nonzero_density_le
  omega

/-- The threshold `b + 2` is chosen before the ambient dimension. -/
theorem union_bound_le_quarter (b r : ℕ) (hr : b + 2 ≤ r) :
    ((2 : ℚ) ^ b - 1) / (2 : ℚ) ^ r ≤ 1 / 4 := by
  have hpow : (2 : ℚ) ^ (b + 2) ≤ (2 : ℚ) ^ r :=
    pow_le_pow_right₀ (by norm_num) hr
  rw [pow_add] at hpow
  norm_num at hpow
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ r)).2
  nlinarith [show (0 : ℚ) ≤ 2 ^ b by positivity]

/-- The enlargement's uniform-injection union bound, including its actual
linear-algebraic bad event. -/
theorem pullback_failure_probability_le {B K : Type*}
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    [FiniteDimensional (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
    [FiniteDimensional (ZMod 2) K]
    [Fintype (LinearInjection (ZMod 2) B K)]
    [Nonempty (LinearInjection (ZMod 2) B K)]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hK : 0 < Module.finrank (ZMod 2) K) :
    probability (fun L : LinearInjection (ZMod 2) B K => S.map L.1.dualMap ≠ ⊤) ≤
      ((2 : ℚ) ^ Module.finrank (ZMod 2) B - 1) /
        (2 : ℚ) ^ Module.finrank (ZMod 2) S := by
  classical
  calc
    _ = probability (fun L : LinearInjection (ZMod 2) B K =>
        ∃ b : {b : B // b ≠ 0}, L.1 b.1 ∈ S.dualCoannihilator) := by
      congr 1
      funext L
      apply propext
      rw [pullback_ne_top_iff]
      exact ⟨fun ⟨b, hb, h⟩ => ⟨⟨b, hb⟩, h⟩,
        fun ⟨b, h⟩ => ⟨b.1, b.2, h⟩⟩
    _ ≤ ∑ b : {b : B // b ≠ 0}, probability
        (fun L : LinearInjection (ZMod 2) B K => L.1 b.1 ∈ S.dualCoannihilator) :=
      probability_exists_le_sum _
    _ ≤ ∑ _b : {b : B // b ≠ 0},
        1 / (2 : ℚ) ^ Module.finrank (ZMod 2) S := by
      apply Finset.sum_le_sum
      intro b _
      rw [injection_eval_uniform b.1 b.2
        (fun x : {x : K // x ≠ 0} => x.1 ∈ S.dualCoannihilator)]
      exact probability_annihilator_le K S hK
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card, card_nonzero_binary B,
        Nat.cast_sub (Nat.one_le_pow _ _ (by decide))]
      push_cast
      ring

/-- At least three quarters of the injection copies restrict onto the full
base dual when the restriction rank is at least `dim B + 2`. -/
theorem pullback_failure_probability_le_quarter {B K : Type*}
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    [FiniteDimensional (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
    [FiniteDimensional (ZMod 2) K]
    [Fintype (LinearInjection (ZMod 2) B K)]
    [Nonempty (LinearInjection (ZMod 2) B K)]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2) S) :
    probability (fun L : LinearInjection (ZMod 2) B K => S.map L.1.dualMap ≠ ⊤) ≤
      1 / 4 := by
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  exact (pullback_failure_probability_le S (by omega)).trans
    (union_bound_le_quarter _ _ hr)

theorem probability_not {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p : Ω → Prop) : probability (fun x => ¬ p x) = 1 - probability p := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω)) p
  have h' : ((Finset.univ.filter p).card : ℚ) +
      ((Finset.univ.filter fun x => ¬p x).card : ℚ) = Fintype.card Ω := by
    exact_mod_cast h
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply (eq_sub_iff_add_eq).2
  rw [← add_div, add_comm, h', div_self hcard]

/-- Averaging a nonnegative detection rate which is at least one quarter on
each good copy. This is the last finite probability step of enlargement. -/
theorem average_detection_lower_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (bad : Ω → Prop) (detected : Ω → ℚ)
    (hnonneg : ∀ x, 0 ≤ detected x)
    (hgood : ∀ x, ¬bad x → 1 / 4 ≤ detected x) :
    (1 - probability bad) * (1 / 4) ≤
      (∑ x, detected x) / (Fintype.card Ω : ℚ) := by
  classical
  have hs : ∑ x : Ω, (if bad x then (0 : ℚ) else 1 / 4) ≤ ∑ x, detected x := by
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : bad x
    · simpa [hx] using hnonneg x
    · simpa [hx] using hgood x hx
  have heq : ∑ x : Ω, (if bad x then (0 : ℚ) else 1 / 4) =
      ((Finset.univ.filter fun x => ¬bad x).card : ℚ) * (1 / 4) := by
    rw [Finset.sum_ite]
    simp
  rw [heq] at hs
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (Fintype.card Ω) :
    (0 : ℚ) ≤ Fintype.card Ω)
  rw [← probability_not]
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [div_mul_eq_mul_div] using hd

/-- The enlargement retains `3/16` detection, and hence the advertised `1/8`.
The hypotheses are the bad-copy probability and the average lower bound from
the base gadget; they make no independence assertion. -/
theorem detection_constants {bad detected : ℚ} (hbad : bad ≤ 1 / 4)
    (hdetected : (1 - bad) * (1 / 4) ≤ detected) :
    3 / 16 ≤ detected ∧ 1 / 8 ≤ detected := by
  constructor <;> linarith

theorem enlarged_detection {B K : Type*}
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    [FiniteDimensional (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
    [FiniteDimensional (ZMod 2) K]
    [Fintype (LinearInjection (ZMod 2) B K)]
    [Nonempty (LinearInjection (ZMod 2) B K)]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2) S)
    (detected : LinearInjection (ZMod 2) B K → ℚ)
    (hnonneg : ∀ L, 0 ≤ detected L)
    (hbase : ∀ L, S.map L.1.dualMap = ⊤ → 1 / 4 ≤ detected L) :
    3 / 16 ≤ (∑ L, detected L) / (Fintype.card (LinearInjection (ZMod 2) B K) : ℚ) ∧
    1 / 8 ≤ (∑ L, detected L) / (Fintype.card (LinearInjection (ZMod 2) B K) : ℚ) := by
  apply detection_constants (pullback_failure_probability_le_quarter S hr)
  apply average_detection_lower_bound _ detected hnonneg
  intro L hL
  exact hbase L (not_not.mp hL)

end

end UniqueGamesTheorem.Gadget.Enlargement

end

section

namespace UniqueGamesTheorem.Gadget.Harmonic

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem harmonic_eq_sum (r : ℕ) :
    harmonic r = ∑ i ∈ Finset.range r, (↑(i + 1) : ℚ)⁻¹ := by
  induction r with
  | zero => simp
  | succ r ih => simp [harmonic_succ, Finset.sum_range_succ, ih]

theorem average_mono {f g : Ω → ℚ} (h : ∀ ω, f ω ≤ g ω) :
    average f ≤ average g :=
  Finset.expect_le_expect fun ω _ => h ω

theorem average_nonneg {f : Ω → ℚ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ average f :=
  Finset.expect_nonneg fun ω _ => h ω

theorem average_add (f g : Ω → ℚ) :
    average (fun ω => f ω + g ω) = average f + average g :=
  Finset.expect_add_distrib _ _ _

theorem average_sub (f g : Ω → ℚ) :
    average (fun ω => f ω - g ω) = average f - average g :=
  Finset.expect_sub_distrib _ _ _

theorem average_mul_left (c : ℚ) (f : Ω → ℚ) :
    average (fun ω => c * f ω) = c * average f :=
  (Finset.mul_expect _ _ _).symm

theorem probability_nonneg (p : Ω → Prop) [DecidablePred p] :
    0 ≤ probability p := by
  apply average_nonneg
  intro ω
  split <;> norm_num

theorem probability_mono (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ ω, p ω → q ω) : probability p ≤ probability q := by
  apply average_mono
  intro ω
  by_cases hp : p ω
  · simp [hp, h ω hp]
  · simp only [ite_eq_right hp]
    split <;> norm_num

theorem probability_not [Nonempty Ω] (p : Ω → Prop) [DecidablePred p] :
    probability (fun ω => ¬ p ω) = 1 - probability p := by
  have he : (fun ω => if ¬ p ω then (1 : ℚ) else 0) =
      (fun ω => 1 - if p ω then (1 : ℚ) else 0) := by
    funext ω
    by_cases h : p ω <;> simp [h]
  unfold probability
  rw [he, average_sub, average_const]

/-- A bijection swapping an event with its complement proves exact half
probability. At a leaf the bijection is translation by a symbol on which a
nonzero binary character is one. -/
theorem probability_eq_half_of_swap [Nonempty Ω]
    (p : Ω → Prop) [DecidablePred p] (e : Ω ≃ Ω)
    (hswap : ∀ ω, p (e ω) ↔ ¬ p ω) : probability p = 1 / 2 := by
  have he : probability (fun ω => ¬ p ω) = probability p := by
    apply Fintype.expect_equiv e
    intro ω
    simp only [hswap ω]
  rw [probability_not] at he
  linarith

/-- Every nonzero binary additive character detects precisely half of uniform
symbols. The witness may depend on the previously sampled path. -/
theorem binary_character_detection_probability [AddGroup Ω]
    (χ : Ω →+ ZMod 2) (v : Ω) (hv : χ v ≠ 0) :
    probability (fun ω => χ ω ≠ 0) = 1 / 2 := by
  apply probability_eq_half_of_swap _ (Equiv.addLeft v)
  intro ω
  change χ (v + ω) ≠ 0 ↔ ¬χ ω ≠ 0
  rw [map_add]
  generalize ha : χ v = a at hv ⊢
  generalize hb : χ ω = b
  fin_cases a <;> fin_cases b
  · exact (hv rfl).elim
  · exact (hv rfl).elim
  · change (1 : ZMod 2) + 0 ≠ 0 ↔ ¬ (0 : ZMod 2) ≠ 0
    decide
  · change (1 : ZMod 2) + 1 ≠ 0 ↔ ¬ (1 : ZMod 2) ≠ 0
    decide

/-- A surviving family contains a nonzero character, so its detection event
contains an event of exact half probability. -/
theorem binary_family_detection_ge_half [AddGroup Ω]
    (detects : Ω → Prop) [DecidablePred detects]
    (χ : Ω →+ ZMod 2) (v : Ω) (hv : χ v ≠ 0)
    (hcontains : ∀ ω, χ ω ≠ 0 → detects ω) :
    (1 / 2 : ℚ) ≤ probability detects := by
  rw [← binary_character_detection_probability χ v hv]
  exact probability_mono _ _ hcontains

theorem harmonic_nonneg (r : ℕ) : 0 ≤ harmonic r := by
  induction r with
  | zero => simp
  | succ r ih => rw [harmonic_succ]; positivity

theorem harmonic_mono {r s : ℕ} (h : r ≤ s) : harmonic r ≤ harmonic s := by
  induction h with
  | refl => exact le_rfl
  | @step s h ih =>
    rw [harmonic_succ]
    have : (0 : ℚ) ≤ (↑(s + 1))⁻¹ := by positivity
    linarith

theorem harmonic_pos {r : ℕ} (h : 0 < r) : 0 < harmonic r := by
  have hm := harmonic_mono (r := 1) (s := r) h
  norm_num [harmonic_succ] at hm
  linarith

theorem harmonic_sub_predecessor {r : ℕ} (h : 0 < r) :
    harmonic r - harmonic (r - 1) = (r : ℚ)⁻¹ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  simp [harmonic_succ]

/-- A generic rank-`r` space loses either zero or one dimension. Its harmonic
drop is exactly the loss indicator times `1/r`. -/
theorem generic_drop_identity (r : ℕ) (next : Ω → ℕ) (hr : 0 < r)
    (hstep : ∀ ω, next ω = r ∨ next ω = r - 1) :
    average (fun ω => harmonic r - harmonic (next ω)) =
      (r : ℚ)⁻¹ * probability (fun ω => next ω < r) := by
  have he : (fun ω => harmonic r - harmonic (next ω)) =
      (fun ω => (r : ℚ)⁻¹ * if next ω < r then 1 else 0) := by
    funext ω
    rcases hstep ω with h | h
    · simp [h]
    · rw [h, ite_eq_left (Nat.sub_lt hr (by omega))]
      simp [harmonic_sub_predecessor hr]
  rw [he, average_mul_left]
  rfl

/-- The generic loss probability `3rθ` becomes the rank-independent harmonic
loss bound `3θ`. -/
theorem generic_expected_drop_le (r : ℕ) (next : Ω → ℕ) (θ : ℚ)
    (hr : 0 < r) (hstep : ∀ ω, next ω = r ∨ next ω = r - 1)
    (hloss : probability (fun ω => next ω < r) ≤ 3 * r * θ) :
    average (fun ω => harmonic r - harmonic (next ω)) ≤ 3 * θ := by
  rw [generic_drop_identity r next hr hstep]
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  calc
    (r : ℚ)⁻¹ * probability (fun ω => next ω < r) ≤
        (r : ℚ)⁻¹ * (3 * r * θ) :=
      mul_le_mul_of_nonneg_left hloss (le_of_lt (inv_pos.mpr hrq))
    _ = 3 * θ := by field_simp [ne_of_gt hrq]

/-- Without genericity, charge the entire harmonic potential only on paths
where some rank is lost. -/
theorem arbitrary_expected_drop_le (r : ℕ) (next : Ω → ℕ) (p : ℚ)
    (hstep : ∀ ω, next ω ≤ r)
    (hloss : probability (fun ω => next ω < r) ≤ p) :
    average (fun ω => harmonic r - harmonic (next ω)) ≤ harmonic r * p := by
  calc
    average (fun ω => harmonic r - harmonic (next ω)) ≤
        average (fun ω => harmonic r * if next ω < r then 1 else 0) := by
      apply average_mono
      intro ω
      by_cases h : next ω < r
      · simp only [ite_eq_left h, mul_one]
        exact sub_le_self _ (harmonic_nonneg _)
      · have he : next ω = r := by have := hstep ω; omega
        simp [he]
    _ = harmonic r * probability (fun ω => next ω < r) := by
      rw [average_mul_left]
      rfl
    _ ≤ harmonic r * p := mul_le_mul_of_nonneg_left hloss (harmonic_nonneg _)

theorem badRankCoefficient_nonneg (r₀ : ℕ) : 0 ≤ badRankCoefficient r₀ := by
  exact mul_nonneg (harmonic_nonneg _) (by positivity)

theorem depth_budget (r₀ : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    4 * (depth r₀ θ : ℚ) * θ ≤ harmonic r₀ / 2 := by
  have hden : (0 : ℚ) < 8 * θ := by positivity
  have hf := Nat.floor_le (div_nonneg (harmonic_nonneg r₀) (le_of_lt hden))
  have hb := (le_div_iff₀ hden).mp hf
  change (depth r₀ θ : ℚ) * (8 * θ) ≤ harmonic r₀ at hb
  nlinarith

/-- The potential-to-survival step needs only the final finite experiment,
allowing earlier levels to have different path sample spaces. -/
theorem survival_probability_ge_half_of_potential (rank : Ω → ℕ) (r₀ : ℕ)
    (hr₀ : 0 < r₀) (hterminal : ∀ ω, rank ω ≤ r₀)
    (hmean : harmonic r₀ / 2 ≤ average (fun ω => harmonic (rank ω))) :
    (1 / 2 : ℚ) ≤ probability (fun ω => 0 < rank ω) := by
  have hpoint : average (fun ω => harmonic (rank ω)) ≤
      harmonic r₀ * probability (fun ω => 0 < rank ω) := by
    calc
      average (fun ω => harmonic (rank ω)) ≤
          average (fun ω => harmonic r₀ * if 0 < rank ω then 1 else 0) := by
        apply average_mono
        intro ω
        by_cases h : 0 < rank ω
        · simpa only [ite_eq_left h, mul_one] using harmonic_mono (hterminal ω)
        · have he : rank ω = 0 := by omega
          simp [he]
      _ = harmonic r₀ * probability (fun ω => 0 < rank ω) := by
        rw [average_mul_left]
        rfl
  have hpos := harmonic_pos hr₀
  nlinarith

/-- Uniform paths and a separately sampled uniform terminal symbol have the
product law used in the leaf-noise experiment. -/
theorem probability_product {Ξ : Type*} [Fintype Ξ]
    (detects : Ω × Ξ → Prop) [DecidablePred detects] :
    probability detects = average (fun ω => probability (fun ξ => detects (ω, ξ))) := by
  unfold probability average
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ξ)
      (fun z => if detects z then (1 : ℚ) else 0))

end UniqueGamesTheorem.Gadget.Harmonic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_AdaptivePathsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# From full character lifts to linear-map detection

If a target linear map is injective on the logical alphabet, a linear left
inverse of that restriction turns all logical characters into a full lift.
Detection by this lift implies that the target map does not annihilate the
noise. The left inverse is proved to exist by the vector-space splitting
theorem; it is not an additional premise.
-/

namespace UniqueGamesTheorem.Gadget.DetectionBridge

open Harmonic

variable {K B V E Ω : Type*} [Field K]
variable [AddCommGroup B] [Module K B] [AddCommGroup V] [Module K V]
variable [AddCommGroup E] [Module K E] [Fintype Ω]

theorem exists_leftInverse_of_logical_injective (ι : B →ₗ[K] V)
    (T : V →ₗ[K] E) (hinjective : Function.Injective (T.comp ι)) :
    ∃ l : E →ₗ[K] B, l.comp (T.comp ι) = LinearMap.id :=
  (T.comp ι).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinjective)

/-- The left inverse supplies an actual full character lift through `T`. -/
theorem fullLift_of_leftInverse (ι : B →ₗ[K] V) (T : V →ₗ[K] E)
    (l : E →ₗ[K] B) (hleft : l.comp (T.comp ι) = LinearMap.id) :
    IsFullLift ι (l.comp T).dualMap := by
  intro z b
  change z (l (T (ι b))) = z b
  have hb : l (T (ι b)) = b := LinearMap.congr_fun hleft b
  rw [hb]

/-- A full-lift detection guarantee transfers to every target map injective
on the logical alphabet. -/
theorem target_detection_of_full_lift_bound [DecidableEq E]
    (noise : Ω → V) (ι : B →ₗ[K] V) (T : V →ₗ[K] E) (q : ℚ)
    (hfull : ∀ ψ : Module.Dual K B →ₗ[K] Module.Dual K V,
      IsFullLift ι ψ → q ≤ characterDetection noise ψ)
    (hinjective : Function.Injective (T.comp ι)) :
    q ≤ probability (fun ω => T (noise ω) ≠ 0) := by
  classical
  obtain ⟨l, hl⟩ := exists_leftInverse_of_logical_injective ι T hinjective
  calc
    q ≤ characterDetection noise (l.comp T).dualMap :=
      hfull _ (fullLift_of_leftInverse ι T l hl)
    _ ≤ probability (fun ω => T (noise ω) ≠ 0) := by
      unfold characterDetection
      apply probability_mono
      rintro ω ⟨z, hz⟩ hzero
      apply hz
      change z (l (T (noise ω))) = 0
      simp [hzero]

end UniqueGamesTheorem.Gadget.DetectionBridge

end

section

/-!
# Exact kernel counts for binary linear maps

The last paragraph of Theorem 3.4 uses the fact that a uniform vector in a
binary vector space lands in the kernel of a rank-k map with probability
2⁻ᵏ. These theorems prove its exact integer-count form from mathlib's
rank-nullity and finite-vector-space cardinality theorems. The target space
does not have to be finite, and no injectivity of any factor map is assumed.
-/

namespace UniqueGamesTheorem.Gadget.LinearKernelCount

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

end UniqueGamesTheorem.Gadget.LinearKernelCount

end

section

/-!
# Fresh finite orientations

The rank is fixed before the fresh isomorphism is sampled.  The finite
counting identities below do not require the subsequent lift to be independent
of that isomorphism.  In particular, an event concerning the oriented subspace
may be tested after arbitrary earlier choices have been fixed.
-/

noncomputable section

open scoped BigOperators
open Module

namespace UniqueGamesTheorem.Gadget.Orientation

section FiniteAction

variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]

omit [Fintype X] in
/-- Right translation of the uniform group element changes the starting point,
but leaves the complete sample sum unchanged. -/
theorem sum_action_eq (x y : X) (h : ∃ a : G, a • x = y) (f : X → ℚ) :
    (∑ g : G, f (g • x)) = ∑ g : G, f (g • y) := by
  obtain ⟨a, rfl⟩ := h
  symm
  exact Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun g => by simp [mul_smul])

/-- Cross-multiplied uniform-pushforward identity for a transitive finite action.
This form also handles empty event sets without additional cases. -/
theorem card_mul_sum_action (x : X)
    (transitive : ∀ y : X, ∃ a : G, a • x = y) (f : X → ℚ) :
    (Fintype.card X : ℚ) * (∑ g : G, f (g • x)) =
      (Fintype.card G : ℚ) * (∑ y : X, f y) := by
  calc
    (Fintype.card X : ℚ) * (∑ g : G, f (g • x)) =
        ∑ y : X, ∑ g : G, f (g • x) := by simp
    _ = ∑ y : X, ∑ g : G, f (g • y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact sum_action_eq x y (transitive y) f
    _ = ∑ g : G, ∑ y : X, f (g • y) := Finset.sum_comm
    _ = ∑ _g : G, ∑ y : X, f y := by
      apply Finset.sum_congr rfl
      intro g _
      exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
    _ = (Fintype.card G : ℚ) * (∑ y : X, f y) := by simp

/-- A uniform group element sends a fixed point to the uniform distribution on
the entire transitive space.  Apply to indicator functions for event bounds. -/
theorem mean_action (x : X)
    (transitive : ∀ y : X, ∃ a : G, a • x = y) (f : X → ℚ) :
    (∑ g : G, f (g • x)) / Fintype.card G =
      (∑ y : X, f y) / Fintype.card X := by
  have : Nonempty X := ⟨x⟩
  have hG : (Fintype.card G : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hX : (Fintype.card X : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (div_eq_div_iff hG hX).2
  simpa [mul_comm] using card_mul_sum_action x transitive f

end FiniteAction

section LinearOrientation

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

/-- Every two equal-dimensional subspaces are related by an automorphism of
the ambient space.  This supplies actual transitivity, rather than assuming
the desired distribution on the Grassmannian. -/
theorem exists_map_eq_of_finrank_eq (E F : Submodule K V)
    (h : finrank K E = finrank K F) :
    ∃ a : V ≃ₗ[K] V, E.map a.toLinearMap = F := by
  let e : E ≃ₗ[K] F := LinearEquiv.ofFinrankEq E F h
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨a, ?_⟩
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (ha ⟨u, hu⟩) ▸ (e ⟨u, hu⟩).property
  · intro hv
    obtain ⟨u, hu⟩ := e.surjective ⟨v, hv⟩
    refine ⟨u, u.property, ?_⟩
    exact (ha u).symm.trans (congrArg Subtype.val hu)

/-- Equal-rank transitivity specialized to the rank-indexed sampling space. -/
theorem rankSpace_transitive {r : ℕ} (E F : RankSpace K V r) :
    ∃ a : V ≃ₗ[K] V, a • E = F := by
  obtain ⟨a, ha⟩ := exists_map_eq_of_finrank_eq E.val F.val
    (E.property.trans F.property.symm)
  exact ⟨a, Subtype.ext ha⟩

/-- The exact uniform law of a fixed-rank subspace under a fresh uniform
linear orientation, with no genericity or independence premise. -/
theorem mean_oriented_subspace {r : ℕ} [Fintype (V ≃ₗ[K] V)]
    [Fintype (RankSpace K V r)] (E : RankSpace K V r) (f : RankSpace K V r → ℚ) :
    (∑ a : V ≃ₗ[K] V, f (a • E)) / Fintype.card (V ≃ₗ[K] V) =
      (∑ F : RankSpace K V r, f F) / Fintype.card (RankSpace K V r) :=
  mean_action E (rankSpace_transitive E) f

variable {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U]

/-- Uniform orientations between two spaces send a fixed character subspace
to the uniform distribution on all subspaces of the same dimension. -/
theorem mean_map_equiv [FiniteDimensional K U] (E : Submodule K B) (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)] [Fintype (U ≃ₗ[K] U)]
    [Fintype (RankSpace K U (finrank K E))]
    (f : RankSpace K U (finrank K E) → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ F : RankSpace K U (finrank K E), f F) /
        Fintype.card (RankSpace K U (finrank K E)) := by
  let E₀ : RankSpace K U (finrank K E) :=
    ⟨E.map J₀.toLinearMap, J₀.finrank_map_eq E⟩
  have hsum : (∑ J : B ≃ₗ[K] U, f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) =
      ∑ a : U ≃ₗ[K] U, f (a • E₀) := by
    apply Fintype.sum_equiv (orientationEquiv J₀)
    intro J
    congr 1
    apply Subtype.ext
    change E.map J.toLinearMap =
      (E.map J₀.toLinearMap).map (J₀.symm.trans J).toLinearMap
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp
  rw [hsum, Fintype.card_congr (orientationEquiv J₀)]
  exact mean_oriented_subspace E₀ f

theorem mean_dual_pullback [FiniteDimensional K B] [FiniteDimensional K U]
    (E : Submodule K (Module.Dual K U)) (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)]
    [Fintype (Module.Dual K U ≃ₗ[K] Module.Dual K B)]
    [Fintype (Module.Dual K B ≃ₗ[K] Module.Dual K B)]
    [Fintype (RankSpace K (Module.Dual K B) (finrank K E))]
    (f : RankSpace K (Module.Dual K B) (finrank K E) → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨E.map J.dualMap.toLinearMap, J.dualMap.finrank_map_eq E⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ F : RankSpace K (Module.Dual K B) (finrank K E), f F) /
        Fintype.card (RankSpace K (Module.Dual K B) (finrank K E)) := by
  let e := dualOrientationEquiv (K := K) (B := B) (U := U)
  have hsum := Fintype.sum_equiv e
    (fun J : B ≃ₗ[K] U => f ⟨E.map J.dualMap.toLinearMap, J.dualMap.finrank_map_eq E⟩)
    (fun J : Module.Dual K U ≃ₗ[K] Module.Dual K B =>
      f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) (fun _ => rfl)
  rw [hsum, Fintype.card_congr e]
  exact mean_map_equiv E J₀.dualMap f

end LinearOrientation

end UniqueGamesTheorem.Gadget.Orientation

end

end

section

/-!
# Fresh orientations of nonzero perturbations

This is the nonzero-symbol uniformity step in the latent-noise recurrence.
The perturbation is fixed before the orientation, and zero is excluded from
both sample spaces explicitly.
-/

noncomputable section

open scoped BigOperators

namespace UniqueGamesTheorem.Gadget.OrientationVectors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Extend the isomorphism taking one specified nonzero vector to another. -/
theorem exists_equiv_map_nonzero (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : V ≃ₗ[K] V, e x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton K V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton K V y hy
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨e, ?_⟩
  have h := (he (ex 1)).symm
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h

theorem nonzero_transitive (x y : {v : V // v ≠ 0}) :
    ∃ a : V ≃ₗ[K] V, a • x = y := by
  obtain ⟨a, ha⟩ := exists_equiv_map_nonzero (K := K) x.val y.val x.property y.property
  exact ⟨a, Subtype.ext ha⟩

/-- A uniform ambient automorphism sends a fixed nonzero symbol uniformly
onto all nonzero symbols. -/
theorem mean_oriented_nonzero [Fintype (V ≃ₗ[K] V)]
    [Fintype {x : V // x ≠ 0}] (x : {v : V // v ≠ 0})
    (f : {v : V // v ≠ 0} → ℚ) :
    (∑ a : V ≃ₗ[K] V, f (a • x)) / Fintype.card (V ≃ₗ[K] V) =
      (∑ y : {v : V // v ≠ 0}, f y) / Fintype.card {v : V // v ≠ 0} :=
  Orientation.mean_action x (nonzero_transitive x) f

/-- The exact law used after fixing a child line and its nonzero output
difference: averaging over all `J : B ≃ₗ[K] U` is uniform on `U \ {0}`. -/
theorem mean_iso_nonzero {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)] [Fintype (U ≃ₗ[K] U)]
    [Fintype {u : U // u ≠ 0}] (b : B) (hb : b ≠ 0)
    (f : {u : U // u ≠ 0} → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨J b, equiv_apply_ne_zero J hb⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ u : {u : U // u ≠ 0}, f u) / Fintype.card {u : U // u ≠ 0} := by
  let x : {u : U // u ≠ 0} := ⟨J₀ b, equiv_apply_ne_zero J₀ hb⟩
  have hsum : (∑ J : B ≃ₗ[K] U, f ⟨J b, equiv_apply_ne_zero J hb⟩) =
      ∑ a : U ≃ₗ[K] U, f (a • x) := by
    apply Fintype.sum_equiv (Orientation.orientationEquiv J₀)
    intro J
    congr 1
    apply Subtype.ext
    change J b = (J₀.symm.trans J) (J₀ b)
    simp
  rw [hsum, Fintype.card_congr (Orientation.orientationEquiv J₀)]
  exact mean_oriented_nonzero x f

end UniqueGamesTheorem.Gadget.OrientationVectors

end

end

section

namespace UniqueGamesTheorem.Gadget.Parameters

open Harmonic
open scoped BigOperators

/-- Every block from `n+1` through `2n` adds at least one half. -/
theorem harmonic_double (n : ℕ) (hn : 0 < n) :
    Harmonic.harmonic n + 1 / 2 ≤ Harmonic.harmonic (2 * n) := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hsplit : Harmonic.harmonic (2 * n) = Harmonic.harmonic n +
      ∑ i ∈ Finset.range n, (↑(n + i + 1) : ℚ)⁻¹ := by
    rw [harmonic_eq_sum, show 2 * n = n + n by omega, Finset.sum_range_add]
    rw [← harmonic_eq_sum n]
  have hs : (∑ _i ∈ Finset.range n, (2 * (n : ℚ))⁻¹) ≤
      ∑ i ∈ Finset.range n, (↑(n + i + 1) : ℚ)⁻¹ := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    apply inv_anti₀ (by positivity)
    exact_mod_cast (show n + i + 1 ≤ 2 * n by omega)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have he : (n : ℚ) * (2 * (n : ℚ))⁻¹ = 1 / 2 := by
    field_simp [ne_of_gt hnq]
  rw [he] at hs
  rw [hsplit]
  linarith

theorem harmonic_pow_two (k : ℕ) : (k : ℚ) / 2 ≤ Harmonic.harmonic (2 ^ k) := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_div, pow_zero] using harmonic_nonneg 1
  | succ k ih =>
    have hd := harmonic_double (2 ^ k) (pow_pos (by decide) _)
    rw [pow_succ, Nat.mul_comm]
    push_cast
    linarith

theorem rankFor_pos (level : ℚ) : 0 < rankFor level := by
  unfold rankFor
  positivity

theorem le_harmonic_rankFor (level : ℚ) : level ≤ Harmonic.harmonic (rankFor level) := by
  have hc := Nat.le_ceil (2 * level)
  have hh := harmonic_pow_two ⌈2 * level⌉₊
  change level ≤ Harmonic.harmonic (2 ^ ⌈2 * level⌉₊)
  linarith

theorem genericityError_pos (r₀ : ℕ) : 0 < genericityError r₀ := by
  unfold genericityError
  have := badRankCoefficient_nonneg r₀
  positivity

theorem genericityError_lt_one (r₀ : ℕ) : genericityError r₀ < 1 := by
  have hc := badRankCoefficient_nonneg r₀
  unfold genericityError
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem genericityError_budget (r₀ : ℕ) :
    badRankCoefficient r₀ * genericityError r₀ ≤ 1 := by
  have hc := badRankCoefficient_nonneg r₀
  unfold genericityError
  rw [← mul_div_assoc, mul_one]
  apply (div_le_one (by positivity)).mpr
  linarith

/-- The geometric decay has an elementary reciprocal upper bound. -/
theorem geometric_reciprocal_bound (θ : ℚ) (_hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (n : ℕ) : (1 - θ) ^ n * (1 + (n : ℚ) * θ) ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 0 ≤ (1 - θ) ^ n := pow_nonneg (sub_nonneg.mpr hθone) _
    have hn : (0 : ℚ) ≤ n := by positivity
    have hstep : (1 - θ) * (1 + ((n + 1 : ℕ) : ℚ) * θ) ≤
        1 + (n : ℚ) * θ := by
      push_cast
      nlinarith [sq_nonneg θ, mul_nonneg hn (sq_nonneg θ)]
    calc
      (1 - θ) ^ (n + 1) * (1 + ((n + 1 : ℕ) : ℚ) * θ) =
          (1 - θ) ^ n * ((1 - θ) * (1 + ((n + 1 : ℕ) : ℚ) * θ)) := by
        rw [pow_succ]
        ring
      _ ≤ (1 - θ) ^ n * (1 + (n : ℚ) * θ) :=
        mul_le_mul_of_nonneg_left hstep hp
      _ ≤ 1 := ih

/-- The chosen harmonic depth works uniformly for every subsequent
`0 < θ ≤ 1`. Thus the rank can be selected before the field/noise parameter. -/
theorem geometric_at_depth_le (p θ : ℚ) (r₀ : ℕ) (hp : 0 < p)
    (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hlarge : 8 * (p⁻¹ + 1) ≤ Harmonic.harmonic r₀) :
    (1 - θ) ^ depth r₀ θ ≤ p := by
  have hden : (0 : ℚ) < 8 * θ := by positivity
  have hf := Nat.lt_floor_add_one (Harmonic.harmonic r₀ / (8 * θ))
  have hf' := (div_lt_iff₀ hden).mp hf
  change Harmonic.harmonic r₀ < ((depth r₀ θ : ℚ) + 1) * (8 * θ) at hf'
  have hnθ : p⁻¹ ≤ (depth r₀ θ : ℚ) * θ := by nlinarith
  have hpne : p ≠ 0 := ne_of_gt hp
  have hm := mul_le_mul_of_nonneg_left hnθ (le_of_lt hp)
  simp only [mul_inv_cancel₀ hpne] at hm
  have hr := geometric_reciprocal_bound θ (le_of_lt hθ) hθone (depth r₀ θ)
  have hb : 1 ≤ p * (1 + (depth r₀ θ : ℚ) * θ) := by nlinarith
  have hpositive : 0 < 1 + (depth r₀ θ : ℚ) * θ := by positivity
  exact (mul_le_mul_iff_left₀ hpositive).mp (by simpa only [mul_comm] using hr.trans hb)

theorem initialRank_pos (p : ℚ) : 0 < initialRank p := rankFor_pos _

theorem initialRank_large (p : ℚ) :
    8 * (p⁻¹ + 1) ≤ Harmonic.harmonic (initialRank p) := le_harmonic_rankFor _

/-- All scalar choices needed before the field dimension is selected. -/
theorem effective_parameters (p : ℚ) (hp : 0 < p) :
    ∃ r₀ : ℕ, ∃ ε : ℚ,
      0 < r₀ ∧ 0 < ε ∧ ε < 1 ∧ badRankCoefficient r₀ * ε ≤ 1 ∧
      ∀ θ : ℚ, 0 < θ → θ ≤ 1 → (1 - θ) ^ depth r₀ θ ≤ p := by
  refine ⟨initialRank p, genericityError (initialRank p), initialRank_pos p,
    genericityError_pos _, genericityError_lt_one _, genericityError_budget _, ?_⟩
  intro θ hθ hθone
  exact geometric_at_depth_le p θ (initialRank p) hp hθ hθone (initialRank_large p)

end UniqueGamesTheorem.Gadget.Parameters

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_AdviceFibersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Finite latent samplers and their actual spectral law

This bridge counts all sampler outcomes, including repeated vectors and the
zero vector.  Uniform sampler detection is exactly the complement of the
matrix operator's annihilation multiplier.
-/

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixNoise

namespace UniqueGamesTheorem.Decoder.NoiseSampler

section FiniteLaw

variable {Noise V : Type*} [Fintype Noise] [Fintype V]

omit [Fintype V] in
theorem samplerLaw_nonneg (noise : Noise → V) (v : V) :
    0 ≤ samplerLaw noise v := by
  classical
  unfold samplerLaw
  apply Finset.sum_nonneg
  intro n _
  split_ifs <;> positivity

theorem samplerLaw_sum (noise : Noise → V) (f : V → ℝ) :
    (∑ v, samplerLaw noise v * f v) =
      (Fintype.card Noise : ℝ)⁻¹ * ∑ n, f (noise n) := by
  classical
  unfold samplerLaw
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  exact (Finset.mul_sum _ _ _).symm

/-- Exact pushforward expectation, with the uniform normalization explicit. -/
theorem sample_expect_eq (noise : Noise → V) (f : V → ℝ) :
    (𝔼 n, f (noise n)) = ∑ v, samplerLaw noise v * f v := by
  rw [samplerLaw_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm]

theorem samplerLaw_normalized [Nonempty Noise] (noise : Noise → V) :
    ∑ v, samplerLaw noise v = 1 := by
  have h := sample_expect_eq noise (fun _ => 1)
  simpa using h.symm

theorem rat_expect_cast (f : Noise → ℚ) :
    ((𝔼 n, f n : ℚ) : ℝ) = 𝔼 n, (f n : ℝ) := by
  simp only [Finset.expect_eq_sum_div_card, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]

end FiniteLaw

section ActualMultiplier

variable {Noise V E : Type*} [Fintype Noise] [Fintype V]
  [AddCommGroup V] [Module F2 V]
  [AddCommGroup E] [Module F2 E]

/-- The actual matrix multiplier is precisely the sampler's kernel event. -/
theorem sample_kernel_eq_eigenvalue (noise : Noise → V) (S : V →ₗ[F2] E) :
    (𝔼 n, if S (noise n) = 0 then (1 : ℝ) else 0) =
      linearNoiseEigenvalue (samplerLaw noise) S := by
  classical
  exact sample_expect_eq noise (fun v => if S v = 0 then 1 else 0)

end ActualMultiplier

end UniqueGamesTheorem.Decoder.NoiseSampler

end

end

section

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier
open MatrixCharacters MatrixFourier MatrixNoise MatrixEnergy

namespace UniqueGamesTheorem.Decoder.PositiveMultiplier

section FiniteSpectra

variable {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]

/-- A `7/8` bound outside the retained set forces at least `0.92` retained
mass when acceptance is at least `0.99`.  The statement keeps the exact
rational constants, rather than assuming a low-rank mass premise. -/
theorem retained_mass_of_acceptance
    (w : J → ℝ) (a lam : (j : J) → I j → ℝ)
    (keep : (j : J) → I j → Prop)
    (hw : ∀ j, 0 ≤ w j) (htotal : energy w a = 1)
    (hone : ∀ j i, lam j i ≤ 1)
    (hhigh : ∀ j i, ¬ keep j i → lam j i ≤ 7 / 8)
    (haccept : (99 : ℝ) / 100 ≤ spectralEnergy w lam a) :
    (23 : ℝ) / 25 ≤ cutoffEnergy w keep a := by
  classical
  have hp (j : J) (i : I j) :
      lam j i * a j i ^ 2 ≤ (7 / 8 : ℝ) * a j i ^ 2 +
        (1 / 8 : ℝ) * (if keep j i then a j i ^ 2 else 0) := by
    by_cases hk : keep j i
    · have h := mul_le_mul_of_nonneg_right (hone j i) (sq_nonneg (a j i))
      simp only [ite_eq_left hk] at *
      nlinarith
    · have h := mul_le_mul_of_nonneg_right (hhigh j i hk) (sq_nonneg (a j i))
      simpa only [ite_eq_right hk, mul_zero, add_zero] using h
  have hb : spectralEnergy w lam a ≤
      (7 / 8 : ℝ) * energy w a + (1 / 8 : ℝ) * cutoffEnergy w keep a := by
    calc
      _ ≤ ∑ j, w j * ∑ i, ((7 / 8 : ℝ) * a j i ^ 2 +
          (1 / 8 : ℝ) * (if keep j i then a j i ^ 2 else 0)) := by
        exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ => hp j i)) (hw j))
      _ = _ := by
        simp only [energy, cutoffEnergy, Finset.sum_add_distrib,
          Finset.mul_sum, mul_add]
        congr 1 <;>
          (apply Finset.sum_congr rfl
           intro j _
           apply Finset.sum_congr rfl
           intro i _
           ring)
  rw [htotal] at hb
  linarith

theorem positive_multiplier_comparison
    (w : J → ℝ) (a lam τ : (j : J) → I j → ℝ)
    (keep : (j : J) → I j → Prop) (t : ℝ)
    (hw : ∀ j, 0 ≤ w j) (htotal : energy w a = 1) (ht : 0 ≤ t)
    (hone : ∀ j i, lam j i ≤ 1)
    (hhigh : ∀ j i, ¬ keep j i → lam j i ≤ 7 / 8)
    (hτ : ∀ j i, 0 ≤ τ j i)
    (hlow : ∀ j i, keep j i → t ≤ τ j i)
    (haccept : (99 : ℝ) / 100 ≤ spectralEnergy w lam a) :
    (9 : ℝ) / 10 * t ≤ spectralEnergy w τ a := by
  classical
  have hmass := retained_mass_of_acceptance w a lam keep hw htotal hone hhigh haccept
  have hp (j : J) (i : I j) :
      t * (if keep j i then a j i ^ 2 else 0) ≤ τ j i * a j i ^ 2 := by
    by_cases hk : keep j i
    · simpa only [ite_eq_left hk] using
        mul_le_mul_of_nonneg_right (hlow j i hk) (sq_nonneg (a j i))
    · simpa only [ite_eq_right hk, mul_zero] using mul_nonneg (hτ j i) (sq_nonneg (a j i))
  have hb : t * cutoffEnergy w keep a ≤ spectralEnergy w τ a := by
    unfold cutoffEnergy spectralEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc
      t * (w j * ∑ i, if keep j i then a j i ^ 2 else 0) =
          w j * (∑ i, t * (if keep j i then a j i ^ 2 else 0)) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => hp j i)) (hw j)
  have hm := mul_le_mul_of_nonneg_left hmass ht
  nlinarith

/-- A finite probability law with mean at least `14.4 η` assigns mass at
least `10 η` to acceptances at least `4 η`. -/
theorem good_fiber_mass
    {Q : Type*} [Fintype Q] (μ p : Q → ℝ) (η : ℝ)
    (hμ : ∀ q, 0 ≤ μ q) (hμsum : ∑ q, μ q = 1)
    (hη : 0 ≤ η) (hp : ∀ q, p q ≤ 1)
    (hmean : (72 : ℝ) / 5 * η ≤ ∑ q, μ q * p q) :
    10 * η ≤ ∑ q, μ q * if 4 * η ≤ p q then 1 else 0 := by
  classical
  have hbound : (∑ q, μ q * p q) ≤
      4 * η + ∑ q, μ q * if 4 * η ≤ p q then 1 else 0 := by
    calc
      _ ≤ ∑ q, μ q * (4 * η + if 4 * η ≤ p q then 1 else 0) := by
        apply Finset.sum_le_sum
        intro q _
        apply mul_le_mul_of_nonneg_left _ (hμ q)
        split_ifs with hq
        · linarith [hp q]
        · linarith
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hμsum, one_mul]
  linarith

end FiniteSpectra

section ActualMatrixTest

variable {Q C E V : Type*} [Fintype Q] [Fintype C]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
  [Fintype V] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 V] [Fintype V]
  [Fintype (E →ₗ[F2] F2)] [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)] in
theorem color_pair_sum (label : (E →ₗ[F2] V) → C)
    (X Y : E →ₗ[F2] V) :
    (∑ c, colorIndicator label c X * colorIndicator label c Y) =
      if label X = label Y then (1 : ℝ) else 0 := by
  classical
  simp [colorIndicator, eq_comm]

/-- Equality acceptance has the actual positive Fourier multiplier.  Color
indicators give the same equality expansion as output characters, with no
extra factor depending on the output alphabet. -/
theorem equalityAcceptance_fourier (ν : V → ℝ)
    (label : (E →ₗ[F2] V) → C) :
    equalityAcceptance ν label =
      ∑ c, ∑ S : V →ₗ[F2] E,
        linearNoiseEigenvalue ν S * linearCoeff (colorIndicator label c) S ^ 2 := by
  classical
  simp_rw [← linearRealNoiseOperator_energy]
  rw [← Finset.expect_sum_comm]
  unfold equalityAcceptance linearRealNoiseOperator
  apply Finset.expect_congr rfl
  intro X _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  calc
    ν v * (𝔼 l : E →ₗ[F2] F2,
        if label X = label (X + l.smulRight v) then (1 : ℝ) else 0) =
      ν v * (𝔼 l : E →ₗ[F2] F2,
        ∑ c, colorIndicator label c X * colorIndicator label c (X + l.smulRight v)) := by
          simp only [color_pair_sum]
    _ = _ := by
      rw [Finset.expect_sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.mul_expect]
      ring

/-- Spectral comparison applied to a genuine family of matrix labelings.
The two explicit probability laws may be the latent gadget law and uniform
sampling in the distinguished subspace, respectively. -/
theorem matrix_test_comparison
    (μ : Q → ℝ) (ν ρ : V → ℝ)
    (label : Q → (E →ₗ[F2] V) → C)
    (keep : (V →ₗ[F2] E) → Prop) (t : ℝ)
    (hμ : ∀ q, 0 ≤ μ q) (hμsum : ∑ q, μ q = 1)
    (hν : ∀ v, 0 ≤ ν v) (hνsum : ∑ v, ν v = 1)
    (hρ : ∀ v, 0 ≤ ρ v) (ht : 0 ≤ t)
    (hhigh : ∀ S : V →ₗ[F2] E, ¬ keep S → linearNoiseEigenvalue ν S ≤ 7 / 8)
    (hlow : ∀ S : V →ₗ[F2] E, keep S → t ≤ linearNoiseEigenvalue ρ S)
    (haccept : (99 : ℝ) / 100 ≤ ∑ q, μ q * equalityAcceptance ν (label q)) :
    (9 : ℝ) / 10 * t ≤ ∑ q, μ q * equalityAcceptance ρ (label q) := by
  have hs (law : V → ℝ) :
      spectralEnergy (fun qc : Q × C => μ qc.1)
        (fun _ S => linearNoiseEigenvalue law S) (labelingCoeff label) =
          ∑ q, μ q * equalityAcceptance law (label q) := by
    simp only [spectralEnergy, labelingCoeff, Fintype.sum_prod_type,
      equalityAcceptance_fourier, Finset.mul_sum]
  rw [← hs] at haccept ⊢
  apply positive_multiplier_comparison
    (fun qc : Q × C => μ qc.1) (labelingCoeff label)
    (fun _ S => linearNoiseEigenvalue ν S)
    (fun _ S => linearNoiseEigenvalue ρ S) (fun _ S => keep S) t
  · exact fun qc => hμ qc.1
  · exact labelingCoeff_energy_one μ label hμsum
  · exact ht
  · exact fun _ S => linearNoiseEigenvalue_le_one ν S hν hνsum
  · exact fun _ S hS => hhigh S hS
  · exact fun _ S => linearNoiseEigenvalue_nonneg ρ S hρ
  · exact fun _ S hS => hlow S hS
  · exact haccept

end ActualMatrixTest

section UniformSubspace

variable {K V E : Type*}
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K] [Fintype K]
  [AddCommGroup V] [Module F2 V] [Fintype V]
  [AddCommGroup E] [Module F2 E]

omit [FiniteDimensional F2 K] [Fintype V] in
theorem subspaceLaw_nonneg (ι : K →ₗ[F2] V) (v : V) :
    0 ≤ subspaceLaw ι v := by
  classical
  unfold subspaceLaw
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> positivity

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
      (UniqueGamesTheorem.Gadget.LinearKernelCount.zero_event_finset_count_mul_pow_rank (S.comp ι))
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

theorem subspaceLaw_eigenvalue_lower (ι : K →ₗ[F2] V) (S : V →ₗ[F2] E)
    (r : ℕ) (hr : Module.finrank F2 (S.comp ι).range < r) :
    ((2 : ℝ) ^ r)⁻¹ ≤ linearNoiseEigenvalue (subspaceLaw ι) S := by
  rw [subspaceLaw_eigenvalue, ← one_div, ← one_div]
  apply one_div_le_one_div_of_le (pow_pos (by norm_num) _)
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hr)

end UniformSubspace

section ManuscriptComparison

variable {Q C K E V : Type*} [Fintype Q] [Fintype C]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K] [Fintype K]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
  [Fintype V] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)]

theorem matrix_spectral_comparison
    (μ : Q → ℝ) (ν : V → ℝ) (ι : K →ₗ[F2] V)
    (label : Q → (E →ₗ[F2] V) → C) (r : ℕ)
    (hμ : ∀ q, 0 ≤ μ q) (hμsum : ∑ q, μ q = 1)
    (hν : ∀ v, 0 ≤ ν v) (hνsum : ∑ v, ν v = 1)
    (hdetect : ∀ S : V →ₗ[F2] E,
      r ≤ Module.finrank F2 (S.comp ι).range → linearNoiseEigenvalue ν S ≤ 7 / 8)
    (haccept : (99 : ℝ) / 100 ≤ ∑ q, μ q * equalityAcceptance ν (label q)) :
    (9 : ℝ) / 10 * ((2 : ℝ) ^ r)⁻¹ ≤
      ∑ q, μ q * equalityAcceptance (subspaceLaw ι) (label q) := by
  apply matrix_test_comparison μ ν (subspaceLaw ι) label
    (fun S => Module.finrank F2 (S.comp ι).range < r) ((2 : ℝ) ^ r)⁻¹
    hμ hμsum hν hνsum (subspaceLaw_nonneg ι)
  · positivity
  · intro S hS
    exact hdetect S (Nat.le_of_not_gt hS)
  · intro S hS
    exact subspaceLaw_eigenvalue_lower ι S r hS
  · exact haccept

end ManuscriptComparison

end UniqueGamesTheorem.Decoder.PositiveMultiplier

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_DimensionSelection
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Logical dimension is chosen after the inverse density and row bound,
and before the tuple length. All row maps, including deficient-rank maps,
satisfy the resulting small trivial-character bound. -/

namespace UniqueGamesTheorem.Decoder.DimensionSelection

noncomputable section

theorem exists_logical_dimension {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (r lower : ℕ) :
    ∃ ell : ℕ, lower ≤ ell ∧ r < ell ∧
      1 / (2 : ℝ) ^ (ell - r) < α / 8 ∧
      1 / (2 : ℝ) ^ ell < η / 4 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (lt_min (show (0 : ℝ) < α / 8 by positivity)
      (show (0 : ℝ) < η / 4 by positivity))
    (show (1 / 2 : ℝ) < 1 by norm_num)
  let ell := max lower (r + n + 1)
  have hrn : r + n + 1 ≤ ell := le_max_right _ _
  have hr : r < ell := lt_of_lt_of_le (by omega) hrn
  have hnsub : n ≤ ell - r := by omega
  have hnell : n ≤ ell := hnsub.trans (Nat.sub_le _ _)
  have hpow (j : ℕ) (hj : n ≤ j) :
      1 / (2 : ℝ) ^ j < min (α / 8) (η / 4) := by
    have hmon : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    simpa only [one_div, inv_pow] using hmon.trans_lt hn
  exact ⟨ell, le_max_left _ _, hr,
    (hpow (ell - r) hnsub).trans_le (min_le_left _ _),
    (hpow ell hnell).trans_le (min_le_right _ _)⟩

end
end UniqueGamesTheorem.Decoder.DimensionSelection

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_FinishBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Scalar estimates for the construction. These lemmas
only perform the stated rounding/subdivision/repetition arithmetic; they do
not assume or assert an unproved repetition theorem or hardness result.
-/

namespace UniqueGamesTheorem.Explicit.FinishBounds

theorem exists_reciprocal_tolerance (ε : ℚ) (hε : 0 < ε) (t : Nat) (ht : 0 < t) :
    ∃ C : Nat, 200 ≤ C ∧ (0 : ℚ) < 1 / C ∧
      1 / (C : ℚ) ≤ 1 / 200 ∧ 1 / (C : ℚ) ≤ ε / t := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℚ) / ε)
  let C := n + 200
  have hC : (0 : ℚ) < C := by dsimp [C]; positivity
  have ht' : (0 : ℚ) < t := by exact_mod_cast ht
  have hCn : (n : ℚ) ≤ C := by dsimp [C]; exact_mod_cast Nat.le_add_right n 200
  have hbound : (t : ℚ) / ε < C := lt_of_lt_of_le hn hCn
  have hbudget : (t : ℚ) ≤ ε * C := by
    have he := (div_lt_iff₀ hε).mp hbound
    nlinarith
  refine ⟨C, by dsimp [C]; omega, one_div_pos.mpr hC, ?_, ?_⟩
  · apply one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 200)
    dsimp [C]
    exact_mod_cast Nat.le_add_left 200 n
  · apply (div_le_div_iff₀ hC ht').mpr
    simpa [mul_comm] using hbudget

end UniqueGamesTheorem.Explicit.FinishBounds

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_PrivateStrategyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The surrogate perturbation fixes the complementary table exactly. Splitting
the actual uniform matrix law therefore expresses surrogate acceptance as the
mean of the uniform shortcode tests on the `(U,T)` fibers, including zero
perturbation factors. This supplies the sampling identification needed before
applying the inverse theorem to the many useful fibers.
-/

namespace UniqueGamesTheorem.Decoder.SurrogateFibers

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier
open PositiveMultiplier
open scoped BigOperators

noncomputable section

variable {E K W C : Type*}
variable [AddCommGroup E] [Module F2 E]
variable [AddCommGroup K] [Module F2 K] [Fintype K]
variable [AddCommGroup W] [Module F2 W] [Fintype W]
variable [Fintype (E →ₗ[F2] F2)]
variable [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] W)]
variable [Fintype (E →ₗ[F2] K × W)]

omit [Fintype K] [Fintype W] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] W)] [Fintype (E →ₗ[F2] K × W)] in
theorem product_perturbation (M : E →ₗ[F2] K) (T : E →ₗ[F2] W)
    (l : E →ₗ[F2] F2) (a : K) :
    M.prod T + l.smulRight ((LinearMap.inl F2 K W) a) =
      (M + l.smulRight a).prod T := by
  ext x <;> simp

theorem surrogate_acceptance_eq_fiber_average
    (label : (E →ₗ[F2] K × W) → C) :
    equalityAcceptance (subspaceLaw (LinearMap.inl F2 K W)) label =
      𝔼 T : E →ₗ[F2] W,
        shortcodeAcceptance (fun M : E →ₗ[F2] K => label (M.prod T)) := by
  classical
  have hsampling : equalityAcceptance (subspaceLaw (LinearMap.inl F2 K W)) label =
      𝔼 X : E →ₗ[F2] K × W, 𝔼 a : K, 𝔼 l : E →ₗ[F2] F2,
        if label X = label (X + l.smulRight ((LinearMap.inl F2 K W) a)) then
          (1 : ℝ) else 0 := by
    unfold equalityAcceptance
    apply Finset.expect_congr rfl
    intro X _
    rw [subspaceLaw_sum, Fintype.expect_eq_sum_div_card]
    ring
  rw [hsampling, SplitMaps.expect_codomain_product, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro T _
  unfold shortcodeAcceptance
  apply Finset.expect_congr rfl
  intro M _
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro l _
  rw [product_perturbation]

end
end UniqueGamesTheorem.Decoder.SurrogateFibers

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators

noncomputable section

theorem indicator_nonneg (p : Prop) : 0 ≤ indicator p := by
  classical
  unfold indicator
  split <;> norm_num

theorem indicator_le_one (p : Prop) : indicator p ≤ 1 := by
  classical
  unfold indicator
  split <;> norm_num

theorem uniformMass_nonneg {X : Type*} [Fintype X] (p : X → Prop) :
    0 ≤ uniformMass p :=
  Finset.expect_nonneg fun x _ => indicator_nonneg (p x)

theorem replaceOn_of_not_mem {X Y : Type*} (B : X → Prop)
    (f replacement : X → Y) {x : X} (hx : ¬ B x) :
    replaceOn B f replacement x = f x := by
  simp [replaceOn, hx]

theorem replaceOn_of_mem {X Y : Type*} (B : X → Prop)
    (f replacement : X → Y) {x : X} (hx : B x) :
    replaceOn B f replacement x = replacement x := by
  simp [replaceOn, hx]

/-- Deterministic acceptance loss under editing a set of entries. Both endpoint
marginals must equal the matrix-uniform law; no independence of endpoints is
required. This applies to every choice of replacement values. -/
theorem acceptance_le_modified_add_two_mass
    {X Y E : Type*} [Fintype X] [Fintype E]
    (left right : E → X) (B : X → Prop) (f g : X → Y)
    (unchanged : ∀ x, ¬ B x → f x = g x)
    (left_uniform : uniformMass (fun e => B (left e)) = uniformMass B)
    (right_uniform : uniformMass (fun e => B (right e)) = uniformMass B) :
    equalityAcceptance left right f ≤
      equalityAcceptance left right g + 2 * uniformMass B := by
  classical
  have pointwise : ∀ e : E,
      indicator (f (left e) = f (right e)) ≤
        indicator (g (left e) = g (right e)) +
          indicator (B (left e)) + indicator (B (right e)) := by
    intro e
    by_cases hl : B (left e)
    · have h₁ := indicator_le_one (f (left e) = f (right e))
      have h₂ := indicator_nonneg (g (left e) = g (right e))
      have h₃ := indicator_nonneg (B (right e))
      simp only [indicator, ite_eq_left hl] at *
      linarith
    · by_cases hr : B (right e)
      · have h₁ := indicator_le_one (f (left e) = f (right e))
        have h₂ := indicator_nonneg (g (left e) = g (right e))
        simp only [indicator, ite_eq_right hl, ite_eq_left hr] at *
        linarith
      · rw [unchanged _ hl, unchanged _ hr]
        simp [indicator, hl, hr]
  have h := Finset.expect_le_expect (s := Finset.univ) (fun e _ => pointwise e)
  simp only [Finset.expect_add_distrib] at h
  change equalityAcceptance left right f ≤
    equalityAcceptance left right g + uniformMass (fun e => B (left e)) +
      uniformMass (fun e => B (right e)) at h
  rw [left_uniform, right_uniform] at h
  linarith

theorem acceptance_ge_original_sub_two_mass
    {X Y E : Type*} [Fintype X] [Fintype E]
    (left right : E → X) (B : X → Prop) (f replacement : X → Y)
    (left_uniform : uniformMass (fun e => B (left e)) = uniformMass B)
    (right_uniform : uniformMass (fun e => B (right e)) = uniformMass B) :
    equalityAcceptance left right f - 2 * uniformMass B ≤
      equalityAcceptance left right (replaceOn B f replacement) := by
  have h := acceptance_le_modified_add_two_mass left right B f
    (replaceOn B f replacement)
    (fun x hx => (replaceOn_of_not_mem B f replacement hx).symm)
    left_uniform right_uniform
  linarith

theorem adviceMass_nonneg {A X : Type*} [Fintype A] [Fintype X]
    (good : A → X → Prop) : 0 ≤ adviceMass good :=
  Finset.expect_nonneg fun x _ => uniformMass_nonneg (fun a => good a x)

/-- Each matrix in the union has at least one successful row-map atom. No
disjointness between good fibers is needed. -/
theorem union_mass_le_card_mul_adviceMass
    {A X : Type*} [Fintype A] [Fintype X] (good : A → X → Prop) :
    uniformMass (goodUnion good) ≤ (Fintype.card A : ℝ) * adviceMass good := by
  classical
  have pointwise : ∀ x : X, indicator (goodUnion good x) ≤
      (Fintype.card A : ℝ) * uniformMass (fun a => good a x) := by
    intro x
    rw [uniformMass, Fintype.card_mul_expect]
    by_cases hx : goodUnion good x
    · obtain ⟨a, ha⟩ := hx
      have h := Finset.single_le_sum
        (s := (Finset.univ : Finset A)) (f := fun a => indicator (good a x))
        (fun a _ => indicator_nonneg (good a x)) (Finset.mem_univ a)
      simpa [indicator, ha, goodUnion, show ∃ a, good a x from ⟨a, ha⟩] using h
    · simp only [indicator, ite_eq_right hx]
      exact Finset.sum_nonneg fun a _ => indicator_nonneg (good a x)
  have h := Finset.expect_le_expect (s := Finset.univ) (fun x _ => pointwise x)
  simpa only [uniformMass, adviceMass, ← Finset.mul_expect] using h

theorem adviceMass_ge_union_div_card
    {A X : Type*} [Fintype A] [Nonempty A] [Fintype X]
    (good : A → X → Prop) :
    uniformMass (goodUnion good) / (Fintype.card A : ℝ) ≤ adviceMass good := by
  have hcard : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).mpr
  simpa [mul_comm] using union_mass_le_card_mul_adviceMass good

theorem adviceMass_ge_of_union_mass
    {A X : Type*} [Fintype A] [Nonempty A] [Fintype X]
    (good : A → X → Prop) (η : ℝ) (hη : η ≤ uniformMass (goodUnion good)) :
    η / (Fintype.card A : ℝ) ≤ adviceMass good := by
  exact (div_le_div_of_nonneg_right hη (Nat.cast_nonneg _)).trans
    (adviceMass_ge_union_div_card good)

end
end UniqueGamesTheorem.Inverse.RowErasure

end

section

/-!
The row-erasure union bound is eventually strictly below one. The number of
descriptions grows exponentially in `m`, while the tail exponent grows as
`2 ^ ((ell-r)*(m-r))`. The only asymptotic input is the standard proved limit
that a fixed polynomial divided by `2^n` tends to zero.
-/

namespace UniqueGamesTheorem.Inverse.RowErasure

open Filter
open scoped Topology

/-- Logarithm of the finite union-bound estimate, for every sufficiently large
column dimension. Neither the threshold nor the proof depends on a parity
condition on the column dimension. -/
theorem eventually_log_unionBound_neg (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∀ᶠ m : ℕ in atTop,
      (((2 * r + 1) * (ell + m) : ℕ) : ℝ) * Real.log 2 -
        α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32 < 0 := by
  let C : ℝ := (2 * r + 1 : ℕ)
  let D : ℝ := (ell + r : ℕ)
  have hzero : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_zero] using
      (tendsto_pow_const_div_const_pow_of_one_lt 0 (show (1 : ℝ) < 2 by norm_num))
  have hone : Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_one] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 (show (1 : ℝ) < 2 by norm_num))
  have hlim' : Tendsto
      (fun n : ℕ => (C * Real.log 2) * (D * (1 / (2 : ℝ) ^ n) +
        (n : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((hzero.const_mul D).add hone).const_mul (C * Real.log 2)
  have hlim : Tendsto
      (fun n : ℕ => C * (D + (n : ℝ)) * Real.log 2 / (2 : ℝ) ^ n)
      atTop (𝓝 0) := by
    convert hlim' using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    ring
  have hpos : 0 < α ^ 2 / 32 := by positivity
  have hsmall : ∀ᶠ n : ℕ in atTop,
      C * (D + (n : ℝ)) * Real.log 2 / (2 : ℝ) ^ n < α ^ 2 / 32 :=
    hlim.eventually (gt_mem_nhds hpos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  apply eventually_atTop.2
  refine ⟨N + r, ?_⟩
  intro m hm
  have hrm : r ≤ m := by omega
  have hn : N ≤ m - r := by omega
  have hmcast : (m : ℝ) = (r : ℝ) + ((m - r : ℕ) : ℝ) := by
    exact_mod_cast (show m = r + (m - r) by omega)
  have hcast : (((2 * r + 1) * (ell + m) : ℕ) : ℝ) =
      C * (D + ((m - r : ℕ) : ℝ)) := by
    dsimp [C, D]
    push_cast
    rw [hmcast]
    ring
  have hlinear := (div_lt_iff₀ (show (0 : ℝ) < 2 ^ (m - r) by positivity)).1
    (hN (m - r) hn)
  have hexponent : m - r ≤ (ell - r) * (m - r) := by
    have h := Nat.mul_le_mul_right (m - r) (show 1 ≤ ell - r by omega)
    simpa only [one_mul] using h
  have hpower : (2 : ℝ) ^ (m - r) ≤ 2 ^ ((ell - r) * (m - r)) :=
    pow_le_pow_right₀ (by norm_num) hexponent
  have hproduct := mul_le_mul_of_nonneg_left hpower hpos.le
  rw [hcast]
  nlinarith

/-- The exact description-count times tail estimate needed for simultaneous
row erasure is strictly below one in all sufficiently large dimensions. -/
theorem eventually_unionBound_lt_one (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∀ᶠ m : ℕ in atTop,
      (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) < 1 := by
  filter_upwards [eventually_log_unionBound_neg α hα ell r hr] with m hm
  have hpositive : (0 : ℝ) < 2 ^ ((2 * r + 1) * (ell + m)) := by positivity
  calc
    (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) =
        Real.exp ((((2 * r + 1) * (ell + m) : ℕ) : ℝ) * Real.log 2 -
          α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) := by
      rw [← Real.exp_log hpositive, ← Real.exp_add, Real.log_pow]
      congr 1
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr hm

/-- A threshold usable by dimension-selection arguments, with enough columns
to accommodate all `r` prescribed column constraints. -/
theorem exists_unionBound_threshold (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → r ≤ m ∧
      (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) < 1 := by
  exact eventually_atTop.1 ((eventually_ge_atTop r).and
    (eventually_unionBound_lt_one α hα ell r hr))

end UniqueGamesTheorem.Inverse.RowErasure

end

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators

noncomputable section

variable {X Y A S D : Type*}

theorem SliceFamily.mem_erasedUnion_of_good_row
    (F : SliceFamily X Y A S D) (f : X → Y) (α : ℝ) (d : D)
    (good : F.GoodAdvice f α (F.rowMap d) (F.rowValue d))
    {x : X} (hx : x ∈ F.points d) : F.erasedUnion f α x := by
  refine ⟨F.rowMap d, ?_⟩
  change F.GoodAdvice f α (F.rowMap d) (F.advice (F.rowMap d) x)
  rw [F.points_row d x hx]
  exact good

theorem SliceFamily.original_agreement_lt_of_not_good
    (F : SliceFamily X Y A S D) (f : X → Y) (α : ℝ) (d : D)
    (hne : (F.points d).Nonempty)
    (not_good : ¬ F.GoodAdvice f α (F.rowMap d) (F.rowValue d)) :
    F.agreement f d < α / 2 := by
  by_contra h
  exact not_good ⟨d, rfl, rfl, hne, le_of_not_gt h⟩

theorem SliceFamily.modified_agreement_le_original_add_randomized
    (F : SliceFamily X Y A S D) (B : X → Prop)
    (f replacement : X → Y) (d : D) :
    F.agreement (replaceOn B f replacement) d ≤
      F.agreement f d + F.randomizedAgreement B replacement d := by
  classical
  have h := Finset.expect_le_expect (s := F.points d)
    (f := fun x => indicator (replaceOn B f replacement x = F.target d x))
    (g := fun x => indicator (f x = F.target d x) +
      indicator (B x ∧ replacement x = F.target d x)) (by
      intro x _
      by_cases hx : B x
      · rw [replaceOn_of_mem B f replacement hx]
        simp only [indicator, hx, true_and]
        have hnonneg := indicator_nonneg (f x = F.target d x)
        unfold indicator at hnonneg
        linarith
      · rw [replaceOn_of_not_mem B f replacement hx]
        simp [indicator, hx])
  simpa only [Finset.expect_add_distrib, SliceFamily.agreement,
    SliceFamily.randomizedAgreement] using h

theorem SliceFamily.modified_agreement_eq_randomized_of_good
    (F : SliceFamily X Y A S D) (f replacement : X → Y)
    (α : ℝ) (d : D)
    (good : F.GoodAdvice f α (F.rowMap d) (F.rowValue d)) :
    F.agreement (replaceOn (F.erasedUnion f α) f replacement) d =
      F.randomizedAgreement (F.erasedUnion f α) replacement d := by
  classical
  apply Finset.expect_congr rfl
  intro x hx
  have hB := F.mem_erasedUnion_of_good_row f α d good hx
  rw [replaceOn_of_mem _ f replacement hB]
  simp [indicator, hB]

/-- If the random replacement bound holds, *every* permitted nonempty slice
has modified agreement strictly below α. The proof splits on goodness of the
whole row fiber, not on goodness of the individual column slice. -/
theorem SliceFamily.modified_agreement_lt
    (F : SliceFamily X Y A S D) (f replacement : X → Y)
    (α : ℝ) (hα : 0 < α)
    (randomized_small : ∀ d, (F.points d).Nonempty →
      F.randomizedAgreement (F.erasedUnion f α) replacement d < α / 4)
    (d : D) (hne : (F.points d).Nonempty) :
    F.agreement (replaceOn (F.erasedUnion f α) f replacement) d < α := by
  classical
  by_cases hg : F.GoodAdvice f α (F.rowMap d) (F.rowValue d)
  · rw [F.modified_agreement_eq_randomized_of_good f replacement α d hg]
    have h := randomized_small d hne
    linarith
  · have ho := F.original_agreement_lt_of_not_good f α d hne hg
    have hr := randomized_small d hne
    have hm := F.modified_agreement_le_original_add_randomized
      (F.erasedUnion f α) f replacement d
    linarith

/-- Conditional erasure contradiction. The two deep inputs remain explicit:
the inverse theorem for arbitrary (possibly unfolded) functions, and existence
of a replacement table uniformly small on every slice/target description. -/
theorem SliceFamily.union_mass_ge_of_inverse_and_erasure
    {E : Type*} [Fintype X] [Fintype E]
    (F : SliceFamily X Y A S D) (left right : E → X)
    (f : X → Y) (η α : ℝ) (hη : 0 < η) (hα : 0 < α)
    (acceptance_large : 4 * η ≤ equalityAcceptance left right f)
    (left_uniform : ∀ B : X → Prop,
      uniformMass (fun e => B (left e)) = uniformMass B)
    (right_uniform : ∀ B : X → Prop,
      uniformMass (fun e => B (right e)) = uniformMass B)
    (inverse : ∀ g : X → Y, η ≤ equalityAcceptance left right g →
      ∃ d, (F.points d).Nonempty ∧ α ≤ F.agreement g d)
    (erasure : ∃ replacement : X → Y, ∀ d, (F.points d).Nonempty →
      F.randomizedAgreement (F.erasedUnion f α) replacement d < α / 4) :
    η ≤ uniformMass (F.erasedUnion f α) := by
  by_contra h
  have hsmall : uniformMass (F.erasedUnion f α) < η := lt_of_not_ge h
  obtain ⟨replacement, hr⟩ := erasure
  have hmodified := acceptance_ge_original_sub_two_mass left right
    (F.erasedUnion f α) f replacement
    (left_uniform (F.erasedUnion f α)) (right_uniform (F.erasedUnion f α))
  have haccept : η ≤ equalityAcceptance left right
      (replaceOn (F.erasedUnion f α) f replacement) := by linarith
  obtain ⟨d, hne, hd⟩ := inverse _ haccept
  have hlt := F.modified_agreement_lt f replacement α hα hr d hne
  linarith

end
end UniqueGamesTheorem.Inverse.RowErasure

end

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators Classical

noncomputable section

theorem uniformMass_exists_le_sum
    {R D : Type*} [Fintype R] [Fintype D] (bad : D → R → Prop) :
    uniformMass (fun r => ∃ d, bad d r) ≤ ∑ d, uniformMass (bad d) := by
  classical
  have hp : ∀ r, indicator (∃ d, bad d r) ≤ ∑ d, indicator (bad d r) := by
    intro r
    by_cases hr : ∃ d, bad d r
    · obtain ⟨d, hd⟩ := hr
      have h := Finset.single_le_sum
        (s := (Finset.univ : Finset D)) (f := fun d => indicator (bad d r))
        (fun d _ => indicator_nonneg (bad d r)) (Finset.mem_univ d)
      simpa [indicator, hd, show ∃ d, bad d r from ⟨d, hd⟩] using h
    · simp only [indicator, ite_eq_right hr]
      exact Finset.sum_nonneg fun d _ => indicator_nonneg (bad d r)
  have h := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hp r)
  simpa only [uniformMass, Finset.expect_sum_comm] using h

theorem exists_avoiding_of_sum_bad_lt_one
    {R D : Type*} [Fintype R] [Nonempty R] [Fintype D]
    (bad : D → R → Prop) (hsmall : (∑ d, uniformMass (bad d)) < 1) :
    ∃ r, ∀ d, ¬ bad d r := by
  classical
  by_contra h
  have hall : ∀ r, ∃ d, bad d r := by
    intro r
    by_contra hr
    exact h ⟨r, fun d hd => hr ⟨d, hd⟩⟩
  have hm : uniformMass (fun r => ∃ d, bad d r) = 1 := by
    simp [uniformMass, indicator, hall]
  have hb := uniformMass_exists_le_sum bad
  rw [hm] at hb
  linarith

theorem exists_avoiding_of_card_mul_bound_lt_one
    {R D : Type*} [Fintype R] [Nonempty R] [Fintype D]
    (bad : D → R → Prop) (ρ : ℝ)
    (hprob : ∀ d, uniformMass (bad d) ≤ ρ)
    (hsmall : (Fintype.card D : ℝ) * ρ < 1) :
    ∃ r, ∀ d, ¬ bad d r := by
  apply exists_avoiding_of_sum_bad_lt_one bad
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset D)) (fun d _ => hprob d)
  have hsum : (∑ d, uniformMass (bad d)) ≤ (Fintype.card D : ℝ) * ρ := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  exact hsum.trans_lt hsmall

/-- The union-bound step for actual replacement tables. Nonempty slice
descriptions with randomized agreement at least α/4 are the bad events. -/
theorem SliceFamily.exists_erasure_of_probability_bound
    {X Y A S D : Type*} [Fintype X] [Fintype Y] [Nonempty Y] [Fintype D]
    (F : SliceFamily X Y A S D) (B : X → Prop) (α ρ : ℝ)
    (hprob : ∀ d, uniformMass (fun replacement : X → Y =>
      (F.points d).Nonempty ∧ α / 4 ≤ F.randomizedAgreement B replacement d) ≤ ρ)
    (hsmall : (Fintype.card D : ℝ) * ρ < 1) :
    ∃ replacement : X → Y, ∀ d, (F.points d).Nonempty →
      F.randomizedAgreement B replacement d < α / 4 := by
  obtain ⟨replacement, hr⟩ := exists_avoiding_of_card_mul_bound_lt_one
    (fun d replacement =>
      (F.points d).Nonempty ∧ α / 4 ≤ F.randomizedAgreement B replacement d)
    ρ hprob hsmall
  refine ⟨replacement, fun d hd => ?_⟩
  exact lt_of_not_ge (fun h => hr d ⟨hd, h⟩)

/-- Average the fixed-context advice bound over the spectral good contexts.
Both samples remain explicit: the context, then the row map and matrix. -/
theorem advice_average_ge
    {Q A X : Type*} [Fintype Q] [Fintype A] [Nonempty A] [Fintype X]
    (goodContext : Q → Prop) (good : Q → A → X → Prop)
    (β η : ℝ) (hη : 0 ≤ η)
    (hcontext : β ≤ uniformMass goodContext)
    (hlocal : ∀ q, goodContext q → η ≤ uniformMass (goodUnion (good q))) :
    β * (η / (Fintype.card A : ℝ)) ≤
      Finset.univ.expect (fun q => adviceMass (good q)) := by
  classical
  have hc : 0 ≤ η / (Fintype.card A : ℝ) :=
    div_nonneg hη (Nat.cast_nonneg _)
  have hp : ∀ q,
      indicator (goodContext q) * (η / (Fintype.card A : ℝ)) ≤ adviceMass (good q) := by
    intro q
    by_cases hq : goodContext q
    · simpa [indicator, hq] using adviceMass_ge_of_union_mass (good q) η (hlocal q hq)
    · simpa [indicator, hq] using adviceMass_nonneg (good q)
  have he := Finset.expect_le_expect (s := Finset.univ) (fun q _ => hp q)
  rw [← Finset.expect_mul] at he
  exact (mul_le_mul_of_nonneg_right hcontext hc).trans he

theorem advice_average_ge_ten_eta_sq_div_card
    {Q A X : Type*} [Fintype Q] [Fintype A] [Nonempty A] [Fintype X]
    (goodContext : Q → Prop) (good : Q → A → X → Prop)
    (η : ℝ) (hη : 0 ≤ η)
    (hcontext : 10 * η ≤ uniformMass goodContext)
    (hlocal : ∀ q, goodContext q → η ≤ uniformMass (goodUnion (good q))) :
    10 * η ^ 2 / (Fintype.card A : ℝ) ≤
      Finset.univ.expect (fun q => adviceMass (good q)) := by
  have h := advice_average_ge goodContext good (10 * η) η hη hcontext hlocal
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end UniqueGamesTheorem.Inverse.RowErasure

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureConcentration
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators Classical

noncomputable section

theorem table_expect_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → ℝ) :
    Finset.univ.expect (fun r : X → Y => ∏ x, f x (r x)) =
      ∏ x, Finset.univ.expect (f x) := by
  classical
  simp only [Fintype.expect_eq_sum_div_card, ← Fintype.prod_sum,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Nat.cast_pow]

private theorem exp_half_le_seven_quarters : Real.exp (1 / 2 : ℝ) ≤ 7 / 4 := by
  have h := Real.exp_bound' (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem exp_half_indicator (P : Prop) :
    Real.exp (indicator P / 2) = 1 + (Real.exp (1 / 2 : ℝ) - 1) * indicator P := by
  classical
  by_cases h : P <;> simp [indicator, h]

theorem table_coordinate_exp_le {Y : Type*} [Fintype Y] [Nonempty Y]
    (P : Prop) (target : Y) :
    Finset.univ.expect (fun y => Real.exp (indicator (P ∧ y = target) / 2)) ≤
      Real.exp (3 / (4 * (Fintype.card Y : ℝ))) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  by_cases hP : P
  · have hsingle : Finset.univ.expect (fun y : Y => indicator (y = target)) =
        1 / (Fintype.card Y : ℝ) := by
      simp [indicator]
    have heq : Finset.univ.expect
        (fun y => Real.exp (indicator (P ∧ y = target) / 2)) =
        1 + (Real.exp (1 / 2 : ℝ) - 1) / (Fintype.card Y : ℝ) := by
      simp_rw [hP, true_and, exp_half_indicator]
      rw [Finset.expect_add_distrib, ← Finset.mul_expect, hsingle]
      simp [div_eq_mul_inv]
    rw [heq]
    calc
      1 + (Real.exp (1 / 2 : ℝ) - 1) / (Fintype.card Y : ℝ) ≤
          1 + 3 / (4 * (Fintype.card Y : ℝ)) := by
        have h := div_le_div_of_nonneg_right
          (show Real.exp (1 / 2 : ℝ) - 1 ≤ 3 / 4 by
            linarith [exp_half_le_seven_quarters]) hcard.le
        simpa only [div_div, add_comm] using add_le_add_left h 1
      _ ≤ Real.exp (3 / (4 * (Fintype.card Y : ℝ))) := by
        simpa only [add_comm] using Real.add_one_le_exp (3 / (4 * (Fintype.card Y : ℝ)))
  · simp only [hP, false_and, indicator_false, zero_div, Real.exp_zero,
      Fintype.expect_const]
    exact Real.one_le_exp (by positivity)

end
end UniqueGamesTheorem.Inverse.RowErasure

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureTail
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators Classical

noncomputable section

private theorem randomizedMatches_eq_masked_sum
    {X Y : Type*} [Fintype X] (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) :
    randomizedMatches s B target replacement =
      ∑ x, indicator (x ∈ s ∧ B x ∧ replacement x = target x) := by
  classical
  symm
  calc
    (∑ x, indicator (x ∈ s ∧ B x ∧ replacement x = target x)) =
        ∑ x ∈ s, indicator (x ∈ s ∧ B x ∧ replacement x = target x) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro x _ hx
      simp [indicator, hx]
    _ = randomizedMatches s B target replacement := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [indicator, hx]

private theorem randomizedMatches_exp_product
    {X Y : Type*} [Fintype X] (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) :
    Real.exp (randomizedMatches s B target replacement / 2) =
      ∏ x, Real.exp (indicator (x ∈ s ∧ B x ∧ replacement x = target x) / 2) := by
  rw [randomizedMatches_eq_masked_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul, Real.exp_sum]

private theorem table_randomizedMatches_mgf_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    (s : Finset X) (B : X → Prop) (target : X → Y) :
    Finset.univ.expect (fun replacement : X → Y =>
      Real.exp (randomizedMatches s B target replacement / 2)) =
      ∏ x, Finset.univ.expect (fun y : Y =>
        Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2)) := by
  classical
  calc
    _ = Finset.univ.expect (fun replacement : X → Y =>
        ∏ x, Real.exp (indicator (x ∈ s ∧ B x ∧ replacement x = target x) / 2)) := by
      apply Finset.expect_congr rfl
      intro replacement _
      exact randomizedMatches_exp_product s B target replacement
    _ = _ := table_expect_prod (X := X) (Y := Y)
      (fun x y => Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))

private theorem table_randomizedMatches_product_le
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : Finset X) (B : X → Prop) (target : X → Y) :
    (∏ x, Finset.univ.expect (fun y : Y =>
      Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))) ≤
      Real.exp (3 / (4 * (Fintype.card Y : ℝ)) * s.card) := by
  classical
  let c : ℝ := 3 / (4 * (Fintype.card Y : ℝ))
  have hpoint : ∀ x : X,
      Finset.univ.expect (fun y : Y =>
        Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2)) ≤
      Real.exp (if x ∈ s then c else 0) := by
    intro x
    by_cases hx : x ∈ s
    · simpa only [hx, true_and, ite_true, if_true] using table_coordinate_exp_le (B x) (target x)
    · simp [hx, indicator]
  calc
    (∏ x, Finset.univ.expect (fun y : Y =>
        Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))) ≤
        ∏ x, Real.exp (if x ∈ s then c else 0) := by
      apply Finset.prod_le_prod
      · intro x _
        exact Finset.expect_nonneg fun _ _ => (Real.exp_pos _).le
      · intro x _
        exact hpoint x
    _ = Real.exp (3 / (4 * (Fintype.card Y : ℝ)) * s.card) := by
      rw [← Real.exp_sum]
      congr 1
      simp [c, mul_comm]

theorem table_randomizedMatches_mgf_le
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : Finset X) (B : X → Prop) (target : X → Y) :
    Finset.univ.expect (fun replacement : X → Y =>
      Real.exp (randomizedMatches s B target replacement / 2)) ≤
      Real.exp (3 / (4 * (Fintype.card Y : ℝ)) * s.card) := by
  rw [table_randomizedMatches_mgf_eq]
  exact table_randomizedMatches_product_le s B target

theorem uniformMass_mono {R : Type*} [Fintype R]
    {p q : R → Prop} (h : ∀ r, p r → q r) : uniformMass p ≤ uniformMass q := by
  classical
  apply Finset.expect_le_expect
  intro r _
  by_cases hp : p r
  · simp [indicator, hp, h r hp]
  · simpa [indicator, hp] using indicator_nonneg (q r)

/-- A full uniform table supplies independent coordinate samples. Only the
entries in `B ∩ s` contribute; all other entries deterministically contribute 0. -/
theorem table_randomizedMatches_tail_le
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : Finset X) (B : X → Prop) (target : X → Y)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hsmall : 1 / (Fintype.card Y : ℝ) ≤ α / 8) :
    uniformMass (fun replacement : X → Y =>
      α * s.card / 4 ≤ randomizedMatches s B target replacement) ≤
      Real.exp (-(α ^ 2 * s.card) / 32) := by
  classical
  let N : ℝ := s.card
  let c : ℝ := 3 / (4 * (Fintype.card Y : ℝ))
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hp : ∀ replacement : X → Y,
      indicator (α * s.card / 4 ≤ randomizedMatches s B target replacement) ≤
        Real.exp (-(α * N) / 8) *
          Real.exp (randomizedMatches s B target replacement / 2) := by
    intro replacement
    by_cases h : α * s.card / 4 ≤ randomizedMatches s B target replacement
    · rw [show indicator (α * s.card / 4 ≤ randomizedMatches s B target replacement) = 1
          from by simp [indicator, h], ← Real.exp_add]
      apply Real.one_le_exp
      dsimp [N]
      linarith
    · simp only [indicator, ite_eq_right h]
      positivity
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun replacement _ => hp replacement)
  change uniformMass _ ≤ _ at hm
  rw [← Finset.mul_expect] at hm
  have hmgf := table_randomizedMatches_mgf_le s B target
  have hc : c ≤ 3 * α / 32 := by
    dsimp [c]
    calc
      3 / (4 * (Fintype.card Y : ℝ)) = (3 / 4) * (1 / (Fintype.card Y : ℝ)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ 3 * α / 32 := by nlinarith [hsmall]
  have hexponent : -(α * N) / 8 + c * N ≤ -(α ^ 2 * N) / 32 := by
    have hcN := mul_le_mul_of_nonneg_right hc hN
    have hsq : α ^ 2 ≤ α := by
      nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hαone)]
    have hsqN := mul_le_mul_of_nonneg_right hsq hN
    nlinarith
  calc
    uniformMass (fun replacement : X → Y =>
        α * s.card / 4 ≤ randomizedMatches s B target replacement) ≤
        Real.exp (-(α * N) / 8) *
          Finset.univ.expect (fun replacement : X → Y =>
            Real.exp (randomizedMatches s B target replacement / 2)) := hm
    _ ≤ Real.exp (-(α * N) / 8) * Real.exp (c * N) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-(α * N) / 8 + c * N) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(α ^ 2 * s.card) / 32) := Real.exp_le_exp.mpr hexponent

/-- The per-description bound used by the simultaneous erasure union bound. -/
theorem SliceFamily.randomizedAgreement_probability_le
    {X Y A S D : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (F : SliceFamily X Y A S D) (B : X → Prop) (α : ℝ)
    (hα : 0 < α) (hαone : α ≤ 1)
    (hsmall : 1 / (Fintype.card Y : ℝ) ≤ α / 8) (d : D) :
    uniformMass (fun replacement : X → Y =>
      (F.points d).Nonempty ∧ α / 4 ≤ F.randomizedAgreement B replacement d) ≤
      Real.exp (-(α ^ 2 * (F.points d).card) / 32) := by
  apply le_trans (uniformMass_mono ?_) (table_randomizedMatches_tail_le
    (F.points d) B (F.target d) α hα hαone hsmall)
  intro replacement h
  have hcard : (0 : ℝ) < (F.points d).card := Nat.cast_pos.mpr h.1.card_pos
  have hmass := h.2
  rw [SliceFamily.randomizedAgreement, Finset.expect_eq_sum_div_card] at hmass
  have hm := (le_div_iff₀ hcard).mp hmass
  dsimp [randomizedMatches]
  nlinarith

end
end UniqueGamesTheorem.Inverse.RowErasure

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeInterfaceLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The size bound for simultaneous row/column slices.
Starting at any point of a nonempty slice, maps from the quotient by its column
span into the common row kernel give distinct points of that same affine slice.
Rank-nullity gives the dimension lower bound even when equations are dependent.
This argument uses only finite-dimensional linear algebra.
-/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Matrix

namespace Slice

variable {ell m : ℕ}

theorem columnSpan_finrank_le (S : Slice ell m) :
    Module.finrank F2 S.columnSpan ≤ S.columns := by
  have h := finrank_range_le_card (R := F2) (M := Vector m) S.columnCoefficient
  change Module.finrank F2 (Submodule.span F2 (Set.range S.columnCoefficient)) ≤
    Fintype.card (Fin S.columns) at h
  rw [Fintype.card_fin] at h
  exact h

theorem quotient_finrank_ge (S : Slice ell m) :
    m - S.columns ≤ Module.finrank F2 (Vector m ⧸ S.columnSpan) := by
  have h := S.columnSpan.finrank_quotient_add_finrank
  have hspan := S.columnSpan_finrank_le
  have hm : Module.finrank F2 (Vector m) = m := by simp [Vector]
  rw [hm] at h
  omega

theorem rowKernel_finrank_ge (S : Slice ell m) :
    ell - S.rows ≤ Module.finrank F2 S.rowMap.ker := by
  have h := S.rowMap.finrank_range_add_finrank_ker
  have hrange : Module.finrank F2 S.rowMap.range ≤ S.rows := by
    exact S.rowMap.range.finrank_le.trans_eq (by simp [Vector])
  have hell : Module.finrank F2 (Vector ell) = ell := by simp [Vector]
  rw [hell] at h
  omega

theorem card_directions (S : Slice ell m) :
    Nat.card S.Directions =
      2 ^ (Module.finrank F2 (Vector m ⧸ S.columnSpan) *
        Module.finrank F2 S.rowMap.ker) := by
  rw [Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

/-- A nonempty affine slice is at least as large as its free-direction space. -/
theorem card_directions_le (S : Slice ell m) (hne : S.points.Nonempty) :
    Nat.card S.Directions ≤ S.points.card := by
  obtain ⟨M, hM⟩ := hne
  have hcontains : S.Contains M := by simpa only [points, Finset.mem_filter,
    Finset.mem_univ, true_and] using hM
  simpa only [Nat.card_eq_finsetCard] using
    Nat.card_le_card_of_injective (S.directionEmbedding M hcontains)
      (S.directionEmbedding M hcontains).injective

/-- The size bound, with truncation making it valid also in small dimensions.
There is no independence hypothesis on the listed equations. -/
theorem pow_dimension_le_card (S : Slice ell m) (r : ℕ)
    (hrows : S.rows ≤ r) (hcolumns : S.columns ≤ r)
    (hne : S.points.Nonempty) :
    2 ^ ((ell - r) * (m - r)) ≤ S.points.card := by
  have hrow : ell - r ≤ Module.finrank F2 S.rowMap.ker :=
    (Nat.sub_le_sub_left hrows ell).trans S.rowKernel_finrank_ge
  have hcol : m - r ≤ Module.finrank F2 (Vector m ⧸ S.columnSpan) :=
    (Nat.sub_le_sub_left hcolumns m).trans S.quotient_finrank_ge
  have hmul := Nat.mul_le_mul hcol hrow
  rw [Nat.mul_comm (m - r) (ell - r)] at hmul
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hmul
  rw [← S.card_directions] at hp
  exact hp.trans (S.card_directions_le hne)

end Slice
end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

/-!
Fixed-length descriptions for the row-erasure union bound. Row and column
equation lists are padded with zero equations. Targets retain both the linear
coefficient and the affine intercept. Thus the finite description count is
exactly `2^((2r+1)(ell+m))`, including descriptions with empty solution sets.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureDescriptions

open UniqueGamesTheorem.Inverse.Shortcode
open scoped BigOperators

noncomputable section

theorem card_vector (n : ℕ) : Fintype.card (Vector n) = 2 ^ n := by
  simp [Shortcode.Vector, F2]

theorem card_rowMap (ell r : ℕ) : Fintype.card (RowMap ell r) = 2 ^ (ell * r) := by
  simp [RowMap, ← pow_mul]

theorem card_description (ell m r : ℕ) :
    Fintype.card (Description ell m r) = 2 ^ ((2 * r + 1) * (ell + m)) := by
  simp only [Description, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ← pow_mul, ← pow_add]
  congr 1
  ring

theorem padSlice_contains_iff {ell m r : ℕ} (S : Slice ell m)
    (hrows : S.rows ≤ r) (hcols : S.columns ≤ r) (M : Mat ell m) :
    (padSlice S r).Contains M ↔ S.Contains M := by
  classical
  constructor
  · rintro ⟨hr, hc⟩
    constructor
    · intro i j
      have h := hr ⟨i.val, lt_of_lt_of_le i.isLt hrows⟩ j
      simpa [padSlice, padZero, i.isLt] using h
    · intro i
      have h := hc ⟨i.val, lt_of_lt_of_le i.isLt hcols⟩
      simpa [padSlice, padZero, i.isLt] using h
  · rintro ⟨hr, hc⟩
    constructor
    · intro i j
      by_cases hi : i.val < S.rows
      · simpa [padSlice, padZero, hi] using hr ⟨i.val, hi⟩ j
      · simp [padSlice, padZero, hi]
    · intro i
      by_cases hi : i.val < S.columns
      · simpa [padSlice, padZero, hi] using hc ⟨i.val, hi⟩
      · simp [padSlice, padZero, hi]

theorem padSlice_points {ell m r : ℕ} (S : Slice ell m)
    (hrows : S.rows ≤ r) (hcols : S.columns ≤ r) :
    (padSlice S r).points = S.points := by
  classical
  ext M
  simp [Slice.points, padSlice_contains_iff S hrows hcols M]

theorem padSlice_affineAgreement {ell m r : ℕ} (S : Slice ell m)
    (hrows : S.rows ≤ r) (hcols : S.columns ≤ r)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell) :
    (padSlice S r).affineAgreement f z u = S.affineAgreement f z u := by
  simp only [Slice.affineAgreement, padSlice_points S hrows hcols]

end
end UniqueGamesTheorem.Inverse.RowErasureDescriptions

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureMatrixLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open scoped BigOperators Classical

noncomputable section

theorem expect_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X × Y → ℝ) :
    Finset.univ.expect f =
      Finset.univ.expect (fun x => Finset.univ.expect fun y => f (x, y)) := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, mul_inv_rev]
  ring

theorem left_uniform {ell m : ℕ} (B : Mat ell m → Prop) :
    uniformMass (fun e : Samples ell m => B (left e)) = uniformMass B := by
  unfold uniformMass
  rw [expect_prod]
  simp only [left, Fintype.expect_const]

theorem right_uniform {ell m : ℕ} (B : Mat ell m → Prop) :
    uniformMass (fun e : Samples ell m => B (right e)) = uniformMass B := by
  have h := Fintype.expect_equiv (stepEquiv ell m)
    (fun e => indicator (B (right e))) (fun e => indicator (B (left e)))
    (fun _ => rfl)
  exact h.trans (left_uniform B)

theorem acceptance_eq {ell m : ℕ} (f : Mat ell m → Vector ell) :
    RowErasure.equalityAcceptance (left (ell := ell) (m := m)) right f =
      Shortcode.equalityAcceptance f := by
  classical
  unfold RowErasure.equalityAcceptance uniformMass Shortcode.equalityAcceptance
  rw [expect_prod]
  apply Finset.expect_congr rfl
  intro M _
  rw [expect_prod]
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro l _
  by_cases h : f M = f (M + rankOne a l)
  · simp [indicator, left, right, h]
  · simp [indicator, left, right, h]

/-- Zero-padding turns the actual bounded-slice inverse conclusion into the
description-based inverse conclusion used by the erasure proof. -/
theorem described_inverse {ell m r : ℕ} (α η : ℝ)
    (inverse : ∀ f : Mat ell m → Vector ell,
      η ≤ Shortcode.equalityAcceptance f → HasAffineSlice f α r) :
    ∀ f : Mat ell m → Vector ell,
      η ≤ RowErasure.equalityAcceptance (left (ell := ell) (m := m)) right f →
        ∃ d : Description ell m r, ((family ell m r).points d).Nonempty ∧
          α ≤ (family ell m r).agreement f d := by
  intro f hf
  rw [acceptance_eq] at hf
  obtain ⟨S, hrows, hcols, hne, z, u, hagree⟩ := inverse f hf
  refine ⟨describe S z u, ?_, ?_⟩
  · change (padSlice S r).points.Nonempty
    simpa only [padSlice_points S hrows hcols] using hne
  · rw [family_agreement]
    simpa only [describe_toSlice, describe_coefficient, describe_intercept,
      padSlice_affineAgreement S hrows hcols] using hagree

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

section

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open scoped BigOperators

noncomputable section

/-- One replacement table simultaneously defeats every padded slice/target.
The budget depends only on dimensions and α, not on the labeling or erased set. -/
theorem exists_replacement_of_budget {ell m r : ℕ}
    (B : Mat ell m → Prop) (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8)
    (hbudget : (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
      Real.exp (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32) < 1) :
    ∃ replacement : Mat ell m → Vector ell,
      ∀ d : Description ell m r, ((family ell m r).points d).Nonempty →
        (family ell m r).randomizedAgreement B replacement d < α / 4 := by
  let ρ := Real.exp (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32)
  apply (family ell m r).exists_erasure_of_probability_bound B α ρ
  · intro d
    by_cases hne : ((family ell m r).points d).Nonempty
    · have htail := (family ell m r).randomizedAgreement_probability_le B α hα hαone
        (by simpa only [card_vector, Nat.cast_pow, Nat.cast_ofNat] using halphabet) d
      have hcardNat := d.toSlice.pow_dimension_le_card r le_rfl le_rfl hne
      have hcard : (2 : ℝ) ^ ((ell - r) * (m - r)) ≤
          (((family ell m r).points d).card : ℝ) := by
        exact_mod_cast hcardNat
      apply htail.trans
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hcard (sq_nonneg α)
      linarith
    · simpa [uniformMass, indicator, hne] using (Real.exp_pos
        (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32)).le
  · simpa only [card_description, Nat.cast_pow, Nat.cast_ofNat] using hbudget

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

section

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open scoped BigOperators

noncomputable section

/-- A single dimension threshold supplies replacements for every erased set.
There is no inverse-theorem premise in this concentration/counting statement. -/
theorem exists_erasure_threshold (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (ell r : ℕ) (hr : r < ell) (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ B : Mat ell m → Prop,
        ∃ replacement : Mat ell m → Vector ell,
          ∀ d : Description ell m r, ((family ell m r).points d).Nonempty →
            (family ell m r).randomizedAgreement B replacement d < α / 4 := by
  obtain ⟨m₀, hm₀⟩ := exists_unionBound_threshold α hα ell r hr
  refine ⟨m₀, ?_⟩
  intro m hm B
  apply exists_replacement_of_budget B α hα hαone halphabet
  simpa only [neg_mul] using (hm₀ m hm).2

theorem exists_contextual_advice_threshold (η α : ℝ)
    (hη : 0 < η) (hα : 0 < α) (hαone : α ≤ 1)
    (ell r : ℕ) (hr : r < ell) (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (∀ g : Mat ell m → Vector ell,
        η ≤ Shortcode.equalityAcceptance g → HasAffineSlice g α r) →
      ∀ (Q : Type) [Fintype Q] (f : Q → Mat ell m → Vector ell),
        10 * η ≤ uniformMass (fun q => 4 * η ≤ Shortcode.equalityAcceptance (f q)) →
          10 * η ^ 2 / (2 ^ (ell * r) : ℝ) ≤
            Finset.univ.expect (fun q => adviceMass ((family ell m r).goodAt (f q) α)) := by
  obtain ⟨m₀, hm₀⟩ := exists_erasure_threshold α hα hαone ell r hr halphabet
  refine ⟨m₀, ?_⟩
  intro m hm inverse Q _ f hcontext
  have hlocal : ∀ q : Q, 4 * η ≤ Shortcode.equalityAcceptance (f q) →
      η ≤ uniformMass (goodUnion ((family ell m r).goodAt (f q) α)) := by
    intro q hq
    exact (family ell m r).union_mass_ge_of_inverse_and_erasure
      left right (f q) η α hη hα
      (by simpa only [acceptance_eq] using hq)
      left_uniform right_uniform (described_inverse α η inverse)
      (hm₀ m hm ((family ell m r).erasedUnion (f q) α))
  have h := advice_average_ge_ten_eta_sq_div_card
    (fun q => 4 * η ≤ Shortcode.equalityAcceptance (f q))
    (fun q => (family ell m r).goodAt (f q) α) η hη.le hcontext hlocal
  simpa only [card_rowMap, Nat.cast_pow, Nat.cast_ofNat] using h

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_MatrixCoordinates
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Decoder.MatrixCoordinates

open Integration.BinaryLinear Reduction
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem indicator_congr (P Q : Prop) (dP : Decidable P) (dQ : Decidable Q)
    (h : P ↔ Q) : @ite ℝ P dP 1 0 = @ite ℝ Q dQ 1 0 := by
  cases propext h
  cases Subsingleton.elim dP dQ
  rfl

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.MatrixCoordinates.homFintype
/-- Coordinate change preserves the complete uniform matrix equality test. -/
theorem shortcodeAcceptance_eq (k ell : ℕ)
    (f : (ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) → (Fin ell → F2)) :
    SurrogateFibers.shortcodeAcceptance f =
      Inverse.Shortcode.equalityAcceptance (fun M => f ((mapEquiv k ell).symm M)) := by
  unfold SurrogateFibers.shortcodeAcceptance Inverse.Shortcode.equalityAcceptance
  apply Fintype.expect_equiv (mapEquiv k ell).toEquiv
  intro M
  apply Finset.expect_congr rfl
  intro a _
  apply Fintype.expect_equiv (functionalEquiv k).toEquiv
  intro l
  simp only [LinearEquiv.coe_toEquiv, mapEquiv_symm_add_rankOne,
    LinearEquiv.symm_apply_apply]
  exact indicator_congr _ _ _ _ Iff.rfl

end
end UniqueGamesTheorem.Decoder.MatrixCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_MaskMomentLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Clean

open Foundations.Games
open scoped BigOperators

noncomputable section

variable {E : Type*} [Fintype E] [Nonempty E]

/-- The exponential estimate uses nonnegativity of `1 - x` before raising to
a natural power. It also covers the empty mask. -/
theorem mask_rate_le_exp {x : ℝ} (hx : x ≤ 1) (k : ℕ) :
    (1 - x) ^ k ≤ Real.exp (-(k : ℝ) * x) := by
  calc
    (1 - x) ^ k ≤ Real.exp (-x) ^ k :=
      pow_le_pow_left₀ (sub_nonneg.mpr hx) (Real.one_sub_le_exp_neg x) k
    _ = Real.exp (-(k : ℝ) * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem cube_singleton_probability_le_one {n : ℕ} (hn : 1 ≤ n) :
    (1 / (n : ℝ)) ^ 2 ≤ 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq₀ : 0 ≤ 1 / (n : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hq₁ : 1 / (n : ℝ) ≤ 1 :=
    (div_le_iff₀ (by linarith)).mpr (by simpa using hn')
  nlinarith [mul_nonneg hq₀ (sub_nonneg.mpr hq₁)]

/-- On cubes, `k = n^3` and `beta = n^(-2)`, so `k * beta = n`.
The advice-space size bound `N` is fixed independently of `n`. -/
theorem cube_mask_rate_le_exp {n : ℕ} (hn : 1 ≤ n) {N : ℝ} (hN : 1 ≤ N) :
    (1 - ((1 / (n : ℝ)) ^ 2 / N) / 3600) ^ (n ^ 3) ≤
      Real.exp (-(n : ℝ) / (3600 * N)) := by
  have hn₀ : (n : ℝ) ≠ 0 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hN₀ : N ≠ 0 := by linarith
  have hq : (1 / (n : ℝ)) ^ 2 / N ≤ 1 :=
    (div_le_iff₀ (by linarith)).mpr
      (by simpa using (cube_singleton_probability_le_one hn).trans hN)
  have hx : (1 / (n : ℝ)) ^ 2 / N / 3600 ≤ 1 :=
    (div_le_iff₀ (by norm_num)).mpr (by linarith)
  have he : -((n ^ 3 : ℕ) : ℝ) * ((1 / (n : ℝ)) ^ 2 / N / 3600) =
      -(n : ℝ) / (3600 * N) := by
    simp only [Nat.cast_pow]
    field_simp [hn₀, hN₀]
  calc
    _ ≤ Real.exp (-((n ^ 3 : ℕ) : ℝ) * ((1 / (n : ℝ)) ^ 2 / N / 3600)) :=
      mask_rate_le_exp hx (n ^ 3)
    _ = _ := congrArg Real.exp he

/-- A repetition cube can be selected after fixing only the advice-space size
bound and the required error. This is a scalar fact, not a game-value theorem. -/
theorem exists_cube_exponential_lt {N error : ℝ} (hN : 0 < N) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ Real.exp (-(n : ℝ) / (3600 * N)) < error := by
  let rate := Real.exp (-(1 / (3600 * N)))
  have hrate₀ : 0 ≤ rate := (Real.exp_pos _).le
  have hrate₁ : rate < 1 := Real.exp_lt_one_iff.mpr
    (neg_lt_zero.mpr (one_div_pos.mpr (mul_pos (by norm_num) hN)))
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hrate₀ hrate₁
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds herror)).exists
  refine ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m), ?_⟩
  have hp : rate ^ (m + 1) < error :=
    lt_of_le_of_lt (by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hrate₀ m) hrate₁.le) hm
  have he : Real.exp (-((m + 1 : ℕ) : ℝ) / (3600 * N)) = rate ^ (m + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [he]

end
end UniqueGamesTheorem.Clean

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_SparseLawLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The finite calculation of projected total variation. The three singleton
lines are averaged before the divergence is taken; projection choices are
not part of the compared sample space. Coordinates are independently sampled
occurrences, irrespective of whether their equation IDs coincide.
-/

namespace UniqueGamesTheorem.Decoder.SparseLaw

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Information

noncomputable section

variable {α : Type*} [Fintype α]

theorem uniformChiSquare_eq_secondMoment [Nonempty α] (p : α → ℝ)
    (hp : IsProbability p) :
    uniformChiSquare p = (Fintype.card α : ℝ) * (∑ a, p a ^ 2) - 1 := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpoint (a : α) :
      (Fintype.card α : ℝ) * (p a - uniformWeights α a) ^ 2 =
        (Fintype.card α : ℝ) * p a ^ 2 - 2 * p a + uniformWeights α a := by
    simp only [uniformWeights]
    field_simp [hn]
    ring
  rw [uniformChiSquare, Finset.mul_sum]
  simp only [hpoint, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2,
    (uniformWeights_isProbability (α := α)).2]
  ring

theorem mixture_isProbability [Nonempty α] (p : α → ℝ) (hp : IsProbability p)
    {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1) : IsProbability (mixture β p) := by
  constructor
  · intro a
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hβ') (uniformWeights_pos a).le)
      (mul_nonneg hβ (hp.1 a))
  · simp only [mixture, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2,
      (uniformWeights_isProbability (α := α)).2]
    ring

theorem uniformChiSquare_mixture (p : α → ℝ) (β : ℝ) :
    uniformChiSquare (mixture β p) = β ^ 2 * uniformChiSquare p := by
  have hpoint (a : α) :
      (mixture β p a - uniformWeights α a) ^ 2 =
        β ^ 2 * (p a - uniformWeights α a) ^ 2 := by
    unfold mixture
    ring
  simp only [uniformChiSquare, hpoint, ← Finset.mul_sum]
  ring

theorem totalVariation_le_half_sqrt (p : α → ℝ) :
    totalVariation p (uniformWeights α) ≤ Real.sqrt (uniformChiSquare p) / 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun _ => (1 : ℝ)) (fun a => |p a - uniformWeights α a|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, sq_abs] at hcs
  have hs := Real.le_sqrt_of_sq_le hcs
  exact div_le_div_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2)

theorem uniformChiSquare_independent [Nonempty α] (p : α → ℝ)
    (hp : IsProbability p) (k : ℕ) :
    uniformChiSquare (independentWeights p k) = (1 + uniformChiSquare p) ^ k - 1 := by
  rw [uniformChiSquare_eq_secondMoment _ (independentWeights_isProbability p hp k),
    uniformChiSquare_eq_secondMoment p hp]
  have hsecond : (∑ x : Fin k → α, independentWeights p k x ^ 2) =
      (∑ a, p a ^ 2) ^ k := by
    simp only [independentWeights, ← Finset.prod_pow]
    exact (Fintype.sum_pow (fun a => p a ^ 2) k).symm
  rw [hsecond]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [← mul_pow]
  exact congrArg (fun t : ℝ => t ^ k - 1) (by ring)

/-- A finite bound sufficient for the cube asymptotic, without introducing a
limit theorem or choosing the alphabet after the repetition count. -/
theorem pow_mul_one_sub_le_one (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k * (1 - k * x) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 ≤ (1 + x) ^ k := pow_nonneg (by linarith) _
    have herr : 0 ≤ (1 + x) ^ k * ((k : ℝ) + 1) * x ^ 2 :=
      mul_nonneg (mul_nonneg hp (by positivity)) (sq_nonneg x)
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem pow_sub_one_le_fraction (x : ℝ) (hx : 0 ≤ x) (k : ℕ)
    (hk : (k : ℝ) * x < 1) :
    (1 + x) ^ k - 1 ≤ (k : ℝ) * x / (1 - (k : ℝ) * x) := by
  apply (le_div_iff₀ (sub_pos.mpr hk)).2
  have h := pow_mul_one_sub_le_one x hx k
  nlinarith

theorem pow_sub_one_le_twice (x : ℝ) (hx : 0 ≤ x) (k : ℕ)
    (hk : (k : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ k - 1 ≤ 2 * (k : ℝ) * x := by
  have hk' : (k : ℝ) * x < 1 := by linarith
  refine (pow_sub_one_le_fraction x hx k hk').trans ?_
  apply (div_le_iff₀ (sub_pos.mpr hk')).2
  have hn : 0 ≤ (k : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  nlinarith

section Singleton

variable (V : Type*) [Fintype V] [Zero V] [DecidableEq V]

theorem lineCount_sum : ∑ z : V × V, lineCount V z = 3 * Fintype.card V := by
  have h₁ : (∑ z : V × V, if z.2 = 0 then (1 : ℝ) else 0) = Fintype.card V := by
    rw [Fintype.sum_prod_type]
    simp
  have h₂ : (∑ z : V × V, if z.1 = 0 then (1 : ℝ) else 0) = Fintype.card V := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp
  have h₃ : (∑ z : V × V, if z.1 = z.2 then (1 : ℝ) else 0) = Fintype.card V := by
    rw [Fintype.sum_prod_type]
    simp
  simp only [lineCount, Finset.sum_add_distrib, h₁, h₂, h₃]
  ring

omit [Fintype V] in
theorem lineCount_sq (z : V × V) :
    lineCount V z ^ 2 = lineCount V z + (if z.1 = 0 ∧ z.2 = 0 then 6 else 0) := by
  by_cases hx : z.1 = 0 <;> by_cases hy : z.2 = 0 <;>
    by_cases hxy : z.1 = z.2 <;> simp_all [lineCount]
  norm_num

theorem lineCount_sq_sum :
    ∑ z : V × V, lineCount V z ^ 2 = 3 * Fintype.card V + 6 := by
  simp only [lineCount_sq, Finset.sum_add_distrib, lineCount_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (0 : V)]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem singletonPairWeights_isProbability : IsProbability (singletonPairWeights V) := by
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  constructor
  · intro z
    unfold singletonPairWeights lineCount
    positivity
  · simp only [singletonPairWeights, div_eq_mul_inv, ← Finset.sum_mul, lineCount_sum]
    exact mul_inv_cancel₀ (ne_of_gt (mul_pos (by norm_num) hn))

theorem singletonPairWeights_secondMoment :
    ∑ z : V × V, singletonPairWeights V z ^ 2 =
      (3 * Fintype.card V + 6) / (3 * Fintype.card V) ^ 2 := by
  simp only [singletonPairWeights, div_pow]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, lineCount_sq_sum]

theorem singletonPairWeights_chiSquare :
    uniformChiSquare (singletonPairWeights V) = ((Fintype.card V : ℝ) - 1) / 3 := by
  rw [uniformChiSquare_eq_secondMoment _ (singletonPairWeights_isProbability V),
    singletonPairWeights_secondMoment]
  simp only [Fintype.card_prod, Nat.cast_mul]
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hn]
  ring

/-- Exact finite divergence of the padded slope law. -/
theorem paddedSlope_chiSquare (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (k : ℕ) :
    uniformChiSquare (independentWeights (mixture β (singletonPairWeights V)) k) =
      (1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1 := by
  rw [uniformChiSquare_independent _
    (mixture_isProbability _ (singletonPairWeights_isProbability V) hβ hβ'),
    uniformChiSquare_mixture, singletonPairWeights_chiSquare]
  exact congrArg (fun t : ℝ => (1 + t) ^ k - 1) (by ring)

theorem paddedSlope_totalVariation (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (k : ℕ) :
    totalVariation (independentWeights (mixture β (singletonPairWeights V)) k)
      (uniformWeights (Fin k → V × V)) ≤
        Real.sqrt ((1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1) / 2 := by
  simpa only [paddedSlope_chiSquare V β hβ hβ' k] using
    totalVariation_le_half_sqrt (independentWeights (mixture β (singletonPairWeights V)) k)

theorem paddedSlope_totalVariation_small (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (k : ℕ)
    (hk : (k : ℝ) * (β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ≤ 1 / 2) :
    totalVariation (independentWeights (mixture β (singletonPairWeights V)) k)
      (uniformWeights (Fin k → V × V)) ≤
        Real.sqrt (2 * (k : ℝ) * (β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3)) / 2 := by
  have hn : (1 : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card V))
  refine (paddedSlope_totalVariation V β hβ hβ' k).trans ?_
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Real.sqrt_le_sqrt
  exact pow_sub_one_le_twice _ (by positivity) _ hk

theorem cubeSlope_totalVariation (m : ℕ) (hm : 0 < m)
    (hsize : 2 * ((Fintype.card V : ℝ) - 1) / 3 ≤ m) :
    totalVariation
      (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
      (uniformWeights (Fin (m ^ 3) → V × V)) ≤
        Real.sqrt (2 * ((Fintype.card V : ℝ) - 1) / (3 * m)) / 2 := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hbeta : (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hmpos)).2
    nlinarith
  have hproduct : ((m ^ 3 : ℕ) : ℝ) *
      ((1 / (m : ℝ) ^ 2) ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) =
        ((Fintype.card V : ℝ) - 1) / (3 * m) := by
    push_cast
    field_simp [hmpos.ne']
  have hsmall : ((m ^ 3 : ℕ) : ℝ) *
      ((1 / (m : ℝ) ^ 2) ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ≤ 1 / 2 := by
    rw [hproduct]
    apply (div_le_iff₀ (mul_pos (by norm_num) hmpos)).2
    linarith
  have h := paddedSlope_totalVariation_small V (1 / (m : ℝ) ^ 2)
    (by positivity) hbeta (m ^ 3) hsmall
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  calc
    2 * ((Fintype.card V : ℝ) - 1) / (3 * m) =
        2 * (((Fintype.card V : ℝ) - 1) / (3 * m)) := by ring
    _ = _ := by rw [← hproduct]; ring

/-- Arbitrarily many expected singleton coordinates coexist with arbitrarily
small variation error: taking `k=m³` and `beta=m⁻²` leaves `k*beta=m`.
The bound involves only the fixed alphabet and requested error. -/
theorem exists_cubeSlope_totalVariation_le (η : ℝ) (hη : 0 < η) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < m ∧
      totalVariation
        (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
        (uniformWeights (Fin (m ^ 3) → V × V)) ≤ η := by
  obtain ⟨m, hm⟩ := exists_nat_ge
    (max (max (1 : ℝ) N)
      (max (2 * ((Fintype.card V : ℝ) - 1) / 3)
        (((Fintype.card V : ℝ) - 1) / (6 * η ^ 2))))
  have hlow : max (1 : ℝ) N ≤ m := (le_max_left _ _).trans hm
  have hmone : (1 : ℝ) ≤ m := (le_max_left _ _).trans hlow
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by norm_num) hmone
  have hN : (N : ℝ) ≤ m := (le_max_right _ _).trans hlow
  have hhigh : max (2 * ((Fintype.card V : ℝ) - 1) / 3)
      (((Fintype.card V : ℝ) - 1) / (6 * η ^ 2)) ≤ m :=
    (le_max_right _ _).trans hm
  have hsize := (le_max_left _ _).trans hhigh
  have hrate := (le_max_right _ _).trans hhigh
  have hrate' : (Fintype.card V : ℝ) - 1 ≤ (m : ℝ) * (6 * η ^ 2) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * η ^ 2)).mp hrate
  refine ⟨m, by exact_mod_cast hN, Nat.cast_pos.mp hmpos, ?_⟩
  refine (cubeSlope_totalVariation V m (Nat.cast_pos.mp hmpos) hsize).trans ?_
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  apply (Real.sqrt_le_left (by positivity : 0 ≤ η * 2)).2
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * m)).2
  nlinarith

end Singleton

end
end UniqueGamesTheorem.Decoder.SparseLaw

end

section

namespace UniqueGamesTheorem.Decoder.ConstantSelection

open UniqueGamesTheorem.Foundations.Information
open SparseLaw

noncomputable section

theorem visibleMass_pos {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r : ℕ) : 0 < visibleMass α g₀ ell r := by
  unfold visibleMass
  positivity

theorem conditionalMass_pos {α : ℝ} (hα : 0 < α) (ell r : ℕ) :
    0 < conditionalMass α ell r := by
  unfold conditionalMass
  positivity

theorem decodingMass_pos {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r : ℕ) : 0 < decodingMass α g₀ ell r :=
  mul_pos (visibleMass_pos hα hg₀ ell r) (conditionalMass_pos hα ell r)

theorem variationBudget_pos {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r : ℕ) : 0 < variationBudget α g₀ ell r := by
  exact div_pos (visibleMass_pos hα hg₀ ell r) (by positivity)

/-- Exponential clean-mask decay persists after increasing the cube root. -/
theorem cube_exponential_antitone {m n : ℕ} (hmn : m ≤ n)
    {N : ℝ} (hN : 0 < N) :
    Real.exp (-(n : ℝ) / (3600 * N)) ≤
      Real.exp (-(m : ℝ) / (3600 * N)) := by
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact neg_le_neg (by exact_mod_cast hmn)

/-- One tuple length meets the sparse-law and repetition requirements, while
exceeding any independent inverse/erasure dimension threshold. -/
theorem exists_simultaneous_cube (V : Type*) [Fintype V] [Zero V] [DecidableEq V]
    {N ε γ : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hγ : 0 < γ) (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ 0 < m ∧
      totalVariation
        (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
        (uniformWeights (Fin (m ^ 3) → V × V)) ≤ ε ∧
      (1 - ((1 / (m : ℝ) ^ 2) / N) / 3600) ^ (m ^ 3) < γ := by
  obtain ⟨m₀, hm₀, hexp⟩ := Clean.exists_cube_exponential_lt
    (show 0 < N by linarith) hγ
  obtain ⟨m, hlarge, hm, htv⟩ := exists_cubeSlope_totalVariation_le V ε hε
    (max lower m₀)
  have hbase : m₀ ≤ m := (le_max_right _ _).trans hlarge
  refine ⟨m, (le_max_left _ _).trans hlarge, hm, htv, ?_⟩
  have hdecay := (Clean.cube_mask_rate_le_exp (Nat.succ_le_iff.mpr hm) hN).trans
    (cube_exponential_antitone hbase (by linarith : 0 < N))
  have hbeta : (1 / (m : ℝ)) ^ 2 = 1 / (m : ℝ) ^ 2 := by ring
  rw [hbeta] at hdecay
  exact hdecay.trans_lt hexp

/-- All scalar requirements for the final decoding contradiction can be met
after the fixed alphabet and inverse parameters have been chosen. -/
theorem exists_matrix_cube (V : Type*) [Fintype V] [Zero V] [DecidableEq V]
    {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r dimW lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ 0 < m ∧
      totalVariation
        (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
        (uniformWeights (Fin (m ^ 3) → V × V)) ≤ variationBudget α g₀ ell r ∧
      (1 - ((1 / (m : ℝ) ^ 2) / (2 : ℝ) ^ (dimW + r)) / 3600) ^ (m ^ 3) <
        decodingMass α g₀ ell r := by
  exact exists_simultaneous_cube V (one_le_pow₀ (by norm_num))
    (variationBudget_pos hα hg₀ ell r) (decodingMass_pos hα hg₀ ell r) lower

end
end UniqueGamesTheorem.Decoder.ConstantSelection

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_QuotientLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Gadget.Quotient

variable {𝕜 P B : Type*} [Ring 𝕜]
variable [AddCommGroup P] [Module 𝕜 P] [AddCommGroup B] [Module 𝕜 B]

/-- Noise pushforward preserves the change event pointwise, before averaging. -/
theorem change_iff (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (u a : P) :
    (output R lam C hC (projection R lam u + projection R lam a) ≠
      output R lam C hC (projection R lam u)) ↔ C (u + a) ≠ C u := by
  rw [← map_add, output_projection, output_projection]

theorem fiberMap_bijective (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (a : P) :
    Function.Bijective (fiberMap R lam a) := by
  constructor
  · intro h k he
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val he)
  · intro u
    have hm : u.val - a ∈ shiftKernel R lam :=
      (Submodule.Quotient.eq _).mp u.property
    refine ⟨⟨u.val - a, hm⟩, Subtype.ext ?_⟩
    change a + (u.val - a) = u.val
    rw [add_comm, sub_add_cancel]

/-- Every fiber has the same cardinality, justifying uniform-input pushforward. -/
theorem fiber_card (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (x : Space R lam) :
    Nat.card {u : P // projection R lam u = x} = Nat.card (shiftKernel R lam) := by
  obtain ⟨a, rfl⟩ := projection_surjective R lam x
  exact (Nat.card_congr (Equiv.ofBijective _ (fiberMap_bijective R lam a))).symm

end UniqueGamesTheorem.Gadget.Quotient

/-!
# Conditional uniformity by translation averaging

For uniform finite input, an equivariant output is uniform even conditional on
any shift-invariant observable.  The observable need not have a finite range.
The proof averages translations directly and therefore never divides by a
conditioning probability.  In particular it applies to the output difference
at a fixed perturbation, and to an independent finite noise choice.
-/

namespace UniqueGamesTheorem.Gadget

section

universe u v

attribute [instance] Stage.inputAdd Stage.inputModule Stage.shiftAdd Stage.shiftModule
  Stage.inputFinite Stage.shiftFinite Stage.noiseFinite Stage.noiseNonempty

end

/-!
# Actual lifts and their descendant restrictions

Every descendant lift is constructed by a linear section of the child image.
Its detection on the child noise implies detection by the parent family on
the actual embedded noise. The common parent family is chosen before the
child index; only the image section is chosen after that index is known.
-/

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B]

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

/-- Pointwise containment of child detection in parent detection. Repeating
this implication along a path preserves the original family at the root. -/
theorem descendant_detection_implies_parent
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S)
    {S' : Submodule k (B →ₗ[k] k)} (L' : Lift s S')
    (sectionMap : S' →ₗ[k] S) (i : I)
    (hfamily : ∀ z p, L'.family z p = L.family (sectionMap z) (Pi.single i p))
    (n : s.Noise) (hdetect : ∃ z, L'.family z (s.noise n) ≠ 0) :
    ∃ z, L.family z ((Stage.next J hJ Q s).noise (i, n)) ≠ 0 := by
  obtain ⟨z, hz⟩ := hdetect
  refine ⟨sectionMap z, ?_⟩
  simpa only [hfamily, Stage.next] using hz

end UniqueGamesTheorem.Gadget

namespace UniqueGamesTheorem.Gadget.Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

omit [Finite B] [FiniteDimensional k B] in
theorem childLift_spec (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I)
    (z : childDomain J hJ Q s S L i) (p : s.Input) :
    (childLift J hJ Q s S L i).family z p =
      L.family (childSection J hJ Q s S L i z) (Pi.single i p) :=
  (Classical.choose_spec (Classical.choose_spec (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i))).2 z p

omit [Finite B] [FiniteDimensional k B] in
theorem child_detection (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) (n : s.Noise)
    (hdetect : ∃ z, (childLift J hJ Q s S L i).family z (s.noise n) ≠ 0) :
    ∃ z, L.family z ((Stage.next J hJ Q s).noise (i, n)) ≠ 0 :=
  descendant_detection_implies_parent J hJ Q s S L _ _ i
    (childLift_spec J hJ Q s S L i) n hdetect

omit [Finite B] in
theorem child_rank_le (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    Module.finrank k (childDomain J hJ Q s S L i) ≤ Module.finrank k S :=
  LinearMap.finrank_range_le _

theorem leafRank_le (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q n) S) (t : (Stage.iterate J hJ Q n).Noise) :
    leafRank J hJ Q n S L t ≤ Module.finrank k S := by
  induction n generalizing S with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih _ _ _).trans (child_rank_le J hJ Q _ S L t.1)

end UniqueGamesTheorem.Gadget.Descent

/-!
# Harmonic potential for the actual recursively selected lifts

This is the adaptive induction on the concrete descendant lift construction.
The first outgoing step may begin at a bad subspace; every later orientation
is fresh. Accordingly the bound has one initial bad-space penalty, which
vanishes for the fixed generic top subspace.
-/

namespace UniqueGamesTheorem.Gadget.DescentProbability

open Harmonic Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

omit [FiniteDimensional k B] in
theorem terminalPotential_succ (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    terminalPotential J hJ Q (n + 1) S L =
      average (fun i => terminalPotential J hJ Q n
        (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
        (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
  unfold terminalPotential average
  change Finset.univ.expect (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    UniqueGamesTheorem.Gadget.Harmonic.harmonic (leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2)) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]

/-- The only geometric inputs are the outgoing harmonic loss estimate for
every lift and the fresh-orientation bound for every child image. The lift may
depend on every previous orientation; the proof never declares it independent. -/
theorem expected_terminal_loss
    (bad : Submodule k (B →ₗ[k] k) → Prop) [DecidablePred bad]
    (r₀ : ℕ) (C θ ε : ℚ) (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hsmall : C * ε ≤ 1)
    (hstep : ∀ (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
      (L : Lift (Stage.next J hJ Q s) S), Module.finrank k S ≤ r₀ →
      average (fun i => UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank k S) -
        UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank k (childDomain J hJ Q s S L i))) ≤
          3 * θ + C * θ * if bad S then 1 else 0)
    (hfresh : ∀ (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
      (L : Lift (Stage.next J hJ Q s) S), Module.finrank k S ≤ r₀ →
      probability (fun i => bad (childDomain J hJ Q s S L i)) ≤ ε)
    (n : ℕ) (S : Submodule k (B →ₗ[k] k)) (L : Lift (Stage.iterate J hJ Q n) S)
    (hcap : Module.finrank k S ≤ r₀) :
    UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank k S) - terminalPotential J hJ Q n S L ≤
      4 * n * θ + C * θ * if bad S then 1 else 0 := by
  induction n generalizing S with
  | zero =>
    simp only [terminalPotential_zero, sub_self, Nat.cast_zero, mul_zero, zero_mul,
      zero_add]
    split <;> simp_all [mul_nonneg]
  | succ n ih =>
    let s := Stage.iterate J hJ Q n
    let Sc := childDomain J hJ Q s S L
    let Lc := childLift J hJ Q s S L
    have hchild : average (fun i => UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank k (Sc i)) -
        terminalPotential J hJ Q n (Sc i) (Lc i)) ≤
        4 * n * θ + C * θ * probability (fun i => bad (Sc i)) := by
      calc
        _ ≤ average (fun i => 4 * n * θ + C * θ * if bad (Sc i) then 1 else 0) := by
          apply average_mono
          intro i
          exact ih (Sc i) (Lc i) ((child_rank_le J hJ Q s S L i).trans hcap)
        _ = _ := by rw [average_add, average_const, average_mul_left]; rfl
    have hdrop := hstep s S L hcap
    have hbad := hfresh s S L hcap
    have hbad' := mul_le_mul_of_nonneg_left hbad (mul_nonneg hC hθ)
    have hsmall' := mul_le_mul_of_nonneg_right hsmall hθ
    rw [terminalPotential_succ]
    rw [average_sub] at hchild
    rw [average_sub, average_const] at hdrop
    change UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank k S) -
      average (fun i => terminalPotential J hJ Q n (Sc i) (Lc i)) ≤ _
    push_cast
    nlinarith

end UniqueGamesTheorem.Gadget.DescentProbability

namespace UniqueGamesTheorem.Gadget.LeafDetection

open Harmonic Descent DescentProbability

universe v

variable {B I X : Type v}
variable [AddCommGroup B] [Module (ZMod 2) B] [Finite B] [FiniteDimensional (ZMod 2) B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module (ZMod 2) X]

variable (J : I → B →ₗ[ZMod 2] X × B)
variable (hJ : Function.Surjective (aggregate J)) (Q : X → B)

omit [FiniteDimensional (ZMod 2) B] in
theorem detectionProbability_nonneg (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) :
    0 ≤ detectionProbability J hJ Q n S L := by
  classical
  exact probability_nonneg _

omit [FiniteDimensional (ZMod 2) B] in
/-- Restricting the logical domain can only remove detecting characters. -/
theorem detectionProbability_restrict_le (n : ℕ)
    (S T : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2)) (hST : S ≤ T)
    (L : Lift (Stage.iterate J hJ Q n) T) :
    detectionProbability J hJ Q n S (L.restrict hST) ≤
      detectionProbability J hJ Q n T L := by
  classical
  apply probability_mono
  rintro t ⟨z, hz⟩
  exact ⟨Submodule.inclusion hST z, hz⟩

omit [FiniteDimensional (ZMod 2) B] in
theorem detectionProbability_zero_of_rank_pos
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q 0) S) (hrank : 0 < Module.finrank (ZMod 2) S) :
    (1 / 2 : ℚ) ≤ detectionProbability J hJ Q 0 S L := by
  classical
  let : Fintype B := Fintype.ofFinite B
  let : Nontrivial S := Module.nontrivial_of_finrank_pos hrank
  obtain ⟨z, hz⟩ := exists_ne (0 : S)
  have hzval : z.val ≠ 0 := by
    intro he
    exact hz (Subtype.ext he)
  have hex : ∃ b : B, z.val b ≠ 0 := by
    by_contra h
    apply hzval
    ext b
    by_contra hb
    exact h ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hex
  have hagree : L.family z b = z.val b := L.agrees z b
  have hχ : L.family z b ≠ 0 := by rwa [hagree]
  change (1 / 2 : ℚ) ≤ probability (fun b : B => ∃ z : S, L.family z b ≠ 0)
  exact binary_family_detection_ge_half _ (L.family z).toAddMonoidHom b hχ
    (fun b hb => ⟨z, hb⟩)

omit [FiniteDimensional (ZMod 2) B] in
theorem survivalProbability_succ (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    survivalProbability J hJ Q (n + 1) S L =
      average (fun i => survivalProbability J hJ Q n
        (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
        (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
  unfold survivalProbability
  change probability (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    0 < leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2) = _
  exact probability_product _

omit [FiniteDimensional (ZMod 2) B] in
theorem average_child_detection_le (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    average (fun i => detectionProbability J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) ≤
        detectionProbability J hJ Q (n + 1) S L := by
  classical
  unfold detectionProbability
  change _ ≤ probability (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    ∃ z : S, L.family z ((Stage.iterate J hJ Q (n + 1)).noise t) ≠ 0)
  rw [probability_product]
  apply average_mono
  intro i
  apply probability_mono
  intro t hdetect
  exact child_detection J hJ Q (Stage.iterate J hJ Q n) S L i t hdetect

omit [FiniteDimensional (ZMod 2) B] in
/-- Detection by the root lift is at least one half the actual terminal-rank
survival probability, on precisely the recursively generated noise sample. -/
theorem half_survival_le_detection (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) :
    (1 / 2 : ℚ) * survivalProbability J hJ Q n S L ≤
      detectionProbability J hJ Q n S L := by
  induction n generalizing S with
  | zero =>
    rw [survivalProbability_zero]
    split_ifs with hrank
    · simpa only [mul_one] using detectionProbability_zero_of_rank_pos J hJ Q S L hrank
    · simpa only [mul_zero] using detectionProbability_nonneg J hJ Q 0 S L
  | succ n ih =>
    rw [survivalProbability_succ, ← average_mul_left]
    calc
      _ ≤ average (fun i => detectionProbability J hJ Q n
          (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
          (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
        apply average_mono
        intro i
        exact ih _ _
      _ ≤ detectionProbability J hJ Q (n + 1) S L :=
        average_child_detection_le J hJ Q n S L

/-- Actual quarter detection follows from retaining half the initial
UniqueGamesTheorem.Gadget.Harmonic.harmonic potential; all leaf-to-root event containments are already proved. -/
theorem quarter_detection_of_terminal_potential (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S)
    (hrank : 0 < Module.finrank (ZMod 2) S)
    (hpotential : UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q n S L) :
    (1 / 4 : ℚ) ≤ detectionProbability J hJ Q n S L := by
  have hsurv : (1 / 2 : ℚ) ≤ survivalProbability J hJ Q n S L :=
    survival_probability_ge_half_of_potential (leafRank J hJ Q n S L)
      (Module.finrank (ZMod 2) S) hrank (leafRank_le J hJ Q n S L) hpotential
  have hdet := half_survival_le_detection J hJ Q n S L
  linarith

/-- The fixed generic top subspace may be chosen inside a full logical
family; the resulting quarter bound still concerns the original lift. -/
theorem quarter_detection_of_restricted_terminal_potential (n : ℕ)
    (S T : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2)) (hST : S ≤ T)
    (L : Lift (Stage.iterate J hJ Q n) T)
    (hrank : 0 < Module.finrank (ZMod 2) S)
    (hpotential : UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q n S (L.restrict hST)) :
    (1 / 4 : ℚ) ≤ detectionProbability J hJ Q n T L :=
  (quarter_detection_of_terminal_potential J hJ Q n S (L.restrict hST)
    hrank hpotential).trans (detectionProbability_restrict_le J hJ Q n S T hST L)

end UniqueGamesTheorem.Gadget.LeafDetection

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_NonlinearRecurrenceLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Gadget.NonlinearRecurrence

open scoped BigOperators

variable {k I P R X B : Type*} [CommRing k]
variable [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X] [Fintype X]
variable [AddCommGroup B] [Module k B] [Fintype B] [DecidableEq B]

omit [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] in
theorem compLeft_surjective (lam : R →ₗ[k] B) (hlam : Function.Surjective lam) :
    Function.Surjective (lam.compLeft I) := by
  intro b
  choose h hh using fun i => hlam (b i)
  exact ⟨h, funext hh⟩

omit [Fintype X] [Fintype B] [DecidableEq B] in
theorem aggregate_single (J : I → B →ₗ[k] X × B) (i : I) (b : B) :
    aggregate J (Pi.single i b) = J i b := by
  classical
  change (∑ j, J j ((Pi.single i b : I → B) j)) = J i b
  simp only [LinearMap.apply_single]
  simp

omit [Fintype I] [Fintype P] [Fintype B] [DecidableEq B] in
theorem child_outputs_perturb (C : P → B) (u : I → P) (i : I) (a : P) :
    (fun j => C ((u + (Pi.single i a : I → P)) j)) =
      (fun j => C (u j)) + (Pi.single i (C (u i + a) - C (u i)) : I → B) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Pi.add_apply, Pi.single_eq_same]
    rw [add_comm (C (u i)), sub_add_cancel]
  · simp [Pi.single_eq_of_ne hj]

omit [Module k P] [Fintype P] [Fintype X] [Fintype B] [DecidableEq B] in
theorem parent_output_perturb (J : I → B →ₗ[k] X × B) (C : P → B)
    (F : X × B → B) (u : I → P) (i : I) (a : P) :
    F (aggregate J (fun j => C ((u + (Pi.single i a : I → P)) j))) =
      F (aggregate J (fun j => C (u j)) + J i (C (u i + a) - C (u i))) := by
  rw [child_outputs_perturb, map_add, aggregate_single]

/-- The exact conditional-uniform and coordinate-marginal law for a fixed
selected index and fixed child perturbation. -/
theorem expect_change_at_index (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (F : X × B → B) (i : I) (a : P) :
    (𝔼 u : I → P,
      change F (aggregate J (fun j => C (u j))) (J i (C (u i + a) - C (u i)))) =
      𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + a) - C x)) := by
  have hCt : ∀ (u : I → P) (h : I → R),
      (fun j => C ((u + (e.compLeft I) h) j)) =
        (fun j => C (u j)) + (lam.compLeft I) h := by
    intro u h
    funext j
    exact hC (u j) (h j)
  have hDt : ∀ (u : I → P) (h : I → R),
      C ((u + (e.compLeft I) h) i + a) - C ((u + (e.compLeft I) h) i) =
        C (u i + a) - C (u i) := by
    intro u h
    change C (u i + e (h i) + a) - C (u i + e (h i)) = _
    have he : u i + e (h i) + a = (u i + a) + e (h i) := by
      simp only [add_assoc, add_comm (e (h i)) a]
    rw [he, hC, hC, add_sub_add_right_eq_sub]
  calc
    _ = 𝔼 u : I → P, 𝔼 b : I → B,
        change F (aggregate J b) (J i (C (u i + a) - C (u i))) :=
      EmbeddedConditional.expect_uniform_output_embedded
        (e.compLeft I) (lam.compLeft I) (compLeft_surjective lam hlam)
        (fun u j => C (u j)) hCt (fun u => C (u i + a) - C (u i)) hDt
        (fun b d => change F (aggregate J b) (J i d))
    _ = 𝔼 u : I → P, 𝔼 z : X × B,
        change F z (J i (C (u i + a) - C (u i))) := by
      apply Finset.expect_congr rfl
      intro u _
      exact EmbeddedConditional.expect_linear_surjective (aggregate J) hJ
        (fun z => change F z (J i (C (u i + a) - C (u i))))
    _ = 𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + a) - C x)) := by
      exact EmbeddedConditional.expect_linear_surjective
        (LinearMap.proj i : (I → P) →ₗ[k] P)
        (fun x => ⟨fun _ => x, rfl⟩)
        (fun x : P => 𝔼 z : X × B, change F z (J i (C (x + a) - C x)))

omit [DecidableEq I] in
/-- The averaged block kernel includes zero differences by multiplication with
their nonzero indicator. -/
theorem kernel_all (J : I → B →ₗ[k] X × B) (F : X × B → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 → (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ)
    (d : B) :
    (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ * (if d ≠ 0 then 1 else 0) := by
  classical
  by_cases hd : d = 0
  · simp [hd]
  · simp only [ite_eq_left hd, mul_one]
    exact hk d hd

/-- One exact nonlinear recurrence on the actual product input and the actual
single-coordinate noise. The only remaining block obligation is `hk`. -/
theorem parent_change_recurrence {N : Type*} [Fintype N]
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (C : P → B) (hC : ∀ u h, C (u + e h) = C u + lam h)
    (F : X × B → B) (noise : N → P) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 → (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ) :
    (𝔼 i, 𝔼 n : N, 𝔼 u : I → P,
      if F (aggregate J (fun j => C ((u + (Pi.single i (noise n) : I → P)) j))) ≠
        F (aggregate J (fun j => C (u j))) then (1 : ℚ) else 0) =
      ρ * (𝔼 n : N, 𝔼 x : P, if C (x + noise n) ≠ C x then (1 : ℚ) else 0) := by
  classical
  have hpoint (i : I) (n : N) :
      (𝔼 u : I → P,
        if F (aggregate J (fun j => C ((u + (Pi.single i (noise n) : I → P)) j))) ≠
          F (aggregate J (fun j => C (u j))) then (1 : ℚ) else 0) =
        𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + noise n) - C x)) := by
    simp_rw [parent_output_perturb]
    exact expect_change_at_index J hJ e lam hlam C hC F i (noise n)
  simp_rw [hpoint]
  rw [Finset.expect_comm]
  calc
    _ = 𝔼 n : N, 𝔼 x : P, 𝔼 i,
        𝔼 z : X × B, change F z (J i (C (x + noise n) - C x)) := by
      apply Finset.expect_congr rfl
      intro n _
      exact Finset.expect_comm _ _ _
    _ = 𝔼 n : N, 𝔼 x : P,
        ρ * (if C (x + noise n) ≠ C x then (1 : ℚ) else 0) := by
      apply Finset.expect_congr rfl
      intro n _
      apply Finset.expect_congr rfl
      intro x _
      simpa only [ne_eq, sub_eq_zero] using kernel_all J F ρ hk (C (x + noise n) - C x)
    _ = _ := by simp only [← Finset.mul_expect]

end UniqueGamesTheorem.Gadget.NonlinearRecurrence

end

section

namespace UniqueGamesTheorem.Gadget.StageQuotient

universe u v

variable {k : Type u} {B : Type v} [CommRing k]
variable [AddCommGroup B] [Module k B]

theorem noise_change_iff (s : Stage k B) (u : s.Input) (t : s.Noise) :
    (output s (projection s u + noise s t) ≠ output s (projection s u)) ↔
      s.output (u + s.noise t) ≠ s.output u :=
  Quotient.change_iff (shifts s) (logical s) s.output (equivariant s) u (s.noise t)

end UniqueGamesTheorem.Gadget.StageQuotient

end

section

noncomputable section

namespace UniqueGamesTheorem.Gadget.EnlargementConstruction

open scoped BigOperators Classical
open Enlargement

theorem probability_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (p : Ξ → Prop) :
    probability (fun x : Ω => p (e x)) = probability p := by
  classical
  unfold probability
  rw [Nat.card_congr (Equiv.subtypeEquivOfSubtype (p := p) e), Nat.card_congr e]

theorem probability_eq_sum_indicator {Ω : Type*} [Fintype Ω]
    (p : Ω → Prop) :
    probability p =
      (∑ x : Ω, if p x then (1 : ℚ) else 0) / (Fintype.card Ω : ℚ) := by
  classical
  simp only [probability, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- Uniform probability on a product is the average of the second-coordinate
probabilities. No nonemptiness hypotheses are needed for this identity. -/
theorem probability_prod_average {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p : Ω → Ξ → Prop) :
    probability (fun z : Ω × Ξ => p z.1 z.2) =
      (∑ x : Ω, probability (p x)) / (Fintype.card Ω : ℚ) := by
  classical
  simp_rw [probability_eq_sum_indicator]
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Finset.sum_div, div_div]
  congr 1
  exact mul_comm _ _

/-- The same product identity, averaging in the other order. -/
theorem probability_prod_average_right {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p : Ω → Ξ → Prop) :
    probability (fun z : Ω × Ξ => p z.1 z.2) =
      (∑ y : Ξ, probability (fun x : Ω => p x y)) /
        (Fintype.card Ξ : ℚ) := by
  classical
  simp_rw [probability_eq_sum_indicator]
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type_right,
    ← Finset.sum_div, div_div]

/-- Every coordinate of a uniformly chosen function has the uniform marginal.
Pointwise transpositions biject the evaluation fibers. -/
theorem probability_coordinate {I X : Type*} [Fintype I] [Fintype X]
    (i : I) (p : X → Prop) :
    probability (fun g : I → X => p (g i)) = probability p := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
      let : IsEmpty X := hX
      let : IsEmpty (I → X) := ⟨fun g => isEmptyElim (g i)⟩
      simp [probability]
  | inr hX =>
      let : Nonempty X := hX
      let : Nonempty (I → X) := ⟨fun _ => Classical.choice hX⟩
      apply probability_preimage_of_fibers (fun g : I → X => g i)
      intro x y
      let e : (I → X) ≃ (I → X) :=
        Equiv.piCongrRight (fun _ : I => Equiv.swap x y)
      let ee : {g : I → X // g i = x} ≃
          {g : I → X // g i = y} :=
        e.subtypeEquiv (fun g => by
          change g i = x ↔ Equiv.swap x y (g i) = y
          constructor
          · intro h
            rw [h, Equiv.swap_apply_left]
          · intro h
            apply (Equiv.swap x y).injective
            exact h.trans (Equiv.swap_apply_left x y).symm)
      exact Nat.card_congr ee

/-- Coordinate projection preserves the joint uniform law with an independent
finite noise sample. -/
theorem probability_coordinate_prod {I X N : Type*}
    [Fintype I] [Fintype X] [Fintype N] (i : I) (p : X → N → Prop) :
    probability (fun z : (I → X) × N => p (z.1 i) z.2) =
      probability (fun z : X × N => p z.1 z.2) := by
  rw [probability_prod_average_right (fun (g : I → X) n => p (g i) n),
    probability_prod_average_right p]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact probability_coordinate i (fun x => p x n)

/-- Grouping the same three uniform choices in another order. -/
theorem probability_prod_reorder {Ω I N : Type*}
    [Fintype Ω] [Fintype I] [Fintype N] (p : Ω → I → N → Prop) :
    probability (fun z : Ω × (I × N) => p z.1 z.2.1 z.2.2) =
      probability (fun z : I × (Ω × N) => p z.2.1 z.1 z.2.2) := by
  let e : (Ω × (I × N)) ≃ (I × (Ω × N)) :=
    { toFun := fun z => (z.2.1, z.1, z.2.2)
      invFun := fun z => (z.2.1, z.1, z.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact probability_equiv e (fun z => p z.2.1 z.1 z.2.2)

/-- If each conditional probability is the same, their uniform average is
that common value. -/
theorem probability_prod_eq_of_const {Ω Ξ : Type*}
    [Fintype Ω] [Fintype Ξ] [Nonempty Ω]
    (p : Ω → Ξ → Prop) (q : ℚ) (h : ∀ x, probability (p x) = q) :
    probability (fun z : Ω × Ξ => p z.1 z.2) = q := by
  rw [probability_prod_average]
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ q hcard

/-- For a fixed selected injection, the enlargement's change event has exactly
the base input/noise probability. -/
theorem enlarged_single_copy_probability {F B K V N : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Fintype V] [Fintype N]
    [Fintype (LinearInjection F B K)]
    (C : V → B) (a : N → V) (L : LinearInjection F B K) :
    probability (fun z : (LinearInjection F B K → V) × N =>
      enlargedOutput C (Function.update z.1 L (z.1 L + a z.2)) ≠
        enlargedOutput C z.1) =
      probability (fun z : V × N => C (z.1 + a z.2) ≠ C z.1) := by
  calc
    _ = probability (fun z : (LinearInjection F B K → V) × N =>
        C (z.1 L + a z.2) ≠ C (z.1 L)) := by
      congr 1
      funext z
      exact propext (enlargedOutput_update_ne_iff C z.1 L (z.1 L + a z.2))
    _ = _ := probability_coordinate_prod L (fun x n => C (x + a n) ≠ C x)

/-- The same equality after selecting the injection uniformly as part of the
noise sample. Its sample space is exactly product-input × (copy × base-noise). -/
theorem enlarged_random_copy_probability {F B K V N : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Fintype V] [Fintype N]
    [Fintype (LinearInjection F B K)] [Nonempty (LinearInjection F B K)]
    (C : V → B) (a : N → V) :
    probability (fun z : (LinearInjection F B K → V) ×
        (LinearInjection F B K × N) =>
      enlargedOutput C
        (Function.update z.1 z.2.1 (z.1 z.2.1 + a z.2.2)) ≠
          enlargedOutput C z.1) =
      probability (fun z : V × N => C (z.1 + a z.2) ≠ C z.1) := by
  rw [probability_prod_reorder (fun x L n =>
    enlargedOutput C (Function.update x L (x L + a n)) ≠ enlargedOutput C x)]
  apply probability_prod_eq_of_const (fun L (z : (LinearInjection F B K → V) × N) =>
    enlargedOutput C (Function.update z.1 L (z.1 L + a z.2)) ≠ enlargedOutput C z.1)
  intro L
  exact enlarged_single_copy_probability C a L

universe u

variable {B K V N : Type u}
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
variable [FiniteDimensional (ZMod 2) B]
variable [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
variable [FiniteDimensional (ZMod 2) K]
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype N] [Nonempty N]

attribute [local instance] OAI.UniqueGamesTheorem.Gadget.EnlargementConstruction.enlargementCopiesFintype
omit [FiniteDimensional (ZMod 2) B] [Fintype K]
  [FiniteDimensional (ZMod 2) K] [Module (ZMod 2) V] [Fintype V] in
theorem add_single_eq_update (x : Copies B K → V) (L : Copies B K) (a : V) :
    x + Pi.single L a = Function.update x L (x L + a) := by
  funext J
  by_cases h : J = L
  · subst J
    simp
  · simp [h]

/-- The quotient and injection preserve each individual nonlinear change
event exactly, before taking any finite averages. -/
theorem change_iff (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) (x : Copies B K → V) (L : Copies B K) (n : N) :
    let s := productStage i hi C hC noise hdim b₀ hb₀
    StageQuotient.output s (StageQuotient.projection s x + StageQuotient.noise s (L, n)) ≠
        StageQuotient.output s (StageQuotient.projection s x) ↔
      C (x L + noise n) ≠ C (x L) := by
  dsimp only
  refine (StageQuotient.noise_change_iff
    (productStage i hi C hC noise hdim b₀ hb₀) x (L, n)).trans ?_
  change enlargedOutput C (x + Pi.single L (noise n)) ≠ enlargedOutput C x ↔ _
  rw [add_single_eq_update]
  convert enlargedOutput_update_ne_iff C x L (x L + noise n)

theorem copyObserver_shift {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (L : Copies B K) :
    (copyObserver i hi C hC noise hdim b₀ hb₀ T L).comp i =
      (T.comp (StageQuotient.shift (productStage i hi C hC noise hdim b₀ hb₀))).comp L.1 := by
  ext b
  let s := productStage i hi C hC noise hdim b₀ hb₀
  have he : s.embed (Pi.single L b) = Pi.single L (i b) := by
    funext J
    change i ((Pi.single L b : Copies B K → B) J) =
      (Pi.single L (i b) : Copies B K → V) J
    by_cases h : J = L
    · subst J
      simp
    · simp [h]
  have hl : s.logical (Pi.single L b) = L.1 b := by
    change (∑ J : Copies B K, J.1 ((Pi.single L b : Copies B K → B) J)) = L.1 b
    simp [Pi.single_apply, apply_ite]
  have hh := congrArg T (StageQuotient.shift_logical s (Pi.single L b))
  rw [he, hl] at hh
  exact hh.symm

omit [Fintype B] [FiniteDimensional (ZMod 2) B]
  [Fintype K] [FiniteDimensional (ZMod 2) K] in
theorem dual_pullback_eq_top_iff {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (A : K →ₗ[ZMod 2] E) (L : B →ₗ[ZMod 2] K) :
    (LinearMap.range A.dualMap).map L.dualMap = ⊤ ↔ Function.Injective (A.comp L) := by
  rw [← LinearMap.range_comp, LinearMap.dualMap_comp_dualMap,
    LinearMap.range_eq_top, LinearMap.dualMap_surjective_iff]

/-- Average detection over the actual injection-indexed base copies. The
restriction threshold is the rank on the final embedded logical space. -/
theorem detection_average {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (hbase : ∀ U : V →ₗ[ZMod 2] E, Function.Injective (U.comp i) →
      1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0))
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (T.comp (StageQuotient.shift
        (productStage i hi C hC noise hdim b₀ hb₀))))) :
    1 / 8 ≤
      (∑ L : Copies B K, probability (fun n : N =>
        copyObserver i hi C hC noise hdim b₀ hb₀ T L (noise n) ≠ 0)) /
          (Fintype.card (Copies B K) : ℚ) := by
  let : Nonempty (Copies B K) := linearInjection_nonempty_of_finrank_le hdim
  let A := T.comp (StageQuotient.shift (productStage i hi C hC noise hdim b₀ hb₀))
  apply (enlarged_detection (LinearMap.range A.dualMap)
    (by simpa only [LinearMap.finrank_range_dualMap_eq_finrank_range] using hr)
    (fun L => probability (fun n : N =>
      copyObserver i hi C hC noise hdim b₀ hb₀ T L (noise n) ≠ 0))
    (fun _ => by unfold probability; positivity) ?_).2
  intro L hL
  apply hbase
  rw [copyObserver_shift]
  exact (dual_pullback_eq_top_iff A L.1).1 hL

omit [Fintype K] [FiniteDimensional (ZMod 2) K] in
/-- Passing uniform input through the actual quotient preserves its law. -/
theorem probability_projection (s : Stage (ZMod 2) K)
    [Fintype s.Input] [Fintype (StageQuotient.Space s)]
    (p : StageQuotient.Space s → Prop) :
    probability (fun x : s.Input => p (StageQuotient.projection s x)) = probability p := by
  apply probability_preimage_of_fibers (StageQuotient.projection s)
  intro x y
  have h := (Quotient.fiber_card (StageQuotient.shifts s) (StageQuotient.logical s) x).trans
    (Quotient.fiber_card (StageQuotient.shifts s) (StageQuotient.logical s) y).symm
  exact h

omit [Fintype K] [FiniteDimensional (ZMod 2) K] in
theorem probability_projection_prod (s : Stage (ZMod 2) K)
    [Fintype s.Input] [Fintype (StageQuotient.Space s)]
    {A : Type*} [Fintype A] (p : StageQuotient.Space s → A → Prop) :
    probability (fun z : s.Input × A => p (StageQuotient.projection s z.1) z.2) =
      probability (fun z : StageQuotient.Space s × A => p z.1 z.2) := by
  rw [probability_prod_average_right (fun x a => p (StageQuotient.projection s x) a),
    probability_prod_average_right p]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact probability_projection s (fun x => p x a)

/-- Nonlinear change probability is exactly the base probability after both
the single-copy enlargement and quotient, on uniform quotient input. -/
theorem change_probability (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    [Fintype (StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀))] :
    let s := productStage i hi C hC noise hdim b₀ hb₀
    probability (fun z : StageQuotient.Space s × (Copies B K × N) =>
      StageQuotient.output s (z.1 + StageQuotient.noise s z.2) ≠ StageQuotient.output s z.1) =
        probability (fun z : V × N => C (z.1 + noise z.2) ≠ C z.1) := by
  dsimp only
  let : Nonempty (Copies B K) := linearInjection_nonempty_of_finrank_le hdim
  let s := productStage i hi C hC noise hdim b₀ hb₀
  let : Fintype s.Input := Fintype.ofFinite _
  have hp := probability_projection_prod s (fun q (t : Copies B K × N) =>
    StageQuotient.output s (q + StageQuotient.noise s t) ≠ StageQuotient.output s q)
  calc
    _ = probability (fun z : s.Input × (Copies B K × N) =>
        StageQuotient.output s (StageQuotient.projection s z.1 + StageQuotient.noise s z.2) ≠
          StageQuotient.output s (StageQuotient.projection s z.1)) := hp.symm
    _ = probability (fun z : (Copies B K → V) × (Copies B K × N) =>
        enlargedOutput C
          (Function.update z.1 z.2.1 (z.1 z.2.1 + noise z.2.2)) ≠ enlargedOutput C z.1) := by
      congr 1
      funext z
      apply propext
      exact (change_iff i hi C hC noise hdim b₀ hb₀ z.1 z.2.1 z.2.2).trans
        (by convert (enlargedOutput_update_ne_iff C z.1 z.2.1 (z.1 z.2.1 + noise z.2.2)).symm)
    _ = _ := by
      convert enlarged_random_copy_probability C noise
      exact inferInstanceAs (Nonempty (Copies B K))

/-- The final noise sample is the actual product sampler and meets the stated
rank-detection bound. No detection premise about the enlarged gadget is assumed. -/
theorem detection_probability {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (hbase : ∀ U : V →ₗ[ZMod 2] E, Function.Injective (U.comp i) →
      1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0))
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (T.comp (StageQuotient.shift
        (productStage i hi C hC noise hdim b₀ hb₀))))) :
    1 / 8 ≤ probability (fun t : Copies B K × N =>
      T (StageQuotient.noise (productStage i hi C hC noise hdim b₀ hb₀) t) ≠ 0) := by
  change 1 / 8 ≤ probability (fun t : Copies B K × N =>
    copyObserver i hi C hC noise hdim b₀ hb₀ T t.1 (noise t.2) ≠ 0)
  rw [probability_prod_average (fun L n =>
    copyObserver i hi C hC noise hdim b₀ hb₀ T L (noise n) ≠ 0)]
  exact detection_average i hi C hC noise hdim b₀ hb₀ hbase T hr

end UniqueGamesTheorem.Gadget.EnlargementConstruction

end

end

section

/-!
# Detection survives the logical-kernel quotient

A full family of logical characters on the quotient pulls back to a full
lift on the original stage. Its detection event is the same pointwise.
Combining this with the proved left-inverse construction gives detection of
every linear map injective on the quotient's logical subspace.
-/

namespace UniqueGamesTheorem.Gadget.QuotientDetection

open Harmonic DetectionBridge
open scoped Classical

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B]

omit [Finite B] in
theorem pullback_detection_iff (s : Stage k B)
    (ψ : Module.Dual k B →ₗ[k] Module.Dual k (StageQuotient.Space s))
    (hψ : IsFullLift (StageQuotient.shift s) ψ) (n : s.Noise) :
    (∃ z, (pullbackFullLift s ψ hψ).family z (s.noise n) ≠ 0) ↔
      ∃ z, ψ z (StageQuotient.noise s n) ≠ 0 := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.val, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨⟨z, Submodule.mem_top⟩, hz⟩

omit [Finite B] in
/-- Any checked full-lift probability bound before quotienting applies to
every full family on the actual quotient, on the same noise sampler. -/
theorem full_detection_after_quotient (s : Stage k B) [Fintype s.Noise] (q : ℚ)
    (hfull : ∀ L : Lift s (⊤ : Submodule k (Module.Dual k B)),
      q ≤ probability (fun n => ∃ z, L.family z (s.noise n) ≠ 0))
    (ψ : Module.Dual k B →ₗ[k] Module.Dual k (StageQuotient.Space s))
    (hψ : IsFullLift (StageQuotient.shift s) ψ) :
    q ≤ characterDetection (StageQuotient.noise s) ψ := by
  classical
  have h := hfull (pullbackFullLift s ψ hψ)
  simpa only [characterDetection, pullback_detection_iff] using h

omit [Finite B] in
/-- The form consumed by the injection enlargement: injectivity on the base
logical alphabet suffices for the same detection probability. -/
theorem target_detection_after_quotient (s : Stage k B) [Fintype s.Noise]
    {E : Type*} [AddCommGroup E] [Module k E] [DecidableEq E]
    (T : StageQuotient.Space s →ₗ[k] E) (q : ℚ)
    (hfull : ∀ L : Lift s (⊤ : Submodule k (Module.Dual k B)),
      q ≤ probability (fun n => ∃ z, L.family z (s.noise n) ≠ 0))
    (hinj : Function.Injective (T.comp (StageQuotient.shift s))) :
    q ≤ probability (fun n => T (StageQuotient.noise s n) ≠ 0) := by
  exact target_detection_of_full_lift_bound (StageQuotient.noise s)
    (StageQuotient.shift s) T q (full_detection_after_quotient s q hfull) hinj

end UniqueGamesTheorem.Gadget.QuotientDetection

end

section

/-!
# Exact finite-stage nonlinear noise law

This packages the one-level recurrence for the actual recursive `Stage`, solves
it at every height, and proves that the ambient-kernel quotient preserves it.
The averaged block kernel remains an explicit argument for later instantiation
with the concrete quadratic family.
-/

namespace UniqueGamesTheorem.Gadget.StageNoiseRecurrence

open scoped BigOperators

theorem average_eq_expect {A : Type*} [Fintype A] (f : A → ℚ) :
    average f = 𝔼 a, f a := by
  have he : Fintype.ofFinite A = ‹Fintype A› := Subsingleton.elim _ _
  unfold average
  rw [he]

universe u v

variable {k : Type u} {B : Type v} [CommRing k] [AddCommGroup B] [Module k B]

theorem error_eq_expect [DecidableEq B] (s : Stage k B) [Fintype s.Input] [Fintype s.Noise] :
    error s = 𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0 := by
  classical
  simp only [error, average_eq_expect]
  apply Finset.expect_congr rfl
  intro n _
  apply Finset.expect_congr rfl
  intro u _
  split_ifs <;> rfl

variable [Fintype B] [DecidableEq B]

theorem base_error : error (Stage.base (k := k) (B := B)) =
    1 - 1 / (Fintype.card B : ℚ) := by
  classical
  let : Fintype (Stage.base (k := k) (B := B)).Input := ‹Fintype B›
  let : Fintype (Stage.base (k := k) (B := B)).Noise := ‹Fintype B›
  rw [error_eq_expect]
  change (𝔼 a : B, 𝔼 u : B, if u + a ≠ u then (1 : ℚ) else 0) = _
  have hpoint (a u : B) : (u + a ≠ u) ↔ a ≠ 0 := by
    constructor
    · intro h ha
      exact h (by rw [ha, add_zero])
    · intro ha h
      apply ha
      exact add_left_cancel (show u + a = u + 0 by simpa only [add_zero] using h)
  simp_rw [hpoint, Fintype.expect_const]
  calc
    (𝔼 a : B, if a ≠ 0 then (1 : ℚ) else 0) =
        𝔼 a : B, (1 - if a = 0 then (1 : ℚ) else 0) := by
      apply Finset.expect_congr rfl
      intro a _
      by_cases ha : a = 0 <;> simp [ha]
    _ = 1 - (𝔼 a : B, if a = 0 then (1 : ℚ) else 0) := by
      rw [Finset.expect_sub_distrib, Fintype.expect_const]
    _ = _ := by simp

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X] [Fintype X]

/-- The exact one-level law for the actual stage constructor. -/
theorem next_error (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 →
      (𝔼 i, 𝔼 z : X × B,
        NonlinearRecurrence.change (fun p => p.2 + Q p.1) z (J i d)) = ρ)
    (s : Stage k B) : error (Stage.next J hJ Q s) = ρ * error s := by
  classical
  let := Fintype.ofFinite s.Input
  let := Fintype.ofFinite s.Noise
  let : Fintype (Stage.next J hJ Q s).Input := inferInstanceAs (Fintype (I → s.Input))
  let : Fintype (Stage.next J hJ Q s).Noise := inferInstanceAs (Fintype (I × s.Noise))
  simp only [error_eq_expect]
  change (𝔼 t : I × s.Noise, 𝔼 u : I → s.Input,
    if parentOutput J s.output Q (u + (Pi.single t.1 (s.noise t.2) : I → s.Input)) ≠
      parentOutput J s.output Q u then (1 : ℚ) else 0) =
    ρ * (𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0)
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact NonlinearRecurrence.parent_change_recurrence J hJ s.embed s.logical
    s.logical_surjective s.output s.equivariant (fun p => p.2 + Q p.1) s.noise ρ hk

/-- Solving the proved recurrence, with the actual height-zero probability. -/
theorem iterate_error (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 →
      (𝔼 i, 𝔼 z : X × B,
        NonlinearRecurrence.change (fun p => p.2 + Q p.1) z (J i d)) = ρ)
    (n : ℕ) : error (Stage.iterate J hJ Q n) =
      (1 - 1 / (Fintype.card B : ℚ)) * ρ ^ n := by
  induction n with
  | zero => simp [Stage.iterate_zero, base_error]
  | succ n ih =>
    rw [Stage.iterate_succ, next_error J hJ Q ρ hk, ih, pow_succ]
    ac_rfl

/-- The quotient uses the original noise choices and preserves their full
uniform-input change probability. -/
theorem quotient_error (s : Stage k B) : error (StageQuotient.toStage s) = error s := by
  classical
  let := Fintype.ofFinite s.Input
  let := Fintype.ofFinite s.Noise
  let := Fintype.ofFinite (StageQuotient.Space s)
  let : Fintype (StageQuotient.toStage s).Input := inferInstanceAs (Fintype (StageQuotient.Space s))
  let : Fintype (StageQuotient.toStage s).Noise := inferInstanceAs (Fintype s.Noise)
  simp only [error_eq_expect]
  change (𝔼 n : s.Noise, 𝔼 x : StageQuotient.Space s,
    if StageQuotient.output s (x + StageQuotient.noise s n) ≠
      StageQuotient.output s x then (1 : ℚ) else 0) =
    𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0
  apply Finset.expect_congr rfl
  intro n _
  calc
    _ = 𝔼 u : s.Input,
      if StageQuotient.output s (StageQuotient.projection s u + StageQuotient.noise s n) ≠
        StageQuotient.output s (StageQuotient.projection s u) then (1 : ℚ) else 0 :=
      (EmbeddedConditional.expect_linear_surjective (StageQuotient.projection s)
        (StageQuotient.projection_surjective s)
        (fun x : StageQuotient.Space s =>
          if StageQuotient.output s (x + StageQuotient.noise s n) ≠
            StageQuotient.output s x then (1 : ℚ) else 0)).symm
    _ = _ := by simp only [StageQuotient.noise_change_iff]

end UniqueGamesTheorem.Gadget.StageNoiseRecurrence

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_ActualGadgetLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual finite binary-vector-space gadgets and their uniform experiments.
The existence statement is the target of the recursive construction, not an
assumed theorem. Noise is indexed by a nonempty finite type; repeated vector
values therefore keep their intended multiplicities. -/

namespace UniqueGamesTheorem.Gadget.ActualGadget

attribute [instance] Data.ambientAddCommGroup Data.ambientModule Data.ambientFintype
attribute [instance] Data.noiseFintype Data.noiseNonempty

end UniqueGamesTheorem.Gadget.ActualGadget

end

section

noncomputable section

namespace UniqueGamesTheorem.Gadget.StageData

open scoped BigOperators Classical
open UniqueGamesTheorem.Gadget

variable {C : Type} [AddCommGroup C] [Module (ZMod 2) C]

/-- Intrinsic count probability and uniform finite expectation are identical. -/
theorem count_probability_eq_expect {Ω : Type*} [Fintype Ω] (p : Ω → Prop) :
    Enlargement.probability p = 𝔼 x : Ω, if p x then (1 : ℚ) else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Enlargement.probability, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem stabilityError_toData (s : Stage (ZMod 2) C) (embed : C →ₗ[ZMod 2] s.Input)
    (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c) :
    ActualGadget.stabilityError (toData s embed hinj hEquiv) = StageNoiseRecurrence.error s := by
  classical
  let := Fintype.ofFinite s.Input
  let := Fintype.ofFinite s.Noise
  rw [StageNoiseRecurrence.error_eq_expect]
  unfold ActualGadget.stabilityError
  change (𝔼 t : s.Input × s.Noise,
    if s.output (t.1 + s.noise t.2) = s.output t.1 then (0 : ℚ) else 1) = _
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  simp only [ne_eq, ite_not]

theorem stabilityError_toData_count (s : Stage (ZMod 2) C)
    [Fintype s.Input] [Fintype s.Noise] (embed : C →ₗ[ZMod 2] s.Input)
    (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c) :
    ActualGadget.stabilityError (toData s embed hinj hEquiv) =
      Enlargement.probability (fun t : s.Input × s.Noise =>
        s.output (t.1 + s.noise t.2) ≠ s.output t.1) := by
  classical
  rw [stabilityError_toData, StageNoiseRecurrence.error_eq_expect,
    count_probability_eq_expect]
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro u _
  apply Finset.expect_congr rfl
  intro n _
  split_ifs <;> rfl

theorem error_eq_count_probability (s : Stage (ZMod 2) C)
    [Fintype s.Input] [Fintype s.Noise] :
    StageNoiseRecurrence.error s = Enlargement.probability
      (fun t : s.Input × s.Noise => s.output (t.1 + s.noise t.2) ≠ s.output t.1) := by
  classical
  rw [StageNoiseRecurrence.error_eq_expect, count_probability_eq_expect]
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro u _
  apply Finset.expect_congr rfl
  intro n _
  split_ifs <;> rfl

theorem kernelError_toData_count (s : Stage (ZMod 2) C) [Fintype s.Noise]
    (embed : C →ₗ[ZMod 2] s.Input) (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (T : s.Input →ₗ[ZMod 2] E) :
    ActualGadget.kernelError (toData s embed hinj hEquiv) T =
      Enlargement.probability (fun n : s.Noise => T (s.noise n) = 0) := by
  classical
  rw [count_probability_eq_expect]
  change StageNoiseRecurrence.average (fun n : s.Noise =>
    if T (s.noise n) = 0 then (1 : ℚ) else 0) = _
  rw [StageNoiseRecurrence.average_eq_expect]

/-- The common interface's zero-image error is exactly the complement of
the nonzero-image detection probability. -/
theorem kernelError_eq_one_sub_detection (s : Stage (ZMod 2) C) [Fintype s.Noise]
    (embed : C →ₗ[ZMod 2] s.Input) (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (T : s.Input →ₗ[ZMod 2] E) :
    ActualGadget.kernelError (toData s embed hinj hEquiv) T =
      1 - Enlargement.probability (fun n : s.Noise => T (s.noise n) ≠ 0) := by
  classical
  rw [kernelError_toData_count, count_probability_eq_expect, count_probability_eq_expect]
  calc
    (𝔼 n : s.Noise, if T (s.noise n) = 0 then (1 : ℚ) else 0) =
        𝔼 n : s.Noise, (1 - if T (s.noise n) ≠ 0 then (1 : ℚ) else 0) := by
      apply Finset.expect_congr rfl
      intro n _
      by_cases hn : T (s.noise n) = 0 <;> simp [hn]
    _ = _ := by
      rw [Finset.expect_sub_distrib, Fintype.expect_const]
      apply congrArg (fun x : ℚ => 1 - x)
      apply Finset.expect_congr rfl
      intro n _
      split_ifs <;> rfl

theorem kernelError_le_of_detection (s : Stage (ZMod 2) C) [Fintype s.Noise]
    (embed : C →ₗ[ZMod 2] s.Input) (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (T : s.Input →ₗ[ZMod 2] E)
    (d : ℚ) (hd : d ≤ Enlargement.probability (fun n : s.Noise => T (s.noise n) ≠ 0)) :
    ActualGadget.kernelError (toData s embed hinj hEquiv) T ≤ 1 - d := by
  rw [kernelError_eq_one_sub_detection]
  exact sub_le_sub_left hd 1

end UniqueGamesTheorem.Gadget.StageData

end

end

section

/-!
# Constant-detection enlargement endpoint

The finite base alphabet and its rank threshold are fixed before the target
logical space. The resulting actual gadget has the same nonlinear error and
linear kernel error at most `7/8`.
-/

noncomputable section

namespace UniqueGamesTheorem.Gadget.EnlargementEndpoint

open scoped Classical
open Enlargement EnlargementConstruction
open UniqueGamesTheorem.Gadget

variable {B K V N : Type}
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
variable [FiniteDimensional (ZMod 2) B]
variable [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
variable [FiniteDimensional (ZMod 2) K]
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype N] [Nonempty N]

/-- Base stability and base detection suffice for the complete enlarged
gadget. Its detection error is the fixed constant `7/8`. -/
theorem data_satisfies (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) (p : ℚ)
    (hchange : probability (fun z : V × N => C (z.1 + noise z.2) ≠ C z.1) ≤ p)
    (hbase : ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
      (U : V →ₗ[ZMod 2] E), Function.Injective (U.comp i) →
        1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0)) :
    ActualGadget.Satisfies (data i hi C hC noise hdim b₀ hb₀) p (7 / 8)
      (Module.finrank (ZMod 2) B + 2) := by
  let s := productStage i hi C hC noise hdim b₀ hb₀
  let q := StageQuotient.toStage s
  let : Fintype (StageQuotient.Space s) := Fintype.ofFinite _
  let : Fintype q.Input := Fintype.ofFinite _
  let : Fintype q.Noise := Fintype.ofFinite _
  constructor
  · change ActualGadget.stabilityError (StageData.toData q (StageQuotient.shift s)
      (StageQuotient.shift_injective s) (StageQuotient.output_equivariant s)) ≤ p
    have heq := StageData.stabilityError_toData_count q (StageQuotient.shift s)
      (StageQuotient.shift_injective s) (StageQuotient.output_equivariant s)
    have hc := change_probability i hi C hC noise hdim b₀ hb₀
    exact heq.le.trans (hc.le.trans hchange)
  · intro E _ _ T hr
    have hd := detection_probability i hi C hC noise hdim b₀ hb₀ (hbase E) T hr
    have he := StageData.kernelError_le_of_detection q (StageQuotient.shift s)
      (StageQuotient.shift_injective s) (StageQuotient.output_equivariant s) T (1 / 8) hd
    norm_num at he
    exact he

/-- For every permitted logical space there is an actual gadget. The rank
threshold `dim B + 2` and all base data are independent of that space. -/
theorem exists_data (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) (p : ℚ)
    (hchange : probability (fun z : V × N => C (z.1 + noise z.2) ≠ C z.1) ≤ p)
    (hbase : ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
      (U : V →ₗ[ZMod 2] E), Function.Injective (U.comp i) →
        1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0)) :
    ∃ g : ActualGadget.Data K,
      ActualGadget.Satisfies g p (7 / 8) (Module.finrank (ZMod 2) B + 2) :=
  ⟨data i hi C hC noise hdim b₀ hb₀,
    data_satisfies i hi C hC noise hdim b₀ hb₀ p hchange hbase⟩

end UniqueGamesTheorem.Gadget.EnlargementEndpoint

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ActualSourceLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.ActualSource

open UniqueGamesTheorem.Integration.BinaryLinear

attribute [instance] SplitGadget.noiseFintype SplitGadget.noiseNonempty

end UniqueGamesTheorem.Reduction.ActualSource

end

section

/-! Transport of actual gadgets to the split coordinate model used by the reduction. -/

namespace UniqueGamesTheorem.Integration.SplitGadget

open BinaryLinear

variable {R : Type} [AddCommGroup R] [Module F2 R] [FiniteDimensional F2 R]

/-- Any injective symbol embedding admits finite coordinates in which it is the
first summand. This is a theorem about the actual ambient vector space. -/
theorem exists_split_equiv {s : Nat} (e : Vector s →ₗ[F2] R)
    (he : Function.Injective e) :
    ∃ d : Nat, ∃ φ : R ≃ₗ[F2] (Vector s × Vector d),
      ∀ c, φ (e c) = (c, 0) := by
  obtain ⟨U, hU⟩ := e.range.exists_isCompl
  let er := LinearEquiv.ofInjective e he
  let eu := (Module.finBasis F2 U).equivFun
  let split := e.range.prodEquivOfIsCompl U hU
  refine ⟨Module.finrank F2 U, split.symm.trans (er.symm.prodCongr eu), ?_⟩
  intro c
  change (er.symm.prodCongr eu) (split.symm (e c)) = (c, 0)
  have hc : split.symm (e c) = (er c, 0) :=
    e.range.prodEquivOfIsCompl_symm_apply_left U hU (er c)
  rw [hc]
  simp

open UniqueGamesTheorem.Gadget.ActualGadget (Data stabilityError failureIndicator kernelError Satisfies)
open UniqueGamesTheorem.Reduction.ActualSource

/-- Uniform stability is invariant under the coordinate change. -/
theorem transport_stabilityError {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0)) :
    (transport g φ he).stabilityError = stabilityError g := by
  classical
  apply Fintype.expect_equiv (φ.symm.toEquiv.prodCongr (Equiv.refl g.NoiseIndex))
  intro x
  simp [transport, failureIndicator, map_add]

/-- The restriction to the symbol space is exactly the same linear map. -/
theorem transport_symbol_map {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0))
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    (S.comp φ.toLinearMap).comp g.embed = S.comp (alphabetEmbedding s d) := by
  apply LinearMap.ext
  intro c
  change S (φ (g.embed c)) = S (c, 0)
  rw [he]

theorem transport_kernelProbability {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0))
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    kernelProbability (transport g φ he) S =
      kernelError g (S.comp φ.toLinearMap) := by
  rfl

/-- The coordinate representative preserves dispersion for every target,
including the question spaces used directly by the soundness analysis. -/
theorem exists_split_gadget_general {s : Nat} (g : Data (Vector s))
    {ζ ν : ℚ} {r : Nat} (hg : Satisfies g ζ ν r) :
    ∃ d : Nat, ∃ h : SplitGadget s d,
      h.stabilityError ≤ ζ ∧
      ∀ (P : Type) [AddCommGroup P] [Module F2 P]
        (S : Ambient s d →ₗ[F2] P),
        r ≤ Module.finrank F2 (S.comp (alphabetEmbedding s d)).range →
        kernelProbability h S ≤ ν := by
  obtain ⟨d, φ, he⟩ := exists_split_equiv g.embed g.embed_injective
  refine ⟨d, transport g φ he, ?_, ?_⟩
  · rw [transport_stabilityError]
    exact hg.1
  · intro P _ _ S hS
    rw [transport_kernelProbability g φ he S]
    apply hg.2 P (S.comp φ.toLinearMap)
    rwa [transport_symbol_map g φ he S]

end UniqueGamesTheorem.Integration.SplitGadget

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_NoiseEnumerationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Finite noise tables for the executable outer reduction. Positions, including
positions containing equal vectors, remain distinct sample outcomes. -/

namespace UniqueGamesTheorem.Integration.NoiseTables

open BinaryLinear UniqueGamesTheorem.Reduction.ActualSource

variable {s d : Nat}

namespace Table

theorem noise_positionEquiv (g : SplitGadget s d) (en : NoiseEnumeration g)
    (i : Fin (ofEnumeration g en).vectors.length) :
    ((ofEnumeration g en).gadget g.f g.equivariant).noise i =
      g.noise (positionEquiv g en i) := by
  change (en.indices.map g.noise)[i.val] = g.noise en.indices[i.val]
  exact List.getElem_map _

theorem stabilityError_ofEnumeration (g : SplitGadget s d) (en : NoiseEnumeration g) :
    ((ofEnumeration g en).gadget g.f g.equivariant).stabilityError =
      g.stabilityError := by
  apply Fintype.expect_equiv
    ((Equiv.refl (Ambient s d)).prodCongr (positionEquiv g en))
  intro x
  change (if g.f (x.1 + _) = g.f x.1 then (0 : ℚ) else 1) = _
  rw [noise_positionEquiv]
  rfl

theorem kernelProbability_ofEnumeration (g : SplitGadget s d)
    (en : NoiseEnumeration g) {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    SplitGadget.kernelProbability ((ofEnumeration g en).gadget g.f g.equivariant) S =
      SplitGadget.kernelProbability g S := by
  classical
  apply Fintype.expect_equiv (positionEquiv g en)
  intro i
  rw [noise_positionEquiv]

end Table
end UniqueGamesTheorem.Integration.NoiseTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualSpectralLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Reduction.ActualSource
open UniqueGamesTheorem.Fourier.MatrixNoise

namespace UniqueGamesTheorem.Decoder.ActualSpectral

open TableKeysGame PositiveMultiplier NoiseSampler SurrogateFibers

theorem expect_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    (𝔼 p, f p) = 𝔼 a, 𝔼 b, f (a, b) := by
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product Finset.univ Finset.univ f)

theorem expect_eq_uniform_sum {I : Type*} [Fintype I] (f : I → ℝ) :
    (𝔼 i, f i) = ∑ i, (Fintype.card I : ℝ)⁻¹ * f i := by
  rw [Fintype.expect_eq_sum_div_card, ← Finset.mul_sum]
  ring

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.ActualSpectral.homFintype
/-- The finite noise law's multiplier is exactly the rational kernel event
of the same gadget, cast to the real numbers. -/
theorem eigenvalue_eq_kernelProbability {s d : Nat} (g : SplitGadget s d)
    {P : Type} [AddCommGroup P] [Module F2 P] (S : Ambient s d →ₗ[F2] P) :
    linearNoiseEigenvalue (samplerLaw g.noise) S =
      (Integration.SplitGadget.kernelProbability g S : ℝ) := by
  rw [← sample_kernel_eq_eigenvalue]
  unfold Integration.SplitGadget.kernelProbability
  rw [rat_expect_cast]
  simp only [apply_ite, Rat.cast_one, Rat.cast_zero]

/-- The four independent samples of the actual single-orbit test. -/
theorem acceptance_nested (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) :
    (acceptanceProbability S k g label : ℝ) =
      𝔼 U : Question S k, 𝔼 X : Map k s d, 𝔼 i : g.NoiseIndex, 𝔼 l : Dual k,
        if unfolded S k s d label (U, X) =
          unfolded S k s d label (U, X + l.smulRight (g.noise i))
        then (1 : ℝ) else 0 := by
  rw [acceptanceProbability_eq_test, rat_expect_cast]
  simp only [apply_ite, Rat.cast_one, Rat.cast_zero]
  simp only [expect_prod, leftQuery, rightQuery, ActualGame.leftQuery, ActualGame.rightQuery]
  apply Finset.expect_congr rfl
  intro U _
  apply Finset.expect_congr rfl
  intro X _
  apply Finset.expect_congr rfl
  intro i _
  apply Finset.expect_congr rfl
  intro l _
  by_cases h : unfolded S k s d label (U, X) =
      unfolded S k s d label (U, X + l.smulRight (g.noise i)) <;> simp [h]

/-- No auxiliary side labeling is introduced: the same restored table occurs
on both sides of the actual equality test. -/
theorem acceptance_eq_equality_mean (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) :
    (acceptanceProbability S k g label : ℝ) =
      𝔼 U : Question S k,
        equalityAcceptance (samplerLaw g.noise) (fun X : Map k s d =>
          unfolded S k s d label (U, X)) := by
  rw [acceptance_nested]
  apply Finset.expect_congr rfl
  intro U _
  unfold equalityAcceptance
  apply Finset.expect_congr rfl
  intro X _
  rw [← sample_expect_eq]
  apply Finset.expect_congr rfl
  intro i _
  apply Finset.expect_congr rfl
  intro l _
  split_ifs <;> rfl

theorem fiberAcceptance_le_one (S : Source) (k s d : Nat)
    (label : Fin (vertexCount S k s d) → Fin (2 ^ s))
    (U : Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d) :
    fiberAcceptance S k s d label U T ≤ 1 := by
  unfold fiberAcceptance shortcodeAcceptance
  apply Finset.expect_le Finset.univ_nonempty
  intro M _
  apply Finset.expect_le Finset.univ_nonempty
  intro a _
  apply Finset.expect_le Finset.univ_nonempty
  intro l _
  split_ifs <;> norm_num

theorem weighted_fiber_mean_lower (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s))
    (μ : Question S k → ℝ) (r : Nat)
    (hμ : ∀ U, 0 ≤ μ U) (hμsum : ∑ U, μ U = 1)
    (hkernel : ∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
      r ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
      Integration.SplitGadget.kernelProbability g L ≤ 7 / 8)
    (haccept : (99 : ℝ) / 100 ≤ ∑ U, μ U *
      equalityAcceptance (samplerLaw g.noise)
        (fun X : Map k s d => unfolded S k s d label (U, X))) :
    (9 : ℝ) / 10 * ((2 : ℝ) ^ r)⁻¹ ≤
      ∑ U, μ U * (𝔼 T, fiberAcceptance S k s d label U T) := by
  have h := matrix_spectral_comparison μ (samplerLaw g.noise) (alphabetEmbedding s d)
    (fun U (X : Map k s d) => unfolded S k s d label (U, X)) r
    hμ hμsum (samplerLaw_nonneg g.noise) (samplerLaw_normalized g.noise)
    (fun L hL => by
      rw [eigenvalue_eq_kernelProbability]
      have hc := (Rat.cast_le (K := ℝ)).mpr (hkernel L hL)
      simpa only [Rat.cast_div, Rat.cast_ofNat] using hc) haccept
  simpa only [alphabetEmbedding, surrogate_acceptance_eq_fiber_average,
    fiberAcceptance] using h

theorem actual_fiber_mean_lower (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) (r : Nat)
    (hkernel : ∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
      r ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
      Integration.SplitGadget.kernelProbability g L ≤ 7 / 8)
    (haccept : (99 : ℚ) / 100 ≤ acceptanceProbability S k g label) :
    (9 : ℝ) / 10 * ((2 : ℝ) ^ r)⁻¹ ≤
      𝔼 U : Question S k, 𝔼 T, fiberAcceptance S k s d label U T := by
  rw [expect_eq_uniform_sum]
  apply weighted_fiber_mean_lower S k g label
    (fun _ => (Fintype.card (Question S k) : ℝ)⁻¹) r
  · intro U
    positivity
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    apply mul_inv_cancel₀
    exact_mod_cast Fintype.card_ne_zero (α := Question S k)
  · exact hkernel
  · have hc := (Rat.cast_le (K := ℝ)).mpr haccept
    rw [acceptance_eq_equality_mean, expect_eq_uniform_sum] at hc
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

theorem eta_pos (r : Nat) : 0 < eta r := by unfold eta; positivity

/-- At least `10 η` of the actual `(U,T)` pairs have shortcode acceptance
at least `4 η`, exactly the input needed by row erasure. -/
theorem actual_good_fiber_mass (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) (r : Nat)
    (hkernel : ∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
      r ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
      Integration.SplitGadget.kernelProbability g L ≤ 7 / 8)
    (haccept : (99 : ℚ) / 100 ≤ acceptanceProbability S k g label) :
    10 * eta r ≤ 𝔼 U : Question S k,
      𝔼 T : ActualHomogeneous.E k →ₗ[F2] Vector d,
        if 4 * eta r ≤ fiberAcceptance S k s d label U T then (1 : ℝ) else 0 := by
  let I := Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d)
  let μ : I → ℝ := fun _ => (Fintype.card I : ℝ)⁻¹
  let p : I → ℝ := fun a => fiberAcceptance S k s d label a.1 a.2
  have hmean := actual_fiber_mean_lower S k g label r hkernel haccept
  have hmean' : (72 : ℝ) / 5 * eta r ≤ ∑ a, μ a * p a := by
    rw [← expect_eq_uniform_sum, expect_prod]
    unfold eta
    nlinarith
  have h := good_fiber_mass μ p (eta r) (fun _ => by positivity)
    (by simp [μ, Fintype.card_ne_zero]) (eta_pos r).le
    (fun a => fiberAcceptance_le_one S k s d label a.1 a.2) hmean'
  change 10 * eta r ≤
    ∑ a : Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d),
      (Fintype.card (Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d)) : ℝ)⁻¹ *
        (if 4 * eta r ≤ fiberAcceptance S k s d label a.1 a.2 then 1 else 0) at h
  rw [← expect_eq_uniform_sum, expect_prod] at h
  exact h

end UniqueGamesTheorem.Decoder.ActualSpectral

end

end

section

namespace UniqueGamesTheorem.Decoder.ActualGoodRows

open Integration.BinaryLinear Reduction ActualSource
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat HasAffineSlice)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] OAI.UniqueGamesTheorem.Decoder.ActualGoodRows.homFintype
theorem table_acceptance (S : Source) (k s d : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (U : ActualGame.Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d) :
    Shortcode.equalityAcceptance (table S k s d labeling U T) =
      ActualSpectral.fiberAcceptance S k s d labeling U T := by
  unfold table
  rw [← MatrixCoordinates.shortcodeAcceptance_eq k s
    (fun M : ActualHomogeneous.E k →ₗ[F2] Vector s =>
      TableKeysGame.unfolded S k s d labeling (U, M.prod T))]
  unfold ActualSpectral.fiberAcceptance SurrogateFibers.shortcodeAcceptance
  apply Finset.expect_congr (by ext M; simp only [Finset.mem_univ])
  intro M _
  apply Finset.expect_congr (by ext a; simp only [Finset.mem_univ])
  intro a _
  apply Finset.expect_congr (by ext l; simp only [Finset.mem_univ])
  intro l _
  rfl

theorem goodRowMass_pos (rstar s r : ℕ) : 0 < goodRowMass rstar s r := by
  unfold goodRowMass
  have h := ActualSpectral.eta_pos rstar
  positivity

theorem exists_actual_advice_threshold (rstar : ℕ) (α : ℝ)
    (hα : 0 < α) (hαone : α ≤ 1) (s r : ℕ)
    (hr : r < s) (halphabet : 1 / (2 : ℝ) ^ s ≤ α / 8) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (∀ f : Mat s (1 + 2 * k) → Vector s,
        ActualSpectral.eta rstar ≤ Shortcode.equalityAcceptance f → HasAffineSlice f α r) →
      ∀ (S : Source) (d : ℕ) (g : SplitGadget s d)
        (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)),
        (∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
          rstar ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
          Integration.SplitGadget.kernelProbability g L ≤ 7 / 8) →
        (99 : ℚ) / 100 ≤ TableKeysGame.acceptanceProbability S k g labeling →
        goodRowMass rstar s r ≤ adviceMass S k s d r labeling α := by
  obtain ⟨m₀, hm₀⟩ := RowErasureMatrix.exists_contextual_advice_threshold
    (ActualSpectral.eta rstar) α (ActualSpectral.eta_pos rstar) hα hαone
    s r hr halphabet
  refine ⟨m₀, ?_⟩
  intro k hk hinverse S d g labeling hkernel haccept
  let Q := ActualGame.Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d)
  let f : Q → Mat s (1 + 2 * k) → Vector s :=
    fun q => table S k s d labeling q.1 q.2
  have hcontext : 10 * ActualSpectral.eta rstar ≤
      uniformMass (fun q : Q => 4 * ActualSpectral.eta rstar ≤
        Shortcode.equalityAcceptance (f q)) := by
    have h := ActualSpectral.actual_good_fiber_mass S k g labeling rstar hkernel haccept
    dsimp only [Q, f]
    unfold uniformMass
    rw [ActualSpectral.expect_prod]
    simpa only [indicator, table_acceptance] using h
  have h := hm₀ (1 + 2 * k) (by omega) hinverse Q f hcontext
  dsimp only [Q, f] at h
  rw [ActualSpectral.expect_prod] at h
  simpa only [goodRowMass, adviceMass] using h

end
end UniqueGamesTheorem.Decoder.ActualGoodRows

end

section

namespace UniqueGamesTheorem.Decoder.MatrixGapChoice

open Integration.BinaryLinear Reduction ActualSource
open Inverse.Shortcode (Mat HasAffineSlice InversePrinciple equalityAcceptance)

noncomputable section

theorem eta_lt_one (rstar : ℕ) : ActualSpectral.eta rstar < 1 := by
  have hp : (1 : ℝ) ≤ 2 ^ rstar := one_le_pow₀ (by norm_num)
  have hi : 1 / (2 : ℝ) ^ rstar ≤ 1 := by
    exact (div_le_one (by positivity)).mpr hp
  unfold ActualSpectral.eta
  rw [← one_div]
  linarith

theorem exists_inverse_parameters (hinverse : InversePrinciple) (rstar : ℕ) :
    Nonempty (InverseParameters rstar) := by
  obtain ⟨α, hα, hαone, r, _hr, s₀, hinv⟩ :=
    hinverse (ActualSpectral.eta rstar) (ActualSpectral.eta_pos rstar) (eta_lt_one rstar)
  obtain ⟨s, hs, hrs, hsmall, _htiny⟩ := DimensionSelection.exists_logical_dimension
    hα (ActualSpectral.eta_pos rstar) r (max rstar s₀)
  have hsstar : rstar ≤ s := (le_max_left _ _).trans hs
  have hs₀ : s₀ ≤ s := (le_max_right _ _).trans hs
  obtain ⟨m₀, hm₀⟩ := hinv s hs₀
  have halphabet : 1 / (2 : ℝ) ^ s ≤ α / 8 := by
    have hp : (2 : ℝ) ^ (s - r) ≤ 2 ^ s :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le s r)
    exact (one_div_le_one_div_of_le (by positivity) hp).trans hsmall.le
  obtain ⟨k₀, hk₀⟩ := ActualGoodRows.exists_actual_advice_threshold
    rstar α hα hαone s r hrs halphabet
  let threshold := max m₀ k₀
  have hi (k : ℕ) (hk : threshold ≤ k) :
      ∀ f : Mat s (1 + 2 * k) → Vector s,
        ActualSpectral.eta rstar ≤ equalityAcceptance f → HasAffineSlice f α r := by
    apply hm₀ (1 + 2 * k)
    have hm : m₀ ≤ k := (le_max_left _ _).trans hk
    omega
  refine ⟨{
    α := α
    positive := hα
    bounded := hαone
    r := r
    s := s
    s_large := hsstar
    r_small := hrs
    trivial_small := hsmall
    tupleThreshold := threshold
    inverse := hi
    advice := ?_ }⟩
  intro k hk S d g labeling hkernel haccept
  exact hk₀ k ((le_max_right _ _).trans hk) (hi k hk) S d g labeling hkernel haccept

/-- After all fixed dimensions are known, the cube simultaneously exceeds the
inverse threshold, reduces full-table variation, and beats the decoder mass. -/
theorem exists_cube {rstar : ℕ} (P : InverseParameters rstar) (d : ℕ) :
    ∃ m : ℕ, 0 < m ∧ P.tupleThreshold ≤ m ^ 3 ∧
      0 ≤ 1 / (m : ℝ) ^ 2 ∧ 1 / (m : ℝ) ^ 2 ≤ 1 ∧
      Foundations.Information.totalVariation
        (SparseLaw.independentWeights
          (SparseLaw.mixture (1 / (m : ℝ) ^ 2)
            (SparseLaw.singletonPairWeights (Ambient P.s d))) (m ^ 3))
        (SparseLaw.uniformWeights (Fin (m ^ 3) → Ambient P.s d × Ambient P.s d)) ≤
          ConstantSelection.variationBudget P.α (ActualGoodRows.goodRowMass rstar P.s P.r) P.s P.r ∧
      (1 - ((1 / (m : ℝ) ^ 2) / (2 : ℝ) ^ (d + P.r)) / 3600) ^ (m ^ 3) <
        ConstantSelection.decodingMass P.α (ActualGoodRows.goodRowMass rstar P.s P.r) P.s P.r := by
  obtain ⟨m, hlarge, hm, htv, hrate⟩ := ConstantSelection.exists_matrix_cube (Ambient P.s d)
    P.positive (ActualGoodRows.goodRowMass_pos rstar P.s P.r) P.s P.r d P.tupleThreshold
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hmsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hmreal
  refine ⟨m, hm, hlarge.trans (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) m),
    by positivity, ?_, htv, hrate⟩
  exact (div_le_one (by positivity)).mpr hmsq

end
end UniqueGamesTheorem.Decoder.MatrixGapChoice

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_AnalyticCheegerLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Scalar parameter selection for the v2 repetition rate.

These results concern powers of real numbers only. In particular, they do not
assert a parallel-repetition theorem for games. The exponent depends only on
the gap and the desired error; no alphabet or logical dimension occurs here.
-/

namespace UniqueGamesTheorem.Repetition

theorem dsRate_lt_one {gap : ℝ} (hgap : 0 < gap) : dsRate gap < 1 := by
  dsimp [dsRate]
  nlinarith [sq_pos_of_pos hgap]

/-- A scalar contraction admits a strictly positive exponent for every positive
target error. This lemma makes no assertion about any game value. -/
theorem exists_positive_power_lt {rate error : ℝ}
    (hrate₀ : 0 ≤ rate) (hrate₁ : rate < 1) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ rate ^ n < error := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hrate₀ hrate₁
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds herror)).exists
  refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), ?_⟩
  calc
    rate ^ (n + 1) = rate ^ n * rate := pow_succ _ _
    _ ≤ rate ^ n := mul_le_of_le_one_right (pow_nonneg hrate₀ n) hrate₁.le
    _ < error := hn

/-- Select the repetition count before choosing any alphabet. -/
theorem exists_dsRate_pow_le {gap error : ℝ}
    (hgap₀ : 0 < gap) (hgap₁ : gap < 1) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ dsRate gap ^ n ≤ error := by
  obtain ⟨n, hn, hbound⟩ := exists_positive_power_lt
    (dsRate_nonneg hgap₀.le hgap₁.le) (dsRate_lt_one hgap₀) herror
  exact ⟨n, hn, hbound.le⟩

theorem dsRate_one_div_eight_hundred :
    dsRate (1 / 800) = 1 - (1 : ℝ) / 10240000 := by
  norm_num [dsRate]

/-- The final soundness exponent depends only on `error`, even when the later
construction chooses its alphabet after this exponent. -/
theorem exists_final_repetition_count {error : ℝ} (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ (1 - (1 : ℝ) / 10240000) ^ n ≤ error := by
  simpa only [dsRate_one_div_eight_hundred] using
    exists_dsRate_pow_le (gap := (1 / 800 : ℝ)) (by norm_num) (by norm_num) herror

end UniqueGamesTheorem.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_TableKeysAddressGameLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Transport the matrix-test bound to the actual direct-address edge list.
Every address labeling restricts to a semantic orbit labeling, with exactly
the same satisfied fraction and the same occurrence multiplicities. -/

namespace UniqueGamesTheorem.Decoder.MatrixGap

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Integration
open ActualSource

noncomputable section

/-- Soundness is measured on the generated direct-address instance. Unused
addresses and reindexing introduce no additional labeling advantage. -/
theorem address_value_le_of_semantic_acceptance (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c)
    (h : ∀ labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s),
      TableKeysGame.acceptanceProbability S k (T.gadget f hf) labeling ≤ (99 : ℚ) / 100) :
    InstanceValue.value (TableKeysAddressGame.tableOutput S k T) ≤ (99 : ℝ) / 100 := by
  rw [TableKeysAddressGame.tableOutput_eq_with_witness S k T f hf]
  apply (InstanceValue.forall_rate_le_iff _ (by positivity) _).mp
  intro labeling
  change (Fin (TableKeysAddressGame.vertexCount S k s d) → Fin (2 ^ s)) at labeling
  have hrate : GapSemantics.satisfactionRate
      (TableKeysAddressGame.outputInstance S k (T.gadget f hf)
        (TableReduction.tableEnumeration T f hf)) labeling ≤ (99 : ℚ) / 100 := by
    rw [address_rate_eq_semantic_acceptance S k (T.gadget f hf)
      (TableReduction.tableEnumeration T f hf) labeling]
    exact h _
  have hreal := (Rat.cast_le (K := ℝ)
    (p := GapSemantics.satisfactionRate
      (TableKeysAddressGame.outputInstance S k (T.gadget f hf)
        (TableReduction.tableEnumeration T f hf)) labeling)
    (q := (99 : ℚ) / 100)).2 hrate
  simpa [GapSemantics.satisfactionRate] using hreal

end

end UniqueGamesTheorem.Decoder.MatrixGap

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_Block
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F]

section CharacteristicTwo

variable [CharP F 2]

variable [Algebra (ZMod 2) F]

theorem mem_U_iff_exists (v : Vec F) (p : Vec F × Vec F) :
    p ∈ U v ↔ ∃ a ∈ line v, ∃ w ∈ hyperplane v, p = (a, Q a + w) := by
  constructor
  · intro hp
    refine ⟨p.1, hp.1, p.2 + Q p.1, hp.2, ?_⟩
    apply Prod.ext
    · rfl
    · change p.2 = Q p.1 + (p.2 + Q p.1)
      have h : Q p.1 + (p.2 + Q p.1) = p.2 + (Q p.1 + Q p.1) := by ac_rfl
      rw [h, vec_add_self, add_zero]
  · rintro ⟨a, ha, w, hw, rfl⟩
    exact pair_mem_U v a w ha hw

end CharacteristicTwo
end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockCounting
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact field-line count for the quadratic block's erasure probability. -/

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F]

variable [Finite F]

/-- Written over rationals, as needed for the finite rational noise law. -/
theorem reciprocal_card_FieldLine :
    (Nat.card (FieldLine F) : ℚ)⁻¹ =
      ((Nat.card F : ℚ) ^ 2 + Nat.card F + 1)⁻¹ := by
  rw [card_FieldLine]
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockNoise
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact nonlinear change count for a quadratic block

For every fixed input, a shear of the line/hyperplane parametrization makes
the output difference the hyperplane coordinate. This proves the uniform
change count before any recursion or random orientation is introduced.
-/

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

private theorem natCard_ne_zero {A : Type*} [Finite A] [Zero A] :
    Nat.card {x : A // x ≠ 0} = Nat.card A - 1 := by
  classical
  let := Fintype.ofFinite A
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem natCard_line (v : Vec F) (hv : v ≠ 0) : Nat.card (line v) = Nat.card F := by
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_line v hv, pow_one]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem natCard_hyperplane (v : Vec F) (hv : v ≠ 0) :
    Nat.card (hyperplane v) = Nat.card F ^ 2 := by
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_hyperplane v hv]

theorem natCard_U (v : Vec F) (hv : v ≠ 0) : Nat.card (U v) = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (blockParametrization v).toEquiv, Nat.card_prod]
  change Nat.card (line v) * Nat.card (hyperplane v) = _
  rw [natCard_line v hv, natCard_hyperplane v hv]
  ring

variable [Finite F]

/-- Exact numerator for the uniform nonzero-perturbation change probability.
Zero never changes the observable, so no exclusion correction is needed. -/
theorem natCard_block_changes (v : Vec F) (hv : v ≠ 0) (p : Vec F × Vec F) :
    Nat.card {u : U v // blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr (changedCoordinatesEquiv v p), Nat.card_prod, natCard_ne_zero]
  change Nat.card (line v) * (Nat.card (hyperplane v) - 1) = _
  rw [natCard_line v hv, natCard_hyperplane v hv]

/-- Exact denominator when the perturbation is conditioned to be nonzero. -/
theorem natCard_nonzero_U (v : Vec F) (hv : v ≠ 0) :
    Nat.card {u : U v // u ≠ 0} = Nat.card F ^ 3 - 1 := by
  rw [natCard_ne_zero, natCard_U v hv]

/-- The count ratio simplifies to the one-level survival factor `1-θ`. -/
theorem block_change_ratio (q : ℚ) (hq : 1 < q) :
    q * (q ^ 2 - 1) / (q ^ 3 - 1) = 1 - 1 / (q ^ 2 + q + 1) := by
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  have hq1 : q - 1 ≠ 0 := by linarith
  have hd : q ^ 2 + q + 1 ≠ 0 := by
    have hs := sq_nonneg q
    linarith
  have hc : q ^ 3 - 1 ≠ 0 := by
    have h : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by ring
    rw [h]
    exact mul_ne_zero hq1 hd
  field_simp [hc, hd]
  ring

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockNoiseProbabilityLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact rational expectation for the quadratic block's conditioned noise. -/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

theorem nonzeroBlockChangeProbability_eq_count (v : Vec F) (p : Vec F × Vec F) :
    nonzeroBlockChangeProbability v p =
      (Nat.card {u : U v //
        blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} : ℚ) /
      (Nat.card (NonzeroBlock v) : ℚ) := by
  classical
  have hcard :
      (Finset.univ.filter (fun u : NonzeroBlock v =>
        blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p)).card =
      Fintype.card {u : U v //
        blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (conditionedChangedEquiv v p)
  simp only [nonzeroBlockChangeProbability, Fintype.expect_eq_sum_div_card,
    Finset.sum_boole, hcard, Nat.card_eq_fintype_card]

/-- The one-level change probability is exactly `1-θ`, for every fixed input.
Here `θ = 1/(q²+q+1)` and `q` is the actual finite-field cardinality. -/
theorem nonzeroBlockChangeProbability_eq (v : Vec F) (hv : v ≠ 0)
    (p : Vec F × Vec F) :
    nonzeroBlockChangeProbability v p =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  rw [nonzeroBlockChangeProbability_eq_count, natCard_block_changes v hv p]
  change ((Nat.card F * (Nat.card F ^ 2 - 1) : ℕ) : ℚ) /
    (Nat.card {u : U v // u ≠ 0} : ℚ) = _
  rw [natCard_nonzero_U v hv]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqpos : 0 < Nat.card F := lt_trans Nat.zero_lt_one hq
  have hq2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow 2 _ hqpos
  have hq3 : 1 ≤ Nat.card F ^ 3 := Nat.one_le_pow 3 _ hqpos
  have hq' : (1 : ℚ) < Nat.card F := by exact_mod_cast hq
  simpa only [Nat.cast_mul, Nat.cast_sub hq2, Nat.cast_sub hq3,
    Nat.cast_pow, Nat.cast_one] using block_change_ratio (Nat.card F) hq'

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_OrientedBlockKernel
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open scoped BigOperators

namespace UniqueGamesTheorem.Gadget.OrientedBlockKernel

open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

variable [∀ A : FieldLine F, Fintype (BlockOrientation A)]

/-- For one fixed field line, random orientation sends a fixed nonzero
logical difference uniformly onto that line's nonzero block perturbations. -/
theorem mean_orientations_change (A : FieldLine F) (p : Vec F × Vec F)
    (d : Vec F) (hd : d ≠ 0) :
    (𝔼 J : BlockOrientation A, orientedBlockChange ⟨A, J⟩ p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  classical
  let : Finite (U (lineGenerator A) ≃ₗ[ZMod 2] U (lineGenerator A)) := DFunLike.finite _
  let := Fintype.ofFinite (U (lineGenerator A) ≃ₗ[ZMod 2] U (lineGenerator A))
  calc
    _ = nonzeroBlockChangeProbability (lineGenerator A) p := by
      unfold nonzeroBlockChangeProbability orientedBlockChange
      simp only [Fintype.expect_eq_sum_div_card]
      exact OrientationVectors.mean_iso_nonzero (chosenBlockOrientation A) d hd
        (fun u => if blockObservable (p + (u.val : Vec F × Vec F)) ≠
          blockObservable p then 1 else 0)
    _ = _ := nonzeroBlockChangeProbability_eq _ (lineGenerator_ne_zero A) p

variable [Fintype (FieldLine F)] [Fintype (Vec F ≃ₗ[ZMod 2] Vec F)]

/-- Equal orientation-fiber sizes make the pair-index average exactly an
independent uniform line followed by a uniform orientation of that line. -/
theorem mean_block_pairs (f : BlockOrientationIndex F → ℚ) :
    (𝔼 i : BlockOrientationIndex F, f i) =
      𝔼 A : FieldLine F, 𝔼 J : BlockOrientation A, f ⟨A, J⟩ := by
  classical
  calc
    _ = 𝔼 z : FieldLine F × (Vec F ≃ₗ[ZMod 2] Vec F),
        f ((blockOrientationIndexEquiv (F := F)).symm z) := by
      exact Fintype.expect_equiv (blockOrientationIndexEquiv (F := F)) _ _
        (fun i => by simp)
    _ = 𝔼 A : FieldLine F, 𝔼 a : Vec F ≃ₗ[ZMod 2] Vec F,
        f ⟨A, (blockOrientationEquiv A).symm a⟩ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      rfl
    _ = _ := by
      apply Finset.expect_congr rfl
      intro A _
      exact Fintype.expect_equiv (blockOrientationEquiv A).symm _ _ (fun _ => rfl)

/-- Pointwise in the initial aggregate: the actual oriented-child average
has the exact one-level nonlinear survival rate. -/
theorem mean_oriented_block_change (p : Vec F × Vec F) (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, orientedBlockChange i p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  classical
  have : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  rw [mean_block_pairs]
  simp_rw [mean_orientations_change _ p d hd]
  exact Fintype.expect_const _

/-- The averaged block kernel required by the parent-noise recurrence,
now proved for the concrete quadratic construction. -/
theorem mean_oriented_block_kernel (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, 𝔼 p : Vec F × Vec F,
      orientedBlockChange i p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  rw [Finset.expect_comm]
  simp_rw [mean_oriented_block_change _ d hd]
  exact Fintype.expect_const _

end UniqueGamesTheorem.Gadget.OrientedBlockKernel

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_Alignment
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Quadratic

open Module
open scoped BigOperators Matrix

noncomputable section

variable {R F V ι n E : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype ι] [Fintype n]

/-- Basis values of a linear lift give the coefficients of the alignment
column combination.  The identity holds for every lift, without selecting
one in advance of the parametrization. -/
theorem dot_lift_eq_alignment_mulVec (b : Basis ι R V)
    (point : E → V) (z : V → n → F) (g : V →ₗ[R] (n → F)) (e : E) :
    (∑ i, z (point e) i * g (point e) i) =
      (alignmentMatrix b point z *ᵥ (fun ij => g (b ij.2) ij.1)) e := by
  have hg : g (point e) = ∑ j, b.repr (point e) j • g (b j) := by
    calc
      g (point e) = g (∑ j, b.repr (point e) j • b j) :=
        congrArg g (b.sum_repr (point e)).symm
      _ = ∑ j, b.repr (point e) j • g (b j) := by simp only [map_sum, map_smul]
  rw [hg]
  simp only [Matrix.mulVec, dotProduct, alignmentMatrix,
    Finset.sum_apply, Algebra.smul_def, Pi.mul_apply,
    Pi.algebraMap_apply, Finset.mul_sum,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockSpanLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

/-- A coordinate-stable subspace containing the coordinates is the whole
function space when the coordinates separate points and exclude the zero
point. The proof constructs each point indicator by successively removing
the other points. -/
theorem eq_top_of_binary_coordinates
    {F X I : Type*} [Field F] [Fintype X]
    (c : I → X → F) (W : Submodule F (X → F))
    (hbinary : ∀ i x, c i x = 0 ∨ c i x = 1)
    (hseparate : ∀ x y, x ≠ y → ∃ i, c i x ≠ c i y)
    (hnonzero : ∀ x, ∃ i, c i x ≠ 0)
    (hcoordinate : ∀ i, c i ∈ W)
    (hstable : ∀ i f, f ∈ W → (fun x => c i x * f x) ∈ W) :
    W = ⊤ := by
  classical
  have hindicator : ∀ x : X, (fun y => if x = y then (1 : F) else 0) ∈ W := by
    intro x
    have hfilter : ∀ s : Finset X,
        ∃ f : X → F, f ∈ W ∧ f x = 1 ∧ ∀ y ∈ s, y ≠ x → f y = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          obtain ⟨i, hi⟩ := hnonzero x
          refine ⟨c i, hcoordinate i, (hbinary i x).resolve_left hi, ?_⟩
          simp
      | @insert y s hy ih =>
          obtain ⟨f, hf, hfx, hfzero⟩ := ih
          by_cases hyx : y = x
          · refine ⟨f, hf, hfx, ?_⟩
            intro z hz hzx
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact (hzx hyx).elim
            · exact hfzero z hz hzx
          · obtain ⟨i, hi⟩ := hseparate x y (Ne.symm hyx)
            rcases hbinary i x with hix | hix <;>
              rcases hbinary i y with hiy | hiy
            · exact (hi (hix.trans hiy.symm)).elim
            · refine ⟨fun z => f z - c i z * f z,
                W.sub_mem hf (hstable i f hf), ?_, ?_⟩
              · simp [hfx, hix]
              · intro z hz hzx
                rcases Finset.mem_insert.mp hz with rfl | hz
                · simp [hiy]
                · simp [hfzero z hz hzx]
            · refine ⟨fun z => c i z * f z, hstable i f hf, ?_, ?_⟩
              · simp [hfx, hix]
              · intro z hz hzx
                rcases Finset.mem_insert.mp hz with rfl | hz
                · simp [hiy]
                · simp [hfzero z hz hzx]
            · exact (hi (hix.trans hiy.symm)).elim
    obtain ⟨f, hf, hfx, hfzero⟩ := hfilter Finset.univ
    have heq : f = fun y => if x = y then (1 : F) else 0 := by
      funext y
      by_cases hxy : x = y
      · subst y
        simp [hfx]
      · simp [hxy, hfzero y (Finset.mem_univ y) (Ne.symm hxy)]
    rwa [← heq]
  apply top_unique
  intro f _
  rw [pi_eq_sum_univ f]
  exact W.sum_mem fun x _ => W.smul_mem (f x) (hindicator x)

theorem eq_top_of_cubic_le_of_le_quadratic
    {F X I : Type*} [Field F] [Fintype X]
    (c : I → X → F) (W : Submodule F (X → F))
    (hbinary : ∀ i x, c i x = 0 ∨ c i x = 1)
    (hseparate : ∀ x y, x ≠ y → ∃ i, c i x ≠ c i y)
    (hnonzero : ∀ x, ∃ i, c i x ≠ 0)
    (hcubic : cubicEvaluationSpan c ≤ W)
    (hquadratic : W ≤ quadraticEvaluationSpan c) : W = ⊤ := by
  apply eq_top_of_binary_coordinates c W hbinary hseparate hnonzero
  · intro i
    have hi : (fun x => c i x * c i x * c i x) ∈ cubicEvaluationSpan c :=
      Submodule.subset_span ⟨(i, i, i), rfl⟩
    have heq : (fun x => c i x * c i x * c i x) = c i := by
      funext x
      rcases hbinary i x with h | h <;> simp [h]
    rw [heq] at hi
    exact hcubic hi
  · intro k f hf
    have hf' : f ∈ Submodule.span F
        (Set.range fun ij : I × I => fun x => c ij.1 x * c ij.2 x) :=
      hquadratic hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨⟨i, j⟩, rfl⟩ := hf
        have h : (fun x => c k x * c i x * c j x) ∈ cubicEvaluationSpan c :=
          Submodule.subset_span ⟨(k, i, j), rfl⟩
        simpa only [mul_assoc] using hcubic h
    | zero =>
        have heq : (fun x => c k x * (0 : X → F) x) = (0 : X → F) := by
          funext x
          exact mul_zero _
        rw [heq]
        exact W.zero_mem
    | add f g hf hg ihf ihg =>
        have heq : (fun x => c k x * ((f + g) x)) =
            (fun x => c k x * f x) + (fun x => c k x * g x) := by
          funext x
          exact mul_add _ _ _
        rw [heq]
        exact W.add_mem ihf ihg
    | smul a f hf ih =>
        have heq : (fun x => c k x * ((a • f) x)) =
            a • (fun x => c k x * f x) := by
          funext x
          exact mul_left_comm _ _ _
        rw [heq]
        exact W.smul_mem a ih

/-- Every element of the binary field is either zero or one. -/
theorem binary_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

end UniqueGamesTheorem.Quadratic

end

section

/-! The low-dimension obstruction used by the all-lifts genericity proof. -/

namespace UniqueGamesTheorem.Quadratic

/-- A proper-dimensional subspace of the quadratic evaluation space misses
at least one cubic evaluation. This supplies a concrete coefficient vector
outside the alignment-column span. -/
theorem exists_cubic_not_mem_of_finrank_lt
    {F X I : Type*} [Field F] [Fintype X]
    (c : I → X → F) (W : Submodule F (X → F))
    (hbinary : ∀ i x, c i x = 0 ∨ c i x = 1)
    (hseparate : ∀ x y, x ≠ y → ∃ i, c i x ≠ c i y)
    (hnonzero : ∀ x, ∃ i, c i x ≠ 0)
    (hquadratic : W ≤ quadraticEvaluationSpan c)
    (hdim : Module.finrank F W < Fintype.card X) :
    ∃ i j k, (fun x => c i x * c j x * c k x) ∉ W := by
  classical
  by_contra h
  have hcubic : cubicEvaluationSpan c ≤ W := by
    apply Submodule.span_le.mpr
    rintro f ⟨⟨i, j, k⟩, rfl⟩
    by_contra hn
    exact h ⟨i, j, k, hn⟩
  have htop := eq_top_of_cubic_le_of_le_quadratic c W hbinary hseparate
    hnonzero hcubic hquadratic
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at hdim
  exact (lt_irrefl _) hdim

end UniqueGamesTheorem.Quadratic

end

section

/-!
A concrete mathematical family of finite binary fields of unbounded size.
The extension degree is chosen from numerical thresholds alone, before the
logical output dimension of the latent gadget is selected.
-/

namespace UniqueGamesTheorem.Quadratic

theorem card_binaryField (d : ℕ) (hd : 0 < d) :
    Nat.card (BinaryField d) = 2 ^ d :=
  GaloisField.card 2 d (Nat.ne_of_gt hd)

theorem finrank_binaryField (d : ℕ) (hd : 0 < d) :
    Module.finrank (ZMod 2) (BinaryField d) = d :=
  GaloisField.finrank 2 (Nat.ne_of_gt hd)

theorem finrank_binaryField_triple (d : ℕ) (hd : 0 < d) :
    Module.finrank (ZMod 2) (Fin 3 → BinaryField d) = 3 * d := by
  rw [← Module.finrank_mul_finrank (ZMod 2) (BinaryField d) (Fin 3 → BinaryField d),
    finrank_binaryField d hd, Module.finrank_fin_fun, mul_comm]

theorem fieldDegree_pos (N r : ℕ) : 0 < fieldDegree N r := by
  simp [fieldDegree]

theorem threshold_lt_two_pow_fieldDegree (N r : ℕ) : N < 2 ^ fieldDegree N r := by
  have h : N ≤ fieldDegree N r := by unfold fieldDegree; omega
  exact lt_of_le_of_lt h Nat.lt_two_pow_self

theorem rankThreshold_le_triple_fieldDegree (N r : ℕ) : r ≤ 3 * fieldDegree N r := by
  unfold fieldDegree
  omega

/-- Simultaneous cardinality and rank threshold attainment by the same field. -/
theorem chosen_binaryField_thresholds (N r : ℕ) :
    N < Nat.card (BinaryField (fieldDegree N r)) ∧
      r ≤ Module.finrank (ZMod 2) (Fin 3 → BinaryField (fieldDegree N r)) := by
  rw [card_binaryField _ (fieldDegree_pos N r),
    finrank_binaryField_triple _ (fieldDegree_pos N r)]
  exact ⟨threshold_lt_two_pow_fieldDegree N r, rankThreshold_le_triple_fieldDegree N r⟩

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Separation of polynomial parity classes

The genericity argument uses monomials with distinct squarefree
exponent vectors. Polynomial coefficients in the original variables become
polynomials in squares after adjoining their square roots. The lemmas below
prove the resulting coefficient separation directly, without assuming an
algebraic independence witness.
-/

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial
open scoped BigOperators

variable {σ ι R : Type*} [CommSemiring R]

/-- Two different squarefree shifts have disjoint expanded supports. -/
theorem coeff_expand_mul_monomial_of_ne
    (p : MvPolynomial σ R) (a b n : σ →₀ ℕ)
    (ha : SquarefreeExponent a) (hb : SquarefreeExponent b) (hab : a ≠ b) :
    (expand 2 p * monomial b 1).coeff (2 • n + a) = 0 := by
  classical
  rw [coeff_mul_monomial']
  split_ifs with hle
  · obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra h
      push Not at h
      exact hab (Finsupp.ext h)
    have hcoeff : (expand 2 p).coeff (2 • n + a - b) = 0 := by
      apply coeff_expand_of_not_dvd (i := k)
      intro hdiv
      obtain ⟨m, hm⟩ := hdiv
      have hle' := hle k
      have ha' := ha k
      have hb' := hb k
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul] at hm hle'
      omega
    simp [hcoeff]
  · rfl

/-- Within one parity class coefficient extraction recovers the coefficient
before expansion. -/
theorem coeff_expand_mul_monomial_self
    (p : MvPolynomial σ R) (a n : σ →₀ ℕ) :
    (expand 2 p * monomial a 1).coeff (2 • n + a) = p.coeff n := by
  rw [coeff_mul_monomial, coeff_expand_smul 2 (by decide), mul_one]

/-- Extraction from a finite sum isolates its unique parity class. -/
theorem coeff_sum_expand_mul_monomial [Fintype ι]
    (e : ι → σ →₀ ℕ) (he : ∀ i, SquarefreeExponent (e i))
    (hinj : Function.Injective e) (p : ι → MvPolynomial σ R)
    (i : ι) (n : σ →₀ ℕ) :
    (∑ j, expand 2 (p j) * monomial (e j) 1).coeff (2 • n + e i) =
      (p i).coeff n := by
  classical
  rw [coeff_sum]
  rw [Finset.sum_eq_single i]
  · exact coeff_expand_mul_monomial_self _ _ _
  · intro j _ hji
    exact coeff_expand_mul_monomial_of_ne _ _ _ _ (he i) (he j)
      (fun h => hji (hinj h).symm)
  · simp

/-- A polynomial dependence between distinct squarefree parity classes is
trivial, even when each coefficient is itself an arbitrary polynomial in the
squared variables. -/
theorem sum_expand_mul_monomial_eq_zero_iff [Fintype ι]
    (e : ι → σ →₀ ℕ) (he : ∀ i, SquarefreeExponent (e i))
    (hinj : Function.Injective e) (p : ι → MvPolynomial σ R) :
    (∑ i, expand 2 (p i) * monomial (e i) 1) = 0 ↔ ∀ i, p i = 0 := by
  constructor
  · intro h i
    ext n
    have hc := congrArg (fun q : MvPolynomial σ R => q.coeff (2 • n + e i)) h
    simpa only [coeff_sum_expand_mul_monomial e he hinj,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, MvPolynomial.coeff_zero] using hc
  · intro h
    simp [h]

theorem blockExponent_squarefree {κ J : Type*} [Finite κ] [Finite J]
    (v : κ → J) : SquarefreeExponent (blockExponent v) := by
  classical
  intro x
  simp only [blockExponent_apply]
  split_ifs <;> decide

theorem blockExponent_injective {κ J : Type*} [Finite κ] [Finite J] :
    Function.Injective (blockExponent (κ := κ) (J := J)) := by
  classical
  intro v w h
  funext i
  have hc := congrArg (fun e : (κ × J) →₀ ℕ => e (i, v i)) h
  by_contra hne
  simp [hne] at hc

theorem blockExponent_eq_sum {κ J : Type*} [Fintype κ] [Finite J]
    (v : κ → J) :
    blockExponent v = ∑ i, Finsupp.single (i, v i) 1 := by
  classical
  ext x
  rw [blockExponent_apply, Finsupp.finsetSum_apply]
  symm
  rw [Finset.sum_eq_single x.1]
  · simp [Finsupp.single_apply, Prod.ext_iff, eq_comm]
  · intro i _ hi
    have hix : (i, v i) ≠ x := fun h => hi (congrArg Prod.fst h)
    simp [hix]
  · simp

theorem monomial_blockExponent {κ J : Type*} [Fintype κ] [Finite J]
    (v : κ → J) :
    (monomial (blockExponent v) 1 : MvPolynomial (κ × J) R) =
      ∏ i, X (i, v i) := by
  rw [blockExponent_eq_sum, monomial_sum_one]
  rfl

/-- In particular the three-block monomials have independent polynomial
coefficients after squaring the variables. -/
theorem sum_expand_mul_blockMonomial_eq_zero_iff {J : Type*} [Fintype J]
    (p : (Fin 3 → J) → MvPolynomial (Fin 3 × J) R) :
    (∑ v, expand 2 (p v) * monomial (blockExponent v) 1) = 0 ↔
      ∀ v, p v = 0 :=
  sum_expand_mul_monomial_eq_zero_iff blockExponent blockExponent_squarefree
    blockExponent_injective p

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Polynomial parity obstruction

This supplies the algebraic obstruction step in the genericity proof.
Squaring a cleared dual row exposes its distinct squarefree parity classes.
No genericity or minor-existence conclusion is assumed here.
-/

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial
open scoped BigOperators
open scoped nonZeroDivisors

variable {σ : Type*}

/-- Every coefficient in the binary prime field is fixed by squaring. -/
theorem zmodTwo_sq (a : ZMod 2) : a ^ 2 = a := by
  classical
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl
  · exact zero_pow (by decide)
  · exact one_pow 2

theorem expand_two_eq_sq (p : MvPolynomial σ (ZMod 2)) : expand 2 p = p ^ 2 := by
  induction p using MvPolynomial.induction_on' with
  | monomial m a => simp only [expand_monomial, monomial_pow, zmodTwo_sq]
  | add p q hp hq => rw [map_add, CharTwo.add_sq, hp, hq]

/-- A separating linear functional written in coordinate form. -/
theorem exists_coordinate_separator {X K : Type*} [Field K] [Fintype X]
    (W : Submodule K (X → K)) (v : X → K) (hv : v ∉ W) :
    ∃ a : X → K, (∀ w ∈ W, ∑ x, a x * w x = 0) ∧
      (∑ x, a x * v x) ≠ 0 := by
  classical
  obtain ⟨f, hfv, hfW⟩ := W.exists_dual_map_eq_bot_of_notMem hv inferInstance
  let a : X → K := fun x => f (fun y => if x = y then 1 else 0)
  have hrepr (w : X → K) : f w = ∑ x, a x * w x := by
    rw [LinearMap.pi_apply_eq_sum_univ]
    apply Finset.sum_congr rfl
    intro x _
    exact mul_comm _ _
  refine ⟨a, ?_, ?_⟩
  · intro w hw
    have hmem : f w ∈ W.map f := ⟨w, hw, rfl⟩
    rw [hfW, Submodule.mem_bot, hrepr] at hmem
    exact hmem
  · rwa [← hrepr]

section Obstruction

variable {J X : Type*} [Fintype J] [Fintype X]

theorem universalLinearForm_prod (t : J → ZMod 2) :
    (∏ i, universalLinearForm t i) =
      ∑ v : Fin 3 → J, C (∏ i, t (v i)) * monomial (blockExponent v) 1 := by
  classical
  unfold universalLinearForm
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.prod_mul_distrib, ← map_prod, monomial_blockExponent]

theorem alignmentObstruction_parity_expansion (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2)) :
    alignmentObstruction t p = ∑ v : Fin 3 → J,
      cubicPairing t p v ^ 2 * monomial (blockExponent v) 1 := by
  classical
  unfold alignmentObstruction
  simp_rw [universalLinearForm_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  unfold cubicPairing
  rw [CharTwo.sum_sq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mul_pow, ← map_pow, zmodTwo_sq, mul_assoc]

theorem alignmentObstruction_ne_zero (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2))
    (v : Fin 3 → J) (hv : cubicPairing t p v ≠ 0) :
    alignmentObstruction t p ≠ 0 := by
  intro h
  rw [alignmentObstruction_parity_expansion] at h
  have hzero : ∀ w, cubicPairing t p w = 0 := by
    apply (sum_expand_mul_blockMonomial_eq_zero_iff _).mp
    simpa only [expand_two_eq_sq] using h
  exact hv (hzero v)

end Obstruction

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial
open scoped nonZeroDivisors

/-- A polynomial row annihilates all alignment columns and detects a cubic
evaluation. The row is constructed from a rational dual separator; there is
no assumed algebraic genericity certificate. -/
theorem exists_polynomial_alignment_annihilator
    {J X : Type*} [Fintype J] [Fintype X]
    (t : X → J → ZMod 2) (ht : Function.Injective t)
    (hnonzero : ∀ x, t x ≠ 0) (hcard : 3 * Fintype.card J < Fintype.card X) :
    ∃ p : X → MvPolynomial (Fin 3 × J) (ZMod 2),
      (∀ ij, ∑ x, p x * universalAlignmentColumn t ij x = 0) ∧
      ∃ v : Fin 3 → J, cubicPairing t p v ≠ 0 := by
  classical
  let P := MvPolynomial (Fin 3 × J) (ZMod 2)
  let K := FractionRing P
  let f : P →+* K := algebraMap P K
  let φ : ZMod 2 →+* K := f.comp C
  let c : J → X → K := fun j x => φ (t x j)
  let M : Matrix X (Fin 3 × J) K := fun x ij => f (universalAlignmentColumn t ij x)
  let W := LinearMap.range M.mulVecLin
  have hquadratic : W ≤ quadraticEvaluationSpan c := by
    change LinearMap.range M.mulVecLin ≤ _
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    have heq : M.col ij = ∑ j, f (MvPolynomial.X (ij.1, j)) •
        (fun x => c ij.2 x * c j x) := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change f (C (t x ij.2) * ∑ j, C (t x j) * MvPolynomial.X (ij.1, j)) =
        ∑ j, f (MvPolynomial.X (ij.1, j)) * (f (C (t x ij.2)) * f (C (t x j)))
      simp only [map_mul, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ac_rfl
    rw [heq]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(ij.2, j), rfl⟩
  have hbinary : ∀ j x, c j x = 0 ∨ c j x = 1 := by
    intro j x
    rcases binary_eq_zero_or_one (t x j) with h | h
    · left
      simp [c, h]
    · right
      simp [c, h]
  have hseparate : ∀ x y, x ≠ y → ∃ j, c j x ≠ c j y := by
    intro x y hxy
    have hfun : t x ≠ t y := fun h => hxy (ht h)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hfun
    exact ⟨j, fun h => hj (φ.injective h)⟩
  have hnz : ∀ x, ∃ j, c j x ≠ 0 := by
    intro x
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (hnonzero x)
    refine ⟨j, ?_⟩
    intro h
    exact hj (φ.injective (by simpa [c] using h))
  have hdim : Module.finrank K W < Fintype.card X := by
    have hle : Module.finrank K W ≤ 3 * Fintype.card J := by
      calc
        Module.finrank K W ≤ Module.finrank K ((Fin 3 × J) → K) :=
          LinearMap.finrank_range_le M.mulVecLin
        _ = 3 * Fintype.card J := by
          rw [Module.finrank_fintype_fun_eq_card]
          simp
    exact hle.trans_lt hcard
  obtain ⟨i, j, k, hijk⟩ := exists_cubic_not_mem_of_finrank_lt
    c W hbinary hseparate hnz hquadratic hdim
  let v : Fin 3 → J := ![i, j, k]
  have hcubic : (fun x => ∏ b : Fin 3, c (v b) x) ∉ W := by
    simpa [v, Fin.prod_univ_succ, mul_assoc] using hijk
  obtain ⟨a, ha, hav⟩ := exists_coordinate_separator W _ hcubic
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite P⁰ a
  choose p hp using hb
  have hp' (x : X) : f (p x) = f (b : P) * a x := by
    simpa only [Algebra.smul_def] using hp x
  have hbne : f (b : P) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
  refine ⟨p, ?_, v, ?_⟩
  · intro ij
    apply IsFractionRing.injective P K
    change f (∑ x, p x * universalAlignmentColumn t ij x) = f 0
    rw [map_sum, map_zero]
    simp only [map_mul, hp', mul_assoc]
    rw [← Finset.mul_sum]
    have hcol : M.col ij ∈ W := by
      change M.col ij ∈ LinearMap.range M.mulVecLin
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨ij, rfl⟩
    have hsum := ha (M.col ij) hcol
    change (∑ x, a x * f (universalAlignmentColumn t ij x)) = 0 at hsum
    rw [hsum, mul_zero]
  · have heq : f (cubicPairing t p v) =
        f (b : P) * ∑ x, a x * ∏ i : Fin 3, c (v i) x := by
      unfold cubicPairing
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp [hp', c, φ, map_prod, mul_assoc]
    intro hz
    have : f (b : P) * (∑ x, a x * ∏ i : Fin 3, c (v i) x) = 0 := by
      rw [← heq, hz, map_zero]
    exact (mul_ne_zero hbne hav) this

/-- Every specialization of the polynomial row obstructs every alignment
column combination simultaneously. -/
theorem alignmentObstruction_eval_eq_zero
    {J X F : Type*} [Fintype J] [Fintype X] [Field F] [CharP F 2]
    (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2))
    (hann : ∀ ij, ∑ x, p x * universalAlignmentColumn t ij x = 0)
    (ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F)
    (c : X → F) (a : (Fin 3 × J) → F)
    (hc : ∀ x, c x ^ 2 = ρ (∏ i, universalLinearForm (t x) i))
    (ha : ∀ x, c x = ∑ ij, ρ (universalAlignmentColumn t ij x) * a ij) :
    ρ (alignmentObstruction t p) = 0 := by
  classical
  have hann' (ij : Fin 3 × J) :
      (∑ x, ρ (p x) * ρ (universalAlignmentColumn t ij x)) = 0 := by
    have h := congrArg ρ (hann ij)
    simpa only [map_sum, map_mul, map_zero] using h
  have hpair : (∑ x, ρ (p x) * c x) = 0 := by
    simp_rw [ha, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro ij _
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, hann', zero_mul]
  calc
    ρ (alignmentObstruction t p) = ∑ x, ρ (p x) ^ 2 *
        ρ (∏ i, universalLinearForm (t x) i) := by
          simp only [alignmentObstruction, map_sum, map_mul, map_pow]
    _ = (∑ x, ρ (p x) * c x) ^ 2 := by
      rw [CharTwo.sum_sq]
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_pow, hc]
    _ = 0 := by rw [hpair, zero_pow (by decide)]

/-- The uniform algebraic obstruction exists for every set of more than
three times the binary dimension many distinct nonzero inputs. Its one
polynomial works for all lifts over every characteristic-two field. -/
theorem exists_nonzero_alignment_obstruction
    {J X : Type*} [Fintype J] [Fintype X]
    (t : X → J → ZMod 2) (ht : Function.Injective t)
    (hnonzero : ∀ x, t x ≠ 0) (hcard : 3 * Fintype.card J < Fintype.card X) :
    ∃ P : MvPolynomial (Fin 3 × J) (ZMod 2), P ≠ 0 ∧
      ∀ (F : Type*) [Field F] [CharP F 2]
        (ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F)
        (c : X → F) (a : (Fin 3 × J) → F),
        (∀ x, c x ^ 2 = ρ (∏ i, universalLinearForm (t x) i)) →
        (∀ x, c x = ∑ ij, ρ (universalAlignmentColumn t ij x) * a ij) →
        ρ P = 0 := by
  obtain ⟨p, hann, v, hv⟩ := exists_polynomial_alignment_annihilator t ht hnonzero hcard
  refine ⟨alignmentObstruction t p, alignmentObstruction_ne_zero t p v hv, ?_⟩
  intro F _ _ ρ c a hc ha
  exact alignmentObstruction_eval_eq_zero t p hann ρ c a hc ha

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_GenericSeparationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Polynomial obstructions to collapsed or proportional binary inputs

One linear polynomial detects each nonzero input. One quadratic polynomial
detects each pair of distinct nonzero binary inputs. The witnesses are proved
nonzero by explicit coordinate-selector evaluations. Together with the
alignment obstruction they yield a finite product whose zero set contains
every failure of genericity. An `O_r(1/q)` bound suffices here.
-/

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial

theorem exists_binary_coordinate_one {J : Type*} (t : J → ZMod 2) (ht : t ≠ 0) :
    ∃ j, t j = 1 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ht
  exact ⟨j, (binary_eq_zero_or_one (t j)).resolve_left hj⟩

/-- Distinct nonzero vectors over the binary field have a nonzero two-column
minor. Since the coefficient field is binary, the minor equals one. -/
theorem exists_binary_minor_one {J : Type*} (t u : J → ZMod 2)
    (ht : t ≠ 0) (hu : u ≠ 0) (htu : t ≠ u) :
    ∃ j k, t j * u k + t k * u j = 1 := by
  obtain ⟨j, hj⟩ := exists_binary_coordinate_one t ht
  by_cases huj : u j = 0
  · obtain ⟨k, hk⟩ := exists_binary_coordinate_one u hu
    exact ⟨j, k, by simp [hj, huj, hk]⟩
  · have huj' : u j = 1 := (binary_eq_zero_or_one (u j)).resolve_left huj
    obtain ⟨k, hk⟩ := Function.ne_iff.mp htu
    refine ⟨j, k, ?_⟩
    rcases binary_eq_zero_or_one (t k) with htk | htk <;>
      rcases binary_eq_zero_or_one (u k) with huk | huk
    · exact (hk (htk.trans huk.symm)).elim
    · simp [hj, huj', htk, huk]
    · simp [hj, huj', htk, huk]
    · exact (hk (htk.trans huk.symm)).elim

section Polynomial

variable {J : Type*} [Fintype J]

theorem eval_universalLinearForm_selector_zero (t : J → ZMod 2) (j k : J) :
    eval (selectorAssignment j k) (universalLinearForm t 0) = t j := by
  classical
  simp [universalLinearForm, selectorAssignment]

theorem eval_universalLinearForm_selector_one (t : J → ZMod 2) (j k : J) :
    eval (selectorAssignment j k) (universalLinearForm t 1) = t k := by
  classical
  simp [universalLinearForm, selectorAssignment]

theorem universalLinearForm_zero_ne_zero (t : J → ZMod 2) (ht : t ≠ 0) :
    universalLinearForm t 0 ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_binary_coordinate_one t ht
  intro h
  have hc := congrArg (eval (selectorAssignment j j)) h
  rw [eval_universalLinearForm_selector_zero, map_zero, hj] at hc
  exact one_ne_zero hc

theorem universalPairMinor_ne_zero (t u : J → ZMod 2)
    (ht : t ≠ 0) (hu : u ≠ 0) (htu : t ≠ u) :
    universalPairMinor t u ≠ 0 := by
  obtain ⟨j, k, hjk⟩ := exists_binary_minor_one t u ht hu htu
  intro h
  have hc := congrArg (eval (selectorAssignment j k)) h
  simp only [universalPairMinor, map_add, map_mul,
    eval_universalLinearForm_selector_zero, eval_universalLinearForm_selector_one,
    map_zero] at hc
  rw [hjk] at hc
  exact one_ne_zero hc

/-- Proportional specialized image vectors force the fixed pair minor to
vanish, for every value of the proportionality scalar. -/
theorem universalPairMinor_eq_zero_of_proportional
    {F : Type*} [Field F] [CharP F 2]
    (t u : J → ZMod 2)
    (ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F) (a : F)
    (h : ∀ i, ρ (universalLinearForm t i) = a * ρ (universalLinearForm u i)) :
    ρ (universalPairMinor t u) = 0 := by
  simp only [universalPairMinor, map_add, map_mul, h]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (CharTwo.add_self_eq_zero
      (a * ρ (universalLinearForm u 0) * ρ (universalLinearForm u 1)))

end Polynomial

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Finite-field polynomial exceptional events

The nonzero polynomial obstruction for each fixed input set gives a uniform
bound over all linear lifts.  Its coefficients lie in the binary prime field,
so its degree is fixed before the extension field is chosen.  The theorems
below keep this order explicit and combine finitely many obstructions without
any union over maps.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Fintype F]

omit [Field F] in
theorem assignmentProbability_mono {n : ℕ}
    {event event' : (Fin n → F) → Prop} (h : ∀ x, event x → event' x) :
    assignmentProbability event ≤ assignmentProbability event' := by
  classical
  apply div_le_div_of_nonneg_right _ zero_le
  exact_mod_cast Finset.card_le_card
    (show Finset.univ.filter event ⊆ Finset.univ.filter event' from by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_filter.mp hx).2⟩)

/-- The checked Schwartz-Zippel theorem on the whole finite field. -/
theorem assignmentProbability_eval_zero_le {n : ℕ}
    (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) :
    assignmentProbability (fun x => MvPolynomial.eval x p = 0) ≤
      (p.totalDegree : ℚ≥0) / Fintype.card F := by
  classical
  simpa [assignmentProbability] using
    MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset F)

omit [Fintype F] in
/-- Injective coefficient extension preserves the total degree exactly. -/
theorem totalDegree_map_eq_of_injective {σ : Type*}
    (φ : K →+* F) (hφ : Function.Injective φ) (p : MvPolynomial σ K) :
    (MvPolynomial.map φ p).totalDegree = p.totalDegree := by
  classical
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective p hφ]

/-- A prime-field polynomial gives the same fixed numerator in every finite
extension field.  Only the denominator grows with the field size. -/
theorem assignmentProbability_eval₂_zero_le {n : ℕ}
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    assignmentProbability (fun x => MvPolynomial.eval₂ φ x p = 0) ≤
      (p.totalDegree : ℚ≥0) / Fintype.card F := by
  have hp' : MvPolynomial.map φ p ≠ 0 := by
    intro hz
    apply hp
    apply MvPolynomial.map_injective φ hφ
    simpa using hz
  have h := assignmentProbability_eval_zero_le (MvPolynomial.map φ p) hp'
  simpa only [← MvPolynomial.eval₂_eq_eval_map,
    totalDegree_map_eq_of_injective φ hφ] using h

/-- An exceptional event contained in a polynomial zero set satisfies the
same bound, including events expressed by existence of an arbitrary lift. -/
theorem assignmentProbability_le_of_polynomial {n : ℕ}
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0)
    (event : (Fin n → F) → Prop)
    (hvanish : ∀ x, event x → MvPolynomial.eval₂ φ x p = 0) :
    assignmentProbability event ≤ (p.totalDegree : ℚ≥0) / Fintype.card F :=
  (assignmentProbability_mono hvanish).trans
    (assignmentProbability_eval₂_zero_le φ hφ p hp)

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Polynomial exceptional events on arbitrary finite variable sets

Reindexing the variable set transports both the polynomial and the uniform
assignment space. Thus the checked finite-field zero bound applies directly
to the three-by-r variables in the genericity proof, without changing the
degree or taking a union over possible linear lifts.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

variable {σ τ K F : Type*} [Field K] [Field F] [Fintype F]

omit [Field F] in
theorem finiteAssignmentProbability_reindex [Fintype σ] {n : ℕ}
    (e : σ ≃ Fin n) (event : (σ → F) → Prop) :
    finiteAssignmentProbability event =
      assignmentProbability (fun y : Fin n → F => event (fun s => y (e s))) := by
  classical
  have hcard : Fintype.card σ = n := by simpa using Fintype.card_congr e
  have hevent (x : σ → F) :
      event x ↔ event (fun s => reindexAssignments e x (e s)) := by
    simp [reindexAssignments]
  have hsub := Fintype.card_congr ((reindexAssignments (F := F) e).subtypeEquiv
    (p := event) (q := fun y : Fin n → F => event (fun s => y (e s))) hevent)
  have hfilter : (Finset.univ.filter event).card =
      (Finset.univ.filter (fun y : Fin n → F => event (fun s => y (e s)))).card := by
    simpa only [Fintype.card_subtype] using hsub
  simp only [finiteAssignmentProbability, assignmentProbability, hfilter, hcard]

/-- A bad event contained in a fixed nonzero polynomial's zero set has
probability at most its total degree divided by the field size. -/
theorem finiteAssignmentProbability_le_of_polynomial [Fintype σ]
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial σ K) (hp : p ≠ 0)
    (event : (σ → F) → Prop)
    (hvanish : ∀ x, event x → MvPolynomial.eval₂ φ x p = 0) :
    finiteAssignmentProbability event ≤ (p.totalDegree : ℚ≥0) / Fintype.card F := by
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let p' := MvPolynomial.renameEquiv K e p
  have hp' : p' ≠ 0 := by
    intro h
    apply hp
    apply (MvPolynomial.renameEquiv K e).injective
    simpa only [map_zero] using h
  rw [finiteAssignmentProbability_reindex e event]
  have hbound := assignmentProbability_le_of_polynomial φ hφ p' hp'
    (fun y => event (fun s => y (e s))) (by
      intro y hy
      change MvPolynomial.eval₂ φ y (MvPolynomial.rename e p) = 0
      rw [MvPolynomial.eval₂_rename]
      exact hvanish (fun s => y (e s)) hy)
  simpa only [p', MvPolynomial.totalDegree_renameEquiv] using hbound

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Rank-loss accounting for quadratic blocks

A nonzero kernel character determines the field line of a lossy block.  On
a generic space there is at most one such character on each field line, so
the rank drops by at most one.  Counting the possible determining characters
also bounds the number of lossy lines.  These are deterministic statements;
the random orientation may be selected only after this data is fixed.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {R V W I : Type*} [Field R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- A vector space with at most one nonzero vector has dimension at most one.
The statement is deliberately independent of any characteristic assumption. -/
theorem finrank_le_one_of_nonzero_unique
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → v = w) :
    Module.finrank R V ≤ 1 := by
  classical
  by_cases hex : ∃ v : V, v ≠ 0
  · obtain ⟨v, hv⟩ := hex
    apply finrank_le_one v
    intro w
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw]⟩
    · exact ⟨1, by simpa using h v w hv hw⟩
  · apply finrank_le_one (0 : V)
    intro w
    have hw : w = 0 := by
      by_contra hw
      exact hex ⟨w, hw⟩
    exact ⟨0, by simp [hw]⟩

/-- Nonproportionality of a generic character space makes every child kernel
at most one-dimensional once the field-line kernel criterion is applied. -/
theorem finrank_ker_le_one_of_nonzero_unique (f : V →ₗ[R] W)
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → f v = 0 → f w = 0 → v = w) :
    Module.finrank R f.ker ≤ 1 := by
  apply finrank_le_one_of_nonzero_unique
  intro v w hv hw
  apply Subtype.ext
  apply h v w
  · intro hv0
    apply hv
    exact Subtype.ext hv0
  · intro hw0
    apply hw
    exact Subtype.ext hw0
  · exact v.property
  · exact w.property

variable [Fintype V] [Fintype I] [DecidableEq I]

theorem lossIndices_subset_image (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i) :
    lossIndices f ⊆ (alignedCharacters aligned).image lineOf := by
  classical
  intro i hi
  obtain ⟨v, hv, hfv⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨halign, hline⟩ := hkernel i v hv hfv
  apply Finset.mem_image.mpr
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, halign⟩, hline⟩

/-- The cardinality bound does not union over lifts or orientations. -/
theorem card_lossIndices_le_card_aligned (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i) :
    (lossIndices f).card ≤ (alignedCharacters aligned).card := by
  classical
  exact (Finset.card_le_card (lossIndices_subset_image f aligned lineOf hkernel)).trans
    (Finset.card_image_le (s := alignedCharacters aligned) (f := lineOf))

theorem card_lossIndices_le (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I) (r : ℕ)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i)
    (hgeneric : (alignedCharacters aligned).card ≤ 3 * r) :
    (lossIndices f).card ≤ 3 * r :=
  (card_lossIndices_le_card_aligned f aligned lineOf hkernel).trans hgeneric

theorem card_lossIndices_le_nonzero (f : I → V →ₗ[R] W)
    (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → lineOf v = i) :
    (lossIndices f).card ≤ Fintype.card V - 1 := by
  classical
  have h := card_lossIndices_le_card_aligned f (fun _ => True) lineOf
    (fun i v hv hfv => ⟨trivial, hkernel i v hv hfv⟩)
  simpa [alignedCharacters, Finset.filter_ne'] using h

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Passing genericity from a parametrization to its actual image

An injective binary-linear parametrization identifies its domain with the
image subspace. The universal quantifier over linear lifts is transported
by composition, and alignment-event cardinalities agree exactly.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

variable {F V : Type*} [Field F] [Fintype F] [CharP F 2]
variable [Algebra (ZMod 2) F] [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- The actual range of an injective parametrization is generic when its
nonproportionality and all-lifts alignment bounds hold on the domain. -/
theorem isGeneric_range_of_injective
    (z : V →ₗ[ZMod 2] (Fin 3 → F)) (hz : Function.Injective z)
    (hseparate : ∀ v w : V, v ≠ 0 → w ≠ 0 →
      (∃ t : F, z v = t • z w) → v = w)
    (halign : ∀ g : V →ₗ[ZMod 2] (Fin 3 → F),
      (alignmentEvent z g (fun v => alignmentRightHandSide (z v))).card ≤
        3 * Module.finrank (ZMod 2) V) :
    IsGeneric (LinearMap.range z) := by
  classical
  let : Fintype (LinearMap.range z) := Subtype.fintype (Membership.mem (LinearMap.range z))
  let e : V ≃ₗ[ZMod 2] LinearMap.range z := LinearEquiv.ofInjective z hz
  have he (v : V) : ((e v : LinearMap.range z) : Fin 3 → F) = z v := rfl
  have hes (s : LinearMap.range z) : z (e.symm s) = (s : Fin 3 → F) :=
    LinearEquiv.ofInjective_symm_apply z s
  have hzero (v : V) : e v ≠ 0 ↔ v ≠ 0 := by
    constructor
    · intro h hv
      apply h
      rw [hv, map_zero]
    · intro h hv
      apply h
      apply e.injective
      simpa only [map_zero] using hv
  constructor
  · intro s t hs ht hprop
    have hs' : e.symm s ≠ 0 := by
      intro h
      apply hs
      have hh := congrArg e h
      simpa only [e.apply_symm_apply, map_zero] using hh
    have ht' : e.symm t ≠ 0 := by
      intro h
      apply ht
      have hh := congrArg e h
      simpa only [e.apply_symm_apply, map_zero] using hh
    have hinput : e.symm s = e.symm t := by
      apply hseparate _ _ hs' ht'
      simpa only [hes] using hprop
    exact e.symm.injective hinput
  · intro g
    have hevent (v : V) :
        v ∈ alignmentEvent z (g.comp e.toLinearMap)
          (fun v => alignmentRightHandSide (z v)) ↔
        e v ∈ alignmentEvent (fun s : LinearMap.range z => (s : Fin 3 → F)) g
          (fun s : LinearMap.range z => alignmentRightHandSide (s : Fin 3 → F)) := by
      simp only [alignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and,
        LinearMap.comp_apply, LinearEquiv.coe_coe, he, hzero]
    have hcard :
        (alignmentEvent z (g.comp e.toLinearMap)
          (fun v => alignmentRightHandSide (z v))).card =
        (alignmentEvent (fun s : LinearMap.range z => (s : Fin 3 → F)) g
          (fun s : LinearMap.range z => alignmentRightHandSide (s : Fin 3 → F))).card := by
      apply Finset.card_bij (fun v _ => e v)
      · intro v hv
        exact (hevent v).mp hv
      · intro v hv w hw h
        exact e.injective h
      · intro s hs
        refine ⟨e.symm s, (hevent (e.symm s)).mpr ?_, e.apply_symm_apply s⟩
        simpa only [e.apply_symm_apply] using hs
    calc
      _ = (alignmentEvent z (g.comp e.toLinearMap)
          (fun v => alignmentRightHandSide (z v))).card := hcard.symm
      _ ≤ 3 * Module.finrank (ZMod 2) V := halign _
      _ = 3 * Module.finrank (ZMod 2) (LinearMap.range z) :=
        congrArg (fun d : ℕ => 3 * d) e.finrank_eq

end

end UniqueGamesTheorem.Quadratic

end

section

/-! The actual random binary-linear parametrization used in the genericity proof. -/

namespace UniqueGamesTheorem.Quadratic

open Module
open scoped BigOperators

noncomputable section

variable {F J : Type*} [Field F] [Algebra (ZMod 2) F] [Fintype J]

theorem parameterMap_apply (x : (Fin 3 × J) → F) (t : J → ZMod 2) (i : Fin 3) :
    parameterMap x t i = ∑ j, algebraMap (ZMod 2) F (t j) * x (i, j) := by
  classical
  simp [parameterMap, Basis.constr_apply_fintype, Algebra.smul_def]

/-- Evaluation of the universal polynomial is the actual linear map. -/
theorem eval_universalLinearForm (x : (Fin 3 × J) → F) (t : J → ZMod 2) (i : Fin 3) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm t i) =
      parameterMap x t i := by
  rw [parameterMap_apply]
  simp [universalLinearForm]

/-- All linear lifts have the prescribed universal alignment columns, with
their arbitrary values on the binary basis as column coefficients. -/
theorem dot_parameter_lift (x : (Fin 3 × J) → F)
    (g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) (t : J → ZMod 2) :
    (∑ i, parameterMap x t i * g t i) =
      ∑ ij : Fin 3 × J,
        MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x
          (universalAlignmentColumn (fun t : J → ZMod 2 => t) ij t) *
          g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1 := by
  have h := dot_lift_eq_alignment_mulVec (Pi.basisFun (ZMod 2) J)
    (fun t : J → ZMod 2 => t) (parameterMap x) g t
  simpa [Matrix.mulVec, dotProduct, alignmentMatrix, Pi.basisFun_repr,
    universalAlignmentColumn, eval_universalLinearForm] using h

variable [Fintype F] [CharP F 2]

/-- The unique square-root value satisfies the universal cubic equation. -/
theorem alignmentRightHandSide_sq (x : (Fin 3 × J) → F) (t : J → ZMod 2) :
    alignmentRightHandSide (parameterMap x t) ^ 2 =
      MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x
        (∏ i : Fin 3, universalLinearForm t i) := by
  simp [alignmentRightHandSide, Fin.prod_univ_succ, eval_universalLinearForm, mul_assoc]

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_AlignmentCertificateLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# One polynomial controls all binary linear lifts

For fixed binary dimension, multiply the nonzero obstructions for the finitely
many sets of `3r + 1` nonzero inputs.  A nonvanishing specialization then obeys
the alignment bound simultaneously for every binary linear map.  The resulting
polynomial and its degree are chosen before the extension field.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

/-- An unconditional polynomial exceptional-set certificate for the complete
all-lifts alignment condition.  There is no quantified bound on the maps `g`
outside the conclusion, and no choice of extension field enters `P`. -/
theorem exists_all_lifts_alignment_polynomial (J : Type*) [Fintype J] [DecidableEq J] :
    ∃ P : MvPolynomial (Fin 3 × J) (ZMod 2), P ≠ 0 ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
        (x : (Fin 3 × J) → F),
        MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x P ≠ 0 →
        ∀ g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F),
          (alignmentEvent (R := ZMod 2) (parameterMap x) g
            (fun t => alignmentRightHandSide (parameterMap x t))).card ≤
              3 * Fintype.card J := by
  classical
  let V := J → ZMod 2
  let Esets := {E : Finset V // (0 : V) ∉ E ∧ E.card = 3 * Fintype.card J + 1}
  have hex (E : Esets) := exists_nonzero_alignment_obstruction
    (fun t : E.val => (t : V)) Subtype.val_injective
    (fun t : E.val => by
      intro hz
      apply E.property.1
      simpa only [hz] using t.property)
    (show 3 * Fintype.card J < Fintype.card E.val by
      simpa only [Fintype.card_coe, E.property.2] using
        Nat.lt_succ_self (3 * Fintype.card J))
  choose p hp hvanish using hex
  let P : MvPolynomial (Fin 3 × J) (ZMod 2) := ∏ E : Esets, p E
  refine ⟨P, Finset.prod_ne_zero_iff.mpr (fun E _ => hp E), ?_⟩
  intro F _ _ _ _ x hP g
  by_contra hbad
  have hlarge : 3 * Fintype.card J + 1 ≤
      (alignmentEvent (R := ZMod 2) (parameterMap x) g
        (fun t => alignmentRightHandSide (parameterMap x t))).card := by omega
  obtain ⟨E, hsub, hcard⟩ := Finset.exists_subset_card_eq hlarge
  have hzero : (0 : V) ∉ E := by
    intro hz
    have hmem := hsub hz
    simp only [alignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.1 rfl
  let E' : Esets := ⟨E, hzero, hcard⟩
  let ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F :=
    MvPolynomial.eval₂Hom (algebraMap (ZMod 2) F) x
  let c : E → F := fun t => alignmentRightHandSide (parameterMap x (t : V))
  let a : (Fin 3 × J) → F :=
    fun ij => g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1
  have hc (t : E) :
      c t ^ 2 = ρ (∏ i : Fin 3, universalLinearForm (t : V) i) := by
    exact alignmentRightHandSide_sq x t
  have ha (t : E) : c t = ∑ ij, ρ
      (universalAlignmentColumn (fun t : E => (t : V)) ij t) * a ij := by
    have hmem := hsub t.property
    simp only [alignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have ht := hmem.2
    calc
      c t = ∑ i, parameterMap x (t : V) i * g (t : V) i := ht.symm
      _ = _ := dot_parameter_lift x g t
  have hz : ρ (p E') = 0 := hvanish E' F ρ c a hc ha
  apply hP
  change ρ P = 0
  simp only [P, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ E') hz

end

end UniqueGamesTheorem.Quadratic

end

section

/-! Exact correspondence between uniform field entries and all binary-linear maps. -/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F J : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Fintype J]

omit [CharP F 2] in
theorem parameterMap_event_card
    (event : ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) → Prop) :
    Nat.card {x : (Fin 3 × J) → F // event (parameterMap x)} =
      Nat.card {g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) // event g} := by
  exact Nat.card_congr ((parameterMapEquiv (F := F) (J := J)).subtypeEquiv
    (p := fun x => event (parameterMap x)) (q := event) (fun _ => Iff.rfl))

variable [Fintype F]

omit [CharP F 2] in
/-- The uniform probability on field entries is literally the uniform
probability on all linear maps.  This is the denominator used before
conditioning on injectivity in `UniformSubspaces.bad_subspace_bound`. -/
theorem parameterMap_event_probability
    (event : ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) → Prop) :
    (finiteAssignmentProbability (fun x => event (parameterMap x)) : ℚ) =
      (Nat.card {g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) // event g} : ℚ) /
        Nat.card ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) := by
  classical
  have hall := Nat.card_congr (parameterMapEquiv (F := F) (J := J))
  have hevent := parameterMap_event_card event
  rw [← hevent, ← hall]
  simp [finiteAssignmentProbability, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext assignment
  simp

end

end UniqueGamesTheorem.Quadratic

end

section

/-! A single finite polynomial certifies injectivity and pair separation of
the actual binary-linear parametrization. -/

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial
open scoped BigOperators

noncomputable section

variable (J : Type*) [Fintype J]

theorem separationPolynomial_ne_zero : separationPolynomial J ≠ 0 := by
  classical
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    exact universalLinearForm_zero_ne_zero t
      (Finset.mem_erase.mp ht).1
  · apply Finset.prod_ne_zero_iff.mpr
    intro tu htu
    have h := (Finset.mem_filter.mp htu).2
    exact universalPairMinor_ne_zero tu.1 tu.2 h.1 h.2.1 h.2.2

variable {J}

/-- Outside the zero set of the fixed separation polynomial, the actual
parametrization is injective and no two distinct nonzero inputs have
proportional images. The same polynomial works over every characteristic-two
field. -/
theorem parameterMap_separated_of_eval_ne_zero
    {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    (x : (Fin 3 × J) → F)
    (hx : eval₂ (algebraMap (ZMod 2) F) x (separationPolynomial J) ≠ 0) :
    Function.Injective (parameterMap x) ∧
      ∀ t u : J → ZMod 2, t ≠ 0 → u ≠ 0 →
        (∃ a : F, parameterMap x t = a • parameterMap x u) → t = u := by
  classical
  let ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F :=
    eval₂Hom (algebraMap (ZMod 2) F) x
  have hprod :
      (∏ t ∈ nonzeroBinaryInputs J, ρ (universalLinearForm t 0)) *
        (∏ tu ∈ distinctNonzeroBinaryPairs J, ρ (universalPairMinor tu.1 tu.2)) ≠ 0 := by
    change ρ (separationPolynomial J) ≠ 0 at hx
    simpa only [separationPolynomial, map_mul, map_prod] using hx
  have hlinear := (mul_ne_zero_iff.mp hprod).1
  have hminor := (mul_ne_zero_iff.mp hprod).2
  have hnonzero (t : J → ZMod 2) (ht : t ≠ 0) : parameterMap x t 0 ≠ 0 := by
    have hmem : t ∈ nonzeroBinaryInputs J := by
      simp [nonzeroBinaryInputs, ht]
    have h := Finset.prod_ne_zero_iff.mp hlinear t hmem
    change eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm t 0) ≠ 0 at h
    rwa [eval_universalLinearForm] at h
  constructor
  · intro t u htu
    by_contra hne
    have hz : parameterMap x (t - u) = 0 := by
      rw [map_sub, htu, sub_self]
    exact hnonzero (t - u) (sub_ne_zero.mpr hne) (congrFun hz 0)
  · intro t u ht hu hprop
    by_contra hne
    have hmem : (t, u) ∈ distinctNonzeroBinaryPairs J := by
      simp [distinctNonzeroBinaryPairs, ht, hu, hne]
    have hnz := Finset.prod_ne_zero_iff.mp hminor (t, u) hmem
    obtain ⟨a, ha⟩ := hprop
    apply hnz
    apply universalPairMinor_eq_zero_of_proportional t u ρ a
    intro i
    change eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm t i) =
      a * eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm u i)
    rw [eval_universalLinearForm, eval_universalLinearForm]
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun ha i

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# A fixed polynomial certifies genuine all-lifts generic subspaces

The certificate is constructed from binary input sets and is independent of
the extension field.  It combines injectivity, pairwise nonproportionality,
and the simultaneous alignment bound, then transports the latter to the
actual image subspace.  The finite-field exceptional probability tends to
zero with field size using a fixed finite numerator.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

theorem exists_genericity_polynomial (J : Type*) [Fintype J] :
    ∃ P : MvPolynomial (Fin 3 × J) (ZMod 2), P ≠ 0 ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
        (x : (Fin 3 × J) → F),
        MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x P ≠ 0 →
        Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range := by
  classical
  obtain ⟨A, hA, halign⟩ := exists_all_lifts_alignment_polynomial J
  refine ⟨separationPolynomial J * A, mul_ne_zero (separationPolynomial_ne_zero J) hA, ?_⟩
  intro F _ _ _ _ x hP
  rw [MvPolynomial.eval₂_mul] at hP
  have hparts := mul_ne_zero_iff.mp hP
  have hsep := parameterMap_separated_of_eval_ne_zero x hparts.1
  refine ⟨hsep.1, isGeneric_range_of_injective (parameterMap x) hsep.1 hsep.2 ?_⟩
  intro g
  simpa only [Module.finrank_fintype_fun_eq_card] using halign F x hparts.2 g

/-- The total exceptional probability for random coordinate entries is
`O_r(1 / |F|)`, with a positive integer numerator fixed before `F` is chosen.
Both noninjectivity and failure of the all-lifts image property are counted. -/
theorem exists_genericity_error_numerator (J : Type*) [Fintype J] :
    ∃ D : ℕ, 0 < D ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F],
        finiteAssignmentProbability (fun x : (Fin 3 × J) → F =>
          ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range)) ≤
            (D : ℚ≥0) / Fintype.card F := by
  classical
  obtain ⟨P, hP, hgood⟩ := exists_genericity_polynomial J
  refine ⟨P.totalDegree + 1, Nat.succ_pos _, ?_⟩
  intro F _ _ _ _
  have h := finiteAssignmentProbability_le_of_polynomial
    (algebraMap (ZMod 2) F) (algebraMap (ZMod 2) F).injective P hP
    (fun x : (Fin 3 × J) → F =>
      ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range))
    (by
      intro x hx
      by_contra hne
      exact hx (hgood F x hne))
  apply h.trans
  apply div_le_div_of_nonneg_right _ zero_le
  exact_mod_cast Nat.le_succ P.totalDegree

end

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2] in
theorem trace_square (x : F) : traceBinary (x ^ 2) = traceBinary x := by
  simpa only [traceBinary, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    ZMod.card] using
    Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) x

/-- Moving a square from the first factor through the trace. -/
theorem trace_square_mul (t c : F) :
    traceBinary (t ^ 2 * c) = traceBinary (t * squareRoot c) := by
  calc
    traceBinary (t ^ 2 * c) = traceBinary ((t * squareRoot c) ^ 2) := by
      rw [mul_pow, squareRoot_sq]
    _ = traceBinary (t * squareRoot c) := trace_square _

theorem trace_quadratic_vanish_iff (a c : F) :
    (∀ t : F, traceBinary (t * a + t ^ 2 * c) = 0) ↔ a = squareRoot c := by
  have heq (t : F) :
      traceBinary (t * a + t ^ 2 * c) = traceBinary (t * (a + squareRoot c)) := by
    rw [map_add, trace_square_mul, mul_add, map_add]
  simp_rw [heq]
  rw [trace_mul_vanish_iff, add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockTrace
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The binary trace annihilator of a quadratic-block hyperplane

The trace annihilator of the field hyperplane perpendicular to a nonzero
vector is exactly its field line.  Scaling test vectors first upgrades binary
trace orthogonality to field-valued orthogonality; explicit coordinate test
vectors then identify the annihilator.  No earlier gadget result is used.
-/

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F]

private theorem dot_sub_right (v y z : Vec F) :
    dot v (y - z) = dot v y - dot v z := by
  simp [dot]
  ring

private theorem dot_single (v : Vec F) (i : Fin 3) (a : F) :
    dot v (Pi.single i a) = v i * a := by
  fin_cases i <;> simp [dot]

/-- The field-valued annihilator of a nonzero vector's perpendicular
hyperplane is the line generated by that vector. -/
theorem annihilator_hyperplane_iff_mem_line {v z : Vec F} (hv : v ≠ 0) :
    (∀ y ∈ hyperplane v, dot z y = 0) ↔ z ∈ line v := by
  constructor
  · intro hz
    have hv' : ∃ i : Fin 3, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    obtain ⟨i, hi⟩ := hv'
    apply (mem_line_iff v z).mpr
    refine ⟨z i / v i, ?_⟩
    ext j
    have hy : Pi.single j (1 : F) - (v j / v i) • Pi.single i (1 : F) ∈
        hyperplane v := by
      rw [mem_hyperplane, dot_sub_right, dot_smul_right, dot_single, dot_single]
      simp [div_mul_cancel₀ _ hi]
    have hzero := hz _ hy
    rw [dot_sub_right, dot_smul_right, dot_single, dot_single,
      mul_one, mul_one, sub_eq_zero] at hzero
    change (z i / v i) * v j = z j
    rw [hzero]
    simp only [div_eq_mul_inv]
    ring
  · intro hz y hy
    obtain ⟨t, rfl⟩ := (mem_line_iff v z).mp hz
    rw [dot_smul_left, (mem_hyperplane v y).mp hy, mul_zero]

variable [Finite F] [Algebra (ZMod 2) F]

/-- Exact trace-annihilator identity for the field hyperplane.  Trace
nondegeneracy is provided by the proved finite-field trace pairing theorem. -/
theorem trace_annihilator_hyperplane_iff_mem_line {v z : Vec F} (hv : v ≠ 0) :
    (∀ y ∈ hyperplane v, traceBinary (dot z y) = 0) ↔ z ∈ line v := by
  rw [← annihilator_hyperplane_iff_mem_line hv]
  constructor
  · intro hz y hy
    apply (trace_mul_vanish_iff (dot z y)).mp
    intro t
    have ht := hz (t • y) ((hyperplane v).smul_mem t hy)
    simpa only [dot_smul_right] using ht
  · intro hz y hy
    rw [hz y hy, map_zero]

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockKernelLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Character kernels on quadratic blocks

The character with horizontal coefficient `g` and vertical coefficient `z`
annihilates the block attached to `Fz` precisely when the alignment
equation holds.  The predicate below is annihilation of the actual binary
submodule, rather than an abstract replacement for that condition.
-/

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [Algebra (ZMod 2) F] in
/-- A field-valued identity before applying the binary trace. -/
theorem dot_Q_smul (z : Vec F) (t : F) :
    dot z (Q (t • z)) = t ^ 2 * (z 0 * z 1 * z 2) := by
  change z 0 * ((t * z 1) * (t * z 2)) +
      z 1 * ((t * z 0) * (t * z 2)) +
      z 2 * ((t * z 0) * (t * z 1)) = _
  calc
    _ = (t ^ 2 * (z 0 * z 1 * z 2)) +
        (t ^ 2 * (z 0 * z 1 * z 2)) +
        (t ^ 2 * (z 0 * z 1 * z 2)) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

omit [Finite F] in
theorem blockCharacter_on_quadratic (g z : Vec F) (t : F) :
    blockCharacter g z (t • z, Q (t • z)) =
      traceBinary (t * dot g z + t ^ 2 * (z 0 * z 1 * z 2)) := by
  simp only [blockCharacter, dot_smul_right, dot_Q_smul]

/-- The exact quadratic-block kernel criterion on the line of the character. -/
theorem blockAnnihilates_self_iff (g z : Vec F) :
    BlockAnnihilates g z z ↔ dot g z = squareRoot (z 0 * z 1 * z 2) := by
  constructor
  · intro h
    apply (trace_quadratic_vanish_iff _ _).mp
    intro t
    have hm : (t • z, Q (t • z)) ∈ U z := by
      simpa only [add_zero] using pair_mem_U z (t • z) 0
        ((mem_line_iff z (t • z)).mpr ⟨t, rfl⟩) (Submodule.zero_mem _)
    simpa only [blockCharacter_on_quadratic] using h _ hm
  · intro h p hp
    obtain ⟨a, ha, w, hw, rfl⟩ := (mem_U_iff_exists z p).mp hp
    obtain ⟨t, rfl⟩ := (mem_line_iff z a).mp ha
    change traceBinary (dot g (t • z) + dot z (Q (t • z) + w)) = 0
    rw [dot_add_right, (mem_hyperplane z w).mp hw, add_zero,
      dot_smul_right, dot_Q_smul]
    exact (trace_quadratic_vanish_iff _ _).mpr h t

/-- A character in a block's kernel has its vertical coefficient on that line. -/
theorem mem_line_of_blockAnnihilates {g z v : Vec F} (hv : v ≠ 0)
    (h : BlockAnnihilates g z v) : z ∈ line v := by
  apply (trace_annihilator_hyperplane_iff_mem_line hv).mp
  intro y hy
  have hm : (0, y) ∈ U v := by
    simpa only [Q_zero, zero_add] using
      pair_mem_U v 0 y (Submodule.zero_mem _) hy
  simpa only [blockCharacter, dot_zero_right, zero_add] using h _ hm

/-- Full nonzero-character criterion, including the field-line condition. -/
theorem blockAnnihilates_iff {g z v : Vec F} (hv : v ≠ 0) (hz : z ≠ 0) :
    BlockAnnihilates g z v ↔
      z ∈ line v ∧ dot g z = squareRoot (z 0 * z 1 * z 2) := by
  constructor
  · intro h
    have hm := mem_line_of_blockAnnihilates hv h
    refine ⟨hm, (blockAnnihilates_self_iff g z).mp ?_⟩
    simpa only [BlockAnnihilates, U_eq_of_nonzero_mem_line hz hm] using h
  · rintro ⟨hm, ha⟩
    have h := (blockAnnihilates_self_iff g z).mpr ha
    simpa only [BlockAnnihilates, U_eq_of_nonzero_mem_line hz hm] using h

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockRestriction
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual child restriction maps

A common-parent lift `g` gives a binary linear map from its logical character
space into the dual of each quadratic block.  Its kernel is literal character
annihilation, so the trace calculation and the all-lifts genericity predicate
apply directly to this map.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Fintype F] in
/-- Equality to zero is exactly annihilation of the underlying block. -/
theorem blockRestriction_eq_zero_iff (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) (z : S) :
    blockRestriction S g v z = 0 ↔ BlockAnnihilates (g z) z v := by
  constructor
  · intro h p hp
    exact LinearMap.congr_fun h ⟨p, hp⟩
  · intro h
    ext p
    exact h p p.property

/-- The exact kernel formula for a nonzero logical character. -/
theorem mem_ker_blockRestriction_iff (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) {v : Vec F} (hv : v ≠ 0)
    {z : S} (hz : z ≠ 0) :
    z ∈ (blockRestriction S g v).ker ↔
      (z : Vec F) ∈ line v ∧
        dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2) := by
  have hz' : (z : Vec F) ≠ 0 := fun h => hz (Subtype.ext h)
  rw [LinearMap.mem_ker, blockRestriction_eq_zero_iff, blockAnnihilates_iff hv hz']

/-- Nonproportionality of a generic space makes every actual block kernel
contain at most one nonzero character. -/
theorem blockRestriction_nonzero_kernel_unique
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S)
    (z w : S) (hz : z ≠ 0) (hw : w ≠ 0)
    (hgz : blockRestriction S g v z = 0)
    (hgw : blockRestriction S g v w = 0) : z = w := by
  have hzline := mem_line_of_blockAnnihilates hv
    ((blockRestriction_eq_zero_iff S g v z).mp hgz)
  have hwline := mem_line_of_blockAnnihilates hv
    ((blockRestriction_eq_zero_iff S g v w).mp hgw)
  obtain ⟨t, ht⟩ := (mem_line_iff v z).mp hzline
  obtain ⟨s, hs⟩ := (mem_line_iff v w).mp hwline
  have hsne : s ≠ 0 := by
    intro hzero
    apply hw
    apply Subtype.ext
    simpa [hzero] using hs.symm
  apply hS.1 z w hz hw
  refine ⟨t / s, ?_⟩
  rw [← ht, ← hs, smul_smul, div_mul_cancel₀ _ hsne]

/-- Every actual child restriction map loses at most one binary dimension. -/
theorem finrank_ker_blockRestriction_le_one
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S) :
    Module.finrank (ZMod 2) (blockRestriction S g v).ker ≤ 1 :=
  finrank_ker_le_one_of_nonzero_unique (blockRestriction S g v)
    (blockRestriction_nonzero_kernel_unique S g hv hS)

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_OrientedRestrictionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Orientation-independent character kernels

Changing the binary parametrization of a block only pulls its dual back along
a linear equivalence.  This leaves the logical kernel unchanged and places
all child maps in one fixed dual space for the finite counting argument.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F B : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [AddCommGroup B] [Module (ZMod 2) B]

omit [Fintype F] in
theorem orientedBlockRestriction_eq_zero_iff
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) (z : S) :
    orientedBlockRestriction S g v J z = 0 ↔ blockRestriction S g v z = 0 := by
  change J.dualMap (blockRestriction S g v z) = 0 ↔ _
  constructor
  · intro h
    apply J.dualMap.injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

omit [Fintype F] in
/-- The kernel depends on the field line and common-parent lift, not on `J`. -/
theorem ker_orientedBlockRestriction
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) :
    (orientedBlockRestriction S g v J).ker = (blockRestriction S g v).ker := by
  ext z
  simp only [LinearMap.mem_ker, orientedBlockRestriction_eq_zero_iff]

theorem mem_ker_orientedBlockRestriction_iff
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (J : B ≃ₗ[ZMod 2] U v)
    {z : S} (hz : z ≠ 0) :
    z ∈ (orientedBlockRestriction S g v J).ker ↔
      (z : Vec F) ∈ line v ∧
        dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2) := by
  rw [ker_orientedBlockRestriction]
  exact mem_ker_blockRestriction_iff S g hv hz

theorem finrank_ker_orientedBlockRestriction_le_one
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S) (J : B ≃ₗ[ZMod 2] U v) :
    Module.finrank (ZMod 2) (orientedBlockRestriction S g v J).ker ≤ 1 := by
  rw [ker_orientedBlockRestriction]
  exact finrank_ker_blockRestriction_le_one S g hv hS

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# At most `3r` actual lossy field lines

The genericity bound applies to the common-parent lift before a line or an
orientation is chosen.  A nonzero kernel character determines exactly one
projective field line, and its actual kernel equation implies alignment.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

attribute [local instance] OAI.UniqueGamesTheorem.Quadratic.instFintypeFieldLine
attribute [local instance] OAI.UniqueGamesTheorem.Quadratic.instFintypeSubtypeVecMemSubmoduleZModOfNatNat
omit [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem characterFieldLine_eq_of_mem {A₀ A : FieldLine F} {z : Vec F}
    (hz : z ≠ 0) (hm : z ∈ line (lineGenerator A)) :
    characterFieldLine A₀ z = A := by
  classical
  rw [characterFieldLine, dite_eq_right hz, ← Projectivization.mk_rep A]
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact (mem_line_iff (lineGenerator A) z).mp hm

/-- The alignment event written with the displayed three-coordinate dot product. -/
theorem alignedCharacters_eq_alignmentEvent
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F) :
    alignedCharacters (fun z : S =>
      dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2)) =
      alignmentEvent (fun z : S => (z : Vec F)) g
        (fun z : S => alignmentRightHandSide (z : Vec F)) := by
  classical
  ext z
  simp [alignedCharacters, alignmentEvent, alignmentRightHandSide,
    Fin.sum_univ_three, dot, mul_comm]

/-- The exact line-loss count, valid for every choice of orientations and every
binary-linear lift, including one chosen adaptively from earlier information. -/
theorem card_loss_fieldLineRestrictions_le
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (J : ∀ A : FieldLine F, BlockOrientation A) (hS : IsGeneric S)
    (A₀ : FieldLine F) :
    (lossIndices (fieldLineRestrictions S g J)).card ≤
      3 * Module.finrank (ZMod 2) S := by
  classical
  apply card_lossIndices_le (fieldLineRestrictions S g J)
    (fun z : S => dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2))
    (fun z : S => characterFieldLine A₀ (z : Vec F)) (Module.finrank (ZMod 2) S)
  · intro A z hz hzero
    have hk := (mem_ker_orientedBlockRestriction_iff S g
      (lineGenerator_ne_zero A) (J A) hz).mp hzero
    refine ⟨hk.2, characterFieldLine_eq_of_mem ?_ hk.1⟩
    exact fun h => hz (Subtype.ext h)
  · rw [alignedCharacters_eq_alignmentEvent]
    exact hS.2 g

/-- The fallback line is only used to totalize the counting map. -/
theorem card_loss_fieldLineRestrictions_le_three_rank
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (J : ∀ A : FieldLine F, BlockOrientation A) (hS : IsGeneric S) :
    (lossIndices (fieldLineRestrictions S g J)).card ≤
      3 * Module.finrank (ZMod 2) S := by
  let A₀ : FieldLine F := Projectivization.mk F (fun _ : Fin 3 => (1 : F)) (by
    intro h
    have h0 := congrFun h 0
    exact one_ne_zero h0)
  exact card_loss_fieldLineRestrictions_le S g J hS A₀

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_HarmonicLoss
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Harmonic loss for the actual quadratic child maps

The probabilistic hypotheses of the harmonic accounting lemmas are discharged
here by the proved field-line kernel criterion and genericity count.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators
open UniqueGamesTheorem.Gadget.Harmonic

noncomputable section

private theorem exists_nonzero_kernel_of_range_rank_lt
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) V]
    (f : V →ₗ[ZMod 2] W)
    (h : Module.finrank (ZMod 2) f.range < Module.finrank (ZMod 2) V) :
    ∃ z, z ≠ 0 ∧ f z = 0 := by
  by_contra hn
  have hk : f.ker = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    change z = 0
    by_contra hz0
    exact hn ⟨z, hz0, hz⟩
  have hdim := f.finrank_range_add_finrank_ker
  rw [hk, finrank_bot, add_zero] at hdim
  omega

private theorem probability_rank_drop_le_loss_count
    {I V W : Type*} [Fintype I] [Fintype V]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (f : I → V →ₗ[ZMod 2] W) :
    probability (fun i => Module.finrank (ZMod 2) (f i).range <
        Module.finrank (ZMod 2) V) ≤
      ((lossIndices f).card : ℚ) / Fintype.card I := by
  classical
  have hsub : Finset.univ.filter (fun i =>
      Module.finrank (ZMod 2) (f i).range < Module.finrank (ZMod 2) V) ⊆
      lossIndices f := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      exists_nonzero_kernel_of_range_rank_lt (f i) (Finset.mem_filter.mp hi).2⟩
  simp only [probability, average, Finset.expect_eq_sum_div_card,
    Finset.sum_boole, Finset.card_univ]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card hsub

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem fieldLineTheta_eq : fieldLineTheta F =
    ((Nat.card F : ℚ) ^ 2 + Nat.card F + 1)⁻¹ :=
  reciprocal_card_FieldLine

attribute [local instance] OAI.UniqueGamesTheorem.Quadratic.instFintypeFieldLine_1
attribute [local instance] OAI.UniqueGamesTheorem.Quadratic.instFintypeSubtypeVecMemSubmoduleZModOfNatNat_1
theorem nextBlockRank_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (A : FieldLine F) : nextBlockRank S g J A ≤ Module.finrank (ZMod 2) S :=
  LinearMap.finrank_range_le _

theorem generic_nextBlockRank_dichotomy (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) (A : FieldLine F) :
    nextBlockRank S g J A = Module.finrank (ZMod 2) S ∨
      nextBlockRank S g J A = Module.finrank (ZMod 2) S - 1 := by
  have hk := finrank_ker_orientedBlockRestriction_le_one S g
    (lineGenerator_ne_zero A) hS (J A)
  have hdim := (fieldLineRestrictions S g J A).finrank_range_add_finrank_ker
  change Module.finrank (ZMod 2) (fieldLineRestrictions S g J A).ker ≤ 1 at hk
  unfold nextBlockRank
  omega

theorem generic_block_loss_probability_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) :
    probability (fun A => nextBlockRank S g J A < Module.finrank (ZMod 2) S) ≤
      3 * Module.finrank (ZMod 2) S * fieldLineTheta F := by
  classical
  calc
    _ ≤ ((lossIndices (fieldLineRestrictions S g J)).card : ℚ) /
        Fintype.card (FieldLine F) :=
      probability_rank_drop_le_loss_count (fieldLineRestrictions S g J)
    _ ≤ (3 * (Module.finrank (ZMod 2) S : ℚ)) / Fintype.card (FieldLine F) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_loss_fieldLineRestrictions_le_three_rank S g J hS
    _ = _ := by simp only [fieldLineTheta, Fintype.card_eq_nat_card, div_eq_mul_inv]

/-- Actual generic block restrictions have rank-independent expected harmonic loss. -/
theorem generic_block_harmonic_loss_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) :
    average (fun A => UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
      UniqueGamesTheorem.Gadget.Harmonic.harmonic (nextBlockRank S g J A)) ≤ 3 * fieldLineTheta F := by
  classical
  by_cases hr : 0 < Module.finrank (ZMod 2) S
  · exact generic_expected_drop_le _ _ _ hr
      (generic_nextBlockRank_dichotomy S g J hS)
      (generic_block_loss_probability_le S g J hS)
  · have hr0 : Module.finrank (ZMod 2) S = 0 := by omega
    have hnext : ∀ A, nextBlockRank S g J A = 0 := by
      intro A
      have := nextBlockRank_le S g J A
      omega
    simp only [hr0, hnext, UniqueGamesTheorem.Gadget.Harmonic.harmonic_zero, sub_self]
    have hzero : average (fun _ : FieldLine F => (0 : ℚ)) = 0 := by
      simp [average]
    rw [hzero]
    unfold fieldLineTheta
    positivity

theorem card_loss_fieldLineRestrictions_le_nonzero
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (J : ∀ A : FieldLine F, BlockOrientation A) :
    (lossIndices (fieldLineRestrictions S g J)).card ≤ Fintype.card S - 1 := by
  classical
  let A₀ : FieldLine F := Projectivization.mk F (fun _ : Fin 3 => (1 : F)) (by
    intro h
    exact one_ne_zero (congrFun h 0))
  apply card_lossIndices_le_nonzero (fieldLineRestrictions S g J)
    (fun z : S => characterFieldLine A₀ (z : Vec F))
  intro A z hz hzero
  have hk := (mem_ker_orientedBlockRestriction_iff S g
    (lineGenerator_ne_zero A) (J A) hz).mp hzero
  exact characterFieldLine_eq_of_mem (fun h => hz (Subtype.ext h)) hk.1

theorem arbitrary_block_loss_probability_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    probability (fun A => nextBlockRank S g J A < Module.finrank (ZMod 2) S) ≤
      2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F := by
  classical
  have hc : Fintype.card S = 2 ^ Module.finrank (ZMod 2) S := by
    simpa only [ZMod.card] using Module.card_eq_pow_finrank (K := ZMod 2) (V := S)
  have hcount : (lossIndices (fieldLineRestrictions S g J)).card ≤
      2 ^ Module.finrank (ZMod 2) S :=
    (card_loss_fieldLineRestrictions_le_nonzero S g J).trans
      ((Nat.sub_le _ _).trans_eq hc)
  calc
    _ ≤ ((lossIndices (fieldLineRestrictions S g J)).card : ℚ) /
        Fintype.card (FieldLine F) :=
      probability_rank_drop_le_loss_count (fieldLineRestrictions S g J)
    _ ≤ ((2 : ℚ) ^ Module.finrank (ZMod 2) S) / Fintype.card (FieldLine F) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcount
    _ = _ := by simp only [fieldLineTheta, Fintype.card_eq_nat_card, div_eq_mul_inv]

theorem arbitrary_block_harmonic_loss_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    average (fun A => UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
      UniqueGamesTheorem.Gadget.Harmonic.harmonic (nextBlockRank S g J A)) ≤
        UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) *
          2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F := by
  simpa only [mul_assoc] using arbitrary_expected_drop_le
    (Module.finrank (ZMod 2) S) (nextBlockRank S g J)
    (2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F)
    (nextBlockRank_le S g J) (arbitrary_block_loss_probability_le S g J)

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_TraceDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Trace coordinates for families of binary characters

The trace pairing identifies the binary dual of `F³` with `F³` itself.  Its
inverse is linear, so a common-parent family of binary functionals produces
one binary-linear lift `g`, as required by the all-lifts genericity theorem.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem representTraceFamily_spec
    (γ : W →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2)) (z : W) (y : Vec F) :
    traceBinary (dot (representTraceFamily γ z) y) = γ z y :=
  traceDualEquiv_symm_apply (γ z) y

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_BlockDescentLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

namespace Gadget.BlockDescent

open Quadratic OrientedBlockKernel

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2] in
theorem traceSpace_finrank (S : Submodule (ZMod 2) (BinaryDual (F := F))) :
    Module.finrank (ZMod 2) (traceSpace S) = Module.finrank (ZMod 2) S :=
  (traceSpaceEquiv S).finrank_eq.symm

omit [CharP F 2] in
theorem traceSpaceEquiv_symm_val
    (S : Submodule (ZMod 2) (BinaryDual (F := F))) (z : traceSpace S) :
    ((traceSpaceEquiv S).symm z).val = traceDualEquiv z.val := by
  apply traceDualEquiv.symm.injective
  have h := congrArg Subtype.val ((traceSpaceEquiv S).apply_symm_apply z)
  simpa only [traceSpaceEquiv_apply_val, LinearEquiv.symm_apply_apply] using h

/-- Equality of actual child maps after a change of logical coordinates. -/
theorem childCharacter_comp_traceSpaceEquiv
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (i : BlockOrientationIndex F) :
    (childCharacter orientedBlockLinear γ i).comp (traceSpaceEquiv S).symm.toLinearMap =
      orientedBlockRestriction (traceSpace S) (traceLift S γ) (lineGenerator i.1) i.2 := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro b
  change γ ((traceSpaceEquiv S).symm z) (i.2 b).val.1 +
    ((traceSpaceEquiv S).symm z).val (i.2 b).val.2 =
      traceBinary (dot (traceLift S γ z) (i.2 b).val.1 + dot z.val (i.2 b).val.2)
  rw [map_add]
  rw [show traceBinary (dot (traceLift S γ z) (i.2 b).val.1) =
    γ ((traceSpaceEquiv S).symm z) (i.2 b).val.1 from
      representTraceFamily_spec (γ.comp (traceSpaceEquiv S).symm.toLinearMap) z _]
  rw [traceSpaceEquiv_symm_val, traceDualEquiv_apply]

/-- The child logical image is unchanged by the trace-coordinate domain
isomorphism. This is equality of subspaces, not merely equality of ranks. -/
theorem childCharacter_range_eq
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (i : BlockOrientationIndex F) :
    (childCharacter orientedBlockLinear γ i).range =
      (orientedBlockRestriction (traceSpace S) (traceLift S γ)
        (lineGenerator i.1) i.2).range := by
  rw [← childCharacter_comp_traceSpaceEquiv]
  exact (LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)).symm

/-- Before the orientation is revealed, the un-oriented image is fixed; the
fresh isomorphism acts only by dual pullback on this fixed image. -/
theorem childCharacter_range_eq_dual_pullback
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (i : BlockOrientationIndex F) :
    (childCharacter orientedBlockLinear γ i).range =
      ((blockRestriction (traceSpace S) (traceLift S γ) (lineGenerator i.1)).range).map
        i.2.dualMap.toLinearMap := by
  rw [childCharacter_range_eq]
  exact LinearMap.range_comp _ _

/-- The rank is independent of the fresh orientation. -/
theorem childCharacter_rank_independent
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F)
    (J J' : BlockOrientation A) :
    Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ ⟨A, J⟩).range =
      Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ ⟨A, J'⟩).range := by
  rw [childCharacter_range_eq_dual_pullback, childCharacter_range_eq_dual_pullback]
  rw [J.dualMap.finrank_map_eq, J'.dualMap.finrank_map_eq]

end Gadget.BlockDescent

namespace Gadget.FreshGenericity

open scoped BigOperators Classical
open Module

open Orientation Quadratic BlockDescent OrientedBlockKernel

attribute [local instance] linearMapFintype linearEquivFintype submoduleFintype rankSpaceFintype

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

theorem mean_bad_rankSpace (r : ℕ) :
    (𝔼 S : RankSpace (ZMod 2) (BinaryDual (F := F)) r,
      if bad S.val then (1 : ℚ) else 0) = nongenericFraction F r := by
  calc
    _ = 𝔼 S : RankSpace (ZMod 2) (Vec F) r,
        if ¬IsGeneric S.val then (1 : ℚ) else 0 := by
      exact Fintype.expect_equiv (rankSpaceEquiv traceDualEquiv.symm r) _ _
        (fun T => by
          by_cases h : IsGeneric (traceSpace T.val)
          · simp only [rankSpaceEquiv_apply, bad, traceSpace] at h ⊢
            simp only [h, not_true_eq_false, ite_false]
          · simp only [rankSpaceEquiv_apply, bad, traceSpace] at h ⊢
            simp only [h, not_false_eq_true, ite_true, if_true])
    _ = _ := by
      simp only [nongenericFraction, Fintype.expect_eq_sum_div_card,
        Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

variable [∀ A : FieldLine F, Fintype (BlockOrientation A)]

theorem mean_fresh_bad_at_line
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F) :
    (𝔼 J : BlockOrientation A,
      if bad (childCharacter orientedBlockLinear γ ⟨A, J⟩).range then (1 : ℚ) else 0) =
      nongenericFraction F
        (finrank (ZMod 2) (blockRestriction (traceSpace S) (traceLift S γ)
          (lineGenerator A)).range) := by
  let E := (blockRestriction (traceSpace S) (traceLift S γ) (lineGenerator A)).range
  calc
    _ = 𝔼 J : BlockOrientation A,
        if bad (E.map J.dualMap.toLinearMap) then (1 : ℚ) else 0 := by
      apply Finset.expect_congr rfl
      intro J _
      rw [childCharacter_range_eq_dual_pullback]
    _ = 𝔼 T : RankSpace (ZMod 2) (BinaryDual (F := F)) (finrank (ZMod 2) E),
        if bad T.val then (1 : ℚ) else 0 := by
      simp only [Fintype.expect_eq_sum_div_card]
      exact mean_dual_pullback E (chosenBlockOrientation A)
        (fun T => if bad T.val then (1 : ℚ) else 0)
    _ = _ := mean_bad_rankSpace _

omit [∀ A : FieldLine F, Fintype (BlockOrientation A)] in
theorem unoriented_rank_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F) :
    finrank (ZMod 2) (blockRestriction (traceSpace S) (traceLift S γ)
      (lineGenerator A)).range ≤ finrank (ZMod 2) S := by
  calc
    _ ≤ finrank (ZMod 2) (traceSpace S) := LinearMap.finrank_range_le _
    _ = _ := traceSpace_finrank S

/-- The field error bound applies to the actual fresh descendant rank,
even though that rank depends on the earlier lift and the selected line. -/
theorem fresh_bad_at_line_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F)
    (r₀ : ℕ) (ε : ℚ) (hS : finrank (ZMod 2) S ≤ r₀)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε) :
    (𝔼 J : BlockOrientation A,
      if bad (childCharacter orientedBlockLinear γ ⟨A, J⟩).range then (1 : ℚ) else 0) ≤ ε := by
  rw [mean_fresh_bad_at_line]
  exact hgeneric _ ((unoriented_rank_le S γ A).trans hS)

variable [Fintype (FieldLine F)]

/-- Fresh nongenericity bound over the actual full child index.  The parent
family and the common-parent map are arbitrary fixed inputs, so the result
applies at every adaptive history without a future-lift independence premise. -/
theorem fresh_bad_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F))
    (r₀ : ℕ) (ε : ℚ) (hS : finrank (ZMod 2) S ≤ r₀)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε) :
    (𝔼 i : BlockOrientationIndex F,
      if bad (childCharacter orientedBlockLinear γ i).range then (1 : ℚ) else 0) ≤ ε := by
  have : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  rw [mean_block_pairs]
  calc
    _ ≤ 𝔼 _A : FieldLine F, ε := Finset.expect_le_expect
      (fun A _ => fresh_bad_at_line_le S γ A r₀ ε hS hgeneric)
    _ = ε := Fintype.expect_const _
/-- The fresh bound for the deterministic descendant of an actual parent
lift. The common-parent map is chosen from the whole lift before sampling the
child index, exactly as required by the adaptive finite-history experiment. -/
theorem descendant_bad_le
    [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] :
    let J := orientedBlockLinear (F := F)
    ∀ (hJ : Function.Surjective (aggregate J))
      (Q : Vec F → Vec F) (s : Stage (ZMod 2) (Vec F))
      (S : Submodule (ZMod 2) (BinaryDual (F := F)))
      (L : Lift (Stage.next J hJ Q s) S)
      (r₀ : ℕ) (ε : ℚ), finrank (ZMod 2) S ≤ r₀ →
      (∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε) →
      (𝔼 i : BlockOrientationIndex F,
        if bad (Descent.childDomain J hJ Q s S L i) then (1 : ℚ) else 0) ≤ ε := by
  intro J hJ Q s S L r₀ ε hS hgeneric
  simpa only [Descent.childDomain] using!
    fresh_bad_le S (Descent.commonGamma J hJ Q s S L) r₀ ε hS hgeneric

end Gadget.FreshGenericity

/-!
# Outgoing harmonic loss for the actual adaptive child map

Uniform sampling of the concrete pair `(field line, binary orientation)` has
the uniform field-line marginal. The child rank is independent of orientation,
so the proved quadratic kernel count gives the outgoing conditional loss for
the common map produced by every parent lift.
-/

namespace Gadget.OutgoingHarmonic

open Quadratic OrientedBlockKernel BlockDescent Harmonic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

attribute [local instance] OAI.UniqueGamesTheorem.Gadget.OutgoingHarmonic.instFiniteLinearEquivZModOfNatNatIdVec
attribute [local instance] OAI.UniqueGamesTheorem.Gadget.OutgoingHarmonic.instFintypeLinearEquivZModOfNatNatIdVec
/-- Averaging all binary orientations reduces exactly to the actual line-law
rank experiment, after transporting logical characters by the trace pairing. -/
theorem outgoingLoss_eq_line_average
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) :
    outgoingLoss S γ = average (fun A : FieldLine F =>
      UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
        UniqueGamesTheorem.Gadget.Harmonic.harmonic (nextBlockRank (traceSpace S) (traceLift S γ) chosenBlockOrientation A)) := by
  unfold outgoingLoss average
  rw [mean_block_pairs]
  apply Finset.expect_congr rfl
  intro A _
  let : Nonempty (BlockOrientation A) := ⟨chosenBlockOrientation A⟩
  have hrank (J : BlockOrientation A) :
      Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ ⟨A, J⟩).range =
        nextBlockRank (traceSpace S) (traceLift S γ) chosenBlockOrientation A := by
    rw [childCharacter_rank_independent S γ A J (chosenBlockOrientation A)]
    rw [childCharacter_range_eq]
    rfl
  simp_rw [hrank]
  exact Finset.expect_const Finset.univ_nonempty _

/-- The generic all-lifts bound applies to the actual common parent map. -/
theorem generic_outgoing_loss_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (hS : IsGeneric (traceSpace S)) :
    outgoingLoss S γ ≤ 3 * fieldLineTheta F := by
  rw [outgoingLoss_eq_line_average]
  simpa only [traceSpace_finrank] using
    generic_block_harmonic_loss_le (traceSpace S) (traceLift S γ) chosenBlockOrientation hS

/-- Nongeneric actual child maps satisfy the fallback harmonic charge. -/
theorem arbitrary_outgoing_loss_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) :
    outgoingLoss S γ ≤ badRankCoefficient (Module.finrank (ZMod 2) S) * fieldLineTheta F := by
  rw [outgoingLoss_eq_line_average]
  simpa only [traceSpace_finrank, badRankCoefficient] using
    arbitrary_block_harmonic_loss_le (traceSpace S) (traceLift S γ) chosenBlockOrientation

theorem badRankCoefficient_mono {r s : ℕ} (h : r ≤ s) :
    badRankCoefficient r ≤ badRankCoefficient s := by
  unfold badRankCoefficient
  apply mul_le_mul (harmonic_mono h) (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) h)
  · positivity
  · exact harmonic_nonneg _

/-- Combined conditional law with a coefficient frozen at the initial rank.
The bad predicate is exactly the nongeneric trace-coordinate domain. -/
theorem outgoing_harmonic_loss_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (r₀ : ℕ)
    (hcap : Module.finrank (ZMod 2) S ≤ r₀)
    [Decidable (IsGeneric (traceSpace S))] :
    outgoingLoss S γ ≤ 3 * fieldLineTheta F +
      badRankCoefficient r₀ * fieldLineTheta F * if ¬ IsGeneric (traceSpace S) then 1 else 0 := by
  have hθ : 0 ≤ fieldLineTheta F := by unfold fieldLineTheta; positivity
  by_cases hS : IsGeneric (traceSpace S)
  · simpa only [not_true_eq_false, hS, ite_false, mul_zero, add_zero] using
      generic_outgoing_loss_le S γ hS
  · rw [ite_eq_left hS, mul_one]
    calc
      outgoingLoss S γ ≤ badRankCoefficient (Module.finrank (ZMod 2) S) * fieldLineTheta F :=
        arbitrary_outgoing_loss_le S γ
      _ ≤ badRankCoefficient r₀ * fieldLineTheta F :=
        mul_le_mul_of_nonneg_right (badRankCoefficient_mono hcap) hθ
      _ ≤ 3 * fieldLineTheta F + badRankCoefficient r₀ * fieldLineTheta F := by linarith
/-- Direct instantiation of `DescentProbability.expected_terminal_loss`'s
outgoing-step hypothesis for the concrete child domain of every actual lift. -/
theorem descendant_harmonic_loss_le
    [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] :
    let J : BlockOrientationIndex F → Vec F →ₗ[ZMod 2] Vec F × Vec F :=
      orientedBlockLinear
    ∀ (hJ : Function.Surjective (aggregate J))
      (Q : Vec F → Vec F) (s : Stage (ZMod 2) (Vec F))
      (S : Submodule (ZMod 2) (BinaryDual (F := F)))
      (L : Lift (Stage.next J hJ Q s) S) (r₀ : ℕ)
      (_hcap : Module.finrank (ZMod 2) S ≤ r₀)
      [Decidable (IsGeneric (traceSpace S))],
      average (fun i : BlockOrientationIndex F => UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
        UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) (Descent.childDomain J hJ Q s S L i))) ≤
        3 * fieldLineTheta F + badRankCoefficient r₀ * fieldLineTheta F *
          if ¬ IsGeneric (traceSpace S) then 1 else 0 := by
  intro J hJ Q s S L r₀ hcap hdec
  exact outgoing_harmonic_loss_le S (Descent.commonGamma J hJ Q s S L) r₀ hcap

end Gadget.OutgoingHarmonic

namespace Gadget.BaseDetection

open Quadratic OrientedBlockKernel BlockDescent Harmonic
open Descent DescentProbability LeafDetection
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)]

omit [CharP F 2] [DecidableEq (BlockOrientationIndex F)]
    [Nonempty (BlockOrientationIndex F)] in
theorem traceSpace_logicalCharacters (S : Submodule (ZMod 2) (Vec F)) :
    traceSpace (logicalCharacters S) = S := by
  exact (Submodule.map_symm_eq_iff traceDualEquiv).mpr rfl

omit [CharP F 2] [DecidableEq (BlockOrientationIndex F)]
    [Nonempty (BlockOrientationIndex F)] in
theorem logicalCharacters_finrank (S : Submodule (ZMod 2) (Vec F)) :
    Module.finrank (ZMod 2) (logicalCharacters S) = Module.finrank (ZMod 2) S :=
  traceDualEquiv.finrank_map_eq S

omit [CharP F 2] [Algebra (ZMod 2) F] [DecidableEq (BlockOrientationIndex F)]
    [Nonempty (BlockOrientationIndex F)] in
theorem theta_pos : 0 < fieldLineTheta F := by
  have hc : (0 : ℚ) < Nat.card (FieldLine F) := by
    exact_mod_cast (card_FieldLine_pos (F := F))
  exact inv_pos.mpr hc
/-- All probabilities concern the actual recursive noise choices. The field
and generic top space satisfy separately proved finite-field properties; no
probability estimate for the whole recursive gadget is an input. -/
theorem full_lift_detection :
    let J : BlockOrientationIndex F → Vec F →ₗ[ZMod 2] Vec F × Vec F :=
      orientedBlockLinear
    ∀ (hJ : Function.Surjective (aggregate J))
      (r₀ : ℕ) (ε : ℚ) (_hr₀ : 0 < r₀)
      (_hbudget : badRankCoefficient r₀ * ε ≤ 1)
      (_hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε)
      (S₀ : Submodule (ZMod 2) (Vec F))
      (_hrank : Module.finrank (ZMod 2) S₀ = r₀) (_hS₀ : IsGeneric S₀)
      (L : Lift (Stage.iterate J hJ Q (depth r₀ (fieldLineTheta F)))
        (⊤ : Submodule (ZMod 2) (BinaryDual (F := F)))),
      (1 / 4 : ℚ) ≤ detectionProbability J hJ Q
        (depth r₀ (fieldLineTheta F)) ⊤ L := by
  intro J hJ r₀ ε hr₀ hbudget hgeneric S₀ hrank hS₀ L
  classical
  let S := logicalCharacters S₀
  have hSrank : Module.finrank (ZMod 2) S = r₀ :=
    (logicalCharacters_finrank S₀).trans hrank
  have hSgeneric : IsGeneric (traceSpace S) := by
    simpa only [S, traceSpace_logicalCharacters] using hS₀
  let L₀ := L.restrict (show S ≤ ⊤ from le_top)
  have hdrop := DescentProbability.expected_terminal_loss J hJ Q
    (fun T => ¬ IsGeneric (traceSpace T)) r₀ (badRankCoefficient r₀)
    (fieldLineTheta F) ε (badRankCoefficient_nonneg r₀) (le_of_lt theta_pos) hbudget
    (by
      intro s T L' hT
      exact OutgoingHarmonic.descendant_harmonic_loss_le hJ Q s T L' r₀ hT)
    (by
      intro s T L' hT
      have hf := FreshGenericity.descendant_bad_le hJ Q s T L' r₀ ε hT hgeneric
      refine (le_of_eq ?_).trans hf
      apply Finset.expect_congr rfl
      intro i _
      by_cases hi : IsGeneric (traceSpace (childDomain J hJ Q s T L' i))
      · simp only [FreshGenericity.bad, J] at hi ⊢
        simp only [hi, not_true_eq_false, ite_false]
      · simp only [FreshGenericity.bad, J] at hi ⊢
        simp only [hi, not_false_eq_true, ite_true, if_true])
    (depth r₀ (fieldLineTheta F)) S L₀ hSrank.le
  have hdepth := depth_budget r₀ (fieldLineTheta F) theta_pos
  have hpotential : UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q (depth r₀ (fieldLineTheta F)) S L₀ := by
    simp only [hSgeneric, not_true_eq_false, ite_false, mul_zero, add_zero, hSrank] at hdrop ⊢
    linarith
  exact quarter_detection_of_restricted_terminal_potential J hJ Q
    (depth r₀ (fieldLineTheta F)) S ⊤ le_top L (hSrank.symm ▸ hr₀) hpotential

end Gadget.BaseDetection

end UniqueGamesTheorem

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_QuadraticStageNoise
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Gadget.QuadraticStageNoise

open scoped BigOperators Classical
open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

attribute [local instance] OAI.UniqueGamesTheorem.Gadget.QuadraticStageNoise.indexDecidableEq
attribute [local instance] OAI.UniqueGamesTheorem.Gadget.QuadraticStageNoise.automorphismFinite
attribute [local instance] OAI.UniqueGamesTheorem.Gadget.QuadraticStageNoise.automorphismFintype
attribute [local instance] OAI.UniqueGamesTheorem.Gadget.QuadraticStageNoise.indexNonempty
theorem actual_kernel (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, 𝔼 p : Vec F × Vec F,
      NonlinearRecurrence.change (fun z => z.2 + Q z.1) p (blockEmbedding i d)) =
      rate F := by
  classical
  exact OrientedBlockKernel.mean_oriented_block_kernel d hd

theorem stage_error (n : ℕ) :
    StageNoiseRecurrence.error (stage (F := F) n) =
      (1 - 1 / (Nat.card F : ℚ) ^ 3) * rate F ^ n := by
  have he := StageNoiseRecurrence.iterate_error (blockEmbedding (F := F))
    aggregate_blockEmbedding_surjective Q (rate F) actual_kernel n
  simpa only [stage, Vec, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    Nat.card_eq_fintype_card] using he

theorem quotientStage_error (n : ℕ) :
    StageNoiseRecurrence.error (quotientStage (F := F) n) =
      (1 - 1 / (Nat.card F : ℚ) ^ 3) * rate F ^ n := by
  rw [quotientStage, StageNoiseRecurrence.quotient_error, stage_error]

end UniqueGamesTheorem.Gadget.QuadraticStageNoise

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_UniformSubspaces
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Uniform injective parameter maps induce the uniform law on subspaces of the
specified rank.  The proof uses actual transitivity of ambient linear
automorphisms on injections, not an assumed distributional premise.
-/

noncomputable section

open scoped BigOperators
open Module
open UniqueGamesTheorem.Gadget.Orientation

namespace UniqueGamesTheorem.Quadratic.UniformSubspaces

variable {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]

omit [FiniteDimensional K W] in
/-- Every two injections are carried to each other by an automorphism of the
ambient space: extend the isomorphism between their two images. -/
theorem injection_transitive (J₁ J₂ : Injection K V W) :
    ∃ a : W ≃ₗ[K] W, a • J₁ = J₂ := by
  let e₁ := LinearEquiv.ofInjective J₁.val J₁.property
  let e₂ := LinearEquiv.ofInjective J₂.val J₂.property
  let e : LinearMap.range J₁.val ≃ₗ[K] LinearMap.range J₂.val := e₁.symm.trans e₂
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨a, ?_⟩
  apply Subtype.ext
  ext x
  have h := (ha (e₁ x)).symm
  change a (J₁.val x) = ((e₂ (e₁.symm (e₁ x))) : W) at h
  change a (J₁.val x) = J₂.val x
  simpa only [LinearEquiv.symm_apply_apply, e₂, LinearEquiv.ofInjective_apply] using h

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem image_action (a : W ≃ₗ[K] W) (J : Injection K V W) :
    image (a • J) = a • image J := by
  apply Subtype.ext
  exact LinearMap.range_comp J.val a.toLinearMap

variable [Fintype (W ≃ₗ[K] W)] [Fintype (Injection K V W)]
    [Fintype (RankSpace K W (finrank K V))]

/-- Exact uniform image law, conditional only on injectivity of the map. -/
theorem mean_image (J₀ : Injection K V W) (f : RankSpace K W (finrank K V) → ℚ) :
    (∑ J : Injection K V W, f (image J)) / Fintype.card (Injection K V W) =
      (∑ S : RankSpace K W (finrank K V), f S) /
        Fintype.card (RankSpace K W (finrank K V)) := by
  have h := mean_action J₀ (injection_transitive J₀) (fun J => f (image J))
  simp_rw [image_action] at h
  exact h.symm.trans (mean_oriented_subspace (image J₀) f)

/-- Indicator specialization of the exact law, without assuming genericity
or independence of a subsequently chosen lift. -/
theorem bad_image_count_ratio (J₀ : Injection K V W)
    (Bad : RankSpace K W (finrank K V) → Prop) :
    (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) /
        Fintype.card (Injection K V W) =
      (Nat.card {S : RankSpace K W (finrank K V) // Bad S} : ℚ) /
        Fintype.card (RankSpace K W (finrank K V)) := by
  classical
  have h := mean_image J₀ (fun S => if Bad S then 1 else 0)
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

/-- An unconditional bad-parameter count bound transfers after conditioning
on injectivity, paying exactly the usual `1/(1-β)` factor.  The premises are
ordinary count inequalities and can come from polynomial union bounds. -/
theorem bad_subspace_bound (J₀ : Injection K V W)
    (Bad : RankSpace K W (finrank K V) → Prop) (α β : ℚ) (hα : 0 ≤ α) (hβ : β < 1)
    (hbad : (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) ≤
      α * Nat.card (V →ₗ[K] W))
    (hinj : (1 - β) * Nat.card (V →ₗ[K] W) ≤ Fintype.card (Injection K V W)) :
    (Nat.card {S : RankSpace K W (finrank K V) // Bad S} : ℚ) /
        Fintype.card (RankSpace K W (finrank K V)) ≤ α / (1 - β) := by
  rw [← bad_image_count_ratio J₀ Bad]
  have : Nonempty (Injection K V W) := ⟨J₀⟩
  have hi : (0 : ℚ) < Fintype.card (Injection K V W) := by
    exact_mod_cast Fintype.card_pos
  have hd : 0 < 1 - β := sub_pos.mpr hβ
  apply (div_le_div_iff₀ hi hd).mpr
  calc
    (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) * (1 - β) ≤
        (α * Nat.card (V →ₗ[K] W)) * (1 - β) :=
      mul_le_mul_of_nonneg_right hbad hd.le
    _ = α * ((1 - β) * Nat.card (V →ₗ[K] W)) := by ring
    _ ≤ α * Fintype.card (Injection K V W) := mul_le_mul_of_nonneg_left hinj hα

end UniqueGamesTheorem.Quadratic.UniformSubspaces

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_GenericSubspaceProbability
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The polynomial exceptional-event bound is transported first to all binary
linear parameter maps and then, by proved uniformity conditional on
injectivity, to the actual finite Grassmannian.  The same argument supplies
a generic subspace, rather than presupposing that one exists.
-/

noncomputable section

open Module
open UniqueGamesTheorem.Gadget.Orientation

namespace UniqueGamesTheorem.Quadratic

private theorem conditioning_counts {A : Type*} [Fintype A] [Nonempty A]
    (P Q : A → Prop) (α : ℚ) (hα : α < 1)
    (hbad : (Nat.card {a : A // ¬(P a ∧ Q a)} : ℚ) / Nat.card A ≤ α) :
    (∃ a : A, P a ∧ Q a) ∧
      (Nat.card {a : {a : A // P a} // ¬Q a.1} : ℚ) ≤ α * Nat.card A ∧
      (1 - α) * Nat.card A ≤ (Nat.card {a : A // P a} : ℚ) := by
  classical
  have hpos : (0 : ℚ) < Nat.card A := by exact_mod_cast Nat.card_pos
  have hbadCount := (div_le_iff₀ hpos).mp hbad
  have hgood : ∃ a : A, P a ∧ Q a := by
    by_contra h
    have hall : ∀ a : A, ¬(P a ∧ Q a) := fun a ha => h ⟨a, ha⟩
    have hcard : Nat.card {a : A // ¬(P a ∧ Q a)} = Nat.card A := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype, hall]
    rw [hcard, div_self hpos.ne'] at hbad
    exact (not_le_of_gt hα) hbad
  have hnoninj : Nat.card {a : A // ¬P a} ≤ Nat.card {a : A // ¬(P a ∧ Q a)} := by
    apply Nat.card_le_card_of_injective
      (fun a : {a : A // ¬P a} => (⟨a.1, fun h => a.2 h.1⟩ : {a : A // ¬(P a ∧ Q a)}))
    intro a b h
    exact Subtype.ext (congrArg (fun c : {a : A // ¬(P a ∧ Q a)} => c.val) h)
  have hbadInj : Nat.card {a : {a : A // P a} // ¬Q a.1} ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by
    apply Nat.card_le_card_of_injective
      (fun a : {a : {a : A // P a} // ¬Q a.1} =>
        (⟨a.1.1, fun h => a.2 h.2⟩ : {a : A // ¬(P a ∧ Q a)}))
    intro a b h
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun c : {a : A // ¬(P a ∧ Q a)} => c.val) h)
  have hpartitionNat : Nat.card {a : A // P a} + Nat.card {a : A // ¬P a} = Nat.card A := by
    have hle := Fintype.card_subtype_le P
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    omega
  have hpartition : (Nat.card {a : A // P a} : ℚ) +
      Nat.card {a : A // ¬P a} = Nat.card A := by exact_mod_cast hpartitionNat
  have hn : (Nat.card {a : A // ¬P a} : ℚ) ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by exact_mod_cast hnoninj
  have hb : (Nat.card {a : {a : A // P a} // ¬Q a.1} : ℚ) ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by exact_mod_cast hbadInj
  refine ⟨hgood, hb.trans hbadCount, ?_⟩
  linarith

variable {F J : Type*} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] [Fintype J]

/-- Both generic-subspace existence and the conditional Grassmannian bound
follow from the single unconditional parameter-map exceptional bound. -/
theorem generic_subspace_and_probability_of_parameter_error (α : ℚ)
    (hα₀ : 0 ≤ α) (hα : α < 1)
    (herror : (finiteAssignmentProbability (fun x : (Fin 3 × J) → F =>
      ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range)) : ℚ) ≤ α) :
    (∃ S : RankSpace (ZMod 2) (Fin 3 → F) (Fintype.card J), IsGeneric S.1) ∧
      nongenericFraction F (Fintype.card J) ≤ α / (1 - α) := by
  classical
  let V := J → ZMod 2
  let W := Fin 3 → F
  let A := V →ₗ[ZMod 2] W
  let P : A → Prop := fun g => Function.Injective g
  let Q : A → Prop := fun g => IsGeneric g.range
  let : Fintype A := Fintype.ofEquiv ((Fin 3 × J) → F) parameterMapEquiv
  let : Fintype (Submodule (ZMod 2) W) :=
    Fintype.ofInjective (fun S : Submodule (ZMod 2) W => (S : Set W)) SetLike.coe_injective
  let : Fintype (W ≃ₗ[ZMod 2] W) :=
    Fintype.ofInjective (fun a : W ≃ₗ[ZMod 2] W => (a : W → W)) DFunLike.coe_injective
  let : Fintype (UniformSubspaces.Injection (ZMod 2) V W) :=
    inferInstanceAs (Fintype {g : A // Function.Injective g})
  let : Fintype (RankSpace (ZMod 2) W (finrank (ZMod 2) V)) :=
    inferInstanceAs (Fintype {S : Submodule (ZMod 2) W // finrank (ZMod 2) S = finrank (ZMod 2) V})
  have hcount : (Nat.card {g : A // ¬(P g ∧ Q g)} : ℚ) / Nat.card A ≤ α := by
    rw [parameterMap_event_probability (fun g : A => ¬(P g ∧ Q g))] at herror
    exact herror
  have hc := conditioning_counts P Q α hα hcount
  obtain ⟨g, hgP, hgQ⟩ := hc.1
  let J₀ : UniformSubspaces.Injection (ZMod 2) V W := ⟨g, hgP⟩
  have hdim : finrank (ZMod 2) V = Fintype.card J :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hfrac := UniformSubspaces.bad_subspace_bound J₀
    (fun S : RankSpace (ZMod 2) W (finrank (ZMod 2) V) => ¬IsGeneric S.1)
    α α hα₀ hα hc.2.1 (by
      rw [← Nat.card_eq_fintype_card]
      exact hc.2.2)
  refine ⟨?_, ?_⟩
  · refine ⟨⟨g.range, ?_⟩, hgQ⟩
    simpa only [V, Module.finrank_fintype_fun_eq_card] using
      (LinearMap.finrank_range_of_inj hgP)
  · rw [← Nat.card_eq_fintype_card] at hfrac
    change nongenericFraction F (finrank (ZMod 2) V) ≤ α / (1 - α) at hfrac
    simpa only [hdim] using hfrac

/-- The exact v2 genericity statement with a positive numerator fixed before
the extension field.  The property quantifies over every binary linear lift. -/
theorem exists_generic_subspace_error_numerator (J : Type*) [Fintype J] :
    ∃ D : ℕ, 0 < D ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F],
        (D : ℚ) / Fintype.card F < 1 →
        (∃ S : RankSpace (ZMod 2) (Fin 3 → F) (Fintype.card J), IsGeneric S.1) ∧
          nongenericFraction F (Fintype.card J) ≤
            ((D : ℚ) / Fintype.card F) / (1 - (D : ℚ) / Fintype.card F) := by
  obtain ⟨D, hD, hbound⟩ := exists_genericity_error_numerator J
  refine ⟨D, hD, ?_⟩
  intro F _ _ _ _ hsmall
  apply generic_subspace_and_probability_of_parameter_error ((D : ℚ) / Fintype.card F)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hsmall
  exact_mod_cast hbound F

/-- A convenient numerical threshold for choosing one field for finitely
many ranks: `α ≤ min(1/2, ε/2)` is sufficient. -/
theorem conditional_error_le_of_small (α ε : ℚ) (hα : 0 ≤ α)
    (hhalf : α ≤ 1 / 2) (hε : α ≤ ε / 2) : α / (1 - α) ≤ ε := by
  have hd : 0 < 1 - α := by linarith
  apply (div_le_iff₀ hd).mpr
  have hε₀ : 0 ≤ ε := by linarith
  have hprod : 0 ≤ ε * (1 / 2 - α) := mul_nonneg hε₀ (by linarith)
  nlinarith

end UniqueGamesTheorem.Quadratic

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_GenericFieldChoice
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# One field for every rank up to a fixed threshold

The extension degree is chosen using only the rank threshold and the requested
genericity error.  In particular it is fixed before the logical dimension in
the later enlargement construction.  A generic top-rank space exists in the
same field.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators
open UniqueGamesTheorem.Gadget.Orientation

noncomputable section

/-- Simultaneous quantitative genericity, with the precise threshold order
used by the latent gadget.  The conclusion covers rank zero as well. -/
theorem exists_uniform_generic_field (r₀ : ℕ) (ε : ℚ) (hε : 0 < ε) :
    ∃ d : ℕ, 0 < d ∧ r₀ ≤ 3 * d ∧
      (∀ r : ℕ, r ≤ r₀ → nongenericFraction (BinaryField d) r ≤ ε) ∧
      (∃ S : RankSpace (ZMod 2) (Fin 3 → BinaryField d) r₀, IsGeneric S.1) := by
  classical
  have hex (r : ℕ) := exists_generic_subspace_error_numerator (Fin r)
  choose D hD hbound using hex
  let M : ℕ := ∑ r ∈ Finset.range (r₀ + 1), D r
  have hDM (r : ℕ) (hr : r ≤ r₀) : D r ≤ M := by
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 * (M : ℚ)) (2 * (M : ℚ) / ε))
  let d := fieldDegree N r₀
  have hd : 0 < d := fieldDegree_pos N r₀
  have hqN : (N : ℚ) < Fintype.card (BinaryField d) := by
    exact_mod_cast (by
      simpa only [Nat.card_eq_fintype_card] using
        (chosen_binaryField_thresholds N r₀).1)
  have hq : (0 : ℚ) < Fintype.card (BinaryField d) := by
    exact_mod_cast Fintype.card_pos
  have hqM : 2 * (M : ℚ) < Fintype.card (BinaryField d) :=
    (le_max_left _ _).trans_lt (hN.trans hqN)
  have hqε : 2 * (M : ℚ) / ε < Fintype.card (BinaryField d) :=
    (le_max_right _ _).trans_lt (hN.trans hqN)
  have hεq : 2 * (M : ℚ) < (Fintype.card (BinaryField d) : ℚ) * ε :=
    (div_lt_iff₀ hε).mp hqε
  have hsmall (r : ℕ) (hr : r ≤ r₀) :
      (D r : ℚ) / Fintype.card (BinaryField d) ≤ 1 / 2 ∧
      (D r : ℚ) / Fintype.card (BinaryField d) ≤ ε / 2 := by
    have hDr : (D r : ℚ) ≤ M := by exact_mod_cast hDM r hr
    constructor
    · apply (div_le_iff₀ hq).mpr
      nlinarith
    · apply (div_le_iff₀ hq).mpr
      nlinarith
  have hready (r : ℕ) (hr : r ≤ r₀) :=
    hbound r (BinaryField d) (show (D r : ℚ) / Fintype.card (BinaryField d) < 1 by
      have := (hsmall r hr).1
      linarith)
  refine ⟨d, hd, rankThreshold_le_triple_fieldDegree N r₀, ?_, ?_⟩
  · intro r hr
    have hb := (hready r hr).2
    simp only [Fintype.card_fin] at hb
    apply hb.trans
    exact conditional_error_le_of_small _ _
      (div_nonneg (Nat.cast_nonneg _) hq.le) (hsmall r hr).1 (hsmall r hr).2
  · obtain ⟨S, hS⟩ := (hready r₀ le_rfl).1
    refine ⟨⟨S.1, ?_⟩, hS⟩
    simpa only [Fintype.card_fin] using S.2

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_BaseConstruction
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The finite base gadget with arbitrarily small nonlinear change

The harmonic rank and genericity error are chosen first. A single finite field
then supplies all required genericity statements, and the actual recursion is
run to its harmonic depth. The kernel quotient injects the logical alphabet.
Every linear map injective there detects at least one quarter of the noise.
-/

namespace UniqueGamesTheorem.Gadget.BaseConstruction

open Quadratic QuadraticStageNoise Harmonic Parameters
open scoped Classical

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

attribute [local instance] OAI.UniqueGamesTheorem.Gadget.BaseConstruction.indexDecidableEq
local instance indexNonempty : Nonempty (BlockOrientationIndex F) := by
  have hA : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  obtain ⟨A⟩ := hA
  exact ⟨⟨A, chosenBlockOrientation A⟩⟩

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem theta_le_one : fieldLineTheta F ≤ 1 := by
  have hc : (1 : ℚ) ≤ Nat.card (FieldLine F) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (card_FieldLine_pos (F := F)))
  exact (inv_anti₀ (by norm_num : (0 : ℚ) < 1) hc).trans_eq (by norm_num)

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem rate_eq_one_sub_theta : rate F = 1 - fieldLineTheta F := by
  rw [rate, fieldLineTheta_eq, one_div]

/-- Detection for the actual quotient, with every whole-recursion estimate
discharged by the adaptive UniqueGamesTheorem.Gadget.Harmonic.harmonic argument. -/
theorem quotient_detection
    (r₀ : ℕ) (ε : ℚ) (hr₀ : 0 < r₀)
    (hbudget : badRankCoefficient r₀ * ε ≤ 1)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε)
    (S₀ : Submodule (ZMod 2) (Vec F))
    (hrank : Module.finrank (ZMod 2) S₀ = r₀) (hS₀ : IsGeneric S₀)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (T : (quotientStage (F := F) (depth r₀ (fieldLineTheta F))).Input →ₗ[ZMod 2] E)
    (hinj : Function.Injective
      (T.comp (quotientStage (F := F) (depth r₀ (fieldLineTheta F))).embed)) :
    (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
      if T ((quotientStage (F := F) (depth r₀ (fieldLineTheta F))).noise t) ≠ 0
      then 1 else 0) := by
  classical
  let n := depth r₀ (fieldLineTheta F)
  let : Fintype (stage (F := F) n).Noise := DescentProbability.noiseFintype
    (blockEmbedding (F := F)) aggregate_blockEmbedding_surjective Q n
  have hJ : Function.Surjective
      (aggregate (OrientedBlockKernel.orientedBlockLinear (F := F))) := by
    exact aggregate_blockEmbedding_surjective (F := F)
  have hfull : ∀ L : Lift (stage (F := F) n)
      (⊤ : Submodule (ZMod 2) (Module.Dual (ZMod 2) (Vec F))),
      (1 / 4 : ℚ) ≤ probability (fun t => ∃ z, L.family z ((stage n).noise t) ≠ 0) := by
    intro L
    exact BaseDetection.full_lift_detection hJ r₀ ε hr₀ hbudget hgeneric S₀ hrank hS₀ L
  have h := QuotientDetection.target_detection_after_quotient
    (stage (F := F) n) T (1 / 4) hfull hinj
  change (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average
    (fun t : (stage (F := F) n).Noise =>
      if T (StageQuotient.noise (stage (F := F) n) t) ≠ 0 then 1 else 0)
  rw [StageNoiseRecurrence.average_eq_expect]
  exact h

/-- The exact nonlinear recurrence satisfies the scalar budget fixed before
the field was selected. -/
theorem quotient_error_le (p : ℚ) (r₀ : ℕ)
    (hgeom : (1 - fieldLineTheta F) ^ depth r₀ (fieldLineTheta F) ≤ p) :
    StageNoiseRecurrence.error
      (quotientStage (F := F) (depth r₀ (fieldLineTheta F))) ≤ p := by
  rw [quotientStage_error, rate_eq_one_sub_theta]
  have hpow : 0 ≤ (1 - fieldLineTheta F) ^ depth r₀ (fieldLineTheta F) :=
    pow_nonneg (sub_nonneg.mpr theta_le_one) _
  have hcoef : 1 - 1 / (Nat.card F : ℚ) ^ 3 ≤ 1 :=
    sub_le_self _ (by positivity)
  exact (mul_le_of_le_one_left hpow hcoef).trans hgeom

/-- The unconditional finite base endpoint. All choices depend only on `p`;
the larger logical alphabet used by the final enlargement is absent here. -/
theorem exists_base (p : ℚ) (hp : 0 < p) :
    ∃ d : ℕ, 0 < d ∧ ∃ n : ℕ,
      StageNoiseRecurrence.error (quotientStage (F := BinaryField d) n) ≤ p ∧
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
        (T : (quotientStage (F := BinaryField d) n).Input →ₗ[ZMod 2] E),
        Function.Injective (T.comp (quotientStage (F := BinaryField d) n).embed) →
        (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
          if T ((quotientStage (F := BinaryField d) n).noise t) ≠ 0 then 1 else 0) := by
  obtain ⟨r₀, ε, hr₀, hε, _hεone, hbudget, hgeom⟩ := effective_parameters p hp
  obtain ⟨d, hd, _hdim, hgeneric, S₀, hS₀⟩ :=
    exists_uniform_generic_field r₀ ε hε
  refine ⟨d, hd, depth r₀ (fieldLineTheta (BinaryField d)), ?_, ?_⟩
  · exact quotient_error_le p r₀
      (hgeom _ BaseDetection.theta_pos theta_le_one)
  · intro E _ _ T hinj
    exact quotient_detection r₀ ε hr₀ hbudget hgeneric S₀.1 S₀.2 hS₀ T hinj

end

end UniqueGamesTheorem.Gadget.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_Final
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Gadget

open Quadratic QuadraticStageNoise
open UniqueGamesTheorem.Integration.BinaryLinear
open scoped Classical

noncomputable section

/-- Actual finite gadget data, with a rank threshold independent of the final
logical dimension and an arbitrarily small nonlinear change probability. -/
theorem exists_actual_gadget (p : ℚ) (hp : 0 < p) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ ℓ : ℕ, r ≤ ℓ →
      ∃ g : UniqueGamesTheorem.Gadget.ActualGadget.Data (Vector ℓ),
        UniqueGamesTheorem.Gadget.ActualGadget.Satisfies g p (7 / 8) r := by
  obtain ⟨d, _hd, n, herror, hdetect⟩ := BaseConstruction.exists_base p hp
  let B := Vec (BinaryField d)
  let s := quotientStage (F := BinaryField d) n
  let : Fintype B := Fintype.ofFinite _
  let : FiniteDimensional (ZMod 2) B := Module.Finite.of_finite
  let : Fintype s.Input := Fintype.ofFinite _
  let : Fintype s.Noise := Fintype.ofFinite _
  let i : B →ₗ[ZMod 2] s.Input := s.embed
  let r := Module.finrank (ZMod 2) B + 2
  refine ⟨r, by omega, ?_⟩
  intro ℓ hℓ
  have hdim : Module.finrank (ZMod 2) B ≤
      Module.finrank (ZMod 2) (Vector ℓ) := by
    rw [finrank_vector]
    omega
  let b₀ : B := fun _ => 1
  have hb₀ : b₀ ≠ 0 := by
    intro h
    have hzero := congrFun h (0 : Fin 3)
    exact one_ne_zero hzero
  have hequiv : ∀ u (b : B), s.output (u + i b) = s.output u + b := by
    intro u b
    exact s.equivariant u b
  have hc : Enlargement.probability (fun z : s.Input × s.Noise =>
      s.output (z.1 + s.noise z.2) ≠ s.output z.1) ≤ p := by
    rw [← StageData.error_eq_count_probability s]
    exact herror
  have hb : ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
      (U : s.Input →ₗ[ZMod 2] E), Function.Injective (U.comp i) →
      (1 / 4 : ℚ) ≤ Enlargement.probability (fun t => U (s.noise t) ≠ 0) := by
    intro E _ _ U hU
    have h := hdetect E U hU
    rw [StageNoiseRecurrence.average_eq_expect] at h
    refine h.trans_eq ?_
    rw [StageData.count_probability_eq_expect]
    apply Finset.expect_congr rfl
    intro t _
    by_cases ht : U (s.noise t) = 0
    · simp only [s] at ht ⊢
      simp only [ht, ne_eq, not_true_eq_false, ite_false]
    · simp only [s] at ht ⊢
      simp only [ht, ne_eq, not_false_eq_true, ite_true, if_true]
  exact EnlargementEndpoint.exists_data (B := B) (K := Vector ℓ)
    i s.embed_injective s.output hequiv s.noise hdim b₀ hb₀ p hc hb

theorem exists_split_gadget (p : ℚ) (hp : 0 < p) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ ℓ : ℕ, r ≤ ℓ →
      ∃ d : ℕ, ∃ g : UniqueGamesTheorem.Reduction.ActualSource.SplitGadget ℓ d,
        g.stabilityError ≤ p ∧
        ∀ (P : Type) [AddCommGroup P] [Module F2 P]
          (S : UniqueGamesTheorem.Reduction.ActualSource.Ambient ℓ d →ₗ[F2] P),
          r ≤ Module.finrank F2
            (S.comp (UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding ℓ d)).range →
          UniqueGamesTheorem.Integration.SplitGadget.kernelProbability g S ≤ 7 / 8 := by
  obtain ⟨r, hr, hg⟩ := exists_actual_gadget p hp
  refine ⟨r, hr, ?_⟩
  intro ℓ hℓ
  obtain ⟨g, hgood⟩ := hg ℓ hℓ
  exact UniqueGamesTheorem.Integration.SplitGadget.exists_split_gadget_general g hgood

end

end UniqueGamesTheorem.Gadget

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_MatrixGapFromInverseLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The matrix reduction assembled from the gadget and decoder, conditional
on the dimension-uniform shortcode inverse. -/

namespace UniqueGamesTheorem.Decoder.MatrixGap

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Integration

noncomputable section

theorem parameters_of_inverse (hinverse : Inverse.Shortcode.InversePrinciple)
    (p : ℚ) (hp : 0 < p) : Nonempty (Parameters p) := by
  obtain ⟨rstar, hrstar, hgadget⟩ := Gadget.exists_split_gadget p hp
  obtain ⟨P⟩ := MatrixGapChoice.exists_inverse_parameters hinverse rstar
  obtain ⟨d, g, hstable, hkernel⟩ := hgadget P.s P.s_large
  let en := NoiseEnumeration.ofFintype g
  let T := NoiseTables.Table.ofEnumeration g en
  let gT := T.gadget g.f g.equivariant
  have hstableT : gT.stabilityError ≤ p := by
    exact (NoiseTables.Table.stabilityError_ofEnumeration g en).trans_le hstable
  have hkernelT : ∀ (Q : Type) [AddCommGroup Q] [Module F2 Q]
      (L : Ambient P.s d →ₗ[F2] Q),
      rstar ≤ Module.finrank F2 (L.comp (alphabetEmbedding P.s d)).range →
        Integration.SplitGadget.kernelProbability gT L ≤ 7 / 8 := by
    intro Q _ _ L hL
    exact (NoiseTables.Table.kernelProbability_ofEnumeration g en L).trans_le (hkernel Q L hL)
  obtain ⟨m, hm, hlarge, hβ, hβ', htv, hrate⟩ := MatrixGapChoice.exists_cube P d
  refine ⟨{
    k := m ^ 3
    s := P.s
    d := d
    k_pos := Nat.succ_le_iff.mpr (pow_pos hm _)
    s_pos := hrstar.trans P.s_large
    T := T
    f := g.f
    equivariant := g.equivariant
    stability := hstableT
    sound := ?_ }⟩
  intro S hdistinct hopt
  apply address_value_le_of_semantic_acceptance S (m ^ 3) T g.f g.equivariant
  intro labeling
  apply le_of_lt
  by_contra hnot
  have haccept : (99 : ℚ) / 100 ≤ TableKeysGame.acceptanceProbability S (m ^ 3) gT labeling :=
    le_of_not_gt hnot
  have hgood := P.advice (m ^ 3) hlarge S d gT labeling
    (fun L hL => hkernelT (ActualHomogeneous.E (m ^ 3)) L hL) haccept
  exact ActualMatrixContradiction.contradiction S labeling P.α
    (ActualGoodRows.goodRowMass rstar P.s P.r) (1 / (m : ℝ) ^ 2)
    P.positive P.trivial_small hβ hβ' hgood htv hrate hdistinct hopt

end
end UniqueGamesTheorem.Decoder.MatrixGap

end

section

/-! The fixed finite matrix reduction obtained from the latent
gadget, dimension-uniform shortcode inverse, sparse full-table law and private
local decoder. The construction precedes the parity input and its accuracy.
No inverse, noise, spectral, or decoder certificate is supplied as a premise. -/

namespace UniqueGamesTheorem.Decoder.MatrixGap

theorem exists_parameters (p : ℚ) (hp : 0 < p) : Nonempty (Parameters p) :=
  parameters_of_inverse Inverse.ShortcodeTheorem.inversePrinciple p hp

end UniqueGamesTheorem.Decoder.MatrixGap

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ParameterSelection
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The outer error parameters are fixed before the latent gadget or its alphabet.
We use the same positive reciprocal integer for the latent noise budget and
the rounding tolerance. This permitted specialization makes uniform occurrence
rounding an exact fixed-copy operation. The later parity error is chosen only
after the tuple length has been fixed.
-/

namespace UniqueGamesTheorem.ParameterSelection
noncomputable section

/-- Choose the alphabet-independent exponent and both rational budgets using
only the two prescribed real errors. -/
theorem exists_outerParameters (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    Nonempty (OuterParameters ε δ) := by
  obtain ⟨ε₀, hε₀, hεbound⟩ := exists_rat_btwn hε
  obtain ⟨δ₀, hδ₀, hδbound⟩ := exists_rat_btwn hδ
  have hεq : (0 : ℚ) < ε₀ := by exact_mod_cast hε₀
  have hδq : (0 : ℚ) < δ₀ := by exact_mod_cast hδ₀
  obtain ⟨t, ht, hrate⟩ := Repetition.exists_final_repetition_count hδ₀
  have htpos : 0 < t := ht
  obtain ⟨C, hC, hCpos, hCsmall, hCbudget⟩ :=
    Explicit.FinishBounds.exists_reciprocal_tolerance ε₀ hεq t htpos
  exact ⟨⟨ε₀, δ₀, hεq, hδq, hεbound.le, hδbound.le,
    t, htpos, hrate, C, hC, hCpos, hCsmall, hCbudget⟩⟩

end
end UniqueGamesTheorem.ParameterSelection

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Theorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Theorem

theorem exists_binaryGapReduction (ε δ : ℝ)
    (hε : 0 < ε) (_hεhalf : ε < 1 / 2)
    (hδ : 0 < δ) (_hδhalf : δ < 1 / 2) :
    Nonempty (Explicit.MachineOutputContract.BinaryGapReduction ε δ) := by
  obtain ⟨P⟩ := ParameterSelection.exists_outerParameters ε δ hε hδ
  obtain ⟨M⟩ := Decoder.MatrixGap.exists_parameters P.pStar P.pStar_pos
  exact ⟨FromMatrixGap.reduction P M⟩

end UniqueGamesTheorem.Theorem

namespace UniqueGamesTheorem


/-- For every fixed pair of errors in `(0, 1/2)`, binary 3SAT reduces in
polynomial time to translation Unique Games with completeness at least `1 - ε`
and soundness at most `δ`. The alphabet and machine depend only on the errors. -/
theorem theorem11_oai (ε δ : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    Nonempty (Explicit.MachineOutputContract.BinaryGapReduction ε δ) :=
  Theorem.exists_binaryGapReduction ε δ hε hεhalf hδ hδhalf

end UniqueGamesTheorem

end

end OAI
end

theorem solution : type_of% @OAI.UniqueGamesTheorem.theorem11_oai := @OAI.UniqueGamesTheorem.theorem11_oai
