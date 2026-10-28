-- Prove2me | solution 1 for OAI.DFVSGames.Decoder.MatrixGap.parameters_of_inverse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T16:48:13.15198+00:00
-- url     : https://prove2.me/submissions/73183d00-221c-4108-91d6-d4fb06de8e20

import Mathlib
import Definitions.Def_OAIQ085D016
import Definitions.Def_OAIQ085D024
import Theorems.Thm_OAI_DFVSGames_Decoder_ActualMatrixContradiction_contradiction
import Theorems.Thm_OAI_DFVSGames_Gadget_BaseConstruction_exists_base

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_FormulaEncoding
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerModule _root_.OAI.DFVSGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.DFVSGames.Soundness.PartnerLinear.sourceModule _root_.OAI.DFVSGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.DFVSGames.Soundness.RawMapLaw.rawMapsFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Integration.BinaryLinear

open BinaryCoordinates

theorem finrank_vector (n : Nat) : Module.finrank F2 (Vector n) = n := by
  simp [Vector]

end DFVSGames.Integration.BinaryLinear


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_MatrixCharacters
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerModule _root_.OAI.DFVSGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.DFVSGames.Soundness.PartnerLinear.sourceModule _root_.OAI.DFVSGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.DFVSGames.Soundness.RawMapLaw.rawMapsFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Fourier.MatrixParity

open DFVSGames.Integration.BinaryLinear
open scoped Matrix BigOperators Classical

section LinearMaps

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

theorem trace_smulRight_comp [FiniteDimensional F2 C]
    (τ : E →ₗ[F2] F2) (c : C) (S : C →ₗ[F2] E) :
    LinearMap.trace F2 C ((τ.smulRight c).comp S) = τ (S c) := by
  have heq : (τ.smulRight c).comp S = (τ.comp S).smulRight c := by
    ext x
    rfl
  rw [heq, LinearMap.trace_smulRight, LinearMap.comp_apply]

end LinearMaps

open MatrixCharacters hiding F2

end DFVSGames.Fourier.MatrixParity
end

noncomputable section

namespace DFVSGames.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open DFVSGames.Fourier.MatrixCharacters

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

end DFVSGames.Fourier.MatrixFourier
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FinishReduction
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Decoder.SparseLaw

open scoped BigOperators
open DFVSGames.Foundations.Information

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
    by_cases hxy : z.1 = z.2 <;> simp_all [lineCount] ; norm_num

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
end DFVSGames.Decoder.SparseLaw


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KernelCardinality
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Gadget.LinearKernelCount

universe u v

variable {V : Type u} {P : Type v}
variable [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable [AddCommGroup P] [Module (ZMod 2) P]

theorem card_binary_space : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp

theorem kernel_card_mul_pow_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card f.ker * 2 ^ Module.finrank (ZMod 2) f.range = Nat.card V := by
  rw [card_binary_space (V := f.ker), card_binary_space (V := V), ← pow_add]
  congr 1
  rw [Nat.add_comm]
  exact f.finrank_range_add_finrank_ker

theorem zero_event_card_mul_pow_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card {x : V // f x = 0} * 2 ^ Module.finrank (ZMod 2) f.range = Nat.card V :=
  kernel_card_mul_pow_rank f

theorem zero_event_finset_count_mul_pow_rank [Fintype V] [DecidableEq P]
    (f : V →ₗ[ZMod 2] P) :
    (Finset.univ.filter (fun x : V => f x = 0)).card *
      2 ^ Module.finrank (ZMod 2) f.range = Fintype.card V := by
  have h := zero_event_card_mul_pow_rank f
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

end DFVSGames.Gadget.LinearKernelCount


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_Mixture
attribute [-instance] _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Clean

open Foundations.Games
open scoped BigOperators

noncomputable section

variable {E : Type*} [Fintype E] [Nonempty E]

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
end DFVSGames.Clean

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FinalParameters
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Gadget.StageQuotient.spaceFinite _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Quadratic.finiteBlockOrientation _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget.ActualGadget

attribute [instance] Data.ambientAddCommGroup Data.ambientModule Data.ambientFintype
attribute [instance] Data.noiseFintype Data.noiseNonempty

end DFVSGames.Gadget.ActualGadget

namespace DFVSGames.Reduction.ActualSource

open DFVSGames.Integration.BinaryLinear

attribute [instance] SplitGadget.noiseFintype SplitGadget.noiseNonempty

end DFVSGames.Reduction.ActualSource

namespace DFVSGames.Integration.SplitGadget

open BinaryLinear

variable {R : Type} [AddCommGroup R] [Module F2 R] [FiniteDimensional F2 R]

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

open DFVSGames.Gadget.ActualGadget (Data stabilityError failureIndicator kernelError Satisfies)
open DFVSGames.Reduction.ActualSource

theorem transport_stabilityError {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0)) :
    (transport g φ he).stabilityError = stabilityError g := by
  classical
  apply Fintype.expect_equiv (φ.symm.toEquiv.prodCongr (Equiv.refl g.NoiseIndex))
  intro x
  simp [transport, failureIndicator, map_add]

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

end DFVSGames.Integration.SplitGadget

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_MatrixNoise
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerModule _root_.OAI.DFVSGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.DFVSGames.Soundness.PartnerLinear.sourceModule _root_.OAI.DFVSGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.DFVSGames.Soundness.RawMapLaw.rawMapsFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DFVSGames.Fourier.MatrixNoise

open scoped BigOperators Matrix
open DFVSGames.Integration.BinaryLinear (Vector)
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

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

theorem average_smulRight_character [FiniteDimensional F2 F]
    [Fintype (E →ₗ[F2] F2)] (S : F →ₗ[F2] E) (v : F) :
    (𝔼 ℓ : E →ₗ[F2] F2, linearTraceCharacter S (ℓ.smulRight v)) =
      if S v = 0 then (1 : ℂ) else 0 := by
  simp only [linearTraceCharacter_apply, linearTracePair,
    MatrixParity.trace_smulRight_comp]
  exact average_evaluationCharacter _

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

theorem linearRealNoiseOperator_energy (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * linearRealNoiseOperator weight f X) =
      ∑ S : F →ₗ[F2] E, linearNoiseEigenvalue weight S * linearCoeff f S ^ 2 := by
  rw [linearRealNoiseOperator_pairing]
  simp only [pow_two, mul_assoc]

end DFVSGames.Fourier.MatrixNoise
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_CanonicalAddress
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Integration.NoiseTables

open BinaryLinear DFVSGames.Reduction.ActualSource

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
end DFVSGames.Integration.NoiseTables
end

section

namespace DFVSGames.Decoder.MatrixGap

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Foundations.Target
open DFVSGames.Integration
open ActualSource

noncomputable section

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

end DFVSGames.Decoder.MatrixGap
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSingleOrbitBridge
attribute [-instance] _root_.OAI.DFVSGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.DimensionSelection

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
end DFVSGames.Decoder.DimensionSelection

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixNoise

namespace DFVSGames.Decoder.NoiseSampler

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

variable {Noise V E : Type*} [Fintype Noise] [Fintype V]
  [AddCommGroup V] [Module F2 V]
  [AddCommGroup E] [Module F2 E]

theorem sample_kernel_eq_eigenvalue (noise : Noise → V) (S : V →ₗ[F2] E) :
    (𝔼 n, if S (noise n) = 0 then (1 : ℝ) else 0) =
      linearNoiseEigenvalue (samplerLaw noise) S := by
  classical
  exact sample_expect_eq noise (fun v => if S v = 0 then 1 else 0)

end DFVSGames.Decoder.NoiseSampler
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_MatrixEnergy
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Fourier.MatrixEnergy

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

end DFVSGames.Fourier.MatrixEnergy
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PositiveMultiplier
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Gadget.StageQuotient.spaceFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Quadratic.finiteBlockOrientation _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier
open MatrixCharacters MatrixFourier MatrixNoise MatrixEnergy

namespace DFVSGames.Decoder.PositiveMultiplier

section FiniteSpectra

variable {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]

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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 V] [Fintype V] [Fintype (E →ₗ[F2] F2)] [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)] in
theorem color_pair_sum (label : (E →ₗ[F2] V) → C)
    (X Y : E →ₗ[F2] V) :
    (∑ c, colorIndicator label c X * colorIndicator label c Y) =
      if label X = label Y then (1 : ℝ) else 0 := by
  classical
  simp [colorIndicator, eq_comm]

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
      (DFVSGames.Gadget.LinearKernelCount.zero_event_finset_count_mul_pow_rank (S.comp ι))
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

end DFVSGames.Decoder.PositiveMultiplier
end

noncomputable section

open scoped BigOperators

namespace DFVSGames.Fourier.SplitMaps

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

end DFVSGames.Fourier.SplitMaps
end

namespace DFVSGames.Decoder.SurrogateFibers

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Fourier
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

omit [Fintype K] [Fintype W] [Fintype (E →ₗ[F2] F2)] [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] W)] [Fintype (E →ₗ[F2] K × W)] in
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
end DFVSGames.Decoder.SurrogateFibers

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Reduction.ActualSource
open DFVSGames.Fourier.MatrixNoise

namespace DFVSGames.Decoder.ActualSpectral

open TableKeysGame PositiveMultiplier NoiseSampler SurrogateFibers

theorem expect_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    (𝔼 p, f p) = 𝔼 a, 𝔼 b, f (a, b) := by
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product Finset.univ Finset.univ f)

theorem expect_eq_uniform_sum {I : Type*} [Fintype I] (f : I → ℝ) :
    (𝔼 i, f i) = ∑ i, (Fintype.card I : ℝ)⁻¹ * f i := by
  rw [Fintype.expect_eq_sum_div_card, ← Finset.mul_sum]
  ring

attribute [local instance] OAI.DFVSGames.Decoder.ActualSpectral.homFintype
theorem eigenvalue_eq_kernelProbability {s d : Nat} (g : SplitGadget s d)
    {P : Type} [AddCommGroup P] [Module F2 P] (S : Ambient s d →ₗ[F2] P) :
    linearNoiseEigenvalue (samplerLaw g.noise) S =
      (Integration.SplitGadget.kernelProbability g S : ℝ) := by
  rw [← sample_kernel_eq_eigenvalue]
  unfold Integration.SplitGadget.kernelProbability
  rw [rat_expect_cast]
  simp only [apply_ite, Rat.cast_one, Rat.cast_zero]

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

end DFVSGames.Decoder.ActualSpectral
end

namespace DFVSGames.Inverse.RowErasure

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
end DFVSGames.Inverse.RowErasure

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_RowErasureSlices
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.RowErasure

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
end DFVSGames.Inverse.RowErasure

namespace DFVSGames.Inverse.RowErasure

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
  convert h using 1 <;> first | rfl | ring

end
end DFVSGames.Inverse.RowErasure

namespace DFVSGames.Inverse.RowErasureDescriptions

open DFVSGames.Inverse.Shortcode
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
end DFVSGames.Inverse.RowErasureDescriptions

namespace DFVSGames.Inverse.RowErasureMatrix

open DFVSGames.Inverse.Shortcode
open DFVSGames.Inverse.RowErasure
open DFVSGames.Inverse.RowErasureDescriptions
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
end DFVSGames.Inverse.RowErasureMatrix

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AffineWitnessNormalization
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Gadget.StageQuotient.spaceFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Quadratic.finiteBlockOrientation _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.Shortcode

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

theorem card_directions_le (S : Slice ell m) (hne : S.points.Nonempty) :
    Nat.card S.Directions ≤ S.points.card := by
  obtain ⟨M, hM⟩ := hne
  have hcontains : S.Contains M := by simpa only [points, Finset.mem_filter,
    Finset.mem_univ, true_and] using hM
  simpa only [Nat.card_eq_finsetCard] using
    Nat.card_le_card_of_injective (S.directionEmbedding M hcontains)
      (S.directionEmbedding M hcontains).injective

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
end DFVSGames.Inverse.Shortcode

namespace DFVSGames.Decoder.MatrixCoordinates

open Integration.BinaryLinear Reduction
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem indicator_congr_inline_MatrixCoordinates (P Q : Prop) (dP : Decidable P) (dQ : Decidable Q)
    (h : P ↔ Q) : @ite ℝ P dP 1 0 = @ite ℝ Q dQ 1 0 := by
  cases propext h
  cases Subsingleton.elim dP dQ
  rfl

attribute [local instance] OAI.DFVSGames.Decoder.MatrixCoordinates.homFintype
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
  exact indicator_congr_inline_MatrixCoordinates _ _ _ _ Iff.rfl

end
end DFVSGames.Decoder.MatrixCoordinates

namespace DFVSGames.Inverse.RowErasure

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

private theorem exp_half_le_seven_quarters_inline_RowErasureConcentration : Real.exp (1 / 2 : ℝ) ≤ 7 / 4 := by
  have h := Real.exp_bound' (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem exp_half_indicator_inline_RowErasureConcentration (P : Prop) :
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
      simp_rw [hP, true_and, exp_half_indicator_inline_RowErasureConcentration]
      rw [Finset.expect_add_distrib, ← Finset.mul_expect, hsingle]
      simp [div_eq_mul_inv]
    rw [heq]
    calc
      1 + (Real.exp (1 / 2 : ℝ) - 1) / (Fintype.card Y : ℝ) ≤
          1 + 3 / (4 * (Fintype.card Y : ℝ)) := by
        have h := div_le_div_of_nonneg_right
          (show Real.exp (1 / 2 : ℝ) - 1 ≤ 3 / 4 by
            linarith [exp_half_le_seven_quarters_inline_RowErasureConcentration]) hcard.le
        simpa only [div_div, add_comm] using add_le_add_left h 1
      _ ≤ Real.exp (3 / (4 * (Fintype.card Y : ℝ))) := by
        simpa only [add_comm] using Real.add_one_le_exp (3 / (4 * (Fintype.card Y : ℝ)))
  · simp only [hP, false_and, indicator_false, zero_div, Real.exp_zero,
      Fintype.expect_const]
    exact Real.one_le_exp (by positivity)

end
end DFVSGames.Inverse.RowErasure

namespace DFVSGames.Inverse.RowErasure

open scoped BigOperators Classical

noncomputable section

private theorem randomizedMatches_eq_masked_sum_inline_RowErasureTail
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

private theorem randomizedMatches_exp_product_inline_RowErasureTail
    {X Y : Type*} [Fintype X] (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) :
    Real.exp (randomizedMatches s B target replacement / 2) =
      ∏ x, Real.exp (indicator (x ∈ s ∧ B x ∧ replacement x = target x) / 2) := by
  rw [randomizedMatches_eq_masked_sum_inline_RowErasureTail]
  simp only [div_eq_mul_inv, Finset.sum_mul, Real.exp_sum]

private theorem table_randomizedMatches_mgf_eq_inline_RowErasureTail
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
      exact randomizedMatches_exp_product_inline_RowErasureTail s B target replacement
    _ = _ := table_expect_prod (X := X) (Y := Y)
      (fun x y => Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))

private theorem table_randomizedMatches_product_le_inline_RowErasureTail
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
  rw [table_randomizedMatches_mgf_eq_inline_RowErasureTail]
  exact table_randomizedMatches_product_le_inline_RowErasureTail s B target

theorem uniformMass_mono {R : Type*} [Fintype R]
    {p q : R → Prop} (h : ∀ r, p r → q r) : uniformMass p ≤ uniformMass q := by
  classical
  apply Finset.expect_le_expect
  intro r _
  by_cases hp : p r
  · simp [indicator, hp, h r hp]
  · simpa [indicator, hp] using indicator_nonneg (q r)

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
end DFVSGames.Inverse.RowErasure

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ActualGoodRows
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.RowErasureMatrix

open DFVSGames.Inverse.Shortcode
open DFVSGames.Inverse.RowErasure
open DFVSGames.Inverse.RowErasureDescriptions
open scoped BigOperators

noncomputable section

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
end DFVSGames.Inverse.RowErasureMatrix

namespace DFVSGames.Inverse.RowErasure

open Filter
open scoped Topology

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

theorem exists_unionBound_threshold (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → r ≤ m ∧
      (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) < 1 := by
  exact eventually_atTop.1 ((eventually_ge_atTop r).and
    (eventually_unionBound_lt_one α hα ell r hr))

end DFVSGames.Inverse.RowErasure

namespace DFVSGames.Inverse.RowErasureMatrix

open DFVSGames.Inverse.Shortcode
open DFVSGames.Inverse.RowErasure
open DFVSGames.Inverse.RowErasureDescriptions
open scoped BigOperators

noncomputable section

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
end DFVSGames.Inverse.RowErasureMatrix

namespace DFVSGames.Decoder.ActualGoodRows

open Integration.BinaryLinear Reduction ActualSource
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat HasAffineSlice)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] OAI.DFVSGames.Decoder.ActualGoodRows.homFintype
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
end DFVSGames.Decoder.ActualGoodRows

namespace DFVSGames.Decoder.ConstantSelection

open DFVSGames.Foundations.Information
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

theorem cube_exponential_antitone {m n : ℕ} (hmn : m ≤ n)
    {N : ℝ} (hN : 0 < N) :
    Real.exp (-(n : ℝ) / (3600 * N)) ≤
      Real.exp (-(m : ℝ) / (3600 * N)) := by
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact neg_le_neg (by exact_mod_cast hmn)

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
end DFVSGames.Decoder.ConstantSelection

namespace DFVSGames.Decoder.MatrixGapChoice

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
end DFVSGames.Decoder.MatrixGapChoice

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_DescentProbability
attribute [-instance] _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget.Quotient

variable {𝕜 P B : Type*} [Ring 𝕜]
variable [AddCommGroup P] [Module 𝕜 P] [AddCommGroup B] [Module 𝕜 B]

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

theorem fiber_card (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (x : Space R lam) :
    Nat.card {u : P // projection R lam u = x} = Nat.card (shiftKernel R lam) := by
  obtain ⟨a, rfl⟩ := projection_surjective R lam x
  exact (Nat.card_congr (Equiv.ofBijective _ (fiberMap_bijective R lam a))).symm

end DFVSGames.Gadget.Quotient

namespace DFVSGames.Gadget.StageQuotient

universe u v

variable {k : Type u} {B : Type v} [CommRing k]
variable [AddCommGroup B] [Module k B]

theorem noise_change_iff (s : Stage k B) (u : s.Input) (t : s.Noise) :
    (output s (projection s u + noise s t) ≠ output s (projection s u)) ↔
      s.output (u + s.noise t) ≠ s.output u :=
  Quotient.change_iff (shifts s) (logical s) s.output (equivariant s) u (s.noise t)

end DFVSGames.Gadget.StageQuotient

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_NonlinearRecurrence
attribute [-instance] _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget.StageNoiseRecurrence

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

end DFVSGames.Gadget.StageNoiseRecurrence

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_Enlargement
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget.Enlargement

open scoped BigOperators Classical

noncomputable section

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

theorem pullback_ne_top_iff {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [FiniteDimensional F B] [AddCommGroup K] [Module F K]
    (L : B →ₗ[F] K) (S : Submodule F (Module.Dual F K)) :
    S.map L.dualMap ≠ ⊤ ↔ ∃ b : B, b ≠ 0 ∧ L b ∈ S.dualCoannihilator := by
  let W := S.map L.dualMap
  have hann : W.dualCoannihilator = S.dualCoannihilator.comap L := by
    ext b
    simp only [Submodule.mem_dualCoannihilator, Submodule.mem_comap,
      ]
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

theorem nonzero_density_le (d r : ℕ) (h : 0 < d + r) :
    ((2 : ℚ) ^ d - 1) / ((2 : ℚ) ^ (d + r) - 1) ≤ 1 / (2 : ℚ) ^ r := by
  have hpow : 1 < (2 : ℚ) ^ (d + r) := one_lt_pow₀ (by norm_num) (by omega)
  have hr : (1 : ℚ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  rw [pow_add]
  nlinarith

theorem card_nonzero_binary (K : Type*) [AddCommGroup K] [Module (ZMod 2) K]
    [Fintype K] :
    Nat.card {x : K // x ≠ 0} = 2 ^ Module.finrank (ZMod 2) K - 1 := by
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : K => x = 0), Fintype.card_subtype_eq]
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

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
  push_cast ; rfl

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

theorem union_bound_le_quarter (b r : ℕ) (hr : b + 2 ≤ r) :
    ((2 : ℚ) ^ b - 1) / (2 : ℚ) ^ r ≤ 1 / 4 := by
  have hpow : (2 : ℚ) ^ (b + 2) ≤ (2 : ℚ) ^ r :=
    pow_le_pow_right₀ (by norm_num) hr
  rw [pow_add] at hpow
  norm_num at hpow
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ r)).2
  nlinarith [show (0 : ℚ) ≤ 2 ^ b by positivity]

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

end DFVSGames.Gadget.Enlargement

noncomputable section

namespace DFVSGames.Gadget.EnlargementConstruction

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

theorem probability_prod_average_right {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p : Ω → Ξ → Prop) :
    probability (fun z : Ω × Ξ => p z.1 z.2) =
      (∑ y : Ξ, probability (fun x : Ω => p x y)) /
        (Fintype.card Ξ : ℚ) := by
  classical
  simp_rw [probability_eq_sum_indicator]
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type_right,
    ← Finset.sum_div, div_div]

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

private theorem update_canonical {A B : Type*} (d : DecidableEq A) (f : A → B) (a : A) (b : B) :
    @Function.update A (fun _ => B) d f a b =
      @Function.update A (fun _ => B) (Classical.typeDecidableEq A) f a b := by
  cases Subsingleton.elim d (Classical.typeDecidableEq A : DecidableEq A)
  rfl

private theorem probability_pointwise {A : Type*} (i j : Fintype A) (p q : A → Prop)
    (h : ∀ a, p a ↔ q a) : @probability A i p = @probability A j q := by
  unfold probability
  have he : p = q := funext (fun a => propext (h a))
  rw [he]

attribute [local instance] OAI.DFVSGames.Gadget.EnlargementConstruction.enlargementCopiesFintype
omit [FiniteDimensional (ZMod 2) B] [Fintype K] [FiniteDimensional (ZMod 2) K] [Module (ZMod 2) V] [Fintype V] in
theorem add_single_eq_update (x : Copies B K → V) (L : Copies B K) (a : V) :
    x + Pi.single L a = Function.update x L (x L + a) := by
  funext J
  by_cases h : J = L
  · subst J
    simp
  · simp [h]

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
  have h := enlargedOutput_update_ne_iff C x L (x L + noise n)
  simp only [update_canonical] at h ⊢
  exact h

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

omit [Fintype B] [FiniteDimensional (ZMod 2) B] [Fintype K] [FiniteDimensional (ZMod 2) K] in
theorem dual_pullback_eq_top_iff {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (A : K →ₗ[ZMod 2] E) (L : B →ₗ[ZMod 2] K) :
    (LinearMap.range A.dualMap).map L.dualMap = ⊤ ↔ Function.Injective (A.comp L) := by
  rw [← LinearMap.range_comp, LinearMap.dualMap_comp_dualMap,
    LinearMap.range_eq_top, LinearMap.dualMap_surjective_iff]

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
      apply probability_pointwise
      intro z
      have h₁ := change_iff i hi C hC noise hdim b₀ hb₀ z.1 z.2.1 z.2.2
      have h₂ := enlargedOutput_update_ne_iff C z.1 z.2.1 (z.1 z.2.1 + noise z.2.2)
      simp only [update_canonical] at h₁ h₂ ⊢
      have hc := h₁.trans h₂.symm

      erw [update_canonical] at hc
      exact hc
    _ = _ := by
      have hh := enlarged_random_copy_probability (F := ZMod 2) (K := K) C noise
      simp only [update_canonical] at hh ⊢
      unfold probability at hh ⊢
      exact hh

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

end DFVSGames.Gadget.EnlargementConstruction
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_StageData
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Gadget.StageData

open scoped BigOperators Classical
open DFVSGames.Gadget

variable {C : Type} [AddCommGroup C] [Module (ZMod 2) C]

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

end DFVSGames.Gadget.StageData
end

noncomputable section

namespace DFVSGames.Gadget.EnlargementEndpoint

open scoped Classical
open Enlargement EnlargementConstruction
open DFVSGames.Gadget

variable {B K V N : Type}
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
variable [FiniteDimensional (ZMod 2) B]
variable [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
variable [FiniteDimensional (ZMod 2) K]
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype N] [Nonempty N]

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

end DFVSGames.Gadget.EnlargementEndpoint
end

namespace DFVSGames.Gadget

open Quadratic QuadraticStageNoise
open DFVSGames.Integration.BinaryLinear
open scoped Classical

noncomputable section

theorem exists_actual_gadget (p : ℚ) (hp : 0 < p) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ ℓ : ℕ, r ≤ ℓ →
      ∃ g : DFVSGames.Gadget.ActualGadget.Data (Vector ℓ),
        DFVSGames.Gadget.ActualGadget.Satisfies g p (7 / 8) r := by
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
      ∃ d : ℕ, ∃ g : DFVSGames.Reduction.ActualSource.SplitGadget ℓ d,
        g.stabilityError ≤ p ∧
        ∀ (P : Type) [AddCommGroup P] [Module F2 P]
          (S : DFVSGames.Reduction.ActualSource.Ambient ℓ d →ₗ[F2] P),
          r ≤ Module.finrank F2
            (S.comp (DFVSGames.Reduction.ActualSource.alphabetEmbedding ℓ d)).range →
          DFVSGames.Integration.SplitGadget.kernelProbability g S ≤ 7 / 8 := by
  obtain ⟨r, hr, hg⟩ := exists_actual_gadget p hp
  refine ⟨r, hr, ?_⟩
  intro ℓ hℓ
  obtain ⟨g, hgood⟩ := hg ℓ hℓ
  exact DFVSGames.Integration.SplitGadget.exists_split_gadget_general g hgood

end

end DFVSGames.Gadget

namespace DFVSGames.Decoder.MatrixGap

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Integration

noncomputable section

theorem parameters_of_inverse_oai (hinverse : Inverse.Shortcode.InversePrinciple)
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
end DFVSGames.Decoder.MatrixGap

end OAI
end

theorem solution : type_of% @OAI.DFVSGames.Decoder.MatrixGap.parameters_of_inverse_oai := @OAI.DFVSGames.Decoder.MatrixGap.parameters_of_inverse_oai
