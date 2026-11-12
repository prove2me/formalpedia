-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionFamily.fixed_allocation_constraint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:24:34.415946+00:00
-- url     : https://prove2.me/submissions/7be34e41-7107-44c8-8164-c61ac02903b4

import Mathlib
import Definitions.Def_MatrixFields
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupSelection_exists_threshold_eventually_selected
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialChoice_eventually_nonempty
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_Arithmetic_equalVolume_inequality_of_polynomialApproximation

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_StageCLaw
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators

theorem stageCWeight_single (t u : Shape) :
    stageCWeight t u 0 + stageCWeight t u 1 = binaryParameter t u := by
  change binaryParameter t u / 2 + binaryParameter t u / 2 = binaryParameter t u
  ring

theorem stageCWeight_cross (t u : Shape) :
    stageCWeight t u 2 + stageCWeight t u 3 = 1 - binaryParameter t u := by
  change (1 - binaryParameter t u) / 2 + (1 - binaryParameter t u) / 2 =
    1 - binaryParameter t u
  ring

end MatrixMultiplication.AllFieldHistory

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

theorem entropyTerm_mul (p q : ℝ) :
    entropyTerm (p * q) = q * entropyTerm p + p * entropyTerm q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [entropyTerm, Real.log_mul hp hq]
  unfold entropyTerm
  ring

end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_PopulationCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldPopulationCounts

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem blockLength_pos (w : I → ℚ) {m : ℕ} (hm : 0 < m) :
    0 < blockLength w m := Nat.mul_pos hm (denominator_pos w)

end

end MatrixMultiplication.AllFieldPopulationCounts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InverseLinearRecovery
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.ExactRecovery

variable {K X Y Z I A B C : Type*} [CommSemiring K]

theorem card_mask_rectangles [Fintype I] :
    Fintype.card (Finset I × Finset I × Finset I) = 2 ^ (3 * Fintype.card I) := by
  classical
  simp only [Fintype.card_prod, Fintype.card_finset]
  rw [Nat.mul_comm 3 (Fintype.card I), pow_mul]
  simp [pow_succ, mul_assoc]

end MatrixMultiplication.ExactRecovery

end




section
noncomputable section

namespace MatrixMultiplication.RecoveryGrowth

open Filter
open scoped Topology BigOperators

theorem shiftCount_div_nat_le {b C : ℝ} {N : ℕ}
    (hb : 0 < b) (hC : 0 < C) (hN : 3 * C < (N : ℝ)) :
    (shiftCount b C N : ℝ) / (N : ℝ) ≤
      (b + 1) / Real.log ((N : ℝ) / (3 * C)) + 1 / (N : ℝ) := by
  have hC3 : 0 < 3 * C := by linarith
  have hN0 : 0 < (N : ℝ) := hC3.trans hN
  have hlog : 0 < Real.log ((N : ℝ) / (3 * C)) :=
    Real.log_pos ((one_lt_div hC3).2 hN)
  have harg : 0 ≤ (b + 1) * (N : ℝ) / Real.log ((N : ℝ) / (3 * C)) :=
    div_nonneg (mul_nonneg (by linarith) hN0.le) hlog.le
  have hceil := div_le_div_of_nonneg_right (Nat.ceil_lt_add_one harg).le hN0.le
  change (shiftCount b C N : ℝ) / (N : ℝ) ≤ _ at hceil
  convert hceil using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hN0.ne', hlog.ne']

theorem tendsto_shiftCount_div_nat {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    Tendsto (fun N : ℕ => (shiftCount b C N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) / (3 * C))) atTop atTop :=
    Real.tendsto_log_atTop.comp (hnat.atTop_div_const (by linarith))
  have hmain : Tendsto (fun N : ℕ =>
      (b + 1) / Real.log ((N : ℝ) / (3 * C))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have herr : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using hmain.add herr)
  · exact Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [hnat.eventually_gt_atTop (3 * C)] with N hN
    exact shiftCount_div_nat_le hb hC hN

theorem log_replicationCount (b C : ℝ) (N : ℕ) :
    Real.log (replicationCount b C N : ℝ) =
      (3 * Real.log 2) * (shiftCount b C N : ℝ) := by
  simp only [replicationCount, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem tendsto_log_replicationCount_div_nat {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    Tendsto (fun N : ℕ => Real.log (replicationCount b C N : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  have h := (tendsto_shiftCount_div_nat hb hC).const_mul (3 * Real.log 2)
  simp only [mul_zero] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  simp only [log_replicationCount]
  ring

theorem tendsto_log_prod_div_nat {J : Type*} (s : Finset J)
    {r : J → ℕ → ℕ}
    (hr : ∀ j ∈ s, ∀ N, 0 < r j N)
    (hlim : ∀ j ∈ s, Tendsto (fun N => Real.log (r j N : ℝ) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N => Real.log ((∏ j ∈ s, r j N : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum s hlim
  simp only [Finset.sum_const_zero] at hsum
  apply hsum.congr
  intro N
  rw [Nat.cast_prod, Real.log_prod
    (fun j hj => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hr j hj N)))]
  simp only [div_eq_mul_inv, Finset.sum_mul]

end MatrixMultiplication.RecoveryGrowth

end
end




section
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.InverseLinearRecovery

theorem card_recovery_copies (b C : ℝ) (N : ℕ) :
    Fintype.card (MaskRectangles (RecoveryGrowth.shiftCount b C N)) =
      RecoveryGrowth.replicationCount b C N := by
  simpa only [MaskRectangles, Fintype.card_fin, RecoveryGrowth.replicationCount] using
    (ExactRecovery.card_mask_rectangles (I := Fin (RecoveryGrowth.shiftCount b C N)))

theorem subexponential_copies {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    Filter.Tendsto (fun N : ℕ =>
      Real.log (Fintype.card (MaskRectangles (RecoveryGrowth.shiftCount b C N))) / N)
      Filter.atTop (nhds 0) := by
  simp_rw [card_recovery_copies]
  exact RecoveryGrowth.tendsto_log_replicationCount_div_nat hb hC

end MatrixMultiplication.InverseLinearRecovery

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_InitialState
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.terminalExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.sidePermutation_refl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.retarget_copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

namespace AllFieldWitness

variable {F : Type*} [Field F]

theorem volume_pos (W : AllFieldWitness F) : 0 < W.volume :=
  Nat.mul_pos (Nat.mul_pos W.rows_pos W.inner_pos) W.columns_pos

theorem finite_inequality (W : AllFieldWitness F) :
    (W.multiplicity : ℝ) * (W.volume : ℝ) ^ (Arithmetic.omega F / 3) ≤ W.rankBound :=
  Arithmetic.equalVolume_inequality_of_polynomialApproximation
    W.rows_pos W.inner_pos W.columns_pos W.approximation

theorem log_inequality (W : AllFieldWitness F) :
    Real.log (W.multiplicity : ℝ) +
      (Arithmetic.omega F / 3) * Real.log (W.volume : ℝ) ≤
        Real.log (W.rankBound : ℝ) := by
  have hm : (0 : ℝ) < W.multiplicity := Nat.cast_pos.mpr W.multiplicity_pos
  have hv : (0 : ℝ) < W.volume := Nat.cast_pos.mpr W.volume_pos
  have hp := Real.rpow_pos_of_pos hv (Arithmetic.omega F / 3)
  have h := Real.log_le_log (mul_pos hm hp) W.finite_inequality
  rw [Real.log_mul hm.ne' hp.ne', Real.log_rpow hv] at h
  exact h

end AllFieldWitness
end MatrixMultiplication

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldFiniteFamily

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

variable {F : Type*} [Field F]

namespace Execution

variable {SX SY SZ X Y Z X' Y' Z' : Type}
  [Fintype SX] [Fintype SY] [Fintype SZ]
  [Fintype X] [Fintype Y] [Fintype Z]
  {source : Tensor F SX SY SZ} {current : Tensor F X Y Z}

@[simp] theorem extractSelectedAndRepair_copies (E : Execution source current)
    {I J : Type} [Fintype I] [Fintype J]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent current assignment)
    (select : J → I) (injective : Function.Injective select)
    (ideal : J → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ j, InverseLinearRecovery.RecoveredBy (ideal j)
      (JointExtraction.branch current assignment (select j)) L) :
    Fintype.card
      (E.extractSelectedAndRepair assignment coherent select injective ideal L repair).Copies =
      2 ^ (3 * L) * Fintype.card E.Copies := by
  change Fintype.card (InverseLinearRecovery.MaskRectangles L × E.Copies) = _
  rw [Fintype.card_prod, ExactRecovery.card_mask_rectangles, Fintype.card_fin]

end Execution

end MatrixMultiplication.AllFieldFiniteFamily

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistorySums
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

 theorem initial_history_sum (K : ℕ) (f : Shape → ℝ) :
    (∑ h : Initial K, (initialAmount h : ℝ) * f (initialShape h)) =
      (K : ℝ) * (sortedInitial.map (fun g => (initialLaw g : ℝ) * f g)).sum := by
  simp only [Fintype.sum_prod_type, initialAmount, initialShape, List.get_eq_getElem]
  simp_rw [Fin.sum_univ_fun_getElem sortedInitial (fun g => (initialLaw g : ℝ) * f g)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_InitialLeafRates
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instDecidableEqResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

theorem entropy_two_points {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A) (hab : a ≠ b) (p q : ℝ) :
    finiteEntropy (fun i => if i = a then p else if i = b then q else 0) =
      entropyTerm p + entropyTerm q := by
  unfold finiteEntropy
  calc
    _ = ∑ i : A, ((if i = a then entropyTerm p else 0) +
        (if i = b then entropyTerm q else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = a
      · subst i
        simp [hab]
      · by_cases hj : i = b
        · subst i
          simp [hab.symm]
        · simp [hi, hj]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem weighted_two_points {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A) (hab : a ≠ b) (p q : ℝ) (f : A → ℝ) :
    (∑ i : A, (if i = a then p else if i = b then q else 0) * f i) =
      p * f a + q * f b := by
  calc
    _ = ∑ i : A, ((if i = a then p * f a else 0) +
        (if i = b then q * f b else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = a
      · subst i
        simp [hab]
      · by_cases hj : i = b
        · subst i
          simp [hi]
        · simp [hi, hj]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem statisticLaw_two_real (d : ℚ) (i : Fin 6) :
    (statisticLaw d 2 i : ℝ) =
      if i = 2 then 1 - (d : ℝ) else if i = 3 then (d : ℝ) else 0 := by
  by_cases hi : i = 2
  · simp [statisticLaw, hi]
  · by_cases hj : i = 3 <;> simp [statisticLaw, hi, hj]

theorem statisticRate_two (d : ℚ) :
    statisticRate d 2 = binaryEntropyRate d + 2 * (1 - (d : ℝ)) * Real.log 5 := by
  unfold statisticRate
  simp_rw [statisticLaw_two_real]
  rw [entropy_two_points (2 : Fin 6) 3 (by decide),
    weighted_two_points (2 : Fin 6) 3 (by decide)]
  have h25 : Real.log (25 : ℝ) = 2 * Real.log 5 := by
    have hp : (5 : ℝ) ^ 2 = 25 := by norm_num
    rw [← hp, Real.log_pow]
    norm_num
  change entropyTerm (1 - (d : ℝ)) + entropyTerm (d : ℝ) +
    ((1 - (d : ℝ)) * Real.log 25 + (d : ℝ) * Real.log 2) = _
  rw [h25]
  unfold binaryEntropyRate
  ring

theorem statisticRate_deterministic (d : ℚ) (k : Fin 5) (hk : k.val ≠ 2) :
    statisticRate d k = Real.log (multiplicity (singletonSlot k.val) : ℝ) := by
  have hmass (i : Fin 6) : (statisticLaw d k i : ℝ) =
      if i = singletonSlot k.val then 1 else 0 := by
    by_cases hi : i = singletonSlot k.val <;> simp [statisticLaw, hk, hi]
  unfold statisticRate finiteEntropy
  simp_rw [hmass]
  simp [entropyTerm, apply_ite]

theorem statisticRate_three (d : ℚ) : statisticRate d 3 = Real.log 10 := by
  rw [statisticRate_deterministic d 3 (by decide)]
  change Real.log (10 : ℝ) = Real.log 10
  rfl

theorem statisticRate_four (d : ℚ) : statisticRate d 4 = 0 := by
  rw [statisticRate_deterministic d 4 (by decide)]
  have hv : multiplicity (singletonSlot (4 : Fin 5).val) = 1 := by decide +kernel
  rw [hv]
  norm_num

end

end MatrixMultiplication.AllFieldParameters

noncomputable section

namespace MatrixMultiplication.AllFieldTerminalRates

open AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

private theorem four_zero_max : ∀ u ∈ shapes 4, positive u = false →
    shapeMax u = 2 ∨ shapeMax u = 3 ∨ shapeMax u = 4 := by
  decide +kernel

private theorem four_positive_max : ∀ u ∈ shapes 4, positive u = true →
    shapeMax u = 2 := by
  decide +kernel

theorem secondLeafRate_zero (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) (hz : positive u = false) :
    secondLeafRate t u = statisticRate (binaryParameter t u)
      ⟨shapeMax u, second_shapeMax_lt_five t ht u hu⟩ := by
  rcases four_zero_max u (stageB_children_size t ht u hu) hz with h2 | h3 | h4
  · have hk : (⟨shapeMax u, second_shapeMax_lt_five t ht u hu⟩ : Fin 5) = 2 :=
      Fin.ext h2
    rw [hk, statisticRate_two]
    simp [secondLeafRate, h2, hz]
  · have hk : (⟨shapeMax u, second_shapeMax_lt_five t ht u hu⟩ : Fin 5) = 3 :=
      Fin.ext h3
    rw [hk, statisticRate_three]
    simp [secondLeafRate, h3]
  · have hk : (⟨shapeMax u, second_shapeMax_lt_five t ht u hu⟩ : Fin 5) = 4 :=
      Fin.ext h4
    rw [hk, statisticRate_four]
    simp [secondLeafRate, h4]

theorem secondLeafRate_positive (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) (hp : positive u = true) :
    secondLeafRate t u = (2 - (binaryParameter t u : ℝ)) * Real.log 5 := by
  have hm := four_positive_max u (stageB_children_size t ht u hu) hp
  simp [secondLeafRate, hm, hp]

private theorem list_filter_sum_inline_MatrixMultiplication_AllFieldTerminalRateFormulas {A : Type*} (xs : List A) (p : A → Bool)
    (f : A → ℝ) :
    ((xs.filter p).map f).sum = (xs.map (fun a => if p a then f a else 0)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases hp : p a <;> simp [hp, ih]

theorem initial_zero_history_rate (K : ℕ) :
    (∑ h : {h : Initial K // initialShape h ∉ positiveInitial},
      (initialAmount h.val : ℝ) * initialRate (initialShape h.val)) = (K : ℝ) * S0 := by
  calc
    _ = ∑ h : Initial K, if initialShape h ∉ positiveInitial then
        (initialAmount h : ℝ) * initialRate (initialShape h) else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype
        (p := fun h : Initial K => initialShape h ∉ positiveInitial)
        (Finset.univ.filter (fun h : Initial K => initialShape h ∉ positiveInitial))
        (by simp)
        (fun h : Initial K => (initialAmount h : ℝ) * initialRate (initialShape h))).symm
    _ = ∑ h : Initial K, (initialAmount h : ℝ) *
        (if initialShape h ∉ positiveInitial then initialRate (initialShape h) else 0) := by
      apply Finset.sum_congr rfl
      intro h _
      split_ifs <;> simp
    _ = _ := by
      rw [initial_history_sum K
        (fun g => if g ∉ positiveInitial then initialRate g else 0), S0, list_filter_sum_inline_MatrixMultiplication_AllFieldTerminalRateFormulas]
      apply congrArg (fun x : ℝ => (K : ℝ) * x)
      apply congrArg List.sum
      apply List.map_congr_left
      intro g hg
      cases hp : positive g <;> simp [positiveInitial, hg, hp]

end MatrixMultiplication.AllFieldTerminalRates

namespace MatrixMultiplication.AllFieldInitialLeafRates

open AllFieldHistory AllFieldParameters AllFieldTerminalRates
open CWWindowedLeaves Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

theorem card_alphabet {K : ℕ} (h : InitialZero K) :
    Fintype.card (Alphabet 8 (shapeMax (initialShape h.val))) =
      Contractions.coefficients[shapeMax (initialShape h.val)]?.getD 0 := by
  have hc := CWWordDimensionParameters.table_eq_card (shapeIndex h)
  rw [Fintype.card_eq_nat_card] at hc ⊢
  exact hc.symm

theorem card_words {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PopulationHistory K) :
    Fintype.card (Words allocation dilation h) =
      (Contractions.coefficients[shapeMax (initialShape h.1.val)]?.getD 0) ^
        population allocation dilation (.initial h.1.val, h.2) := by
  simp only [Words, Fintype.card_fun, Fintype.card_fin, card_alphabet]

theorem log_card_words {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PopulationHistory K) :
    Real.log (Fintype.card (Words allocation dilation h) : ℝ) =
      (population allocation dilation (.initial h.1.val, h.2) : ℝ) *
        initialRate (initialShape h.1.val) := by
  simp only [card_words, Nat.cast_pow, Real.log_pow, initialRate]

theorem log_volume {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    Real.log (volume (K := K) allocation dilation : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        ∑ h : PopulationHistory K,
          (amount allocation (.initial h.1.val, h.2) : ℝ) *
            initialRate (initialShape h.1.val) := by
  rw [volume_eq_prod, Nat.cast_prod, Real.log_prod
    (fun h _ => Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (card_words_pos allocation dilation h)))]
  simp only [log_card_words]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  have hc : (population allocation dilation (.initial h.1.val, h.2) : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        (amount allocation (.initial h.1.val, h.2) : ℝ) := by
    exact_mod_cast population_cast allocation dilation (.initial h.1.val, h.2)
  rw [hc, mul_assoc]

theorem sum_populationHistory_rate {K : ℕ} (allocation : Allocation) :
    (∑ h : PopulationHistory K,
      (amount allocation (.initial h.1.val, h.2) : ℝ) *
        initialRate (initialShape h.1.val)) =
      ∑ h : InitialZero K,
        (initialAmount h.val : ℝ) * initialRate (initialShape h.val) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  dsimp only
  rw [← Finset.sum_mul]
  have hm : (∑ phi : Placement, (amount allocation (.initial h.val, phi) : ℝ)) =
      (initialAmount h.val : ℝ) := by
    exact_mod_cast sum_placement_amount allocation (.initial h.val)
  rw [hm]

theorem log_volume_eq_S0 {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    Real.log (volume (K := K) allocation dilation : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) * ((K : ℝ) * S0) := by
  rw [log_volume, sum_populationHistory_rate, initial_zero_history_rate]

end MatrixMultiplication.AllFieldInitialLeafRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWStageCPlacements
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instDecidableEqResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.CWStageCProducts

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type*} [Fintype H]

theorem historyVolume_eq (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    historyVolume side counts =
      5 ^ ∑ h, (singleCount (counts h) + 2 * crossCount (counts h)) := by
  rw [historyVolume_eq_prod]
  simp only [volume_eq]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem log_historyVolume (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    Real.log (historyVolume side counts : ℝ) =
      ∑ h, ((singleCount (counts h) : ℝ) + 2 * crossCount (counts h)) * Real.log 5 := by
  rw [historyVolume_eq]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_sum,
    Nat.cast_add, Nat.cast_mul, Finset.sum_mul]

theorem log_historyVolume_of_mass_counts (side : H → Fin 3)
    (counts : H → Fin 4 → ℕ) (t u : H → AllFieldParameters.Shape)
    (mass : H → ℚ) (N : ℕ)
    (hc : ∀ h i, (counts h i : ℚ) =
      (N : ℚ) * mass h * AllFieldHistory.stageCWeight (t h) (u h) i) :
    Real.log (historyVolume side counts : ℝ) =
      (N : ℝ) * ∑ h, (mass h : ℝ) *
        (2 - (AllFieldParameters.binaryParameter (t h) (u h) : ℝ)) * Real.log 5 := by
  have hs (h : H) : (singleCount (counts h) : ℚ) =
      (N : ℚ) * mass h * AllFieldParameters.binaryParameter (t h) (u h) := by
    simp only [singleCount, Nat.cast_add, hc, ← mul_add,
      AllFieldHistory.stageCWeight_single]
  have hx (h : H) : (crossCount (counts h) : ℚ) =
      (N : ℚ) * mass h * (1 - AllFieldParameters.binaryParameter (t h) (u h)) := by
    simp only [crossCount, Nat.cast_add, hc, ← mul_add,
      AllFieldHistory.stageCWeight_cross]
  rw [log_historyVolume, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  have hsr : (singleCount (counts h) : ℝ) =
      (N : ℝ) * (mass h : ℝ) * (AllFieldParameters.binaryParameter (t h) (u h) : ℝ) := by
    exact_mod_cast hs h
  have hxr : (crossCount (counts h) : ℝ) =
      (N : ℝ) * (mass h : ℝ) * (1 - (AllFieldParameters.binaryParameter (t h) (u h) : ℝ)) := by
    exact_mod_cast hx h
  rw [hsr, hxr]
  ring

theorem log_population_historyVolume {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (side : PopulationHistory K → Fin 3) :
    Real.log (historyVolume side (populationAtomCounts allocation dilation) : ℝ) =
      (AllFieldHistory.populationLength (K := K) allocation dilation : ℝ) *
        ∑ h : PopulationHistory K,
          (AllFieldHistory.amount allocation (.partC h.1, h.2) : ℝ) *
            (2 - (AllFieldParameters.binaryParameter
              (AllFieldHistory.cParameterParent h.1)
              (AllFieldHistory.cShapeParent h.1) : ℝ)) * Real.log 5 := by
  exact log_historyVolume_of_mass_counts side (populationAtomCounts allocation dilation)
    (fun h => AllFieldHistory.cParameterParent h.1)
    (fun h => AllFieldHistory.cShapeParent h.1)
    (fun h => AllFieldHistory.amount allocation (.partC h.1, h.2))
    (AllFieldHistory.populationLength (K := K) allocation dilation)
    (populationAtomCounts_mass allocation dilation)

theorem log_populationVolume {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) :
    Real.log (populationVolume (K := K) allocation dilation : ℝ) =
      (AllFieldHistory.populationLength (K := K) allocation dilation : ℝ) *
        ∑ h : PopulationHistory K,
          (AllFieldHistory.amount allocation (.partC h.1, h.2) : ℝ) *
            (2 - (AllFieldParameters.binaryParameter
              (AllFieldHistory.cParameterParent h.1)
              (AllFieldHistory.cShapeParent h.1) : ℝ)) * Real.log 5 :=
  log_population_historyVolume allocation dilation populationSide

end MatrixMultiplication.CWStageCProducts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_StageCTerminalRates
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instDecidableEqResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldStageCTerminalRates

open AllFieldHistory AllFieldParameters CWStageCProducts
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sum_populationHistory_rate {K : ℕ} (allocation : Allocation) :
    (∑ h : PopulationHistory K,
      (amount allocation (.partC h.1, h.2) : ℝ) *
        (2 - (binaryParameter (cParameterParent h.1) (cShapeParent h.1) : ℝ)) *
          Real.log 5) =
      ∑ h : BPositive K, (bAmount h.val : ℝ) *
        (2 - (binaryParameter (aShape h.val.1.val) (bShape h.val) : ℝ)) *
          Real.log 5 := by
  calc
    _ = ∑ h : PartC K, (partAmount allocation h : ℝ) *
        (2 - (binaryParameter (cParameterParent h) (cShapeParent h) : ℝ)) *
          Real.log 5 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro h _
      dsimp only
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hm : (∑ phi : Placement, (amount allocation (.partC h, phi) : ℝ)) =
          (partAmount allocation h : ℝ) := by
        exact_mod_cast sum_placement_amount allocation (.partC h)
      rw [hm]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro h _
      simp only [cParameterParent, cShapeParent]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hm : (∑ i : Fin 3, (partAmount allocation (h, i) : ℝ)) =
          (bAmount h.val : ℝ) := by
        exact_mod_cast part_transition allocation h
      rw [hm]

theorem log_populationVolume_eq_bPositive {K : ℕ} (allocation : Allocation)
    (dilation : ℕ) :
    Real.log (populationVolume (K := K) allocation dilation : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        ∑ h : BPositive K, (bAmount h.val : ℝ) *
          (2 - (binaryParameter (aShape h.val.1.val) (bShape h.val) : ℝ)) *
            Real.log 5 := by
  rw [log_populationVolume, sum_populationHistory_rate]

theorem bPositive_rate_eq_interior (K : ℕ) :
    (∑ h : BPositive K, (bAmount h.val : ℝ) *
      (2 - (binaryParameter (aShape h.val.1.val) (bShape h.val) : ℝ)) *
        Real.log 5) = (K : ℝ) * interiorS2 := by
  simpa only [interiorS2, littleMass_cast, mul_assoc] using
    b_positive_history_sum K
      (fun t u => (2 - (binaryParameter t u : ℝ)) * Real.log 5)

theorem log_populationVolume_eq_interior {K : ℕ} (allocation : Allocation)
    (dilation : ℕ) :
    Real.log (populationVolume (K := K) allocation dilation : ℝ) =
      (K : ℝ) * populationLength (K := K) allocation dilation * interiorS2 := by
  rw [log_populationVolume_eq_bPositive, bPositive_rate_eq_interior]
  ring

theorem normalized_log_populationVolume_eq_interior {K : ℕ} (hK : 0 < K)
    (allocation : Allocation) (dilation : ℕ) (hd : 0 < dilation) :
    Real.log (populationVolume (K := K) allocation dilation : ℝ) /
        ((K : ℝ) * populationLength (K := K) allocation dilation) = interiorS2 := by
  have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  have hn : (populationLength (K := K) allocation dilation : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (AllFieldPopulationCounts.blockLength_pos _ hd))
  rw [log_populationVolume_eq_interior]
  exact mul_div_cancel_left₀ _ (mul_ne_zero hk hn)

end MatrixMultiplication.AllFieldStageCTerminalRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_ZeroHistorySums
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instDecidableEqResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.half_unhalfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.unhalf_halfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldZeroHistorySums

open AllFieldHistory AllFieldParameters AllFieldTerminalStatisticLaws
open AllFieldTerminalRates AllFieldStageCTerminalRates
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

private theorem subtype_sum_indicator_inline_MatrixMultiplication_AllFieldZeroHistorySums {A : Type*} [Fintype A]
    (P : A → Prop) [DecidablePred P] [Fintype {a // P a}] (f : A → ℝ) :
    (∑ a : {a // P a}, f a.val) = ∑ a, if P a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

private theorem sum_subtype_complement {A : Type*} [Fintype A]
    (P : A → Prop) [DecidablePred P]
    [Fintype {a // P a}] [Fintype {a // ¬P a}] (f : A → ℝ) :
    (∑ a : {a // ¬P a}, f a.val) + (∑ a : {a // P a}, f a.val) = ∑ a, f a := by
  rw [subtype_sum_indicator_inline_MatrixMultiplication_AllFieldZeroHistorySums (fun a => ¬P a) f, subtype_sum_indicator_inline_MatrixMultiplication_AllFieldZeroHistorySums P f,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P a <;> simp [ha]

private theorem list_filter_sum_inline_MatrixMultiplication_AllFieldZeroHistorySums {A : Type*} (xs : List A) (p : A → Bool)
    (f : A → ℝ) :
    ((xs.filter p).map f).sum = (xs.map (fun a => if p a then f a else 0)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases hp : p a <;> simp [hp, ih]

theorem sum_placement_rate {K : ℕ} {H : Type*} [Fintype H]
    (allocation : Allocation) (canonical : H → CanonicalHistory K) (f : H → ℝ) :
    (∑ h : H × Placement, (amount allocation (canonical h.1, h.2) : ℝ) * f h.1) =
      ∑ h : H, (canonicalAmount allocation (canonical h) : ℝ) * f h := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  change (∑ phi : Placement, (amount allocation (canonical h, phi) : ℝ) * f h) =
    (canonicalAmount allocation (canonical h) : ℝ) * f h
  rw [← Finset.sum_mul]
  have hm : (∑ phi : Placement, (amount allocation (canonical h, phi) : ℝ)) =
      (canonicalAmount allocation (canonical h) : ℝ) := by
    exact_mod_cast sum_placement_amount allocation (canonical h)
  rw [hm]

theorem a_zero_canonical_rate (K : ℕ) :
    (∑ h : {h : AfterA K // aShape h ∉ positiveSecond},
      (aAmount h.val : ℝ) * AllFieldZeroLeafRates.fourRate (aShape h.val)) =
      (K : ℝ) * S1 := by
  rw [subtype_sum_indicator_inline_MatrixMultiplication_AllFieldZeroHistorySums (fun h : AfterA K => aShape h ∉ positiveSecond)
    (fun h => (aAmount h : ℝ) * AllFieldZeroLeafRates.fourRate (aShape h))]
  calc
    _ = ∑ h : AfterA K, (aAmount h : ℝ) *
        (if aShape h ∉ positiveSecond then AllFieldZeroLeafRates.fourRate (aShape h)
          else 0) := by
      apply Finset.sum_congr rfl
      intro h _
      split_ifs <;> simp
    _ = _ := by
      rw [a_history_sum K (fun t =>
        if t ∉ positiveSecond then AllFieldZeroLeafRates.fourRate t else 0),
        S1, zeroSecond, list_filter_sum_inline_MatrixMultiplication_AllFieldZeroHistorySums]
      apply congrArg (fun r : ℝ => (K : ℝ) * r)
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      cases hp : positive t <;> simp [positiveSecond, ht, hp]

theorem a_zero_history_rate (K : ℕ) (allocation : Allocation) :
    (∑ h : AZero K, (amount allocation (history (.inl h)) : ℝ) *
      AllFieldZeroLeafRates.fourRate (aShape h.1.val)) = (K : ℝ) * S1 := by
  calc
    _ = ∑ h : {h : AfterA K // aShape h ∉ positiveSecond},
        (aAmount h.val : ℝ) * AllFieldZeroLeafRates.fourRate (aShape h.val) := by
      exact sum_placement_rate (H := {h : AfterA K // aShape h ∉ positiveSecond})
        allocation (fun h => .afterA h.val)
        (fun h => AllFieldZeroLeafRates.fourRate (aShape h.val))
    _ = _ := a_zero_canonical_rate K

theorem b_positive_secondLeafRate (K : ℕ) :
    (∑ h : BPositive K, (bAmount h.val : ℝ) *
      secondLeafRate (aShape h.val.1.val) (bShape h.val)) = (K : ℝ) * interiorS2 := by
  calc
    _ = ∑ h : BPositive K, (bAmount h.val : ℝ) *
        (2 - (binaryParameter (aShape h.val.1.val) (bShape h.val) : ℝ)) *
          Real.log 5 := by
      apply Finset.sum_congr rfl
      intro h _
      rw [secondLeafRate_positive _ h.val.1.property _ (bShape_mem h.val) h.property]
      ring
    _ = _ := bPositive_rate_eq_interior K

theorem b_zero_canonical_rate (K : ℕ) :
    (∑ h : {h : AfterB K // positive (bShape h) ≠ true},
      (bAmount h.val : ℝ) * secondLeafRate (aShape h.val.1.val) (bShape h.val)) +
      (K : ℝ) * interiorS2 = (K : ℝ) * S2 := by
  rw [← b_positive_secondLeafRate K]
  rw [sum_subtype_complement (fun h : AfterB K => positive (bShape h) = true)
    (fun h => (bAmount h : ℝ) * secondLeafRate (aShape h.1.val) (bShape h))]
  exact b_history_sum K secondLeafRate

theorem b_zero_rate_eq_secondLeafRate {K : ℕ} (h : BZero K) :
    statisticRate (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h) =
      secondLeafRate (aShape h.1.val.1.val) (bShape h.1.val) := by
  have hz : positive (bShape h.1.val) = false := by simpa using h.1.property
  exact (secondLeafRate_zero _ h.1.val.1.property _ (bShape_mem h.1.val) hz).symm

theorem b_zero_history_rate (K : ℕ) (allocation : Allocation) :
    (∑ h : BZero K, (amount allocation (history (.inr h)) : ℝ) *
      statisticRate (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h)) +
      (K : ℝ) * interiorS2 = (K : ℝ) * S2 := by
  have he : (∑ h : BZero K, (amount allocation (history (.inr h)) : ℝ) *
        statisticRate (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h)) =
      ∑ h : {h : AfterB K // positive (bShape h) ≠ true},
        (bAmount h.val : ℝ) * secondLeafRate (aShape h.val.1.val) (bShape h.val) := by
    simp_rw [b_zero_rate_eq_secondLeafRate]
    exact sum_placement_rate (H := {h : AfterB K // positive (bShape h) ≠ true})
      allocation (fun h => .afterB h.val)
      (fun h => secondLeafRate (aShape h.val.1.val) (bShape h.val))
  rw [he]
  exact b_zero_canonical_rate K

theorem zero_history_sum (K : ℕ) (allocation : Allocation) :
    (∑ h : TerminalZero K, (amount allocation (history h) : ℝ) * zeroRate h) =
      (K : ℝ) * (S1 + S2 - interiorS2) := by
  rw [Fintype.sum_sum_type]
  simp only [zeroRate]
  rw [a_zero_history_rate K allocation]
  have hb := b_zero_history_rate K allocation
  nlinarith

end MatrixMultiplication.AllFieldZeroHistorySums

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRates
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open Filter
open scoped Topology

theorem factorialLogRemainder_stirling (n : ℕ) :
    factorialLogRemainder n =
      Real.log (Stirling.stirlingSeq n) + (1 / 2 : ℝ) * Real.log (2 * n) := by
  cases n with
  | zero => simp
  | succ n =>
    have h := Stirling.log_stirlingSeq_formula (n + 1)
    rw [Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
    unfold factorialLogRemainder
    linarith

theorem tendsto_factorialLogRemainder_div :
    Tendsto (fun n : ℕ => factorialLogRemainder n / (n : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hstirling :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ))
        atTop (𝓝 0) :=
    (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hconstant : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnat
  have hsum : Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (1 / 2 : ℝ) * (Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using hstirling.add ((hconstant.add hlog).const_mul (1 / 2 : ℝ))
  apply hsum.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  rw [factorialLogRemainder_stirling,
    Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr hn)]
  ring

theorem tendsto_factorialLogRemainder_mul_div (c : ℕ) :
    Tendsto (fun t : ℕ => factorialLogRemainder (t * c) / (t : ℝ))
      atTop (𝓝 0) := by
  by_cases hc : c = 0
  · subst c
    simp
  have hmul : Tendsto (fun t : ℕ => t * c) atTop atTop :=
    tendsto_id.atTop_mul_const' (Nat.pos_of_ne_zero hc)
  have hscaled : Tendsto
      (fun t : ℕ => factorialLogRemainder (t * c) / (t * c : ℕ) * (c : ℝ))
      atTop (𝓝 0) := by
    simpa using (tendsto_factorialLogRemainder_div.comp hmul).mul_const (c : ℝ)
  apply hscaled.congr
  intro t
  by_cases ht : t = 0
  · simp [ht]
  rw [Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr hc, Nat.cast_ne_zero.mpr ht]

end MatrixMultiplication.Foundation





namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

variable {A : Type*} [Fintype A]

theorem log_multinomial (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      Real.log (Nat.factorial (∑ a, counts a) : ℝ) -
        ∑ a, Real.log (Nat.factorial (counts a) : ℝ) := by
  have hspec :
      (∏ a, (Nat.factorial (counts a) : ℝ)) *
          (Nat.multinomial Finset.univ counts : ℝ) =
        (Nat.factorial (∑ a, counts a) : ℝ) := by
    exact_mod_cast Nat.multinomial_spec Finset.univ counts
  have hprod : (∏ a, (Nat.factorial (counts a) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => by positivity)
  have hmulti : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ counts))
  have hlog := congrArg Real.log hspec
  rw [Real.log_mul hprod hmulti,
    Real.log_prod (fun a _ => by positivity)] at hlog
  linarith

private theorem entropyTerm_div_scalar (x y : ℝ) :
    entropyTerm (x / y) = entropyTerm x / y + (x / y) * Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [entropyTerm, Real.log_div hx hy]
  unfold entropyTerm
  ring

theorem finiteEntropy_nat_normalize (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) /
          (∑ a, counts a : ℕ) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  unfold finiteEntropy
  simp only [entropyTerm_div_scalar]
  simp only [entropyTerm, neg_mul,
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    Finset.sum_neg_distrib]
  rw [← Nat.cast_sum, div_self hD']
  ring

theorem log_multinomial_eq_main_add_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  rw [log_multinomial]
  unfold factorialLogRemainder
  simp only [Finset.sum_sub_distrib, ← Nat.cast_sum]
  ring

private theorem mul_log_mul (x y : ℝ) :
    (x * y) * Real.log (x * y) =
      (x * Real.log x) * y + x * (y * Real.log y) := by
  calc
    (x * y) * Real.log (x * y) = -entropyTerm (x * y) := by
      simp [entropyTerm]
    _ = -(y * entropyTerm x + x * entropyTerm y) := by
      rw [entropyTerm_mul]
    _ = (x * Real.log x) * y + x * (y * Real.log y) := by
      unfold entropyTerm
      ring

theorem log_multinomial_mul_eq (counts : A → ℕ) (t : ℕ) :
    Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) =
      (t : ℝ) *
          ((∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
            ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (t * ∑ a, counts a) -
        ∑ a, factorialLogRemainder (t * counts a) := by
  have hsum : (∑ a, t * counts a) = t * ∑ a, counts a :=
    (Finset.mul_sum Finset.univ counts t).symm
  have hlogs :
      (∑ a, ((t : ℝ) * counts a) * Real.log ((t : ℝ) * counts a)) =
        ((t : ℝ) * Real.log t) * (∑ a, counts a : ℕ) +
          (t : ℝ) * ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ) := by
    simp only [mul_log_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Nat.cast_sum]
  rw [log_multinomial_eq_main_add_remainder, hsum]
  simp only [Nat.cast_mul]
  rw [mul_log_mul, hlogs]
  ring

theorem tendsto_log_multinomial_mul (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ =>
        Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  have hsum :
      Tendsto (fun t : ℕ => ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ))
        atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ
      (fun a _ => tendsto_factorialLogRemainder_mul_div (counts a))
  have herror : Tendsto
      (fun t : ℕ =>
        (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
          ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) /
            (∑ a, counts a : ℕ)) atTop (𝓝 0) := by
    simpa using ((tendsto_factorialLogRemainder_mul_div (∑ a, counts a)).sub
      hsum).div_const (∑ a, counts a : ℕ)
  have hlimit : Tendsto
      (fun t : ℕ =>
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
          (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
            ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) /
              (∑ a, counts a : ℕ))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  apply hlimit.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  rw [log_multinomial_mul_eq, finiteEntropy_nat_normalize counts hD,
    ← Finset.sum_div]
  have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  field_simp [ht', hD']
  ring

end MatrixMultiplication.Foundation





noncomputable section






namespace MatrixMultiplication.LeafRates

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

variable {A U : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]

omit [DecidableEq U] in
theorem log_card_supported (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, 0 < counts a → Fintype.card {u : U // statistic u = a} = b a)
    (hbpos : ∀ a, 0 < b a) :
    Real.log (Fintype.card (ExactStatisticWords.Words statistic counts) : ℝ) =
      Real.log (Nat.multinomial Finset.univ counts : ℝ) +
        ∑ a, (counts a : ℝ) * Real.log (b a : ℝ) := by
  rw [ExactStatisticWords.card_of_supported statistic counts b hb, Nat.cast_mul, Nat.cast_prod]
  have hm : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ counts))
  have hp : (∏ a, (b a ^ counts a : ℕ) : ℝ) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a _
    exact_mod_cast (Nat.ne_of_gt (pow_pos (hbpos a) _))
  rw [Real.log_mul hm hp, Real.log_prod
    (fun a _ => by exact_mod_cast (Nat.ne_of_gt (pow_pos (hbpos a) (counts a))))]
  simp only [Nat.cast_pow, Real.log_pow]

omit [DecidableEq U] in
theorem tendsto_log_card_supported (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, 0 < counts a → Fintype.card {u : U // statistic u = a} = b a)
    (hbpos : ∀ a, 0 < b a) (hD : 0 < ∑ a, counts a) :
    Tendsto (fun t : ℕ =>
      Real.log (Fintype.card (ExactStatisticWords.Words statistic (fun a => t * counts a)) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (b a : ℝ))) := by
  have hl := (tendsto_log_multinomial_mul counts hD).add_const
    (∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (b a : ℝ))
  apply hl.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  have hbt : ∀ a, 0 < t * counts a → Fintype.card {u : U // statistic u = a} = b a :=
    fun a ha => hb a (by nlinarith)
  rw [log_card_supported statistic (fun a => t * counts a) b hbt hbpos, add_div]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hDsum : (∑ a, (counts a : ℝ)) ≠ 0 := by
    simpa only [Nat.cast_sum] using hD'
  simp only [Nat.cast_mul]
  field_simp [ht', hD', hDsum]

end MatrixMultiplication.LeafRates






namespace MatrixMultiplication.AllFieldZeroLeafRates

open MatrixMultiplication.Foundation Filter AllFieldParameters CWWindowedLeaves CWCompleteStatistics
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

theorem four_tendsto_log_card (t : Shape) (counts : PairSlot → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (zeroPairLaw t s.1 s.2 : ℝ)) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (fourWords t counts m) : ℝ) /
      ((m : ℝ) * (∑ s, counts s : ℕ))) atTop (𝓝 (fourRate t)) := by
  have h := LeafRates.tendsto_log_card_supported
    (fun w : Alphabet 4 (shapeMax t) => fourStatistic w.val) counts
    (fun s => AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2)
    (four_supported t counts hD hlaw)
    (fun s => Nat.mul_pos (multiplicity_pos s.1) (multiplicity_pos s.2)) hD
  simpa only [fourWords, hlaw, fourRate] using h

theorem two_tendsto_log_card (d : ℚ) (k : Fin 5) (counts : Fin 6 → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (statisticLaw d k s : ℝ)) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (twoWords k counts m) : ℝ) /
      ((m : ℝ) * (∑ s, counts s : ℕ))) atTop (𝓝 (statisticRate d k)) := by
  have h := LeafRates.tendsto_log_card_supported
    (fun w : Alphabet 2 k.val => twoStatistic w.val) counts AllFieldParameters.multiplicity
    (two_supported d k counts hD hlaw) multiplicity_pos hD
  simp only [Fintype.card_eq_nat_card] at h ⊢
  simpa only [twoWords, hlaw, statisticRate] using h

end MatrixMultiplication.AllFieldZeroLeafRates

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_TerminalRates
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instDecidableEqResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeResidentStatistic _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.half_unhalfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.unhalf_halfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldTerminalRates

open AllFieldHistory AllFieldParameters AllFieldTerminalStatisticLaws
open AllFieldZeroLeafRates AllFieldZeroHistorySums Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

variable {K : ℕ}

theorem terminalDilation_pos {m : ℕ} (hm : 0 < m) :
    0 < terminalDilation K m :=
  AllFieldTerminalPopulations.dilation_pos law hm

theorem terminalLength_pos (allocation : Allocation) {m : ℕ} (hm : 0 < m) :
    0 < terminalLength allocation K m :=
  AllFieldPopulationCounts.blockLength_pos _ (terminalDilation_pos hm)

theorem terminalLength_mul_one (allocation : Allocation) (m : ℕ) :
    terminalLength allocation K m = m * terminalLength allocation K 1 := by
  simp only [terminalLength, terminalDilation, AllFieldTerminalPopulations.dilation,
    populationLength, AllFieldPopulationCounts.blockLength, one_mul, mul_assoc]

theorem statisticCounts_sum (allocation : Allocation) (h : TerminalZero K) :
    (∑ s, statisticCounts allocation h s) =
      population allocation (terminalDilation K 1) (history h) :=
  AllFieldTerminalPopulations.sum_count allocation history law law_nonneg law_total 1 h

theorem statisticCounts_sum_cast (allocation : Allocation) (h : TerminalZero K) :
    ((∑ s, statisticCounts allocation h s : ℕ) : ℝ) =
      (terminalLength allocation K 1 : ℝ) * (amount allocation (history h) : ℝ) := by
  rw [statisticCounts_sum]
  exact_mod_cast population_cast allocation (terminalDilation K 1) (history h)

attribute [local instance] OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.terminalTwoWordsFintype
theorem tendsto_zeroWords_local (allocation : Allocation) (h : TerminalZero K) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (ZeroWords allocation m h) : ℝ) /
      ((m : ℝ) * (∑ s, statisticCounts allocation h s : ℕ))) atTop
      (𝓝 (zeroRate h)) := by
  cases h with
  | inl h =>
      simp only [zeroWords_card_inl, zeroRate, statisticCounts_sum_inl]
      simpa only [Fintype.card_eq_nat_card] using
        four_tendsto_log_card (aShape h.1.val) (statisticCounts allocation (.inl h))
        (by simpa only [statisticCounts_sum_inl] using statisticCounts_pos allocation (.inl h))
        (by
          intro slot
          simpa only [statisticCounts_sum_inl, law_inl] using
            statisticCounts_ratio allocation (.inl h) slot)
  | inr h =>
      simp only [zeroWords_card_inr, zeroRate, statisticCounts_sum_inr]
      simpa only [Fintype.card_eq_nat_card] using
        two_tendsto_log_card (binaryParameter (bParent h) (bShape h.1.val))
        (bWeight h) (statisticCounts allocation (.inr h))
        (by simpa only [statisticCounts_sum_inr] using statisticCounts_pos allocation (.inr h))
        (by
          intro slot
          simpa only [statisticCounts_sum_inr, law_inr] using
            statisticCounts_ratio allocation (.inr h) slot)

theorem tendsto_zeroWords (hK : 0 < K) (allocation : Allocation) (h : TerminalZero K) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (ZeroWords allocation m h) : ℝ) /
      ((K : ℝ) * terminalLength allocation K m)) atTop
      (𝓝 ((amount allocation (history h) : ℝ) * zeroRate h / K)) := by
  have ht := (tendsto_zeroWords_local allocation h).mul_const
    ((amount allocation (history h) : ℝ) / K)
  have hr : zeroRate h * ((amount allocation (history h) : ℝ) / K) =
      (amount allocation (history h) : ℝ) * zeroRate h / K := by ring
  rw [hr] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hk' : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hn' : (terminalLength allocation K 1 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (terminalLength_pos allocation (K := K) (m := 1) (by decide))
  have ha' : (amount allocation (history h) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (history_amount_pos allocation h)
  rw [terminalLength_mul_one, Nat.cast_mul, statisticCounts_sum_cast]
  field_simp [hm', hk', hn', ha']

theorem log_zeroVolume (allocation : Allocation) (m : ℕ) :
    Real.log (zeroVolume (K := K) allocation m : ℝ) =
      ∑ h : TerminalZero K, Real.log (Fintype.card (ZeroWords allocation m h) : ℝ) := by
  rw [zeroVolume, Fintype.card_pi, Nat.cast_prod]
  exact Real.log_prod (fun h _ => by
    exact_mod_cast Nat.ne_of_gt (zeroWords_card_pos allocation m h))

theorem tendsto_zeroVolume (hK : 0 < K) (allocation : Allocation) :
    Tendsto (fun m : ℕ => Real.log (zeroVolume (K := K) allocation m : ℝ) /
      ((K : ℝ) * terminalLength allocation K m)) atTop
      (𝓝 (S1 + S2 - AllFieldStageCTerminalRates.interiorS2)) := by
  have ht := tendsto_finsetSum Finset.univ
    (fun h _ => tendsto_zeroWords hK allocation h)
  have hr : (∑ h : TerminalZero K, (amount allocation (history h) : ℝ) * zeroRate h / K) =
      S1 + S2 - AllFieldStageCTerminalRates.interiorS2 := by
    rw [← Finset.sum_div, zero_history_sum K allocation]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.ne_of_gt hK)
  rw [hr] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ext m
  rw [log_zeroVolume, Finset.sum_div]

theorem log_terminalVolume (allocation : Allocation) (m : ℕ) :
    Real.log (terminalVolume (K := K) allocation m : ℝ) =
      Real.log (AllFieldInitialLeafRates.volume (K := K) allocation
        (terminalDilation K m) : ℝ) +
      Real.log (zeroVolume (K := K) allocation m : ℝ) +
      Real.log (CWStageCProducts.populationVolume (K := K) allocation
        (terminalDilation K m) : ℝ) := by
  have hI : (AllFieldInitialLeafRates.volume (K := K) allocation
      (terminalDilation K m) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (AllFieldInitialLeafRates.volume_pos allocation _)
  have hZ : (zeroVolume (K := K) allocation m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (zeroVolume_pos allocation m)
  have hC : (CWStageCProducts.populationVolume (K := K) allocation
      (terminalDilation K m) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (stageCVolume_pos allocation _)
  simp only [terminalVolume, Nat.cast_mul, Real.log_mul (mul_ne_zero hI hZ) hC,
    Real.log_mul hI hZ]

theorem normalized_log_initialVolume (hK : 0 < K) (allocation : Allocation)
    {m : ℕ} (hm : 0 < m) :
    Real.log (AllFieldInitialLeafRates.volume (K := K) allocation
      (terminalDilation K m) : ℝ) / ((K : ℝ) * terminalLength allocation K m) = S0 := by
  rw [AllFieldInitialLeafRates.log_volume_eq_S0]
  change (terminalLength allocation K m : ℝ) * ((K : ℝ) * S0) /
    ((K : ℝ) * terminalLength allocation K m) = S0
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hn : (terminalLength allocation K m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (terminalLength_pos allocation hm)
  field_simp [hk, hn]

theorem normalized_log_stageCVolume (hK : 0 < K) (allocation : Allocation)
    {m : ℕ} (hm : 0 < m) :
    Real.log (CWStageCProducts.populationVolume (K := K) allocation
      (terminalDilation K m) : ℝ) / ((K : ℝ) * terminalLength allocation K m) =
        AllFieldStageCTerminalRates.interiorS2 :=
  AllFieldStageCTerminalRates.normalized_log_populationVolume_eq_interior
    hK allocation _ (terminalDilation_pos hm)

theorem tendsto_terminalVolume (hK : 0 < K) (allocation : Allocation) :
    Tendsto (fun m : ℕ => Real.log (terminalVolume (K := K) allocation m : ℝ) /
      ((K : ℝ) * terminalLength allocation K m)) atTop (𝓝 S) := by
  have hI : Tendsto (fun m : ℕ =>
      Real.log (AllFieldInitialLeafRates.volume (K := K) allocation
        (terminalDilation K m) : ℝ) / ((K : ℝ) * terminalLength allocation K m))
        atTop (𝓝 S0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact (normalized_log_initialVolume hK allocation hm).symm
  have hC : Tendsto (fun m : ℕ =>
      Real.log (CWStageCProducts.populationVolume (K := K) allocation
        (terminalDilation K m) : ℝ) / ((K : ℝ) * terminalLength allocation K m))
        atTop (𝓝 AllFieldStageCTerminalRates.interiorS2) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact (normalized_log_stageCVolume hK allocation hm).symm
  have ht := (hI.add (tendsto_zeroVolume hK allocation)).add hC
  have hr : S0 + (S1 + S2 - AllFieldStageCTerminalRates.interiorS2) +
      AllFieldStageCTerminalRates.interiorS2 = S := by unfold S; ring
  rw [hr] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ext m
  rw [log_terminalVolume, add_div, add_div]

end MatrixMultiplication.AllFieldTerminalRates

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_FloorExponentialRates
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.FloorExponentialRates

open Filter
open scoped BigOperators Topology Classical

theorem log_count_bounds {rate : ℝ} (hr : 0 ≤ rate) (m : ℕ) :
    (m : ℝ) * rate - Real.log 2 ≤ Real.log (count rate m : ℝ) ∧
      Real.log (count rate m : ℝ) ≤ (m : ℝ) * rate := by
  have hp : (0 : ℝ) < count rate m := Nat.cast_pos.mpr (count_pos hr m)
  have hone : (1 : ℝ) ≤ count rate m := by exact_mod_cast count_pos hr m
  have hround := Nat.lt_floor_add_one (Real.exp ((m : ℝ) * rate))
  have hhalf : Real.exp ((m : ℝ) * rate) / 2 ≤ (count rate m : ℝ) := by
    change Real.exp ((m : ℝ) * rate) < (count rate m : ℝ) + 1 at hround
    linarith
  constructor
  · have h := Real.log_le_log (by positivity : 0 < Real.exp ((m : ℝ) * rate) / 2) hhalf
    simpa only [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_exp] using h
  · have h := Real.log_le_log hp (Nat.floor_le (Real.exp_pos _).le)
    simpa only [Real.log_exp] using h

theorem tendsto_log_count_div_nat {rate : ℝ} (hr : 0 ≤ rate) :
    Tendsto (fun m : ℕ => Real.log (count rate m : ℝ) / (m : ℝ))
      atTop (𝓝 rate) := by
  have hinv : Tendsto (fun m : ℕ => Real.log 2 / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun m : ℕ => rate - Real.log 2 / (m : ℝ)) atTop (𝓝 rate) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have h := div_le_div_of_nonneg_right (log_count_bounds hr m).1 hm'.le
    simpa only [sub_div, mul_div_cancel_left₀ rate hm'.ne'] using h
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have h := div_le_div_of_nonneg_right (log_count_bounds hr m).2 hm'.le
    simpa only [mul_div_cancel_left₀ rate hm'.ne'] using h

theorem tendsto_log_prod_count_div_nat {I : Type*} [Fintype I] (rate : I → ℝ)
    (hr : ∀ i, 0 ≤ rate i) :
    Tendsto (fun m : ℕ => Real.log ((∏ i, count (rate i) m : ℕ) : ℝ) / (m : ℝ))
      atTop (𝓝 (∑ i, rate i)) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ => tendsto_log_count_div_nat (hr i))
  apply h.congr
  intro m
  rw [Nat.cast_prod, Real.log_prod
    (fun i _ => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (count_pos (hr i) m)))]
  simp only [div_eq_mul_inv, Finset.sum_mul]

end MatrixMultiplication.FloorExponentialRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryRecoveryBudget
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial




section
noncomputable section






namespace MatrixMultiplication.AllFieldHistoryRecovery

open AllFieldHistory AllFieldHistorySupport

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem replication_subexponential (allocation : Allocation) (ε : ℝ) :
    Filter.Tendsto (fun m : ℕ =>
      Real.log (Fintype.card (InverseLinearRecovery.MaskRectangles
        (shiftCount (K := K) (tick := tick) allocation ε m))) / m)
      Filter.atTop (nhds 0) :=
  InverseLinearRecovery.subexponential_copies (supportRate_pos allocation)
    (by have := AllFieldHistoryMasks.lossConstant_nonneg (K := K) (tick := tick) allocation ε
        linarith)

end MatrixMultiplication.AllFieldHistoryRecovery

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section






namespace MatrixMultiplication.AllFieldActiveLaws

open AllFieldParameters AllFieldHistory MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

theorem populationLength_dilation {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    populationLength (K := K) allocation dilation =
      dilation * populationLength (K := K) allocation 1 := by
  simp only [populationLength, AllFieldPopulationCounts.blockLength, one_mul]

end MatrixMultiplication.AllFieldActiveLaws






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_ConstructionLabels
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldConstructionRates

open MatrixMultiplication.Foundation AllFieldHistory AllFieldScheduledYield
open AllFieldActiveLaws Filter
open scoped BigOperators Topology Classical

variable {K : ℕ}

theorem denominator_pos (allocation : Allocation) : 0 < denominator (K := K) allocation :=
  AllFieldPopulationCounts.blockLength_pos _ (by decide)

theorem population_length (allocation : Allocation) (m : ℕ) :
    populationLength (K := K) allocation m = m * denominator (K := K) allocation :=
  populationLength_dilation allocation m

theorem populationLength_tendsto (allocation : Allocation) :
    Tendsto (populationLength (K := K) allocation) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with m hm
  rw [population_length]
  exact hm.trans (by simpa using Nat.mul_le_mul_left m (denominator_pos allocation))

theorem slot_card : Fintype.card (Slot K) = 1 + 6 * (K + 2) := by
  simp [Slot, Placement, Fintype.card_perm, Nat.factorial_succ]
  omega

theorem sum_capacity (allocation : Allocation) :
    (∑ slot : Slot K, capacity allocation slot) =
      (K : ℝ) * AllFieldInitialEntropy.nativeH0 + physicalYield K allocation := by
  simp only [Slot, Fintype.sum_sum_type, capacity, Fintype.sum_unique,
    Fintype.sum_prod_type]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun tick : ℕ =>
    ∑ σ : Placement, Staggering.minCapacity
      (physicalTickCapacity allocation tick (workCapacity (K := K)) σ)) (K + 2)

theorem sum_selectionRate (allocation : Allocation) (δ : ℝ) :
    (∑ slot : Slot K, selectionRate allocation δ slot) =
      (denominator (K := K) allocation : ℝ) *
        ((K : ℝ) * AllFieldInitialEntropy.nativeH0 + physicalYield K allocation) -
      (1 + 6 * (K + 2) : ℕ) * δ := by
  simp only [selectionRate, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, slot_card, sum_capacity]

theorem selected_rate (hK : 0 < K) (allocation : Allocation) (δ : ℝ)
    (hδ : ∀ slot : Slot K, δ ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card
      (SelectedLabels (K := K) allocation δ m) : ℝ) /
      ((K : ℝ) * populationLength (K := K) allocation m)) atTop
      (𝓝 (AllFieldInitialEntropy.nativeH0 + physicalYield K allocation / K -
        (1 + 6 * (K + 2) : ℕ) * δ /
          ((K : ℝ) * denominator (K := K) allocation))) := by
  have h := (FloorExponentialRates.tendsto_log_prod_count_div_nat
    (selectionRate (K := K) allocation δ) (fun slot => sub_nonneg.mpr (hδ slot))).div_const
    ((K : ℝ) * denominator (K := K) allocation)
  rw [sum_selectionRate] at h
  have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  have hd : (denominator (K := K) allocation : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (denominator_pos allocation).ne'
  have hr : ((denominator (K := K) allocation : ℝ) *
      ((K : ℝ) * AllFieldInitialEntropy.nativeH0 + physicalYield K allocation) -
      (1 + 6 * (K + 2) : ℕ) * δ) / ((K : ℝ) * denominator (K := K) allocation) =
      AllFieldInitialEntropy.nativeH0 + physicalYield K allocation / K -
        (1 + 6 * (K + 2) : ℕ) * δ /
          ((K : ℝ) * denominator (K := K) allocation) := by
    field_simp [hk, hd]
  rw [hr] at h
  apply h.congr
  intro m
  rw [card_selected_product, population_length, Nat.cast_mul]
  ring

theorem exists_positive_slack (allocation : Allocation)
    (hcap : ∀ slot : Slot K, 0 < capacity allocation slot) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, δ ≤ η → ∀ slot : Slot K,
      δ ≤ (denominator (K := K) allocation : ℝ) * capacity allocation slot := by
  let η := Finset.univ.inf' (show (Finset.univ : Finset (Slot K)).Nonempty from
    ⟨.inl (), Finset.mem_univ _⟩)
    (fun slot => (denominator (K := K) allocation : ℝ) * capacity allocation slot)
  refine ⟨η, ?_, ?_⟩
  · apply (Finset.lt_inf'_iff _).mpr
    intro slot _
    exact mul_pos (Nat.cast_pos.mpr (denominator_pos allocation)) (hcap slot)
  · intro δ hδ slot
    exact hδ.trans (Finset.inf'_le _ (Finset.mem_univ slot))

theorem exists_slack_for_loss (hK : 0 < K) (allocation : Allocation)
    (hcap : ∀ slot : Slot K, 0 < capacity allocation slot)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ slot : Slot K, δ ≤ (denominator (K := K) allocation : ℝ) *
        capacity allocation slot) ∧
      (1 + 6 * (K + 2) : ℕ) * δ /
        ((K : ℝ) * denominator (K := K) allocation) < η := by
  obtain ⟨bound, hbound, hslots⟩ := exists_positive_slack allocation hcap
  have hk : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hd : (0 : ℝ) < denominator (K := K) allocation :=
    Nat.cast_pos.mpr (denominator_pos allocation)
  have hc : (0 : ℝ) < (1 + 6 * (K + 2) : ℕ) := by positivity
  let target := η * ((K : ℝ) * denominator (K := K) allocation) /
    (1 + 6 * (K + 2) : ℕ)
  have ht : 0 < target := div_pos (mul_pos hη (mul_pos hk hd)) hc
  let δ := min bound target / 2
  have hm : 0 < min bound target := lt_min hbound ht
  have hδ : 0 < δ := div_pos hm (by norm_num)
  have hδmin : δ < min bound target := by dsimp [δ] <;> linarith
  refine ⟨δ, hδ, hslots δ (hδmin.le.trans (min_le_left _ _)), ?_⟩
  apply (div_lt_iff₀ (mul_pos hk hd)).mpr
  have hsmall := (lt_div_iff₀ hc).mp (hδmin.trans_le (min_le_right bound target))
  change δ * ((1 + 6 * (K + 2) : ℕ) : ℝ) <
    η * ((K : ℝ) * denominator (K := K) allocation) at hsmall
  simpa only [mul_comm δ] using hsmall

theorem terminalDilation_mul_one (K m : ℕ) :
    AllFieldTerminalRates.terminalDilation K m =
      m * AllFieldTerminalRates.terminalDilation K 1 := by
  simp only [AllFieldTerminalRates.terminalDilation,
    AllFieldTerminalPopulations.dilation, one_mul]

theorem terminalDilation_tendsto (K : ℕ) :
    Tendsto (AllFieldTerminalRates.terminalDilation K) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with m hm
  rw [terminalDilation_mul_one]
  have hD := AllFieldTerminalRates.terminalDilation_pos (K := K) (m := 1) (by decide)
  have hmul : m ≤ m * AllFieldTerminalRates.terminalDilation K 1 := by
    simpa using Nat.mul_le_mul_left m hD
  exact hm.trans hmul

theorem selected_terminal_rate (hK : 0 < K) (allocation : Allocation) (δ : ℝ)
    (hδ : ∀ slot : Slot K, δ ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card
      (SelectedLabels (K := K) allocation δ (AllFieldTerminalRates.terminalDilation K m)) : ℝ) /
      ((K : ℝ) * AllFieldTerminalRates.terminalLength allocation K m)) atTop
      (𝓝 (AllFieldInitialEntropy.nativeH0 + physicalYield K allocation / K -
        (1 + 6 * (K + 2) : ℕ) * δ /
          ((K : ℝ) * denominator (K := K) allocation))) :=
  (selected_rate hK allocation δ hδ).comp (terminalDilation_tendsto K)

end MatrixMultiplication.AllFieldConstructionRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ConstructionRates
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldSourceRates

open AllFieldSource Filter
open scoped Topology

private theorem tendsto_log_linear_div_nat (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log (a * N + 1) / (N : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun N : ℕ => a * N + 1) atTop atTop :=
    (hnat.const_mul_atTop ha).atTop_add_nonneg (fun _ => zero_le_one)
  have hlog : Tendsto (fun N : ℕ => Real.log (a * N + 1) / (a * N + 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp harg
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hratio : Tendsto (fun N : ℕ => (a * N + 1) / (N : ℝ)) atTop (𝓝 a) := by
    have hsum : Tendsto (fun N : ℕ => a + 1 / (N : ℝ)) atTop (𝓝 a) := by
      simpa only [add_zero] using hinv.const_add a
    apply hsum.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with N hN
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    field_simp [hN']
  have hprod : Tendsto (fun N : ℕ =>
      (Real.log (a * N + 1) / (a * N + 1)) * ((a * N + 1) / (N : ℝ)))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using hlog.mul hratio
  apply hprod.congr
  intro N
  have harg' : a * (N : ℝ) + 1 ≠ 0 := by positivity
  exact div_mul_div_cancel₀ harg'

theorem tendsto_log_polynomial_overhead (K : ℕ) (hK : 0 < K) :
    Tendsto (fun N : ℕ =>
      Real.log (((3 * (8 * K * N) + 1) ^ 2 : ℕ) : ℝ) / ((K : ℝ) * N))
      atTop (𝓝 0) := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hbase := tendsto_log_linear_div_nat (3 * (8 * (K : ℝ))) (by positivity)
  have hscaled : Tendsto (fun N : ℕ =>
      (2 * (Real.log (3 * (8 * (K : ℝ)) * N + 1) / (N : ℝ))) / (K : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using (hbase.const_mul 2).div_const (K : ℝ)
  apply hscaled.congr
  intro N
  have harg : ((3 * (8 * K * N) + 1 : ℕ) : ℝ) =
      3 * (8 * (K : ℝ)) * N + 1 := by push_cast <;> ring
  rw [Nat.cast_pow, Real.log_pow, harg]
  norm_num only [Nat.cast_ofNat]
  ring

theorem tendsto_log_exponential_source (K : ℕ) (hK : 0 < K) :
    Tendsto (fun N : ℕ =>
      Real.log ((7 ^ (8 * K * N) : ℕ) : ℝ) / ((K : ℝ) * N))
      atTop (𝓝 (8 * Real.log 7)) := by
  have hK' : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with N hN
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  field_simp [hK', hN']

theorem log_rankBudget (Copies : Type*) [Fintype Copies] (K N : ℕ)
    (hcopies : 0 < Fintype.card Copies) :
    Real.log (rankBudget Copies K N : ℝ) =
      Real.log (Fintype.card Copies : ℝ) +
        Real.log (((3 * (8 * K * N) + 1) ^ 2 : ℕ) : ℝ) +
        Real.log ((7 ^ (8 * K * N) : ℕ) : ℝ) := by
  have hc : (Fintype.card Copies : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hcopies)
  have hp : (((3 * (8 * K * N) + 1) ^ 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have he : ((7 ^ (8 * K * N) : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [rankBudget, Nat.cast_mul]
  rw [Real.log_mul hc (mul_ne_zero hp he), Real.log_mul hp he, ← add_assoc]

end MatrixMultiplication.AllFieldSourceRates

namespace MatrixMultiplication.AllFieldConstructionRates

open MatrixMultiplication.Foundation AllFieldHistory Filter
open scoped BigOperators Topology Classical

variable {K : ℕ}

theorem card_copies_pos (allocation : Allocation) (ε : ℝ) (m : ℕ) :
    0 < Fintype.card (Copies (K := K) allocation ε m) := Fintype.card_pos

theorem copies_subexponential (allocation : Allocation) (ε : ℝ) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (Copies (K := K) allocation ε m) : ℝ) /
      (m : ℝ)) atTop (𝓝 0) := by
  have h := RecoveryGrowth.tendsto_log_prod_div_nat (Finset.univ : Finset (Fin (K + 2)))
    (r := fun tick m => Fintype.card (InverseLinearRecovery.MaskRectangles
      (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick.val) allocation ε m)))
    (fun _ _ _ => Fintype.card_pos)
    (fun tick _ => AllFieldHistoryRecovery.replication_subexponential
      (K := K) (tick := tick.val) allocation ε)
  simpa only [Copies, Fintype.card_pi] using h

theorem copies_rate (_hK : 0 < K) (allocation : Allocation) (ε : ℝ) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (Copies (K := K) allocation ε m) : ℝ) /
      ((K : ℝ) * populationLength (K := K) allocation m)) atTop (𝓝 0) := by
  have h := (copies_subexponential (K := K) allocation ε).div_const
    ((K : ℝ) * denominator (K := K) allocation)
  simp only [zero_div] at h
  apply h.congr
  intro m
  rw [population_length, Nat.cast_mul]
  ring

theorem source_rank_rate (hK : 0 < K) (allocation : Allocation) (ε : ℝ) :
    Tendsto (fun m : ℕ => Real.log
      (AllFieldSource.rankBudget (Copies (K := K) allocation ε m) K
        (populationLength (K := K) allocation m) : ℝ) /
      ((K : ℝ) * populationLength (K := K) allocation m))
      atTop (𝓝 (8 * Real.log 7)) := by
  have hp := (AllFieldSourceRates.tendsto_log_polynomial_overhead K hK).comp
    (populationLength_tendsto (K := K) allocation)
  have he := (AllFieldSourceRates.tendsto_log_exponential_source K hK).comp
    (populationLength_tendsto (K := K) allocation)
  have h := ((copies_rate hK allocation ε).add hp).add he
  simp only [zero_add] at h
  apply h.congr
  intro m
  rw [AllFieldSourceRates.log_rankBudget _ _ _ (card_copies_pos allocation ε m),
    add_div, add_div]
  rfl

theorem source_rank_terminal_rate (hK : 0 < K) (allocation : Allocation) (ε : ℝ) :
    Tendsto (fun m : ℕ => Real.log
      (AllFieldSource.rankBudget
        (Copies (K := K) allocation ε (AllFieldTerminalRates.terminalDilation K m)) K
        (AllFieldTerminalRates.terminalLength allocation K m) : ℝ) /
      ((K : ℝ) * AllFieldTerminalRates.terminalLength allocation K m))
      atTop (𝓝 (8 * Real.log 7)) :=
  (source_rank_rate hK allocation ε).comp (terminalDilation_tendsto K)

end MatrixMultiplication.AllFieldConstructionRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_RateLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldRateLimit

open Filter
open scoped Topology

variable {F : Type*} [Field F]

theorem inequality_of_rates {W : ℕ → AllFieldWitness F} {scale : ℕ → ℝ}
    {Y S R : ℝ} (h : HasRates W scale Y S R) :
    Y + (Arithmetic.omega F / 3) * S ≤ R := by
  apply le_of_tendsto_of_tendsto
    (h.yield_limit.add (h.volume_limit.const_mul (Arithmetic.omega F / 3))) h.rank_limit
  filter_upwards [h.scale_positive] with n hn
  have hb := div_le_div_of_nonneg_right (W n).log_inequality hn.le
  simpa only [add_div, mul_div_assoc] using hb

end MatrixMultiplication.AllFieldRateLimit

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryIteration
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.terminalExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryTick

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldGroupSelection AllFieldHistoryGroupedRecovery
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ) (ε slack : ℝ)

attribute [local instance] OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsDecidableEq
@[simp] theorem activeExecution_copies (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Fintype.card (activeExecution allocation m ε slack F hε hm chosen).Copies =
      2 ^ (3 * AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) := by
  simp only [activeExecution, Execution.restrict]
  erw [Execution.extractSelectedAndRepair_copies]
  simp only [Execution.initial]
  exact mul_one _

@[simp] theorem execution_copies (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Fintype.card (execution allocation m ε slack F hε hm chosen).Copies =
      2 ^ (3 * AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) :=
  activeExecution_copies allocation m ε slack F hε hm chosen

end MatrixMultiplication.AllFieldHistoryTick

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryIteration

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ} (allocation : Allocation) (m : ℕ) (ε slack : ℝ)

variable (F : Type*) [Field F] (hε : 0 < ε)
    (hm : ∀ t : Fin (K + 2),
      AllFieldHistoryRecovery.minimumDilation (K := K) (tick := t.val) allocation ε ≤ m)
    (chosen : ScheduleChoices (K := K) allocation m ε slack)
    {InitialTag : Type} [Fintype InitialTag]
    (start : Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : InitialTag => stateTensor F (K := K) allocation m ε 0)))

theorem run_copies (n : ℕ) (hn : n ≤ K + 2) :
    Fintype.card (run allocation m ε slack F hε hm chosen start n hn).Copies =
      Fintype.card start.Copies * ∏ t : Fin n,
        2 ^ (3 * AllFieldHistoryRecovery.shiftCount (K := K) (tick := t.val) allocation ε m) := by
  induction n with
  | zero =>
      simp [run]
      rfl
  | succ n ih =>
      rw [run]
      erw [retarget_copies, Execution.branchOperation_copies, AllFieldHistoryTick.execution_copies,
        ih, Fin.prod_univ_castSucc]
      ring

@[simp] theorem execution_copies :
    Fintype.card (execution allocation m ε slack F hε hm chosen start).Copies =
      Fintype.card start.Copies * ∏ t : Fin (K + 2),
        2 ^ (3 * AllFieldHistoryRecovery.shiftCount (K := K) (tick := t.val) allocation ε m) :=
  run_copies allocation m ε slack F hε hm chosen start (K + 2) le_rfl

end MatrixMultiplication.AllFieldHistoryIteration

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_OrderedLimits
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldConstructionData

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ}

variable (allocation : Allocation) (dilation : ℕ) (width slack : ℝ)

theorem execution_copies (F : Type*) [Field F] (hwidth : 0 < width)
    (data : Data (K := K) allocation dilation width slack) :
    Fintype.card (execution allocation dilation width slack F hwidth data).Copies =
      Fintype.card (AllFieldConstructionRates.Copies
        (K := K) allocation width dilation) := by
  rw [execution, AllFieldHistoryIteration.execution_copies,
    AllFieldInitialChoice.execution_copies, one_mul]
  simp only [AllFieldConstructionRates.Copies, Fintype.card_pi,
    InverseLinearRecovery.MaskRectangles, ExactRecovery.card_mask_rectangles, Fintype.card_fin]

variable {F : Type*} [Field F] (m : ℕ)

@[simp] theorem witness_rankBound (hm : 0 < m) (hwidth : 0 < width)
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K m) width slack) :
    (witness (F := F) allocation width slack m hm hwidth hslack data).rankBound =
      AllFieldSource.rankBudget
        (AllFieldConstructionRates.Copies (K := K) allocation width
          (AllFieldTerminalRates.terminalDilation K m)) K
        (AllFieldTerminalRates.terminalLength allocation K m) := by
  change AllFieldSource.rankBudget
    (execution allocation (AllFieldTerminalRates.terminalDilation K m) width slack F hwidth data).Copies
    K (AllFieldTerminalRates.terminalLength allocation K m) = _
  unfold AllFieldSource.rankBudget
  rw [execution_copies]

end MatrixMultiplication.AllFieldConstructionData

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldConstructionFamily

open MatrixMultiplication.Foundation AllFieldHistory AllFieldConstructionData
open AllFieldConstructionRates Filter
open scoped BigOperators Topology Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ}

theorem exists_width_eventually_data (allocation : Allocation)
    {slack widthMax : ℝ} (hslack : 0 < slack) (hmax : 0 < widthMax) :
    ∃ width : ℝ, 0 < width ∧ width ≤ widthMax ∧
      ∀ᶠ m : ℕ in atTop, Nonempty (Data (K := K) allocation m width slack) := by
  let Index := Fin (K + 2) × Placement
  have hindex : (Finset.univ : Finset Index).Nonempty :=
    ⟨(⟨0, by omega⟩, Equiv.refl _), Finset.mem_univ _⟩
  have hb (i : Index) :=
    AllFieldGroupSelection.exists_threshold_eventually_selected
      (K := K) (tick := i.1.val) allocation i.2 hslack hmax
  choose threshold hpositive hmaximum hselected using hb
  let width := Finset.univ.inf' hindex threshold
  have hwidth : 0 < width := by
    apply (Finset.lt_inf'_iff hindex).mpr
    intro i _
    exact hpositive i
  have hbound (i : Index) : width ≤ threshold i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  have hwidthMax : width ≤ widthMax :=
    (hbound hindex.choose).trans (hmaximum hindex.choose)
  have hgroups : ∀ᶠ m : ℕ in atTop, ∀ i : Index,
      Nonempty (AllFieldGroupSelection.Selected (K := K) (tick := i.1.val)
        allocation m width i.2 slack) :=
    Filter.eventually_all.mpr (fun i => hselected i width hwidth (hbound i))
  have hthresholds : ∀ᶠ m : ℕ in atTop, ∀ t : Fin (K + 2),
      AllFieldHistoryRecovery.minimumDilation (K := K) (tick := t.val) allocation width ≤ m :=
    Filter.eventually_all.mpr (fun _ => eventually_ge_atTop _)
  refine ⟨width, hwidth, hwidthMax, ?_⟩
  filter_upwards [AllFieldInitialChoice.eventually_nonempty (K := K) allocation hslack,
    hgroups, hthresholds] with m hinitial hgroup hthreshold
  exact ⟨{ initial := Classical.choice hinitial
           groups := fun t sigma => Classical.choice (hgroup (t, sigma))
           threshold := hthreshold }⟩

theorem exists_family (F : Type*) [Field F] (hK : 0 < K)
    (allocation : Allocation) {slack : ℝ} (hslack : 0 < slack)
    (hslots : ∀ slot : Slot K, slack ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot) :
    ∃ (W : ℕ → AllFieldWitness F) (scale : ℕ → ℝ),
      AllFieldRateLimit.HasRates W scale (yieldRate (K := K) allocation slack)
        AllFieldTerminalRates.S (8 * Real.log 7) := by
  obtain ⟨width, hwidth, _hmax, hd⟩ := exists_width_eventually_data
    (K := K) allocation hslack (show (0 : ℝ) < 1 by norm_num)
  have hterminal := (terminalDilation_tendsto K).eventually hd
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (hterminal.and (eventually_gt_atTop (0 : ℕ)))
  let data (n : ℕ) : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K (n + M)) width slack :=
    Classical.choice (hM (n + M) (by omega)).1
  have hn (n : ℕ) : 0 < n + M := (hM (n + M) (by omega)).2
  let W (n : ℕ) := witness (F := F) allocation width slack (n + M)
    (hn n) hwidth hslots (data n)
  let scale (n : ℕ) : ℝ := (K : ℝ) *
    AllFieldTerminalRates.terminalLength allocation K (n + M)
  refine ⟨W, scale, ?_⟩
  refine { scale_positive := ?_, yield_limit := ?_, volume_limit := ?_, rank_limit := ?_ }
  · apply Eventually.of_forall
    intro n
    exact mul_pos (Nat.cast_pos.mpr hK)
      (Nat.cast_pos.mpr (AllFieldTerminalRates.terminalLength_pos allocation (hn n)))
  · have h := (selected_terminal_rate hK allocation slack hslots).comp
      (tendsto_add_atTop_nat M)
    apply h.congr
    intro n
    simp only [Function.comp_def, W, scale, witness_multiplicity]
  · have h := (AllFieldTerminalRates.tendsto_terminalVolume hK allocation).comp
      (tendsto_add_atTop_nat M)
    apply h.congr
    intro n
    simp only [Function.comp_def, W, scale, witness_volume]
  · have h := (source_rank_terminal_rate hK allocation width).comp
      (tendsto_add_atTop_nat M)
    apply h.congr
    intro n
    simp only [Function.comp_def, W, scale, witness_rankBound]

theorem fixed_prescription_constraint (F : Type*) [Field F] (hK : 0 < K)
    (allocation : Allocation) {slack : ℝ} (hslack : 0 < slack)
    (hslots : ∀ slot : Slot K, slack ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot) :
    yieldRate (K := K) allocation slack + (Arithmetic.omega F / 3) *
      AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
  obtain ⟨W, scale, h⟩ := exists_family F hK allocation hslack hslots
  exact AllFieldRateLimit.inequality_of_rates h

theorem fixed_allocation_constraint_oai (F : Type*) [Field F] (hK : 0 < K)
    (allocation : Allocation) (hcapacity : ∀ slot : Slot K, 0 < capacity allocation slot) :
    AllFieldInitialEntropy.nativeH0 + AllFieldScheduledYield.physicalYield K allocation / K +
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨slack, hslack, hslots, hloss⟩ :=
    exists_slack_for_loss hK allocation hcapacity hη
  have h := fixed_prescription_constraint F hK allocation hslack hslots
  unfold yieldRate at h
  linarith

end MatrixMultiplication.AllFieldConstructionFamily

end
end

end MatrixAllFields

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionFamily.fixed_allocation_constraint_oai.{u_1} := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionFamily.fixed_allocation_constraint_oai.{u_1}
