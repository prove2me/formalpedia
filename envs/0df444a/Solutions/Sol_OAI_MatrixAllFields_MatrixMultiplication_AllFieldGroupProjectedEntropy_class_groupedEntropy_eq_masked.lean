-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.class_groupedEntropy_eq_masked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:24:47.075776+00:00
-- url     : https://prove2.me/submissions/725372e2-b081-4786-8dd2-f8f61a89ceff

import Mathlib
import Definitions.Def_OAIQ254M007

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
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

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

theorem map_mass_apply (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) (a : A) : (p.map f).mass (f a) = p.mass a := by
  classical
  simp [map_mass, hf.eq_iff]

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_GroupOrbitCount
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.nativeSplitWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
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

theorem work_source_amount_pos {K : ℕ} (allocation : Allocation) (w : PlacedWork K) :
    0 < amount allocation (w.1.source, w.2) := by
  apply div_pos _ (by norm_num)
  cases w.1 with
  | stageA h => exact initialAmount_pos h.val
  | stageB h => exact aAmount_pos h.val
  | stageC h => exact partAmount_pos allocation h

theorem work_source_population_pos {K : ℕ} (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (w : PlacedWork K) :
    0 < population allocation dilation (w.1.source, w.2) :=
  (AllFieldPopulationCounts.count_pos_iff _ (amount_nonneg allocation) hd _).mpr
    (work_source_amount_pos allocation w)

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
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

theorem placedLaw_mass_branch {K : ℕ} (w : PlacedWork K) (b : w.1.Branch) :
    (placedLaw w).mass (branchShape w b) = (branchProbability w.1 b : ℝ) :=
  FiniteLaw.map_mass_apply _ _ (branchShape_injective w) b

theorem branchPopulation_cast_rat {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    (branchPopulation allocation dilation w b : ℚ) =
      (population allocation dilation (w.1.source, w.2) : ℚ) *
        branchProbability w.1 b := by
  rcases w with ⟨w, phi⟩
  cases w <;>
    simp only [branchPopulation, Work.child, Work.source, population_cast,
      amount, canonicalAmount, aAmount, bAmount, cAmount, branchProbability] <;> ring

theorem branchPopulation_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    (branchPopulation allocation dilation w b : ℝ) =
      (population allocation dilation (w.1.source, w.2) : ℝ) *
        (branchLaw w.1).mass b := by
  rw [branchLaw_mass]
  exact_mod_cast branchPopulation_cast_rat allocation dilation w b

theorem jointCounts_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) =
      (population allocation dilation (w.1.source, w.2) : ℝ) *
        (placedLaw w).mass u := by
  simp only [jointCounts, shapeCounts, Nat.cast_sum, placedLaw_mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : branchShape w b = u
  · simp only [hb, ite_true, if_true, branchPopulation_cast, branchLaw_mass]
  · simp [hb]

end MatrixMultiplication.AllFieldActiveLaws






namespace MatrixMultiplication.AllFieldGroupNativeLaws

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldActiveLaws
open AllFieldNativeCapacity AllFieldPairMarginals AllFieldPairConditionalEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem supportedHalfLaw_eq_of_counts_pos {K tick : ℕ} (allocation : Allocation)
    (m : ℕ) (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (side : Fin 3) :
    supportedHalfLaw allocation right h u side = halfLawAt right h u side := by
  have hbase : 0 < activeCounts allocation 1 h u := by
    rw [AllFieldHistorySupport.activeCounts_dilation] at hu
    exact Nat.pos_of_mul_pos_left hu
  simp only [supportedHalfLaw, hbase, ite_true, if_true]

theorem placement_symm_order_side {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) :
    h.val.val.2.symm (sigma side) = h.val.val.1.priority side := by
  have hs : h.val.val.2 (h.val.val.1.priority side) = sigma side :=
    Equiv.congr_fun h.property side
  rw [← hs, Equiv.symm_apply_apply]

theorem order_branch_weight {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) (b : h.val.val.1.Branch) :
    JointPopulation.shapeSide (sigma side) (branchShape h.val.val b) =
      nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side) b := by
  apply Fin.ext
  rw [branchShape, encodePhysicalShape_side, nativeSplitWeightCode_val,
    placement_symm_order_side]

end MatrixMultiplication.AllFieldGroupNativeLaws






namespace MatrixMultiplication.AllFieldGroupBranchLaws

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldActiveLaws
open AllFieldGroupNativeLaws
attribute [local instance] Classical.propDecidable Classical.decEq

theorem jointCounts_branch_pos {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) (b : w.1.Branch)
    (hb : 0 < (branchLaw w.1).mass b) :
    0 < jointCounts allocation dilation w (branchShape w b) := by
  have hp : 0 < (population allocation dilation (w.1.source, w.2) : ℝ) := by
    exact_mod_cast work_source_population_pos allocation hd w
  have hc : 0 < (jointCounts allocation dilation w (branchShape w b) : ℝ) := by
    rw [jointCounts_cast, placedLaw_mass_branch]
    exact mul_pos hp hb
  exact_mod_cast hc

theorem supportedHalfLaw_branchShape_of_mass_pos {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (right : Bool) (h : ActiveOrder K tick sigma)
    (b : h.val.val.1.Branch) (hb : 0 < (branchLaw h.val.val.1).mass b)
    (side : Fin 3) :
    supportedHalfLaw allocation right h.val (branchShape h.val.val b) (sigma side) =
      fun a => (h.val.val.1.childLaw
        (halfShape h.val.val.1.parentShape (h.val.val.1.splitShape b) right)
        (h.val.val.1.priority side) a : ℝ) := by
  have hc : 0 < activeCounts allocation 1 h.val (branchShape h.val.val b) :=
    jointCounts_branch_pos allocation (by decide) h.val.val b hb
  rw [supportedHalfLaw_eq_of_counts_pos allocation 1 right h.val _ hc]
  funext a
  rw [halfLawAt_eq, canonicalChildShape_branchShape, placement_symm_order_side]

theorem supportedHalfLaw_branchShape_of_mass_ne_zero {K tick : ℕ}
    {sigma : Placement} (allocation : Allocation) (right : Bool)
    (h : ActiveOrder K tick sigma) (b : h.val.val.1.Branch)
    (hb : (branchLaw h.val.val.1).mass b ≠ 0) (side : Fin 3) :
    supportedHalfLaw allocation right h.val (branchShape h.val.val b) (sigma side) =
      fun a => (h.val.val.1.childLaw
        (halfShape h.val.val.1.parentShape (h.val.val.1.splitShape b) right)
        (h.val.val.1.priority side) a : ℝ) := by
  exact supportedHalfLaw_branchShape_of_mass_pos allocation right h b
    (lt_of_le_of_ne ((branchLaw h.val.val.1).nonneg b) (Ne.symm hb)) side

end MatrixMultiplication.AllFieldGroupBranchLaws

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupBranchDesignation
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldGroupBranchDesignation

open AllFieldHistory AllFieldHistoryChildLaws AllFieldGroupOrbitData
open AllFieldGroupNativeLaws
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sharing_iff_stage_ne_two {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) :
    sharing h = true ↔ h.val.val.1.stage ≠ 2 := by
  rcases h with ⟨⟨⟨w, phi⟩, ht⟩, ho⟩
  cases w <;> simp [sharing, Work.stage]

theorem order_branch_childWeight {K tick : ℕ} {sigma : Placement}
    (right : Bool) (h : ActiveOrder K tick sigma) (side : Fin 3)
    (b : h.val.val.1.Branch) :
    childWeight right h.val (branchShape h.val.val b) (sigma side) =
      (halfShape h.val.val.1.parentShape (h.val.val.1.splitShape b) right)
        (h.val.val.1.priority side) := by
  rw [← halfShape_childWeight, canonicalChildShape_branchShape,
    placement_symm_order_side]

theorem designated_branchShape {K tick : ℕ} {sigma : Placement}
    (right : Bool) (side : Fin 3) (h : ActiveOrder K tick sigma)
    (hside : side ≠ 0) (b : h.val.val.1.Branch) :
    AllFieldGroupOrbitData.designated right side sigma h (branchShape h.val.val b) ↔
      nativeBranchDesignated h.val.val.1 right side b := by
  change (sharing h = true ∧
    (if side = 1 then childWeight right h.val (branchShape h.val.val b) (sigma 2) = 0
      else if side = 2 then
        childWeight right h.val (branchShape h.val.val b) (sigma 0) *
          childWeight right h.val (branchShape h.val.val b) (sigma 1) = 0
      else False)) ↔ _
  rw [sharing_iff_stage_ne_two]
  simp only [order_branch_childWeight, nativeBranchDesignated,
    AllFieldNativeCapacity.designated]
  fin_cases side
  · exact False.elim (hside rfl)
  · simp
  · simp

end MatrixMultiplication.AllFieldGroupBranchDesignation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupProjectedEntropy
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

namespace MatrixMultiplication.JointGroupedEntropyPartition

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open JointNativeGroupedEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section FiniteGroups

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

omit [Fintype K] in
theorem groupMass_mul (s : ℝ) (p : U → ℝ) (group : U → K) (k : K) :
    JointCompatibilityIncidence.groupMass (fun u => s * p u) group k =
      s * JointCompatibilityIncidence.groupMass p group k := by
  unfold JointCompatibilityIncidence.groupMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : group u = k <;> simp [hu]

omit [Fintype K] [Fintype A] in
theorem groupMeasure_mul (s : ℝ) (p : U → ℝ) (group : U → K)
    (q : U → A → ℝ) (k : K) :
    groupMeasure (fun u => s * p u) group q k =
      fun a => s * groupMeasure p group q k a := by
  funext a
  unfold groupMeasure
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : group u = k <;> simp [hu, mul_assoc]

omit [Fintype K] [Fintype A] in
theorem groupLaw_mul_of_ne_zero (s : ℝ) (hs : s ≠ 0) (p : U → ℝ)
    (group : U → K) (q : U → A → ℝ) (k : K) :
    JointCompatibilityIncidence.groupLaw (fun u => s * p u) group q k =
      JointCompatibilityIncidence.groupLaw p group q k := by
  funext a
  change groupMeasure (fun u => s * p u) group q k a /
      JointCompatibilityIncidence.groupMass (fun u => s * p u) group k =
    groupMeasure p group q k a / JointCompatibilityIncidence.groupMass p group k
  rw [groupMeasure_mul, groupMass_mul]
  exact mul_div_mul_left _ _ hs

theorem groupedEntropy_mul (s : ℝ) (p : U → ℝ) (group : U → K)
    (q : U → A → ℝ) :
    JointCompatibilityIncidence.groupedEntropy (fun u => s * p u) group q =
      s * JointCompatibilityIncidence.groupedEntropy p group q := by
  by_cases hs : s = 0
  · simp [hs, JointCompatibilityIncidence.groupedEntropy,
      JointCompatibilityIncidence.groupMass]
  · unfold JointCompatibilityIncidence.groupedEntropy
    simp only [groupMass_mul, groupLaw_mul_of_ne_zero s hs, mul_assoc, Finset.mul_sum]

end FiniteGroups

end MatrixMultiplication.JointGroupedEntropyPartition

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointGroupedEntropyEmbedding

open MatrixMultiplication.Foundation JointCompatibilityIncidence JointNativeGroupedEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {U V K L A : Type*}
  [Fintype U] [Fintype V] [Fintype K] [Fintype L] [Fintype A]

omit [Fintype K] [Fintype L] in
theorem groupMass_label_injective (j : K → L) (hj : Function.Injective j)
    (p : U → ℝ) (group : U → K) (k : K) :
    groupMass p (j ∘ group) (j k) = groupMass p group k := by
  simp only [groupMass, Function.comp_apply, hj.eq_iff]

omit [Fintype K] [Fintype L] [Fintype A] in
theorem groupLaw_label_injective (j : K → L) (hj : Function.Injective j)
    (p : U → ℝ) (group : U → K) (q : U → A → ℝ) (k : K) :
    groupLaw p (j ∘ group) q (j k) = groupLaw p group q k := by
  funext a
  simp only [groupLaw, groupMass_label_injective j hj,
    Function.comp_apply, hj.eq_iff]

omit [Fintype K] [Fintype L] in
theorem groupMass_label_not_mem_range (j : K → L) (p : U → ℝ)
    (group : U → K) (l : L) (hl : l ∉ Set.range j) :
    groupMass p (j ∘ group) l = 0 := by
  apply Finset.sum_eq_zero
  intro u _
  exact ite_eq_right (fun h => hl ⟨group u, h⟩)

theorem groupedEntropy_label_injective (j : K → L) (hj : Function.Injective j)
    (p : U → ℝ) (group : U → K) (q : U → A → ℝ) :
    groupedEntropy p (j ∘ group) q = groupedEntropy p group q := by
  unfold groupedEntropy
  symm
  apply Fintype.sum_of_injective j hj
  · intro l hl
    rw [groupMass_label_not_mem_range j p group l hl, zero_mul]
  · intro k
    rw [groupMass_label_injective j hj, groupLaw_label_injective j hj]

theorem sum_pushforwardWeight_mul (p : U → ℝ) (f : U → V) (test : V → ℝ) :
    (∑ v, pushforwardWeight p f v * test v) = ∑ u, p u * test (f u) := by
  simp only [pushforwardWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [ite_mul, zero_mul]
  simp

omit [Fintype K] in
theorem groupMass_pushforward (p : U → ℝ) (f : U → V)
    (group : V → K) (k : K) :
    groupMass (pushforwardWeight p f) group k = groupMass p (group ∘ f) k := by
  simpa only [groupMass, mul_ite, mul_one, mul_zero, Function.comp_apply] using
    (sum_pushforwardWeight_mul p f (fun v => if group v = k then 1 else 0))

omit [Fintype K] [Fintype A] in
theorem groupMeasure_pushforward (p : U → ℝ) (f : U → V)
    (group : V → K) (q : V → A → ℝ) (k : K) :
    groupMeasure (pushforwardWeight p f) group q k =
      groupMeasure p (group ∘ f) (q ∘ f) k := by
  funext a
  simpa only [groupMeasure, mul_ite, mul_zero, Function.comp_apply] using
    (sum_pushforwardWeight_mul p f (fun v => if group v = k then q v a else 0))

omit [Fintype K] [Fintype A] in
theorem groupLaw_pushforward (p : U → ℝ) (f : U → V)
    (group : V → K) (q : V → A → ℝ) (k : K) :
    groupLaw (pushforwardWeight p f) group q k =
      groupLaw p (group ∘ f) (q ∘ f) k := by
  funext a
  change groupMeasure (pushforwardWeight p f) group q k a /
      groupMass (pushforwardWeight p f) group k =
    groupMeasure p (group ∘ f) (q ∘ f) k a / groupMass p (group ∘ f) k
  rw [groupMeasure_pushforward, groupMass_pushforward]

theorem groupedEntropy_pushforward (p : U → ℝ) (f : U → V)
    (group : V → K) (q : V → A → ℝ) :
    groupedEntropy (pushforwardWeight p f) group q =
      groupedEntropy p (group ∘ f) (q ∘ f) := by
  simp only [groupedEntropy, groupMass_pushforward, groupLaw_pushforward]

end MatrixMultiplication.JointGroupedEntropyEmbedding

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupProjectedEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldGroupDegrees
open AllFieldGroupNativeLaws AllFieldGroupPairWindows AllFieldGroupDegreeLaws
open JointCompatibilityScaling JointCompatibilityRateLimit JointCompatibilityControls
open JointCompatibilityIncidence JointGroupedEntropyEmbedding JointGroupedEntropyPartition
open AllFieldGroupBranchDesignation AllFieldGroupBranchLaws AllFieldNativeGroupedRates
open AllFieldScheduledYield AllFieldGroupPairEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section Kernel

variable {U V G A : Type*} [Fintype U] [Fintype V] [Fintype G] [Fintype A]

theorem groupedEntropy_congr_law_on_support (p : U → ℝ) (group : U → G)
    (q q' : U → A → ℝ) (hq : ∀ u, p u ≠ 0 → q u = q' u) :
    groupedEntropy p group q = groupedEntropy p group q' := by
  have he (g : G) : groupLaw p group q g = groupLaw p group q' g := by
    funext a
    unfold groupLaw
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    by_cases hp : p u = 0
    · simp only [hp, zero_mul]
    · rw [hq u hp]
  simp only [groupedEntropy, he]

theorem groupedEntropy_designated_pushforward (p : U → ℝ) (f : U → V)
    (hf : Function.Injective f) (d : V → Prop) (d' : U → Prop)
    (hd : ∀ u, d (f u) ↔ d' u) (q : V → A → ℝ) (q' : U → A → ℝ)
    (hq : ∀ u, p u ≠ 0 → q (f u) = q' u) :
    groupedEntropy (pushforwardWeight p f) (designatedGroup d) q =
      groupedEntropy p (designatedGroup d') q' := by
  rw [groupedEntropy_pushforward]
  have hg : designatedGroup d ∘ f = Option.map f ∘ designatedGroup d' := by
    funext u
    by_cases hu : d' u
    · simp [designatedGroup, (hd u).mpr hu, hu]
    · simp [designatedGroup, mt (hd u).mp hu, hu]
  rw [hg, groupedEntropy_label_injective (Option.map f) (Option.map_injective hf)]
  exact groupedEntropy_congr_law_on_support p _ _ q' hq

end Kernel

variable {K tick : ℕ} {sigma : Placement}

theorem classCounts_cast_eq_pushforward (allocation : Allocation) (side : Fin 3)
    (h : ActiveOrder K tick sigma) (k : Fin 17) :
    (fun u => (base allocation sigma side (h, k) u : ℝ)) =
      fun u => (parentBase allocation h : ℝ) *
        pushforwardWeight (maskedBranchMass h side k) (branchShape h.val.val) u := by
  have hpmap : (placedLaw h.val.val).mass =
      pushforwardWeight (branchLaw h.val.val.1).mass (branchShape h.val.val) := by
    funext u
    simp only [placedLaw, FiniteLaw.map_mass, pushforwardWeight]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : branchShape h.val.val b = u <;> simp only [hb, ite_true, if_true, ite_false, if_false]
  have hm : (fun u => if JointPopulation.shapeSide (sigma side) u = k
      then (placedLaw h.val.val).mass u else 0) =
      pushforwardWeight (maskedBranchMass h side k) (branchShape h.val.val) := by
    rw [hpmap]
    funext u
    unfold pushforwardWeight maskedBranchMass
    by_cases hu : JointPopulation.shapeSide (sigma side) u = k
    · simp only [hu, ite_true, if_true]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : branchShape h.val.val b = u
      · have hk : nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side) b = k := by
          rw [← order_branch_weight h side b, hb]
          exact hu
        simp only [hb, hk, ite_true, if_true]
      · simp only [hb, ite_false, if_false]
    · simp only [hu, ite_false, if_false]
      symm
      apply Finset.sum_eq_zero
      intro b _
      by_cases hb : branchShape h.val.val b = u
      · have hk : nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side) b ≠ k := by
          rw [← order_branch_weight h side b, hb]
          exact hu
        simp only [hb, hk, ite_true, if_true, ite_false, if_false]
      · simp only [hb, ite_false, if_false]
  funext u
  change ((if JointPopulation.shapeSide (sigma side) u = k
    then Counts allocation 1 sigma h u else 0 : ℕ) : ℝ) = _
  rw [Nat.cast_ite, Nat.cast_zero]
  rw [← hm]
  by_cases hu : JointPopulation.shapeSide (sigma side) u = k
  · simp only [hu, ite_true, if_true]
    exact jointCounts_cast allocation 1 h.val.val u
  · simp only [hu, ite_false, if_false, mul_zero]

theorem class_groupedEntropy_eq_masked_oai (allocation : Allocation) (right : Bool)
    (side : Fin 3) (hside : side ≠ 0) (h : ActiveOrder K tick sigma) (k : Fin 17) :
    groupedEntropy (fun u => (base allocation sigma side (h, k) u : ℝ))
      (designatedGroup (classDesignated right side sigma (h, k)))
      (nativeLaw allocation right side sigma (h, k)) =
      (parentBase allocation h : ℝ) *
        groupedEntropy (maskedBranchMass h side k)
          (designatedGroup (nativeBranchDesignated h.val.val.1 right side))
          (branchHalfLaw h.val.val.1 right side) := by
  rw [classCounts_cast_eq_pushforward, groupedEntropy_mul]
  congr 1
  apply groupedEntropy_designated_pushforward _ _ (branchShape_injective h.val.val)
    _ _ (fun b => designated_branchShape right side h hside b)
  intro b hb
  have hp : (branchLaw h.val.val.1).mass b ≠ 0 := by
    intro hp
    apply hb
    simp only [maskedBranchMass, hp, ite_self]
  exact supportedHalfLaw_branchShape_of_mass_ne_zero allocation right h b hp side

end MatrixMultiplication.AllFieldGroupProjectedEntropy

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.class_groupedEntropy_eq_masked_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.class_groupedEntropy_eq_masked_oai
