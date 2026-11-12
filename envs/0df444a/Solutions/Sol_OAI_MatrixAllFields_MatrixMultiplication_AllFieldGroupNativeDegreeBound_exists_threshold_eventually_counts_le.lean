-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:18:47.331044+00:00
-- url     : https://prove2.me/submissions/c7e273a9-424e-4093-b935-eb9c9a17143a

import Mathlib
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupCountRate_exists_widths_eventually_nativeCount_le
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupDegreeLaws_eventually_eligibility_card_le
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupNativeDegreeBound_nativeCompatibilityRate_eq

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointPairClassWindows
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section






namespace MatrixMultiplication.JointPairClassWindows

open MatrixMultiplication.Foundation

attribute [local instance] Classical.propDecidable

variable {I A C : Type*} [Fintype I] [Fintype A] [Fintype C]
  [DecidableEq I] [DecidableEq A] [DecidableEq C]

omit [Fintype A] [Fintype C] [DecidableEq I] in
theorem fiber_population (z : I → A) (k : I → C) (f : A → C)
    (hf : ∀ i, f (z i) = k i) (c : C) (a : A) :
    wordPopulation (fiberWord z k c) a =
      if f a = c then wordPopulation z a else 0 := by
  classical
  by_cases ha : f a = c
  · rw [ite_eq_left ha]
    unfold wordPopulation
    apply Fintype.card_congr
    exact
      { toFun := fun i => ⟨i.val.val, i.property⟩
        invFun := fun i => ⟨⟨i.val, by rw [← hf i.val, i.property, ha]⟩, i.property⟩
        left_inv := fun ⟨⟨i, hi⟩, hia⟩ => rfl
        right_inv := fun ⟨i, hia⟩ => rfl }
  · rw [ite_eq_right ha]
    let : IsEmpty {i : Fiber k c // fiberWord z k c i = a} :=
      ⟨fun i => ha (calc
        f a = f (z i.val.val) := congrArg f i.property.symm
        _ = k i.val.val := hf _
        _ = c := i.val.property)⟩
    exact Fintype.card_eq_zero

omit [Fintype A] [Fintype C] [DecidableEq I] in
theorem fiber_window (z : I → A) (k : I → C) (f : A → C)
    (hf : ∀ i, f (z i) = k i) (c : C) (q : A → ℝ) (mass η : ℝ)
    (hmass : 0 < mass) (hη : 0 ≤ η)
    (hclass : (Fintype.card (Fiber k c) : ℝ) = (Fintype.card I : ℝ) * mass)
    (hwindow : ∀ a, |(wordPopulation z a : ℝ) / Fintype.card I - q a| ≤ η) :
    ∀ a, |(wordPopulation (fiberWord z k c) a : ℝ) / Fintype.card (Fiber k c) -
      conditionalCenter f c q mass a| ≤ η / mass := by
  intro a
  rw [fiber_population z k f hf c a]
  by_cases ha : f a = c
  · simp only [ha, ite_true, if_true, conditionalCenter]
    rw [hclass]
    have hid : (wordPopulation z a : ℝ) / ((Fintype.card I : ℝ) * mass) - q a / mass =
        ((wordPopulation z a : ℝ) / Fintype.card I - q a) / mass := by
      rw [sub_div, div_div]
    rw [hid, abs_div, abs_of_pos hmass]
    exact div_le_div_of_nonneg_right (hwindow a) hmass.le
  · simp only [ha, ite_false, if_false, Nat.cast_zero, zero_div, conditionalCenter, sub_zero, abs_zero]
    exact div_nonneg hη hmass.le

end MatrixMultiplication.JointPairClassWindows

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryChildLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.nativeSplitWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.half_unhalfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.unhalf_halfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl
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

open AllFieldParameters CWStrands CWWindowedLeaves
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem Work.statistic_weight {K : ℕ} (w : Work K) (hsharing : w.stage ≠ 2)
    (x : Raw w.halfLength) : CWStrands.weight x = w.statisticWeight (w.statistic x) := by
  cases w with
  | stageA h => exact CWCompleteStatistics.four_weight x
  | stageB h => exact CWCompleteStatistics.two_weight x
  | stageC h => exact False.elim (hsharing rfl)

theorem Work.childLaw_outside_support {K : ℕ} (w : Work K) (hsharing : w.stage ≠ 2)
    (u : Shape) (hu : u ∈ shapes (2 * w.halfLength)) (side : Fin 3)
    (a : w.Statistic) (ha : w.statisticWeight a ≠ u side) : w.childLaw u side a = 0 := by
  cases w with
  | stageA h => exact halfLaw_outside_support u hu side a ha
  | stageB h =>
      have hbound : u side < 5 :=
        lt_of_le_of_lt (mem_shapes_bound hu side) (by norm_num [Work.halfLength])
      exact littleLaw_outside_support (aShape h.val) u side hbound a ha
  | stageC h => exact False.elim (hsharing rfl)

theorem leftChildLaw_normalized_of_pos {K tick : ℕ} (allocation : Allocation)
    (dilation : ℕ) (side : Fin 3) (c : Active K tick × JointPopulation.Shape)
    (hc : 0 < activeCounts allocation dilation c.1 c.2) :
    ∑ a : ActiveStatistic c.1, leftChildLaw side c a = 1 := by
  change (∑ a : c.1.val.1.Statistic,
    (placedChildLawRat c.1.val c.2 side false a : ℝ)) = 1
  exact_mod_cast placedChildLawRat_normalized_of_pos allocation dilation
    c.1.val c.2 hc side false

end MatrixMultiplication.AllFieldHistory

namespace MatrixMultiplication.AllFieldHistoryChildLaws

open AllFieldHistory
open scoped BigOperators

theorem leftLaw_normalized {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation dilation h u) (side : Fin 3) :
    ∑ a : Statistic h, leftLaw h u side a = 1 :=
  leftChildLaw_normalized_of_pos allocation dilation side (h, u) hu

end MatrixMultiplication.AllFieldHistoryChildLaws

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointPopulationMixedCompatibility
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationCompatibility

open MatrixMultiplication.Foundation JointPopulation JointTypeCounts InheritedMasks
open JointCompatibilityIncidence
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
  (counts : H → Shape → ℕ)

omit [Fintype H] [DecidableEq H] in
theorem classCounts_size (s : Fin 3) (b : Position counts → Fin 17)
    (e : FixedSideTargets counts s b) (c : ClassKey (H := H)) :
    Fintype.card (ClassPos counts b c) = ∑ u, classCounts counts s c u := by
  calc
    Fintype.card (ClassPos counts b c) =
        ∑ u, wordPopulation ((candidateEquiv counts s b e) c).val u :=
      (wordPopulation_sum _).symm
    _ = ∑ u, classCounts counts s c u :=
      Finset.sum_congr rfl fun u _ => ((candidateEquiv counts s b e) c).property u

section Statistics

variable (L R : H → Type*)
  (SL SR : ClassKey (H := H) → Type*)
  [∀ c, Fintype (SL c)] [∀ c, DecidableEq (SL c)]
  [∀ c, Fintype (SR c)] [∀ c, DecidableEq (SR c)]
  (leftStatistic : ∀ c, L c.1 → SL c)
  (rightStatistic : ∀ c, R c.1 → SR c)

variable (designatedLeft designatedRight : ClassKey (H := H) → Shape → Prop)
  (leftLaw : ∀ c, Shape → SL c → ℝ) (rightLaw : ∀ c, Shape → SR c → ℝ) (χ : ℝ)

omit [Fintype H] [DecidableEq H] in
theorem compatibleByTriple_target (s : Fin 3) (e : Target counts)
    (w : JointCanonicalization.RawPairs counts L R) :
    compatibleByTriple counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ s (triple counts e) w ↔
    Compatible counts L R SL SR leftStatistic rightStatistic designatedLeft designatedRight
      leftLaw rightLaw χ s e w := by
  constructor
  · rintro ⟨f, hf, hw⟩
    have he : f = e := triple_injective counts hf
    subst f
    exact hw
  · intro hw
    exact ⟨e, rfl, hw⟩

omit [Fintype H] [DecidableEq H] in
theorem compatibleWithCoarse_target
    (ownCoarse : JointCanonicalization.RawPairs counts L R → Position counts → Fin 17)
    (s : Fin 3) (e : Target counts) (w : JointCanonicalization.RawPairs counts L R) :
    compatibleWithCoarse counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ ownCoarse s (triple counts e) w ↔
    (∀ h i, shapeSide s ((e h).val i) = ownCoarse w ⟨h, i⟩) ∧
      Compatible counts L R SL SR leftStatistic rightStatistic designatedLeft designatedRight
        leftLaw rightLaw χ s e w := by
  exact and_congr Iff.rfl (compatibleByTriple_target counts L R SL SR leftStatistic
    rightStatistic designatedLeft designatedRight leftLaw rightLaw χ s e w)

theorem compatibleWithCoarse_target_count
    (ownCoarse : JointCanonicalization.RawPairs counts L R → Position counts → Fin 17)
    (s : Fin 3) (w : JointCanonicalization.RawPairs counts L R) :
    Fintype.card {e : Target counts //
      compatibleWithCoarse counts L R SL SR leftStatistic rightStatistic
        designatedLeft designatedRight leftLaw rightLaw χ ownCoarse s (triple counts e) w} =
    compatibleTargetCount counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ s (ownCoarse w) w := by
  apply Fintype.card_congr
  exact (Equiv.subtypeEquivRight (fun e => compatibleWithCoarse_target counts L R SL SR
    leftStatistic rightStatistic designatedLeft designatedRight leftLaw rightLaw χ
      ownCoarse s e w)).trans (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun e : Target counts => ∀ h i, shapeSide s ((e h).val i) = ownCoarse w ⟨h, i⟩)
        (fun e => Compatible counts L R SL SR leftStatistic rightStatistic
          designatedLeft designatedRight leftLaw rightLaw χ s e w)).symm

end Statistics

end MatrixMultiplication.JointPopulationCompatibility






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointMarginalSupport
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.nativeSplitWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section






namespace MatrixMultiplication.AllFieldGroupDegrees

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData JointPopulation JointCanonicalization
open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem tripleSide_triple (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (s : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (h : ActiveOrder K tick sigma) (i : JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) :
    tripleSide s (triple (Counts (K := K) (tick := tick) allocation m sigma) e) ⟨h, i⟩ =
      shapeSide s ((e h).val i) := by
  fin_cases s <;> rfl

theorem childWidth_le {ε : ℝ} (hε : 0 ≤ ε) (h : Active K tick) :
    AllFieldHistoryMasks.childWidth ε h ≤ ε := by
  have hp : 0 ≤ AllFieldHistoryMasks.pairWidth ε h := by
    unfold AllFieldHistoryMasks.pairWidth
    positivity
  calc
    AllFieldHistoryMasks.childWidth ε h ≤ AllFieldHistoryMasks.pairWidth ε h :=
      div_le_self hp (by norm_num)
    _ ≤ ε := div_le_self hε (one_le_pow₀ (by norm_num))

theorem fineCompatible_uniform (allocation : Allocation) (m : ℕ)
    {ε χ : ℝ} (hε : 0 ≤ ε) (hχ : ε ≤ χ) (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : fineCompatible allocation m ε sigma side e w) :
    JointPopulationCompatibility.Compatible (Counts (K := K) (tick := tick) allocation m sigma)
      (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
      (projectedStatistic sigma) (projectedStatistic sigma)
      (classDesignated false side sigma) (classDesignated true side sigma)
      (classLaw false side sigma) (classLaw true side sigma) χ (sigma side) e w := by
  constructor
  · intro h u hd a
    exact (hw false h u hd a).trans
      (mul_le_mul_of_nonneg_left ((childWidth_le hε h.val).trans hχ) (Nat.cast_nonneg _))
  · intro h u hd a
    exact (hw true h u hd a).trans
      (mul_le_mul_of_nonneg_left ((childWidth_le hε h.val).trans hχ) (Nat.cast_nonneg _))

theorem Compatible_uniform (allocation : Allocation) (m : ℕ)
    {ε χ : ℝ} (hε : 0 ≤ ε) (hχ : ε ≤ χ) (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : Compatible allocation m ε sigma side e w) :
    uniformCompatible allocation m χ sigma side e w := by
  apply (JointPopulationCompatibility.compatibleWithCoarse_target
    (Counts (K := K) (tick := tick) allocation m sigma) (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma)
    (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (classLaw false side sigma) (classLaw true side sigma) χ
    (ownWord allocation m sigma) (sigma side) e w).2
  refine ⟨?_, fineCompatible_uniform allocation m hε hχ sigma side e w hw.2⟩
  intro h i
  have hh := congrFun hw.1 ⟨h, i⟩
  simpa only [coarse, tripleSide_reorder, tripleSide_triple] using hh

theorem uniformCompatible_count (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) :
    Fintype.card {e : Targets (K := K) (tick := tick) allocation m sigma //
      uniformCompatible allocation m χ sigma side e w} =
      conditionalCount allocation m χ sigma side w :=
  JointPopulationCompatibility.compatibleWithCoarse_target_count
    (Counts (K := K) (tick := tick) allocation m sigma) (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma)
    (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (classLaw false side sigma) (classLaw true side sigma) χ
    (ownWord allocation m sigma) (sigma side) w

theorem competitors_card_le_conditionalCount (allocation : Allocation) (m : ℕ)
    {ε χ : ℝ} (hε : 0 ≤ ε) (hχ : ε ≤ χ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma) :
    (competitors allocation m ε sigma e o v).card ≤
      conditionalCount allocation m χ sigma v.1 v.2 := by
  classical
  let candidates : Finset (Targets (K := K) (tick := tick) allocation m sigma) :=
    Finset.univ.filter fun f => uniformCompatible allocation m χ sigma v.1 f v.2
  have hsub : competitors allocation m ε sigma e o v ⊆
      candidates.image (coarse allocation m sigma) := by
    intro t ht
    obtain ⟨f, hf, hc⟩ := (Finset.mem_filter.mp ht).2.2.2
    exact Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Compatible_uniform allocation m hε hχ sigma v.1 f v.2 hc⟩, hf⟩
  calc
    (competitors allocation m ε sigma e o v).card ≤
        (candidates.image (coarse allocation m sigma)).card := Finset.card_le_card hsub
    _ ≤ candidates.card := Finset.card_image_le
    _ = Fintype.card {f : Targets (K := K) (tick := tick) allocation m sigma //
        uniformCompatible allocation m χ sigma v.1 f v.2} := by
      simp only [candidates, Fintype.card_subtype]
    _ = conditionalCount allocation m χ sigma v.1 v.2 :=
      uniformCompatible_count allocation m χ sigma v.1 v.2

end MatrixMultiplication.AllFieldGroupDegrees






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






namespace MatrixMultiplication.AllFieldGroupNativeLaws

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldActiveLaws
open AllFieldNativeCapacity AllFieldPairMarginals AllFieldPairConditionalEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem halfLawAt_normalized {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (side : Fin 3) :
    ∑ a, halfLawAt right h u side a = 1 := by
  cases right
  · exact leftLaw_normalized allocation m h u hu side
  · exact rightLaw_normalized allocation m h u hu side

theorem supportedHalfLaw_eq_of_counts_pos {K tick : ℕ} (allocation : Allocation)
    (m : ℕ) (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (side : Fin 3) :
    supportedHalfLaw allocation right h u side = halfLawAt right h u side := by
  have hbase : 0 < activeCounts allocation 1 h u := by
    rw [AllFieldHistorySupport.activeCounts_dilation] at hu
    exact Nat.pos_of_mul_pos_left hu
  simp only [supportedHalfLaw, hbase, ite_true, if_true]

end MatrixMultiplication.AllFieldGroupNativeLaws






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_GroupPairWindows
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupPairWindows

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistorySupport
open AllFieldHistoryChildLaws AllFieldHistoryMasks AllFieldHistoryMaskLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupNativeLaws
open JointCompatibilityScaling JointCompatibilityRateLimit
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ} {sigma : Placement}

theorem windowFactor_pos (allocation : Allocation) (sigma : Placement) :
    0 < windowFactor (K := K) (tick := tick) allocation sigma := by
  unfold windowFactor
  positivity

theorem parentBase_pos (allocation : Allocation) (h : ActiveOrder K tick sigma) :
    0 < parentBase (K := K) (tick := tick) allocation h :=
  AllFieldHistorySupport.work_source_population_pos allocation (by decide : 0 < (1 : ℕ)) h.val.val

theorem parent_positions_card (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (h : ActiveOrder K tick sigma) :
    Fintype.card (JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) =
      m * parentBase (K := K) (tick := tick) allocation h := by
  change Fintype.card (Fin (∑ u, jointCounts allocation m h.val.val u)) = _
  rw [Fintype.card_fin, jointCounts_sum]
  exact population_dilation allocation m _

theorem positions_card (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w)
    (c : Class (K := K) (tick := tick) sigma) :
    Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) =
      m * baseSize (base (K := K) (tick := tick) allocation sigma side) c := by
  have he : JointPopulationCompatibility.FixedSideTargets (Counts (K := K) (tick := tick) allocation m sigma)
      (sigma side) (ownWord (K := K) (tick := tick) allocation m sigma w) :=
    ⟨e, fun h j => (hw.1.1 h j).symm⟩
  rw [JointPopulationCompatibility.classCounts_size
    (Counts (K := K) (tick := tick) allocation m sigma) (sigma side) (ownWord (K := K) (tick := tick) allocation m sigma w) he c]
  simp only [JointPopulationCompatibility.classCounts, Counts, groupCounts,
    activeCounts_dilation allocation m, base, baseSize, Finset.mul_sum, mul_ite, mul_zero]

theorem parentPair_eq_parentCenter (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (h : ActiveOrder K tick sigma)
    (a : Statistic h.val × Statistic h.val) :
    parentPair (K := K) (tick := tick) allocation sigma side h a = parentCenter allocation (sigma side) h.val a.1 a.2 := by
  unfold parentPair parentCenter parentBase
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : 0 < activeCounts allocation 1 h.val u
  · simp only [supportedHalfLaw, ite_eq_left hu, halfLawAt, Bool.false_eq_true,
      ite_false, if_false, ite_true, if_true]
    ring
  · have hz := Nat.eq_zero_of_not_pos hu
    simp only [hz, Nat.cast_zero, zero_mul, zero_div]

theorem parent_window (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : AllFieldHistoryGroupMasks.rawPass allocation m ε (sigma side) sigma w)
    (h : ActiveOrder K tick sigma) (a : Statistic h.val × Statistic h.val) :
    |(wordPopulation (parentStatistic (K := K) (tick := tick) allocation m sigma w h) a : ℝ) /
      Fintype.card (JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) -
        parentPair (K := K) (tick := tick) allocation sigma side h a| ≤ pairWidth ε h.val := by
  let defaults : SymbolChoice K tick := fun h => statistic h (fun _ => 0)
  let l : SymbolChoice K tick := Function.update defaults h.val a.1
  let r : SymbolChoice K tick := Function.update defaults h.val a.2
  have hp := hw (h.val, l, r) h.property
  rw [center_eq_parentCenter] at hp
  simp only [l, r, Function.update_self] at hp
  rw [parentPair_eq_parentCenter]
  have hpop : Fintype.card (JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) =
      population allocation m (h.val.val.1.source, h.val.val.2) := by
    change Fintype.card (Fin (∑ u, jointCounts allocation m h.val.val u)) = _
    rw [Fintype.card_fin]
    exact jointCounts_sum allocation m h.val.val
  rw [hpop]
  have hcount : (wordPopulation (parentStatistic (K := K) (tick := tick) allocation m sigma w h) a : ℝ) =
      ∑ j : JointPopulation.Positions (activeCounts allocation m) h.val,
        if statistic h.val (w h j).1 = a.1 ∧ statistic h.val (w h j).2 = a.2
          then (1 : ℝ) else 0 := by
    rcases a with ⟨a₁, a₂⟩
    simp only [wordPopulation, Fintype.card_subtype, Finset.card_eq_sum_ones,
      Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      parentStatistic, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> rfl
  rw [hcount]
  exact hp

theorem weightCode_statistic {K : ℕ} (w : Work K) (hs : w.stage ≠ 2)
    (x : CWWindowedLeaves.Raw w.halfLength) :
    (weightCode w (w.statistic x)).val = CWStrands.weight x :=
  (weightCode_val w _).trans (w.statistic_weight hs x).symm

theorem left_supported_zero (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (h : ActiveOrder K tick sigma) (hs : h.val.val.1.stage ≠ 2)
    (u : JointPopulation.Shape) (a : Statistic h.val)
    (ha : weightCode h.val.val.1 a ≠ JointPopulation.shapeSide (sigma side) u) :
    supportedHalfLaw allocation false h.val u (sigma side) a = 0 := by
  by_cases hu : 0 < activeCounts allocation 1 h.val u
  · rw [supportedHalfLaw_eq_of_counts_pos allocation 1 false h.val u hu, halfLawAt_eq]
    apply Rat.cast_eq_zero.mpr
    apply h.val.val.1.childLaw_outside_support hs _
      (halfShape_mem_of_counts_pos allocation 1 false h.val u hu) _ a
    rw [halfShape_childWeight]
    simpa only [childWeight, Bool.false_eq_true, ite_false, if_false, ← weightCode_val,
      ne_eq, Fin.ext_iff] using ha
  · simp only [supportedHalfLaw, ite_eq_right hu]

theorem filtered_pair_sum (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) (hs : c.1.val.val.1.stage ≠ 2)
    (a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c) :
    (∑ u, (base (K := K) (tick := tick) allocation sigma side c u : ℝ) *
      supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
      supportedHalfLaw allocation true c.1.val u (sigma side) a.2) =
      if weightCode c.1.val.val.1 a.1 = c.2 then
        ∑ u, (activeCounts allocation 1 c.1.val u : ℝ) *
          supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
          supportedHalfLaw allocation true c.1.val u (sigma side) a.2
      else 0 := by
  have hterm (u : JointPopulation.Shape) :
      (base (K := K) (tick := tick) allocation sigma side c u : ℝ) *
        supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
        supportedHalfLaw allocation true c.1.val u (sigma side) a.2 =
      if weightCode c.1.val.val.1 a.1 = c.2 then
        (activeCounts allocation 1 c.1.val u : ℝ) *
          supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
          supportedHalfLaw allocation true c.1.val u (sigma side) a.2
      else 0 := by
    by_cases hu : JointPopulation.shapeSide (sigma side) u = c.2
    · simp only [base, JointPopulationCompatibility.classCounts, Counts, groupCounts,
        hu, ite_true, if_true]
      by_cases ha : weightCode c.1.val.val.1 a.1 = c.2
      · rw [ite_eq_left ha]
      · have hz := left_supported_zero (K := K) (tick := tick) allocation sigma side c.1 hs u a.1
          (fun he => ha (he.trans hu))
        simp only [ha, ite_false, if_false, hz, mul_zero, zero_mul]
    · simp only [base, JointPopulationCompatibility.classCounts, Counts, groupCounts,
        hu, ite_false, if_false, Nat.cast_zero, zero_mul]
      by_cases ha : weightCode c.1.val.val.1 a.1 = c.2
      · have hz := left_supported_zero (K := K) (tick := tick) allocation sigma side c.1 hs u a.1
          (fun he => hu (he.symm.trans ha))
        simp only [ha, ite_true, if_true, hz, mul_zero, zero_mul]
      · rw [ite_eq_right ha]
  simp_rw [hterm]
  split_ifs <;> simp

theorem q_eq_conditionalCenter (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) (hs : c.1.val.val.1.stage ≠ 2) :
    q (K := K) (tick := tick) allocation sigma side c = JointPairClassWindows.conditionalCenter
      (fun a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c => weightCode c.1.val.val.1 a.1)
      c.2 (parentPair (K := K) (tick := tick) allocation sigma side c.1) (classMass (K := K) (tick := tick) allocation sigma side c) := by
  funext a
  rw [q, JointPairMixtureControls.pairMixture, filtered_pair_sum (K := K) (tick := tick) allocation sigma side c hs]
  unfold JointPairClassWindows.conditionalCenter parentPair classMass
  by_cases ha : weightCode c.1.val.val.1 a.1 = c.2
  · simp only [ha, ite_true, if_true]
    have hp : (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (parentBase_pos (K := K) (tick := tick) allocation c.1))
    rw [div_div_div_cancel_right₀ hp]
  · simp only [ha, ite_false, if_false, zero_div]

theorem classMass_pos (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma)
    (hc : 0 < baseSize (base (K := K) (tick := tick) allocation sigma side) c) :
    0 < classMass (K := K) (tick := tick) allocation sigma side c :=
  div_pos (Nat.cast_pos.mpr hc) (Nat.cast_pos.mpr (parentBase_pos (K := K) (tick := tick) allocation c.1))

theorem fiber_mass (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w)
    (c : Class (K := K) (tick := tick) sigma) :
    (Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) : ℝ) =
      (Fintype.card (JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) c.1) : ℝ) *
        classMass (K := K) (tick := tick) allocation sigma side c := by
  rw [positions_card (K := K) (tick := tick) allocation m ε sigma side e w hw, parent_positions_card]
  rw [Nat.cast_mul, Nat.cast_mul]
  unfold classMass
  have hp : (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (parentBase_pos (K := K) (tick := tick) allocation c.1))
  rw [mul_assoc, mul_div_cancel₀ _ hp]

theorem width_le (allocation : Allocation) {ε : ℝ} (hε : 0 ≤ ε)
    (sigma : Placement) (side : Fin 3) (c : Class (K := K) (tick := tick) sigma)
    (hc : 0 < baseSize (base (K := K) (tick := tick) allocation sigma side) c) :
    pairWidth ε c.1.val / classMass (K := K) (tick := tick) allocation sigma side c ≤
      windowFactor (K := K) (tick := tick) allocation sigma * ε := by
  have hpw : 0 ≤ pairWidth ε c.1.val := by unfold pairWidth; positivity
  have hw : pairWidth ε c.1.val ≤ ε :=
    div_le_self hε (one_le_pow₀ (by norm_num))
  have hb : (1 : ℝ) ≤ baseSize (base (K := K) (tick := tick) allocation sigma side) c := by exact_mod_cast hc
  have hn : (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) ≤ windowFactor (K := K) (tick := tick) allocation sigma := by
    unfold windowFactor
    exact (Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ c.1)).trans
      (le_add_of_nonneg_left zero_le_one)
  unfold classMass
  rw [div_div_eq_mul_div]
  calc
    pairWidth ε c.1.val * (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) /
        (baseSize (base (K := K) (tick := tick) allocation sigma side) c : ℝ) ≤
        pairWidth ε c.1.val * (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) :=
      div_le_self (mul_nonneg hpw (Nat.cast_nonneg _)) hb
    _ ≤ ε * windowFactor (K := K) (tick := tick) allocation sigma := mul_le_mul hw hn (Nat.cast_nonneg _) hε
    _ = _ := mul_comm _ _

theorem sharing_window (allocation : Allocation) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w)
    (hp : AllFieldHistoryGroupMasks.rawPass allocation m ε (sigma side) sigma w)
    (c : Class (K := K) (tick := tick) sigma) (hs : c.1.val.val.1.stage ≠ 2)
    (hc : 0 < baseSize (base (K := K) (tick := tick) allocation sigma side) c)
    (a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c) :
    |(pairCounts (K := K) (tick := tick) allocation m sigma w c a : ℝ) /
        Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) - q (K := K) (tick := tick) allocation sigma side c a| ≤
      windowFactor (K := K) (tick := tick) allocation sigma * ε := by
  let z := parentStatistic (K := K) (tick := tick) allocation m sigma w c.1
  let k : JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) c.1 → Fin 17 :=
    fun j => ownWord (K := K) (tick := tick) allocation m sigma w ⟨c.1, j⟩
  let f : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c → Fin 17 :=
    fun a => weightCode c.1.val.val.1 a.1
  have hf (j) : f (z j) = k j := by
    apply Fin.ext
    exact weightCode_statistic c.1.val.val.1 hs (w c.1 j).1
  have hη : 0 ≤ pairWidth ε c.1.val := by unfold pairWidth; positivity
  have hh := JointPairClassWindows.fiber_window z k f hf c.2
    (parentPair (K := K) (tick := tick) allocation sigma side c.1) (classMass (K := K) (tick := tick) allocation sigma side c)
    (pairWidth ε c.1.val) (classMass_pos (K := K) (tick := tick) allocation sigma side c hc) hη
    (fiber_mass (K := K) (tick := tick) allocation m ε sigma side e w hw c)
    (parent_window (K := K) (tick := tick) allocation m ε sigma side w hp c.1) a
  rw [← q_eq_conditionalCenter (K := K) (tick := tick) allocation sigma side c hs] at hh
  exact hh.trans (width_le (K := K) (tick := tick) allocation hε sigma side c hc)

theorem q_eq_one_of_subsingleton (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) [Subsingleton (Symbol (K := K) (tick := tick) sigma c)]
    (hc : 0 < baseSize (base (K := K) (tick := tick) allocation sigma side) c)
    (a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c) : q (K := K) (tick := tick) allocation sigma side c a = 1 := by
  have hl (right : Bool) (u : JointPopulation.Shape)
      (hu : 0 < base (K := K) (tick := tick) allocation sigma side c u) :
      supportedHalfLaw allocation right c.1.val u (sigma side) (if right then a.2 else a.1) = 1 := by
    have hu' : 0 < activeCounts allocation 1 c.1.val u := by
      unfold base JointPopulationCompatibility.classCounts Counts groupCounts at hu
      split_ifs at hu with he
      · exact hu
      · omega
    rw [supportedHalfLaw_eq_of_counts_pos allocation 1 right c.1.val u hu']
    have ht := halfLawAt_normalized allocation 1 right c.1.val u hu' (sigma side)
    have he : (∑ b, halfLawAt right c.1.val u (sigma side) b) =
        halfLawAt right c.1.val u (sigma side) (if right then a.2 else a.1) :=
      Fintype.sum_subsingleton _ _
    exact he.symm.trans ht
  unfold q JointPairMixtureControls.pairMixture
  have hn : (∑ u, (base (K := K) (tick := tick) allocation sigma side c u : ℝ) *
      supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
      supportedHalfLaw allocation true c.1.val u (sigma side) a.2) =
      (baseSize (base (K := K) (tick := tick) allocation sigma side) c : ℝ) := by
    rw [baseSize, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : 0 < base (K := K) (tick := tick) allocation sigma side c u
    · have hleft : supportedHalfLaw allocation false c.1.val u (sigma side) a.1 = 1 := by
        simpa only [Bool.false_eq_true, ite_false, if_false] using hl false u hu
      have hright : supportedHalfLaw allocation true c.1.val u (sigma side) a.2 = 1 := by
        simpa only [ite_true, if_true] using hl true u hu
      rw [hleft, hright, mul_one, mul_one]
    · simp only [Nat.eq_zero_of_not_pos hu, Nat.cast_zero, zero_mul]
  rw [hn]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc))

theorem pairWindow_of_completeKeep (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w)
    (hp : completeKeep allocation m ε (sigma side) sigma w) :
    PairWindow (base (K := K) (tick := tick) allocation sigma side) (q (K := K) (tick := tick) allocation sigma side)
      (Positions (K := K) (tick := tick) allocation m sigma w) (pairCounts (K := K) (tick := tick) allocation m sigma w)
      (windowFactor (K := K) (tick := tick) allocation sigma * ε) := by
  intro c hc a
  by_cases hs : c.1.val.val.1.stage ≠ 2
  · exact sharing_window (K := K) (tick := tick) allocation m hε sigma side e w hw hp.2.2 c hs hc a
  · have hstage : c.1.val.val.1.stage = 2 := not_ne_iff.mp hs
    have : Subsingleton (Symbol (K := K) (tick := tick) sigma c) := by
      change Subsingleton c.1.val.val.1.Statistic
      cases hh : c.1.val.val.1 with
      | stageA h => simp [hh, Work.stage] at hstage
      | stageB h => simp [hh, Work.stage] at hstage
      | stageC h => dsimp [Work.Statistic]; infer_instance
    have hpc : pairCounts (K := K) (tick := tick) allocation m sigma w c a =
        Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) := by
      unfold pairCounts JointPopulationCompatibility.statisticCounts
      have hall : ∀ i, JointPopulationCompatibility.statisticWord
          (Counts (K := K) (tick := tick) allocation m sigma) (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
          (projectedStatistic (K := K) (tick := tick) sigma) (projectedStatistic (K := K) (tick := tick) sigma)
          (ownWord (K := K) (tick := tick) allocation m sigma w) w c i = a := fun _ => Subsingleton.elim _ _
      simp [wordPopulation, hall]
    have hn : (Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) : ℝ) ≠ 0 := by
      rw [positions_card (K := K) (tick := tick) allocation m ε sigma side e w hw c]
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hm hc))
    rw [hpc, div_self hn, q_eq_one_of_subsingleton (K := K) (tick := tick) allocation sigma side c hc a,
      sub_self, abs_zero]
    exact mul_nonneg (windowFactor_pos (K := K) (tick := tick) allocation sigma).le hε

theorem passing_pairWindow (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (ho : o ∈ (data (K := K) (tick := tick) allocation m ε sigma).orbits e)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (hv : v ∈ (data (K := K) (tick := tick) allocation m ε sigma).passing e o) :
    PairWindow (base (K := K) (tick := tick) allocation sigma v.1) (q (K := K) (tick := tick) allocation sigma v.1)
      (Positions (K := K) (tick := tick) allocation m sigma v.2) (pairCounts (K := K) (tick := tick) allocation m sigma v.2)
      (windowFactor (K := K) (tick := tick) allocation sigma * ε) := by
  have hpass := (mem_passing allocation m ε sigma e o v).mp hv
  exact pairWindow_of_completeKeep (K := K) (tick := tick) allocation hm hε sigma v.1 e v.2
    (AllFieldGroupAdmissible.full_admissible allocation m ε sigma e o ho v hpass.1) hpass.2

end MatrixMultiplication.AllFieldGroupPairWindows

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupCountRate
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

namespace MatrixMultiplication.AllFieldGroupDegreeLaws

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupNativeLaws
open JointPopulation JointCanonicalization MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem weighted_classLaw_eq_native (allocation : Allocation) (m : ℕ)
    (right : Bool) (side : Fin 3) (sigma : Placement)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hd : designated right side sigma h u) (a : Statistic h.val) :
    (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) * compatibilityLaw right side sigma h u a =
      (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) *
        supportedHalfLaw allocation right h.val u (sigma side) a := by
  by_cases hp : 0 < Counts (K := K) (tick := tick) allocation m sigma h u
  · rw [compatibilityLaw_eq allocation m sigma right side h u hp hd,
      supportedHalfLaw_eq_of_counts_pos allocation m right h.val u hp (sigma side)]
    rfl
  · have hz : Counts (K := K) (tick := tick) allocation m sigma h u = 0 := Nat.eq_zero_of_not_pos hp
    simp only [hz, Nat.cast_zero, zero_mul]

theorem compatible_iff_native (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) :
    JointPopulationCompatibility.Compatible (Counts (K := K) (tick := tick) allocation m sigma)
      (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
      (projectedStatistic sigma) (projectedStatistic sigma)
      (classDesignated false side sigma) (classDesignated true side sigma)
      (classLaw false side sigma) (classLaw true side sigma) χ (sigma side) e w ↔
    JointPopulationCompatibility.Compatible (Counts (K := K) (tick := tick) allocation m sigma)
      (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
      (projectedStatistic sigma) (projectedStatistic sigma)
      (classDesignated false side sigma) (classDesignated true side sigma)
      (nativeLaw allocation false side sigma) (nativeLaw allocation true side sigma)
      χ (sigma side) e w := by
  constructor <;> rintro ⟨hL, hR⟩ <;> constructor
  · intro h u hd a
    have hh := hL h u hd a
    change |_ - (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) *
      supportedHalfLaw allocation false h.val u (sigma side) a| ≤ _
    rw [← weighted_classLaw_eq_native allocation m false side sigma h u hd a]
    exact hh
  · intro h u hd a
    have hh := hR h u hd a
    change |_ - (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) *
      supportedHalfLaw allocation true h.val u (sigma side) a| ≤ _
    rw [← weighted_classLaw_eq_native allocation m true side sigma h u hd a]
    exact hh
  · intro h u hd a
    have hh := hL h u hd a
    change |_ - (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) *
      compatibilityLaw false side sigma h u a| ≤ _
    rw [weighted_classLaw_eq_native allocation m false side sigma h u hd a]
    exact hh
  · intro h u hd a
    have hh := hR h u hd a
    change |_ - (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) *
      compatibilityLaw true side sigma h u a| ≤ _
    rw [weighted_classLaw_eq_native allocation m true side sigma h u hd a]
    exact hh

theorem conditionalCount_eq_native (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) :
    conditionalCount allocation m χ sigma side w = nativeCount allocation m χ sigma side w := by
  unfold conditionalCount nativeCount JointPopulationCompatibility.compatibleTargetCount
  exact Fintype.card_congr (Equiv.subtypeEquivRight
    (fun e : JointPopulationCompatibility.FixedSideTargets
      (Counts (K := K) (tick := tick) allocation m sigma) (sigma side)
      (ownWord allocation m sigma w) =>
        compatible_iff_native allocation m χ sigma side e.val w))

theorem competitors_card_le_nativeCount (allocation : Allocation) (m : ℕ)
    {ε χ : ℝ} (hε : 0 ≤ ε) (hχ : ε ≤ χ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma) :
    (competitors allocation m ε sigma e o v).card ≤ nativeCount allocation m χ sigma v.1 v.2 := by
  rw [← conditionalCount_eq_native]
  exact competitors_card_le_conditionalCount allocation m hε hχ sigma e o v

theorem competitors_subset_eligibility_of_first (allocation : Allocation) (m : ℕ)
    (width : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma) (hv : v.1 = 0) :
    competitors allocation m width sigma e o v ⊆
      (data allocation m width sigma).eligibilityCompetitors e := by
  intro t ht
  apply ((data allocation m width sigma).mem_eligibilityCompetitors e t).2
  refine ⟨competitor_mem allocation m width sigma e o v t ht,
    (Finset.mem_filter.mp ht).2.1, ?_⟩
  have hh := (Finset.mem_filter.mp ht).2.2.1
  simp only [hv, tripleSide, Matrix.cons_val_zero] at hh
  exact hh

end MatrixMultiplication.AllFieldGroupDegreeLaws

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupCountRate

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupDegreeLaws
open AllFieldGroupNativeLaws AllFieldGroupPairWindows
open JointCompatibilityControls JointCompatibilityScaling JointCompatibilityRateLimit
open JointPopulationCompatibility JointTypeCounts MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem exists_threshold_eventually_competitors_le (allocation : Allocation)
    (sigma : Placement) (side : Fin 3) {δ widthMax : ℝ}
    (hδ : 0 < δ) (hwidthMax : 0 < widthMax) :
    ∃ threshold : ℝ, 0 < threshold ∧ threshold ≤ widthMax ∧
      ∀ width : ℝ, 0 < width → width ≤ threshold →
        ∀ᶠ m : ℕ in atTop,
          ∀ (e : Targets (K := K) (tick := tick) allocation m sigma)
            (o : Orbit (K := K) (tick := tick) allocation m sigma), o ∈ (data allocation m width sigma).orbits e →
            ∀ w : Raw (K := K) (tick := tick) allocation m sigma,
              (side, w) ∈ (data allocation m width sigma).passing e o →
              ((competitors allocation m width sigma e o (side, w)).card : ℝ) ≤
                Real.exp ((m : ℝ) *
                  (nativeCompatibilityRate (K := K) (tick := tick) allocation sigma side + δ)) := by
  obtain ⟨χ, η, hχ, hχMax, hη, _, hbound⟩ :=
    exists_widths_eventually_nativeCount_le (K := K) (tick := tick)
      allocation sigma side (ηMax := 1) hδ hwidthMax zero_lt_one
  let threshold := min χ (η / windowFactor (K := K) (tick := tick) allocation sigma)
  have hf := windowFactor_pos (K := K) (tick := tick) allocation sigma
  have ht : 0 < threshold := lt_min hχ (div_pos hη hf)
  refine ⟨threshold, ht, (min_le_left _ _).trans hχMax, ?_⟩
  intro width hw hwt
  have hwχ : width ≤ χ := hwt.trans (min_le_left _ _)
  have hww : windowFactor (K := K) (tick := tick) allocation sigma * width ≤ η := by
    have hh := (le_div_iff₀ hf).mp (hwt.trans (min_le_right _ _))
    simpa only [mul_comm] using hh
  filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)] with m hm hmpos
  intro e o ho w hpass
  have ha := AllFieldGroupAdmissible.full_admissible allocation m width sigma
    e o ho (side, w) ((data allocation m width sigma).passing_subset e o ho hpass)
  have hp := passing_pairWindow allocation hmpos hw.le sigma e o ho (side, w) hpass
  have hpair : PairWindow (base allocation sigma side) (q allocation sigma side)
      (Positions (K := K) (tick := tick) allocation m sigma w) (pairCounts allocation m sigma w) η :=
    fun c hc a => (hp c hc a).trans hww
  have hc := hm e w (fun h j => (ha.1.1 h j).symm) hpair
  exact (Nat.cast_le.mpr (competitors_card_le_nativeCount allocation m hw.le hwχ sigma
    e o (side, w))).trans hc

end MatrixMultiplication.AllFieldGroupCountRate

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupNativeDegreeBound
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

namespace MatrixMultiplication.AllFieldGroupNativeDegreeBound

open AllFieldHistory AllFieldActiveLaws AllFieldActiveCapacity
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupDegreeLaws
open AllFieldGroupCountRate AllFieldGroupPairWindows AllFieldGroupPairEntropy
open AllFieldGroupProjectedEntropy JointCompatibilityRateLimit
open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem orderNativeDegree_le_max (allocation : Allocation) (sigma : Placement) (side : Fin 3) :
    orderNativeDegree (K := K) (tick := tick) allocation sigma side ≤
      maxNativeDegree (K := K) (tick := tick) allocation sigma := by
  fin_cases side
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem exists_threshold_eventually_counts_le_oai (allocation : Allocation) (sigma : Placement)
    {δ widthMax : ℝ} (hδ : 0 < δ) (hwidthMax : 0 < widthMax) :
    ∃ threshold : ℝ, 0 < threshold ∧ threshold ≤ widthMax ∧
      ∀ width : ℝ, 0 < width → width ≤ threshold →
        ∀ᶠ m : ℕ in atTop,
          (∀ e : Targets (K := K) (tick := tick) allocation m sigma,
            (((data allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤
              Real.exp ((m : ℝ) * (maxNativeDegree (K := K) (tick := tick) allocation sigma + δ))) ∧
          (∀ (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma),
            o ∈ (data allocation m width sigma).orbits e →
            ∀ v : Variable (K := K) (tick := tick) allocation m sigma,
              v ∈ (data allocation m width sigma).passing e o →
              (((data allocation m width sigma).competitors e o v).card : ℝ) ≤
                Real.exp ((m : ℝ) * (maxNativeDegree (K := K) (tick := tick) allocation sigma + δ))) := by
  obtain ⟨t₁, ht₁, ht₁Max, h₁⟩ :=
    exists_threshold_eventually_competitors_le (K := K) (tick := tick)
      allocation sigma 1 hδ hwidthMax
  obtain ⟨t₂, ht₂, _, h₂⟩ :=
    exists_threshold_eventually_competitors_le (K := K) (tick := tick)
      allocation sigma 2 hδ hwidthMax
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, (min_le_left _ _).trans ht₁Max, ?_⟩
  intro width hw hwt
  filter_upwards [eventually_eligibility_card_le (K := K) (tick := tick)
    allocation sigma width hδ,
    h₁ width hw (hwt.trans (min_le_left _ _)),
    h₂ width hw (hwt.trans (min_le_right _ _))] with m hm₀ hm₁ hm₂
  have hm (side : Fin 3) :
      Real.exp ((m : ℝ) * (orderNativeDegree (K := K) (tick := tick) allocation sigma side + δ)) ≤
        Real.exp ((m : ℝ) * (maxNativeDegree (K := K) (tick := tick) allocation sigma + δ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (add_le_add (orderNativeDegree_le_max (K := K) (tick := tick) allocation sigma side) le_rfl) (Nat.cast_nonneg m))
  refine ⟨fun e => (hm₀ e).trans (hm 0), ?_⟩
  intro e o ho v hv
  rcases v with ⟨side, w⟩
  fin_cases side
  · exact (Nat.cast_le.mpr (Finset.card_le_card
      (competitors_subset_eligibility_of_first allocation m width sigma e o (0, w) rfl))).trans
        ((hm₀ e).trans (hm 0))
  · have hh := hm₁ e o ho w hv
    rw [nativeCompatibilityRate_eq (K := K) (tick := tick) allocation sigma 1 (by decide)] at hh
    exact hh.trans (hm 1)
  · have hh := hm₂ e o ho w hv
    rw [nativeCompatibilityRate_eq (K := K) (tick := tick) allocation sigma 2 (by decide)] at hh
    exact hh.trans (hm 2)

end MatrixMultiplication.AllFieldGroupNativeDegreeBound

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le_oai
