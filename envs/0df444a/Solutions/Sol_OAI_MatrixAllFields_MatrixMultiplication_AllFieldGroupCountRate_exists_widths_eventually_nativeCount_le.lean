-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCountRate.exists_widths_eventually_nativeCount_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:26:20.259575+00:00
-- url     : https://prove2.me/submissions/8cc4849d-7fc6-4b71-8dec-b53f4fdb9514

import Mathlib
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_JointCompatibilityCountProducer_exists_widths_eventually_count_le

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryChildLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
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

theorem leftChildLaw_nonnegative {K tick : ℕ} (side : Fin 3)
    (c : Active K tick × JointPopulation.Shape) (a : ActiveStatistic c.1) :
    0 ≤ leftChildLaw side c a := by
  change (0 : ℝ) ≤ (placedChildLawRat c.1.val c.2 side false a : ℝ)
  exact_mod_cast placedChildLawRat_nonnegative c.1.val c.2 side false a

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

theorem leftLaw_nonnegative {K tick : ℕ} (h : Active K tick) (u : JointPopulation.Shape)
    (side : Fin 3) (a : Statistic h) : 0 ≤ leftLaw h u side a :=
  leftChildLaw_nonnegative side (h, u) a

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
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.initialExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
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

theorem jointCount_le_population {P U Z A : Type*}
    [Fintype P] [Fintype U] [DecidableEq U] [DecidableEq A]
    (w : P → U) (z : P → Z) (part : Z → A) (u : U) (a : A) :
    jointCount w z part u a ≤ wordPopulation w u := by
  exact Fintype.card_le_of_injective
    (fun i : {i : P // w i = u ∧ part (z i) = a} =>
      (⟨i.val, i.property.1⟩ : {i : P // w i = u}))
    (fun _ _ h => Subtype.ext
      (congrArg (fun j : {i : P // w i = u} => j.val) h))

omit [Fintype H] [DecidableEq H] in
theorem class_jointCount_eq {A : Type*} [Fintype A] [DecidableEq A]
    (s : Fin 3) (b : Position counts → Fin 17) (e : FixedSideTargets counts s b)
    (c : ClassKey (H := H)) (u : Shape) (hu : shapeSide s u = c.2)
    (f : Positions counts c.1 → A) (a : A) :
    jointCount ((candidateEquiv counts s b e) c).val
      (fun i => f i.val) id u a = shapeStatisticCount counts (A := A) e.val c.1 u f a := by
  let eFiber : {i : ClassPos counts b c //
      ((candidateEquiv counts s b e) c).val i = u ∧ f i.val = a} ≃
      {i : Class counts e.val c.1 u // f i.val = a} :=
    { toFun := fun i => ⟨⟨i.val.val, by
        simpa only [candidateEquiv_apply] using i.property.1⟩, i.property.2⟩
      invFun := fun i =>
        ⟨⟨i.val.val, by
          calc
            b ⟨c.1, i.val.val⟩ = shapeSide s ((e.val c.1).val i.val.val) :=
              (e.property c.1 i.val.val).symm
            _ = shapeSide s u := congrArg (shapeSide s) i.val.property
            _ = c.2 := hu⟩,
          by simpa only [candidateEquiv_apply] using i.val.property, i.property⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro i
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  unfold jointCount shapeStatisticCount wordPopulation
  exact Fintype.card_congr eFiber

omit [Fintype H] [DecidableEq H] in
theorem class_jointCount_zero {A : Type*} [DecidableEq A]
    (s : Fin 3) (b : Position counts → Fin 17) (e : FixedSideTargets counts s b)
    (c : ClassKey (H := H)) (u : Shape) (hu : shapeSide s u ≠ c.2)
    (f : ClassPos counts b c → A) (a : A) :
    jointCount ((candidateEquiv counts s b e) c).val f id u a = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc
    jointCount ((candidateEquiv counts s b e) c).val f id u a ≤
        wordPopulation ((candidateEquiv counts s b e) c).val u :=
      jointCount_le_population _ _ _ _ _
    _ = classCounts counts s c u := ((candidateEquiv counts s b e) c).property u
    _ = 0 := ite_eq_right hu

omit [Fintype H] [DecidableEq H] in
theorem side_compatibility_iff_class_counts
    (A : ClassKey (H := H) → Type*)
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (s : Fin 3) (b : Position counts → Fin 17) (e : FixedSideTargets counts s b)
    (f : ∀ h k, Positions counts h → A (h, k))
    (designated : ClassKey (H := H) → Shape → Prop)
    (law : ∀ c, Shape → A c → ℝ) (χ : ℝ) :
    (∀ h u, designated (h, shapeSide s u) u → ∀ a : A (h, shapeSide s u),
      |(shapeStatisticCount counts (A := A (h, shapeSide s u))
          e.val h u (f h (shapeSide s u)) a : ℝ) -
        (counts h u : ℝ) * law (h, shapeSide s u) u a| ≤ (counts h u : ℝ) * χ) ↔
    (∀ c u, designated c u → ∀ a : A c,
      |(jointCount ((candidateEquiv counts s b e) c).val
          (fun i => f c.1 c.2 i.val) id u a : ℝ) -
        (classCounts counts s c u : ℝ) * law c u a| ≤
          (classCounts counts s c u : ℝ) * χ) := by
  constructor
  · intro h c u hd a
    by_cases hu : shapeSide s u = c.2
    · rw [class_jointCount_eq counts s b e c u hu]
      rcases c with ⟨h₀, k⟩
      dsimp at hu
      subst k
      simpa only [classCounts, ite_eq_left rfl, ite_true, if_true] using h h₀ u hd a
    · rw [class_jointCount_zero counts s b e c u hu]
      simp only [classCounts, ite_eq_right hu, Nat.cast_zero, zero_mul, sub_zero, abs_zero, le_refl]
  · intro h h₀ u hd a
    have hh := h (h₀, shapeSide s u) u hd a
    rw [class_jointCount_eq counts s b e (h₀, shapeSide s u) u rfl] at hh
    simpa only [classCounts, ite_eq_left rfl, ite_true, if_true] using hh

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
theorem compatible_iff_kernel (s : Fin 3) (b : Position counts → Fin 17)
    (e : FixedSideTargets counts s b) (w : JointCanonicalization.RawPairs counts L R) :
    Compatible counts L R SL SR leftStatistic rightStatistic designatedLeft designatedRight
      leftLaw rightLaw χ s e.val w ↔
    DesignatedCompatibility (ClassPos counts b) (fun _ => Shape) (fun c => SL c × SR c)
      SL SR (classCounts counts s)
      (statisticCounts counts L R SL SR leftStatistic rightStatistic b w)
      (fun _ p => p.1) (fun _ p => p.2) designatedLeft designatedRight leftLaw rightLaw χ
      (candidateEquiv counts s b e)
      (statisticElement counts L R SL SR leftStatistic rightStatistic b w) := by
  exact and_congr
    (side_compatibility_iff_class_counts counts SL s b e
      (fun h k i => leftStatistic (h, k) (w h i).1) designatedLeft leftLaw χ)
    (side_compatibility_iff_class_counts counts SR s b e
      (fun h k i => rightStatistic (h, k) (w h i).2) designatedRight rightLaw χ)

theorem compatibleTargetCount_eq_kernel (s : Fin 3) (b : Position counts → Fin 17)
    (w : JointCanonicalization.RawPairs counts L R) :
    compatibleTargetCount counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ s b w =
    compatibleCandidateCount (ClassPos counts b) (fun _ => Shape) (fun c => SL c × SR c)
      SL SR (classCounts counts s)
      (statisticCounts counts L R SL SR leftStatistic rightStatistic b w)
      (fun _ p => p.1) (fun _ p => p.2) designatedLeft designatedRight leftLaw rightLaw χ
      (statisticElement counts L R SL SR leftStatistic rightStatistic b w) := by
  exact Fintype.card_congr ((candidateEquiv counts s b).subtypeEquiv
    (fun e => compatible_iff_kernel counts L R SL SR leftStatistic rightStatistic
      designatedLeft designatedRight leftLaw rightLaw χ s b e w))

end Statistics

end MatrixMultiplication.JointPopulationCompatibility






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false
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

theorem halfLawAt_nonnegative {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) (a : Statistic h) :
    0 ≤ halfLawAt right h u side a := by
  cases right
  · exact leftLaw_nonnegative h u side a
  · exact rightLaw_nonnegative h u side a

theorem halfLawAt_normalized {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (side : Fin 3) :
    ∑ a, halfLawAt right h u side a = 1 := by
  cases right
  · exact leftLaw_normalized allocation m h u hu side
  · exact rightLaw_normalized allocation m h u hu side

theorem halfLawAt_le_one_of_counts_pos {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (side : Fin 3) (a : Statistic h) :
    halfLawAt right h u side a ≤ 1 := by
  have hle := Finset.single_le_sum
    (fun b (_ : b ∈ Finset.univ) => halfLawAt_nonnegative right h u side b)
    (Finset.mem_univ a)
  rw [halfLawAt_normalized allocation m right h u hu side] at hle
  exact hle

theorem supportedHalfLaw_bounds {K tick : ℕ} (allocation : Allocation) (right : Bool)
    (h : Active K tick) (u : JointPopulation.Shape) (side : Fin 3) (a : Statistic h) :
    0 ≤ supportedHalfLaw allocation right h u side a ∧
      supportedHalfLaw allocation right h u side a ≤ 1 := by
  unfold supportedHalfLaw
  split_ifs with hu
  · exact ⟨halfLawAt_nonnegative right h u side a,
      halfLawAt_le_one_of_counts_pos allocation 1 right h u hu side a⟩
  · norm_num

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
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPairMixtureControls

open JointCompatibilityControls JointCompatibilityScaling
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A B : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
  [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (B c)] in
theorem sum_first_fiber (c : C) (q : A c × B c → ℝ) (a : A c) :
    (∑ ab : {ab : A c × B c // ab.1 = a}, q ab.val) = ∑ b, q (a, b) := by
  let e : B c ≃ {ab : A c × B c // ab.1 = a} :=
    { toFun := fun b => ⟨(a, b), rfl⟩
      invFun := fun ab => ab.val.2
      left_inv := fun _ => rfl
      right_inv := fun ab => by apply Subtype.ext; exact Prod.ext ab.property.symm rfl }
  exact (e.sum_comp (fun ab => q ab.val)).symm

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (A c)] in
theorem sum_second_fiber (c : C) (q : A c × B c → ℝ) (b : B c) :
    (∑ ab : {ab : A c × B c // ab.2 = b}, q ab.val) = ∑ a, q (a, b) := by
  let e : A c ≃ {ab : A c × B c // ab.2 = b} :=
    { toFun := fun a => ⟨(a, b), rfl⟩
      invFun := fun ab => ab.val.1
      left_inv := fun _ => rfl
      right_inv := fun ab => by apply Subtype.ext; exact Prod.ext rfl ab.property.symm }
  exact (e.sum_comp (fun ab => q ab.val)).symm

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)] in
theorem base_eq_zero_of_size_eq_zero (base : ∀ c, Shape c → ℕ)
    (c : C) (hz : baseSize base c = 0) (u : Shape c) : base c u = 0 :=
  Nat.eq_zero_of_le_zero ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ u)).trans_eq hz)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem totalCenterCount_eq_zero_of_size_eq_zero (base : ∀ c, Shape c → ℕ)
    (law : ∀ c, Shape c → A c → ℝ) (c : C) (hz : baseSize base c = 0) (a : A c) :
    totalCenterCount base law c a = 0 := by
  simp only [totalCenterCount, base_eq_zero_of_size_eq_zero base c hz,
    Nat.cast_zero, zero_mul, Finset.sum_const_zero]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, DecidableEq (B c)] in
theorem pairMixture_left_balance (base : ∀ c, Shape c → ℕ)
    (left : ∀ c, Shape c → A c → ℝ) (right : ∀ c, Shape c → B c → ℝ)
    (hnormalized : ∀ c u, 0 < base c u → ∑ b, right c u b = 1)
    (c : C) (a : A c) :
    (baseSize base c : ℝ) *
      (∑ ab : {ab : A c × B c // ab.1 = a}, pairMixture base left right c ab.val) =
      totalCenterCount base left c a := by
  rw [sum_first_fiber]
  simp only [pairMixture, ← Finset.sum_div]
  have hnum : (∑ b : B c, ∑ u : Shape c,
      (base c u : ℝ) * left c u a * right c u b) = totalCenterCount base left c a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : base c u = 0
    · simp [hu]
    · rw [← Finset.mul_sum, hnormalized c u (Nat.pos_of_ne_zero hu), mul_one]
  rw [hnum]
  by_cases hz : baseSize base c = 0
  · rw [totalCenterCount_eq_zero_of_size_eq_zero base left c hz a]
    simp
  · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, DecidableEq (A c)] in
theorem pairMixture_right_balance (base : ∀ c, Shape c → ℕ)
    (left : ∀ c, Shape c → A c → ℝ) (right : ∀ c, Shape c → B c → ℝ)
    (hnormalized : ∀ c u, 0 < base c u → ∑ a, left c u a = 1)
    (c : C) (b : B c) :
    (baseSize base c : ℝ) *
      (∑ ab : {ab : A c × B c // ab.2 = b}, pairMixture base left right c ab.val) =
      totalCenterCount base right c b := by
  rw [sum_second_fiber]
  simp only [pairMixture, ← Finset.sum_div]
  have hnum : (∑ a : A c, ∑ u : Shape c,
      (base c u : ℝ) * left c u a * right c u b) = totalCenterCount base right c b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : base c u = 0
    · simp [hu]
    · rw [← Finset.sum_mul, ← Finset.mul_sum,
        hnormalized c u (Nat.pos_of_ne_zero hu), mul_one]
  rw [hnum]
  by_cases hz : baseSize base c = 0
  · rw [totalCenterCount_eq_zero_of_size_eq_zero base right c hz b]
    simp
  · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz)

end MatrixMultiplication.JointPairMixtureControls

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupCountRate
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
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

theorem nativeLaw_bounds (allocation : Allocation) (right : Bool) (side : Fin 3)
    (sigma : Placement) (c : Class (K := K) (tick := tick) sigma)
    (u : JointPopulation.Shape) (a : Symbol (K := K) (tick := tick) sigma c) :
    0 ≤ nativeLaw allocation right side sigma c u a ∧
      nativeLaw allocation right side sigma c u a ≤ 1 :=
  supportedHalfLaw_bounds allocation right c.1.val u (sigma side) a

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

theorem base_positive_counts (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) (u : JointPopulation.Shape)
    (hu : 0 < base allocation sigma side c u) :
    0 < Counts (K := K) (tick := tick) allocation 1 sigma c.1 u := by
  unfold base classCounts at hu
  split_ifs at hu with hs
  · exact hu
  · exact (Nat.lt_irrefl 0 hu).elim

theorem nativeLaw_normalized (allocation : Allocation) (right : Bool)
    (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) (u : JointPopulation.Shape)
    (hu : 0 < base allocation sigma side c u) :
    ∑ a, nativeLaw allocation right side sigma c u a = 1 := by
  have hp := base_positive_counts allocation sigma side c u hu
  simp only [nativeLaw,
    supportedHalfLaw_eq_of_counts_pos allocation 1 right c.1.val u hp (sigma side)]
  exact halfLawAt_normalized allocation 1 right c.1.val u hp (sigma side)

theorem classCounts_dilation (allocation : Allocation) (m : ℕ)
    (sigma : Placement) (side : Fin 3) :
    classCounts (Counts (K := K) (tick := tick) allocation m sigma) (sigma side) =
      fun c u => m * base allocation sigma side c u := by
  funext c u
  change (if JointPopulation.shapeSide (sigma side) u = c.2 then
    activeCounts allocation m c.1.val u else 0) =
    m * (if JointPopulation.shapeSide (sigma side) u = c.2 then
      activeCounts allocation 1 c.1.val u else 0)
  rw [activeCounts_dilation]
  split_ifs <;> simp

theorem exists_widths_eventually_nativeCount_le_oai (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) {δ χMax ηMax : ℝ}
    (hδ : 0 < δ) (hχMax : 0 < χMax) (hηMax : 0 < ηMax) :
    ∃ χ η : ℝ, 0 < χ ∧ χ ≤ χMax ∧ 0 < η ∧ η ≤ ηMax ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ (e : Targets (K := K) (tick := tick) allocation m sigma)
          (w : Raw (K := K) (tick := tick) allocation m sigma),
          (∀ h j, JointPopulation.shapeSide (sigma side) ((e h).val j) =
            ownWord allocation m sigma w ⟨h, j⟩) →
          PairWindow (base allocation sigma side) (q allocation sigma side)
            (Positions (K := K) (tick := tick) allocation m sigma w) (pairCounts allocation m sigma w) η →
          (nativeCount allocation m χ sigma side w : ℝ) ≤
            Real.exp ((m : ℝ) *
              (nativeCompatibilityRate (K := K) (tick := tick) allocation sigma side + δ)) := by
  have hparts : ∀ c : Class (K := K) (tick := tick) sigma,
      Function.Injective (fun a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c => (a.1, a.2)) :=
    fun _ => fun _ _ h => h
  have hleft : ∀ (c : Class (K := K) (tick := tick) sigma) (a : Symbol (K := K) (tick := tick) sigma c),
      (baseSize (base allocation sigma side) c : ℝ) *
        (∑ b : {b : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c // b.1 = a}, q allocation sigma side c b.val) =
          totalCenterCount (base allocation sigma side) (nativeLaw allocation false side sigma) c a := by
    intro c a
    exact JointPairMixtureControls.pairMixture_left_balance
      (base allocation sigma side) (nativeLaw allocation false side sigma)
      (nativeLaw allocation true side sigma)
      (nativeLaw_normalized allocation true sigma side) c a
  have hright : ∀ (c : Class (K := K) (tick := tick) sigma) (a : Symbol (K := K) (tick := tick) sigma c),
      (baseSize (base allocation sigma side) c : ℝ) *
        (∑ b : {b : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c // b.2 = a}, q allocation sigma side c b.val) =
          totalCenterCount (base allocation sigma side) (nativeLaw allocation true side sigma) c a := by
    intro c a
    exact JointPairMixtureControls.pairMixture_right_balance
      (base allocation sigma side) (nativeLaw allocation false side sigma)
      (nativeLaw allocation true side sigma)
      (nativeLaw_normalized allocation false sigma side) c a
  obtain ⟨χ, η, hχ, hχMax', hη, hηMax', hbound⟩ :=
    JointCompatibilityCountProducer.exists_widths_eventually_count_le
      (base allocation sigma side) (q allocation sigma side)
      (fun _ p => p.1) (fun _ p => p.2)
      (classDesignated false side sigma) (classDesignated true side sigma)
      (nativeLaw allocation false side sigma) (nativeLaw allocation true side sigma)
      hparts
      (fun c u a => (nativeLaw_bounds allocation false side sigma c u a).1)
      (fun c u a => (nativeLaw_bounds allocation false side sigma c u a).2)
      (fun c u a => (nativeLaw_bounds allocation true side sigma c u a).1)
      (fun c u a => (nativeLaw_bounds allocation true side sigma c u a).2)
      hleft hright hδ hχMax hηMax
  refine ⟨χ, η, hχ, hχMax', hη, hηMax', ?_⟩
  filter_upwards [hbound] with m hm
  intro e w hown hwindow
  rw [← classCounts_dilation allocation m sigma side] at hm
  let target : FixedSideTargets (Counts (K := K) (tick := tick) allocation m sigma) (sigma side)
      (ownWord allocation m sigma w) := ⟨e, hown⟩
  have hb := (hm (Positions (K := K) (tick := tick) allocation m sigma w) (pairCounts allocation m sigma w)
    (candidateEquiv (Counts (K := K) (tick := tick) allocation m sigma) (sigma side)
      (ownWord allocation m sigma w) target)
    (statisticElement (Counts (K := K) (tick := tick) allocation m sigma) (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma)
      (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (projectedStatistic sigma) (projectedStatistic sigma)
      (ownWord allocation m sigma w) w) hwindow).1
  rw [nativeCount, compatibleTargetCount_eq_kernel]
  exact hb

end MatrixMultiplication.AllFieldGroupCountRate

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCountRate.exists_widths_eventually_nativeCount_le_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCountRate.exists_widths_eventually_nativeCount_le_oai
