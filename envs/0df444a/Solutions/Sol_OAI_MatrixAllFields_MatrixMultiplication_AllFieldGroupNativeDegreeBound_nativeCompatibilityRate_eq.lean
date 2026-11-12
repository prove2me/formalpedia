-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.nativeCompatibilityRate_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:24:36.387921+00:00
-- url     : https://prove2.me/submissions/bc90deff-298a-4f9c-a1e5-82638f71e1fe

import Mathlib
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupPairEntropy_history_pair_entropy_of_sharing
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupProjectedEntropy_branchConditionalCost_eq_observed
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupProjectedEntropy_class_groupedEntropy_eq_masked

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

theorem entropyTerm_mul (p q : ℝ) :
    entropyTerm (p * q) = q * entropyTerm p + p * entropyTerm q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [entropyTerm, Real.log_mul hp hq]
  unfold entropyTerm
  ring

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mass_le_map_mass (p : FiniteLaw A) (f : A → B) (a : A) :
    p.mass a ≤ (p.map f).mass (f a) := by
  classical
  rw [map_mass]
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset A))
    (f := fun a' => if f a' = f a then p.mass a' else 0)
    (fun a' _ => by
      split_ifs
      · exact p.nonneg a'
      · exact le_rfl)
    (Finset.mem_univ a)
  simpa using h

theorem map_mass_mul_conditional [DecidableEq B]
    (p : FiniteLaw A) (f : A → B) (b : B) (a : A) :
    (p.map f).mass b * (p.conditional f b).mass a =
      if f a = b then p.mass a else 0 := by
  classical
  by_cases hzero : (p.map f).mass b = 0
  · have ha : f a = b → p.mass a = 0 := by
      intro hab
      have hle := p.mass_le_map_mass f a
      rw [hab, hzero] at hle
      exact le_antisymm hle (p.nonneg a)
    rw [hzero, zero_mul]
    by_cases hab : f a = b
    · rw [ite_eq_left hab, ha hab]
    · rw [ite_eq_right hab]
  · simp only [conditional, hzero, ↓reduceDIte]
    by_cases hab : f a = b
    · simpa only [hab, ite_true, if_true] using (mul_div_cancel₀ (p.mass a) hzero)
    · simp only [hab, ite_false, if_false, zero_div, mul_zero]

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

end OAI
end

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
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCompatibilityIncidence
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

namespace MatrixMultiplication.JointCompatibilityIncidence

open MatrixMultiplication.Foundation JointTypeCounts
open scoped BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] fixedWordsMulAction

section Groups

variable {P U Z A : Type*} [Fintype P] [DecidableEq P]
  [Fintype U] [DecidableEq U] [Fintype A] [DecidableEq A]

omit [Fintype U] [DecidableEq U] in
theorem designatedGroup_eq_some (d : U → Prop) (u v : U) :
    designatedGroup d v = some u ↔ d u ∧ v = u := by
  constructor
  · intro h
    by_cases hv : d v
    · have he : v = u := Option.some.inj (by simpa [designatedGroup, hv] using h)
      exact ⟨he ▸ hv, he⟩
    · simp [designatedGroup, hv] at h
  · rintro ⟨hu, rfl⟩
    simp [designatedGroup, hu]

omit [Fintype U] [DecidableEq U] in
theorem designatedGroup_eq_none (d : U → Prop) (v : U) :
    designatedGroup d v = none ↔ ¬d v := by
  simp [designatedGroup]

end Groups

end MatrixMultiplication.JointCompatibilityIncidence

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

namespace MatrixMultiplication.JointPopulationRates

open MatrixMultiplication.Foundation Filter JointPopulation
open scoped BigOperators Topology

theorem finiteEntropy_scalar {A : Type*} [Fintype A]
    (p : A → ℝ) (mass : ℝ) (hp : ∑ a, p a = 1) :
    finiteEntropy (fun a => mass * p a) = entropyTerm mass + mass * finiteEntropy p := by
  simp only [finiteEntropy, entropyTerm_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hp, one_mul]

theorem weighted_empirical_entropy_eq {A : Type*} [Fintype A]
    (counts : A → ℕ) (scale : ℝ) :
    ((∑ a, counts a : ℕ) / scale) *
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
        finiteEntropy (fun a => (counts a : ℝ) / scale) -
          entropyTerm ((∑ a, counts a : ℕ) / scale) := by
  by_cases hzero : (∑ a, counts a) = 0
  · have hc : ∀ a, counts a = 0 := by
      intro a
      have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      rw [hzero] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp [hc, finiteEntropy]
  have hD : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hzero
  have hsum : (∑ a, (counts a : ℝ) / (∑ a, counts a : ℕ)) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, div_self hD]
  have hfac (a : A) : (counts a : ℝ) / scale =
      ((∑ a, counts a : ℕ) / scale) * ((counts a : ℝ) / (∑ a, counts a : ℕ)) := by
    rw [div_mul_div_comm,
      mul_comm ((∑ a, counts a : ℕ) : ℝ) (counts a : ℝ), mul_div_mul_right _ _ hD]
  have h := finiteEntropy_scalar
    (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))
    ((∑ a, counts a : ℕ) / scale) hsum
  simp_rw [← hfac] at h
  linarith

end MatrixMultiplication.JointPopulationRates






namespace MatrixMultiplication.AllFieldActiveLaws

open AllFieldParameters AllFieldHistory MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

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

theorem population_cast_real {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : History K) :
    (population allocation dilation h : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) * (amount allocation h : ℝ) := by
  exact_mod_cast population_cast allocation dilation h

end MatrixMultiplication.AllFieldActiveLaws






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






namespace MatrixMultiplication.JointConditionalCountEntropy

open MatrixMultiplication.Foundation JointPopulationRates
open scoped BigOperators

variable {U A : Type*} [Fintype U] [Fintype A]

attribute [local instance] Classical.propDecidable

theorem sum_masked_entropy (p : U → ℝ) (f : U → A) :
    (∑ a, finiteEntropy (fun u => if f u = a then p u else 0)) =
      finiteEntropy p := by
  classical
  have ht (a : A) (u : U) :
      entropyTerm (if f u = a then p u else 0) =
        if f u = a then entropyTerm (p u) else 0 := by
    by_cases h : f u = a <;> simp [h]
  simp only [finiteEntropy, ht]
  rw [Finset.sum_comm]
  simp

theorem sum_classCounts_entropy (n : U → ℕ) (f : U → A) (scale : ℝ) :
    (∑ a, finiteEntropy (fun u => (classCounts n f a u : ℝ) / scale)) =
      finiteEntropy (fun u => (n u : ℝ) / scale) := by
  classical
  have hm (a : A) :
      (fun u => (classCounts n f a u : ℝ) / scale) =
        (fun u => if f u = a then (n u : ℝ) / scale else 0) := by
    funext u
    by_cases h : f u = a <;> simp [classCounts, h]
  simp_rw [hm]
  exact sum_masked_entropy _ f

theorem sum_scaled_class_empirical_entropy (n : U → ℕ) (f : U → A)
    (scale : ℝ) :
    (∑ a, ((classSize n f a : ℝ) / scale) *
      finiteEntropy (fun u =>
        (classCounts n f a u : ℝ) / (classSize n f a : ℝ))) =
      finiteEntropy (fun u => (n u : ℝ) / scale) -
        finiteEntropy (fun a => (classSize n f a : ℝ) / scale) := by
  calc
    _ = ∑ a, (finiteEntropy (fun u => (classCounts n f a u : ℝ) / scale) -
        entropyTerm ((classSize n f a : ℝ) / scale)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact weighted_empirical_entropy_eq (classCounts n f a) scale
    _ = _ := by
      rw [Finset.sum_sub_distrib, sum_classCounts_entropy]
      rfl

theorem sum_classSize_mul_entropy_of_law (n : U → ℕ) (f : U → A)
    (p : FiniteLaw U) (scale : ℝ)
    (hn : ∀ u, (n u : ℝ) = scale * p.mass u) :
    (∑ a, (classSize n f a : ℝ) *
      finiteEntropy (fun u =>
        (classCounts n f a u : ℝ) / (classSize n f a : ℝ))) =
      scale * (finiteEntropy p.mass - finiteEntropy (p.map f).mass) := by
  classical
  have hclass (a : A) : (classSize n f a : ℝ) = scale * (p.map f).mass a := by
    rw [classSize, Nat.cast_sum, FiniteLaw.map_mass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : f u = a <;> simp [classCounts, h, hn]
  have h := sum_scaled_class_empirical_entropy n f 1
  simp only [div_one] at h
  rw [h]
  simp_rw [hn, hclass]
  rw [finiteEntropy_scalar p.mass scale p.total,
    finiteEntropy_scalar (p.map f).mass scale (p.map f).total]
  ring

end MatrixMultiplication.JointConditionalCountEntropy






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_GroupPairWindows
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

namespace MatrixMultiplication.AllFieldGroupPairWindows

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistorySupport
open AllFieldHistoryChildLaws AllFieldHistoryMasks AllFieldHistoryMaskLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupNativeLaws
open JointCompatibilityScaling JointCompatibilityRateLimit
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ} {sigma : Placement}

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

end MatrixMultiplication.AllFieldGroupPairWindows

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupPairEntropy
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

namespace MatrixMultiplication.AllFieldGroupPairEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldHistoryChildLaws AllFieldGroupOrbitData
open AllFieldGroupDegrees AllFieldGroupNativeLaws AllFieldGroupPairWindows
open JointCompatibilityScaling JointCompatibilityRateLimit JointPairClassWindows
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

theorem history_pair_entropy_of_ordinary (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (h : ActiveOrder K tick sigma) (hs : h.val.val.1.stage = 2) :
    (∑ k : Fin 17, (baseSize (base allocation sigma side) (h, k) : ℝ) *
      finiteEntropy (q allocation sigma side (h, k))) = 0 := by
  have : Subsingleton (Statistic h.val) := by
    change Subsingleton h.val.val.1.Statistic
    cases he : h.val.val.1 with
    | stageA a => simp [he, Work.stage] at hs
    | stageB a => simp [he, Work.stage] at hs
    | stageC a => dsimp [Work.Statistic]; infer_instance
  apply Finset.sum_eq_zero
  intro k _
  by_cases hz : baseSize (base allocation sigma side) (h, k) = 0
  · simp only [hz, Nat.cast_zero, zero_mul]
  · have hq : q allocation sigma side (h, k) = fun _ => 1 := by
      funext a
      exact q_eq_one_of_subsingleton allocation sigma side (h, k)
        (Nat.pos_of_ne_zero hz) a
    simp only [hq, finiteEntropy, entropyTerm, Real.log_one, mul_zero,
      Finset.sum_const_zero]

theorem pairReferenceEntropy_eq (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) :
    pairReferenceEntropy (base (K := K) (tick := tick) allocation sigma side)
      (q allocation sigma side) =
      ∑ h : ActiveOrder K tick sigma, (parentBase allocation h : ℝ) *
        (if h.val.val.1.stage ≠ 2 then
          finiteEntropy (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass -
            finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma side))
        else 0) := by
  unfold pairReferenceEntropy
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hs : h.val.val.1.stage ≠ 2
  · rw [ite_eq_left hs]
    exact history_pair_entropy_of_sharing allocation sigma side h hs
  · rw [ite_eq_right hs, mul_zero]
    exact history_pair_entropy_of_ordinary allocation sigma side h (not_not.mp hs)

theorem baseEntropy_eq (allocation : Allocation) (sigma : Placement) (side : Fin 3) :
    baseEntropy (base (K := K) (tick := tick) allocation sigma side) =
      ∑ h : ActiveOrder K tick sigma, (parentBase allocation h : ℝ) *
        (finiteEntropy (orderLaw h).mass -
          finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma side))) := by
  unfold baseEntropy
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  have hb (k : Fin 17) : base allocation sigma side (h, k) =
      JointConditionalCountEntropy.classCounts (Counts allocation 1 sigma h)
        (JointPopulation.shapeSide (sigma side)) k := by
    funext u
    by_cases hu : JointPopulation.shapeSide (sigma side) u = k
    · simp only [base, JointPopulationCompatibility.classCounts,
        JointConditionalCountEntropy.classCounts, hu, ite_true, if_true]
    · simp only [base, JointPopulationCompatibility.classCounts,
        JointConditionalCountEntropy.classCounts, hu, ite_false, if_false]
  have hs (k : Fin 17) : baseSize (base allocation sigma side) (h, k) =
      JointConditionalCountEntropy.classSize (Counts allocation 1 sigma h)
        (JointPopulation.shapeSide (sigma side)) k := by
    simp only [baseSize, JointConditionalCountEntropy.classSize, hb k]
  have hm : ((orderLaw h).map (JointPopulation.shapeSide (sigma side))).mass =
      JointPopulationRates.sideMass (orderLaw h).mass (sigma side) := by
    funext k
    rw [FiniteLaw.map_mass]
    rfl
  have he := JointConditionalCountEntropy.sum_classSize_mul_entropy_of_law
    (Counts allocation 1 sigma h) (JointPopulation.shapeSide (sigma side))
    (orderLaw h) (parentBase allocation h : ℝ)
    (fun u => jointCounts_cast allocation 1 h.val.val u)
  rw [hm] at he
  simpa only [hs, hb] using he

theorem baseEntropy_sub_pairReferenceEntropy (allocation : Allocation)
    (sigma : Placement) (side : Fin 3) :
    baseEntropy (base (K := K) (tick := tick) allocation sigma side) -
      pairReferenceEntropy (base (K := K) (tick := tick) allocation sigma side)
        (q allocation sigma side) =
      ∑ h : ActiveOrder K tick sigma, (parentBase allocation h : ℝ) *
        (finiteEntropy (orderLaw h).mass - observedEntropy h side) := by
  rw [baseEntropy_eq, pairReferenceEntropy_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h _
  unfold observedEntropy
  split_ifs <;> ring

end MatrixMultiplication.AllFieldGroupPairEntropy

end
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

namespace MatrixMultiplication.JointProjectedGroupEntropy

open MatrixMultiplication.Foundation JointCompatibilityIncidence
open JointCompatibilityScaling JointCompatibilityControls JointCompatibilityRateLimit
open JointGroupedEntropyPartition
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

section FiniteGroups

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

theorem groupMass_designated_some (p : U → ℝ) (d : U → Prop) (u : U) :
    groupMass p (designatedGroup d) (some u) = if d u then p u else 0 := by
  simp only [groupMass, designatedGroup_eq_some]
  by_cases hd : d u <;> simp [hd]

theorem weighted_groupLaw_designated_some (p : U → ℝ) (d : U → Prop)
    (law : U → A → ℝ) (u : U) :
    groupMass p (designatedGroup d) (some u) *
        finiteEntropy (groupLaw p (designatedGroup d) law (some u)) =
      (if d u then p u else 0) * finiteEntropy (law u) := by
  by_cases hd : d u
  · rw [groupMass_designated_some, ite_eq_left hd]
    by_cases hp : p u = 0
    · simp [hp]
    · have hl : groupLaw p (designatedGroup d) law (some u) = law u := by
        funext a
        simp [groupLaw, groupMass_designated_some, designatedGroup_eq_some, hd, hp]
      rw [hl]
  · rw [groupMass_designated_some, ite_eq_right hd]
    simp

end FiniteGroups

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

omit [Fintype C] [DecidableEq C] in
theorem baseGroupSize_eq_groupMass (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (g : Σ c, Option (Shape c)) :
    (baseGroupSize base d g : ℝ) =
      groupMass (fun u => (base g.1 u : ℝ)) (designatedGroup (d g.1)) g.2 := by
  calc
    (baseGroupSize base d g : ℝ) =
        ∑ u ∈ Finset.univ.filter (fun u => designatedGroup (d g.1) u = g.2),
          (base g.1 u : ℝ) := by
      rw [baseGroupSize, Nat.cast_sum]
      exact (Finset.sum_subtype
        (Finset.univ.filter (fun u => designatedGroup (d g.1) u = g.2))
        (by simp) (fun u => (base g.1 u : ℝ))).symm
    _ = ∑ u, if designatedGroup (d g.1) u = g.2 then (base g.1 u : ℝ) else 0 := by
      rw [Finset.sum_filter]
    _ = _ := by
      unfold groupMass
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : designatedGroup (d g.1) u = g.2 <;> simp only [hu, ite_true, if_true, ite_false, if_false]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem residualCenter_eq_groupLaw (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (law : ∀ c, Shape c → A c → ℝ) (c : C) :
    residualCenter base d law c =
      groupLaw (fun u => (base c u : ℝ)) (designatedGroup (d c)) (law c) none := by
  funext a
  simp only [residualCenter, residualBase, Nat.cast_sum, groupLaw, groupMass,
    designatedGroup_eq_none]
  congr 1
  · rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun u => ¬ d c u))
      (by simp) (fun u => (base c u : ℝ) * law c u a)).symm
  · rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun u => ¬ d c u))
      (by simp) (fun u => (base c u : ℝ))).symm

omit [DecidableEq C] [∀ c, DecidableEq (A c)] in
theorem projectedReferenceEntropy_eq_sum_counts_groupedEntropy
    (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) :
    projectedReferenceEntropy base d (groupCap base d law 0) =
      ∑ c, groupedEntropy (fun u => (base c u : ℝ))
        (designatedGroup (d c)) (law c) := by
  simp only [projectedReferenceEntropy, Fintype.sum_sigma, groupCap, add_zero,
    groupedEntropy]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro k _
  rw [baseGroupSize_eq_groupMass]
  cases k with
  | none =>
      change _ * finiteEntropy (residualCenter base d law c) = _
      rw [residualCenter_eq_groupLaw]
  | some u =>
      change _ * finiteEntropy (law c u) = _
      rw [weighted_groupLaw_designated_some, groupMass_designated_some]

end MatrixMultiplication.JointProjectedGroupEntropy

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
open AllFieldGroupBranchDesignation AllFieldNativeGroupedRates
open AllFieldScheduledYield AllFieldGroupPairEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

theorem maskedBranchMass_eq_conditional (h : ActiveOrder K tick sigma)
    (side : Fin 3) (k : Fin 17) :
    maskedBranchMass h side k = fun b =>
      ((branchLaw h.val.val.1).map
        (nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side))).mass k *
      ((branchLaw h.val.val.1).conditional
        (nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side)) k).mass b := by
  funext b
  exact ((branchLaw h.val.val.1).map_mass_mul_conditional
    (nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side)) k b).symm

theorem history_projected_entropy_eq (allocation : Allocation)
    (side : Fin 3) (hside : side ≠ 0) (h : ActiveOrder K tick sigma) :
    (∑ k : Fin 17,
      (groupedEntropy (fun u => (base allocation sigma side (h, k) u : ℝ))
        (designatedGroup (classDesignated false side sigma (h, k)))
        (nativeLaw allocation false side sigma (h, k)) +
      groupedEntropy (fun u => (base allocation sigma side (h, k) u : ℝ))
        (designatedGroup (classDesignated true side sigma (h, k)))
        (nativeLaw allocation true side sigma (h, k)))) =
      (parentBase allocation h : ℝ) * branchConditionalCost h.val.val.1 side := by
  simp_rw [class_groupedEntropy_eq_masked allocation _ side hside,
    maskedBranchMass_eq_conditional, groupedEntropy_mul]
  simp only [branchConditionalCost, Finset.mul_sum, mul_add]

theorem projected_native_entropy_eq (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (hside : side ≠ 0) :
    projectedReferenceEntropy (base (K := K) (tick := tick) allocation sigma side)
        (classDesignated false side sigma)
        (groupCap (base allocation sigma side) (classDesignated false side sigma)
          (nativeLaw allocation false side sigma) 0) +
      projectedReferenceEntropy (base (K := K) (tick := tick) allocation sigma side)
        (classDesignated true side sigma)
        (groupCap (base allocation sigma side) (classDesignated true side sigma)
          (nativeLaw allocation true side sigma) 0) =
      ∑ h : ActiveOrder K tick sigma, (parentBase allocation h : ℝ) *
        (observedEntropy h side - workCapacity h.val.val.1 side) := by
  rw [JointProjectedGroupEntropy.projectedReferenceEntropy_eq_sum_counts_groupedEntropy,
    JointProjectedGroupEntropy.projectedReferenceEntropy_eq_sum_counts_groupedEntropy,
    ← Finset.sum_add_distrib, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  rw [history_projected_entropy_eq allocation side hside,
    branchConditionalCost_eq_observed h side hside]

end MatrixMultiplication.AllFieldGroupProjectedEntropy

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

theorem nativeCompatibilityRate_eq_oai (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (hside : side ≠ 0) :
    nativeCompatibilityRate (K := K) (tick := tick) allocation sigma side =
      orderNativeDegree (K := K) (tick := tick) allocation sigma side := by
  have hp := projected_native_entropy_eq (K := K) (tick := tick) allocation sigma side hside
  have hb := baseEntropy_sub_pairReferenceEntropy (K := K) (tick := tick) allocation sigma side
  unfold nativeCompatibilityRate compatibilityRate
  rw [show ∀ a b c d : ℝ, a - b + c + d = (a - b) + (c + d) by intros; ring,
    hb, hp, ← Finset.sum_add_distrib]
  unfold orderNativeDegree
  apply Finset.sum_congr rfl
  intro h _
  have hs : (parentBase allocation h : ℝ) =
      (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h :=
    population_cast_real allocation 1 (h.val.val.1.source, h.val.val.2)
  rw [hs]
  ring

end MatrixMultiplication.AllFieldGroupNativeDegreeBound

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.nativeCompatibilityRate_eq_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.nativeCompatibilityRate_eq_oai
