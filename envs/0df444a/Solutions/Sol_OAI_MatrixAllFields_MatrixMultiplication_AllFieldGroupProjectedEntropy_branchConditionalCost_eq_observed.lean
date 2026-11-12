-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.branchConditionalCost_eq_observed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:24:44.000388+00:00
-- url     : https://prove2.me/submissions/c77e176f-8935-4f41-a93d-c11a32633065

import Mathlib
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldActiveCapacity_workCapacity_stageC_physical

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
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

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldParameters

open MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

theorem homogeneousEntropy_normalized {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∑ a, p a = 1) :
    homogeneousEntropy p = finiteEntropy p := by
  simp [homogeneousEntropy, hp]

theorem entropyTerm_divide (x m : ℝ) :
    entropyTerm (x / m) = entropyTerm x / m + (x / m) * Real.log m := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hm : m = 0
  · simp [hm]
  rw [entropyTerm, Real.log_div hx hm]
  unfold entropyTerm
  ring

theorem homogeneousEntropy_eq_mass_mul {A : Type*} [Fintype A]
    (p : A → ℝ) (hm : ∑ a, p a ≠ 0) :
    homogeneousEntropy p =
      (∑ a, p a) * finiteEntropy (fun a => p a / ∑ b, p b) := by
  simp only [finiteEntropy, entropyTerm_divide, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.sum_mul]
  unfold homogeneousEntropy finiteEntropy
  rw [div_self hm]
  field_simp
  ring

theorem homogeneousEntropy_zero {A : Type*} [Fintype A] :
    homogeneousEntropy (fun _ : A => 0) = 0 := by
  simp [homogeneousEntropy, finiteEntropy]

end

end MatrixMultiplication.AllFieldParameters

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

section GroupEntropy

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

omit [Fintype K] in
theorem groupMass_relabel {L : Type*} (e : K ≃ L) (p : U → ℝ)
    (group : U → K) (k : K) :
    groupMass p (e ∘ group) (e k) = groupMass p group k := by
  simp only [groupMass, Function.comp_apply, e.injective.eq_iff]

omit [Fintype A] [Fintype K] in
theorem groupLaw_relabel {L : Type*} (e : K ≃ L) (p : U → ℝ)
    (group : U → K) (law : U → A → ℝ) (k : K) :
    groupLaw p (e ∘ group) law (e k) = groupLaw p group law k := by
  funext a
  simp only [groupLaw, groupMass_relabel, Function.comp_apply, e.injective.eq_iff]

theorem groupedEntropy_relabel {L : Type*} [Fintype L] (e : K ≃ L)
    (p : U → ℝ) (group : U → K) (law : U → A → ℝ) :
    groupedEntropy p (e ∘ group) law = groupedEntropy p group law := by
  unfold groupedEntropy
  calc
    (∑ l, groupMass p (e ∘ group) l * finiteEntropy (groupLaw p (e ∘ group) law l)) =
        ∑ k, groupMass p (e ∘ group) (e k) *
          finiteEntropy (groupLaw p (e ∘ group) law (e k)) := (e.sum_comp _).symm
    _ = ∑ k, groupMass p group k * finiteEntropy (groupLaw p group law k) := by
      simp only [groupMass_relabel, groupLaw_relabel]

omit [Fintype K] in
theorem groupMass_reindex (e : U ≃ U) (p : U → ℝ) (group : U → K)
    (hp : ∀ u, p (e u) = p u) (k : K) :
    groupMass p (group ∘ e) k = groupMass p group k := by
  unfold groupMass
  calc
    (∑ u, if (group ∘ e) u = k then p u else 0) =
        ∑ u, if group (e u) = k then p (e u) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      simp only [Function.comp_apply, hp u]
    _ = ∑ u, if group u = k then p u else 0 :=
      e.sum_comp (fun u => if group u = k then p u else 0)

omit [Fintype A] [Fintype K] in
theorem groupLaw_reindex (e : U ≃ U) (p : U → ℝ) (group : U → K)
    (law : U → A → ℝ) (hp : ∀ u, p (e u) = p u) (k : K) :
    groupLaw p (group ∘ e) (law ∘ e) k = groupLaw p group law k := by
  funext a
  unfold groupLaw
  rw [groupMass_reindex e p group hp]
  congr 1
  calc
    (∑ u, if (group ∘ e) u = k then p u * (law ∘ e) u a else 0) =
        ∑ u, if group (e u) = k then p (e u) * law (e u) a else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      simp only [Function.comp_apply, hp u]
    _ = ∑ u, if group u = k then p u * law u a else 0 :=
      e.sum_comp (fun u => if group u = k then p u * law u a else 0)

theorem groupedEntropy_reindex (e : U ≃ U) (p : U → ℝ) (group : U → K)
    (law : U → A → ℝ) (hp : ∀ u, p (e u) = p u) :
    groupedEntropy p (group ∘ e) (law ∘ e) = groupedEntropy p group law := by
  simp only [groupedEntropy, groupMass_reindex e p group hp,
    groupLaw_reindex e p group law hp]

end GroupEntropy

end MatrixMultiplication.JointCompatibilityIncidence

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_NativeCapacity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldNativeCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {A : Type*} [Fintype A]

theorem nativeCapacity_sharing (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (priority : Placement) (q : Shape → Fin 3 → A → ℝ)
    (i : Fin 3) (hi : i ≠ 0) :
    nativeCapacity support s p priority q i =
      homogeneousEntropy (pairLaw support s p (fun u => q u (priority i))) -
        2 * groupedEntropy support p priority i (fun u => q u (priority i)) := by
  simp only [nativeCapacity, ite_eq_right hi]

end MatrixMultiplication.AllFieldNativeCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_NativeLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldNativeCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators

theorem stageACapacity_sharing (g : Shape) (hg : g ∈ positiveInitial)
    (i : Fin 3) (hi : i ≠ 0) :
    stageACapacity g i = finiteEntropy (stageAPairLaw g hg i).mass -
      2 * groupedEntropy (below g) (fun u => (stageALaw g u : ℝ))
        (Equiv.refl (Fin 3)) i (fun u a => (halfLaw u i a : ℝ)) := by
  rw [stageACapacity, nativeCapacity_sharing _ _ _ _ _ i hi]
  congr 1
  exact homogeneousEntropy_normalized _ (stageAPairLaw g hg i).total

theorem stageBCapacity_sharing (t : Shape) (ht : t ∈ positiveSecond)
    (i : Fin 3) (hi : i ≠ 0) :
    stageBCapacity t i = finiteEntropy (stageBPairLaw t ht (stageBPriority t i)).mass -
      2 * groupedEntropy (below t) (fun u => (stageBLaw t u : ℝ))
        (stageBPriority t) i (fun u a => (littleLaw t u (stageBPriority t i) a : ℝ)) := by
  rw [stageBCapacity, nativeCapacity_sharing _ _ _ _ _ i hi]
  congr 1
  exact homogeneousEntropy_normalized _ (stageBPairLaw t ht (stageBPriority t i)).total

end MatrixMultiplication.AllFieldNativeCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupProjectedEntropy
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointNativeGroupedEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section FiniteGroups

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

omit [Fintype K] in
theorem groupMeasure_total (p : U → ℝ) (group : U → K) (q : U → A → ℝ)
    (hq : ∀ u, ∑ a, q u a = 1) (k : K) :
    ∑ a, groupMeasure p group q k a =
      JointCompatibilityIncidence.groupMass p group k := by
  unfold groupMeasure JointCompatibilityIncidence.groupMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : group u = k
  · simp only [hu, ite_true, if_true, ← Finset.mul_sum, hq, mul_one]
  · simp [hu]

omit [Fintype K] [Fintype A] in
theorem groupMeasure_zero_of_mass_zero (p : U → ℝ) (group : U → K)
    (q : U → A → ℝ) (hp : ∀ u, 0 ≤ p u) (k : K)
    (hm : JointCompatibilityIncidence.groupMass p group k = 0) :
    groupMeasure p group q k = fun _ => 0 := by
  have ht : ∀ u, (if group u = k then p u else 0) = 0 := by
    have hn : ∀ u ∈ (Finset.univ : Finset U),
        0 ≤ (if group u = k then p u else 0) := by
      intro u _
      split_ifs
      · exact hp u
      · exact le_rfl
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hm
    exact fun u => hz u (Finset.mem_univ u)
  funext a
  apply Finset.sum_eq_zero
  intro u _
  by_cases hu : group u = k
  · have hpu : p u = 0 := by simpa only [hu, ite_true, if_true] using ht u
    simp [hu, hpu]
  · simp [hu]

omit [Fintype K] in
theorem group_term_eq_homogeneous (p : U → ℝ) (group : U → K)
    (q : U → A → ℝ) (hp : ∀ u, 0 ≤ p u)
    (hq : ∀ u, ∑ a, q u a = 1) (k : K) :
    JointCompatibilityIncidence.groupMass p group k *
      finiteEntropy (JointCompatibilityIncidence.groupLaw p group q k) =
      homogeneousEntropy (groupMeasure p group q k) := by
  by_cases hm : JointCompatibilityIncidence.groupMass p group k = 0
  · rw [hm, zero_mul, groupMeasure_zero_of_mass_zero p group q hp k hm,
      homogeneousEntropy_zero]
  · have ht := groupMeasure_total p group q hq k
    have hn : ∑ a, groupMeasure p group q k a ≠ 0 := by rwa [ht]
    rw [homogeneousEntropy_eq_mass_mul _ hn, ht]
    rfl

theorem groupedEntropy_eq_sum_homogeneous (p : U → ℝ) (group : U → K)
    (q : U → A → ℝ) (hp : ∀ u, 0 ≤ p u)
    (hq : ∀ u, ∑ a, q u a = 1) :
    JointCompatibilityIncidence.groupedEntropy p group q =
      ∑ k, homogeneousEntropy (groupMeasure p group q k) := by
  unfold JointCompatibilityIncidence.groupedEntropy
  exact Finset.sum_congr rfl fun k _ => group_term_eq_homogeneous p group q hp hq k

theorem homogeneousEntropy_mul_normalized (s : ℝ) (q : A → ℝ)
    (hq : ∑ a, q a = 1) :
    homogeneousEntropy (fun a => s * q a) = s * homogeneousEntropy q := by
  have he : finiteEntropy (fun a => s * q a) =
      entropyTerm s + s * finiteEntropy q := by
    simp only [finiteEntropy, entropyTerm_mul, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hq, one_mul]
  rw [homogeneousEntropy, ← Finset.mul_sum, hq, mul_one, he,
    homogeneousEntropy_normalized q hq]
  unfold entropyTerm
  ring

omit [Fintype U] [Fintype K] in
theorem singletonResidualGroup_eq_inl (d : U → Prop) (weight : U → K)
    (u v : U) :
    singletonResidualGroup d weight v = Sum.inl u ↔ d u ∧ v = u := by
  constructor
  · intro h
    by_cases hv : d v
    · have he : v = u := by simpa [singletonResidualGroup, hv] using h
      exact ⟨he ▸ hv, he⟩
    · simp [singletonResidualGroup, hv] at h
  · rintro ⟨hu, rfl⟩
    simp [singletonResidualGroup, hu]

omit [Fintype U] [Fintype K] in
theorem singletonResidualGroup_eq_inr (d : U → Prop) (weight : U → K)
    (u : U) (k : K) :
    singletonResidualGroup d weight u = Sum.inr k ↔ ¬ d u ∧ weight u = k := by
  by_cases hu : d u <;> simp [singletonResidualGroup, hu]

omit [Fintype K] [Fintype A] in
theorem groupMeasure_singleton (p : U → ℝ) (d : U → Prop)
    (weight : U → K) (q : U → A → ℝ) (u : U) :
    groupMeasure p (singletonResidualGroup d weight) q (Sum.inl u) =
      fun a => if d u then p u * q u a else 0 := by
  funext a
  simp only [groupMeasure, singletonResidualGroup_eq_inl]
  by_cases hu : d u <;> simp [hu]

omit [Fintype K] [Fintype A] in
theorem groupMeasure_residual (p : U → ℝ) (d : U → Prop)
    (weight : U → K) (q : U → A → ℝ) (k : K) :
    groupMeasure p (singletonResidualGroup d weight) q (Sum.inr k) =
      fun a => ∑ u, if ¬ d u ∧ weight u = k then p u * q u a else 0 := by
  funext a
  simp only [groupMeasure, singletonResidualGroup_eq_inr]

theorem groupedEntropy_singletons_residuals (p : U → ℝ) (d : U → Prop)
    (weight : U → K) (q : U → A → ℝ) (hp : ∀ u, 0 ≤ p u)
    (hq : ∀ u, ∑ a, q u a = 1) :
    JointCompatibilityIncidence.groupedEntropy p (singletonResidualGroup d weight) q =
      (∑ u, if d u then p u * homogeneousEntropy (q u) else 0) +
      ∑ k, homogeneousEntropy (fun a =>
        ∑ u, if ¬ d u ∧ weight u = k then p u * q u a else 0) := by
  rw [groupedEntropy_eq_sum_homogeneous p _ q hp hq, Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro u _
    rw [groupMeasure_singleton]
    by_cases hu : d u
    · simp only [hu, ite_true, if_true]
      exact homogeneousEntropy_mul_normalized (p u) (q u) (hq u)
    · simp only [hu, ite_false, if_false, homogeneousEntropy_zero]
  · apply Finset.sum_congr rfl
    intro k _
    rw [groupMeasure_residual]

end FiniteGroups

section NativeSupport

variable {A : Type*} [Fintype A]

theorem groupedEntropy_eq_native (support : List Shape) (p : Shape → ℝ)
    (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (hp : ∀ i : SupportIndex support, 0 ≤ p support[i.val])
    (hq : ∀ i : SupportIndex support, ∑ a, q support[i.val] a = 1) :
    JointCompatibilityIncidence.groupedEntropy
      (fun i : SupportIndex support => p support[i.val])
      (nativeGroup support priority position hbound)
      (fun i : SupportIndex support => q support[i.val]) =
      AllFieldNativeCapacity.groupedEntropy support p priority position q := by
  rw [nativeGroup, groupedEntropy_singletons_residuals _ _ _ _ hp hq]
  unfold AllFieldNativeCapacity.groupedEntropy AllFieldNativeCapacity.singletonEntropy
  congr 1
  · exact Fin.sum_univ_fun_getElem support fun u =>
      if AllFieldNativeCapacity.designated priority position u
      then p u * homogeneousEntropy (q u) else 0
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    funext a
    simp only [ownWeight, Fin.ext_iff]
    exact Fin.sum_univ_fun_getElem support fun u =>
      if ¬ AllFieldNativeCapacity.designated priority position u ∧
          u (priority position) = k.val then p u * q u a else 0

end NativeSupport

end MatrixMultiplication.JointNativeGroupedEntropy

end
end

end MatrixAllFields

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

omit [Fintype A] in
theorem groupMeasure_designated_some (p : U → ℝ) (d : U → Prop)
    (q : U → A → ℝ) (u : U) :
    groupMeasure p (JointCompatibilityIncidence.designatedGroup d) q (some u) =
      fun a => if d u then p u * q u a else 0 := by
  funext a
  simp only [groupMeasure, JointCompatibilityIncidence.designatedGroup_eq_some]
  by_cases hu : d u <;> simp [hu]

omit [Fintype A] in
theorem groupMeasure_designated_none (p : U → ℝ) (d : U → Prop)
    (q : U → A → ℝ) :
    groupMeasure p (JointCompatibilityIncidence.designatedGroup d) q none =
      fun a => ∑ u, if ¬ d u then p u * q u a else 0 := by
  funext a
  simp only [groupMeasure, JointCompatibilityIncidence.designatedGroup_eq_none]

theorem groupedEntropy_designated (p : U → ℝ) (d : U → Prop)
    (q : U → A → ℝ) (hp : ∀ u, 0 ≤ p u) (hq : ∀ u, ∑ a, q u a = 1) :
    JointCompatibilityIncidence.groupedEntropy p
        (JointCompatibilityIncidence.designatedGroup d) q =
      (∑ u, if d u then p u * homogeneousEntropy (q u) else 0) +
      homogeneousEntropy (fun a => ∑ u, if ¬ d u then p u * q u a else 0) := by
  rw [groupedEntropy_eq_sum_homogeneous p _ q hp hq, Fintype.sum_option,
    groupMeasure_designated_none, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [groupMeasure_designated_some]
  by_cases hu : d u
  · simp only [hu, ite_true, if_true]
    exact homogeneousEntropy_mul_normalized (p u) (q u) (hq u)
  · simp only [hu, ite_false, if_false, homogeneousEntropy_zero]

theorem groupedEntropy_partition (p : U → ℝ) (d : U → Prop) (weight : U → K)
    (q : U → A → ℝ) (hp : ∀ u, 0 ≤ p u) (hq : ∀ u, ∑ a, q u a = 1) :
    JointCompatibilityIncidence.groupedEntropy p (singletonResidualGroup d weight) q =
      ∑ k, JointCompatibilityIncidence.groupedEntropy
        (fun u => if weight u = k then p u else 0)
        (JointCompatibilityIncidence.designatedGroup d) q := by
  have hclass (k : K) := groupedEntropy_designated
    (fun u => if weight u = k then p u else 0) d q
    (fun u => by split_ifs; exact hp u; exact le_rfl) hq
  rw [groupedEntropy_singletons_residuals p d weight q hp hq]
  simp_rw [hclass]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro u _
    by_cases hu : d u <;> simp [hu, ite_mul]
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    funext a
    apply Finset.sum_congr rfl
    intro u _
    by_cases hd : d u <;> by_cases hw : weight u = k <;> simp [hd, hw]

theorem groupedEntropy_conditional_partition (p : FiniteLaw U) (d : U → Prop)
    (weight : U → K) (q : U → A → ℝ) (hq : ∀ u, ∑ a, q u a = 1) :
    JointCompatibilityIncidence.groupedEntropy p.mass (singletonResidualGroup d weight) q =
      ∑ k, (p.map weight).mass k *
        JointCompatibilityIncidence.groupedEntropy (p.conditional weight k).mass
          (JointCompatibilityIncidence.designatedGroup d) q := by
  rw [groupedEntropy_partition p.mass d weight q p.nonneg hq]
  apply Finset.sum_congr rfl
  intro k _
  have hm : (fun u => if weight u = k then p.mass u else 0) =
      fun u => (p.map weight).mass k * (p.conditional weight k).mass u := by
    funext u
    exact (p.map_mass_mul_conditional weight k u).symm
  rw [hm, groupedEntropy_mul]

end FiniteGroups

section NativeSupport

variable {A : Type*} [Fintype A]

theorem native_groupedEntropy_eq_sum_conditional (support : List Shape) (p : Shape → ℝ)
    (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (law : FiniteLaw (SupportIndex support))
    (hlaw : ∀ i : SupportIndex support, law.mass i = p support[i.val])
    (hq : ∀ i : SupportIndex support, ∑ a, q support[i.val] a = 1) :
    AllFieldNativeCapacity.groupedEntropy support p priority position q =
      ∑ k : Fin 17, (law.map (ownWeight support priority position hbound)).mass k *
        JointCompatibilityIncidence.groupedEntropy
          (law.conditional (ownWeight support priority position hbound) k).mass
          (JointCompatibilityIncidence.designatedGroup
            (fun i => AllFieldNativeCapacity.designated priority position support[i.val]))
          (fun i => q support[i.val]) := by
  have hp (i : SupportIndex support) : 0 ≤ p support[i.val] := by
    rw [← hlaw i]
    exact law.nonneg i
  have hm : law.mass = fun i : SupportIndex support => p support[i.val] := funext hlaw
  have hn : JointCompatibilityIncidence.groupedEntropy law.mass
      (nativeGroup support priority position hbound) (fun i => q support[i.val]) =
      AllFieldNativeCapacity.groupedEntropy support p priority position q := by
    rw [hm]
    exact groupedEntropy_eq_native support p priority position q hbound hp hq
  exact hn.symm.trans (groupedEntropy_conditional_partition law _ _ _ hq)

end NativeSupport

end MatrixMultiplication.JointGroupedEntropyPartition

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldNativeGroupedRates

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open JointNativeGroupedEntropy JointGroupedEntropyPartition
open AllFieldNativeCapacity AllFieldPairConditionalEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section Reindex

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

omit [Fintype U] [Fintype K] in
theorem singletonResidualGroup_transport (e : U ≃ U) (c : K ≃ K)
    (d : U → Prop) (weight : U → K)
    (hw : ∀ u, c (weight u) = weight (e u)) :
    (Equiv.sumCongr e c) ∘ singletonResidualGroup (d ∘ e) weight =
      singletonResidualGroup d weight ∘ e := by
  funext u
  by_cases hu : d (e u) <;>
    simp [singletonResidualGroup, Function.comp_apply, hu, hw]

theorem singletonResidual_groupedEntropy_reindex (e : U ≃ U) (c : K ≃ K)
    (p : U → ℝ) (d : U → Prop) (weight : U → K) (q : U → A → ℝ)
    (hp : ∀ u, p (e u) = p u) (hw : ∀ u, c (weight u) = weight (e u)) :
    JointCompatibilityIncidence.groupedEntropy p
      (singletonResidualGroup (d ∘ e) weight) (q ∘ e) =
      JointCompatibilityIncidence.groupedEntropy p (singletonResidualGroup d weight) q := by
  calc
    _ = JointCompatibilityIncidence.groupedEntropy p
        ((Equiv.sumCongr e c) ∘ singletonResidualGroup (d ∘ e) weight) (q ∘ e) :=
      (JointCompatibilityIncidence.groupedEntropy_relabel (Equiv.sumCongr e c) p _ _).symm
    _ = JointCompatibilityIncidence.groupedEntropy p
        (singletonResidualGroup d weight ∘ e) (q ∘ e) := by
      rw [singletonResidualGroup_transport e c d weight hw]
    _ = _ := JointCompatibilityIncidence.groupedEntropy_reindex e p _ q hp

theorem right_conditional_sum_eq (e : U ≃ U) (c : K ≃ K)
    (p : FiniteLaw U) (d : U → Prop) (weight : U → K) (q : U → A → ℝ)
    (hp : ∀ u, p.mass (e u) = p.mass u)
    (hw : ∀ u, c (weight u) = weight (e u)) (hq : ∀ u, ∑ a, q u a = 1) :
    (∑ k, (p.map weight).mass k *
      JointCompatibilityIncidence.groupedEntropy (p.conditional weight k).mass
        (JointCompatibilityIncidence.designatedGroup (d ∘ e)) (q ∘ e)) =
      JointCompatibilityIncidence.groupedEntropy p.mass (singletonResidualGroup d weight) q := by
  rw [← groupedEntropy_conditional_partition p (d ∘ e) weight (q ∘ e)
    (fun u => hq (e u))]
  exact singletonResidual_groupedEntropy_reindex e c p.mass d weight q hp hw

end Reindex

theorem supportIndexEquiv_get {α : Type*} [DecidableEq α] (xs : List α)
    (hn : xs.Nodup) (f : α → α) (hm : ∀ x ∈ xs, f x ∈ xs)
    (hi : ∀ x ∈ xs, f (f x) = x) (i : Fin xs.length) :
    xs.get (supportIndexEquiv xs hn f hm hi i) = f (xs.get i) := by
  exact congrArg Subtype.val ((hn.getEquiv xs).apply_symm_apply
    ((supportSubtypeEquiv xs f hm hi) ((hn.getEquiv xs) i)))

section NativeSupport

variable {A : Type*} [Fintype A]

theorem native_right_conditional_sum_eq (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (hn : support.Nodup) (hm : ∀ u ∈ support, complement s u ∈ support)
    (hsupp : ∀ u ∈ support, ∀ side, u side ≤ s side)
    (hs : s (priority position) < 17)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (law : FiniteLaw (SupportIndex support))
    (hlaw : ∀ i : SupportIndex support, law.mass i = p support[i.val])
    (hp : ∀ u ∈ support, p (complement s u) = p u)
    (hq : ∀ i : SupportIndex support, ∑ a, q support[i.val] a = 1) :
    (∑ k : Fin 17, (law.map (ownWeight support priority position hbound)).mass k *
      JointCompatibilityIncidence.groupedEntropy
        (law.conditional (ownWeight support priority position hbound) k).mass
        (JointCompatibilityIncidence.designatedGroup (fun i =>
          AllFieldNativeCapacity.designated priority position (complement s support[i.val])))
        (fun i => q (complement s support[i.val]))) =
      AllFieldNativeCapacity.groupedEntropy support p priority position q := by
  let hi : ∀ u ∈ support, complement s (complement s u) = u :=
    fun u hu => complement_involution_of_le s u (hsupp u hu)
  let e := supportIndexEquiv support hn (complement s) hm hi
  let c := boundedComplementEquiv (s (priority position)) hs
  let weight := ownWeight support priority position hbound
  let d : SupportIndex support → Prop :=
    fun i => AllFieldNativeCapacity.designated priority position support[i.val]
  let q₀ : SupportIndex support → A → ℝ := fun i => q support[i.val]
  have he (i : SupportIndex support) :
      support[(e i).val] = complement s support[i.val] := by
    simpa only [List.get_eq_getElem] using
      supportIndexEquiv_get support hn (complement s) hm hi i
  have hmass (i : SupportIndex support) : law.mass (e i) = law.mass i := by
    simp only [hlaw, he]
    exact hp _ (List.getElem_mem i.isLt)
  have hw (i : SupportIndex support) : c (weight i) = weight (e i) := by
    apply Fin.ext
    change (if support[i.val] (priority position) ≤ s (priority position)
      then s (priority position) - support[i.val] (priority position)
      else support[i.val] (priority position)) = support[(e i).val] (priority position)
    rw [ite_eq_left (hsupp _ (List.getElem_mem i.isLt) _), he]
    rfl
  have hright := right_conditional_sum_eq e c law d weight q₀ hmass hw hq
  have hd : d ∘ e = fun i =>
      AllFieldNativeCapacity.designated priority position (complement s support[i.val]) := by
    funext i
    dsimp only [d, Function.comp_apply]
    rw [he]
  have hqr : q₀ ∘ e = fun i => q (complement s support[i.val]) := by
    funext i
    dsimp only [q₀, Function.comp_apply]
    rw [he]
  rw [hd, hqr] at hright
  have hnonneg (i : SupportIndex support) : 0 ≤ p support[i.val] := by
    rw [← hlaw i]
    exact law.nonneg i
  have hmassfun : law.mass = fun i : SupportIndex support => p support[i.val] := funext hlaw
  calc
    _ = JointCompatibilityIncidence.groupedEntropy law.mass
        (nativeGroup support priority position hbound) (fun i => q support[i.val]) := by
      simpa only [d, q₀, weight, nativeGroup] using hright
    _ = _ := by
      rw [hmassfun]
      exact groupedEntropy_eq_native support p priority position q hbound hnonneg hq

theorem native_two_conditional_sums_eq (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (hn : support.Nodup) (hm : ∀ u ∈ support, complement s u ∈ support)
    (hsupp : ∀ u ∈ support, ∀ side, u side ≤ s side)
    (hs : s (priority position) < 17)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (law : FiniteLaw (SupportIndex support))
    (hlaw : ∀ i : SupportIndex support, law.mass i = p support[i.val])
    (hp : ∀ u ∈ support, p (complement s u) = p u)
    (hq : ∀ i : SupportIndex support, ∑ a, q support[i.val] a = 1) :
    (∑ k : Fin 17, (law.map (ownWeight support priority position hbound)).mass k *
      (JointCompatibilityIncidence.groupedEntropy
        (law.conditional (ownWeight support priority position hbound) k).mass
        (JointCompatibilityIncidence.designatedGroup (fun i =>
          AllFieldNativeCapacity.designated priority position support[i.val]))
        (fun i => q support[i.val]) +
      JointCompatibilityIncidence.groupedEntropy
        (law.conditional (ownWeight support priority position hbound) k).mass
        (JointCompatibilityIncidence.designatedGroup (fun i =>
          AllFieldNativeCapacity.designated priority position (complement s support[i.val])))
        (fun i => q (complement s support[i.val])))) =
      2 * AllFieldNativeCapacity.groupedEntropy support p priority position q := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← native_groupedEntropy_eq_sum_conditional support p priority position q hbound law hlaw hq,
    native_right_conditional_sum_eq support s p priority position q hn hm hsupp hs
      hbound law hlaw hp hq]
  ring

end NativeSupport

theorem stageA_twoHalfConditionalCost_eq (g : Shape) (hg : g ∈ positiveInitial)
    (priority : Placement) (position : Fin 3) :
    twoHalfConditionalCost (below g) g priority position
      (fun u a => (halfLaw u (priority position) a : ℝ)) (stageASplitLaw g hg)
      (stageASplitWeight g hg (priority position)) =
      2 * AllFieldNativeCapacity.groupedEntropy (below g)
        (fun u => (stageALaw g u : ℝ)) priority position
        (fun u a => (halfLaw u (priority position) a : ℝ)) := by
  have hs : g (priority position) < 17 :=
    Nat.lt_succ_of_le ((positiveInitial_shape_spec g hg).1 (priority position))
  let hb : ∀ i : SupportIndex (below g), (below g)[i.val] (priority position) < 17 :=
    fun i => lt_of_le_of_lt (below_le (List.getElem_mem i.isLt) _) hs
  have hq (i : SupportIndex (below g)) :
      ∑ a, (halfLaw (below g)[i.val] (priority position) a : ℝ) = 1 :=
    (halfFiniteLaw _ (stageA_children_size g hg _ (List.getElem_mem i.isLt))
      (priority position)).total
  have hh := native_two_conditional_sums_eq (below g) g
    (fun u => (stageALaw g u : ℝ)) priority position
    (fun u a => (halfLaw u (priority position) a : ℝ))
    (stageA_below_nodup g hg) (fun u hu => (stageA_support_complement g hg u hu).1)
    (fun _ hu => below_le hu) hs hb (stageASplitLaw g hg) (fun _ => rfl)
    (fun u hu => by rw [stageALaw_complement g u hg hu]) hq
  exact hh

theorem stageB_twoHalfConditionalCost_eq (t : Shape) (ht : t ∈ positiveSecond)
    (priority : Placement) (position : Fin 3) :
    twoHalfConditionalCost (below t) t priority position
      (fun u a => (littleLaw t u (priority position) a : ℝ)) (stageBSplitLaw t ht)
      (stageBSplitWeight t ht (priority position)) =
      2 * AllFieldNativeCapacity.groupedEntropy (below t)
        (fun u => (stageBLaw t u : ℝ)) priority position
        (fun u a => (littleLaw t u (priority position) a : ℝ)) := by
  have hs : t (priority position) < 17 :=
    Nat.lt_succ_of_le ((positiveSecond_shape_spec t ht).1 (priority position))
  let hb : ∀ i : SupportIndex (below t), (below t)[i.val] (priority position) < 17 :=
    fun i => lt_of_le_of_lt (below_le (List.getElem_mem i.isLt) _) hs
  have hq (i : SupportIndex (below t)) :
      ∑ a, (littleLaw t (below t)[i.val] (priority position) a : ℝ) = 1 :=
    (littleFiniteLaw t _ (priority position)).total
  have hh := native_two_conditional_sums_eq (below t) t
    (fun u => (stageBLaw t u : ℝ)) priority position
    (fun u a => (littleLaw t u (priority position) a : ℝ))
    (stageB_below_nodup t ht) (fun u hu => (stageB_support_complement t ht u hu).1)
    (fun _ hu => below_le hu) hs hb (stageBSplitLaw t ht) (fun _ => rfl)
    (fun u hu => by rw [stageBLaw_complement t u ht hu]) hq
  exact hh

theorem stageA_twoHalfConditionalCost_eq_entropy_sub_capacity
    (g : Shape) (hg : g ∈ positiveInitial) (side : Fin 3) (hside : side ≠ 0) :
    twoHalfConditionalCost (below g) g (Equiv.refl (Fin 3)) side
      (fun u a => (halfLaw u side a : ℝ)) (stageASplitLaw g hg)
      (stageASplitWeight g hg side) =
      finiteEntropy (stageAPairLaw g hg side).mass - stageACapacity g side := by
  rw [stageACapacity_sharing g hg side hside]
  have hh := stageA_twoHalfConditionalCost_eq g hg (Equiv.refl (Fin 3)) side
  simpa only [Equiv.refl_apply, sub_sub_cancel] using hh

theorem stageB_twoHalfConditionalCost_eq_entropy_sub_capacity
    (t : Shape) (ht : t ∈ positiveSecond) (side : Fin 3) (hside : side ≠ 0) :
    twoHalfConditionalCost (below t) t (stageBPriority t) side
      (fun u a => (littleLaw t u (stageBPriority t side) a : ℝ)) (stageBSplitLaw t ht)
      (stageBSplitWeight t ht (stageBPriority t side)) =
      finiteEntropy (stageBPairLaw t ht (stageBPriority t side)).mass -
        stageBCapacity t side := by
  rw [stageBCapacity_sharing t ht side hside]
  have hh := stageB_twoHalfConditionalCost_eq t ht (stageBPriority t) side
  simpa only [sub_sub_cancel] using hh

end MatrixMultiplication.AllFieldNativeGroupedRates

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

section Kernel

variable {U V G A : Type*} [Fintype U] [Fintype V] [Fintype G] [Fintype A]

theorem groupedEntropy_const_one (p : U → ℝ) (group : U → G) :
    groupedEntropy p group (fun _ (_ : A) => 1) = 0 := by
  unfold groupedEntropy
  apply Finset.sum_eq_zero
  intro g _
  by_cases hg : groupMass p group g = 0
  · rw [hg, zero_mul]
  · have he : groupLaw p group (fun _ (_ : A) => 1) g = fun _ => 1 := by
      funext a
      simp only [groupLaw, mul_one]
      exact div_self hg
    rw [he]
    simp [finiteEntropy, entropyTerm]

end Kernel

variable {K tick : ℕ} {sigma : Placement}

theorem branchConditionalCost_eq (w : Work K) (side : Fin 3) (hside : side ≠ 0) :
    branchConditionalCost w side =
      if w.stage ≠ 2 then
        finiteEntropy (nativePairLaw w (w.priority side)).mass - workCapacity w side
      else 0 := by
  cases w with
  | stageA h =>
      have hs : (Work.stageA h).stage ≠ 2 := by change (0 : Fin 3) ≠ 2; decide
      have hl : branchLaw (Work.stageA h) =
          AllFieldNativeCapacity.stageASplitLaw (initialShape h.val) h.property := rfl
      have hw : nativeSplitWeightCode (Work.stageA h) ((Work.stageA h).priority side) =
          AllFieldPairConditionalEntropy.stageASplitWeight (initialShape h.val) h.property side := by
        funext b
        apply Fin.ext
        rfl
      have hd (right : Bool) : nativeBranchDesignated (Work.stageA h) right side =
          fun b => AllFieldNativeCapacity.designated (Equiv.refl (Fin 3)) side
            (halfShape (initialShape h.val) (below (initialShape h.val))[b.val] right) := by
        funext b
        apply propext
        change (_ ∧ _) ↔ _
        exact ⟨fun hh => hh.2, fun hh => ⟨hs, hh⟩⟩
      have hq (right : Bool) : branchHalfLaw (Work.stageA h) right side =
          fun b a => (halfLaw
            (halfShape (initialShape h.val) (below (initialShape h.val))[b.val] right)
            side a : ℝ) := rfl
      rw [ite_eq_left hs]
      rw [branchConditionalCost, hl, hw]
      simp_rw [hd, hq]
      exact stageA_twoHalfConditionalCost_eq_entropy_sub_capacity _ h.property side hside
  | stageB h =>
      have hs : (Work.stageB h).stage ≠ 2 := by change (1 : Fin 3) ≠ 2; decide
      have hl : branchLaw (Work.stageB h) =
          AllFieldNativeCapacity.stageBSplitLaw (aShape h.val) h.property := rfl
      have hw : nativeSplitWeightCode (Work.stageB h) ((Work.stageB h).priority side) =
          AllFieldPairConditionalEntropy.stageBSplitWeight (aShape h.val) h.property
            (stageBPriority (aShape h.val) side) := by
        funext b
        apply Fin.ext
        rfl
      have hd (right : Bool) : nativeBranchDesignated (Work.stageB h) right side =
          fun b => AllFieldNativeCapacity.designated (stageBPriority (aShape h.val)) side
            (halfShape (aShape h.val) (below (aShape h.val))[b.val] right) := by
        funext b
        apply propext
        change (_ ∧ _) ↔ _
        exact ⟨fun hh => hh.2, fun hh => ⟨hs, hh⟩⟩
      have hq (right : Bool) : branchHalfLaw (Work.stageB h) right side =
          fun b a => (littleLaw (aShape h.val)
            (halfShape (aShape h.val) (below (aShape h.val))[b.val] right)
            (stageBPriority (aShape h.val) side) a : ℝ) := rfl
      rw [ite_eq_left hs]
      rw [branchConditionalCost, hl, hw]
      simp_rw [hd, hq]
      exact stageB_twoHalfConditionalCost_eq_entropy_sub_capacity _ h.property side hside
  | stageC h =>
      rw [ite_eq_right (show ¬ (Work.stageC h).stage ≠ 2 by simp [Work.stage])]
      unfold branchConditionalCost
      have hq (right : Bool) : branchHalfLaw (Work.stageC h) right side =
          fun _ _ => 1 := by
        funext b a
        simp only [branchHalfLaw, Work.childLaw, Rat.cast_one]
      simp only [hq, groupedEntropy_const_one, zero_add, mul_zero, Finset.sum_const_zero]

theorem branchConditionalCost_eq_observed_oai (h : ActiveOrder K tick sigma)
    (side : Fin 3) (hside : side ≠ 0) :
    branchConditionalCost h.val.val.1 side =
      observedEntropy h side - workCapacity h.val.val.1 side := by
  rw [branchConditionalCost_eq _ side hside]
  unfold observedEntropy
  by_cases hs : h.val.val.1.stage ≠ 2
  · rw [ite_eq_left hs, ite_eq_left hs]
  · rw [ite_eq_right hs, ite_eq_right hs]
    have hc : workCapacity h.val.val.1 side = finiteEntropy
        (JointPopulationRates.sideMass (orderLaw h).mass (sigma side)) := by
      rcases h with ⟨⟨⟨w, phi⟩, ht⟩, ho⟩
      cases w with
      | stageA a => exact False.elim (hs (by change (0 : Fin 3) ≠ 2; decide))
      | stageB a => exact False.elim (hs (by change (1 : Fin 3) ≠ 2; decide))
      | stageC a =>
          have hh := AllFieldActiveCapacity.workCapacity_stageC_physical a phi side
          simpa only [ho, orderLaw] using hh
    rw [hc, sub_self]

end MatrixMultiplication.AllFieldGroupProjectedEntropy

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.branchConditionalCost_eq_observed_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.branchConditionalCost_eq_observed_oai
