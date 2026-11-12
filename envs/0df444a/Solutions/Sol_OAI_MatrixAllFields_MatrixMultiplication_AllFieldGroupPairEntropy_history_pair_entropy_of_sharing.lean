-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairEntropy.history_pair_entropy_of_sharing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:24:42.518322+00:00
-- url     : https://prove2.me/submissions/518bea50-d3e5-44b0-b82d-7a56bb707a89

import Mathlib
import Definitions.Def_OAIQ254M007

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

theorem finiteEntropy_chain {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : A → B → ℝ) (hq : ∀ a, ∑ b, q a b = 1) :
    finiteEntropy (fun ab : A × B => p ab.1 * q ab.1 ab.2) =
      finiteEntropy p + ∑ a, p a * finiteEntropy (q a) := by
  simp only [finiteEntropy, Fintype.sum_prod_type, entropyTerm_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq, one_mul]

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

theorem map_mass_apply (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) (a : A) : (p.map f).mass (f a) = p.mass a := by
  classical
  simp [map_mass, hf.eq_iff]

theorem map_entropy_of_injective (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) : finiteEntropy (p.map f).mass = finiteEntropy p.mass := by
  classical
  have hterm (b : B) : entropyTerm ((p.map f).mass b) =
      ∑ a, if f a = b then entropyTerm (p.mass a) else 0 := by
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [map_mass_apply p f hf]
      simp [hf.eq_iff]
    · simp [map_mass, not_exists.mp hb]
  unfold finiteEntropy
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp

theorem joint_entropy (p : FiniteLaw A) (q : A → FiniteLaw B) :
    finiteEntropy (p.joint q).mass =
      finiteEntropy p.mass + ∑ a, p.mass a * finiteEntropy (q a).mass :=
  finiteEntropy_chain p.mass (fun a => (q a).mass) (fun a => (q a).total)

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

theorem entropy_eq_map_add_conditional (p : FiniteLaw A) (f : A → B) :
    finiteEntropy p.mass = finiteEntropy (p.map f).mass +
      ∑ b, (p.map f).mass b * finiteEntropy (p.conditional f b).mass := by
  classical
  let graph : A → B × A := fun a => (f a, a)
  have hinj : Function.Injective graph := fun _ _ h => congrArg Prod.snd h
  have hmass : ((p.map f).joint (p.conditional f)).mass = (p.map graph).mass := by
    funext ba
    rcases ba with ⟨b, a⟩
    change (p.map f).mass b * (p.conditional f b).mass a = (p.map graph).mass (b, a)
    rw [map_mass_mul_conditional, map_mass, Finset.sum_eq_single a]
    · simp only [graph, Prod.mk.injEq, and_true]
    · intro x _ hxa
      simp only [graph, Prod.mk.injEq, hxa, and_false, ite_false, if_false]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  calc
    finiteEntropy p.mass = finiteEntropy (p.map graph).mass :=
      (p.map_entropy_of_injective graph hinj).symm
    _ = finiteEntropy ((p.map f).joint (p.conditional f)).mass := by rw [hmass]
    _ = _ := (p.map f).joint_entropy (p.conditional f)

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.JointEntropyMax

theorem sum_mass_mul_coordinate {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (f : A → B) (v : B → ℝ) :
    (∑ a, p.mass a * v (f a)) = ∑ b, (p.map f).mass b * v b := by
  classical
  simp_rw [FiniteLaw.map_mass, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

end MatrixMultiplication.JointEntropyMax

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryChildLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
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

end MatrixMultiplication.AllFieldHistory

end
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

theorem indexedMarginalLaw_mass (support : List Shape) (p : Shape → ℚ)
    (hpos : ∀ u ∈ support, 0 ≤ p u) (htotal : (support.map p).sum = 1)
    (side : Fin 3) (hbound : ∀ u ∈ support, u side < 17) (k : Fin 17) :
    (indexedMarginalLaw support p hpos htotal side hbound).mass k =
      marginal support (fun u => (p u : ℝ)) side k := by
  simp only [indexedMarginalLaw, FiniteLaw.map_mass, RationalLaw.toFiniteLaw_mass,
    indexedRationalLaw, Fin.ext_iff, marginal, List.get_eq_getElem]
  exact Fin.sum_univ_fun_getElem support (fun u : Shape => if u side = k.val then (p u : ℝ) else 0)

end MatrixMultiplication.AllFieldNativeCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_PairMarginals
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldPairMarginals

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldNativeCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem statistic_weight_mass {A : Type*} [Fintype A]
    (q : A → ℝ) (weight : A → Fin 17) (own : ℕ)
    (hq : ∀ a, 0 ≤ q a) (htotal : ∑ a, q a = 1)
    (hweight : ∀ a, 0 < q a → (weight a).val = own) (k : Fin 17) :
    (∑ a, if weight a = k then q a else 0) = if own = k.val then 1 else 0 := by
  have hterm (a : A) : (if weight a = k then q a else 0) =
      if own = k.val then q a else 0 := by
    by_cases ha : q a = 0
    · simp only [ha, ite_self]
    · have hw := hweight a (lt_of_le_of_ne (hq a) (Ne.symm ha))
      have he : weight a = k ↔ own = k.val := by rw [Fin.ext_iff, hw]
      simp only [he]
  simp_rw [hterm]
  split_ifs <;> simp_all

theorem pairLaw_leftWeight_mass {A : Type*} [Fintype A]
    (support : List Shape) (s : Shape) (p : Shape → ℝ) (q : Shape → A → ℝ)
    (side : Fin 3) (weight : A → Fin 17)
    (hq : ∀ u ∈ support, ∀ a, 0 ≤ q u a)
    (hleft : ∀ u ∈ support, ∑ a, q u a = 1)
    (hright : ∀ u ∈ support, ∑ a, q (complement s u) a = 1)
    (hweight : ∀ u ∈ support, ∀ a, 0 < q u a → (weight a).val = u side)
    (k : Fin 17) :
    (∑ ij : A × A, if weight ij.1 = k then pairLaw support s p q ij else 0) =
      marginal support p side k := by
  unfold pairLaw marginal
  induction support with
  | nil => simp
  | cons u us ih =>
      have hu : u ∈ u :: us := by simp
      have hw := statistic_weight_mass (q u) weight (u side)
        (hq u hu) (hleft u hu) (hweight u hu) k
      have hr := hright u hu
      have head : (∑ ij : A × A, if weight ij.1 = k then
          p u * q u ij.1 * q (complement s u) ij.2 else 0) =
            if u side = k.val then p u else 0 := by
        rw [Fintype.sum_prod_type]
        calc
          _ = ∑ a, if weight a = k then p u * q u a else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases ha : weight a = k
            · simp only [ha, ite_true, if_true, ← Finset.mul_sum, hr, mul_one]
            · simp [ha]
          _ = p u * (∑ a, if weight a = k then q u a else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            split_ifs <;> simp
          _ = _ := by rw [hw]; split_ifs <;> simp
      have tail := ih (fun v hv => hq v (by simp [hv]))
        (fun v hv => hleft v (by simp [hv]))
        (fun v hv => hright v (by simp [hv]))
        (fun v hv => hweight v (by simp [hv]))
      simpa only [List.map_cons, List.sum_cons, ite_add_zero, Finset.sum_add_distrib,
        head] using congrArg (fun r : ℝ => (if u side = k.val then p u else 0) + r) tail

theorem littleLaw_positive_weight (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) (side : Fin 3) (a : Fin 6)
    (ha : 0 < (littleLaw t u side a : ℝ)) : (statisticWeightCode a).val = u side := by
  change statisticWeight a = u side
  by_contra hne
  have hz := littleLaw_outside_support t u side
    (child_statistic_weight_bounded t ht u hu side) a hne
  have hz' : (littleLaw t u side a : ℝ) = 0 := by exact_mod_cast hz
  linarith

theorem halfLaw_positive_weight (u : Shape) (hu : u ∈ shapes 8)
    (side : Fin 3) (a : PairSlot) (ha : 0 < (halfLaw u side a : ℝ)) :
    (halfWeightCode a).val = u side := by
  change statisticWeight a.1 + statisticWeight a.2 = u side
  by_contra hne
  have hz := halfLaw_outside_support u hu side a hne
  have hz' : (halfLaw u side a : ℝ) = 0 := by exact_mod_cast hz
  linarith

theorem stageBPairLaw_leftWeight_mass (t : Shape) (ht : t ∈ positiveSecond)
    (side : Fin 3) (k : Fin 17) :
    ((stageBPairLaw t ht side).map (fun ij => statisticWeightCode ij.1)).mass k =
      (stageBMarginalLaw t ht side).mass k := by
  rw [FiniteLaw.map_mass]
  change (∑ ij : Fin 6 × Fin 6, if statisticWeightCode ij.1 = k then
    pairLaw (below t) t (fun u => (stageBLaw t u : ℝ))
      (fun u a => (littleLaw t u side a : ℝ)) ij else 0) = _
  rw [pairLaw_leftWeight_mass (below t) t (fun u => (stageBLaw t u : ℝ))
    (fun u a => (littleLaw t u side a : ℝ)) side statisticWeightCode
    (fun u _ a => Rat.cast_nonneg.mpr (littleLaw_nonnegative t u side a))
    (fun u _ => (littleFiniteLaw t u side).total)
    (fun u _ => (littleFiniteLaw t (complement t u) side).total)
    (fun u hu a => littleLaw_positive_weight t ht u hu side a)]
  exact (indexedMarginalLaw_mass _ _ _ _ _ _ k).symm

theorem stageAPairLaw_leftWeight_mass (g : Shape) (hg : g ∈ positiveInitial)
    (side : Fin 3) (k : Fin 17) :
    ((stageAPairLaw g hg side).map (fun ij => halfWeightCode ij.1)).mass k =
      (stageAMarginalLaw g hg side).mass k := by
  rw [FiniteLaw.map_mass]
  change (∑ ij : PairSlot × PairSlot, if halfWeightCode ij.1 = k then
    pairLaw (below g) g (fun u => (stageALaw g u : ℝ))
      (fun u a => (halfLaw u side a : ℝ)) ij else 0) = _
  rw [pairLaw_leftWeight_mass (below g) g (fun u => (stageALaw g u : ℝ))
    (fun u a => (halfLaw u side a : ℝ)) side halfWeightCode
    (fun u _ a => Rat.cast_nonneg.mpr (halfLaw_nonnegative u side a))
    (fun u hu => (halfFiniteLaw u (stageA_children_size g hg u hu) side).total)
    (fun u hu => (halfFiniteLaw (complement g u)
      (stageA_children_size g hg _ (stageA_support_complement g hg u hu).1) side).total)
    (fun u hu a => halfLaw_positive_weight u (stageA_children_size g hg u hu) side a)]
  exact (indexedMarginalLaw_mass _ _ _ _ _ _ k).symm

private theorem law_ext {A : Type*} [Fintype A] (p q : FiniteLaw A)
    (h : ∀ a, p.mass a = q.mass a) : p = q := by
  cases p with
  | mk p hp htotal =>
      cases q with
      | mk q hq hqtotal =>
          have heq : p = q := funext h
          subst q
          rfl

theorem stageBPairLaw_leftWeight_marginal (t : Shape) (ht : t ∈ positiveSecond)
    (side : Fin 3) :
    (stageBPairLaw t ht side).map (fun ij => statisticWeightCode ij.1) =
      stageBMarginalLaw t ht side :=
  law_ext _ _ (stageBPairLaw_leftWeight_mass t ht side)

theorem stageAPairLaw_leftWeight_marginal (g : Shape) (hg : g ∈ positiveInitial)
    (side : Fin 3) :
    (stageAPairLaw g hg side).map (fun ij => halfWeightCode ij.1) =
      stageAMarginalLaw g hg side :=
  law_ext _ _ (stageAPairLaw_leftWeight_mass g hg side)

end MatrixMultiplication.AllFieldPairMarginals

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

theorem placedLaw_sideMass {K : ℕ} (w : PlacedWork K) (s : Fin 3)
    (k : Fin 17) :
    JointPopulationRates.sideMass (placedLaw w).mass s k =
      ∑ b : w.1.Branch, if JointPopulation.shapeSide s (branchShape w b) = k
        then (branchProbability w.1 b : ℝ) else 0 := by
  unfold JointPopulationRates.sideMass
  simp only [placedLaw_mass]
  calc
    _ = ∑ u : JointPopulation.Shape, ∑ b : w.1.Branch,
        if branchShape w b = u then
          if JointPopulation.shapeSide s u = k then (branchProbability w.1 b : ℝ) else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : JointPopulation.shapeSide s u = k <;> simp [hu]
    _ = _ := by rw [Finset.sum_comm]; simp

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

theorem jointCounts_ratio {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) /
      population allocation dilation (w.1.source, w.2) = (placedLaw w).mass u := by
  rw [jointCounts_cast]
  have hp : (population allocation dilation (w.1.source, w.2) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (work_source_population_pos allocation hd w)
  exact mul_div_cancel_left₀ _ hp

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

theorem placedLaw_sum_mul {K : ℕ} (w : PlacedWork K)
    (f : JointPopulation.Shape → ℝ) :
    (∑ u, (placedLaw w).mass u * f u) =
      ∑ b : w.1.Branch, (branchLaw w.1).mass b * f (branchShape w b) := by
  exact (JointEntropyMax.sum_mass_mul_coordinate
    (branchLaw w.1) (branchShape w) f).symm

theorem childLaw_branchShape {K : ℕ} (w : PlacedWork K)
    (b : w.1.Branch) (side : Fin 3) (a : w.1.Statistic) :
    childLaw w (branchShape w b) side a =
      (w.1.childLaw (w.1.splitShape b) (w.2.symm side) a : ℝ) := by
  change (w.1.childLaw (canonicalChildShape w (branchShape w b))
    (w.2.symm side) a : ℝ) = _
  rw [canonicalChildShape_branchShape]

theorem rightChildLaw_branchShape {K : ℕ} (w : PlacedWork K)
    (b : w.1.Branch) (side : Fin 3) (a : w.1.Statistic) :
    rightChildLaw w (branchShape w b) side a =
      (w.1.childLaw (AllFieldParameters.complement w.1.parentShape (w.1.splitShape b))
        (w.2.symm side) a : ℝ) := by
  change (w.1.childLaw
    (AllFieldParameters.complement w.1.parentShape (canonicalChildShape w (branchShape w b)))
    (w.2.symm side) a : ℝ) = _
  rw [canonicalChildShape_branchShape]

theorem branchPairMixture_eq_native {K : ℕ} (w : Work K) (side : Fin 3)
    (a : w.Statistic × w.Statistic) :
    (∑ b : w.Branch, (branchLaw w).mass b *
      (w.childLaw (w.splitShape b) side a.1 : ℝ) *
      (w.childLaw (AllFieldParameters.complement w.parentShape (w.splitShape b)) side a.2 : ℝ)) =
      (nativePairLaw w side).mass a := by
  cases w with
  | stageA h =>
      change (∑ b : Fin (below (initialShape h.val)).length,
        (stageALaw (initialShape h.val) (below (initialShape h.val))[b.val] : ℝ) *
          (halfLaw (below (initialShape h.val))[b.val] side a.1 : ℝ) *
          (halfLaw (AllFieldParameters.complement (initialShape h.val)
            (below (initialShape h.val))[b.val]) side a.2 : ℝ)) = _
      exact Fin.sum_univ_fun_getElem _ (fun u : Shape =>
        (stageALaw (initialShape h.val) u : ℝ) * (halfLaw u side a.1 : ℝ) *
          (halfLaw (AllFieldParameters.complement (initialShape h.val) u) side a.2 : ℝ))
  | stageB h =>
      change (∑ b : Fin (below (aShape h.val)).length,
        (stageBLaw (aShape h.val) (below (aShape h.val))[b.val] : ℝ) *
          (littleLaw (aShape h.val) (below (aShape h.val))[b.val] side a.1 : ℝ) *
          (littleLaw (aShape h.val) (AllFieldParameters.complement (aShape h.val)
            (below (aShape h.val))[b.val]) side a.2 : ℝ)) = _
      exact Fin.sum_univ_fun_getElem _ (fun u : Shape =>
        (stageBLaw (aShape h.val) u : ℝ) *
          (littleLaw (aShape h.val) u side a.1 : ℝ) *
          (littleLaw (aShape h.val) (AllFieldParameters.complement (aShape h.val) u) side a.2 : ℝ))
  | stageC h =>
      simpa only [Work.childLaw, Rat.cast_one, mul_one, nativePairLaw] using
        (branchLaw (Work.stageC h)).total

theorem placedPairMixture_eq_native {K : ℕ} (w : PlacedWork K) (side : Fin 3)
    (a : w.1.Statistic × w.1.Statistic) :
    placedPairMixture w side a = (nativePairLaw w.1 (w.2.symm side)).mass a := by
  simp only [placedPairMixture, mul_assoc]
  rw [placedLaw_sum_mul]
  simpa only [childLaw_branchShape, rightChildLaw_branchShape, mul_assoc] using
    branchPairMixture_eq_native w.1 (w.2.symm side) a

theorem placement_symm_order_side {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) :
    h.val.val.2.symm (sigma side) = h.val.val.1.priority side := by
  have hs : h.val.val.2 (h.val.val.1.priority side) = sigma side :=
    Equiv.congr_fun h.property side
  rw [← hs, Equiv.symm_apply_apply]

theorem orderPairMixture_eq_native {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3)
    (a : Statistic h.val × Statistic h.val) :
    orderPairMixture h side a =
      (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass a := by
  change placedPairMixture h.val.val (sigma side) a = _
  rw [placedPairMixture_eq_native, placement_symm_order_side]

end MatrixMultiplication.AllFieldGroupNativeLaws






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_GroupPairWindows
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
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

theorem parentBase_pos (allocation : Allocation) (h : ActiveOrder K tick sigma) :
    0 < parentBase (K := K) (tick := tick) allocation h :=
  AllFieldHistorySupport.work_source_population_pos allocation (by decide : 0 < (1 : ℕ)) h.val.val

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

theorem parentPair_eq_native (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (h : ActiveOrder K tick sigma)
    (a : Statistic h.val × Statistic h.val) :
    parentPair (K := K) (tick := tick) allocation sigma side h a = orderPairMixture h side a := by
  rw [parentPair_eq_parentCenter]
  unfold parentCenter orderPairMixture
  apply Finset.sum_congr rfl
  intro u _
  rw [show (activeCounts allocation 1 h.val u : ℝ) /
      population allocation 1 (h.val.val.1.source, h.val.val.2) =
      (AllFieldActiveLaws.orderLaw h).mass u from
    AllFieldActiveLaws.jointCounts_ratio allocation (by decide : 0 < (1 : ℕ)) h.val.val u]
  ring

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

end MatrixMultiplication.AllFieldGroupPairWindows

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_GroupSelectionParameters
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldActiveCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldNativeCapacity AllFieldActiveLaws AllFieldScheduledYield
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem placedLaw_priority_sideMass {K : ℕ} (w : PlacedWork K)
    (i : Fin 3) :
    JointPopulationRates.sideMass (placedLaw w).mass (w.physicalOrder i) =
      canonicalSideMass w.1 (w.1.priority i) := by
  funext k
  rw [placedLaw_sideMass]
  simp only [Fin.ext_iff, branchShape, encodePhysicalShape_side,
    PlacedWork.physicalOrder, Equiv.trans_apply, Equiv.symm_apply_apply,
    canonicalSideMass, branchLaw_mass]

theorem canonicalSideMass_stageA {K : ℕ} (h : InitialPositive K) (s : Fin 3) :
    canonicalSideMass (.stageA h) s =
      (stageAMarginalLaw (initialShape h.val) h.property s).mass := by
  funext k
  rw [show (stageAMarginalLaw (initialShape h.val) h.property s).mass k =
      marginal (below (initialShape h.val))
        (fun u => (stageALaw (initialShape h.val) u : ℝ)) s k from
    indexedMarginalLaw_mass _ _ _ _ _ _ k]
  change (∑ b : ASplit h, if (below (initialShape h.val))[b.val] s = k.val
      then (stageALaw (initialShape h.val) (below (initialShape h.val))[b.val] : ℝ)
      else 0) = _
  exact Fin.sum_univ_fun_getElem _
    (fun u : Shape => if u s = k.val then (stageALaw (initialShape h.val) u : ℝ) else 0)

theorem canonicalSideMass_stageB {K : ℕ} (h : APositive K) (s : Fin 3) :
    canonicalSideMass (.stageB h) s =
      (stageBMarginalLaw (aShape h.val) h.property s).mass := by
  funext k
  rw [show (stageBMarginalLaw (aShape h.val) h.property s).mass k =
      marginal (below (aShape h.val))
        (fun u => (stageBLaw (aShape h.val) u : ℝ)) s k from
    indexedMarginalLaw_mass _ _ _ _ _ _ k]
  change (∑ b : BSplit h, if (below (aShape h.val))[b.val] s = k.val
      then (stageBLaw (aShape h.val) (below (aShape h.val))[b.val] : ℝ)
      else 0) = _
  exact Fin.sum_univ_fun_getElem _
    (fun u : Shape => if u s = k.val then (stageBLaw (aShape h.val) u : ℝ) else 0)

end MatrixMultiplication.AllFieldActiveCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupPairEntropy
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

namespace MatrixMultiplication.AllFieldGroupPairEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldHistoryChildLaws AllFieldGroupOrbitData
open AllFieldGroupDegrees AllFieldGroupNativeLaws AllFieldGroupPairWindows
open JointCompatibilityScaling JointCompatibilityRateLimit JointPairClassWindows
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sum_conditionalCenter_entropy {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (p : FiniteLaw A) (f : A → B) :
    (∑ b, (p.map f).mass b * finiteEntropy
      (conditionalCenter f b p.mass ((p.map f).mass b))) =
        finiteEntropy p.mass - finiteEntropy (p.map f).mass := by
  have ht (b : B) :
      (p.map f).mass b * finiteEntropy
        (conditionalCenter f b p.mass ((p.map f).mass b)) =
      (p.map f).mass b * finiteEntropy (p.conditional f b).mass := by
    by_cases hz : (p.map f).mass b = 0
    · simp only [hz, zero_mul]
    · congr 1
      congr 1
      funext a
      simp only [conditionalCenter, FiniteLaw.conditional, dite_eq_right hz]
      split_ifs <;> simp
  simp_rw [ht]
  have he := p.entropy_eq_map_add_conditional f
  linarith

variable {K tick : ℕ} {sigma : Placement}

theorem baseSize_eq_parentBase_mul_sideMass (allocation : Allocation)
    (sigma : Placement) (side : Fin 3) (h : ActiveOrder K tick sigma) (k : Fin 17) :
    (baseSize (base allocation sigma side) (h, k) : ℝ) =
      (parentBase allocation h : ℝ) *
        JointPopulationRates.sideMass (orderLaw h).mass (sigma side) k := by
  simp only [baseSize, base, JointPopulationCompatibility.classCounts,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, JointPopulationRates.sideMass,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : JointPopulation.shapeSide (sigma side) u = k
  · simp only [hu, ite_true, if_true]
    exact jointCounts_cast allocation 1 h.val.val u
  · simp only [hu, ite_false, if_false, mul_zero]

theorem classMass_eq_sideMass (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (c : Class (K := K) (tick := tick) sigma) :
    classMass allocation sigma side c =
      JointPopulationRates.sideMass (orderLaw c.1).mass (sigma side) c.2 := by
  rcases c with ⟨h, k⟩
  unfold classMass
  rw [baseSize_eq_parentBase_mul_sideMass]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (parentBase_pos allocation h).ne')

theorem nativePair_weight_marginal {K : ℕ} (w : Work K) (side : Fin 3)
    (hs : w.stage ≠ 2) :
    ((nativePairLaw w side).map (fun a => weightCode w a.1)).mass =
      canonicalSideMass w side := by
  cases w with
  | stageA h =>
      rw [canonicalSideMass_stageA]
      exact congrArg FiniteLaw.mass
        (AllFieldPairMarginals.stageAPairLaw_leftWeight_marginal _ h.property side)
  | stageB h =>
      rw [canonicalSideMass_stageB]
      exact congrArg FiniteLaw.mass
        (AllFieldPairMarginals.stageBPairLaw_leftWeight_marginal _ h.property side)
  | stageC h => exact False.elim (hs rfl)

theorem orderPair_weight_marginal (h : ActiveOrder K tick sigma) (side : Fin 3)
    (hs : h.val.val.1.stage ≠ 2) :
    ((nativePairLaw h.val.val.1 (h.val.val.1.priority side)).map
      (fun a => weightCode h.val.val.1 a.1)).mass =
      JointPopulationRates.sideMass (orderLaw h).mass (sigma side) := by
  rw [nativePair_weight_marginal _ _ hs]
  have hm := placedLaw_priority_sideMass h.val.val side
  rw [h.property] at hm
  exact hm.symm

theorem q_eq_native_conditionalCenter (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (c : Class (K := K) (tick := tick) sigma)
    (hs : c.1.val.val.1.stage ≠ 2) :
    q allocation sigma side c = conditionalCenter
      (fun a => weightCode c.1.val.val.1 a.1) c.2
      (nativePairLaw c.1.val.val.1 (c.1.val.val.1.priority side)).mass
      (((nativePairLaw c.1.val.val.1 (c.1.val.val.1.priority side)).map
        (fun a => weightCode c.1.val.val.1 a.1)).mass c.2) := by
  rw [q_eq_conditionalCenter allocation sigma side c hs, classMass_eq_sideMass,
    orderPair_weight_marginal _ _ hs]
  have hp : parentPair allocation sigma side c.1 =
      (nativePairLaw c.1.val.val.1 (c.1.val.val.1.priority side)).mass := by
    funext a
    rw [parentPair_eq_native, orderPairMixture_eq_native]
  rw [hp]

theorem history_pair_entropy_of_sharing_oai (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (h : ActiveOrder K tick sigma) (hs : h.val.val.1.stage ≠ 2) :
    (∑ k : Fin 17, (baseSize (base allocation sigma side) (h, k) : ℝ) *
      finiteEntropy (q allocation sigma side (h, k))) =
      (parentBase allocation h : ℝ) *
        (finiteEntropy (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass -
          finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma side))) := by
  have hq (k : Fin 17) := q_eq_native_conditionalCenter allocation sigma side (h, k) hs
  simp_rw [baseSize_eq_parentBase_mul_sideMass, hq, mul_assoc]
  rw [← Finset.mul_sum]
  simpa only [orderPair_weight_marginal h side hs] using
    congrArg (fun x : ℝ => (parentBase allocation h : ℝ) * x)
      (sum_conditionalCenter_entropy
        (nativePairLaw h.val.val.1 (h.val.val.1.priority side))
        (fun a => weightCode h.val.val.1 a.1))

end MatrixMultiplication.AllFieldGroupPairEntropy

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairEntropy.history_pair_entropy_of_sharing_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairEntropy.history_pair_entropy_of_sharing_oai
