-- Prove2me | solution 1 for OAI.RandomKSAT.deletion_difference_le_rewards
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:35:16.755879+00:00
-- url     : https://prove2.me/submissions/3a32cefb-69bf-4cd4-855f-6453f303fe1e

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/OmissionCompression.lean:L120-L161
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.deletion_difference_le_rewards. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression

-- ---- from OAI.Probability.SATVariance.RootDisintegration ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma satisfies_iff_read {n k : ℕ} (c : Clause n k) (a : Assignment n) :
    Satisfies c a ↔ ∃ v, clauseRead c v = some (a v) := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v, by simp [clauseRead, v.property, hv]⟩
  · rintro ⟨v,hv⟩
    unfold clauseRead at hv
    split_ifs at hv with h
    exact ⟨⟨v,h⟩, (Option.some.inj hv).symm⟩

lemma satisfies_merge {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (t : RootType k) (c : Clause u (k-rootSize t)) (a : Assignment n) :
    Satisfies (mergeClause e t c) a ↔
      RootSatisfies t (fun j => a (e (Sum.inl j))) ∨
      Satisfies c (fun j => a (e (Sum.inr j))) := by
  rw [satisfies_iff_read, satisfies_iff_read]
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨z,rfl⟩ := e.surjective v
    cases z with
    | inl j => exact Or.inl ⟨j, by simpa only [read_merge_inl] using hv⟩
    | inr j => exact Or.inr ⟨j, by simpa only [read_merge_inr] using hv⟩
  · rintro (⟨j,hj⟩ | ⟨j,hj⟩)
    · exact ⟨e (Sum.inl j), by simpa only [read_merge_inl] using hj⟩
    · exact ⟨e (Sum.inr j), by simpa only [read_merge_inr] using hj⟩

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.PairEvolution ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma forcedReward_nonneg {u k : ℕ} (a : Assignment k) (S : PairState u k) :
    0 ≤ forcedReward a S := by unfold forcedReward; split <;> norm_num

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.OmissionCompression ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma joinedAssignment_inl {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (x : Assignment k × Assignment u) (j : Fin k) :
    joinedAssignment e x (e (Sum.inl j)) = x.1 j := by simp [joinedAssignment]

lemma joinedAssignment_inr {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (x : Assignment k × Assignment u) (j : Fin u) :
    joinedAssignment e x (e (Sum.inr j)) = x.2 j := by simp [joinedAssignment]

lemma joinedAssignment_surjective {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) :
    Function.Surjective (joinedAssignment e) := by
  intro b
  refine ⟨⟨fun j => b (e (Sum.inl j)), fun j => b (e (Sum.inr j))⟩, ?_⟩
  funext v
  obtain ⟨z,rfl⟩ := e.surjective v
  cases z <;> simp [joinedAssignment]

lemma satisfies_joined_merge {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (p : RootData u k) (x : Assignment k × Assignment u) :
    Satisfies (mergeClause e p.1 p.2) (joinedAssignment e x) ↔ DataSatisfies p x := by
  simpa only [joinedAssignment_inl, joinedAssignment_inr, DataSatisfies] using
    satisfies_merge e p.1 p.2 (joinedAssignment e x)

lemma succAbove_lt_succ_iff {M : ℕ} (i : Fin (M+1)) (l j : Fin M) (hi : i.val ≤ l.val) :
    (i.succAbove j).val < l.val+1 ↔ j.val < l.val := by
  by_cases hj : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt _ _ hj]
    have hji : j.val < i.val := hj
    simp only [Fin.val_castSucc]
    omega
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hj)]
    simp only [Fin.val_succ, Nat.succ_lt_succ_iff]

lemma finiteSAT_omittedSAT {n k L m : ℕ} {i : Fin L} {cs : Fin L → Clause n k}
    (h : finiteSAT cs m) : omittedSAT i cs m := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a,fun j hj _ => ha j hj⟩

lemma omittedSAT_before {n k L m : ℕ} {i : Fin L} {cs : Fin L → Clause n k}
    (hm : m ≤ i.val) : omittedSAT i cs m ↔ finiteSAT cs m := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,fun j hj => ha j hj ?_⟩
    intro hji
    subst j
    omega
  · exact finiteSAT_omittedSAT

lemma omittedSAT_compressed {n k u M : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (i : Fin (M+1)) (c : Clause n k) (ps : Fin M → RootData u k)
    (l : Fin M) (hi : i.val ≤ l.val) :
    omittedSAT i (i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)) (l.val+1) ↔
      (pairPrefix Finset.univ ps l.val).Nonempty := by
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨x,rfl⟩ := joinedAssignment_surjective e b
    refine ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => ?_⟩⟩
    have hh := hb (i.succAbove j) ((succAbove_lt_succ_iff i l j hi).mpr hj) (Fin.succAbove_ne i j)
    simpa only [Fin.insertNth_apply_succAbove, satisfies_joined_merge] using hh
  · rintro ⟨x,hx⟩
    refine ⟨joinedAssignment e x,fun j hj hji => ?_⟩
    obtain ⟨t,rfl⟩ := Fin.exists_succAbove_eq hji
    rw [Fin.insertNth_apply_succAbove, satisfies_joined_merge]
    exact (Finset.mem_filter.mp hx).2 t ((succAbove_lt_succ_iff i l t hi).mp hj)

lemma fullSAT_compressed {n k u M : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (i : Fin (M+1)) (c : Clause n k) (ps : Fin M → RootData u k)
    (l : Fin M) (hi : i.val ≤ l.val) :
    finiteSAT (i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)) (l.val+1) ↔
      ∃ x ∈ pairPrefix Finset.univ ps l.val, Satisfies c (joinedAssignment e x) := by
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨x,rfl⟩ := joinedAssignment_surjective e b
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => ?_⟩, ?_⟩
    · have hh := hb (i.succAbove j) ((succAbove_lt_succ_iff i l j hi).mpr hj)
      simpa only [Fin.insertNth_apply_succAbove, satisfies_joined_merge] using hh
    · simpa only [Fin.insertNth_apply_same] using hb i (by omega)
  · rintro ⟨x,hx,hc⟩
    refine ⟨joinedAssignment e x,fun j hj => ?_⟩
    by_cases hji : j = i
    · subst j
      simpa only [Fin.insertNth_apply_same] using hc
    · obtain ⟨t,rfl⟩ := Fin.exists_succAbove_eq hji
      rw [Fin.insertNth_apply_succAbove, satisfies_joined_merge]
      exact (Finset.mem_filter.mp hx).2 t ((succAbove_lt_succ_iff i l t hi).mp hj)

lemma deletion_difference_le_rewards {n k u M : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (i : Fin (M+1)) (c : Clause n k) (a : Assignment k)
    (hc : ∀ x, ¬Satisfies c (joinedAssignment e x) ↔ x.1 = a)
    (ps : Fin M → RootData u k) :
    omittedTime i (i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)) -
      finiteTime (i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)) ≤
      dataRewards (forcedReward a) Finset.univ ps := by
  let cs : Fin (M+1) → Clause n k := i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)
  change omittedTime i cs-finiteTime cs ≤ _
  unfold omittedTime finiteTime dataRewards
  rw [← Finset.sum_sub_distrib, Fin.sum_univ_succ]
  have hzero : finiteSAT cs 0 := ⟨fun _ => false,fun _ hj => by omega⟩
  change ((if omittedSAT i cs 0 then (1 : ℝ) else 0)-(if finiteSAT cs 0 then 1 else 0)) +
    ∑ l : Fin M, ((if omittedSAT i cs (l.val+1) then 1 else 0)-(if finiteSAT cs (l.val+1) then 1 else 0)) ≤ _
  rw [ite_eq_left hzero, ite_eq_left (finiteSAT_omittedSAT (i := i) hzero), sub_self, zero_add]
  apply Finset.sum_le_sum
  intro l _
  change (if omittedSAT i cs (l.val+1) then (1 : ℝ) else 0) -
    (if finiteSAT cs (l.val+1) then 1 else 0) ≤ forcedReward a (pairPrefix Finset.univ ps l.val)
  by_cases hi : i.val ≤ l.val
  · by_cases hs : finiteSAT cs (l.val+1)
    · simp only [ite_eq_left hs, ite_eq_left (finiteSAT_omittedSAT (i := i) hs), sub_self]
      exact forcedReward_nonneg _ _
    by_cases ho : omittedSAT i cs (l.val+1)
    · have hp := (omittedSAT_compressed e i c ps l hi).mp ho
      have hf : ∀ x ∈ pairPrefix Finset.univ ps l.val, x.1 = a := by
        intro x hx
        apply (hc x).mp
        intro hsat
        exact hs ((fullSAT_compressed e i c ps l hi).mpr ⟨x,hx,hsat⟩)
      have hforce : (pairPrefix Finset.univ ps l.val).Nonempty ∧
          ∀ x ∈ pairPrefix Finset.univ ps l.val, x.1 = a := ⟨hp,hf⟩
      simp only [ite_eq_left ho, ite_eq_right hs, sub_zero, forcedReward, ite_eq_left hforce, le_refl]
    · simp only [ite_eq_right hs, ite_eq_right ho, sub_self]
      exact forcedReward_nonneg _ _
  · have he := omittedSAT_before (cs := cs) (i := i) (by omega : l.val+1 ≤ i.val)
    by_cases hs : finiteSAT cs (l.val+1)
    · simp only [ite_eq_left hs, ite_eq_left (he.mpr hs), sub_self]
      exact forcedReward_nonneg _ _
    · have ho : ¬omittedSAT i cs (l.val+1) := fun h => hs (he.mp h)
      simp only [ite_eq_right hs, ite_eq_right ho, sub_self]
      exact forcedReward_nonneg _ _

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.deletion_difference_le_rewards := @_root_.OAI.RandomKSAT.deletion_difference_le_rewards
