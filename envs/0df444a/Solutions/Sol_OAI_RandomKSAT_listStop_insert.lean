-- Prove2me | solution 1 for OAI.RandomKSAT.listStop_insert
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:50:16.637195+00:00
-- url     : https://prove2.me/submissions/fcd7e960-556b-42f2-a409-5da53016e9f3

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/BystanderStops.lean:L121-L143
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.listStop_insert. The node keeps its source
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
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
import Definitions.Def_OAI_Probability_SATVariance_BystanderStops
import Theorems.Thm_OAI_RandomKSAT_lt_listStop_iff

-- ---- from OAI.Probability.SATVariance.BystanderStops ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma listSAT_perm {n k : ℕ} {l r : List (Clause n k)} (h : l.Perm r) :
    listSAT l ↔ listSAT r := by
  constructor <;> rintro ⟨a,ha⟩ <;> refine ⟨a,fun c hc => ?_⟩
  · exact ha c (h.mem_iff.mpr hc)
  · exact ha c (h.mem_iff.mp hc)

lemma listStop_le {n k : ℕ} (l : List (Clause n k)) : listStop l ≤ l.length+1 :=
  Nat.find_min' _ (Or.inl rfl)

lemma take_insertIdx_perm.{u_1} {α : Type u_1} (l : List α) (c : α) (i m : ℕ)
    (hi : i ≤ l.length) (him : i < m) :
    ((l.insertIdx i c).take m).Perm (c::l.take (m-1)) := by
  induction l generalizing i m with
  | nil =>
    have : i = 0 := by simpa using hi
    subst i
    cases m with
    | zero => omega
    | succ m => simp
  | cons a l ih =>
    cases i with
    | zero =>
      cases m with
      | zero => omega
      | succ m => simp
    | succ i =>
      cases m with
      | zero => omega
      | succ m =>
        have hi' : i ≤ l.length := by simpa using hi
        have him' : i < m := by omega
        have hh := (ih i m hi' him').cons a
        have hm : 0 < m := by omega
        cases m with
        | zero => omega
        | succ m =>
          simpa only [List.insertIdx_succ_cons, List.take_succ_cons, Nat.add_sub_cancel,
            Nat.succ_sub_one] using hh.trans (List.Perm.swap c a _)

lemma listSAT_insert_take {n k : ℕ} (c : Clause n k) (l : List (Clause n k))
    (hc : Harmless c l) (i m : ℕ) (hi : i ≤ l.length) :
    listSAT ((l.insertIdx i c).take m) ↔
      listSAT (l.take (m - if i < m then 1 else 0)) := by
  by_cases him : i < m
  · rw [ite_eq_left him, listSAT_perm (take_insertIdx_perm l c i m hi him)]
    exact hc _ (List.take_sublist _ _)
  · rw [ite_eq_right him, Nat.sub_zero, List.take_insertIdx_eq_take_of_le _ _ m i (by omega)]

lemma listStop_insert {n k : ℕ} (c : Clause n k) (l : List (Clause n k))
    (hc : Harmless c l) (i : ℕ) (hi : i ≤ l.length) :
    listStop (l.insertIdx i c) = listStop l + if i < listStop l then 1 else 0 := by
  apply eq_of_forall_lt_iff
  intro m
  have hl : (l.insertIdx i c).length = l.length+1 := List.length_insertIdx_of_le_length hi c
  rw [lt_listStop_iff, hl, listSAT_insert_take c l hc i m hi]
  have ht := listStop_le l
  by_cases hm : m ≤ l.length+1
  · simp only [hm, true_and]
    have hr : m - (if i < m then 1 else 0) ≤ l.length := by split_ifs <;> omega
    have he := lt_listStop_iff (m := m - (if i < m then 1 else 0)) l
    rw [and_iff_right hr] at he
    rw [← he]
    split_ifs <;> omega
  · simp only [hm, false_and]
    constructor
    · exact False.elim
    · intro h
      have hb : listStop l + (if i < listStop l then 1 else 0) ≤ l.length+2 := by
        have hx : (if i < listStop l then 1 else 0) ≤ (1 : ℕ) := by split_ifs <;> omega
        omega
      omega

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.listStop_insert := @_root_.OAI.RandomKSAT.listStop_insert
