-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.terminalLog_fiber_inter_initial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:23:12.925841+00:00
-- url     : https://prove2.me/submissions/bd928597-bdee-4bc9-817a-d0fd5ef15d8a

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/History.lean:L359-L378
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.terminalLog_fiber_inter_initial. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_run_eq_iff_mem

-- ---- from OAI.Probability.Localization.History ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma state_nil {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) :
    state P Q [] = ⟨Q,cellSet Q,false⟩ := rfl

lemma state_append {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) (a : Letter n) :
    state P Q (h++[a]) = update P (state P Q h) a := by
  simp only [state,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma state_event_subset_initial {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) :
    (state P Q h).event ⊆ cellSet Q := by
  induction h using List.reverseRecOn with
  | nil => exact Subset.rfl
  | append_singleton h a ih =>
    rw [state_append]
    unfold update
    split
    · exact ih
    · exact Set.inter_subset_left.trans ih

lemma run_length_of_active {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ)
    (z : Coordinate n) (ha : (state P Q (run P Q N z)).stopped = false) :
    (run P Q N z).length = N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hprev : (state P Q (run P Q N z)).stopped = false := by
      cases he : (state P Q (run P Q N z)).stopped
      · rfl
      · simp only [run,he,ite_true] at ha
        exact ha
    simp only [run,hprev,Bool.false_eq_true,ite_false,List.length_append,List.length_singleton]
    rw [ih hprev]

lemma run_succ_of_stopped {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ)
    (z : Coordinate n) (h : (state P Q (run P Q N z)).stopped = true) :
    run P Q (N+1) z = run P Q N z := by simp only [run,h,ite_true]

lemma run_add_of_stopped {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N M : ℕ)
    (z : Coordinate n) (h : (state P Q (run P Q N z)).stopped = true) :
    run P Q (N+M) z = run P Q N z := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.add_succ,run_succ_of_stopped P Q (N+M) z (by rw [ih]; exact h),ih]

lemma run_of_stopped_le {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {N M : ℕ}
    (z : Coordinate n) (hNM : N ≤ M) (h : (state P Q (run P Q N z)).stopped = true) :
    run P Q M z = run P Q N z := by
  obtain ⟨M,rfl⟩ := Nat.exists_eq_add_of_le hNM
  exact run_add_of_stopped P Q N M z h

lemma attempts_spec {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) : (state P Q (terminalLog P Q z)).stopped = true := by
  simpa only [terminalLog,attempts,dite_eq_left hz] using Nat.find_spec hz

lemma attempts_min {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) {N : ℕ} (hN : N < attempts P Q z) :
    (state P Q (run P Q N z)).stopped = false := by
  have hm : ¬ (state P Q (run P Q N z)).stopped = true := Nat.find_min hz (by
    simpa only [attempts,dite_eq_left hz] using hN)
  simpa using hm

lemma attempts_pos {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) : 0 < attempts P Q z := by
  by_contra h
  have he : attempts P Q z = 0 := by omega
  have hs := attempts_spec P Q hz
  simp [terminalLog,he,run,state_nil] at hs

lemma terminalLog_length {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) : (terminalLog P Q z).length = attempts P Q z := by
  obtain ⟨N,hN⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (attempts_pos P Q hz))
  have hn : (state P Q (run P Q N z)).stopped = false := attempts_min P Q hz (by omega)
  simp only [terminalLog,hN,run,hn,Bool.false_eq_true,ite_false,List.length_append,List.length_singleton]
  rw [run_length_of_active P Q N z hn]

lemma terminalLog_of_stopped {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    {N : ℕ} {z : Coordinate n} (h : (state P Q (run P Q N z)).stopped = true) :
    terminalLog P Q z = run P Q N z := by
  have ht : Terminates P Q z := ⟨N,h⟩
  have hle : attempts P Q z ≤ N := by
    simpa only [attempts,dite_eq_left ht] using Nat.find_min' ht h
  exact (run_of_stopped_le P Q z hle (attempts_spec P Q ht)).symm

lemma terminates_of_terminal_stopped {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hs : (state P Q (terminalLog P Q z)).stopped = true) : Terminates P Q z :=
  ⟨attempts P Q z,hs⟩

lemma terminalLog_fiber_inter_initial {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) (ht : Terminates P Q z) :
    cellSet Q ∩ {w | terminalLog P Q w = terminalLog P Q z} =
      (state P Q (terminalLog P Q z)).event := by
  ext w
  constructor
  · rintro ⟨hw,he⟩
    change terminalLog P Q w = terminalLog P Q z at he
    have htw : Terminates P Q w := terminates_of_terminal_stopped P Q (by rw [he]; exact attempts_spec P Q ht)
    have hlen : attempts P Q w = attempts P Q z := by
      rw [← terminalLog_length P Q htw,← terminalLog_length P Q ht,he]
    apply (run_eq_iff_mem hn P Q (attempts P Q z) hz hw).mp
    simpa only [terminalLog,hlen] using he
  · intro hm
    have hw := state_event_subset_initial _ _ _ hm
    have he := (run_eq_iff_mem hn P Q (attempts P Q z) hz hw).mpr hm
    refine ⟨hw,?_⟩
    have hs : (state P Q (run P Q (attempts P Q z) w)).stopped = true := by
      rw [he]; exact attempts_spec P Q ht
    exact (terminalLog_of_stopped P Q hs).trans he

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) (ht : Terminates P Q z) :
    cellSet Q ∩ {w | terminalLog P Q w = terminalLog P Q z} =
      (state P Q (terminalLog P Q z)).event := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.terminalLog_fiber_inter_initial hn P Q hz ht
    | exact OAI.RepeatedLocalization.FiniteEntropy.terminalLog_fiber_inter_initial
    | (apply OAI.RepeatedLocalization.FiniteEntropy.terminalLog_fiber_inter_initial <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.terminalLog_fiber_inter_initial <;> assumption)
