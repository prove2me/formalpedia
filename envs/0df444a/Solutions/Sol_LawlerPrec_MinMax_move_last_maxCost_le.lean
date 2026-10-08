-- Prove2me | solution 1 for LawlerPrec.MinMax.move_last_maxCost_le
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-05T12:11:48.879061+00:00
-- url     : https://prove2.me/submissions/f7c9cdf9-c690-43b2-a4bb-cada43d196f4

import Mathlib
import Definitions.Def_LawlerPrec_MinMax_IsMinmaxOptimal
import Definitions.Def_LawlerPrec_MinMax_IsLawlerSequence

set_option autoImplicit false

open MooreLateJobs.Shared MooreLateJobs.MaxDeferral LawlerPrec.MinMax

namespace LawlerProofG

variable {ι : Type*} [DecidableEq ι]

lemma schedule_toFinset {J : Finset ι} {l : List ι} (h : IsSchedule J l) :
    l.toFinset = J := by
  ext j
  simpa using h.2 j

lemma schedule_sum (a : ι → ℝ) {J : Finset ι} {l : List ι} (h : IsSchedule J l) :
    (l.map a).sum = ∑ j ∈ J, a j := by
  rw [← schedule_toFinset h, List.sum_toFinset a h.1]

lemma schedule_erase {J : Finset ι} {l : List ι} (h : IsSchedule J l) (k : ι) :
    IsSchedule (J.erase k) (l.erase k) := by
  refine ⟨h.1.erase _, fun j => ?_⟩
  simp [h.1.mem_erase_iff, h.2]

lemma schedule_append {J : Finset ι} {l : List ι} {k : ι} (hk : k ∈ J)
    (h : IsSchedule (J.erase k) l) : IsSchedule J (l ++ [k]) := by
  have hnot : k ∉ l := by simpa using (h.2 k)
  refine ⟨?_, fun j => ?_⟩
  · simp only [List.nodup_append, List.nodup_singleton, List.mem_singleton,
      forall_eq, true_and]
    exact ⟨h.1, fun j hj he => hnot (he ▸ hj)⟩
  · simp only [List.mem_append, List.mem_singleton, h.2, Finset.mem_erase]
    constructor
    · rintro (⟨_, hj⟩ | rfl)
      · exact hj
      · exact hk
    · intro hj
      by_cases he : j = k
      · exact Or.inr he
      · exact Or.inl ⟨he, hj⟩

lemma eligible_mem {prec : ι → ι → Prop} {J : Finset ι} {k : ι}
    (hk : k ∈ lastEligible prec J) : k ∈ J := by
  classical
  simp only [lastEligible, Finset.mem_filter] at hk
  exact hk.1

lemma eligible_forall {prec : ι → ι → Prop} {J : Finset ι} {k : ι}
    (hk : k ∈ lastEligible prec J) : ∀ j ∈ J, j ≠ k → ¬ prec k j := by
  classical
  simp only [lastEligible, Finset.mem_filter] at hk
  exact hk.2

lemma feasible_erase {prec : ι → ι → Prop} {J : Finset ι} {l : List ι}
    (h : IsFeasible prec J l) (k : ι) : IsFeasible prec (J.erase k) (l.erase k) :=
  ⟨schedule_erase h.1 k, h.2.sublist List.erase_sublist⟩

lemma feasible_append {prec : ι → ι → Prop} {J : Finset ι} {l : List ι} {k : ι}
    (hk : k ∈ lastEligible prec J) (h : IsFeasible prec (J.erase k) l) :
    IsFeasible prec J (l ++ [k]) := by
  refine ⟨schedule_append (eligible_mem hk) h.1, List.pairwise_append.mpr ⟨h.2, by simp, ?_⟩⟩
  intro j hj b hb
  simp only [List.mem_singleton] at hb
  subst b
  have hjJ := (h.1.2 j).mp hj
  exact eligible_forall hk j (Finset.mem_erase.mp hjJ).2 (Finset.mem_erase.mp hjJ).1

lemma move_feasible (prec : ι → ι → Prop) (J : Finset ι) (l : List ι) (k : ι)
    (hl : IsFeasible prec J l) (hk : k ∈ lastEligible prec J) :
    IsFeasible prec J (l.erase k ++ [k]) :=
  feasible_append hk (feasible_erase hl k)

lemma completion_cons_self (a : ι → ℝ) (l : List ι) (j : ι) :
    completionTime a (j :: l) j = a j := by
  simp [completionTime, completionAt]

lemma completion_cons_ne (a : ι → ℝ) (l : List ι) {x j : ι} (hxj : x ≠ j) :
    completionTime a (x :: l) j = a x + completionTime a l j := by
  simp [completionTime, completionAt, hxj, List.idxOf_cons_ne]

lemma completion_append_mem (a : ι → ℝ) {l : List ι} (r : List ι) {j : ι}
    (hj : j ∈ l) : completionTime a (l ++ r) j = completionTime a l j := by
  unfold completionTime completionAt
  rw [List.idxOf_append_of_mem hj, List.take_append_of_le_length]
  exact Nat.succ_le_of_lt (List.idxOf_lt_length_iff.mpr hj)

lemma completion_last (a : ι → ℝ) {l : List ι} {k : ι} (hk : k ∉ l) :
    completionTime a (l ++ [k]) k = ((l ++ [k]).map a).sum := by
  unfold completionTime completionAt
  rw [List.idxOf_append_of_notMem hk]
  simp

lemma completion_erase_le (a : ι → ℝ) (l : List ι) (k j : ι)
    (ha : ∀ x ∈ l, 0 ≤ a x) (hjk : j ≠ k) :
    completionTime a (l.erase k) j ≤ completionTime a l j := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hal : ∀ y ∈ l, 0 ≤ a y := fun y hy => ha y (by simp [hy])
    by_cases hxk : x = k
    · subst x
      rw [List.erase_cons_head, completion_cons_ne a l hjk.symm]
      exact le_add_of_nonneg_left (ha k (by simp))
    · rw [List.erase_cons_tail (by simpa using hxk)]
      by_cases hxj : x = j
      · subst x
        rw [completion_cons_self, completion_cons_self]
      · rw [completion_cons_ne a _ hxj, completion_cons_ne a _ hxj]
        exact add_le_add le_rfl (ih hal)

lemma move_completion (a : ι → ℝ) (J : Finset ι) (ha : ∀ j ∈ J, 0 ≤ a j)
    (l : List ι) (hl : IsSchedule J l) (k : ι) (hk : k ∈ J) :
    (∀ j ∈ J, j ≠ k → completionTime a (l.erase k ++ [k]) j ≤ completionTime a l j) ∧
    completionTime a (l.erase k ++ [k]) k = ∑ j ∈ J, a j := by
  have hs := schedule_append hk (schedule_erase hl k)
  constructor
  · intro j hj hjk
    rw [completion_append_mem a [k] (hl.1.mem_erase_iff.mpr ⟨hjk, (hl.2 j).mpr hj⟩)]
    exact completion_erase_le a l k j (fun x hx => ha x ((hl.2 x).mp hx)) hjk
  · rw [completion_last a (by simp [hl.1.mem_erase_iff])]
    exact schedule_sum a hs

end LawlerProofG


set_option autoImplicit false
open MooreLateJobs.Shared MooreLateJobs.MaxDeferral LawlerPrec.MinMax

namespace LawlerProofG
variable {ι : Type*} [DecidableEq ι]

lemma schedule_prefix {J : Finset ι} {l : List ι} {k : ι}
    (h : IsSchedule J (l ++ [k])) : IsSchedule (J.erase k) l := by
  have hn := List.nodup_append.mp h.1
  refine ⟨hn.1, fun j => ?_⟩
  have hknot : k ∉ l := fun hkl => hn.2.2 k hkl k (by simp) rfl
  constructor
  · intro hj
    exact Finset.mem_erase.mpr ⟨fun e => hknot (e ▸ hj), (h.2 j).mp (by simp [hj])⟩
  · intro hj
    rcases Finset.mem_erase.mp hj with ⟨hne, hm⟩
    have := (h.2 j).mpr hm
    simpa [hne] using this

lemma feasible_last_eligible {prec : ι → ι → Prop} {J : Finset ι} {l : List ι} {k : ι}
    (h : IsFeasible prec J l) (hlast : l.getLast? = some k) :
    k ∈ lastEligible prec J := by
  classical
  obtain ⟨p, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  simp only [lastEligible, Finset.mem_filter]
  refine ⟨(h.1.2 k).mp (by simp), ?_⟩
  intro j hj hne
  have hjp : j ∈ p := by
    have := (h.1.2 j).mpr hj
    simpa [hne] using this
  exact (List.pairwise_append.mp h.2).2.2 j hjp k (by simp)

lemma schedule_nonempty {J : Finset ι} {l : List ι} (hJ : J.Nonempty)
    (h : IsSchedule J l) : l ≠ [] := by
  obtain ⟨j, hj⟩ := hJ
  exact List.ne_nil_of_mem ((h.2 j).mpr hj)

lemma completion_of_last (a : ι → ℝ) {J : Finset ι} {l : List ι} {k : ι}
    (h : IsSchedule J l) (hlast : l.getLast? = some k) :
    completionTime a l k = ∑ j ∈ J, a j := by
  obtain ⟨p, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  have hknot : k ∉ p := fun hkp => (List.nodup_append.mp h.1).2.2 k hkp k (by simp) rfl
  rw [completion_last a hknot, schedule_sum a h]

lemma move_maxcost (a : ι → ℝ) (c : ι → ℝ → ℝ) (prec : ι → ι → Prop)
    (J : Finset ι) (hJ : J.Nonempty) (ha : ∀ j ∈ J, 0 ≤ a j)
    (hc : ∀ j ∈ J, Monotone (c j)) (l : List ι) (hl : IsFeasible prec J l)
    (k k' : ι) (hlast : l.getLast? = some k') (hk : k ∈ lastEligible prec J)
    (hkk' : c k (∑ j ∈ J, a j) ≤ c k' (∑ j ∈ J, a j)) :
    maxCost a c J hJ (l.erase k ++ [k]) ≤ maxCost a c J hJ l := by
  have htime := move_completion a J ha l hl.1 k (eligible_mem hk)
  apply Finset.sup'_le
  intro j hj
  by_cases hjk : j = k
  · subst j
    rw [htime.2]
    calc
      c k (∑ j ∈ J, a j) ≤ c k' (∑ j ∈ J, a j) := hkk'
      _ = c k' (completionTime a l k') := by rw [completion_of_last a hl.1 hlast]
      _ ≤ maxCost a c J hJ l := Finset.le_sup' (fun j => c j (completionTime a l j))
        ((hl.1.2 k').mp (List.mem_of_getLast? hlast))
  · exact (hc j hj (htime.1 j hj hjk)).trans
      (Finset.le_sup' (fun j => c j (completionTime a l j)) hj)

end LawlerProofG


theorem solution {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (c : ι → ℝ → ℝ)
    (prec : ι → ι → Prop) (J : Finset ι) (hJ : J.Nonempty) (ha : ∀ j ∈ J, 0 ≤ a j)
    (hc : ∀ j ∈ J, Monotone (c j)) (l : List ι) (hl : IsFeasible prec J l) (k k' : ι)
    (hlast : l.getLast? = some k') (hk : k ∈ lastEligible prec J)
    (hkk' : c k (∑ j ∈ J, a j) ≤ c k' (∑ j ∈ J, a j)) :
    MooreLateJobs.MaxDeferral.maxCost a c J hJ (l.erase k ++ [k]) ≤
      MooreLateJobs.MaxDeferral.maxCost a c J hJ l := by
  exact LawlerProofG.move_maxcost a c prec J hJ ha hc l hl k k' hlast hk hkk'
