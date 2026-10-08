-- Prove2me | solution 1 for LawlerPrec.MinMax.move_last_feasible
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-05T12:09:42.937587+00:00
-- url     : https://prove2.me/submissions/ecad8ba4-9ed9-47ae-90a9-d72233eb9363

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

end LawlerProofG


theorem solution {ι : Type*} [DecidableEq ι] (prec : ι → ι → Prop) (J : Finset ι)
    (l : List ι) (k : ι) (hl : IsFeasible prec J l) (hk : k ∈ lastEligible prec J) :
    IsFeasible prec J (l.erase k ++ [k]) := by
  exact LawlerProofG.move_feasible prec J l k hl hk
