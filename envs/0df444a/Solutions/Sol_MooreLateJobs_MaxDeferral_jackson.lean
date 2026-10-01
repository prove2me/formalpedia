-- Prove2me | solution 1 for MooreLateJobs.MaxDeferral.jackson
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:37:27.946478+00:00
-- url     : https://prove2.me/submissions/e07c5dbf-d9de-4a43-8933-b3ed6b6d5c73

import Definitions.Def_MooreLateJobs_MaxDeferral_NoLateAt
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open MooreLateJobs Shared MaxDeferral Finset
namespace CMoore
variable {ι : Type*} [DecidableEq ι]

theorem completion_cons (t : ι → ℝ) (a j : ι) (l : List ι) (h : a ≠ j) :
    completionTime t (a::l) j = t a + completionTime t l j := by
  simp [completionTime, completionAt, List.idxOf_cons_ne _ h]

theorem selected_total_le (t : ι → ℝ) (l : List ι) (K : Finset ι)
    (hK : K.Nonempty) (hKl : ∀ j ∈ K, j ∈ l) (ht : ∀ j ∈ l, 0 ≤ t j)
    (c : ℝ) (B : EReal) (hb : ∀ j ∈ K, ((c+completionTime t l j : ℝ) : EReal) ≤ B) :
    ((c+∑ j ∈ K, t j : ℝ) : EReal) ≤ B := by
  classical
  induction l generalizing K c with
  | nil => obtain ⟨j,hj⟩ := hK; simpa using hKl j hj
  | cons a l ih =>
    have hKt : ∀ j ∈ K.erase a, j ∈ l := by
      intro j hj
      have hx := hKl j (Finset.mem_of_mem_erase hj)
      exact (List.mem_cons.mp hx).resolve_left (Finset.ne_of_mem_erase hj)
    by_cases he : (K.erase a).Nonempty
    · have hh := ih (K.erase a) he hKt (fun j hj => ht j (List.mem_cons_of_mem _ hj)) (c+t a) (by
        intro j hj
        have h := hb j (Finset.mem_of_mem_erase hj)
        rw [completion_cons t a j l (Finset.ne_of_mem_erase hj).symm] at h
        simpa only [add_assoc] using h)
      by_cases ha : a ∈ K
      · rw [← Finset.add_sum_erase K t ha]
        simpa only [add_assoc] using hh
      · rw [Finset.erase_eq_of_notMem ha] at hh
        exact le_trans (EReal.coe_le_coe_iff.mpr (by linarith [ht a List.mem_cons_self])) hh
    · have hKe : K.erase a = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      have hKa : K = {a} := by
        ext j
        constructor
        · intro hj
          have : j = a := by by_contra h; have hx := Finset.mem_erase.mpr ⟨h,hj⟩; rw [hKe] at hx; exact Finset.notMem_empty _ hx
          simpa [this]
        · intro hj
          have hja : j=a := Finset.mem_singleton.mp hj
          obtain ⟨k,hk⟩ := hK
          have hka : k=a := by by_contra h; have hx := Finset.mem_erase.mpr ⟨h,hk⟩; rw [hKe] at hx; exact Finset.notMem_empty _ hx
          simpa [hja,hka] using hk
      have hh := hb a (by simp [hKa])
      simpa [hKa,completionTime,completionAt] using hh

theorem prefix_deadline (D : ι → EReal) (l : List ι) (hs : l.Pairwise (fun a b => D a ≤ D b))
    (j : ι) (hj : j ∈ l) : ∀ k ∈ l.take (l.idxOf j+1), D k ≤ D j := by
  induction l with
  | nil => simp at hj
  | cons a l ih =>
    rcases List.pairwise_cons.mp hs with ⟨ha,hl⟩
    by_cases he : a=j
    · subst a
      simpa using (show ∀ k ∈ [j], D k ≤ D j by simp)
    · have hjl : j ∈ l := (List.mem_cons.mp hj).resolve_left (Ne.symm he)
      rw [List.idxOf_cons_ne _ he, List.take_succ_cons]
      intro k hk
      rcases List.mem_cons.mp hk with rfl|hk
      · exact ha j hjl
      · exact ih hl hjl k hk

theorem sorted_feasible (t : ι → ℝ) (D : ι → EReal) (J : Finset ι)
    (ht : ∀ i ∈ J, 0 ≤ t i) (l s : List ι)
    (hl : IsSchedule J l) (hs : IsSchedule J s) (hsl : s.Pairwise (fun a b => D a ≤ D b))
    (hf : NoLate t D l) : NoLate t D s := by
  intro j hj
  apply not_lt.mpr
  let K := (s.take (s.idxOf j+1)).toFinset
  have hKj : j ∈ K := by
    apply List.mem_toFinset.mpr
    exact (List.mem_take_iff_idxOf_lt hj).mpr (by omega)
  have hKl : ∀ k ∈ K, k ∈ l := by
    intro k hk
    exact (hl.2 k).mpr ((hs.2 k).mp (List.mem_of_mem_take (List.mem_toFinset.mp hk)))
  have hb : ∀ k ∈ K, ((0+completionTime t l k : ℝ) : EReal) ≤ D j := by
    intro k hk
    simp only [zero_add]
    exact (not_lt.mp (hf k (hKl k hk))).trans
      (prefix_deadline D s hsl j hj k (List.mem_toFinset.mp hk))
  have hh := selected_total_le t l K ⟨j,hKj⟩ hKl (fun k hk => ht k ((hl.2 k).mp hk)) 0 (D j) hb
  simpa only [zero_add, K, List.sum_toFinset _ (hs.1.take), completionTime, completionAt] using hh

theorem exists_sorted (J : Finset ι) (D : ι → EReal) :
    ∃ s : List ι, IsSchedule J s ∧ s.Pairwise (fun a b => D a ≤ D b) := by
  classical
  let s := J.toList.mergeSort (fun a b => decide (D a ≤ D b))
  have hp : s.Perm J.toList := List.mergeSort_perm _ _
  refine ⟨s,⟨hp.nodup_iff.mpr J.nodup_toList, fun j => hp.mem_iff.trans Finset.mem_toList⟩,?_⟩
  apply List.pairwise_mergeSort'

theorem jackson (J : Finset ι) (t : ι → ℝ) (D : ι → EReal) (ht : ∀ i ∈ J, 0 ≤ t i) :
    (∃ S : List ι, IsSchedule J S ∧ NoLate t D S) ↔
      ∀ S : List ι, IsSchedule J S → S.Pairwise (fun a b => D a ≤ D b) → NoLate t D S := by
  constructor
  · rintro ⟨l,hl,hf⟩ s hs hsl
    exact sorted_feasible t D J ht l s hl hs hsl hf
  · intro h
    obtain ⟨s,hs,hsl⟩ := exists_sorted J D
    exact ⟨s,hs,h s hs hsl⟩

end CMoore



theorem solution {ι : Type*} [DecidableEq ι] (J : Finset ι) (t : ι → ℝ) (D : ι → EReal)
    (ht : ∀ i ∈ J, 0 ≤ t i) :
    (∃ S : List ι, Shared.IsSchedule J S ∧ NoLate t D S) ↔
      ∀ S : List ι, Shared.IsSchedule J S → S.Pairwise (fun a b => D a ≤ D b) → NoLate t D S := by
  exact CMoore.jackson J t D ht


