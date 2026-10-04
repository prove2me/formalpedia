-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.geom_dominance_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T13:45:03.769249+00:00
-- url     : https://prove2.me/submissions/14fab497-6ca3-4f3e-9257-9ecd7ee5d6d6

import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance

set_option autoImplicit false

open KKBinPacking.GeometricGrouping

namespace KKDominance

lemma takeUntil_append_drop (k : ℝ) (L : List ℝ) :
    takeUntil k L ++ L.drop (takeUntil k L).length = L := by
  induction L generalizing k with
  | nil => simp [takeUntil]
  | cons x xs ih =>
    rw [takeUntil]
    split_ifs with h
    · simp
    · simpa using congrArg (List.cons x) (ih (k - x))

lemma groups_sum (k : ℝ) : (L : List ℝ) →
    ((geomGroupsList k L).map (fun (G : List ℝ) => (G : Multiset ℝ))).sum =
      (L : Multiset ℝ)
  | [] => by simp [geomGroupsList]
  | x :: xs => by
    rw [geomGroupsList]
    simp only [List.map_cons, List.sum_cons]
    rw [groups_sum k ((x :: xs).drop (takeUntil k (x :: xs)).length)]
    rw [Multiset.coe_add, takeUntil_append_drop]
termination_by L => L.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have := takeUntil_cons_length_pos k x xs
  omega

lemma groups_flatten (k : ℝ) : (L : List ℝ) →
    (geomGroupsList k L).flatten = L
  | [] => by simp [geomGroupsList]
  | x :: xs => by
    rw [geomGroupsList, List.flatten_cons]
    rw [groups_flatten k ((x :: xs).drop (takeUntil k (x :: xs)).length)]
    exact takeUntil_append_drop k (x :: xs)
termination_by L => L.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have := takeUntil_cons_length_pos k x xs
  omega

def groupCertificate (A G : List ℝ) : Multiset (ℝ × ℝ) :=
  ((A.take G.length).map (fun x => (G.headD 0, x)) : List (ℝ × ℝ))

def adjacentCertificate (A : List ℝ) (Gs : List (List ℝ)) : Multiset (ℝ × ℝ) :=
  (List.zipWith groupCertificate (A :: Gs) Gs).sum

lemma group_first (A G : List ℝ) :
    (groupCertificate A G).map Prod.fst =
      ((((G.take A.length).map (fun x => (x, G.headD 0))) : Multiset (ℝ × ℝ))).map
        Prod.snd := by
  simp [groupCertificate, Multiset.map_coe, List.map_map, Function.comp_def,
    List.map_const', Nat.min_comm]

lemma group_second (A G : List ℝ) :
    (groupCertificate A G).map Prod.snd = (A.take G.length : List ℝ) := by
  simp [groupCertificate, Multiset.map_coe, List.map_map, Function.comp_def]

lemma adjacent_first (A : List ℝ) (Gs : List (List ℝ)) :
    (adjacentCertificate A Gs).map Prod.fst =
      (List.zipWith
        (fun (Gprev Gi : List ℝ) =>
          (((Gi.take Gprev.length).map (fun x => (x, Gi.headD 0))) : Multiset (ℝ × ℝ)))
        (A :: Gs) Gs).sum.map Prod.snd := by
  induction Gs generalizing A with
  | nil => simp [adjacentCertificate]
  | cons G Gs ih =>
    simp only [adjacentCertificate, List.zipWith_cons_cons, List.sum_cons,
      Multiset.map_add]
    rw [group_first, ← adjacentCertificate, ih G]

lemma adjacent_second_le (A : List ℝ) (Gs : List (List ℝ)) :
    (adjacentCertificate A Gs).map Prod.snd ≤
      (((A :: Gs).map (fun (G : List ℝ) => (G : Multiset ℝ))).sum) := by
  induction Gs generalizing A with
  | nil => simp [adjacentCertificate]
  | cons G Gs ih =>
    have htake : ((A.take G.length : List ℝ) : Multiset ℝ) ≤ (A : Multiset ℝ) :=
      Multiset.coe_le.mpr (List.take_sublist G.length A).subperm
    simp only [adjacentCertificate, List.zipWith_cons_cons, List.sum_cons,
      Multiset.map_add]
    rw [group_second, ← adjacentCertificate]
    exact (add_le_add htake (ih G)).trans_eq (by simp)

lemma adjacent_order (A : List ℝ) (Gs : List (List ℝ))
    (hsorted : (A :: Gs).flatten.Pairwise (· ≥ ·)) :
    ∀ p ∈ adjacentCertificate A Gs, p.1 ≤ p.2 := by
  induction Gs generalizing A with
  | nil => simp [adjacentCertificate]
  | cons G Gs ih =>
    have hsplit := List.pairwise_append.mp
      (show (A ++ (G :: Gs).flatten).Pairwise (· ≥ ·) by simpa using hsorted)
    intro p hp
    simp only [adjacentCertificate, List.zipWith_cons_cons, List.sum_cons,
      Multiset.mem_add] at hp
    rcases hp with hp | hp
    · simp only [groupCertificate, Multiset.mem_coe, List.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      cases G with
      | nil => simp at hx
      | cons y ys =>
        exact hsplit.2.2 x (List.mem_of_mem_take hx) y (by simp)
    · exact ih G hsplit.2.1 p hp

end KKDominance

open KKDominance

/-- Every rounded piece has a distinct source slot in the original instance
whose size is at least its rounded size. No positivity or lower bound on k is needed. -/
theorem solution (k : ℕ) (I : Multiset ℝ) :
    ∃ pairs : Multiset (ℝ × ℝ),
      pairs.map Prod.fst = geomJ k I ∧
      pairs.map Prod.snd ≤ I ∧
      ∀ p ∈ pairs, p.1 ≤ p.2 := by
  have hsum : ((geomGroups k I).map (fun (G : List ℝ) => (G : Multiset ℝ))).sum = I := by
    rw [geomGroups, groups_sum, Multiset.sort_eq]
  have hsorted : (geomGroups k I).flatten.Pairwise (· ≥ ·) := by
    rw [geomGroups, groups_flatten]
    exact Multiset.pairwise_sort _ _
  unfold geomJ geomPairs
  generalize geomGroups k I = Gs at *
  cases Gs with
  | nil => exact ⟨0, by simp, by simp, by simp⟩
  | cons A Gs =>
    refine ⟨adjacentCertificate A Gs, ?_, ?_, adjacent_order A Gs hsorted⟩
    · simpa only [List.tail_cons] using adjacent_first A Gs
    · rw [← hsum]
      exact adjacent_second_le A Gs
