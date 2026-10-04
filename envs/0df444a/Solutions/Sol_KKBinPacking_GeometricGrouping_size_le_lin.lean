-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.size_le_lin
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T13:20:47.813129+00:00
-- url     : https://prove2.me/submissions/62180682-e5b6-4539-bbe8-95e232733f4a

import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP

set_option autoImplicit false
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

namespace KKSizeLower

lemma weighted_count_sum (I c : Multiset ℝ) (hc : ∀ t ∈ c, t ∈ I) :
    (∑ t ∈ I.toFinset, (c.count t : ℝ) * t) = c.sum := by
  classical
  calc
    (∑ t ∈ I.toFinset, (c.count t : ℝ) * t) =
        ∑ t ∈ c.toFinset, (c.count t : ℝ) * t := by
      symm
      apply Finset.sum_subset
      · intro t ht
        exact Multiset.mem_toFinset.mpr (hc t (Multiset.mem_toFinset.mp ht))
      · intro t _ ht
        simp [Multiset.count_eq_zero.mpr (by simpa using ht)]
    _ = c.sum := by
      simpa only [nsmul_eq_mul, Multiset.map_id'] using
        (Finset.sum_multiset_map_count c (fun t => t)).symm

lemma size_le_cost (I : Multiset ℝ) (hI : IsInstance I)
    (x : Multiset ℝ →₀ ℝ) (hx : IsLPFeasible I x) : SIZE I ≤ lpCost x := by
  classical
  calc
    SIZE I = ∑ t ∈ I.toFinset, (I.count t : ℝ) * t :=
      (weighted_count_sum I I (fun _ ht => ht)).symm
    _ ≤ ∑ t ∈ I.toFinset, (∑ c ∈ x.support, x c * (c.count t : ℝ)) * t := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_right (hx.2.2 t ht)
        (hI t (Multiset.mem_toFinset.mp ht)).1.le
    _ = ∑ c ∈ x.support, x c * c.sum := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [← weighted_count_sum I c (hx.1 c hc).2.1, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ lpCost x := by
      apply Finset.sum_le_sum
      intro c hc
      simpa using mul_le_mul_of_nonneg_left (hx.1 c hc).2.2 (hx.2.1 c)

lemma join_filter_nonzero (P : Multiset (Multiset ℝ)) :
    (P.filter (fun c => c ≠ 0)).join = P.join := by
  classical
  induction P using Multiset.induction_on with
  | empty => simp
  | cons c P ih =>
    by_cases hc : c = 0
    · simp [hc, ih]
    · simp [hc, ih]

lemma lp_of_packing (I : Multiset ℝ) (P : Multiset (Multiset ℝ))
    (hP : IsPacking I P) : ∃ x, IsLPFeasible I x := by
  classical
  let Q := P.filter (fun c => c ≠ 0)
  have hQjoin : Q.join = I := (join_filter_nonzero P).trans hP.1
  let x : Multiset ℝ →₀ ℝ := Q.toFinsupp.mapRange (fun n : ℕ => (n : ℝ)) (by simp)
  have hsupp : x.support = Q.toFinset := by
    exact (Finsupp.support_mapRange_of_injective (by simp) Q.toFinsupp Nat.cast_injective).trans
      (Multiset.toFinsupp_support Q)
  have hx (c : Multiset ℝ) : x c = (Q.count c : ℝ) := by simp [x]
  refine ⟨x, ?_, ?_, ?_⟩
  · intro c hc
    rw [hsupp, Multiset.mem_toFinset] at hc
    have hmem := Multiset.mem_filter.mp hc
    refine ⟨hmem.2, ?_, hP.2 c hmem.1⟩
    intro t ht
    rw [← hP.1]
    exact Multiset.mem_join.mpr ⟨c, hmem.1, ht⟩
  · intro c
    rw [hx]
    positivity
  · intro t ht
    rw [hsupp]
    simp_rw [hx]
    have hcount : I.count t = ∑ c ∈ Q.toFinset, Q.count c * c.count t := by
      rw [← hQjoin]
      calc
        Q.join.count t = (Q.map (fun c => c.count t)).sum := by
          induction Q using Multiset.induction_on with
          | empty => simp
          | cons c Q ih => simp [ih]
        _ = _ := by simpa only [nsmul_eq_mul, Nat.cast_id] using
          (Finset.sum_multiset_map_count Q (fun c => c.count t))
    exact le_of_eq (by exact_mod_cast hcount)

lemma feasible_exists (I : Multiset ℝ) (hI : IsInstance I) :
    ∃ x, IsLPFeasible I x := by
  apply lp_of_packing I (I.map (fun t => {t}))
  constructor
  · induction I using Multiset.induction_on with
    | empty => simp
    | cons t I ih => simpa using ih (fun s hs => hI s (by simp [hs]))
  · intro b hb
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hb
    simpa using (hI t ht).2.le

end KKSizeLower

theorem solution (I : Multiset ℝ) (hI : IsInstance I) : SIZE I ≤ LIN I := by
  obtain ⟨x, hx⟩ := KKSizeLower.feasible_exists I hI
  exact le_csInf ⟨lpCost x, x, hx, rfl⟩ fun z ⟨y, hy, hcost⟩ =>
    hcost ▸ KKSizeLower.size_le_cost I hI y hy
