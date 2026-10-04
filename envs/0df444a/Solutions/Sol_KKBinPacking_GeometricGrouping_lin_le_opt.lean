-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.lin_le_opt
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T12:24:24.907177+00:00
-- url     : https://prove2.me/submissions/956de592-7e80-4f94-ae20-f0b7fe913d4e

import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP

set_option autoImplicit false
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

namespace KKLinOpt

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
    (hP : IsPacking I P) :
    ∃ x, IsLPFeasible I x ∧ lpCost x ≤ (P.card : ℝ) := by
  classical
  let Q := P.filter (fun c => c ≠ 0)
  have hQjoin : Q.join = I := by
    exact (join_filter_nonzero P).trans hP.1
  let x : Multiset ℝ →₀ ℝ := Q.toFinsupp.mapRange (fun n : ℕ => (n : ℝ)) (by simp)
  have hsupp : x.support = Q.toFinset := by
    exact (Finsupp.support_mapRange_of_injective (by simp) Q.toFinsupp Nat.cast_injective).trans
      (Multiset.toFinsupp_support Q)
  have hx (c : Multiset ℝ) : x c = (Q.count c : ℝ) := by simp [x]
  refine ⟨x, ⟨?_, ?_, ?_⟩, ?_⟩
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
  · unfold lpCost
    rw [hsupp]
    simp_rw [hx]
    have hcost : (∑ c ∈ Q.toFinset, (Q.count c : ℝ)) = (Q.card : ℝ) := by
      exact_mod_cast Multiset.toFinset_sum_count_eq Q
    rw [hcost]
    exact_mod_cast Multiset.card_le_card (Multiset.filter_le (fun c => c ≠ 0) P)

end KKLinOpt

theorem solution (I : Multiset ℝ) (hI : IsInstance I) : LIN I ≤ (OPT I : ℝ) := by
  classical
  have hex : {B : ℕ | ∃ P : Multiset (Multiset ℝ), IsPacking I P ∧ P.card = B}.Nonempty := by
    refine ⟨I.card, I.map (fun t => {t}), ⟨?_, ?_⟩, by simp⟩
    · induction I using Multiset.induction_on with
      | empty => simp
      | cons t I ih => simpa using ih (fun s hs => hI s (by simp [hs]))
    · intro b hb
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hb
      simpa using (hI t ht).2.le
  obtain ⟨P, hP, hcard⟩ := Nat.sInf_mem hex
  obtain ⟨x, hx, hcost⟩ := KKLinOpt.lp_of_packing I P hP
  have hbelow : BddBelow {z : ℝ | ∃ x, IsLPFeasible I x ∧ lpCost x = z} := by
    refine ⟨0, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact Finset.sum_nonneg fun c _ => hy.2.1 c
  have hlin : LIN I ≤ lpCost x := csInf_le hbelow ⟨x, hx, rfl⟩
  have hcard' : P.card = OPT I := hcard
  rw [hcard'] at hcost
  exact hlin.trans hcost

