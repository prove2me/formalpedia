-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.lin_mono_submultiset
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T13:57:02.745956+00:00
-- url     : https://prove2.me/submissions/f6a79723-f605-481e-8251-2c1e668d071e

import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP

set_option autoImplicit false
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

namespace KKLPMonotone

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

lemma feasible_nonempty (I : Multiset ℝ) (hI : IsInstance I) :
    ∃ x, IsLPFeasible I x := by
  classical
  obtain ⟨x, hx, _⟩ := lp_of_packing I (I.map fun t => {t}) (by
    refine ⟨Multiset.sum_map_singleton I, ?_⟩
    intro b hb
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hb
    simpa using (hI t ht).2.le)
  exact ⟨x, hx⟩

lemma lin_le_cost {I : Multiset ℝ} {x : Multiset ℝ →₀ ℝ}
    (hx : IsLPFeasible I x) : LIN I ≤ lpCost x := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact Finset.sum_nonneg fun c _ => hy.2.1 c
  · exact ⟨x, hx, rfl⟩

lemma lin_nonneg (I : Multiset ℝ) : 0 ≤ LIN I := by
  apply Real.sInf_nonneg
  rintro z ⟨x, hx, rfl⟩
  exact Finset.sum_nonneg fun c _ => hx.2.1 c

lemma lin_zero : LIN 0 = 0 := by
  apply le_antisymm _ (lin_nonneg _)
  have hz : IsLPFeasible 0 (0 : Multiset ℝ →₀ ℝ) := by
    simp [IsLPFeasible]
  simpa [lpCost] using lin_le_cost hz

lemma filter_sum_le (I : Multiset ℝ) (p : ℝ → Prop) [DecidablePred p]
    (hI : ∀ x ∈ I, 0 ≤ x) : (I.filter p).sum ≤ I.sum := by
  revert hI
  induction I using Multiset.induction_on with
  | empty => simp
  | @cons a I ih =>
    intro hI
    have ha := hI a (by simp)
    have htail := ih (fun x hx => hI x (by simp [hx]))
    by_cases hpa : p a <;> simp [hpa] <;> linarith

lemma mapDomain_nonneg (x : Multiset ℝ →₀ ℝ) (hx : ∀ c, 0 ≤ x c)
    (f : Multiset ℝ → Multiset ℝ) : ∀ c, 0 ≤ (x.mapDomain f) c := by
  classical
  intro c
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  apply Finset.sum_nonneg
  intro d hd
  simp only [Finsupp.single_apply]
  split_ifs
  · exact hx d
  · exact le_rfl

lemma cost_mapDomain (x : Multiset ℝ →₀ ℝ) (f : Multiset ℝ → Multiset ℝ) :
    lpCost (x.mapDomain f) = lpCost x := by
  change (x.mapDomain f).sum (fun _ w => w) = x.sum (fun _ w => w)
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

lemma cover_mapDomain (x : Multiset ℝ →₀ ℝ) (f : Multiset ℝ → Multiset ℝ) (t : ℝ) :
    (∑ c ∈ (x.mapDomain f).support, (x.mapDomain f) c * (c.count t : ℝ)) =
      ∑ c ∈ x.support, x c * ((f c).count t : ℝ) := by
  change (x.mapDomain f).sum (fun c w => w * (c.count t : ℝ)) =
    x.sum (fun c w => w * ((f c).count t : ℝ))
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

/-- A finite deterministic transformation of configurations preserves cost. -/
lemma feasible_mapDomain (A B : Multiset ℝ) (x : Multiset ℝ →₀ ℝ)
    (hx : IsLPFeasible B x) (f : Multiset ℝ → Multiset ℝ)
    (hf : ∀ c ∈ x.support, IsConfiguration A (f c))
    (hcover : ∀ t ∈ A.toFinset, (A.count t : ℝ) ≤
      ∑ c ∈ x.support, x c * ((f c).count t : ℝ)) :
    IsLPFeasible A (x.mapDomain f) := by
  classical
  refine ⟨?_, mapDomain_nonneg x hx.2.1 f, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hc)
    exact hf d hd
  · intro t ht
    rw [cover_mapDomain]
    exact hcover t ht

/-- Deleting arbitrary occurrences, including whole types, does not increase the LP value. -/
lemma lin_mono_submultiset (A B : Multiset ℝ) (hA : IsInstance A) (hB : IsInstance B)
    (hAB : A ≤ B) : LIN A ≤ LIN B := by
  classical
  by_cases hzero : A = 0
  · simpa [hzero, lin_zero] using lin_nonneg B
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hzero
  let f : Multiset ℝ → Multiset ℝ := fun c =>
    if c.filter (fun t => t ∈ A) = 0 then {a} else c.filter (fun t => t ∈ A)
  obtain ⟨x₀, hx₀⟩ := feasible_nonempty B hB
  change LIN A ≤ sInf {z : ℝ | ∃ x, IsLPFeasible B x ∧ lpCost x = z}
  have hcosts : {z : ℝ | ∃ x, IsLPFeasible B x ∧ lpCost x = z}.Nonempty :=
    ⟨lpCost x₀, x₀, hx₀, rfl⟩
  apply le_csInf hcosts
  rintro z ⟨x, hx, rfl⟩
  have hmap : IsLPFeasible A (x.mapDomain f) := by
    apply feasible_mapDomain A B x hx f
    · intro c hc
      obtain ⟨hc0, htypes, hsum⟩ := hx.1 c hc
      dsimp [f]
      split_ifs with he
      · exact ⟨by simp, by simpa using ha, by simpa using (hA a ha).2.le⟩
      · refine ⟨he, fun t ht => (Multiset.mem_filter.mp ht).2, ?_⟩
        exact (filter_sum_le c _ (fun t ht => (hB t (htypes t ht)).1.le)).trans hsum
    · intro t ht
      have htA : t ∈ A := Multiset.mem_toFinset.mp ht
      have htB : t ∈ B.toFinset := Multiset.mem_toFinset.mpr (Multiset.mem_of_le hAB htA)
      calc
        (A.count t : ℝ) ≤ (B.count t : ℝ) := by exact_mod_cast Multiset.count_le_of_le t hAB
        _ ≤ ∑ c ∈ x.support, x c * (c.count t : ℝ) := hx.2.2 t htB
        _ ≤ ∑ c ∈ x.support, x c * ((f c).count t : ℝ) := by
          apply Finset.sum_le_sum
          intro c hc
          apply mul_le_mul_of_nonneg_left _ (hx.2.1 c)
          have hcount : (c.filter (fun t => t ∈ A)).count t = c.count t :=
            Multiset.count_filter_of_pos htA
          dsimp [f]
          split_ifs with he
          · have hc0 : c.count t = 0 := by simpa [he] using hcount.symm
            simp [hc0]
          · exact le_of_eq (by exact_mod_cast hcount.symm)
  simpa [cost_mapDomain] using lin_le_cost hmap

end KKLPMonotone


theorem solution (A B : Multiset ℝ) (hA : IsInstance A) (hB : IsInstance B)
    (hAB : A ≤ B) : LIN A ≤ LIN B :=
  KKLPMonotone.lin_mono_submultiset A B hA hB hAB
