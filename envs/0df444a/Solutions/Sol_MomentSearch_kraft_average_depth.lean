-- Prove2me | solution 1 for MomentSearch.kraft_average_depth
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:46:06.540659+00:00
-- url     : https://prove2.me/submissions/c1fbf564-f79b-443a-983b-0924688dad3a

import Mathlib
import Definitions.Def_MomentSearch_queries

open Finset MomentSearch

private theorem tree_kraft {a b : ℕ} (T : SearchTree a b) :
    ∑ t ∈ Icc a b, ((3:ℝ)^queries T t)⁻¹ ≤ 1 := by
  classical
  induction T with
  | leaf a => simp [queries]
  | @node a b v hav hvb hab left right ihl ihr =>
    let W := fun t => ((3:ℝ)^queries (.node v hav hvb hab left right) t)⁻¹
    let U := (Icc a b).filter (· < v)
    let V := (Icc a b).filter (v < ·)
    have huv : Disjoint U V := by
      apply Finset.disjoint_left.mpr
      intro t ht h'
      exact lt_asymm (Finset.mem_filter.mp ht).2 (Finset.mem_filter.mp h').2
    have partition : Icc a b = insert v (U ∪ V) := by
      ext t
      simp only [U,V,Finset.mem_Icc,Finset.mem_insert,Finset.mem_union,Finset.mem_filter]
      constructor
      · intro ht
        rcases lt_trichotomy t v with hh | rfl | hh
        · exact Or.inr (Or.inl ⟨ht,hh⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨ht,hh⟩)
      · rintro (rfl | h | h)
        · exact ⟨hav,hvb⟩
        · exact h.1
        · exact h.1
    have hn : v ∉ U ∪ V := by simp [U,V]
    have vW : W v = 1/3 := by norm_num [W,queries]
    have scale (q : ℕ) : ((3:ℝ)^(1+q))⁻¹ = (1/3)*((3:ℝ)^q)⁻¹ := by
      simp [pow_add,mul_inv_rev,div_eq_mul_inv,mul_comm]
    have lw : (∑ t ∈ U, W t) ≤ 1/3 := by
      by_cases hh : a < v
      · have Ueq : U = Icc a (v-1) := by
          ext t
          simp only [U,Finset.mem_filter,Finset.mem_Icc]
          omega
        rw [Ueq]
        have e : ∑ t ∈ Icc a (v-1), W t =
            (1/3)*∑ t ∈ Icc a (v-1), ((3:ℝ)^queries (left hh) t)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          have ht' : t < v := by have q := (Finset.mem_Icc.mp ht).2; omega
          simp only [W,queries,if_neg ht'.ne,if_pos ht',dif_pos hh,scale]
        rw [e]
        exact mul_le_mul_of_nonneg_left (ihl hh) (by norm_num) |>.trans (by norm_num)
      · have e : U = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro t ht
          have h := Finset.mem_filter.mp ht
          have ha := (Finset.mem_Icc.mp h.1).1
          omega
        rw [e]
        norm_num
    have rw' : (∑ t ∈ V, W t) ≤ 1/3 := by
      by_cases hh : v < b
      · have Veq : V = Icc (v+1) b := by
          ext t
          simp only [V,Finset.mem_filter,Finset.mem_Icc]
          omega
        rw [Veq]
        have e : ∑ t ∈ Icc (v+1) b, W t =
            (1/3)*∑ t ∈ Icc (v+1) b, ((3:ℝ)^queries (right hh) t)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          have ht' : v < t := (Finset.mem_Icc.mp ht).1
          simp only [W,queries,if_neg ht'.ne.symm,if_neg (not_lt_of_gt ht'),dif_pos hh,scale]
        rw [e]
        exact mul_le_mul_of_nonneg_left (ihr hh) (by norm_num) |>.trans (by norm_num)
      · have e : V = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro t ht
          have h := Finset.mem_filter.mp ht
          have hb := (Finset.mem_Icc.mp h.1).2
          omega
        rw [e]
        norm_num
    change ∑ t ∈ Icc a b, W t ≤ 1
    rw [partition,Finset.sum_insert hn,Finset.sum_union huv,vW]
    linarith

theorem solution {n : ℕ} (_hn : 2 ≤ n) (T : Strategy n) (R : ℕ)
    (m : Fin (R + 1) → Fin n) (hm : Function.Injective m) :
    ∑ r : Fin (R + 1), ((3 : ℝ) ^ queries T (m r : ℕ))⁻¹ ≤ 1 ∧
    Real.logb 3 ((R : ℝ) + 1) ≤
      (1 / ((R : ℝ) + 1)) * ∑ r : Fin (R + 1), (queries T (m r : ℕ) : ℝ) := by
  classical
  let f := fun t : ℕ => ((3:ℝ)^queries T t)⁻¹
  let u := fun r : Fin (R+1) => (m r:ℕ)
  have inj : Function.Injective u := fun a b he => hm (Fin.ext he)
  have sub : Finset.univ.image u ⊆ Finset.Icc 0 (n-1) := by
    intro x hx
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,by have h := (m r).isLt; dsimp [u]; omega⟩
  have K : (∑ r : Fin (R+1), f (u r)) ≤ 1 := by
    rw [← Finset.sum_image (fun a _ b _ h => inj h)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg sub
      (fun x _ _ => by dsimp [f]; positivity)).trans (tree_kraft T)
  refine ⟨K,?_⟩
  let M := (R:ℝ)+1
  let w := fun _ : Fin (R+1) => (1:ℝ)/M
  let d := fun r : Fin (R+1) => -(queries T (m r:ℕ):ℝ)
  have pos : 0 < M := by dsimp [M]; positivity
  have sw : ∑ r : Fin (R+1), w r = 1 := by
    simp only [w,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_one]
    change M*(1/M) = _
    field_simp
  have je := (convexOn_rpow_left (by norm_num : (0:ℝ)<3)).map_sum_le
    (t := Finset.univ) (w := w) (p := d) (fun _ _ => by dsimp [w]; positivity) sw
    (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at je
  have exp_d (r : Fin (R+1)) : (3:ℝ)^d r = f (u r) := by
    dsimp [d,f,u]; rw [Real.rpow_neg (by norm_num),Real.rpow_natCast]
  have avg : (∑ r : Fin (R+1), w r*d r) =
      -((1/M)*∑ r : Fin (R+1), (queries T (m r:ℕ):ℝ)) := by
    simp only [w,d,mul_neg,Finset.sum_neg_distrib,← Finset.mul_sum]
  rw [avg,Real.rpow_neg (by norm_num)] at je
  simp_rw [exp_d,w,← Finset.mul_sum] at je
  have j := je.trans (mul_le_mul_of_nonneg_left K (by positivity : 0 ≤ 1/M))
  rw [mul_one] at j
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<3) pos).mpr
  apply (inv_le_inv₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) _) pos).mp
  simpa only [one_div] using j
