-- Prove2me | solution 1 for HararySachs.Hyper.exp_newton
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T05:17:13.73074+00:00
-- url     : https://prove2.me/submissions/a11c503e-2ae6-477c-89de-fb415508fa3c

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators

open HararySachs.Hyper Finset

namespace ExpNewtonAux

/-- `t` with the value at `0` killed -/
def tz (t : ℕ → ℚ) (j : ℕ) : ℚ := if j = 0 then 0 else t j

/-- weighted count of `m`-part compositions of `e` with parts bounded by `B` -/
def H (t : ℕ → ℚ) (B m e : ℕ) : ℚ :=
  ∑ x : Fin m → Fin (B + 1), if (∑ i, (x i).val) = e then ∏ i, tz t (x i).val else 0

lemma sum_range_eq_Icc (g : ℕ → ℚ) (h0 : g 0 = 0) (d : ℕ) :
    ∑ j ∈ range (d + 1), g j = ∑ j ∈ Icc 1 d, g j := by
  have : range (d + 1) = insert 0 (Icc 1 d) := by
    ext j; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [this, sum_insert (by simp), h0, zero_add]

lemma H_zero_parts (t : ℕ → ℚ) (B e : ℕ) (he : 1 ≤ e) : H t B 0 e = 0 := by
  unfold H
  simp only [univ_eq_empty, Finset.sum_empty, univ_unique, sum_singleton]
  rw [if_neg (by omega)]

lemma H_big (t : ℕ → ℚ) (B m e : ℕ) (hm : e < m) : H t B m e = 0 := by
  unfold H
  apply sum_eq_zero
  intro x _
  split_ifs with h
  · obtain ⟨i, hi⟩ : ∃ i, (x i).val = 0 := by
      by_contra hall
      push Not at hall
      have : ∑ i : Fin m, 1 ≤ ∑ i, (x i).val :=
        sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (hall i)
      simp at this; omega
    exact prod_eq_zero (mem_univ i) (by simp [tz, hi])
  · rfl

/-- the bound on the parts is irrelevant once it exceeds `e` -/
lemma H_bound (t : ℕ → ℚ) (B m e : ℕ) (hB : e ≤ B) : H t B m e = H t e m e := by
  unfold H
  rw [← sum_filter, ← sum_filter]
  symm
  apply sum_bij (fun x _ => fun i => Fin.castLE (by omega) (x i))
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    simpa using hx
  · intro x _ y _ h
    funext i
    have := congrFun h i
    exact Fin.castLE_injective _ this
  · intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    have hle : ∀ i, (y i).val ≤ e := fun i => by
      rw [← hy]; exact single_le_sum (f := fun i => (y i).val) (fun _ _ => Nat.zero_le _) (mem_univ i)
    refine ⟨fun i => ⟨(y i).val, by have := hle i; omega⟩, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]; exact hy
    · funext i; ext; simp
  · intro x _
    simp

lemma schurP_eq (t : ℕ → ℚ) (d : ℕ) :
    schurP d t = ∑ m ∈ range (d + 1), H t d m d / (m.factorial : ℚ) := by
  unfold schurP
  split_ifs with hd
  · subst hd; simp [H]
  · rw [sum_range_eq_Icc (fun m => H t d m d / (m.factorial : ℚ))
      (by simp [H_zero_parts t d d (by omega)])]
    refine sum_congr rfl fun m _ => ?_
    unfold H
    rw [sum_div]
    refine sum_congr rfl fun a _ => ?_
    by_cases hs : (∑ i, (a i).val) = d
    · by_cases hp : ∀ i, 0 < (a i).val
      · rw [if_pos ⟨hp, hs⟩, if_pos hs]
        congr 1
        exact prod_congr rfl fun i _ => by simp [tz, (hp i).ne']
      · rw [if_neg (fun h => hp h.1), if_pos hs]
        push Not at hp
        obtain ⟨i, hi⟩ := hp
        rw [prod_eq_zero (mem_univ i) (by simp [tz, Nat.le_zero.mp hi]), zero_div]
    · rw [if_neg (fun h => hs h.2), if_neg hs, zero_div]

lemma H_succ (t : ℕ → ℚ) (m d : ℕ) :
    (d : ℚ) * H t d (m + 1) d =
      (m + 1 : ℚ) * ∑ j ∈ range (d + 1), (j : ℚ) * tz t j * H t d m (d - j) := by
  set P : (Fin (m + 1) → Fin (d + 1)) → ℚ := fun x => ∏ i, tz t (x i).val with hP
  -- step a: distribute `d = ∑ xᵢ`
  have ha : (d : ℚ) * H t d (m + 1) d = ∑ i : Fin (m + 1), ∑ x : Fin (m + 1) → Fin (d + 1),
      if (∑ l, (x l).val) = d then ((x i).val : ℚ) * P x else 0 := by
    unfold H
    rw [mul_sum, sum_comm]
    refine sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [← sum_mul, show (d : ℚ) = ∑ i, ((x i).val : ℚ) by exact_mod_cast h.symm]
    · simp
  -- step b: every position contributes like position `0`
  have hb : ∀ i : Fin (m + 1), (∑ x : Fin (m + 1) → Fin (d + 1),
      if (∑ l, (x l).val) = d then ((x i).val : ℚ) * P x else 0) =
      ∑ x : Fin (m + 1) → Fin (d + 1),
      if (∑ l, (x l).val) = d then ((x 0).val : ℚ) * P x else 0 := by
    intro i
    rw [← (Equiv.arrowCongr (Equiv.swap 0 i) (Equiv.refl (Fin (d + 1)))).sum_comp]
    refine sum_congr rfl fun x _ => ?_
    have hs : (∑ l, ((Equiv.arrowCongr (Equiv.swap 0 i) (Equiv.refl (Fin (d + 1)))) x l).val)
        = ∑ l, (x l).val := by
      simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq,
        Equiv.symm_swap]
      exact Equiv.sum_comp (Equiv.swap 0 i) (fun l => (x l).val)
    have hp : P ((Equiv.arrowCongr (Equiv.swap 0 i) (Equiv.refl (Fin (d + 1)))) x) = P x := by
      simp only [hP, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq,
        Equiv.symm_swap]
      exact Equiv.prod_comp (Equiv.swap 0 i) (fun l => tz t (x l).val)
    have hx : (Equiv.arrowCongr (Equiv.swap 0 i) (Equiv.refl (Fin (d + 1)))) x i = x 0 := by
      simp
    rw [hs, hp, hx]
  rw [ha, sum_congr rfl fun i _ => hb i, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  congr 1
  -- step c: split off the first part
  rw [← (Fin.consEquiv (fun _ => Fin (d + 1))).sum_comp, Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun j => (j : ℚ) * tz t j * H t d m (d - j)) (d + 1)]
  refine sum_congr rfl fun j _ => ?_
  unfold H
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, hP, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  have hj := j.isLt
  by_cases h : (∑ l, (y l).val) = d - j.val
  · rw [if_pos (by omega), if_pos h]; ring
  · rw [if_neg (by omega), if_neg h, mul_zero]

lemma schurP_rec (t : ℕ → ℚ) (d : ℕ) (hd : 1 ≤ d) :
    (d : ℚ) * schurP d t = ∑ j ∈ Icc 1 d, (j : ℚ) * t j * schurP (d - j) t := by
  rw [schurP_eq, mul_sum, sum_range_succ', H_zero_parts t d d hd]
  simp only [zero_div, mul_zero, add_zero]
  have h1 : ∀ m ∈ range d, (d : ℚ) * (H t d (m + 1) d / ((m + 1).factorial : ℚ)) =
      ∑ j ∈ range (d + 1), (j : ℚ) * tz t j * (H t d m (d - j) / (m.factorial : ℚ)) := by
    intro m _
    rw [mul_div_assoc', H_succ, Nat.factorial_succ, mul_sum, sum_div]
    refine sum_congr rfl fun j _ => ?_
    have : (m.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [sum_congr rfl h1, sum_comm]
  simp_rw [← mul_sum]
  rw [sum_range_eq_Icc _ (by simp [tz])]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_Icc] at hj
  rw [show tz t j = t j by simp [tz]; omega, schurP_eq]
  congr 1
  symm
  rw [← sum_subset (range_subset_range.mpr (show d - j + 1 ≤ d by omega))]
  · refine sum_congr rfl fun m _ => ?_
    rw [H_bound t d m (d - j) (by omega)]
  · intro m hm hm'
    simp only [mem_range] at hm hm'
    rw [H_big t d m (d - j) (by omega), zero_div]

end ExpNewtonAux

open ExpNewtonAux in
theorem solution (D : ℕ) (t c : ℕ → ℚ) (h0 : c 0 = 1)
    (hrec : ∀ d, 1 ≤ d → d ≤ D →
      (d : ℚ) * c d = ∑ j ∈ Finset.Icc 1 d, (j : ℚ) * t j * c (d - j)) :
    ∀ d ≤ D, c d = schurP d t := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · rw [h0]; unfold schurP; simp
    · have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
      apply mul_left_cancel₀ hd0
      rw [hrec d hpos hd, schurP_rec t d hpos]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Icc] at hj
      rw [ih (d - j) (by omega) (by omega)]
