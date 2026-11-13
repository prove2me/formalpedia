-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:21:51.448561+00:00
-- url     : https://prove2.me/submissions/6b4a416f-5dd1-4d07-940b-9df106296275

import Mathlib
import Theorems.Thm_LocalLemmaHierarchy_Completeness_lemma_F_1

section
set_option autoImplicit false

namespace LocalLemmaHierarchy.Completeness.Dev.L35

open Finset

/-- Hölder via weighted AM-GM. -/
lemma holder {α : Type} (A : Finset α) (J : Finset ℕ) (f : ℕ → α → ℝ) (w : ℕ → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j) (hw1 : ∑ j ∈ J, w j = 1)
    (hf : ∀ j ∈ J, ∀ a ∈ A, 0 ≤ f j a) (hS : ∀ j ∈ J, 0 < ∑ a ∈ A, f j a) :
    ∑ a ∈ A, ∏ j ∈ J, f j a ^ w j ≤ ∏ j ∈ J, (∑ a ∈ A, f j a) ^ w j := by
  set S : ℕ → ℝ := fun j => ∑ a ∈ A, f j a with hSdef
  have key : ∀ a ∈ A, ∏ j ∈ J, f j a ^ w j ≤ (∏ j ∈ J, S j ^ w j) * ∑ j ∈ J, w j * (f j a / S j) := by
    intro a ha
    have h1 : ∏ j ∈ J, (f j a / S j) ^ w j ≤ ∑ j ∈ J, w j * (f j a / S j) :=
      Real.geom_mean_le_arith_mean_weighted J w _ hw hw1
        (fun j hj => div_nonneg (hf j hj a ha) (hS j hj).le)
    have h2 : ∏ j ∈ J, f j a ^ w j = (∏ j ∈ J, S j ^ w j) * ∏ j ∈ J, (f j a / S j) ^ w j := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Real.div_rpow (hf j hj a ha) (hS j hj).le]
      have : 0 < (∑ a ∈ A, f j a) ^ w j := Real.rpow_pos_of_pos (hS j hj) _
      field_simp
      rfl
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1
      (Finset.prod_nonneg fun j hj => Real.rpow_nonneg (hS j hj).le _)
  calc ∑ a ∈ A, ∏ j ∈ J, f j a ^ w j
      ≤ ∑ a ∈ A, (∏ j ∈ J, S j ^ w j) * ∑ j ∈ J, w j * (f j a / S j) := Finset.sum_le_sum key
    _ = (∏ j ∈ J, S j ^ w j) * ∑ j ∈ J, w j * (∑ a ∈ A, f j a / S j) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [← Finset.mul_sum]
    _ = ∏ j ∈ J, S j ^ w j := by
        have : ∀ j ∈ J, w j * (∑ a ∈ A, f j a / S j) = w j := by
          intro j hj
          rw [← Finset.sum_div]
          have := (hS j hj).ne'
          simp only [hSdef] at this ⊢
          rw [div_self this, mul_one]
        rw [Finset.sum_congr rfl this, hw1, mul_one]

lemma ms_pos {S : Type} (m : Multiset S) (h : S → ℝ) (hh : ∀ u, 0 < h u) :
    0 < (m.map h).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => rw [Multiset.map_cons, Multiset.prod_cons]; exact mul_pos (hh a) ih


lemma tele (Y : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (Y (j - 1) - Y j) = Y 0 - Y n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]; simp

/-- Key mean inequality. -/
lemma key (q : ℕ) (hq : 1 ≤ q) (b : ℝ) (hb1 : b < 1) (y : ℕ → ℝ)
    (hy : ∀ j ≤ q, 0 ≤ y j ∧ y j ≤ b) :
    (∏ j ∈ Finset.Icc 1 q, y (j - 1)) ^ ((1 : ℝ) / q)
      + (∏ j ∈ Finset.Icc 1 q, (1 - y j)) ^ ((1 : ℝ) / q)
      ≤ 1 + (y 0 - y q) / q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  set J := Finset.Icc 1 q with hJ
  have hmem : ∀ j ∈ J, 1 ≤ j ∧ j ≤ q := fun j hj => Finset.mem_Icc.1 hj
  let f : ℕ → Bool → ℝ := fun j a => if a then y (j - 1) else 1 - y j
  have hc : ∀ j ∈ J, 0 < 1 + (y (j - 1) - y j) := fun j hj => by
    have h1 := hy (j - 1) (by have := hmem j hj; omega)
    have h2 := hy j (hmem j hj).2
    linarith [h1.1, h2.2]
  have hH := holder (Finset.univ : Finset Bool) J f (fun _ => (1 : ℝ) / q)
    (fun j _ => by positivity)
    (by rw [Finset.sum_const, Nat.card_Icc]; simp; field_simp)
    (fun j hj a _ => by
      have h1 := hy (j - 1) (by have := hmem j hj; omega)
      have h2 := hy j (hmem j hj).2
      cases a <;> simp [f] <;> linarith [h1.1, h1.2, h2.1, h2.2])
    (fun j hj => by
      rw [Fintype.sum_bool]; simp only [f]; simp; linarith [hc j hj])
  simp only [Fintype.sum_bool, f, ↓reduceIte, Bool.false_eq_true] at hH
  have hnn1 : ∀ j ∈ J, 0 ≤ y (j - 1) := fun j hj =>
    (hy (j - 1) (by have := hmem j hj; omega)).1
  have hnn2 : ∀ j ∈ J, 0 ≤ 1 - y j := fun j hj => by
    have := hy j (hmem j hj).2; linarith [this.2]
  rw [← Real.finsetProd_rpow _ _ hnn1, ← Real.finsetProd_rpow _ _ hnn2]
  refine hH.trans ?_
  have hS : ∀ j ∈ J, (y (j - 1) + (1 - y j)) = 1 + (y (j - 1) - y j) := fun j _ => by ring
  have hAM : ∏ j ∈ J, (y (j - 1) + (1 - y j)) ^ ((1 : ℝ) / q)
      ≤ ∑ j ∈ J, (1 : ℝ) / q * (y (j - 1) + (1 - y j)) :=
    Real.geom_mean_le_arith_mean_weighted J (fun _ => (1 : ℝ) / q) _ (fun j _ => by positivity)
      (by rw [Finset.sum_const, Nat.card_Icc]; simp; field_simp)
      (fun j hj => by have := hc j hj; linarith [hS j hj])
  refine hAM.trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_congr rfl hS, Finset.sum_add_distrib]
  have hcard : (J.card : ℝ) = q := by simp [hJ]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [tele y q, hcard]
  field_simp

end LocalLemmaHierarchy.Completeness.Dev.L35

namespace LocalLemmaHierarchy.Completeness
open Finset
open LocalLemmaHierarchy.Completeness.Dev.L35

theorem chk_lemma_3_5 {S ι : Type} (A : S → Finset ι) (t : S → ι → ℝ) (C : S → ι → Multiset S)
    (ht : ∀ s, ∀ a ∈ A s, 0 < t s a) (q : ℕ) (hq : 1 ≤ q) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (Y : ℕ → S → ℝ) (hY : ∀ j ≤ q, ∀ s, 0 ≤ Y j s ∧ Y j s ≤ b)
    (hF : ∀ j, 1 ≤ j → j ≤ q → ∀ s, productRowUpdate A t C (Y j) s ≤ Y (j - 1) s) :
    let xbar : S → ℝ := fun s => 1 - (∏ j ∈ Finset.Icc 1 q, (1 - Y j s)) ^ ((1 : ℝ) / q)
    (∀ s, 0 ≤ xbar s ∧ xbar s ≤ b) ∧
    ∀ s, productRowUpdate A t C xbar s ≤ xbar s + (Y 0 s - Y q s) / q ∧
      xbar s + (Y 0 s - Y q s) / q ≤ xbar s + 1 / q := by
  intro xbar
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hYJ : ∀ j ∈ Finset.Icc 1 q, ∀ s, 0 ≤ Y j s ∧ Y j s ≤ b := fun j hj s =>
    hY j (Finset.mem_Icc.1 hj).2 s
  have hF1 := lemma_F_1 A t C ht q b hb1 Y hYJ (fun _ => (1 : ℝ) / q)
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Nat.card_Icc]; simp; field_simp)
  have hx : (fun s => 1 - ∏ j ∈ Finset.Icc 1 q, (1 - Y j s) ^ ((1 : ℝ) / q)) = xbar := by
    funext s
    simp only [xbar]
    rw [← Real.finsetProd_rpow _ _ (fun j hj => by
      have := hY j (Finset.mem_Icc.1 hj).2 s; linarith [this.2])]
  simp only [hx] at hF1
  obtain ⟨h1, h2, h3⟩ := hF1
  have h1' : ∀ s, 0 ≤ xbar s ∧ xbar s ≤ b := fun s => by
    have := congrFun hx s
    rw [← this]; exact h1 s
  refine ⟨h1', fun s => ?_⟩
  have hkey := key q hq b hb1 (fun j => Y j s) (fun j hj => hY j hj s)
  have hM0 : 0 ≤ (∏ j ∈ Finset.Icc 1 q, Y (j - 1) s) ^ ((1 : ℝ) / q) :=
    Real.rpow_nonneg (Finset.prod_nonneg fun j hj => (hY (j - 1) (by
      have := Finset.mem_Icc.1 hj; omega) s).1) _
  have hmain : productRowUpdate A t C xbar s ≤ xbar s + (Y 0 s - Y q s) / q := by
    have hxs : xbar s = 1 - (∏ j ∈ Finset.Icc 1 q, (1 - Y j s)) ^ ((1 : ℝ) / q) := rfl
    have hfin : (∏ j ∈ Finset.Icc 1 q, Y (j - 1) s) ^ ((1 : ℝ) / q) ≤ xbar s + (Y 0 s - Y q s) / q := by
      rw [hxs]; linarith
    rcases (A s).eq_empty_or_nonempty with he | hne
    · rw [h3 s he]; linarith
    · refine (h2 s hne).trans (le_trans ?_ hfin)
      rw [← Real.finsetProd_rpow _ _ (fun j hj => (hY (j - 1) (by
        have := Finset.mem_Icc.1 hj; omega) s).1)]
      refine Finset.prod_le_prod (fun j hj => Real.rpow_nonneg ?_ _) (fun j hj => ?_)
      · unfold productRowUpdate
        exact Finset.sum_nonneg fun a ha => (mul_pos (ht s a ha)
          (ms_pos _ _ (fun u => inv_pos.2 (by
            have := (hY j (Finset.mem_Icc.1 hj).2 u).2; linarith)))).le
      · refine Real.rpow_le_rpow ?_ (hF j (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 s) (by positivity)
        unfold productRowUpdate
        exact Finset.sum_nonneg fun a ha => (mul_pos (ht s a ha)
          (ms_pos _ _ (fun u => inv_pos.2 (by
            have := (hY j (Finset.mem_Icc.1 hj).2 u).2; linarith)))).le
  refine ⟨hmain, ?_⟩
  have := (hY 0 (by omega) s).2
  have := (hY q le_rfl s).1
  have e : (Y 0 s - Y q s) / q ≤ 1 / q := by
    apply div_le_div_of_nonneg_right _ hqpos.le; linarith
  linarith

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_lemma_3_5 := @LocalLemmaHierarchy.Completeness.chk_lemma_3_5
