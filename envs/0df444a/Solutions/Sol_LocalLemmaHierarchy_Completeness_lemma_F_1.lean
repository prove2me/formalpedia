-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.lemma_F_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:21:50.828532+00:00
-- url     : https://prove2.me/submissions/43d1e906-d9e2-4aa2-bde4-904eae71d2af

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory

section
set_option autoImplicit false

namespace LocalLemmaHierarchy.Completeness.Dev.F1

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

lemma ms_eq {S : Type} (J : Finset ℕ) (w : ℕ → ℝ) (g : ℕ → S → ℝ) (hg : ∀ j ∈ J, ∀ u, 0 < g j u)
    (m : Multiset S) :
    (m.map fun u => (∏ j ∈ J, g j u ^ w j)⁻¹).prod
      = ∏ j ∈ J, ((m.map fun u => (g j u)⁻¹).prod) ^ w j := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih]
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Real.mul_rpow (inv_nonneg.2 (hg j hj a).le)
      (ms_pos m _ (fun u => inv_pos.2 (hg j hj u))).le, Real.inv_rpow (hg j hj a).le]

end LocalLemmaHierarchy.Completeness.Dev.F1

namespace LocalLemmaHierarchy.Completeness
open Finset
open LocalLemmaHierarchy.Completeness.Dev.F1

theorem chk_lemma_F_1 {S ι : Type} (A : S → Finset ι) (t : S → ι → ℝ) (C : S → ι → Multiset S)
    (ht : ∀ s, ∀ a ∈ A s, 0 < t s a) (q : ℕ) (b : ℝ) (hb : b < 1) (Y : ℕ → S → ℝ)
    (hY : ∀ j ∈ Finset.Icc 1 q, ∀ s, 0 ≤ Y j s ∧ Y j s ≤ b)
    (w : ℕ → ℝ) (hw : ∀ j ∈ Finset.Icc 1 q, 0 < w j) (hw1 : ∑ j ∈ Finset.Icc 1 q, w j = 1) :
    let x : S → ℝ := fun s => 1 - ∏ j ∈ Finset.Icc 1 q, (1 - Y j s) ^ w j
    (∀ s, 0 ≤ x s ∧ x s ≤ b) ∧
    (∀ s, (A s).Nonempty →
      productRowUpdate A t C x s ≤ ∏ j ∈ Finset.Icc 1 q, productRowUpdate A t C (Y j) s ^ w j) ∧
    (∀ s, A s = ∅ → productRowUpdate A t C x s = 0) := by
  intro x
  set J := Finset.Icc 1 q with hJ
  have hg : ∀ j ∈ J, ∀ u, 0 < 1 - Y j u := fun j hj u => by
    have := hY j hj u; linarith [this.2]
  have hP : ∀ u, 0 < ∏ j ∈ J, (1 - Y j u) ^ w j := fun u =>
    Finset.prod_pos fun j hj => Real.rpow_pos_of_pos (hg j hj u) _
  refine ⟨?_, ?_, ?_⟩
  · intro s
    constructor
    · have : ∏ j ∈ J, (1 - Y j s) ^ w j ≤ 1 :=
        Finset.prod_le_one (fun j hj => Real.rpow_nonneg (hg j hj s).le _)
          (fun j hj => Real.rpow_le_one (hg j hj s).le (by linarith [(hY j hj s).1])
            (hw j hj).le)
      simp only [x]; linarith
    · have : (1 - b) ≤ ∏ j ∈ J, (1 - Y j s) ^ w j := by
        calc (1 - b) = (1 - b) ^ (∑ j ∈ J, w j) := by rw [hw1, Real.rpow_one]
          _ = ∏ j ∈ J, (1 - b) ^ w j := Real.rpow_sum_of_pos (by linarith) _ _
          _ ≤ _ := Finset.prod_le_prod (fun j hj => Real.rpow_nonneg (by linarith) _)
              (fun j hj => Real.rpow_le_rpow (by linarith) (by linarith [(hY j hj s).2])
                (hw j hj).le)
      simp only [x]; linarith
  · intro s hs
    have hxe : ∀ u, 1 - x u = ∏ j ∈ J, (1 - Y j u) ^ w j := fun u => by simp only [x, sub_sub_cancel, hJ]
    -- the row-term identity
    have hterm : ∀ a ∈ A s, t s a * ((C s a).map (fun u => (1 - x u)⁻¹)).prod
        = ∏ j ∈ J, (t s a * ((C s a).map (fun u => (1 - Y j u)⁻¹)).prod) ^ w j := by
      intro a ha
      have e1 : ((C s a).map (fun u => (1 - x u)⁻¹)).prod
          = ∏ j ∈ J, (((C s a).map fun u => (1 - Y j u)⁻¹).prod) ^ w j := by
        simp only [hxe]
        exact ms_eq J w (fun j u => 1 - Y j u) hg _
      rw [e1]
      have e2 : t s a = ∏ j ∈ J, t s a ^ w j := by
        rw [← Real.rpow_sum_of_pos (ht s a ha), hw1, Real.rpow_one]
      conv_lhs => rw [e2]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Real.mul_rpow (ht s a ha).le
        (ms_pos _ _ (fun u => inv_pos.2 (hg j hj u))).le]
    have hpos : ∀ j ∈ J, ∀ a ∈ A s, 0 ≤ t s a * ((C s a).map (fun u => (1 - Y j u)⁻¹)).prod :=
      fun j hj a ha => (mul_pos (ht s a ha)
        (ms_pos _ _ (fun u => inv_pos.2 (hg j hj u)))).le
    have hS : ∀ j ∈ J, 0 < ∑ a ∈ A s, t s a * ((C s a).map (fun u => (1 - Y j u)⁻¹)).prod :=
      fun j hj => Finset.sum_pos (fun a ha => mul_pos (ht s a ha)
        (ms_pos _ _ (fun u => inv_pos.2 (hg j hj u)))) hs
    unfold productRowUpdate
    rw [Finset.sum_congr rfl hterm]
    exact holder (A s) J (fun j a => t s a * ((C s a).map (fun u => (1 - Y j u)⁻¹)).prod) w
      (fun j hj => (hw j hj).le) hw1 hpos hS
  · intro s hs
    simp [productRowUpdate, hs]

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_lemma_F_1 := @LocalLemmaHierarchy.Completeness.chk_lemma_F_1
