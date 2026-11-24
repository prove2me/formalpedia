-- Prove2me | solution 1 for KissingNumber.kissing_number_one
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T21:43:08.71267+00:00
-- url     : https://prove2.me/submissions/8c8e33ff-7c6d-44dc-8160-8980aaa3039f

import Definitions.Def_KissingNumber
set_option autoImplicit false
open KissingNumber
open scoped InnerProductSpace

private lemma norm_one_dim (x : Ambient 1) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

private lemma coord_mem (x : Ambient 1) (hx : ‖x‖ = 1) : x 0 ∈ ({-1, 1} : Finset ℝ) := by
  rw [norm_one_dim] at hx
  rcases abs_eq (zero_le_one' ℝ) |>.mp hx with h | h <;> simp [h]

private lemma card_le_two (C : KissingConfig 1) : C.points.card ≤ 2 := by
  have hinj : Set.InjOn (fun x : Ambient 1 => x 0) (C.points : Set (Ambient 1)) := by
    intro x _ y _ hxy
    ext i
    fin_cases i
    exact hxy
  calc C.points.card ≤ ({-1, 1} : Finset ℝ).card :=
        Finset.card_le_card_of_injOn (fun x : Ambient 1 => x 0)
          (fun x hx => coord_mem x (C.unit_norm x hx)) hinj
    _ ≤ 2 := Finset.card_le_two

private noncomputable def e : Ambient 1 := EuclideanSpace.single 0 1

private lemma norm_e : ‖e‖ = 1 := by simp [e]

private lemma norm_neg_e : ‖-e‖ = 1 := by rw [norm_neg, norm_e]

private lemma e_ne : e ≠ -e := by
  intro h
  have h2 := congrArg (fun v : Ambient 1 => v 0) h
  simp [e] at h2
  norm_num at h2

private lemma inner_e_neg : ⟪e, -e⟫_ℝ = -1 := by
  rw [inner_neg_right, real_inner_self_eq_norm_sq, norm_e]; norm_num

private lemma inner_neg_e : ⟪-e, e⟫_ℝ = -1 := by
  rw [real_inner_comm, inner_e_neg]

theorem solution : kissingNumber 1 = (2 : ℕ∞) := by
  let C : KissingConfig 1 :=
    { points := {e, -e}
      unit_norm := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact norm_e
        · exact norm_neg_e
      inner_le := by
        intro x hx y hy hxy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · rw [inner_e_neg]; norm_num
        · rw [inner_neg_e]; norm_num
        · exact absurd rfl hxy }
  have hcard : C.points.card = 2 := Finset.card_pair e_ne
  apply le_antisymm
  · refine iSup_le fun D => ?_
    exact_mod_cast card_le_two D
  · have := le_iSup (fun C : KissingConfig 1 => (C.points.card : ℕ∞)) C
    simp only [hcard] at this
    exact_mod_cast this
