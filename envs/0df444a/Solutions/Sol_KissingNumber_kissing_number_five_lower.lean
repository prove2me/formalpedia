-- Prove2me | solution 1 for KissingNumber.kissing_number_five_lower
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:34:15.788907+00:00
-- url     : https://prove2.me/submissions/21c56dfd-4486-44a5-a473-0a89a57f218d

import Definitions.Def_KissingNumber
set_option autoImplicit false
open KissingNumber
open scoped InnerProductSpace

private def sg (b : Bool) : ℝ := if b then 1 else -1

private lemma sg_mul_le (a b : Bool) : sg a * sg b ≤ 1 := by
  cases a <;> cases b <;> norm_num [sg]

private lemma sg_mul_self (a : Bool) : sg a * sg a = 1 := by
  cases a <;> norm_num [sg]

private lemma sg_add_le (a b c e : Bool) (h : ¬ (a = c ∧ b = e)) :
    sg a * sg c + sg b * sg e ≤ 1 := by
  cases a <;> cases b <;> cases c <;> cases e <;> simp_all [sg] <;> norm_num

private lemma inner_single_single (i k : Fin 5) (a b : ℝ) :
    ⟪EuclideanSpace.single i a, EuclideanSpace.single k b⟫_ℝ = if i = k then a * b else 0 := by
  rw [EuclideanSpace.inner_single_left, PiLp.single_apply]
  split_ifs <;> simp_all

private noncomputable def vD (p : Fin 5 × Fin 5 × Bool × Bool) : Ambient 5 :=
  (Real.sqrt 2)⁻¹ • (EuclideanSpace.single p.1 (sg p.2.2.1) + EuclideanSpace.single p.2.1 (sg p.2.2.2))

private def idxD : Finset (Fin 5 × Fin 5 × Bool × Bool) := Finset.univ.filter (fun p => p.1 < p.2.1)

private lemma idxD_card : idxD.card = 40 := by decide

private lemma inner_vD (i j k l : Fin 5) (s t u w : Bool) :
    ⟪vD (i, j, s, t), vD (k, l, u, w)⟫_ℝ = (1 / 2) *
      ((if i = k then sg s * sg u else 0) + (if i = l then sg s * sg w else 0) +
       ((if j = k then sg t * sg u else 0) + (if j = l then sg t * sg w else 0))) := by
  simp only [vD, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    inner_single_single]
  have h2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp only [RCLike.conj_to_real]
  rw [← h2]; ring

private lemma inner_vD_self (p : Fin 5 × Fin 5 × Bool × Bool) (hp : p ∈ idxD) :
    ⟪vD p, vD p⟫_ℝ = 1 := by
  obtain ⟨i, j, s, t⟩ := p
  simp only [idxD, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rw [inner_vD, if_pos rfl, if_pos rfl, if_neg (ne_of_lt hp), if_neg (ne_of_gt hp),
    sg_mul_self, sg_mul_self]
  norm_num

private lemma inner_vD_le (p q : Fin 5 × Fin 5 × Bool × Bool) (hp : p ∈ idxD) (hq : q ∈ idxD)
    (hpq : p ≠ q) : ⟪vD p, vD q⟫_ℝ ≤ 1 / 2 := by
  obtain ⟨i, j, s, t⟩ := p
  obtain ⟨k, l, u, w⟩ := q
  simp only [idxD, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  rw [inner_vD]
  have key : ((if i = k then sg s * sg u else 0) + (if i = l then sg s * sg w else 0) +
       ((if j = k then sg t * sg u else 0) + (if j = l then sg t * sg w else 0))) ≤ 1 := by
    have a1 := sg_mul_le s u
    have a2 := sg_mul_le s w
    have a3 := sg_mul_le t u
    have a4 := sg_mul_le t w
    split_ifs with h1 h2 h3 h4 h4 h3 h4 h4 h2 h3 h4 h4 h3 h4 h4 <;>
      first
      | (subst_vars; exact absurd hq (lt_asymm hp))
      | (subst_vars; exact absurd hq (lt_irrefl _))
      | (subst_vars; exact absurd hp (lt_irrefl _))
      | linarith
      | (subst_vars
         have := sg_add_le s t u w (fun h => hpq (by rw [h.1, h.2]))
         linarith)
  linarith

theorem solution : (40 : ℕ∞) ≤ kissingNumber 5 := by
  have hinj : Set.InjOn vD idxD := by
    intro p hp q hq hpq
    by_contra hne
    have h1 := inner_vD_le p q hp hq hne
    rw [hpq, inner_vD_self q hq] at h1
    norm_num at h1
  let C : KissingConfig 5 :=
    { points := idxD.image vD
      unit_norm := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
        have h := inner_vD_self p hp
        rw [real_inner_self_eq_norm_sq] at h
        have h0 := norm_nonneg (vD p)
        nlinarith
      inner_le := by
        intro x hx y hy hxy
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
        exact inner_vD_le p q hp hq (fun h => hxy (by rw [h])) }
  have hcard : C.points.card = 40 := by
    show (idxD.image vD).card = 40
    rw [Finset.card_image_of_injOn hinj, idxD_card]
  have := le_iSup (fun C : KissingConfig 5 => (C.points.card : ℕ∞)) C
  simp only [hcard] at this
  exact this
