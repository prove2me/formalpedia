-- Prove2me | solution 1 for HarmonicGames.UniformMixed.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:43:41.38074+00:00
-- url     : https://prove2.me/submissions/2bf4e5d6-796d-408d-8bfc-5e606fb5d5a3

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Games
import Definitions.Def_HarmonicGames_GenericPure_Games
set_option autoImplicit false

open HarmonicGames.Decomposition
open scoped InnerProductSpace

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)]
    (X : HarmonicGames.Decomposition.Flow E) (S : Finset (∀ k, E k)) :
    ∑ p ∈ S, (LinearMap.adjoint (HarmonicGames.Decomposition.delta0 (HarmonicGames.Decomposition.gameGraph E)) X) p = -∑ p ∈ S, ∑ q ∈ Sᶜ, X p q := by
  classical
  set G := gameGraph E with hG
  let f : C0 (∀ k, E k) := WithLp.toLp 2 (fun p => if p ∈ S then (1:ℝ) else 0)
  have hf : ∀ p, f p = if p ∈ S then (1:ℝ) else 0 := fun p => rfl
  have hanti : ∀ p q, X q p = - X p q := by
    intro p q
    by_cases h : G.Adj p q
    · exact C1.antisymm G X h
    · have h' : ¬ G.Adj q p := fun h2 => h h2.symm
      rw [C1.eq_zero_of_not_adj G X h, C1.eq_zero_of_not_adj G X h']; simp
  have h1 : ⟪LinearMap.adjoint (delta0 G) X, f⟫_ℝ = ⟪X, delta0 G f⟫_ℝ :=
    LinearMap.adjoint_inner_left (delta0 G) f X
  have hL : ⟪LinearMap.adjoint (delta0 G) X, f⟫_ℝ
      = ∑ p ∈ S, (LinearMap.adjoint (delta0 G) X) p := by
    rw [PiLp.inner_apply]
    simp only [hf]
    have hx : ∀ x : (∀ k, E k), ⟪(LinearMap.adjoint (delta0 G) X).ofLp x, (if x ∈ S then (1:ℝ) else 0)⟫_ℝ
        = if x ∈ S then (LinearMap.adjoint (delta0 G) X).ofLp x else 0 := by
      intro x; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun x _ => hx x), ← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hR : ⟪X, delta0 G f⟫_ℝ = (1 / 2 : ℝ) * ∑ p, ∑ q, X p q * (f q - f p) := by
    show innerC1 G X (delta0 G f) = _
    unfold innerC1
    congr 1
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    by_cases h : G.Adj p q
    · simp only [h, if_true]
      show X p q * (((if G.Adj p q then (1:ℝ) else 0)) * (f.ofLp q - f.ofLp p)) = _
      simp [h]
    · simp [h, C1.eq_zero_of_not_adj G X h]
  have hsum : ∑ p, ∑ q, X p q * (f q - f p) = -2 * ∑ p, f p * ∑ q, X p q := by
    have e1 : ∑ p, ∑ q, X p q * f q = - ∑ p, f p * ∑ q, X p q := by
      rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro q _
      rw [← Finset.sum_mul]
      have : ∑ p, X p q = - ∑ p, X q p := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro p _; exact hanti q p
      rw [this]; ring
    have e2 : ∑ p, ∑ q, X p q * f p = ∑ p, f p * ∑ q, X p q := by
      apply Finset.sum_congr rfl; intro p _
      rw [← Finset.sum_mul]; ring
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e1, e2]; ring
  have hmain : ∑ p, f p * ∑ q, X p q = ∑ p ∈ S, ∑ q ∈ Sᶜ, X p q := by
    have : ∀ p, f p * ∑ q, X p q = if p ∈ S then ∑ q, X p q else 0 := by
      intro p; rw [hf]; split_ifs <;> simp
    simp only [this]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hz : ∑ p ∈ S, ∑ q ∈ S, X p q = 0 := by
      have : ∑ p ∈ S, ∑ q ∈ S, X p q = - ∑ p ∈ S, ∑ q ∈ S, X p q := by
        calc ∑ p ∈ S, ∑ q ∈ S, X p q = ∑ q ∈ S, ∑ p ∈ S, X p q := Finset.sum_comm
          _ = ∑ q ∈ S, ∑ p ∈ S, -X q p := by
            apply Finset.sum_congr rfl; intro q _
            apply Finset.sum_congr rfl; intro p _
            exact hanti q p
          _ = - ∑ p ∈ S, ∑ q ∈ S, X p q := by simp [Finset.sum_neg_distrib]
      linarith
    have : ∀ p ∈ S, ∑ q, X p q = ∑ q ∈ S, X p q + ∑ q ∈ Sᶜ, X p q := by
      intro p _; rw [Finset.sum_add_sum_compl]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hz]; ring
  rw [← hL, h1, hR, hsum, hmain]; ring
