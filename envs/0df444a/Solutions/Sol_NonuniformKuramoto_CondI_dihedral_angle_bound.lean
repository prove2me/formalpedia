-- Prove2me | solution 1 for NonuniformKuramoto.CondI.dihedral_angle_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:08:54.813282+00:00
-- url     : https://prove2.me/submissions/0e6f34a7-d431-4fe9-83db-147e3f45e563

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants
set_option autoImplicit false
open NonuniformKuramoto.CondI

theorem solution {n : ℕ} (D : Fin n → ℝ) (hD : ∀ i, 0 < D i)
    (δ : Fin n → ℝ) (hδ : ∑ i, D i * δ i = 0) :
    norm2 (fun i => δ i - (∑ j, δ j) / n) ≤ norm2 δ ∧
    norm2 δ * cosAngleD D ≤ norm2 (fun i => δ i - (∑ j, δ j) / n) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [norm2, cosAngleD]
  have hn : (0:ℝ) < n := by exact_mod_cast hpos
  haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  set T := ∑ j, δ j with hT
  set μ := T / n with hμ
  set s := ∑ i, D i with hs
  set S2 := ∑ i, D i ^ 2 with hS2
  set b := ∑ i, δ i ^ 2 with hb
  set a := ∑ i, (δ i - μ) ^ 2 with ha
  have hcard : ∑ _i : Fin n, (1:ℝ) = n := by simp
  have h1 : a = b - T ^ 2 / n := by
    have : ∀ i, (δ i - μ) ^ 2 = δ i ^ 2 - 2 * μ * δ i + μ ^ 2 := fun i => by ring
    simp only [ha, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hT, ← hb]
    rw [hμ]; field_simp; ring
  have h3 : ∑ i, (δ i - μ) * (D i - s / n) = -(s * T / n) := by
    have : ∀ i, (δ i - μ) * (D i - s / n) = D i * δ i - (s / n) * δ i - μ * D i + μ * (s / n) := fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hT, ← hs, hδ]
    rw [hμ]; field_simp; ring
  have h4 : ∑ i, (D i - s / n) ^ 2 = S2 - s ^ 2 / n := by
    have : ∀ i, (D i - s / n) ^ 2 = D i ^ 2 - 2 * (s / n) * D i + (s / n) ^ 2 := fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hs, ← hS2]
    field_simp; ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => δ i - μ) (fun i => D i - s / n)
  rw [h3, h4] at hcs
  have hb_ge : 0 ≤ b := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ha_ge : 0 ≤ a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hS2pos : 0 < S2 := Finset.sum_pos (fun i _ => pow_pos (hD i) 2) Finset.univ_nonempty
  have hspos : 0 < s := Finset.sum_pos (fun i _ => hD i) Finset.univ_nonempty
  have hsimp : (fun i => δ i - (∑ j, δ j) / n) = fun i => δ i - μ := rfl
  rw [hsimp]
  unfold norm2 cosAngleD
  constructor
  · apply Real.sqrt_le_sqrt
    have : 0 ≤ T ^ 2 / n := by positivity
    change a ≤ b
    linarith
  · have hx : 0 ≤ Real.sqrt b * (s / (Real.sqrt n * Real.sqrt S2)) := by positivity
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hb_ge, Real.sq_sqrt hn.le, Real.sq_sqrt hS2pos.le]
    have hcs' : (s * T / n) ^ 2 ≤ a * (S2 - s ^ 2 / n) := by
      have := hcs
      rw [neg_sq] at this
      exact this
    have hbe : b = a + T ^ 2 / n := by linarith
    have e1 : (n:ℝ) * (s * T / n) ^ 2 = s ^ 2 * T ^ 2 / n := by field_simp
    have e2 : (n:ℝ) * (a * (S2 - s ^ 2 / n)) = a * (n * S2) - a * s ^ 2 := by field_simp
    have e3 : b * s ^ 2 = a * s ^ 2 + s ^ 2 * T ^ 2 / n := by rw [hbe]; ring
    have := mul_le_mul_of_nonneg_left hcs' hn.le
    have key : b * s ^ 2 ≤ a * (n * S2) := by linarith
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    linarith
