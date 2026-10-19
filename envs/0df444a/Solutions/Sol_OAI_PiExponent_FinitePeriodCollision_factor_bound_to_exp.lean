-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.factor_bound_to_exp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:17:34.126978+00:00
-- url     : https://prove2.me/submissions/f218878b-feda-4d28-8344-085c2aae9a57

import Mathlib
import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation


theorem solution
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (ell : ι → ℕ) {H A v : ℝ}
    (hH : 0 < H) (hv : 0 < v)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v) :
    (((Fintype.card ι).factorial : ℝ) *
        (Real.exp (H * A)) ^ Fintype.card ι * (2 : ℝ) ^ (∑ r, ell r)) *
      (Real.exp (-Real.log 2 / 2)) ^
        (∑ b : κ, (((Finset.univ : Finset ι).filter (fun r => group r = b)).card).choose 2) *
      ((1 - Real.exp (-Real.log 2 / 2))⁻¹) ^ Fintype.card ι ≤
    Real.exp (-(Real.log 2 / 4) *
      (∑ b : κ, ((((Finset.univ : Finset ι).filter
        (fun r => group r = b)).card : ℝ) ^ 2)) +
      (Fintype.card ι : ℝ) * H *
        (A + Real.log 2 / v + collisionAllowance (Fintype.card ι) H)) := by
  classical
  set M := Fintype.card ι with hM
  set S := ∑ r, ell r with hS
  set n : κ → ℕ := fun b => ((Finset.univ : Finset ι).filter (fun r => group r = b)).card with hn
  set q := Real.exp (-Real.log 2 / 2) with hq
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq1 : q < 1 := by rw [hq, ← Real.exp_zero, Real.exp_lt_exp]; linarith
  have hq0 : 0 < q := Real.exp_pos _
  have h1q : 0 < 1 - q := by linarith
  have hsumn : ∑ b, (n b : ℝ) = M := by
    have := (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset ι)) (t := Finset.univ)
      (f := group) (fun _ _ => Finset.mem_univ _))
    rw [hM, ← Finset.card_univ, this]; push_cast; rfl
  have hC : ((∑ b, (n b).choose 2 : ℕ) : ℝ) = ((∑ b, (n b : ℝ) ^ 2) - M) / 2 := by
    push_cast
    simp only [Nat.cast_choose_two]
    rw [← hsumn, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun b _ => by ring)
  -- factor bounds
  have hF : ((M.factorial : ℕ) : ℝ) ≤ Real.exp (M * Real.log M) := by
    rcases Nat.eq_zero_or_pos M with h0 | hpos
    · rw [h0]; simp
    · have : ((M.factorial : ℕ) : ℝ) ≤ (M : ℝ) ^ M := by exact_mod_cast Nat.factorial_le_pow M
      refine this.trans (le_of_eq ?_)
      rw [← Real.exp_log (show (0:ℝ) < (M:ℝ) ^ M by positivity), Real.log_pow]
  have hE : (Real.exp (H * A)) ^ M = Real.exp (M * (H * A)) := by
    rw [← Real.exp_nat_mul]
  have hT : (2 : ℝ) ^ S ≤ Real.exp (M * H * (Real.log 2 / v)) := by
    have : (2 : ℝ) ^ S = Real.exp (S * Real.log 2) := by
      rw [← Real.exp_log (show (0:ℝ) < 2 ^ S by positivity), Real.log_pow]
    rw [this]
    apply Real.exp_le_exp.2
    have h2 : (S : ℝ) ≤ M * H / v := hell
    have : M * H * (Real.log 2 / v) = (M * H / v) * Real.log 2 := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right h2 hl2.le
  have hG : q ^ (∑ b, (n b).choose 2) =
      Real.exp (-(Real.log 2 / 4) * ((∑ b, (n b : ℝ) ^ 2) - M)) := by
    rw [hq, ← Real.exp_nat_mul, hC]
    congr 1; ring
  have hU : ((1 - q)⁻¹) ^ M = Real.exp (-(M * Real.log (1 - q))) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log h1q, inv_pow]
  calc ((M.factorial : ℝ) * (Real.exp (H * A)) ^ M * (2 : ℝ) ^ S) * q ^ (∑ b, (n b).choose 2) *
        ((1 - q)⁻¹) ^ M
      ≤ (Real.exp (M * Real.log M) * Real.exp (M * (H * A)) * Real.exp (M * H * (Real.log 2 / v))) *
          Real.exp (-(Real.log 2 / 4) * ((∑ b, (n b : ℝ) ^ 2) - M)) *
          Real.exp (-(M * Real.log (1 - q))) := by
        rw [hG, hU, hE]
        gcongr
    _ = Real.exp (-(Real.log 2 / 4) * (∑ b, (n b : ℝ) ^ 2) +
          (M : ℝ) * H * (A + Real.log 2 / v + collisionAllowance M H)) := by
        simp only [← Real.exp_add]
        congr 1
        unfold collisionAllowance
        rw [← hq]
        field_simp
        ring

