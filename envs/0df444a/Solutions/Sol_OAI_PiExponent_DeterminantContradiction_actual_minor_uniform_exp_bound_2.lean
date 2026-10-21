-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.actual_minor_uniform_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:25:16.646538+00:00
-- url     : https://prove2.me/submissions/6c4f0147-1324-4dbf-b6a4-9ae2857c3094

import Definitions.Def_OAI_PiExponent_AnalyticRemainder
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_expansion_and_card
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_index_geometry
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_scalar_product_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_period_determinant_bound
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_weighted_occupancy_dichotomy
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) :
    ‖(actualMinor d H selection).det‖ ≤
      Real.exp ((actualRowCount d H : ℝ) * H *
        (d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
  classical
  let M : ℝ := actualRowCount d H
  let W : ℝ := M * H
  let Q : ℝ := translationEnvelope d.m d.v0 H
  let rho : ℝ := collisionAllowance (actualRowCount d H) H
  let B : ℝ := (d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H
  let R : ℝ := max (-collisionRate d H) (-nu * B)
  let E : ℝ := d.analyticError + rho + R
  have hW : 0 ≤ W := mul_nonneg (Nat.cast_nonneg _) hH.le
  have hv : 0 < (d.v0 : ℝ) := d.v0_pos
  have hQ : 0 < Q := by
    dsimp [Q, translationEnvelope]
    positivity
  have hc : 0 ≤ collisionConstant := by
    unfold collisionConstant
    exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have hA : 0 ≤ (d.base.A : ℝ) :=
    (d.base.theta_pos.trans d.base.theta_lt_A).le
  rcases expansion_and_card d hH selection with ⟨hexpansion, hcard⟩
  rcases index_geometry d hH with ⟨hN, hweight, hcapacity, hselected⟩
  have hcollision : W * (-collisionRate d H) =
      -collisionConstant * (d.base.eta ^ 2 * M ^ 2 / (lowIndexCount d H : ℝ)) := by
    dsimp only [W, M]
    unfold collisionRate
    field_simp [ne_of_gt hH, ne_of_gt hN] <;> ring
  have hterm : ∀ f : Family d H, ‖term d selection f‖ ≤ Real.exp (W * E) := by
    intro f
    by_cases hz : (∏ r : Row d H, scalar d r (f r)) = 0
    · rw [term, hz, zero_mul, norm_zero]
      exact (Real.exp_pos _).le
    let S : ℝ := ∑ r : Row d H, weight d (f r).1
    let Z : ℝ := ∑ a : Index d H,
      (((Finset.univ : Finset (Row d H)).filter (fun r => (f r).1 = a)).card : ℝ) ^ 2
    have hmono : W * actualMean d H ≤ S := hselected f hz
    have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsplit :=
      OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy
        (fun r : Row d H => (f r).1) (fun a : Index d H => weight d a)
        hH hA d.base.eta_pos.le hN hweight (hselected f hz) hcapacity
    change (d.base.eta ^ 2 * M ^ 2 / (lowIndexCount d H : ℝ) ≤ Z) ∨
      (W * B ≤ S - W * actualMean d H) at hsplit
    have hrate : -nu * (S - W * actualMean d H) - collisionConstant * Z ≤ W * R := by
      rcases hsplit with hlow | hhigh
      · have hsc : -nu * (S - W * actualMean d H) ≤ 0 := by
          nlinarith [mul_nonneg hnu (sub_nonneg.mpr hmono)]
        have hcoll : -collisionConstant * Z ≤ W * (-collisionRate d H) := by
          rw [hcollision]
          nlinarith [mul_le_mul_of_nonneg_left hlow hc]
        have hmax : W * (-collisionRate d H) ≤ W * R :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hW
        linarith
      · have hsc : -nu * (S - W * actualMean d H) ≤ W * (-nu * B) := by
          nlinarith [mul_le_mul_of_nonneg_left hhigh hnu]
        have hcoll : -collisionConstant * Z ≤ 0 := by
          nlinarith [mul_nonneg hc hZ]
        have hmax : W * (-nu * B) ≤ W * R :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hW
        linarith
    have hs := scalar_product_bound d hnu hH f
    have hd := period_determinant_bound d hH selection f
    change ‖∏ r : Row d H, scalar d r (f r)‖ ≤
      Real.exp (-nu * (S - W * actualMean d H) + W * d.translationError) at hs
    change ‖(coefficientMatrix d selection f).det‖ ≤
      Real.exp (-collisionConstant * Z + W * (d.holomorphicError + rho)) at hd
    calc
      ‖term d selection f‖ =
          ‖∏ r : Row d H, scalar d r (f r)‖ * ‖(coefficientMatrix d selection f).det‖ := by
        rw [term, norm_mul]
      _ ≤ Real.exp (-nu * (S - W * actualMean d H) + W * d.translationError) *
          Real.exp (-collisionConstant * Z + W * (d.holomorphicError + rho)) :=
        mul_le_mul hs hd (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (W * E) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp only [E]
        rw [AdmissibleParameters.analyticError]
        nlinarith only [hrate]
  have hpower : Q ^ actualRowCount d H = Real.exp (M * Real.log Q) := by
    dsimp only [M]
    rw [Real.exp_nat_mul, Real.exp_log hQ]
  have hrem : analyticRemainder d H = rho + Real.log Q / H := rfl
  calc
    ‖(actualMinor d H selection).det‖ = ‖∑ f : Family d H, term d selection f‖ := by
      rw [hexpansion]
    _ ≤ ∑ f : Family d H, ‖term d selection f‖ := norm_sum_le _ _
    _ ≤ ∑ _f : Family d H, Real.exp (W * E) :=
      Finset.sum_le_sum fun f _ => hterm f
    _ = (Fintype.card (Family d H) : ℝ) * Real.exp (W * E) := by simp
    _ ≤ Q ^ actualRowCount d H * Real.exp (W * E) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = Real.exp (M * Real.log Q + W * E) := by
      rw [hpower, ← Real.exp_add]
    _ = Real.exp ((actualRowCount d H : ℝ) * H *
        (d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
      congr 1
      change M * Real.log Q + W * E = W * (d.analyticError + analyticRemainder d H + R)
      rw [hrem]
      dsimp only [E, W]
      field_simp [ne_of_gt hH] <;> ring