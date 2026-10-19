-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.period_determinant_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-19T03:11:10.484795+00:00
-- url     : https://prove2.me/submissions/782b9b32-e1d8-4f43-a47b-df805a41317b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coefficient_determinant_factor_bound
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_factor_bound_to_exp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : Family d H) :
    ‖(coefficientMatrix d selection f).det‖ ≤
      Real.exp (-collisionConstant *
        (∑ a : Index d H,
          (((Finset.univ : Finset (Row d H)).filter
            (fun r => (f r).1 = a)).card : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + collisionAllowance (actualRowCount d H) H)) := by
  classical
  let ell : Row d H → ℕ := fun r => r.2.1 0 - ((f r).2.2 : ℕ)
  have hw (i : Fin d.m) :
      d.wstar ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by
    simpa only [d.x_log, MatrixArithmetic.logWeights, finiteDenominators]
      using d.wstar_lower i
  have hcol (c : Row d H) :
      (d.w0 : ℝ) * ((selection c).1 0 : ℝ) +
        ∑ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i *
          ((selection c).1 i.succ : ℝ) ≤ H := by
    have hm := (selection c).2
    change (selection c).1 ∈ realWeightedSimplex
      (InterpolationMatrix.columnWeights (d.w0 : ℝ)
        (MatrixArithmetic.logWeights (finiteDenominators d))) H at hm
    have hs := (Finset.mem_filter.mp hm).2
    simpa only [Fin.sum_univ_succ, InterpolationMatrix.columnWeights,
      Fin.cases_zero, Fin.cases_succ] using hs
  have horder (r : Row d H) : (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) := by
    have hm := r.2.2
    change r.2.1 ∈ strictWeightedSimplex
      (InterpolationMatrix.rowWeights (d.v0 : ℝ) (d.base.theta : ℝ)
        (MatrixArithmetic.logWeights (finiteDenominators d))) H at hm
    have hs := (Finset.mem_filter.mp hm).2
    have hs' :
        (d.v0 : ℝ) * (r.2.1 0 : ℝ) +
          ∑ i : Fin d.m,
            (MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ)) *
              (r.2.1 i.succ : ℝ) < H := by
      simpa only [Fin.sum_univ_succ, InterpolationMatrix.rowWeights,
        Fin.cases_zero, Fin.cases_succ] using hs
    have hnonneg : 0 ≤ ∑ i : Fin d.m,
        (MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ)) *
          (r.2.1 i.succ : ℝ) := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg
        (div_nonneg (d.wstar_pos.le.trans (hw i)) d.base.theta_pos.le)
        (Nat.cast_nonneg _)
    apply (le_div_iff₀ d.v0_pos).mpr
    nlinarith
  have hell :
      ((Finset.univ.sum ell : ℕ) : ℝ) ≤
        (Fintype.card (Row d H) : ℝ) * H / (d.v0 : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ r : Row d H, H / (d.v0 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        change ((r.2.1 0 - ((f r).2.2 : ℕ) : ℕ) : ℝ) ≤ H / (d.v0 : ℝ)
        exact le_trans
          (Nat.cast_le.mpr (Nat.sub_le (r.2.1 0) ((f r).2.2 : ℕ))) (horder r)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hb := OAI.PiExponent.FinitePeriodCollision.coefficient_determinant_factor_bound
    (fun r : Row d H => (f r).1) (fun a : Index d H => a.1)
    (fun r : Row d H => r.1.val)
    ell
    (fun c : Row d H => (selection c).1 0)
    (fun (c : Row d H) (i : Fin d.m) => (selection c).1 i.succ)
    (MatrixArithmetic.logWeights (finiteDenominators d))
    (K := d.K) (H := H) (w0 := (d.w0 : ℝ)) (wstar := d.wstar)
    (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) hH d.w0_pos d.wstar_pos hw
    (fun r => r.1.isLt) hcol
  have he := OAI.PiExponent.FinitePeriodCollision.factor_bound_to_exp
    (fun r : Row d H => (f r).1)
    ell
    (A := 100 * (d.K : ℝ) / (d.w0 : ℝ) +
      Real.log (200 * (d.K : ℝ)) / d.wstar)
    hH d.v0_pos hell
  have ha :
      (100 * (d.K : ℝ) / (d.w0 : ℝ) + Real.log (200 * (d.K : ℝ)) / d.wstar) +
        Real.log 2 / (d.v0 : ℝ) = d.holomorphicError := by
    unfold AdmissibleParameters.holomorphicError
    ring
  rw [ha] at he
  change ‖(coefficientMatrix d selection f).det‖ ≤ _ at hb
  unfold collisionConstant actualRowCount
  exact hb.trans he
