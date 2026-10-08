-- Prove2me | solution 1 for OAI.PiExponent.pi_cofinal_real_height_determinant_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T19:30:21.106608+00:00
-- url     : https://prove2.me/submissions/148cea1b-9371-49a6-8d5f-ac4aa6050acc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_exists_admissible_parameters
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_arithmetic_lower_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_tendsto_collisionRate
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_global_interpolation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_analytic_aggregate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Topology
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

-- This finite-dimensional argument is the source's nonzero-minor extraction.
private theorem nonzero_minor_of_surjective
    {R C K : Type*} [Fintype R] [Fintype C] [DecidableEq R] [Field K]
    (A : Matrix R C K) (hA : Function.Surjective A.mulVecLin) :
    ∃ selection : R → C, (A.submatrix id selection).det ≠ 0 := by
  classical
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hA
  have hexp : (A * B).det =
      ∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i := by
    calc
      (A * B).det = ∑ p : R → C, ∑ σ : Equiv.Perm R,
          ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, A (σ i) (p i) * B (p i) i := by
        simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
          Finset.mul_sum, Fintype.piFinset_univ]
        rw [Finset.sum_comm]
      _ = ∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq,
          Finset.prod_mul_distrib, ← mul_assoc, ← Finset.sum_mul]
  have hsum : (∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i) ≠ 0 := by
    rw [← hexp, hB, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨p, fun h => hp (by rw [h, zero_mul])⟩

private theorem fixed_error_margins {nu : ℝ} (d : FixedData nu) :
    d.arithmeticError + d.analyticError <
      nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) - (1 - d.base.theta) ∧
    1 + d.arithmeticError + d.analyticError < collisionLimit d := by
  have heq : d.arithmeticError + d.analyticError =
      nu / d.F0 +
        ((Arithmetic.lcmConstant * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
          100 * (d.K : ℝ) / (d.w0 : ℝ)) +
        (Arithmetic.lcmConstant * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
          weightErrorCoefficient nu d.base.theta d.K / d.wstar) := by
    unfold AdmissibleParameters.arithmeticError AdmissibleParameters.analyticError
      AdmissibleParameters.translationError AdmissibleParameters.holomorphicError
      weightErrorCoefficient
    ring
  have h1 := d.initial_margin
  have h2 := d.dimension_margin
  have h3 := d.weight_margin
  have h4 := d.epsilon_lt_gap
  have h5 := d.epsilon_le_half
  have h6 := d.collision_margin
  change 2 < collisionLimit d at h6
  constructor
  · rw [heq]
    linarith
  · rw [add_assoc, heq]
    linarith

private theorem fixed_mean_bounds {nu : ℝ} (d : FixedData nu) (H : ℝ) (hH : 0 < H) :
    0 ≤ actualMean d H ∧ actualMean d H ≤ (d.base.theta : ℝ) := by
  classical
  have htheta := d.base.theta_pos
  have hnonneg : 0 ≤ MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
      (finiteDenominators d) H := by
    apply Finset.sum_nonneg
    intro ρ hρ
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hden : 0 ≤ (actualRowCount d H : ℝ) * H :=
    mul_nonneg (Nat.cast_nonneg _) hH.le
  constructor
  · exact div_nonneg hnonneg hden
  · by_cases hcard : actualRowCount d H = 0
    · change MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta (finiteDenominators d) H /
          ((actualRowCount d H : ℝ) * H) ≤ (d.base.theta : ℝ)
      rw [hcard]
      simpa using htheta.le
    have hcardpos : 0 < (actualRowCount d H : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hcard
    apply (div_le_iff₀ (mul_pos hcardpos hH)).mpr
    calc
      MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta (finiteDenominators d) H ≤
          ∑ _ρ : Row d H, H * (d.base.theta : ℝ) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have hb := (Finset.mem_filter.mp ρ.2.property).2
        have hb' : (d.v0 : ℝ) * (ρ.2.val 0 : ℝ) +
            (∑ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i *
              (ρ.2.val i.succ : ℝ)) / (d.base.theta : ℝ) < H := by
          simpa only [InterpolationMatrix.rowWeights, Fin.sum_univ_succ,
            Fin.cases_zero, Fin.cases_succ, div_mul_eq_mul_div, Finset.sum_div] using hb
        have h0 : 0 ≤ (d.v0 : ℝ) * (ρ.2.val 0 : ℝ) :=
          mul_nonneg d.v0_pos.le (Nat.cast_nonneg _)
        have hq : (∑ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i *
            (ρ.2.val i.succ : ℝ)) / (d.base.theta : ℝ) ≤ H := by linarith
        have hm := (div_le_iff₀ htheta).mp hq
        simpa only [mul_comm] using hm
      _ = (d.base.theta : ℝ) * ((actualRowCount d H : ℝ) * H) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]
        ring

theorem solution
    (nu : ℝ) (hnu : 2 < nu)
    (hbad : ∀ Q : ℕ, ∃ (p : ℤ) (q : ℕ),
      Q ≤ q ∧ |Real.pi - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-nu)) :
    ∃ theta x ear ean collisionLimit : ℝ,
      ∃ mean error rate : ℝ → ℝ,
        ear + ean < nu * (x - theta) - (1 - theta) ∧
        1 + ear + ean < collisionLimit ∧
        Tendsto error atTop (𝓝 0) ∧
        Tendsto rate atTop (𝓝 collisionLimit) ∧
        ∀ L : ℝ, ∃ H D : ℝ,
          L ≤ H ∧ 0 < H ∧
          0 ≤ mean H ∧ mean H ≤ theta ∧
          -(1 - mean H) - ear ≤ D ∧
          D ≤ ean + error H + max (-rate H) (-nu * (x - mean H)) := by
  classical
  have hLambda : 0 < Arithmetic.lcmConstant := by
    unfold Arithmetic.lcmConstant
    linarith [Real.log_pos (show (1 : ℝ) < 4 by norm_num)]
  have hc : 0 < collisionConstant :=
    div_pos (Real.log_pos (show (1 : ℝ) < 2 by norm_num)) (by norm_num)
  obtain ⟨d⟩ := exists_admissible_parameters nu Arithmetic.lcmConstant collisionConstant
    hnu hLambda hc hbad
  obtain ⟨error, herr, hu⟩ := analytic_aggregate nu hnu d
  obtain ⟨L0, hL0⟩ := Filter.eventually_atTop.mp hu
  obtain ⟨hgap, hcollision⟩ := fixed_error_margins d
  refine ⟨d.base.theta, (d.base.A : ℝ) * (1 - d.base.eta), d.arithmeticError,
    d.analyticError, collisionLimit d, actualMean d, error, collisionRate d,
    hgap, hcollision, herr, tendsto_collisionRate d, ?_⟩
  intro L
  obtain ⟨H, hheight, hsurj⟩ := global_interpolation nu hnu d (max L (max L0 1))
  have hLH : L ≤ H := (le_max_left _ _).trans hheight
  have hL0H : L0 ≤ H := ((le_max_left _ _).trans (le_max_right _ _)).trans hheight
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one
    (((le_max_right _ _).trans (le_max_right _ _)).trans hheight)
  obtain ⟨selection, hdet⟩ := nonzero_minor_of_surjective (actualMatrix d H) hsurj
  have hdet' : (actualMinor d H selection).det ≠ 0 := hdet
  obtain ⟨hb0, hbtheta⟩ := fixed_mean_bounds d H hH
  exact ⟨H, Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H),
    hLH, hH, hb0, hbtheta, actual_minor_arithmetic_lower_bound d H hH selection hdet',
    hL0 H hL0H selection hdet'⟩
