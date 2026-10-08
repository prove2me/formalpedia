-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.no_fixed_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T07:03:10.285487+00:00
-- url     : https://prove2.me/submissions/9abfebdd-405f-4d9f-89ce-f31d804ca45e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_global_interpolation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_analytic_aggregate
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_tendsto_collisionRate
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_arithmetic_lower_bound
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Topology
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

private theorem fixed_data_exponent_gt_two {nu : ℝ} (d : FixedData nu) : 2 < nu := by
  have hBpos : 0 < (d.base.B : ℝ) :=
    lt_trans d.base.theta_pos (lt_trans d.base.theta_lt_A d.base.A_lt_B)
  have hCpos : 0 < (d.base.C : ℝ) := lt_trans zero_lt_one d.base.one_lt_C
  have hBC : (d.base.B : ℝ) * d.base.C < 1 :=
    (lt_div_iff₀ hCpos).mp d.base.B_lt_inv_C
  have hBB : (d.base.B : ℝ) ^ 2 < d.base.theta := by
    have h1 := mul_lt_mul_of_pos_left d.base.B_lt_C_theta hBpos
    have h2 := mul_lt_mul_of_pos_right hBC d.base.theta_pos
    nlinarith
  have hApos : 0 < (d.base.A : ℝ) := lt_trans d.base.theta_pos d.base.theta_lt_A
  have hAA : (d.base.A : ℝ) ^ 2 < d.base.theta := by
    nlinarith [d.base.A_lt_B]
  have hgap : 2 * ((d.base.A : ℝ) - d.base.theta) < 1 - d.base.theta := by
    nlinarith [sq_nonneg (1 - (d.base.A : ℝ))]
  by_contra h
  have hnu : nu ≤ 2 := le_of_not_gt h
  have hmul := mul_le_mul_of_nonneg_right hnu
    (sub_nonneg.mpr d.base.theta_lt_A.le)
  linarith [d.base.approximation_gap]

private theorem fixed_error_margins {nu : ℝ} (d : FixedData nu) :
    d.arithmeticError + d.analyticError <
      nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
        (1 - d.base.theta) ∧
    1 + d.arithmeticError + d.analyticError < collisionLimit d := by
  have heq : d.arithmeticError + d.analyticError =
      nu / d.F0 +
        ((Arithmetic.lcmConstant * d.F0 * (d.m : ℝ) + 2 * Real.log 2) /
          (d.v0 : ℝ) + 100 * (d.K : ℝ) / (d.w0 : ℝ)) +
        (Arithmetic.lcmConstant *
          (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
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
    exact Finset.sum_nonneg (fun i hi =>
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hden : 0 ≤ (actualRowCount d H : ℝ) * H :=
    mul_nonneg (Nat.cast_nonneg _) hH.le
  constructor
  · exact div_nonneg hnonneg hden
  · by_cases hcard : actualRowCount d H = 0
    · change MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
          (finiteDenominators d) H /
          ((actualRowCount d H : ℝ) * H) ≤ (d.base.theta : ℝ)
      rw [hcard]
      simpa using htheta.le
    · have hcardpos : 0 < (actualRowCount d H : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hcard
      change MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
          (finiteDenominators d) H /
          ((actualRowCount d H : ℝ) * H) ≤ (d.base.theta : ℝ)
      apply (div_le_iff₀ (mul_pos hcardpos hH)).mpr
      calc
        MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
            (finiteDenominators d) H ≤
          ∑ _ρ : Row d H, H * (d.base.theta : ℝ) := by
            apply Finset.sum_le_sum
            intro ρ hρ
            have hb := (Finset.mem_filter.mp ρ.2.property).2
            have hb' : (d.v0 : ℝ) * (ρ.2.1 0 : ℝ) +
                (∑ i : Fin d.m, MatrixArithmetic.logWeights
                  (finiteDenominators d) i * (ρ.2.1 i.succ : ℝ)) /
                  (d.base.theta : ℝ) < H := by
              simpa only [InterpolationMatrix.rowWeights, Fin.sum_univ_succ,
                Fin.cases_zero, Fin.cases_succ, div_mul_eq_mul_div,
                Finset.sum_div] using hb
            have h0 : 0 ≤ (d.v0 : ℝ) * (ρ.2.1 0 : ℝ) :=
              mul_nonneg d.v0_pos.le (Nat.cast_nonneg _)
            have hq : (∑ i : Fin d.m, MatrixArithmetic.logWeights
                (finiteDenominators d) i * (ρ.2.1 i.succ : ℝ)) /
                  (d.base.theta : ℝ) ≤ H := by linarith
            have hm := (div_le_iff₀ htheta).mp hq
            simpa only [mul_comm] using hm
        _ = (d.base.theta : ℝ) * ((actualRowCount d H : ℝ) * H) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            actualRowCount]
          ring

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

private theorem scalar_determinant_bounds_inconsistent
    (nu theta x b ear ean err collision d : ℝ)
    (hnu : 1 < nu) (hb0 : 0 ≤ b) (hb : b ≤ theta)
    (hgap : ear + ean + err < nu * (x - theta) - (1 - theta))
    (hcollision : 1 + ear + ean + err < collision)
    (hlower : -(1 - b) - ear ≤ d)
    (hupper : d ≤ ean + err + max (-collision) (-nu * (x - b))) : False := by
  have hfirst : ean + err - collision < -(1 - b) - ear := by linarith
  have hmono : nu * (x - theta) - (1 - theta) ≤
      nu * (x - b) - (1 - b) := by nlinarith
  have hsecond : ean + err - nu * (x - b) < -(1 - b) - ear := by
    nlinarith
  rcases le_total (-collision) (-nu * (x - b)) with h | h
  · rw [max_eq_right h] at hupper
    linarith
  · rw [max_eq_left h] at hupper
    linarith

theorem solution (nu : ℝ) : IsEmpty (FixedData nu) := by
  classical
  refine ⟨?_⟩
  intro d
  have hnu : 2 < nu := fixed_data_exponent_gt_two d
  obtain ⟨error, herror, hupper⟩ := analytic_aggregate nu hnu d
  have hsum : Tendsto (fun H : ℝ => d.arithmeticError + d.analyticError + error H)
      atTop (𝓝 (d.arithmeticError + d.analyticError + 0)) :=
    tendsto_const_nhds.add herror
  have hsmall : ∀ᶠ H : ℝ in atTop,
      d.arithmeticError + d.analyticError + error H <
        nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
          (1 - d.base.theta) :=
    hsum.eventually (Iio_mem_nhds (by simpa using (fixed_error_margins d).1))
  have hdiff : Tendsto (fun H : ℝ => collisionRate d H -
      (1 + d.arithmeticError + d.analyticError + error H)) atTop
      (𝓝 (collisionLimit d - (1 + d.arithmeticError + d.analyticError + 0))) :=
    (tendsto_collisionRate d).sub (tendsto_const_nhds.add herror)
  have hlarge : ∀ᶠ H : ℝ in atTop,
      0 < collisionRate d H -
        (1 + d.arithmeticError + d.analyticError + error H) := by
    apply hdiff.eventually (Ioi_mem_nhds ?_)
    have hh := (fixed_error_margins d).2
    change 1 + d.arithmeticError + d.analyticError < collisionLimit d at hh
    linarith
  have hnot_surj : ∀ᶠ H : ℝ in atTop,
      Function.Surjective (actualMatrix d H).mulVecLin → False := by
    filter_upwards [hsmall, hlarge, hupper, eventually_gt_atTop (0 : ℝ)]
      with H hs hc hu hH
    intro hsurj
    obtain ⟨selection, hdet⟩ :=
      nonzero_minor_of_surjective (actualMatrix d H) hsurj
    have hlower := actual_minor_arithmetic_lower_bound d H hH selection hdet
    obtain ⟨hb0, hbtheta⟩ := fixed_mean_bounds d H hH
    exact scalar_determinant_bounds_inconsistent nu (d.base.theta : ℝ)
      ((d.base.A : ℝ) * (1 - d.base.eta)) (actualMean d H)
      d.arithmeticError d.analyticError (error H) (collisionRate d H)
      (Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : ℝ) * H))
      (by linarith) hb0 hbtheta (by linarith) (by linarith) hlower
      (hu selection hdet)
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hnot_surj
  obtain ⟨H, hLH, hsurj⟩ := global_interpolation nu hnu d L
  exact hL H hLH hsurj
