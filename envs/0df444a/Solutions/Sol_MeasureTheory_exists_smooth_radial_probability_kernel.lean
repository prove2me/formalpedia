-- Prove2me | solution 1 for MeasureTheory.exists_smooth_radial_probability_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T11:12:04.332363+00:00
-- url     : https://prove2.me/submissions/7566c4c5-2da6-4ad6-ae10-ef86319df93f

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set Metric Function
open scoped ContDiff Topology
set_option autoImplicit false

theorem solution {n : ℕ} {R : ℝ} (hR : 0 < R) :
    ∃ (k : EuclideanSpace ℝ (Fin n) → ℝ) (κ : ℝ → ℝ),
      ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧
      (∀ y, k y = κ ‖y‖) ∧ (∀ y, R ≤ ‖y‖ → k y = 0) ∧
      (∫ y, k y) = 1 := by
  let E := EuclideanSpace ℝ (Fin n)
  let B := ContDiffBumpBase.ofInnerProductSpace E
  let b : E → ℝ := fun y => B.toFun 2 ((2 / R) • y)
  have hscale : 0 < (2 : ℝ) / R := div_pos (by norm_num) hR
  have hb : ContDiff ℝ ∞ b := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    change ContDiffAt ℝ ∞ (fun z : E => (uncurry B.toFun) (2, (2 / R) • z)) y
    have hpair : ContDiffAt ℝ ∞ (fun z : E => ((2 : ℝ), (2 / R) • z)) y :=
      contDiffAt_const.prodMk (contDiffAt_id.const_smul (2 / R))
    exact (B.smooth.contDiffAt (IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_univ)
      (by simp : (2, (2 / R) • y) ∈ Ioi (1 : ℝ) ×ˢ (univ : Set E)))).comp y hpair
  have hbs : ∀ y, R ≤ ‖y‖ → b y = 0 := by
    intro y hy
    apply notMem_support.mp
    change (2 / R) • y ∉ support (B.toFun 2)
    rw [B.support 2 (by norm_num), mem_ball_zero_iff]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
    have : 2 ≤ (2 / R) * ‖y‖ := by
      calc
        2 = (2 / R) * R := by field_simp
        _ ≤ (2 / R) * ‖y‖ := mul_le_mul_of_nonneg_left hy (div_pos (by norm_num) hR).le
    exact not_lt.mpr this
  have hbc : HasCompactSupport b := by
    apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E) R) isClosed_closure
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    rw [mem_closedBall_zero_iff]
    exact le_of_lt (lt_of_not_ge (fun h => hy (hbs y h)))
  have hbi : Integrable b := hb.continuous.integrable_of_hasCompactSupport hbc
  have hbp : 0 < ∫ y, b y := by
    apply integral_pos_of_integrable_nonneg_nonzero (x := (0 : E)) hb.continuous hbi
    · intro y; exact (B.mem_Icc 2 _).1
    · simp only [b, smul_zero]
      rw [B.eq_one 2 (by norm_num) 0 (by simp)]
      norm_num
  refine ⟨fun y => b y / ∫ z, b z,
    fun t => Real.smoothTransition (2 - (2 / R) * t) / ∫ z, b z,
    hb.div_const _, ?_, ?_, ?_, ?_⟩
  · apply IsCompact.of_isClosed_subset hbc isClosed_closure
    apply closure_mono
    intro y hy
    exact fun hz => hy (by simp only [hz, zero_div])
  · intro y
    simp [b, B, ContDiffBumpBase.ofInnerProductSpace, norm_smul,
      abs_of_pos hR, show (2 : ℝ) - 1 = 1 by norm_num]
  · intro y hy; simp [hbs y hy]
  · rw [integral_div, div_self hbp.ne']
