-- Prove2me | solution 1 for MasulloRH.negative_lag_radial_measurement_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T23:59:48.389215+00:00
-- url     : https://prove2.me/submissions/b98b7e84-242a-46a6-95fa-feb3ae239058

import Mathlib

open Filter MeasureTheory Set
open scoped Topology

theorem solution (α L : ℝ) (hα : 0 < α) (hL : 0 < L) (U : ℝ → ℂ)
    (hU : IntervalIntegrable U volume 0 L)
    (hW : ∀ᵐ u ∂volume.restrict (Ioo 0 L),
      (∫ a in (0 : ℝ)..u, (Real.exp (2 * α * a) : ℂ) * U a) +
        (Real.exp (-(2 * α * L)) : ℂ) *
          (∫ a in u..L, (Real.exp (2 * α * a) : ℂ) * U a) = 0) :
    (∀ᵐ a ∂volume.restrict (Ioo 0 L), U a = 0) ∧ (∫ a in (0 : ℝ)..L, U a) = 0 := by
  let f : ℝ → ℂ := fun a => (Real.exp (2 * α * a) : ℂ) * U a
  let q : ℂ := (Real.exp (-(2 * α * L)) : ℝ)
  let P (z u : ℝ) : ℂ := ∫ a in z..u, f a
  let W (u : ℝ) : ℂ := P 0 u - q * P L u
  have hf : IntervalIntegrable f volume 0 L := hU.continuousOn_mul (by fun_prop)
  have hsmall : Real.exp (-(2 * α * L)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (by positivity))
  have hq : q ≠ 1 := by
    change (Real.exp (-(2 * α * L)) : ℂ) ≠ 1
    exact_mod_cast hsmall.ne
  have hsub : Ioo 0 L ⊆ uIcc 0 L := by
    rw [uIcc_of_le hL.le]
    exact Ioo_subset_Icc_self
  have hP {z : ℝ} (hz : z ∈ uIcc 0 L) : ContinuousOn (P z) (Ioo 0 L) :=
    (intervalIntegral.continuousOn_primitive_interval' hf hz).mono hsub
  have hcont : ContinuousOn W (Ioo 0 L) :=
    (hP left_mem_uIcc).sub (continuousOn_const.mul (hP right_mem_uIcc))
  have hae : W =ᵐ[volume.restrict (Ioo 0 L)] fun _ => 0 := by
    filter_upwards [hW] with u hu
    change P 0 u + q * (∫ a in u..L, f a) = 0 at hu
    rw [intervalIntegral.integral_symm L u] at hu
    simpa [W, P, sub_eq_add_neg] using hu
  have heq : EqOn W (fun _ => 0) (Ioo 0 L) :=
    Measure.eqOn_open_of_ae_eq (μ := volume) hae isOpen_Ioo hcont continuousOn_const
  have hzero : ∀ᵐ a ∂volume.restrict (Ioo 0 L), U a = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hf.ae_hasDerivAt_integral] with a ha
    intro ha₀
    have hda := ha (hsub ha₀)
    have hd : HasDerivAt W (f a - q * f a) a :=
      (hda 0 left_mem_uIcc).sub ((hda L right_mem_uIcc).const_mul q)
    have hz : HasDerivAt W 0 a :=
      (hasDerivAt_const a (0 : ℂ)).congr_of_eventuallyEq (by
        filter_upwards [isOpen_Ioo.mem_nhds ha₀] with x hx
        exact heq hx)
    have hcoef : (1 - q) * f a = 0 := by
      simpa [sub_mul] using hd.unique hz
    have hfa : f a = 0 := (mul_eq_zero.mp hcoef).resolve_left (sub_ne_zero.mpr hq.symm)
    exact (mul_eq_zero.mp hfa).resolve_left (by exact_mod_cast (Real.exp_ne_zero (2 * α * a)))
  refine ⟨hzero, ?_⟩
  rw [intervalIntegral.integral_of_le hL.le]
  apply integral_eq_zero_of_ae
  rwa [← restrict_Ioo_eq_restrict_Ioc]
