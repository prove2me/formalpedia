-- Prove2me | solution 1 for O3.Experimental.scalarUniformConvexity_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:01:37.02801+00:00
-- url     : https://prove2.me/submissions/b0a47ec6-c829-49bc-8c7a-04de7984af0b

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
import Theorems.Thm_O3_Experimental_scalarJ_nonneg
import Theorems.Thm_O3_Experimental_scalarJ_strongMonotone
import Theorems.Thm_O3_Experimental_hasDerivAt_scalarEnergy
import Theorems.Thm_O3_Experimental_continuous_scalarJ
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open O3 O3.Experimental
namespace O3.Experimental
theorem _root_.solution {p x y : ℝ} (hp : 2 < p) (hxy : x ≤ y) :
    scalarEnergy p y ≥ scalarEnergy p x + scalarJ p x * (y - x) +
      ((2 : ℝ) ^ (2 - p) / p) * |y - x| ^ p := by
  let c : ℝ := (2 : ℝ) ^ (2 - p)
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hJint : IntervalIntegrable (scalarJ p) MeasureTheory.volume x y :=
    (continuous_scalarJ hp).intervalIntegrable _ _
  have hdiffcont : Continuous (fun t : ℝ ↦ scalarJ p t - scalarJ p x) :=
    (continuous_scalarJ hp).sub continuous_const
  have hdiffint : IntervalIntegrable (fun t : ℝ ↦ scalarJ p t - scalarJ p x)
      MeasureTheory.volume x y := hdiffcont.intervalIntegrable _ _
  have hlowercont : Continuous (fun t : ℝ ↦ c * scalarJ p (t - x)) := by
    exact continuous_const.mul
      ((continuous_scalarJ hp).comp (continuous_id.sub continuous_const))
  have hlowerint : IntervalIntegrable (fun t : ℝ ↦ c * scalarJ p (t - x))
      MeasureTheory.volume x y := hlowercont.intervalIntegrable _ _
  have hpoint : ∀ t ∈ Set.Icc x y,
      c * scalarJ p (t - x) ≤ scalarJ p t - scalarJ p x := by
    intro t ht
    by_cases htx : t = x
    · subst t
      simp [scalarJ]
    · have htxpos : 0 < t - x := sub_pos.mpr (lt_of_le_of_ne ht.1 (Ne.symm htx))
      have hs := scalarJ_strongMonotone (p := p) (u := t) (v := x) hp
      have hjmul : scalarJ p (t - x) * (t - x) = |t - x| ^ p := by
        rw [scalarJ_nonneg hp htxpos.le, abs_of_pos htxpos]
        rw [← Real.rpow_add_one' htxpos.le (by linarith : p - 1 + 1 ≠ 0)]
        congr 1
        ring
      have hmul : (c * scalarJ p (t - x)) * (t - x) ≤
          (scalarJ p t - scalarJ p x) * (t - x) := by
        rw [mul_assoc, hjmul]
        exact hs
      exact (le_of_mul_le_mul_right hmul htxpos)
  have hmono := intervalIntegral.integral_mono_on hxy hlowerint hdiffint hpoint
  have henergy : ∫ t in x..y, scalarJ p t = scalarEnergy p y - scalarEnergy p x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_scalarEnergy hp t) hJint
  have hlowerDeriv : ∀ t ∈ Set.uIcc x y,
      HasDerivAt (fun s : ℝ ↦ c * scalarEnergy p (s - x))
        (c * scalarJ p (t - x)) t := by
    intro t _
    simpa only [Function.comp_apply, id_eq, one_mul, mul_one] using
      ((hasDerivAt_scalarEnergy hp (t - x)).comp t
        ((hasDerivAt_id t).sub_const x) |>.const_mul c)
  have hlower : ∫ t in x..y, c * scalarJ p (t - x) =
      c * scalarEnergy p (y - x) - c * scalarEnergy p (x - x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hlowerDeriv hlowerint
  rw [hlower, intervalIntegral.integral_sub hJint
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ scalarJ p x)
      MeasureTheory.volume x y), henergy, intervalIntegral.integral_const] at hmono
  have hp0 : p ≠ 0 := by linarith
  simp [scalarEnergy, scalarJ, c, hp0] at hmono ⊢
  ring_nf at hmono ⊢
  linarith
end O3.Experimental
