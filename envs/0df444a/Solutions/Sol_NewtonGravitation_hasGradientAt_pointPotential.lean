-- Prove2me | solution 1 for NewtonGravitation.hasGradientAt_pointPotential
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:23:51.371533+00:00
-- url     : https://prove2.me/submissions/c5d366d8-33a0-4eb5-a8a7-249a73953d15

import Definitions.Def_NewtonGravitation_Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic
open NewtonGravitation

theorem solution (M : ℝ) (c x : Space) (hx : x ≠ c) :
    HasGradientAt (pointPotential M c) (-pointField M c x) x := by
  have hn : ‖x-c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have hd := ((hasFDerivAt_id x).sub_const c).norm_sq.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at hd
  have hs := (((hasDerivAt_const ‖x-c‖ (G*M)).div (hasDerivAt_id ‖x-c‖) hn).neg).comp_hasFDerivAt x hd
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! hs using 1
  ext z
  simp [pointField,real_inner_smul_left,ContinuousLinearMap.comp_apply]
  field_simp
  <;> ring

