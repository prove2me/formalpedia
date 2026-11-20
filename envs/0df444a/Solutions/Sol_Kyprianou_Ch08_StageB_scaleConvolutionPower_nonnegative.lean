-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.scaleConvolutionPower_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:03:23.936176+00:00
-- url     : https://prove2.me/submissions/00eda309-85d5-4ea5-af4f-ec44aba54fd8

import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Order.Interval.Set.Defs
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB Set

theorem solution (W : ℝ → ℝ)
    (hW : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ scaleConvolutionPower W n x := by
  induction n generalizing x with
  | zero => simpa only [scaleConvolutionPower] using hW x hx
  | succ n ih =>
    change 0 ≤ ∫ s in Set.Ioc (0 : ℝ) x,
      W s * scaleConvolutionPower W n (x - s) ∂volume
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg (hW s hs.1.le)
      (ih (x - s) (sub_nonneg.mpr hs.2))
