-- Prove2me | solution 1 for Kyprianou.Ch04.leftLimitSquareSupV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:46:58.468829+00:00
-- url     : https://prove2.me/submissions/588cd5d5-f307-43cf-9bdc-956b9121b888

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Positive-time left-limit differences inherit a compact path square bound. -/
theorem solution (U V : NNReal → ℝ) (u v : ℝ) (t T : NNReal)
    (ht : 0 < t) (hT : t ≤ T)
    (hu : Tendsto U (𝓝[<] t) (𝓝 u))
    (hv : Tendsto V (𝓝[<] t) (𝓝 v))
    (hb : BddAbove ((fun s : NNReal => |U s - V s|^2) '' Iic T)) :
    (u - v)^2 ≤ sSup ((fun s : NNReal => |U s - V s|^2) '' Iic T) := by
  haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  apply le_of_tendsto ((hu.sub hv).pow 2)
  filter_upwards [self_mem_nhdsWithin (a := t) (s := Iio t)] with s hs
  rw [← sq_abs (U s - V s)]
  exact le_csSup hb ⟨s, hs.le.trans hT, rfl⟩
