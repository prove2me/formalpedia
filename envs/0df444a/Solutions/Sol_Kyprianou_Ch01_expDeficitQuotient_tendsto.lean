-- Prove2me | solution 1 for Kyprianou.Ch01.expDeficitQuotient_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T12:21:30.917791+00:00
-- url     : https://prove2.me/submissions/012256b2-19a9-4fa4-bf39-1ee8b99dae4d

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_expDeficit_hasDerivAt_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem solution (x : ℝ) :
    Tendsto (fun theta : ℝ => (1 - Real.exp (-theta * x)) / theta)
      (𝓝[>] (0 : ℝ)) (𝓝 x) := by
  have hd := Kyprianou.Ch01.expDeficit_hasDerivAt_zero x
  have hs : (𝓝[>] (0 : ℝ)) ≤ (𝓝[≠] (0 : ℝ)) := by
    apply nhdsWithin_mono
    intro theta ht
    exact Set.mem_compl (ne_of_gt ht)
  have hlim := hd.tendsto_slope_zero.mono_left hs
  convert hlim using 1
  ext theta
  simp [div_eq_mul_inv, smul_eq_mul] <;> ring
