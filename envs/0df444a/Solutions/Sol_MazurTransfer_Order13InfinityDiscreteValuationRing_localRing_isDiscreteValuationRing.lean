-- Prove2me | solution 1 for MazurTransfer.Order13InfinityDiscreteValuationRing.localRing_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T11:50:29.910174+00:00
-- url     : https://prove2.me/submissions/7633f661-0680-400f-82fa-78adc3754077

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual reciprocal-chart local rings at the two infinity
points are discrete valuation rings, with z as a uniformizer, in characteristic
zero. Named downstream consumer: the exact Pell orders and principal divisor.
-/
import Definitions.Def_MazurTransfer_Order13InfinityLocalRingDomain
import Theorems.Thm_MazurTransfer_Order13InfinityLocalParameter_maximalIdeal_eq_span_z
noncomputable section
open MazurTransfer
universe u
open MazurTransfer.Order13InfinityDiscreteValuationRing
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13InfinityLocalParameter
variable (K : Type u) [Field K] [CharZero K] (a : K) (ha : a ^ 2 = 1)

namespace MazurTransfer.InfinityLocalDVRHelpers20261017
theorem localRing_not_isField : ¬ IsField (LocalRing K a ha) := by
  intro h
  have hz : z K a ha ∈ IsLocalRing.maximalIdeal (LocalRing K a ha) := by
    rw [maximalIdeal_eq_span_z K a ha (by norm_num)]
    exact Ideal.subset_span (by simp)
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp h] at hz
  exact z_ne_zero K a ha hz

end MazurTransfer.InfinityLocalDVRHelpers20261017
theorem solution : IsDiscreteValuationRing (LocalRing K a ha) := by
  apply ((IsDiscreteValuationRing.TFAE (LocalRing K a ha)
    (MazurTransfer.InfinityLocalDVRHelpers20261017.localRing_not_isField K a ha)).out 0 4).mpr
  rw [maximalIdeal_eq_span_z K a ha (by norm_num)]
  infer_instance


#print axioms solution
