-- Prove2me | solution 1 for GoodmanWitten.coherent_rate_order_1e4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:50:39.136037+00:00
-- url     : https://prove2.me/submissions/8a61d32c-6cb1-4bcb-824a-6e12c850eda2

import Mathlib
import Definitions.Def_GoodmanWitten_basic
open GoodmanWitten

theorem solution (A : ℝ) (hA : 0 < A) :
    1e4 ≤ eventRatePerKgDay A (coherentCrossSection (nucleusMass A) (nucleusMass A) 1 100)
        1e-24 2e7 (nucleusMass A) ∧
      eventRatePerKgDay A (coherentCrossSection (nucleusMass A) (nucleusMass A) 1 100)
        1e-24 2e7 (nucleusMass A) < 1e5 := by
  have hval : eventRatePerKgDay A (coherentCrossSection (nucleusMass A) (nucleusMass A) 1 100)
      1e-24 2e7 (nucleusMass A) =
      6.0e26 * 1e-24 * 2e7 * secondsPerDay * fermiConstant ^ 2 * 1e4 / 2 * hbarc ^ 2 *
        nucleonMass / (4 * Real.pi * gramsPerGeV) := by
    unfold eventRatePerKgDay coherentCrossSection elasticCrossSection coherentAmpSq
      targetNucleiPerKg nucleusMass
    have hpi := Real.pi_pos
    have hn : 0 < nucleonMass := by unfold nucleonMass; norm_num
    have hg : 0 < gramsPerGeV := by unfold gramsPerGeV; norm_num
    field_simp
    ring
  rw [hval]
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  unfold secondsPerDay fermiConstant hbarc nucleonMass gramsPerGeV
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
