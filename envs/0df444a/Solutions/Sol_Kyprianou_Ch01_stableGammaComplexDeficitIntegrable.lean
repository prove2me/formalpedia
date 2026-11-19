-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaComplexDeficitIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:55:44.021016+00:00
-- url     : https://prove2.me/submissions/1c285ffa-16fb-49b6-a83d-7f60d338cfcb

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
import Theorems.Thm_Kyprianou_Ch01_stableGammaPowerEnvelopeIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitEnvelopeBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

/-- Complex compensated stable kernel integrability from a source-exact power envelope. -/
theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re ≤ 0) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (w * (r : ℂ)) - 1) *
          ((r ^ (-alpha - 1) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have henv0 : IntegrableOn
      (fun r : ℝ => if r ≤ 1 then ‖w‖ * r ^ (-alpha)
        else r ^ (-alpha - 1)) (Set.Ioi (0 : ℝ)) :=
    Kyprianou.Ch01.stableGammaPowerEnvelopeIntegrable
      alpha ‖w‖ h0 h1 hwpos
  have henv : IntegrableOn
      (fun r : ℝ => 2 * (if r ≤ 1 then ‖w‖ * r ^ (-alpha)
        else r ^ (-alpha - 1))) (Set.Ioi (0 : ℝ)) :=
    henv0.const_mul 2
  apply Integrable.mono' henv
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact Kyprianou.Ch01.stableGammaComplexDeficitEnvelopeBound
      alpha w hwre r hr
