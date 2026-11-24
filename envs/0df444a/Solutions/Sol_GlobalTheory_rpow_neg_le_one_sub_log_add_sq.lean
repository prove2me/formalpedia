-- Prove2me | solution 1 for GlobalTheory.rpow_neg_le_one_sub_log_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:40.546638+00:00
-- url     : https://prove2.me/submissions/86038f0b-9cef-493d-9ba3-df2ff7631a03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsRpowNegSumLeOfSumLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ω δ t : ℝ} (hω : 1 ≤ ω) (hδ : 0 < δ)
    (hδL : δ * Real.log ω ≤ 1) (h1 : ω⁻¹ ≤ t) (h2 : t ≤ ω) :
    t ^ (-δ) ≤ 1 - δ * Real.log t + (δ * Real.log ω) ^ 2 := by
  have hω0 : 0 < ω := by linarith
  have ht : 0 < t := lt_of_lt_of_le (inv_pos.mpr hω0) h1
  have hu : Real.log t ≤ Real.log ω := Real.log_le_log ht h2
  have hl : -Real.log ω ≤ Real.log t := by
    rw [← Real.log_inv]; exact Real.log_le_log (inv_pos.mpr hω0) h1
  have habs : |Real.log t * (-δ)| ≤ δ * Real.log ω := by
    rw [abs_le]; constructor <;> nlinarith
  have h := Real.abs_exp_sub_one_sub_id_le (habs.trans hδL)
  have h' := (abs_le.mp h).2
  have hsq : (Real.log t * (-δ)) ^ 2 ≤ (δ * Real.log ω) ^ 2 := by
    rw [← sq_abs (Real.log t * (-δ))]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [Real.rpow_def_of_pos ht]
  linarith
end GlobalTheory
