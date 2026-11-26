-- Prove2me | solution 1 for Kyprianou.Ch05.smithRenewalRatioTransfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:09:13.859342+00:00
-- url     : https://prove2.me/submissions/39d15a48-10f5-4037-901d-2c3c0b4bee8b

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch05 SmithRenewal.Elementary

/-- A finite positive extended-real renewal-rate limit is unchanged by including the initial renewal and taking the real-valued ratio. -/
theorem solution
    (V H : Real → ENNReal) (m : Real) (hm : 0 < m)
    (hV : ∀ t : Real, 0 ≤ t → V t = 1 + H t)
    (hH : Tendsto (fun t : Real => H t / ENNReal.ofReal t)
      atTop (nhds (ENNReal.ofReal m)⁻¹)) :
    Tendsto (fun t : Real => (V t).toReal / t) atTop (nhds (1 / m)) := by
  have h0 : Tendsto (fun t : Real => (ENNReal.ofReal t)⁻¹) atTop (nhds 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero : Tendsto (fun t : Real => t⁻¹) atTop (nhds 0))
    change Tendsto (fun t : Real => ENNReal.ofReal (t⁻¹))
      atTop (nhds (ENNReal.ofReal 0)) at h
    rw [ENNReal.ofReal_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with t ht
    exact ENNReal.ofReal_inv_of_pos ht
  have hsum := h0.add hH
  have hratio : Tendsto (fun t : Real => V t / ENNReal.ofReal t)
      atTop (nhds (ENNReal.ofReal m)⁻¹) := by
    rw [zero_add] at hsum
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop (0 : Real)] with t ht
    rw [hV t ht, ENNReal.add_div, one_div]
  have hfinite : (ENNReal.ofReal m)⁻¹ ≠ ⊤ := by
    simp [hm.ne', ENNReal.ofReal_eq_zero]
    exact hm
  have hreal := (ENNReal.continuousAt_toReal hfinite).tendsto.comp hratio
  change Tendsto (fun t : Real => (V t / ENNReal.ofReal t).toReal)
    atTop (nhds ((ENNReal.ofReal m)⁻¹).toReal) at hreal
  have hreal' : Tendsto (fun t : Real => (V t / ENNReal.ofReal t).toReal)
      atTop (nhds (1 / m)) := by
    simpa only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hm.le, one_div] using hreal
  apply hreal'.congr'
  filter_upwards [eventually_ge_atTop (0 : Real)] with t ht
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal ht]
