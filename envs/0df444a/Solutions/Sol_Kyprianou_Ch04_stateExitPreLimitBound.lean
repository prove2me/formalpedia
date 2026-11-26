-- Prove2me | solution 1 for Kyprianou.Ch04.stateExitPreLimitBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:40:03.196601+00:00
-- url     : https://prove2.me/submissions/d4c9d090-1842-4aaf-bb39-d0691f028f0e

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A first open spatial exit bounds every earlier state and the left limit at exit. -/
theorem solution (Y L : NNReal → ℝ) (n : ℝ)
    (hl : ∀ t : NNReal, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t))) :
    let tau : WithTop NNReal := sInf {v : WithTop NNReal |
      ∃ u : NNReal, v = ↑u ∧ n < |Y u|}
    (∀ u : NNReal, (u : WithTop NNReal) < tau → |Y u| ≤ n) ∧
    (∀ t : NNReal, 0 < t → (t : WithTop NNReal) ≤ tau → |L t| ≤ n) := by
  let tau : WithTop NNReal := sInf {v : WithTop NNReal |
      ∃ u : NNReal, v = ↑u ∧ n < |Y u|}
  have hpre (u : NNReal) (hu : (u : WithTop NNReal) < tau) : |Y u| ≤ n := by
    by_contra hn
    exact (not_le_of_gt hu) (sInf_le ⟨u,rfl,lt_of_not_ge hn⟩)
  refine ⟨hpre,?_⟩
  intro t ht hstop
  haveI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,ht⟩
  apply isClosed_Iic.mem_of_tendsto (continuous_abs.continuousAt.tendsto.comp (hl t ht))
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact hpre u ((WithTop.coe_lt_coe.mpr hu).trans_le hstop)
