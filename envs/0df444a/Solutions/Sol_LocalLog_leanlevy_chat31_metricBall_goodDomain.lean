-- Prove2me | solution 1 for LocalLog.leanlevy_chat31_metricBall_goodDomain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:42:27.343714+00:00
-- url     : https://prove2.me/submissions/fd4ca0d5-f293-480e-8718-c3552a80d507

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Topology Filter

/-- The canonical metric topology makes the slit-plane preimage a neighbourhood. -/
theorem solution
    {E : Type*} [SeminormedAddCommGroup E] {φ : E → ℂ}
    (hφ_cont : Continuous φ) (hφ_zero : φ 0 = 1) :
    ∃ ε > 0, Metric.ball (0 : E) ε ⊆ LocalLog.goodDomain φ := by
  have hopen : IsOpen (LocalLog.goodDomain φ) :=
    Complex.isOpen_slitPlane.preimage hφ_cont
  have hzero : (0 : E) ∈ LocalLog.goodDomain φ := by
    simpa only [LocalLog.goodDomain, Set.mem_preimage, hφ_zero] using
      Complex.one_mem_slitPlane
  exact Metric.isOpen_iff.mp hopen 0 hzero
