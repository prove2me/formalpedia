-- Prove2me | solution 1 for LocalLog.leanlevy_chat29_exists_ball_subset_goodDomain_norm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T12:59:29.204051+00:00
-- url     : https://prove2.me/submissions/6f47d03c-5adb-47b2-97cf-c3dcadb077c4

import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Module.Connected
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Topology Filter

/-- Correct norm-topology local-log ball, after auditing imported source variables. -/
theorem solution
    {E : Type*} [SeminormedAddCommGroup E] {φ : E → ℂ}
    (hφ_cont : Continuous φ) (hφ_zero : φ 0 = 1) :
    ∃ ε > 0, Metric.ball (0 : E) ε ⊆ LocalLog.goodDomain φ := by
  have hOpen : IsOpen (LocalLog.goodDomain φ) :=
    Complex.isOpen_slitPlane.preimage hφ_cont
  have hZero : (0 : E) ∈ LocalLog.goodDomain φ := by
    simpa [LocalLog.goodDomain, hφ_zero] using Complex.one_mem_slitPlane
  exact Metric.isOpen_iff.mp hOpen 0 hZero
