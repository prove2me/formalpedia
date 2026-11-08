-- Prove2me | solution 1 for LocalLog.continuousOn_localCharExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:16:47.575203+00:00
-- url     : https://prove2.me/submissions/c5a7b1d1-9cd2-43be-a82e-330987e910f6

import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

universe u

/-- The principal logarithm is continuous on the preimage of the complex slit plane. -/
theorem solution
    {E : Type u} [TopologicalSpace E] [Zero E] {φ : E → ℂ}
    (hφ_cont : Continuous φ) :
    ContinuousOn (LocalLog.localCharExponent φ) (LocalLog.goodDomain φ) := by
  exact hφ_cont.continuousOn.clog (fun _ hx => hx)
