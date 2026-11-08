-- Prove2me | solution 1 for LocalLog.isOpen_goodDomain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:15:43.033937+00:00
-- url     : https://prove2.me/submissions/03495b63-a86f-4edb-9bf9-7bc237a5855c

import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Mathlib.Topology.Defs.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

universe u

/-- Continuity transports the openness of the complex logarithm's slit-plane domain. -/
theorem solution
    {E : Type u} [TopologicalSpace E] [Zero E] {φ : E → ℂ}
    (hφ_cont : Continuous φ) :
    IsOpen (LocalLog.goodDomain φ) := by
  exact Complex.isOpen_slitPlane.preimage hφ_cont
