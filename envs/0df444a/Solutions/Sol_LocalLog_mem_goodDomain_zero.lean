-- Prove2me | solution 1 for LocalLog.mem_goodDomain_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:14:06.563177+00:00
-- url     : https://prove2.me/submissions/a9112051-79fb-4ca2-9567-07bc3de50f3a

import Definitions.Def_LeanLevy_Levy_CharacteristicExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

universe u

/-- The origin lies in the logarithm domain because the characteristic function is one there. -/
theorem solution
    {E : Type u} [TopologicalSpace E] [Zero E] {φ : E → ℂ}
    (hφ_zero : φ 0 = 1) :
    (0 : E) ∈ LocalLog.goodDomain φ := by
  simp [LocalLog.goodDomain, Set.mem_preimage, hφ_zero, Complex.one_mem_slitPlane]
