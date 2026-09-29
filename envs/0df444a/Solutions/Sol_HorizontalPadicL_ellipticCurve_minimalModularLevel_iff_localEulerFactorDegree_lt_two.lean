-- Prove2me | solution 1 for HorizontalPadicL.ellipticCurve_minimalModularLevel_iff_localEulerFactorDegree_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T03:11:21.347406+00:00
-- url     : https://prove2.me/submissions/83f8c962-dce9-46d1-8654-71f5794dcf04

import Theorems.Thm_HorizontalPadicL_minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo
import Theorems.Thm_HorizontalPadicL_not_minimalModularLevel_dvd_iff_localEulerFactorDegreeTwo
import Definitions.Def_HorizontalPadicL_LocalEulerFactorDegree

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open HorizontalPadicL

theorem _root_.solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E)
    (p : ℕ) (hp : p.Prime) :
    (p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeBelowTwo E p) ∧
      (¬ p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeTwo E p) :=
  ⟨HorizontalPadicL.minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo E hmod p hp,
   HorizontalPadicL.not_minimalModularLevel_dvd_iff_localEulerFactorDegreeTwo E hmod p hp⟩

#print axioms solution
