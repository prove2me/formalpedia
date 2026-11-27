-- Prove2me | solution 1 for HostParam.Seam.ofP_toP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:49.474181+00:00
-- url     : https://prove2.me/submissions/d8d90cb5-1a12-4964-b6a6-982d6186867e

import Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_MemRealCyclotomicSubgroup
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_OfPInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HC Formalism.FrobeniusOrbits
noncomputable section
open HostParam HostParam.Seam
namespace HostParam.Seam
theorem _root_.solution (κ : PrimChar) (h : 0 < κ.1) (hp : κ.2.IsPrimitive) : ofP (toP κ h hp) = κ := rfl
end HostParam.Seam
