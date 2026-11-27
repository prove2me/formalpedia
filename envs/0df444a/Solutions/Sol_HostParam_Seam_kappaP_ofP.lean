-- Prove2me | solution 1 for HostParam.Seam.kappaP_ofP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:29.361346+00:00
-- url     : https://prove2.me/submissions/9b0bcf96-36b5-4233-bc8e-b927cc3b2cac

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
theorem _root_.solution (ψ : PChar) : kappaP (ofP ψ) = An.logDerivativeAtOne ψ.χ := dif_neg (NeZero.ne ψ.N)
end HostParam.Seam
