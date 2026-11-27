-- Prove2me | solution 1 for HostParam.Seam.toPrimitive_ofPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:56.50219+00:00
-- url     : https://prove2.me/submissions/71c22b05-77f5-4797-94a7-44dc0d10eb71

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
theorem _root_.solution (ψ : PChar) : toP (ofP ψ) (ofP_fst_pos ψ) (ofP_snd_isPrimitive ψ) = ψ := rfl
end HostParam.Seam
