-- Prove2me | solution 1 for HostParam.Seam.exists_cmType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:46.087098+00:00
-- url     : https://prove2.me/submissions/e2426422-5914-466a-8370-1e58339a6c50

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_SecondSetNoRelation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HC Formalism.BasicNotions
open scoped Pointwise
noncomputable section
open HostParam HostParam.Seam
namespace HostParam.Seam
theorem _root_.solution {φ : Frame} (H : HostAx φ) : ∃ ψ : H.E →+* ℂ, ψ ∈ H.toHostRaw.cmType := by
  have h := H.der.cmType.2.1
  have := φ.ord_pos
  exact Set.nonempty_of_ncard_ne_zero (by omega)
end HostParam.Seam
