-- Prove2me | solution 1 for HostParam.Seam.exists_host
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:51:17.677168+00:00
-- url     : https://prove2.me/submissions/3e7ee77f-45a1-409f-a69f-b1452bbaf15a

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_SecondSetNoRelation
import Theorems.Thm_HostParam_Seam_exists_hostNF

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
theorem _root_.solution (R : Ranks) (H : HostAx R.toFrame) {b : ℕ} (h : FieldRows H.toHostRaw b)
    (hq : 4 * R.t * R.r + 1 < H.q ∧ 4 * R.t * R.r + 1 < H.d) (c : Choices R.toFrame H.toHostRaw) :
    ∃ D : Formalism.BasicNotions.Host R, D.toHostAx = H ∧ D.splitBound = b ∧ HEq (HostNF.ofHost D).ch c := by
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_hostNF R H h hq c
  exact ⟨N.toHost, hN1, hN2, hN3⟩
end HostParam.Seam
