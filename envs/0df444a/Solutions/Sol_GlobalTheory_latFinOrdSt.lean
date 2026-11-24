-- Prove2me | solution 1 for GlobalTheory.latFinOrdSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:14:47.29311+00:00
-- url     : https://prove2.me/submissions/9d18a982-a585-4e28-90a2-2a093adeacc3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsPowEqOneOfPosDefForm
import Theorems.Thm_GlobalTheory_exists_pow_eq_one_of_posDef_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LatFinOrdSt :=
  fun Y _ _ _ b hs hp σ hσ => exists_pow_eq_one_of_posDef_form Y b hs hp σ hσ
end GlobalTheory
