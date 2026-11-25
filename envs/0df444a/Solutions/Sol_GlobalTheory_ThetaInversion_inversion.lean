-- Prove2me | solution 1 for GlobalTheory.ThetaInversion.inversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:42.248836+00:00
-- url     : https://prove2.me/submissions/4634dbae-4d7c-481e-a405-cabd391f5115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ChiGen
import Theorems.Thm_GlobalTheory_inversionStatement_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Key
open GlobalTheory GlobalTheory.ThetaInversion
namespace GlobalTheory.ThetaInversion
theorem _root_.solution : Chi.InversionStatement := GlobalTheory.inversionStatement_holds
end GlobalTheory.ThetaInversion
