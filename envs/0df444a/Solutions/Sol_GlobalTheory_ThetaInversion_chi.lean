-- Prove2me | solution 1 for GlobalTheory.ThetaInversion.chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:24.953667+00:00
-- url     : https://prove2.me/submissions/e9059642-cb08-47bd-a8dd-4322d39499a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ChiGen
import Theorems.Thm_GlobalTheory_ThetaInversion_inversion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chi_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spGen


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
theorem _root_.solution : Chi.ChiStatement := Chi.chi_of inversion Chi.spGen
end GlobalTheory.ThetaInversion
