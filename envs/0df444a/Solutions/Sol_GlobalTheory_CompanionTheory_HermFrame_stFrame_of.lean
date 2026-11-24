-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermFrame.stFrame_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:29:29.155598+00:00
-- url     : https://prove2.me/submissions/9cde122d-84ec-47b0-8da8-3abbf7a66e35

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FrameOfAnisotropicPlaneSplitting
import Theorems.Thm_GlobalTheory_CompanionTheory_HermFrame_exists_adapted_frame_with_unit_scaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermFrame
namespace GlobalTheory.CompanionTheory.HermFrame
theorem _root_.solution : StAniso → StPlane → StSplit → StFrame := by
  intro hA hP hS L _ _ _ _ s hs δ hδ V _ _ _ h hh
  exact exists_adapted_frame_with_unit_scaling hA hP hS L s hs δ hδ _ V h rfl hh
end GlobalTheory.CompanionTheory.HermFrame
