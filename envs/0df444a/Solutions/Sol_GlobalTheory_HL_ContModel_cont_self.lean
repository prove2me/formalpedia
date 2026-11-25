-- Prove2me | solution 1 for GlobalTheory.HL.ContModel.cont_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:45:20.038312+00:00
-- url     : https://prove2.me/submissions/20ba58d6-c726-4f02-964a-367a7534c97b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Theorems.Thm_GlobalTheory_HL_ContModel_cont_subgroup
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
namespace GlobalTheory.HL.ContModel
theorem _root_.solution {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) : cont W0 (W0 : Set W) = 1 := by
  rw [cont_subgroup (by simp) (by simp)]
  simp [relVol]
end GlobalTheory.HL.ContModel
