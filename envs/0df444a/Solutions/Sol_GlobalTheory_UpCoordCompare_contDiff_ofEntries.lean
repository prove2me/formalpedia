-- Prove2me | solution 1 for GlobalTheory.UpCoordCompare.contDiff_ofEntries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:18:06.257787+00:00
-- url     : https://prove2.me/submissions/1173652f-1814-40bd-ab44-0b29c4605f32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeadingBlockLowerEntriesToBlockCoords
import Theorems.Thm_GlobalTheory_UpCoordCompare_contDiff_coordOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_cd_Zt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_cd_nM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UpCoordCompare
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open scoped Matrix ComplexOrder ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace GlobalTheory.UpCoordCompare
theorem _root_.solution : ContDiff ℂ ∞ (ofEntries X) := by
  refine contDiff_coordOf X fun τ a b => ?_
  split_ifs
  · exact ExF.cd_Zt X τ _ _
  · exact ExF.cd_nM X τ a b
end GlobalTheory.UpCoordCompare
