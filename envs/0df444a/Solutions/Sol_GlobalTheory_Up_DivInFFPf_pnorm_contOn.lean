-- Prove2me | solution 1 for GlobalTheory.Up.DivInFFPf.pnorm_contOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:56:41.033262+00:00
-- url     : https://prove2.me/submissions/be560c43-c546-471a-a96b-5619b818cbc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralFundSetInterLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralBallLtTopOfLocalInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsOpenSaturation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurablePhi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_nfac_contOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.Up GlobalTheory.Up.DivInFFPf
open Filter
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (Xa : ArchInM X) (Fl : FlatM X Xa)
namespace GlobalTheory.Up.DivInFFPf
theorem _root_.solution {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) :
    ContinuousOn (X.pnorm la P) X.dom :=
  hP.1.continuousOn.norm.mul (ExtFPf.nfac_contOn X la)
end GlobalTheory.Up.DivInFFPf
