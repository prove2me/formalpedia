-- Prove2me | solution 1 for GlobalTheory.MajNear.continuous_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:09:22.631537+00:00
-- url     : https://prove2.me/submissions/cf3dbc5f-12ea-4d12-a22d-db69391d8e17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsomOfGramEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_cpt_entry_cd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.MajNear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MajNear
theorem _root_.solution {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : Continuous (cpt X x) :=
  continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b =>
    (IW.cpt_entry_cd X x τ a b).continuous
end GlobalTheory.MajNear
