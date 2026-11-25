-- Prove2me | solution 1 for GlobalTheory.CurvMargin.leviRh_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:41:27.965432+00:00
-- url     : https://prove2.me/submissions/56d92e6c-c34a-4ddc-85a1-ae98d28d78a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PhlaBlockWtCpt
import Theorems.Thm_GlobalTheory_CurvMargin_phla_blockWt_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_isOpen_OmF
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.CurvMargin
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.CurvMargin
theorem _root_.solution {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0)
    {z : V (nd X)} (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    leviRh X x0 z ξ = leviM X (phla X (blockWt X)) x0 z ξ := by
  have hev : (fun w => ((rhF X x0 w : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => ((phla X (blockWt X) (cpt X x0 w) : ℝ) : ℂ) := by
    filter_upwards [(ExF.isOpen_OmF X x0).mem_nhds hz] with w hw
    rw [phla_blockWt_cpt X x0 ho hw]
  unfold leviRh leviM
  rw [leviV_congr hev]
end GlobalTheory.CurvMargin
