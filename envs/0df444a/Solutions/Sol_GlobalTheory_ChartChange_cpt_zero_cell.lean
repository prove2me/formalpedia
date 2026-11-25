-- Prove2me | solution 1 for GlobalTheory.ChartChange.cpt_zero_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:08.599542+00:00
-- url     : https://prove2.me/submissions/aaba70a2-fcd8-4e65-ad70-29a0c51696bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralBallLtTopOfLocalInverse
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_cpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_orth_mem_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_zero_mem_OmF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthogonalFrameDomain_rmul_mem_dom


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
open GlobalTheory GlobalTheory.ChartChange
open Filter
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ExtFPf
namespace GlobalTheory.ChartChange
theorem _root_.solution {r : ℕ} {X : Data E r} {x1 b : Frame X.Ψ r} (D : LUData X x1) (ho : IsOrth X x1)
    (hb : b ∈ Bor X.Ψ r) :
    cpt X (rmul x1 b) 0 ∈ cell D ∧ D.zOf (cpt X (rmul x1 b) 0) = 0 := by
  have h := D.uniq 0 (IW.zero_mem_OmF X x1 ho) b hb
  rw [IW.cpt_zero] at h
  rw [IW.cpt_zero]
  exact ⟨⟨OrthogonalFrameDomain.rmul_mem_dom X (IW.orth_mem_dom X x1 ho) hb, h.1⟩, h.2.1⟩
end GlobalTheory.ChartChange
