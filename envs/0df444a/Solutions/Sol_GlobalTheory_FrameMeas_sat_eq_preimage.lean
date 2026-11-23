-- Prove2me | solution 1 for GlobalTheory.FrameMeas.sat_eq_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:24.889568+00:00
-- url     : https://prove2.me/submissions/b8e540ae-1f6f-441e-87ab-0812fe092b29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetBorSat
import Theorems.Thm_GlobalTheory_FrameMeas_borSat_subset_dom

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
open GlobalTheory GlobalTheory.FrameMeas
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.FrameMeas
theorem _root_.solution {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {C : Set (Frame X.Ψ r)}
    (hC : C ⊆ X.dom) : sat X x0 C = cpt X x0 ⁻¹' borSat X C := by
  ext z
  exact ⟨fun h => h.2, fun h => ⟨borSat_subset_dom X hC h, h⟩⟩
end GlobalTheory.FrameMeas
