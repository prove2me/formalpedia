-- Prove2me | solution 1 for GlobalTheory.Unfold.rmul_mem_satFrames_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:49.64687+00:00
-- url     : https://prove2.me/submissions/5d51afe7-755b-45f6-b9a6-d2fb1f273866

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetSatFrames
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_invF_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_mul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_assoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_invF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_oneF


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
open GlobalTheory GlobalTheory.Unfold
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Unfold
theorem _root_.solution (X : Data E r) (x0 : Frame X.Ψ r) (A : Set (V (nd X)))
    (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ satFrames X x0 A ↔ x ∈ satFrames X x0 A := by
  constructor
  · rintro ⟨z, hz, b', hb', h⟩
    refine ⟨z, hz, rmul b' (ExtFPf.invF X b), ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb), ?_⟩
    rw [← ExtFPf.rmul_assoc, ← h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
  · rintro ⟨z, hz, b', hb', rfl⟩
    exact ⟨z, hz, rmul b' b, ExtFPf.mul_mem X hb' hb, by rw [ExtFPf.rmul_assoc]⟩
end GlobalTheory.Unfold
