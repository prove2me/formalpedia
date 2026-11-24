-- Prove2me | solution 1 for GlobalTheory.GramSchmidtCont.continuousOn_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:53:53.379021+00:00
-- url     : https://prove2.me/submissions/fce3d4a7-2117-4231-a75c-c9645e4966ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsContinuousGramSchmidt

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
open GlobalTheory GlobalTheory.GramSchmidtCont
open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
namespace GlobalTheory.GramSchmidtCont
theorem _root_.solution {T : Type} [TopologicalSpace T] {n : ℕ} {s : Set T}
    {M : T → Matrix (Fin n) (Fin n) ℂ} (hM : Continuous M) (hd : ∀ t ∈ s, (M t).det ≠ 0)
    (i j : Fin n) : ContinuousOn (fun t => (M t)⁻¹ i j) s := by
  have hdet : Continuous fun t => (M t).det := hM.matrix_det
  have hadj : Continuous fun t => (M t).adjugate i j := hM.matrix_adjugate.matrix_elem i j
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (hdet.continuousOn.inv₀ hd).mul hadj.continuousOn
end GlobalTheory.GramSchmidtCont
