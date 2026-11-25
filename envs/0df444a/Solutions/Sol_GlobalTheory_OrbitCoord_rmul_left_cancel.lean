-- Prove2me | solution 1 for GlobalTheory.OrbitCoord.rmul_left_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:34:13.274798+00:00
-- url     : https://prove2.me/submissions/5fbd1269-96cd-4798-8ad7-99e5825becea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetFderivNeZeroOrbit

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
open GlobalTheory GlobalTheory.OrbitCoord
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.OrbitCoord
theorem _root_.solution {r : ℕ} {Ψ : Finset (E →+* ℂ)} {o a c : Frame Ψ r}
    (ho : ∀ τ, (mat o τ).det ≠ 0) (h : rmul o a = rmul o c) : a = c := by
  funext τ
  have h1 : mat o τ * mat a τ = mat o τ * mat c τ := congrFun h τ
  have hu : IsUnit (mat o τ) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (ho τ))
  exact hu.mul_left_cancel h1
end GlobalTheory.OrbitCoord
