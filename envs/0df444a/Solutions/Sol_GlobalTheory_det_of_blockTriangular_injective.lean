-- Prove2me | solution 1 for GlobalTheory.det_of_blockTriangular_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:44:44.813332+00:00
-- url     : https://prove2.me/submissions/c89f4248-1b79-469e-91ca-9823d70b0eec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetOfBlockTriangularInjective

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {m α R : Type} [Fintype m] [DecidableEq m]
    [LinearOrder α] [CommRing R] (M : Matrix m m R) (f : m → α) (hf : Function.Injective f)
    (h : M.BlockTriangular f) : M.det = ∏ i, M i i := by
  letI : LinearOrder m := LinearOrder.lift' f hf
  exact Matrix.det_of_upperTriangular (M := M) (fun i j hij => h hij)
end GlobalTheory
