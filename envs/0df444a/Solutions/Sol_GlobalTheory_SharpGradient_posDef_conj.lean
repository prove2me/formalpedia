-- Prove2me | solution 1 for GlobalTheory.SharpGradient.posDef_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:10:28.024075+00:00
-- url     : https://prove2.me/submissions/02268a35-97af-47b3-b429-9446e9992d18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry

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
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
namespace GlobalTheory.SharpGradient
theorem _root_.solution {p : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (hU : Uᴴ * U = 1)
    {A : Matrix (Fin p) (Fin p) ℂ} (hA : A.PosDef) : (Uᴴ * A * U).PosDef := by
  have hu : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact IsUnit.of_mul_eq_one_right _ h
  exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hu).2 hA
end GlobalTheory.SharpGradient
