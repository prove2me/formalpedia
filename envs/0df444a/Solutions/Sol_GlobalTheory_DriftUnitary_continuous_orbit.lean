-- Prove2me | solution 1 for GlobalTheory.DriftUnitary.continuous_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:00.336117+00:00
-- url     : https://prove2.me/submissions/5cc7df1a-beb8-4a14-acdb-9e1d90469763

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionOrthonormalHermitianFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FrameStepOfRightMulRealUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionRealUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.DriftUnitary
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.DriftUnitary
namespace _root_.GlobalTheory.DriftUnitary
theorem _root_.solution {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ))
    (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    Continuous fun g : H => X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC
  refine continuous_pi fun τ => ?_
  exact (Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).matrix_mul
    continuous_const
end _root_.GlobalTheory.DriftUnitary
end GlobalTheory.DriftUnitary
