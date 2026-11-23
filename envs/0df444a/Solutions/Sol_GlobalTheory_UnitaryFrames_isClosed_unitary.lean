-- Prove2me | solution 1 for GlobalTheory.UnitaryFrames.isClosed_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:48.043653+00:00
-- url     : https://prove2.me/submissions/affc9f73-c212-4dac-856a-603a97eaa247

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Theorems.Thm_GlobalTheory_UnitaryFrames_hermC_eq_dot

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
open GlobalTheory GlobalTheory.UnitaryFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.UnitaryFrames
theorem _root_.solution {r : ℕ} (X : Data E r) :
    IsClosed {g : X.Ψ → GL (Fin r) ℂ | X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)} := by
  simp only [Data.IsUnitaryC, Set.setOf_forall]
  refine isClosed_iInter fun τ => isClosed_iInter fun u => isClosed_iInter fun w => ?_
  refine isClosed_eq ?_ continuous_const
  have hc : Continuous fun g : X.Ψ → GL (Fin r) ℂ => (g τ : Matrix (Fin r) (Fin r) ℂ) :=
    Units.continuous_val.comp (continuous_apply τ)
  simp only [hermC_eq_dot]
  exact (hc.matrix_mulVec continuous_const).dotProduct
    (continuous_const.matrix_mulVec (hc.matrix_mulVec continuous_const).star)
end GlobalTheory.UnitaryFrames
