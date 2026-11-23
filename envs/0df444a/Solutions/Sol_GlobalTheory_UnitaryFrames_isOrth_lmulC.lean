-- Prove2me | solution 1 for GlobalTheory.UnitaryFrames.isOrth_lmulC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:31.877106+00:00
-- url     : https://prove2.me/submissions/41f10a36-c5b0-4671-be56-723b245277f8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Theorems.Thm_P2M_GlobalTheory_UnitaryFrames_col_mul__08ccc1f94cd1

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
theorem _root_.solution {r : ℕ} (X : Data E r) {n : X.Ψ → Matrix (Fin r) (Fin r) ℂ}
    (hn : X.IsUnitaryC n) {x : Frame X.Ψ r} (hx : IsOrth X x) : IsOrth X (X.lmulC n x) := by
  intro τ
  rw [← hx τ, show mat (X.lmulC n x) τ = n τ * mat x τ from rfl]
  ext a b
  simp only [gram, Matrix.of_apply, col_mul', hn τ]
end GlobalTheory.UnitaryFrames
