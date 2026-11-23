-- Prove2me | solution 1 for GlobalTheory.UnitaryFrames.hermC_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:13.22329+00:00
-- url     : https://prove2.me/submissions/70b7d947-bb7a-48ea-94d1-066bd5eaf163

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
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.UnitaryFrames
theorem _root_.solution {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) (u w : Fin r → ℂ) :
    hermC τ G (P *ᵥ u) (P *ᵥ w) = u ⬝ᵥ (gram τ G P *ᵥ star w) := by
  have h : star (P *ᵥ w) = P.map (starRingEnd ℂ) *ᵥ star w := by
    ext a
    simp [Matrix.mulVec, dotProduct]
  rw [hermC_eq_dot, gram_eq_mul, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]
end GlobalTheory.UnitaryFrames
