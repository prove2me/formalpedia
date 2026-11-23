-- Prove2me | solution 1 for GlobalTheory.UnitaryFrames.quotient_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:02.57883+00:00
-- url     : https://prove2.me/submissions/98d11d0d-646f-4c19-a419-404b7852f46d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Theorems.Thm_GlobalTheory_UnitaryFrames_hermC_mulVec
import Theorems.Thm_GlobalTheory_UnitaryFrames_val_toGL

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
theorem _root_.solution {r : ℕ} (X : Data E r) {x y : Frame X.Ψ r} (hx : IsOrth X x)
    (hy : IsOrth X y) :
    X.IsUnitaryC fun τ => ((toGL X hx * (toGL X hy)⁻¹) τ : Matrix (Fin r) (Fin r) ℂ) := by
  intro τ u w
  have key : ∀ u w, hermC τ.1 X.Gm (mat x τ *ᵥ u) (mat x τ *ᵥ w) =
      hermC τ.1 X.Gm (mat y τ *ᵥ u) (mat y τ *ᵥ w) := by
    intro u w
    rw [hermC_mulVec, hermC_mulVec, hx τ, hy τ]
  have h := key ((((toGL X hy τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
    ((((toGL X hy τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
  rw [← val_toGL X hx, ← val_toGL X hy] at h
  simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
  simp only [Pi.mul_apply, Pi.inv_apply, Units.val_mul]
  exact h
end GlobalTheory.UnitaryFrames
