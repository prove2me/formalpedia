-- Prove2me | solution 1 for GlobalTheory.HeightEnds.norm_det_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:33.378431+00:00
-- url     : https://prove2.me/submissions/1a8463a0-4e61-4181-83ec-8aeb8e14ef79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightBotTop
import Theorems.Thm_GlobalTheory_HeightEnds_gram_eq_mul

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
open GlobalTheory GlobalTheory.HeightEnds
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HeightEnds
theorem _root_.solution {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (τ : X.Ψ) :
    ‖(mat x τ).det‖ ^ 2 * ‖τ.1 X.Gm.det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (hx τ)
  simp only [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_conjTranspose,
    Matrix.det_diagonal, norm_mul, norm_star, norm_prod] at h
  have h1 : ∀ a : Fin r, ‖((sgn X.p0 (a : ℕ) : ℝ) : ℂ)‖ = 1 := by
    intro a
    unfold sgn
    split_ifs <;> simp
  simp only [h1, Finset.prod_const_one] at h
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← h]
  ring
end GlobalTheory.HeightEnds
