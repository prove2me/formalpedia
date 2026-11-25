-- Prove2me | solution 1 for GlobalTheory.TensorLat.tensorEps_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:35:05.257535+00:00
-- url     : https://prove2.me/submissions/14d1ce08-7149-4f43-9eee-fae1c5acf508

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
noncomputable section
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution (w₀ : 𝓞 E) (γ : Fin n → Vsp dim) :
    tensorEps w₀ γ = ∏ k, cexp (Real.pi * I * ((Hf (γ k) (act w₀ (γ k))).im : ℂ)) := by
  rw [tensorEps, HC, Complex.im_sum, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
end GlobalTheory.TensorLat
