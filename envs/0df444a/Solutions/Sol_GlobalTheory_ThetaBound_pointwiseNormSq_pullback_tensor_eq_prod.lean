-- Prove2me | solution 1 for GlobalTheory.ThetaBound.pointwiseNormSq_pullback_tensor_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:59:13.369171+00:00
-- url     : https://prove2.me/submissions/ed390832-765e-4a0e-879e-1a1f79c7bca9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.ThetaBound
open TensorLat
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.ThetaBound
theorem _root_.solution (X : PT E) {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim}
    (hπ : ∀ v w, Hf (π v) (π w) = q * Hf v w) (s : (Fin 1 → Vsp X.dim) → ℂ)
    (v : Fin n → Vsp X.dim) :
    X.ptN2 q (s0 X π s) v = ∏ k, X.ptN2 1 s fun _ => π (v k) := by
  unfold PT.ptN2 s0
  rw [norm_prod, ← Finset.prod_pow, Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  simp only [HC, Complex.re_sum, Fin.sum_univ_one, hπ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
  push_cast
  ring
end GlobalTheory.ThetaBound
