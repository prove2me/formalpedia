-- Prove2me | solution 1 for GroundTheory.LocalField.differentiable_evalQpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:35:26.869747+00:00
-- url     : https://prove2.me/submissions/d2388908-07ed-41bc-ad7f-e0fff4d56988

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
import Theorems.Thm_GroundTheory_LocalField_evalQpow_C_mul_T
import Theorems.Thm_GroundTheory_LocalField_evalQpow_add
import Theorems.Thm_GroundTheory_LocalField_differentiable_qpow
import Theorems.Thm_GroundTheory_LocalField_qpow_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution (P : LaurentPolynomial ℂ) : Differentiable ℂ (evalQpow K P) := by
  induction P using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    have : evalQpow K (p + q) = fun s => evalQpow K p s + evalQpow K q s :=
      funext fun s => evalQpow_add p q s
    rw [this]
    exact hp.add hq
  | C_mul_T n a =>
    have : evalQpow K (LaurentPolynomial.C a * LaurentPolynomial.T n) =
        fun s => a * ((residueCard K : ℂ) ^ (-s)) ^ n :=
      funext fun s => evalQpow_C_mul_T a n s
    rw [this]
    exact (differentiable_qpow.zpow (Or.inl fun s => qpow_ne_zero s)).const_mul a
end GroundTheory.LocalField
