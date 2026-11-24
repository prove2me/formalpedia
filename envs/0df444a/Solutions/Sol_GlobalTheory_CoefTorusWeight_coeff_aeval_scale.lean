-- Prove2me | solution 1 for GlobalTheory.CoefTorusWeight.coeff_aeval_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:15:59.755077+00:00
-- url     : https://prove2.me/submissions/634247f7-e624-4ab3-9832-73788138b4ce

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceEndomorphismPreservesTorusWei
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
open GlobalTheory GlobalTheory.CoefTorusWeight
namespace GlobalTheory.CoefTorusWeight
theorem _root_.solution {K σ : Type} [Field K] [Fintype σ] (c : σ → K) (F : MvPolynomial σ K)
    (m : σ →₀ ℕ) :
    coeff m (aeval (fun v => (C (c v) * X v : MvPolynomial σ K)) F) = (∏ v, c v ^ m v) * coeff m F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have h : aeval (fun v => (C (c v) * X v : MvPolynomial σ K)) (monomial u a)
        = monomial u ((∏ v, c v ^ u v) * a) := by
      rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), monomial_eq,
        Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod, algebraMap_eq, C_mul]
      ring
    rw [h, coeff_monomial, coeff_monomial]
    split_ifs with hu
    · rw [hu]
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
end GlobalTheory.CoefTorusWeight
