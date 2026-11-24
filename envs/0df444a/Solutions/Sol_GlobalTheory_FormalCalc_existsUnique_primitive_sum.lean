-- Prove2me | solution 1 for GlobalTheory.FormalCalc.existsUnique_primitive_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:05:52.065907+00:00
-- url     : https://prove2.me/submissions/84fa4bf1-a830-48b3-b5d5-2d3f980962c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Theorems.Thm_GlobalTheory_FormalCalc_subst_elim_zero_eq_zero_iff
import Theorems.Thm_GlobalTheory_FormalCalc_existsUnique_primitive_param
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Sum
variable {σ τ ι κ μ A : Type*} [CommRing A]
namespace GlobalTheory.FormalCalc
theorem _root_.solution [Finite σ] [Finite τ] [Algebra ℚ A]
    (a : σ → MvPowerSeries (σ ⊕ τ) A)
    (ha : ∀ i j, pderiv A (inl i) (a j) = pderiv A (inl j) (a i)) :
    ∃! f : MvPowerSeries (σ ⊕ τ) A,
      subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) f = 0 ∧
        ∀ i, pderiv A (inl i) f = a i := by
  simp only [subst_elim_zero_eq_zero_iff]
  exact existsUnique_primitive_param inl_injective a ha
end GlobalTheory.FormalCalc
