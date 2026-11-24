-- Prove2me | solution 1 for GlobalTheory.FormalCalc.eq_sum_of_additive_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:59:44.44418+00:00
-- url     : https://prove2.me/submissions/4e3e793f-cf7b-403e-bde9-720530f96dea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Theorems.Thm_GlobalTheory_FormalCalc_subst_subst
import Theorems.Thm_GlobalTheory_FormalCalc_subst_sumElim
import Theorems.Thm_GlobalTheory_FormalCalc_subst_elim_X
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_pderiv_subst__7084ce132710
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_X_ite
import Theorems.Thm_GlobalTheory_FormalCalc_ext_of_pderiv_of_subst
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_sum__4ef444666b63
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_zero__b9c8f67e64a1
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
variable [IsAddTorsionFree A]
namespace GlobalTheory.FormalCalc
theorem _root_.solution [Fintype σ] [Finite τ] {f : MvPowerSeries (σ ⊕ τ) A}
    (h : subst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) f =
      subst (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) f +
      subst (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) f) :
    f = ∑ i, X (inl i) * subst (fun j => X (inr j) : τ → MvPowerSeries (σ ⊕ τ) A)
      (subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) (pderiv A (inl i) f)) := by
  classical
  have := Fintype.ofFinite τ
  have hb : HasSubst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) fun j => X (inr j)) :
      σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hc : HasSubst (fun j => X (inr j) : τ → MvPowerSeries (σ ⊕ τ) A) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have hd : HasSubst (Sum.elim (fun _ => 0) fun j => X (inr j) :
      σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  refine ext_of_pderiv_of_subst inl (b := Sum.elim (fun _ => 0) fun j => X (inr j))
    (by simp) (by simp) (fun i => ?_) ?_
  · have h1 := congrArg (pderiv A (inr (inl i))) h
    simp [pderiv_subst', pderiv_X_ite] at h1
    have h2 := congrArg (subst (Sum.elim (fun i => X (inl i))
      (Sum.elim (fun _ => 0) fun j => X (inr j)) : σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A)) h1
    simp [subst_subst hb, subst_sumElim, subst_X hb, subst_add hb, subst_elim_X] at h2
    conv_lhs => rw [h2]
    simp [pderiv_subst', pderiv_X_ite, subst_subst hc, subst_sumElim, subst_X hc, subst_zero' hc]
  · have h2 := congrArg (subst (Sum.elim (fun i => X (inl i))
      (Sum.elim (fun _ => 0) fun j => X (inr j)) : σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A)) h
    simp [subst_subst hb, subst_sumElim, subst_X hb, subst_add hb, subst_elim_X] at h2
    simp [h2, subst_sum' hd, subst_mul hd, subst_X hd]
end GlobalTheory.FormalCalc
