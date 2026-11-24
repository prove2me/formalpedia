-- Prove2me | solution 1 for GlobalTheory.FormalCalc.subst_elim_zero_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:43:44.678953+00:00
-- url     : https://prove2.me/submissions/c1d18d6f-9610-4ce1-8e97-04ad51528d90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Theorems.Thm_GlobalTheory_FormalCalc_subst_subst
import Theorems.Thm_GlobalTheory_FormalCalc_subst_sumElim
import Theorems.Thm_GlobalTheory_FormalCalc_coeff_subst_kill
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
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
namespace GlobalTheory.FormalCalc
theorem _root_.solution [Finite σ] [Finite τ] (f : MvPowerSeries (σ ⊕ τ) A) :
    subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) f = 0 ↔
      ∀ α : σ ⊕ τ →₀ ℕ, (∀ i, α (inl i) = 0) → coeff α f = 0 := by
  have hk := coeff_subst_kill (A := A) (inl : σ → σ ⊕ τ)
    (b := Sum.elim (fun _ => 0) fun j => X (inr j)) (by simp) (by simp) f
  constructor
  · intro h α hα
    have hb : HasSubst (fun j => X (inr j) : τ → MvPowerSeries (σ ⊕ τ) A) :=
      hasSubst_of_constantCoeff_zero (by simp)
    have h2 := congrArg (subst (fun j => X (inr j) : τ → MvPowerSeries (σ ⊕ τ) A)) h
    simp [subst_subst hb, subst_sumElim, subst_X hb, subst_zero' hb] at h2
    rw [← if_pos hα (t := coeff α f) (e := 0), ← hk, h2, map_zero]
  · intro h
    have h1 : subst (Sum.elim (fun _ => 0) fun j => X (inr j) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) f = 0 := by
      ext α
      rw [hk]
      split_ifs with hα
      · simp [h α hα]
      · simp
    have hb : HasSubst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) :=
      hasSubst_of_constantCoeff_zero (by simp)
    have h2 := congrArg (subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A)) h1
    simpa [subst_subst hb, subst_sumElim, subst_X hb, subst_zero' hb] using h2
end GlobalTheory.FormalCalc
