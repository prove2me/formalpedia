-- Prove2me | solution 1 for GlobalTheory.FormalCalc.existsUnique_coboundary_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:24:49.106232+00:00
-- url     : https://prove2.me/submissions/75337370-3bd9-4a28-8a63-4ce2caf5fa93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Theorems.Thm_GlobalTheory_FormalCalc_subst_subst
import Theorems.Thm_GlobalTheory_FormalCalc_subst_sumElim
import Theorems.Thm_GlobalTheory_FormalCalc_subst_elim_X
import Theorems.Thm_GlobalTheory_FormalCalc_subst_elim_elim_X
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_pderiv_subst__7084ce132710
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_X_ite
import Theorems.Thm_GlobalTheory_FormalCalc_ext_of_pderiv_of_subst
import Theorems.Thm_GlobalTheory_FormalCalc_existsUnique_primitive_sum
import Theorems.Thm_GlobalTheory_FormalCalc_eq_sum_of_additive_param
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_comm
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
variable [Algebra ℚ A]
namespace GlobalTheory.FormalCalc
theorem _root_.solution [Finite σ] [Finite τ] {B : MvPowerSeries (σ ⊕ σ ⊕ τ) A}
    (h0 : subst (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) X) :
        σ ⊕ σ ⊕ τ → MvPowerSeries τ A) B = 0)
    (hsymm : subst (Sum.elim (fun i => X (inr (inl i))) (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) B = B)
    (hcoc : subst (Sum.elim (fun i => X (inl i))
        (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr (inr j)))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ σ ⊕ τ) A) B +
      subst (Sum.elim (fun i => X (inl i) + X (inr (inl i)))
        (Sum.elim (fun i => X (inr (inr (inl i)))) fun j => X (inr (inr (inr j)))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ σ ⊕ τ) A) B =
      subst (Sum.elim (fun i => X (inr (inl i)))
        (Sum.elim (fun i => X (inr (inr (inl i)))) fun j => X (inr (inr (inr j)))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ σ ⊕ τ) A) B +
      subst (Sum.elim (fun i => X (inl i))
        (Sum.elim (fun i => X (inr (inl i)) + X (inr (inr (inl i)))) fun j => X (inr (inr (inr j)))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ σ ⊕ τ) A) B) :
    ∃! k : MvPowerSeries (σ ⊕ τ) A, subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) k = 0 ∧
      (∀ i, subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) (pderiv A (inl i) k) = 0) ∧
      B = subst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k -
      subst (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k -
      subst (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k := by
  classical
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite τ
  have : IsAddTorsionFree A := .of_module_rat A

  have hz : HasSubst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun i => X (inr (inl i))) (Sum.elim (fun _ => 0) fun j => X (inr (inr j)))) :
        σ ⊕ σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hyz : HasSubst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun j => X (inr (inr j)))) :
        σ ⊕ σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hxy : HasSubst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hx : HasSubst (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hy : HasSubst (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hsw : HasSubst (Sum.elim (fun i => X (inr (inl i))) (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hy0 : HasSubst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) fun j => X (inr j)) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hy3 : HasSubst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) fun j => X (inr (inr j))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have h00 : HasSubst (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) X) :
        σ ⊕ σ ⊕ τ → MvPowerSeries τ A) := hasSubst_of_constantCoeff_zero (by simp)
  have ht : HasSubst (fun j => X (inr (inr j)) : τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hz2 : HasSubst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) := hasSubst_of_constantCoeff_zero (by simp)
  obtain ⟨a, ha⟩ : ∃ a : σ → MvPowerSeries (σ ⊕ τ) A, ∀ i, a i =
      subst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) fun j => X (inr j)) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) (pderiv A (inr (inl i)) B) :=
    ⟨_, fun _ => rfl⟩
  have hP (i : σ) : pderiv A (inr (inl i)) B =
      subst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) (a i) - subst (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) (a i) := by
    have h1 := congrArg (pderiv A (inr (inr (inl i)))) hcoc
    simp [pderiv_subst', pderiv_X_ite] at h1
    have h2 := congrArg (subst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun i => X (inr (inl i))) (Sum.elim (fun _ => 0) fun j => X (inr (inr j)))) :
        σ ⊕ σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A)) h1
    simp [subst_subst hz, subst_X hz, subst_add hz, subst_sub hz, subst_zero' hz, subst_sumElim, subst_elim_elim_X] at h2
    simp [ha, subst_subst hxy, subst_X hxy, subst_add hxy, subst_sub hxy, subst_zero' hxy, subst_subst hy, subst_X hy, subst_add hy, subst_sub hy, subst_zero' hy, subst_sumElim, h2]
  have hQ (i : σ) : pderiv A (inl i) B =
      subst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) (a i) - subst (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) (a i) := by
    have h1 := congrArg (pderiv A (inl i)) hsymm
    simp [pderiv_subst', pderiv_X_ite] at h1
    rw [← h1, hP]
    simp [subst_subst hsw, subst_X hsw, subst_add hsw, subst_sub hsw, subst_zero' hsw, subst_sumElim, add_comm]
  have hclosed (i j : σ) : pderiv A (inl i) (a j) = pderiv A (inl j) (a i) := by
    have h1 := pderiv_comm (inl i) (inr (inl j)) B
    rw [hP, hQ] at h1
    simp [pderiv_subst', pderiv_X_ite] at h1
    have h2 := congrArg (subst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) fun j => X (inr j)) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A)) h1
    simpa [subst_subst hy0, subst_X hy0, subst_add hy0, subst_sub hy0, subst_zero' hy0, subst_sumElim, subst_elim_X] using h2
  have ha0 (i : σ) : subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) (a i) = 0 := by
    have h1 := congrArg (subst (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) X) :
        σ ⊕ σ ⊕ τ → MvPowerSeries τ A)) (hP i)
    simp [subst_subst h00, subst_X h00, subst_add h00, subst_sub h00, subst_zero' h00, subst_sumElim] at h1
    simpa [ha, subst_subst hz2, subst_X hz2, subst_add hz2, subst_sub hz2, subst_zero' hz2, subst_sumElim] using h1
  obtain ⟨k, ⟨hk0, hk⟩, -⟩ := existsUnique_primitive_sum a hclosed
  have hB : B = subst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k -
      subst (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k -
      subst (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k := by
    refine ext_of_pderiv_of_subst (fun i : σ => (inr (inl i) : σ ⊕ σ ⊕ τ))
      (b := Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) fun j => X (inr (inr j)))) (by simp) (by simp) (fun i => ?_) ?_
    · simp [pderiv_subst', pderiv_X_ite, hk, hP]
    · have h1 := congrArg (subst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun j => X (inr (inr j)))) :
        σ ⊕ σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A)) hcoc
      have h2 := congrArg (subst (fun j => X (inr (inr j)) : τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A)) h0
      have h3 := congrArg (subst (fun j => X (inr (inr j)) : τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A)) hk0
      simp [subst_subst ht, subst_X ht, subst_add ht, subst_sub ht, subst_zero' ht, subst_sumElim] at h2 h3
      simp [subst_subst hyz, subst_X hyz, subst_add hyz, subst_sub hyz, subst_zero' hyz, subst_sumElim, h2] at h1
      simp [subst_subst hy3, subst_X hy3, subst_add hy3, subst_sub hy3, subst_zero' hy3, subst_sumElim, h1, h3]
  refine ⟨k, ⟨hk0, fun i => by rw [hk, ha0], hB⟩, ?_⟩
  rintro k' ⟨-, hk1, hk2⟩
  have hd := eq_sum_of_additive_param (f := k' - k) (by
    rw [subst_sub hxy, subst_sub hx, subst_sub hy]
    linear_combination hB - hk2)
  rw [← sub_eq_zero, hd]
  simp [subst_sub hz2, hk1, hk, ha0, subst_zero' (hasSubst_of_constantCoeff_zero (by simp) :
    HasSubst (fun j => X (inr j) : τ → MvPowerSeries (σ ⊕ τ) A))]
end GlobalTheory.FormalCalc
