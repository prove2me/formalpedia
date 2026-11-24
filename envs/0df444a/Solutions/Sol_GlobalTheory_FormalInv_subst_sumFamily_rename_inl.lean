-- Prove2me | solution 1 for GlobalTheory.FormalInv.subst_sumFamily_rename_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:27:08.031411+00:00
-- url     : https://prove2.me/submissions/9b1824ad-365f-4b2c-b87d-243e8627e34e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inl
import Theorems.Thm_GlobalTheory_FormalInv_constantCoeff_sumFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inl

set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable {σ' τ' : Type*}
namespace GlobalTheory.FormalInv
theorem _root_.solution [Finite σ] [Finite σ'] [Finite τ] [Finite τ']
    {a : σ → MvPowerSeries τ R} {a' : σ' → MvPowerSeries τ' R}
    (ha : ∀ i, constantCoeff (a i) = 0) (ha' : ∀ j, constantCoeff (a' j) = 0)
    (f : MvPowerSeries σ R) :
    (rename Sum.inl f).subst (sumFamily a a') = rename Sum.inl (f.subst a) := by
  have h := hasSubst_of_constantCoeff_zero (constantCoeff_sumFamily ha ha')
  rw [rename_eq_subst, rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) h,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) (HasSubst.X_comp _)]
  congr 1
  funext i
  rw [Function.comp_apply, subst_X h, sumFamily_inl, rename_eq_subst]
end GlobalTheory.FormalInv
