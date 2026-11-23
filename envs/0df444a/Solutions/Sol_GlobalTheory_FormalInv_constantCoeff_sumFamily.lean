-- Prove2me | solution 1 for GlobalTheory.FormalInv.constantCoeff_sumFamily
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:23.174341+00:00
-- url     : https://prove2.me/submissions/3b2eeef0-b4ac-417d-98c8-19cb37451d10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_apply
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_symm_apply
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inl
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_apply
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_symm_apply
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inl
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inr

set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable {σ' τ' : Type*}
namespace GlobalTheory.FormalInv
theorem _root_.solution [Finite τ] [Finite τ'] {a : σ → MvPowerSeries τ R}
    {a' : σ' → MvPowerSeries τ' R} (ha : ∀ i, constantCoeff (a i) = 0)
    (ha' : ∀ j, constantCoeff (a' j) = 0) (s : σ ⊕ σ') :
    constantCoeff (sumFamily a a' s) = 0 := by
  cases s <;> simp [ha, ha']
end GlobalTheory.FormalInv
