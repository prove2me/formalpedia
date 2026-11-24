-- Prove2me | solution 1 for GlobalTheory.FormalInv.subst_sumFamily_sumFamily
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:50:54.919588+00:00
-- url     : https://prove2.me/submissions/b901454d-5eca-469e-a305-0bc67e01c976

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_subst_sumFamily_rename_inl
import Theorems.Thm_GlobalTheory_FormalInv_subst_sumFamily_rename_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable {σ' τ' : Type*}
namespace GlobalTheory.FormalInv
theorem _root_.solution {υ' : Type*} [Finite σ] [Finite σ'] [Finite τ] [Finite τ']
    (b : υ → MvPowerSeries σ R) (b' : υ' → MvPowerSeries σ' R)
    {a : σ → MvPowerSeries τ R} {a' : σ' → MvPowerSeries τ' R}
    (ha : ∀ i, constantCoeff (a i) = 0) (ha' : ∀ j, constantCoeff (a' j) = 0) (s : υ ⊕ υ') :
    (sumFamily b b' s).subst (sumFamily a a') =
      sumFamily (fun i => (b i).subst a) (fun j => (b' j).subst a') s := by
  cases s
  · exact subst_sumFamily_rename_inl ha ha' _
  · exact subst_sumFamily_rename_inr ha ha' _
end GlobalTheory.FormalInv
