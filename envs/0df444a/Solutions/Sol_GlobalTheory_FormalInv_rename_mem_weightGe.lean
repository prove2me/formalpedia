-- Prove2me | solution 1 for GlobalTheory.FormalInv.rename_mem_weightGe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:27:06.370712+00:00
-- url     : https://prove2.me/submissions/112b0351-ad4c-4738-88fc-7796e2814506

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_X_mem_weightGe

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
theorem _root_.solution [Finite σ] (e : σ → τ) {w : τ → ℕ} {m : ℕ} {f : MvPowerSeries σ R}
    (hf : f ∈ weightGe (w ∘ e) m) : rename e f ∈ weightGe w m := by
  rw [rename_eq_subst]
  exact subst_mem_weightGe (HasSubst.X_comp e) (fun s => X_mem_weightGe w (e s)) hf
end GlobalTheory.FormalInv
