-- Prove2me | solution 1 for GlobalTheory.FormalInv.rename_mem_coeffsIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:11:58.799809+00:00
-- url     : https://prove2.me/submissions/eb62c33e-dc8f-4af0-b8e9-836b2e0049b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_X_mem_coeffsIn
import Theorems.Thm_GlobalTheory_FormalInv_subst_mem_coeffsIn
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
theorem _root_.solution {κ : Type*} [Finite σ] (e : σ → τ) {S : Subring R} {w : κ → τ → ℕ}
    {g : κ → ℕ} {f : MvPowerSeries σ R} (hf : f ∈ coeffsIn S (fun k => w k ∘ e) g) :
    rename e f ∈ coeffsIn S w g := by
  rw [rename_eq_subst]
  exact subst_mem_coeffsIn (HasSubst.X_comp e) (fun k s => X_mem_weightGe (w k) (e s))
    (fun s => X_mem_coeffsIn (e s)) hf
end GlobalTheory.FormalInv
