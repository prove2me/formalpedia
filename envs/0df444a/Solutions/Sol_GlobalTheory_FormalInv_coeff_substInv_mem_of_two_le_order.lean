-- Prove2me | solution 1 for GlobalTheory.FormalInv.coeff_substInv_mem_of_two_le_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:31:07.285016+00:00
-- url     : https://prove2.me/submissions/07777f0c-58b2-44ae-8b37-8dfd00e585dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_apply
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_symm_apply
import Theorems.Thm_GlobalTheory_FormalInv_coeff_substInv_mem
import Theorems.Thm_GlobalTheory_FormalInv_two_le_order_sub_X_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_apply
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_symm_apply

set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable [Fintype σ] [DecidableEq σ]
variable {u v : σ → MvPowerSeries σ R}
namespace GlobalTheory.FormalInv
theorem _root_.solution (hu : ∀ i, (2 : ℕ∞) ≤ (u i - X i).order)
    {S : Subring R} {g : ℕ} (huS : ∀ i (d : σ →₀ ℕ), d.degree < g → coeff d (u i) ∈ S) (i : σ)
    (d : σ →₀ ℕ) (hd : d.degree < g) : coeff d (substInv u i) ∈ S := by
  obtain ⟨h0, h1⟩ := two_le_order_sub_X_iff.1 hu
  refine coeff_substInv_mem h0 (fun i j => ?_) huS i d hd
  rw [h1, inv_one, Matrix.one_apply]
  split_ifs <;> simp
end GlobalTheory.FormalInv
