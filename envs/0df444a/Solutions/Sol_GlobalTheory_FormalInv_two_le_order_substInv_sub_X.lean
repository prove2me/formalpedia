-- Prove2me | solution 1 for GlobalTheory.FormalInv.two_le_order_substInv_sub_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:29:39.135652+00:00
-- url     : https://prove2.me/submissions/14e0ccb6-dbfe-4b6c-b7d7-f99d3da91657

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_linearPart_substInv
import Theorems.Thm_GlobalTheory_FormalInv_two_le_order_sub_X_iff

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
variable [Fintype σ] [DecidableEq σ]
variable {u v : σ → MvPowerSeries σ R}
namespace GlobalTheory.FormalInv
theorem _root_.solution (hu : ∀ i, (2 : ℕ∞) ≤ (u i - X i).order) (i : σ) :
    (2 : ℕ∞) ≤ (substInv u i - X i).order := by
  obtain ⟨h0, h1⟩ := two_le_order_sub_X_iff.1 hu
  refine two_le_order_sub_X_iff.2 ⟨constantCoeff_substInv h0, ?_⟩ i
  rw [linearPart_substInv h0 (h1 ▸ isUnit_one), h1, inv_one]
end GlobalTheory.FormalInv
