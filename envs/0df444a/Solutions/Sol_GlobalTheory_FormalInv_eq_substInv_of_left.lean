-- Prove2me | solution 1 for GlobalTheory.FormalInv.eq_substInv_of_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:53:39.455546+00:00
-- url     : https://prove2.me/submissions/c00579c8-c803-4bd7-a8e2-537a28ece75b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder

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
theorem _root_.solution (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (h : ∀ i, (v i).subst u = X i) : v = substInv u :=
  eq_of_subst_eq_X hu (constantCoeff_substInv hu) h (subst_substInv_right hu
    (IsUnit.of_mul_eq_one_right _ (linearPart_mul_eq_one hv hu h)))
end GlobalTheory.FormalInv
