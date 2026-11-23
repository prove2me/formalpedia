-- Prove2me | solution 1 for GlobalTheory.FormalInv.eq_substInv_of_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:24.15451+00:00
-- url     : https://prove2.me/submissions/4905c5c3-4eff-4868-944f-4e136b133ff8

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
    (hv : ∀ i, constantCoeff (v i) = 0) (h : ∀ i, (u i).subst v = X i) : v = substInv u :=
  (eq_of_subst_eq_X hu hv (subst_substInv_left hu
    (IsUnit.of_mul_eq_one _ (linearPart_mul_eq_one hu hv h))) h).symm
end GlobalTheory.FormalInv
