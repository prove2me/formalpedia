-- Prove2me | solution 1 for GlobalTheory.FormalInv.linearPart_substInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:11:56.017776+00:00
-- url     : https://prove2.me/submissions/f988c56a-e31f-4a6a-b568-476351acbbdf

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
theorem _root_.solution (hu : ∀ i, constantCoeff (u i) = 0) (hA : IsUnit (linearPart u)) :
    linearPart (substInv u) = (linearPart u)⁻¹ :=
  (Matrix.inv_eq_right_inv (linearPart_mul_eq_one hu (constantCoeff_substInv hu)
    (subst_substInv_right hu hA))).symm
end GlobalTheory.FormalInv
