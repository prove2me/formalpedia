-- Prove2me | solution 1 for GlobalTheory.EvenCubicNorm.prodPow_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:42:46.992636+00:00
-- url     : https://prove2.me/submissions/596c88a5-71fe-45da-8beb-7bf5a4e324cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEvenCubicUnitMultipleFractionRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.EvenCubicNorm
open Finset
variable {M : Type*} [CommGroup M] {ι : Type*} [Fintype ι]
namespace GlobalTheory.EvenCubicNorm
theorem _root_.solution [DecidableEq ι] (z : ι → ι → M) (k l : ι) :
    prodPow z (fun i j => if i = k ∧ j = l then 1 else 0) = z k l := by
  unfold prodPow
  rw [Finset.prod_eq_single k, Finset.prod_eq_single l]
  · simp
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi
    apply Finset.prod_eq_one
    intro j _; simp [hi]
  · simp
end GlobalTheory.EvenCubicNorm
