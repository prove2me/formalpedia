-- Prove2me | solution 1 for GlobalTheory.EvenCubicNorm.prodPow_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:42:44.916038+00:00
-- url     : https://prove2.me/submissions/f7117595-2661-4a61-bf13-d208d9ea5296

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
theorem _root_.solution (z : ι → ι → M) (e e' : ι → ι → ℤ) :
    prodPow z e * prodPow z e' = prodPow z (fun i j => e i j + e' i j) := by
  simp only [prodPow, zpow_add, Finset.prod_mul_distrib]
end GlobalTheory.EvenCubicNorm
