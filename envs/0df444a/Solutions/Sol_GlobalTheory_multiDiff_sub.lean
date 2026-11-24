-- Prove2me | solution 1 for GlobalTheory.multiDiff_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:22:39.209532+00:00
-- url     : https://prove2.me/submissions/1b956b2b-cd24-4b2f-b3ad-9d971623b7ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] (g : ι → G) (φ ψ : G → M) :
    multiDiff g (φ - ψ) = multiDiff g φ - multiDiff g ψ := by
  simp [multiDiff_eq_shiftAct]
end GlobalTheory
