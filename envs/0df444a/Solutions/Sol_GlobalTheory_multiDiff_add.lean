-- Prove2me | solution 1 for GlobalTheory.multiDiff_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:09.493782+00:00
-- url     : https://prove2.me/submissions/b9abd9e4-2194-47ae-9d54-70bb5876cd06

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
    multiDiff g (φ + ψ) = multiDiff g φ + multiDiff g ψ := by
  simp [multiDiff_eq_shiftAct]
end GlobalTheory
