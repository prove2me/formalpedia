-- Prove2me | solution 1 for GlobalTheory.DiffVanish.comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:22:10.529496+00:00
-- url     : https://prove2.me/submissions/5991a1a4-f1f2-4774-be86-d6e2389b1907

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_multiDiff_comap

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
namespace DiffVanish
theorem _root_.solution {H : Type*} [AddCommGroup H] {n : ℕ} {φ : G → M} (h : DiffVanish n φ)
    (f : H →+ G) : DiffVanish n (φ ∘ f) := fun g ↦ by
  rw [multiDiff_comap, h]; rfl
end DiffVanish
end GlobalTheory
