-- Prove2me | solution 1 for GlobalTheory.DiffVanish.map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:38:40.021468+00:00
-- url     : https://prove2.me/submissions/398b3d74-fc03-4604-8b07-acef446e6663

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_multiDiff_map

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
theorem _root_.solution {N : Type*} [AddCommGroup N] {n : ℕ} {φ : G → M} (h : DiffVanish n φ)
    (f : M →+ N) : DiffVanish n (f ∘ φ) := fun g ↦ by
  rw [multiDiff_map, h]; ext; simp
end DiffVanish
end GlobalTheory
