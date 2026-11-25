-- Prove2me | solution 1 for GlobalTheory.DiffVanish.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:38:58.709559+00:00
-- url     : https://prove2.me/submissions/b4e1d494-6156-478d-9d8b-50c9cee8b4c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_DiffVanish_multiDiff_eq_zero

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
theorem _root_.solution {m n : ℕ} {φ : G → M} (h : DiffVanish m φ) (hmn : m ≤ n) :
    DiffVanish n φ := fun g ↦ h.multiDiff_eq_zero (by simpa) g
end DiffVanish
end GlobalTheory
