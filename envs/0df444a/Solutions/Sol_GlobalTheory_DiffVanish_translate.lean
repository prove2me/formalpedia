-- Prove2me | solution 1 for GlobalTheory.DiffVanish.translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:23:49.39036+00:00
-- url     : https://prove2.me/submissions/9ba5e631-9d73-408c-82e2-f93d425a7e56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_multiDiff_translate

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
theorem _root_.solution {n : ℕ} {φ : G → M} (h : DiffVanish n φ) (a : G) :
    DiffVanish n (fun y ↦ φ (a + y)) := fun g ↦ by
  ext x; rw [multiDiff_translate, h]; rfl
end DiffVanish
end GlobalTheory
