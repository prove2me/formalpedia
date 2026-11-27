-- Prove2me | solution 1 for GlobalTheory.diffVanish_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:13.533801+00:00
-- url     : https://prove2.me/submissions/9d61ce80-3f4f-4862-ac2b-9324a5b67d5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_P2M_GlobalTheory_multiDiff_cons__e9b475c9a4ea

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
theorem _root_.solution {n : ℕ} {φ : G → M} :
    DiffVanish (n + 1) φ ↔ ∀ a, DiffVanish n (bwdDiff a φ) := by
  refine ⟨fun h a g ↦ by rw [← multiDiff_cons', h], fun h g ↦ ?_⟩
  rw [← Fin.cons_self_tail g, multiDiff_cons', h]
end GlobalTheory
