-- Prove2me | solution 1 for GlobalTheory.DiffVanish.form_comp_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:38:52.552999+00:00
-- url     : https://prove2.me/submissions/c5fae2be-183b-462d-bbc0-22f399cfbd1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_multiDiff_comp_equiv
import Theorems.Thm_GlobalTheory_DiffVanish_form_apply

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
theorem _root_.solution {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ)
    (g : Fin d → G) (σ : Equiv.Perm (Fin d)) : h.form (g ∘ σ) = h.form g := by
  rw [h.form_apply _ 0, h.form_apply _ 0, multiDiff_comp_equiv]
end DiffVanish
end GlobalTheory
