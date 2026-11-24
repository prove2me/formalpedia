-- Prove2me | solution 1 for GlobalTheory.DiffVanish.form_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:41:07.027402+00:00
-- url     : https://prove2.me/submissions/001f288c-9298-49a7-9043-54f9955a7146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_DiffVanish_multiDiff_eq

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
theorem _root_.solution {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ) (g : Fin d → G)
    (x : G) : h.form g = multiDiff g φ x := h.multiDiff_eq g 0 x
end DiffVanish
end GlobalTheory
