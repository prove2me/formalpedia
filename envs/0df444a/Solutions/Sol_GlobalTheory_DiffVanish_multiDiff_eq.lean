-- Prove2me | solution 1 for GlobalTheory.DiffVanish.multiDiff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:22:11.606436+00:00
-- url     : https://prove2.me/submissions/5feae2a7-d97f-4bca-8156-7f86603a2a7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_bwdDiff_apply
import Theorems.Thm_GlobalTheory_multiDiff_cons

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
    (x y : G) : multiDiff g φ x = multiDiff g φ y := by
  have := congrFun (h (Fin.cons (x - y) g)) x
  rw [multiDiff_cons, bwdDiff_apply, sub_sub_cancel] at this
  exact sub_eq_zero.1 this
end DiffVanish
end GlobalTheory
