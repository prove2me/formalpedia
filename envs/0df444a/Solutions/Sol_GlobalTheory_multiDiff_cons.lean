-- Prove2me | solution 1 for GlobalTheory.multiDiff_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:18.335187+00:00
-- url     : https://prove2.me/submissions/0e1d86ed-f37e-4ac8-970b-b7aef6c0640a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_shiftAct_diffElt

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
theorem _root_.solution {d : ℕ} (a : G) (g : Fin d → G) (φ : G → M) :
    multiDiff (Fin.cons a g : Fin (d + 1) → G) φ = bwdDiff a (multiDiff g φ) := by
  simp [multiDiff_eq_shiftAct, Fin.prod_univ_succ, shiftAct_diffElt]
end GlobalTheory
