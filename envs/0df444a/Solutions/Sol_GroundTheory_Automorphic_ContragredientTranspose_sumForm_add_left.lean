-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.sumForm_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:46.870072+00:00
-- url     : https://prove2.me/submissions/9515f930-cb81-4100-91bd-d9526f79ba59

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ellQ_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → F[X])
  (hq : ∀ i, q i ≠ 0)
omit [DecidableEq ι]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (x x' y : CycSum q) :
    sumForm q hq (x + x') y = sumForm q hq x y + sumForm q hq x' y := by
  unfold sumForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DirectSum.add_apply, add_mul, ellQ_add]
end GroundTheory.Automorphic.ContragredientTranspose
