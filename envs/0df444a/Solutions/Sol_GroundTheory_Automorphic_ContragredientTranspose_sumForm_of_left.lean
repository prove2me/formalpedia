-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.sumForm_of_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:54:30.366018+00:00
-- url     : https://prove2.me/submissions/9feebe75-eb1f-4fe0-a847-3da11a1b35e1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ellQ_zero

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
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (i : ι) (b : F[X] ⧸ F[X] ∙ q i) (y : CycSum q) :
    sumForm q hq (DirectSum.of (fun i => F[X] ⧸ F[X] ∙ q i) i b) y = ellQ (q i) (hq i) (b * y i) := by
  unfold sumForm
  rw [Finset.sum_eq_single i]
  · rw [DirectSum.of_eq_same]
  · intro j _ hj
    rw [DirectSum.of_eq_of_ne _ _ _ hj, zero_mul, ellQ_zero]
  · simp
end GroundTheory.Automorphic.ContragredientTranspose
