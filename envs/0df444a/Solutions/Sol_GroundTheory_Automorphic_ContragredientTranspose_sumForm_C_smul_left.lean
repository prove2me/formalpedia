-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.sumForm_C_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:00:30.9438+00:00
-- url     : https://prove2.me/submissions/492457dc-30ef-4114-8344-174c2fc37340

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ellQ_C_smul

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
theorem _root_.solution (c : F) (x y : CycSum q) :
    sumForm q hq (C c • x) y = c * sumForm q hq x y := by
  unfold sumForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DirectSum.smul_apply, smul_mul_assoc, ellQ_C_smul]
end GroundTheory.Automorphic.ContragredientTranspose
