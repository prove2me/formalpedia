-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.sumForm_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:47.555598+00:00
-- url     : https://prove2.me/submissions/74f0aae7-b7cb-4621-a020-8722c2ecb820

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity

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
theorem _root_.solution (x y : CycSum q) : sumForm q hq x y = sumForm q hq y x := by
  unfold sumForm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
end GroundTheory.Automorphic.ContragredientTranspose
