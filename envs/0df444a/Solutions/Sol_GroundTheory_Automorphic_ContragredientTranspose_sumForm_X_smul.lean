-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.sumForm_X_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:55.191586+00:00
-- url     : https://prove2.me/submissions/586f4725-9eb8-4168-ae78-e1228ee7aad0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_smul_eq_mk_mul

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
theorem _root_.solution (x y : CycSum q) :
    sumForm q hq ((X : F[X]) • x) y = sumForm q hq x ((X : F[X]) • y) := by
  unfold sumForm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DirectSum.smul_apply, DirectSum.smul_apply, smul_eq_mk_mul, smul_eq_mk_mul]
  congr 1
  ring
end GroundTheory.Automorphic.ContragredientTranspose
