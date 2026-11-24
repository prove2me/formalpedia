-- Prove2me | solution 1 for GlobalTheory.apply_perpVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:23:03.052059+00:00
-- url     : https://prove2.me/submissions/3fa85e05-0b6e-4b6e-b5ca-6d0a9386933c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_pairingMatrix_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.pairingMatrix_apply

set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (ε : ι → Module.Dual R M) (e' : ι → M) (g : M) (c : ι) :
    ε c (perpVector ε e' g) = 0 := by
  have key : ∀ a, ∑ a', (pairingMatrix ε e').adjugate a a' * ε a g * ε c (e' a')
      = ε a g * ((pairingMatrix ε e').det * if a = c then 1 else 0) := by
    intro a
    have h := congrFun (congrFun (Matrix.adjugate_mul (pairingMatrix ε e')) a) c
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [pairingMatrix_apply]; ring
  simp only [perpVector, map_sub, map_sum, map_smul, smul_eq_mul, key]
  simp [mul_comm]
end GlobalTheory
