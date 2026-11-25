-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.capelliMatrix_pow_succ_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:47.335922+00:00
-- url     : https://prove2.me/submissions/998a0aad-f4f5-4c86-823c-d8e79331fb8c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EMulSubMulCapelliMatrixPow
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (m : ℕ) (c d : Fin n) :
    (capelliMatrix ^ (m + 1)) c d = ∑ i : Fin m → Fin n,
      word (List.ofFn fun t : Fin (m + 1) => ((Fin.cons c i : Fin (m + 1) → Fin n) t,
        (Fin.snoc i d : Fin (m + 1) → Fin n) t)) := by
  induction m generalizing c with
  | zero =>
    rw [Fintype.sum_unique]
    simp [capelliMatrix, word, List.ofFn_succ, Fin.snoc]
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    rw [← Fin.cons_snoc_eq_snoc_cons, List.ofFn_succ, word_cons]
    simp [capelliMatrix]
end GroundTheory.Automorphic.HarishChandra
