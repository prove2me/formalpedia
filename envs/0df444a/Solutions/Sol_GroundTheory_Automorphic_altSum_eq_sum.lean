-- Prove2me | solution 1 for GroundTheory.Automorphic.altSum_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:35.245616+00:00
-- url     : https://prove2.me/submissions/da5313a9-ffdb-4fcd-b1b8-897608d915f7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_AltSum
import Theorems.Thm_GroundTheory_Automorphic_altSum_zero
import Theorems.Thm_GroundTheory_Automorphic_altSum_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.altSum_zero

set_option autoImplicit false
open Finset
open GroundTheory GroundTheory.Automorphic
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
namespace GroundTheory.Automorphic
theorem _root_.solution : ∀ (k : ℕ) (h : V → W) (y : Fin k → V) (s : V),
    altSum k h y s = ∑ ε : Fin k → Bool, altSign ε • h (s + altPoint y ε)
  | 0, h, y, s => by simp [altSign, altPoint]
  | k + 1, h, y, s => by
    rw [altSum_succ, solution k, ← (Fin.consEquiv fun _ => Bool).sum_comp,
      Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ε _ => ?_
    simp only [Fin.consEquiv_apply, altSign, altPoint, Fin.prod_univ_succ, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ, if_true, Bool.false_eq_true, if_false, one_mul, zero_add,
      Fin.tail]
    rw [smul_sub, neg_mul, one_mul, neg_smul, add_comm (y 0), ← add_assoc]
    abel
end GroundTheory.Automorphic
