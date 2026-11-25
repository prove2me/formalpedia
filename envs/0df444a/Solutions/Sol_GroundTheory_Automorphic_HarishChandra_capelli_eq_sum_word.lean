-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.capelli_eq_sum_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:29.241102+00:00
-- url     : https://prove2.me/submissions/1ded1be1-a6b5-4402-ad51-a6e2ce62cca3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EMulSubMulCapelliMatrixPow
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_capelliMatrix_pow_succ_apply
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
theorem _root_.solution (k : ℕ) :
    capelli (n := n) (k + 1) = ∑ i : Fin (k + 1) → Fin n,
      word (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))) := by
  rw [capelli, Matrix.trace]
  simp only [Matrix.diag, capelliMatrix_pow_succ_apply]
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.consEquiv_apply]
  congr 2
  funext t
  congr 1
  induction t using Fin.lastCases with
  | last => simp [finRotate_apply]
  | cast s => simp [finRotate_apply, Fin.coeSucc_eq_succ]
end GroundTheory.Automorphic.HarishChandra
