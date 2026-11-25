-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.capelli_mem_center
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:30.983814+00:00
-- url     : https://prove2.me/submissions/e6c1c2d7-ef21-4b2c-826f-f3e06796a9c9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EMulSubMulCapelliMatrixPow
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_mul_sub_mul_capelliMatrix_pow
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_center_of_commute_e
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
import Theorems.Thm_UpperTheory_Reformulated_B_Qk36_e_mul_sub_mul_capelliMatrix_pow
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
theorem _root_.solution (k : ℕ) : capelli (n := n) k ∈ Subalgebra.center ℂ (U n) := by
  apply mem_center_of_commute_e
  rintro ⟨a, b⟩
  rw [← sub_eq_zero]
  simp only [capelli, Matrix.trace, Matrix.diag]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp_rw [e_mul_sub_mul_capelliMatrix_pow]
  simp [Finset.sum_sub_distrib]
end GroundTheory.Automorphic.HarishChandra
