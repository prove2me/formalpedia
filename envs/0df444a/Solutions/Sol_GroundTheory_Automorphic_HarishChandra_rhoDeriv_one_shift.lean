-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rhoDeriv_one_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:29.599024+00:00
-- url     : https://prove2.me/submissions/6a36b26c-c9a2-4eaa-ba2b-3f27c95b1a8b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_shift_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_shift_C
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
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (M : gl n) (f : Poly n) :
    rhoDeriv 1 M (shift f) = shift (rhoDeriv 0 M f) := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    have : shift (C r : Poly n) = C r := (shift : Poly n ≃ₐ[ℂ] Poly n).commutes r
    rw [this, derivation_C, derivation_C, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p a hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, map_add, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, map_mul, map_mul]
    congr 2
    rw [shift_X, Derivation.map_add, derivation_C, add_zero, rhoDeriv_X, rhoDeriv_X, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [shift_X, shift_C, Matrix.one_apply]
end GroundTheory.Automorphic.HarishChandra
