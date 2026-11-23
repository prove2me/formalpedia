-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rhoDeriv_E_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:05.964142+00:00
-- url     : https://prove2.me/submissions/bf625605-09c7-4427-a2b9-f0e9044b0edd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
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
theorem _root_.solution (c : Matrix (Fin n) (Fin n) ℂ) (i j a b : Fin n) :
    rhoDeriv c (E (i, j)) (X (a, b)) = if a = j then X (i, b) + C (c i b) else 0 := by
  rw [rhoDeriv_X, Finset.sum_eq_single i]
  · by_cases h : a = j
    · subst h; simp [E]
    · simp [E, Matrix.single_apply, Ne.symm h, h]
  · intro k _ hk
    simp [E, Matrix.single_apply, Ne.symm hk]
  · simp
end GroundTheory.Automorphic.HarishChandra
