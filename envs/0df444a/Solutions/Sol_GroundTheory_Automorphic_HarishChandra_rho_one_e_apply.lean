-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rho_one_e_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:40.730266+00:00
-- url     : https://prove2.me/submissions/207df00a-6c47-4e3a-8a31-f7a98ff71b5a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rho_e_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rhoDeriv_E_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowDeriv_apply
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
theorem _root_.solution (i j : Fin n) (f : Poly n) :
    rho 1 (e (i, j)) f = pderiv (j, i) f + rowOp i j f := by
  rw [rho_e_apply, ← rowDeriv_apply, ← Derivation.add_apply]
  congr 1
  apply derivation_ext
  rintro ⟨a, b⟩
  rw [rhoDeriv_E_X, Derivation.add_apply, pderiv_X]
  simp only [rowDeriv, mkDerivation_X, Matrix.one_apply, Pi.single_apply, Prod.mk.injEq]
  by_cases h : a = j
  · subst h
    by_cases h' : b = i
    · subst h'; simp [add_comm]
    · simp [h'] <;> exact fun hh => h' hh.symm
  · simp [h]
end GroundTheory.Automorphic.HarishChandra
