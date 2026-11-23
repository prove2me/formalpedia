-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rowDeriv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:06.436806+00:00
-- url     : https://prove2.me/submissions/d4caf30d-d58f-4c4a-8d91-8d21df38178f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_apply
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
theorem _root_.solution (i j : Fin n) (f : Poly n) : rowDeriv i j f = rowOp i j f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [rowDeriv, rowOp_apply, derivation_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p a hp =>
    rw [Derivation.leibniz, hp, rowOp_apply, rowOp_apply, smul_eq_mul, smul_eq_mul]
    have h1 : rowDeriv i j (X a) = ∑ k, X (i, k) * pderiv (j, k) (X a) := by
      obtain ⟨a1, a2⟩ := a
      simp only [rowDeriv, mkDerivation_X, pderiv_X, Pi.single_apply, Prod.mk.injEq]
      rw [Finset.sum_eq_single a2]
      · by_cases h : a1 = j <;> simp [h]
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    rw [h1]
    simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring
end GroundTheory.Automorphic.HarishChandra
