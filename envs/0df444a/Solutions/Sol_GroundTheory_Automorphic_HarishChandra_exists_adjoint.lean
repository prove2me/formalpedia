-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.exists_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:08:10.766443+00:00
-- url     : https://prove2.me/submissions/b7d15a30-af1f-4886-8dad-38cf5f5c4449

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Injective
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_add_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_add_right
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_rowOp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_smul_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_smul_right
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_sum_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_sum_right
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_right
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProj0_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rho_zero_e
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
import Theorems.Thm_P2M_GroundTheory_Automorphic_HarishChandra___eq_sum_e_072213ad0100
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.diagExp_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_left
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_right
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcEmb_X
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcProj0_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.pbw_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (u : U n) :
    ∃ u' : U n, ∀ f g : Poly n, fischer (rho 0 u f) g = fischer f (rho 0 u' g) := by
  induction u using U.induction with
  | halg r =>
    refine ⟨algebraMap ℂ (U n) (star r), fun f g => ?_⟩
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, fischer_smul_left, fischer_smul_right]
  | hι X =>
    refine ⟨∑ a : Fin n × Fin n, star (X a.1 a.2) • e (a.2, a.1), fun f g => ?_⟩
    rw [ι_eq_sum_e]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fischer_sum_left,
      fischer_sum_right, fischer_smul_left, fischer_smul_right, star_star]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show e a = e (a.1, a.2) from rfl, rho_zero_e, rho_zero_e, fischer_rowOp]
  | hmul a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨b' * a', fun f g => ?_⟩
    rw [map_mul, Module.End.mul_apply, ha', hb', map_mul, Module.End.mul_apply]
  | hadd a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨a' + b', fun f g => ?_⟩
    rw [map_add, LinearMap.add_apply, fischer_add_left, ha', hb', map_add, LinearMap.add_apply,
      fischer_add_right]
end GroundTheory.Automorphic.HarishChandra
