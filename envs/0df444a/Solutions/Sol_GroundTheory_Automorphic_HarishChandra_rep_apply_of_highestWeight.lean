-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rep_apply_of_highestWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:14.374559+00:00
-- url     : https://prove2.me/submissions/0ccb5d69-2246-43d2-ac6a-566194d55f58

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProj0_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
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
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.diagExp_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcEmb_X
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.pbw_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcProj0_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : U n →ₐ[ℂ] Module.End ℂ V) {v : V} (lam : Fin n → ℂ)
    (hup : ∀ a, IsUpper a → φ (e a) v = 0) (hH : ∀ k, φ (e (k, k)) v = lam k • v)
    {z : U n} (hz : ∀ k, e (k, k) * z = z * e (k, k)) :
    φ z v = eval lam (hcProjLin z) • v := by
  have hN : ∀ x ∈ nPlusU n, φ x v = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, a, ha, rfl⟩ := hx
      rw [map_mul, Module.End.mul_apply, hup a ha, map_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul r x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  have hC : ∀ p, φ (hcEmb p) v = eval lam p • v := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp [AlgHom.commutes, Module.algebraMap_end_apply]
    | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, hp, hq, map_add, add_smul]
    | mul_X p i hp =>
      rw [map_mul, map_mul, Module.End.mul_apply, hcEmb_X, hH, map_smul, hp, smul_smul,
        eval_mul, eval_X, mul_comm]
  have := sub_hcEmb_mem_nPlusU hz
  have h := hN _ this
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h
  rw [h, hC]
end GroundTheory.Automorphic.HarishChandra
