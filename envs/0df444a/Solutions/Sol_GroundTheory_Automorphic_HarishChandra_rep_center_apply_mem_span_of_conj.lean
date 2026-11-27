-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rep_center_apply_mem_span_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:35.21137+00:00
-- url     : https://prove2.me/submissions/0b101a57-df64-4962-9e09-93e9410bf39d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Consequences
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rep_center_apply_of_highestWeight
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_conjU_conjU_inv
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_conjU_mem_center
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProj0_apply
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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : U n →ₐ[ℂ] Module.End ℂ V) (g : (gl n)ˣ) {v : V} (lam : Fin n → ℂ)
    (hup : ∀ a, IsUpper a → φ (conjU g (e a)) v = 0)
    (hH : ∀ k, φ (conjU g (e (k, k))) v = lam k • v) {z : U n} (hz : z ∈ Subalgebra.center ℂ (U n)) :
    ∃ c : ℂ, φ z v = c • v := by
  have hz' : conjU g⁻¹ z ∈ Subalgebra.center ℂ (U n) := conjU_mem_center hz
  refine ⟨eval (lam + rhoVec n) (harishChandraHom ⟨_, hz'⟩), ?_⟩
  have := rep_center_apply_of_highestWeight (φ.comp (conjU g)) lam hup hH ⟨_, hz'⟩
  simpa [conjU_conjU_inv] using this
end GroundTheory.Automorphic.HarishChandra
