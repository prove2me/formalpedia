-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.exists_rankOne_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:02:52.295419+00:00
-- url     : https://prove2.me/submissions/157a52bb-e0bb-4d68-853f-55cdb2093f65

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Existence
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_adjoin_eq_top
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_of_mem_adjoin_restrictSet
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_simple_stable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Filter Function Module Set PiTensorProduct
open scoped TensorProduct RestrictedProduct
variable {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (T : Set (End ℂ M)) [Nontrivial M] :
    ∃ (N : Submodule ℂ M) (hN : IsStable T N), N ≠ ⊥ ∧ IsSimpleUnder (restrictSet T N hN) ∧
      ∃ p ∈ Algebra.adjoin ℂ T, ∃ n₀ ∈ N, n₀ ≠ 0 ∧ p n₀ = n₀ ∧ ∀ x ∈ N, ∃ c : ℂ, p x = c • n₀ := by
  obtain ⟨N, hNs, hN0, hsimple⟩ := exists_simple_stable T
  have := hsimple.1
  obtain ⟨n, hn⟩ := exists_ne (0 : N)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ N, f n = 1 := by
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ N, f n ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hn ((Module.forall_dual_apply_eq_zero_iff ℂ n).1 hcon)
    exact ⟨(f n)⁻¹ • f, by simp [hf]⟩
  let b : End ℂ N := f.smulRight n
  have hb : b ∈ Algebra.adjoin ℂ (restrictSet T N hNs) := by
    rw [adjoin_eq_top hsimple]; trivial
  obtain ⟨p, hp, hpb⟩ := exists_of_mem_adjoin_restrictSet hNs hb
  refine ⟨N, hNs, hN0, hsimple, p, hp, n, n.2, fun h => hn (Subtype.ext h), ?_, ?_⟩
  · rw [← hpb n]
    simp [b, hf]
  · intro x hx
    refine ⟨f ⟨x, hx⟩, ?_⟩
    rw [← hpb ⟨x, hx⟩]
    simp [b]
end GroundTheory.Automorphic.RestrictedTensor
