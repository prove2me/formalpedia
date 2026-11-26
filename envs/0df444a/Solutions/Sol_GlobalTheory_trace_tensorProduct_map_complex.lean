-- Prove2me | solution 1 for GlobalTheory.trace_tensorProduct_map_complex
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:50:06.779952+00:00
-- url     : https://prove2.me/submissions/1fd09d9e-81c4-4fb1-8d78-e924992e2ed4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteLeftOfFiniteTensorProductComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open scoped TensorProduct
theorem _root_.solution {U U' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] (T : U →ₗ[ℂ] U) (T' : U' →ₗ[ℂ] U') :
    LinearMap.trace ℂ (U ⊗[ℂ] U') (TensorProduct.map T T') =
      LinearMap.trace ℂ U T * LinearMap.trace ℂ U' T' := by
  classical
  by_cases hU : Module.Finite ℂ U
  · by_cases hU' : Module.Finite ℂ U'
    · exact LinearMap.trace_tensorProduct' T T'
    · by_cases hz : Subsingleton U
      · have : T = 0 := Subsingleton.elim _ _
        subst this
        rw [TensorProduct.map_zero_left, map_zero, map_zero, zero_mul]
      · rw [not_subsingleton_iff_nontrivial] at hz
        obtain ⟨u, hu⟩ := exists_ne (0 : U)
        have h2 : LinearMap.trace ℂ U' T' = 0 := by
          rw [LinearMap.trace, dif_neg]
          · rfl
          · rintro ⟨s, ⟨b⟩⟩; exact hU' (Module.Finite.of_basis b)
        have h3 : ¬ Module.Finite ℂ (U ⊗[ℂ] U') := by
          intro hf
          obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℂ hu
          apply hU'
          refine Module.Finite.of_surjective ((TensorProduct.lid ℂ U').toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id) ?_
          intro y
          refine ⟨((φ u)⁻¹ • u) ⊗ₜ[ℂ] y, ?_⟩
          simp [hφ]
        rw [h2, mul_zero, LinearMap.trace, dif_neg]
        · rfl
        · rintro ⟨s, ⟨b⟩⟩; exact h3 (Module.Finite.of_basis b)
  · have h1 : LinearMap.trace ℂ U T = 0 := by
      rw [LinearMap.trace, dif_neg]
      · rfl
      · rintro ⟨s, ⟨b⟩⟩; exact hU (Module.Finite.of_basis b)
    by_cases hz : Subsingleton U'
    · have : T' = 0 := Subsingleton.elim _ _
      subst this
      rw [TensorProduct.map_zero_right, map_zero, map_zero, mul_zero]
    · rw [not_subsingleton_iff_nontrivial] at hz
      obtain ⟨v, hv⟩ := exists_ne (0 : U')
      have h3 : ¬ Module.Finite ℂ (U ⊗[ℂ] U') := by
        intro hf
        obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
        apply hU
        refine Module.Finite.of_surjective ((TensorProduct.rid ℂ U).toLinearMap ∘ₗ TensorProduct.map LinearMap.id ψ) ?_
        intro x
        refine ⟨x ⊗ₜ[ℂ] ((ψ v)⁻¹ • v), ?_⟩
        simp [hψ]
      rw [h1, zero_mul, LinearMap.trace, dif_neg]
      · rfl
      · rintro ⟨s, ⟨b⟩⟩; exact h3 (Module.Finite.of_basis b)

