-- Prove2me | solution 2 for GlobalTheory.trace_tensorProduct_map_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:42:31.229182+00:00
-- url     : https://prove2.me/submissions/be805b64-10a8-4d28-8b7e-2a29ec488adc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteLeftOfFiniteTensorProductComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
namespace GlobalTheory
open scoped TensorProduct in
private lemma trace_eq_zero_of_not_finite' {V : Type} [AddCommGroup V] [Module ℂ V]
    (h : ¬ Module.Finite ℂ V) (f : V →ₗ[ℂ] V) : LinearMap.trace ℂ V f = 0 := by
  have hb : ¬ ∃ s : Finset V, Nonempty (Module.Basis s ℂ V) := by
    rintro ⟨s, ⟨b⟩⟩
    exact h (Module.Finite.of_basis b)
  simp [LinearMap.trace, hb]
open scoped TensorProduct in
private lemma finite_left_of_finite_tensor_of_nontrivial {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial W] [Module.Finite ℂ (V ⊗[ℂ] W)] :
    Module.Finite ℂ V := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
    by_contra! h
    exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).mp h)
  let p : V ⊗[ℂ] W →ₗ[ℂ] V :=
    (TensorProduct.rid ℂ V).toLinearMap ∘ₗ TensorProduct.map LinearMap.id φ
  refine Module.Finite.of_surjective p fun v => ⟨v ⊗ₜ ((φ w)⁻¹ • w), ?_⟩
  simp [p, hφ]
open scoped TensorProduct in
private lemma finite_right_of_finite_tensor_of_nontrivial {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial V] [Module.Finite ℂ (V ⊗[ℂ] W)] :
    Module.Finite ℂ W := by
  have : Module.Finite ℂ (W ⊗[ℂ] V) :=
    Module.Finite.equiv (TensorProduct.comm ℂ V W)
  exact finite_left_of_finite_tensor_of_nontrivial (W := V)
end GlobalTheory
end

set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open scoped TensorProduct
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {U U' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] (T : U →ₗ[ℂ] U) (T' : U' →ₗ[ℂ] U') :
    LinearMap.trace ℂ (U ⊗[ℂ] U') (TensorProduct.map T T') =
      LinearMap.trace ℂ U T * LinearMap.trace ℂ U' T' := by
  by_cases hU : Module.Finite ℂ U
  · by_cases hU' : Module.Finite ℂ U'
    · exact LinearMap.trace_tensorProduct' T T'
    · rw [trace_eq_zero_of_not_finite' hU' T', mul_zero]
      by_cases hUU : Module.Finite ℂ (U ⊗[ℂ] U')
      · rcases subsingleton_or_nontrivial U with hs | hs
        · rw [Subsingleton.elim T 0, TensorProduct.map_zero_left, map_zero]
        · exact absurd (finite_right_of_finite_tensor_of_nontrivial (V := U)) hU'
      · exact trace_eq_zero_of_not_finite' hUU _
  · rw [trace_eq_zero_of_not_finite' hU T, zero_mul]
    by_cases hUU : Module.Finite ℂ (U ⊗[ℂ] U')
    · rcases subsingleton_or_nontrivial U' with hs | hs
      · rw [Subsingleton.elim T' 0, TensorProduct.map_zero_right, map_zero]
      · exact absurd (finite_left_of_finite_tensor_of_nontrivial (W := U')) hU
    · exact trace_eq_zero_of_not_finite' hUU _
end _root_.GlobalTheory
end GlobalTheory
