-- Prove2me | solution 1 for GlobalTheory.invariant_derivation_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:43.500219+00:00
-- url     : https://prove2.me/submissions/b47975bc-e755-48d3-b9fc-2232f3c165f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInvariantDerivationOfCounitalComul

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
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∀ l : A →ₗ[k] k, (∀ a b, l (a * b) = ε a * l b + ε b * l a) → ∃ D : Derivation k A A, ∀ a, ε (D a) = l a := by
  intro k A _ _ _ ε Δ hε l hl
  obtain ⟨h1, h2⟩ := hε
  let F : A ⊗[k] A →ₗ[k] A := (TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A l
  let E : A ⊗[k] A →ₗ[k] A :=
    (TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A ε.toLinearMap
  have hF : ∀ a b : A, F (a ⊗ₜ b) = l b • a := fun a b => by simp [F]
  have hE : ∀ a b : A, E (a ⊗ₜ b) = ε b • a := fun a b => by simp [E]
  have key : ∀ x y : A ⊗[k] A, F (x * y) = E x * F y + E y * F x := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c d =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hF, hF, hF, hE, hE, hl]
        simp only [Algebra.smul_def, map_add, map_mul]
        ring
      | add y₁ y₂ ih₁ ih₂ =>
        rw [mul_add, map_add, ih₁, ih₂, map_add, map_add]
        ring
    | add x₁ x₂ ih₁ ih₂ =>
      rw [add_mul, map_add, ih₁, ih₂, map_add, map_add]
      ring
  have hEΔ : ∀ a, E (Δ a) = a := fun a => h2 a
  have hεF : ∀ x : A ⊗[k] A,
      ε (F x) = l (TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hF]
      simp [mul_comm]
    | add x₁ x₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, map_add, map_add, map_add]
  refine ⟨Derivation.mk' (F ∘ₗ Δ.toLinearMap) (fun a b => ?_), fun a => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      key, hEΔ, smul_eq_mul]
  · show ε (F (Δ a)) = l a
    rw [hεF, h1]
end GlobalTheory
