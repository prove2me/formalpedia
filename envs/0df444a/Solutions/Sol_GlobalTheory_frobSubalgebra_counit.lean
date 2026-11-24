-- Prove2me | solution 1 for GlobalTheory.frobSubalgebra_counit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:59:11.266813+00:00
-- url     : https://prove2.me/submissions/7b07492e-9b11-4f8f-a573-28e1ea95ebed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusSubalgebraCounitalComul

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
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ B : Subalgebra k A, (∀ a, a ∈ B ↔ ∃ c : A, c ^ p = a) ∧ ∃ Δ' : B →ₐ[k] B ⊗[k] B, ((∀ a : B, TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a) ∧ (∀ a : B, TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a)) := by
  intro p _ k A _ _ _ _ _ ε Δ ⟨hl, hr⟩
  have injA : Function.Injective (algebraMap k A) := fun x y h => by
    simpa using congrArg ε h
  haveI : CharP A p := charP_of_injective_algebraMap injA p
  let εε : A ⊗[k] A →ₐ[k] k := Algebra.TensorProduct.lift ε ε (fun _ _ => Commute.all _ _)
  have injAA : Function.Injective (algebraMap k (A ⊗[k] A)) := fun x y h => by
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using congrArg εε h
  haveI : CharP (A ⊗[k] A) p := charP_of_injective_algebraMap injAA p
  let B : Subalgebra k A :=
    { carrier := {a | ∃ c : A, c ^ p = a}
      mul_mem' := by rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c * d, mul_pow c d p⟩
      add_mem' := by rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c + d, add_pow_char c d p⟩
      algebraMap_mem' := by
        intro r
        obtain ⟨s, hs⟩ := surjective_frobenius k p r
        exact ⟨algebraMap k A s, by rw [← map_pow, ← hs, frobenius_def]⟩ }
  refine ⟨B, fun a => Iff.rfl, ?_⟩
  let j : B ⊗[k] B →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.map B.val B.val
  have hj : Function.Injective j :=
    TensorProduct.map_injective_of_flat_flat B.val.toLinearMap B.val.toLinearMap
      Subtype.val_injective Subtype.val_injective
  have hpow : ∀ t : A ⊗[k] A, t ^ p ∈ j.range := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [zero_pow (Fact.out : p.Prime).ne_zero]⟩
    | tmul a b =>
      exact ⟨(⟨a ^ p, a, rfl⟩ : B) ⊗ₜ (⟨b ^ p, b, rfl⟩ : B), by
        simp [j, Algebra.TensorProduct.tmul_pow]⟩
    | add x y hx hy => rw [add_pow_char]; exact add_mem hx hy
  have hΔ : ∀ b : B, Δ (B.val b) ∈ j.range := by
    rintro ⟨_, c, rfl⟩
    simpa [map_pow] using hpow (Δ c)
  let e := AlgEquiv.ofInjective j hj
  let Δ' : B →ₐ[k] B ⊗[k] B := e.symm.toAlgHom.comp ((Δ.comp B.val).codRestrict j.range hΔ)
  have hjΔ : ∀ b : B, j (Δ' b) = Δ (B.val b) := by
    intro b
    have h1 := e.apply_symm_apply ⟨Δ (B.val b), hΔ b⟩
    exact congrArg Subtype.val h1
  have kl : ∀ x : B ⊗[k] B, ((TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap x) : B) : A)
      = TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (j x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [j]
    | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  have kr : ∀ x : B ⊗[k] B, ((TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap x) : B) : A)
      = TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (j x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [j]
    | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  refine ⟨Δ', fun b => ?_, fun b => ?_⟩
  · apply Subtype.ext
    rw [kl, hjΔ]; exact hl _
  · apply Subtype.ext
    rw [kr, hjΔ]; exact hr _
end GlobalTheory
