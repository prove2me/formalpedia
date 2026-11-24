-- Prove2me | solution 1 for GlobalTheory.quotient_base_change_invariant_derivations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:30:36.277605+00:00
-- url     : https://prove2.me/submissions/5fca8c3e-c8b3-4773-8def-c8cf0093d6e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInvariantDerivationOfCounitalComul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInvariantDerivationsQuotientBialgebra
import Theorems.Thm_GlobalTheory_invariant_derivation_exists


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
    ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] (I : Ideal O) (d : ℕ) (l : Fin d → (A →ₗ[O] O ⧸ I)), (∀ i a b, l i (a * b) = Coalgebra.counit (R := O) a • l i b + Coalgebra.counit (R := O) b • l i a) → ∃ D : Fin d → Derivation (O ⧸ I) ((O ⧸ I) ⊗[O] A) ((O ⧸ I) ⊗[O] A), ∀ i a, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] A) (D i (1 ⊗ₜ a)) = l i a := by
  intro O A _ _ _ I d l hl
  set S := O ⧸ I
  set B := S ⊗[O] A
  let ε := Bialgebra.counitAlgHom S B
  let Δ := Bialgebra.comulAlgHom S B
  have hεt : ∀ (s : S) (a : A), ε (s ⊗ₜ a) = Coalgebra.counit (R := O) a • s := by
    intro s a
    show Coalgebra.counit (R := S) (s ⊗ₜ[O] a) = _
    rw [TensorProduct.counit_tmul]
    rfl
  have hε : (∀ b : B, TensorProduct.lid S B (LinearMap.rTensor B ε.toLinearMap (Δ b)) = b) ∧
      (∀ b : B, TensorProduct.rid S B (LinearMap.lTensor B ε.toLinearMap (Δ b)) = b) := by
    constructor
    · intro b
      have := Coalgebra.rTensor_counit_comul (R := S) b
      show TensorProduct.lid S B (LinearMap.rTensor B Coalgebra.counit (Coalgebra.comul b)) = b
      rw [this]; simp
    · intro b
      have := Coalgebra.lTensor_counit_comul (R := S) b
      show TensorProduct.rid S B (LinearMap.lTensor B Coalgebra.counit (Coalgebra.comul b)) = b
      rw [this]; simp
  have key : ∀ i, ∃ D : Derivation S B B, ∀ b, ε (D b) = LinearMap.liftBaseChange S (l i) b := by
    intro i
    refine invariant_derivation_exists S B ε Δ hε (LinearMap.liftBaseChange S (l i)) ?_
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul t c =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hεt, hεt]
        rw [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
          LinearMap.liftBaseChange_tmul, hl]
        simp only [smul_eq_mul, smul_add, Algebra.smul_def]
        ring
      | add y₁ y₂ ih₁ ih₂ =>
        rw [mul_add, map_add, ih₁, ih₂, map_add, map_add]
        ring
    | add x₁ x₂ ih₁ ih₂ =>
      rw [add_mul, map_add, ih₁, ih₂, map_add, map_add]
      ring
  choose D hD using key
  refine ⟨D, fun i a => ?_⟩
  rw [hD, LinearMap.liftBaseChange_tmul, one_smul]
end GlobalTheory
