-- Prove2me | solution 1 for GlobalTheory.annihilator_diagonal_form_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:50.182088+00:00
-- url     : https://prove2.me/submissions/f63039af-befd-45cc-a600-a7ee07b523dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped TensorProduct
namespace GlobalTheory
theorem _root_.solution {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    {d : ℕ} (b : Fin d → B) (M : Matrix (Fin d) (Fin d) R)
    (h : ∀ x : B, (∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j)) *
      (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0)
    (f : B →ₗ[R] R) (y : B) :
    ∑ i, ∑ j, (M i j * f (b i * y)) • b j = ∑ i, ∑ j, (M i j * f (b i)) • (b j * y) := by
  classical
  let L : TensorProduct R B B →ₗ[R] B :=
    TensorProduct.lift ((LinearMap.lsmul R B).compl₁₂ f LinearMap.id)
  have hL : ∀ a c : B, L (TensorProduct.tmul R a c) = f a • c := fun a c => by simp [L]
  have e := h y
  rw [mul_sub, sub_eq_zero] at e
  simp only [Finset.sum_mul, smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one] at e
  have e2 := congrArg L e
  simp only [map_sum, map_smul, hL, smul_smul] at e2
  exact e2
end GlobalTheory
