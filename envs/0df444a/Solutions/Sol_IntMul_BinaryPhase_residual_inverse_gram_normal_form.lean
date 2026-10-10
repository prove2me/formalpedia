-- Prove2me | solution 1 for IntMul.BinaryPhase.residual_inverse_gram_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T17:44:56.23598+00:00
-- url     : https://prove2.me/submissions/0e57dd77-d4c7-4d56-8162-3ffe2a378e9f

import Definitions.Def_IntMul_BinaryQuadraticPhase
import Theorems.Thm_IntMul_BinaryPhase_residual_normal_form
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
open scoped BigOperators Matrix
open IntMul.BinaryPhase

namespace IntMul.BinaryPhase

open scoped BigOperators

theorem twice_add (a b : ZMod 2) : twice (a + b) = twice a + twice b := by
  fin_cases a <;> fin_cases b <;> rfl

theorem twice_zero : twice 0 = 0 := rfl

theorem lift_bit_polarization (a b : ZMod 2) :
    liftBit (a + b) = liftBit a + liftBit b + twice (a * b) := by
  fin_cases a <;> fin_cases b <;> rfl

theorem twice_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    twice (∑ i ∈ s, f i) = ∑ i ∈ s, twice (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [twice_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, twice_add, ih]

/-- Hamming weight modulo four is a quadratic refinement of the binary dot
product. This is the polar identity required by the actual residual construction. -/
theorem hamming_weight_polarization {ι : Type*} [Fintype ι]
    (x y : ι → ZMod 2) :
    quadraticWeight (x + y) = quadraticWeight x + quadraticWeight y +
      twice (∑ i, x i * y i) := by
  classical
  simp only [quadraticWeight, Pi.add_apply, lift_bit_polarization]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, twice_sum]

theorem hamming_weight_zero {ι : Type*} [Fintype ι] :
    quadraticWeight (0 : ι → ZMod 2) = 0 := by
  simp [quadraticWeight, liftBit]

end IntMul.BinaryPhase


namespace IntMul.BinaryPhase

open scoped BigOperators Matrix

variable {m r : Type*} [Fintype m] [Fintype r] [DecidableEq r]

/-- The Gram inverse is the Gram matrix of the dual-coordinate embedding. -/
theorem dual_embedding_gram (A : Matrix m r (ZMod 2))
    (hG : IsUnit (Aᵀ * A).det) :
    (A * (Aᵀ * A)⁻¹)ᵀ * (A * (Aᵀ * A)⁻¹) = (Aᵀ * A)⁻¹ := by
  have hsym : (Aᵀ * A)ᵀ = Aᵀ * A := by simp
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hsym]
  calc
    (Aᵀ * A)⁻¹ * Aᵀ * (A * (Aᵀ * A)⁻¹) =
        ((Aᵀ * A)⁻¹ * (Aᵀ * A)) * (Aᵀ * A)⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = (Aᵀ * A)⁻¹ := by rw [Matrix.nonsing_inv_mul (Aᵀ * A) hG, Matrix.one_mul]

/-- The actual Hamming-weight phase has the claimed inverse-Gram polarization. -/
theorem inverse_gram_weight_polarization (A : Matrix m r (ZMod 2))
    (hG : IsUnit (Aᵀ * A).det) (z w : r → ZMod 2) :
    quadraticWeight (A *ᵥ ((Aᵀ * A)⁻¹ *ᵥ (z + w))) =
      quadraticWeight (A *ᵥ ((Aᵀ * A)⁻¹ *ᵥ z)) +
        quadraticWeight (A *ᵥ ((Aᵀ * A)⁻¹ *ᵥ w)) +
          twice (z ⬝ᵥ ((Aᵀ * A)⁻¹ *ᵥ w)) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_add, hamming_weight_polarization]
  congr 1
  congr 1
  change (A *ᵥ ((Aᵀ * A)⁻¹ *ᵥ z)) ⬝ᵥ
      (A *ᵥ ((Aᵀ * A)⁻¹ *ᵥ w)) = z ⬝ᵥ ((Aᵀ * A)⁻¹ *ᵥ w)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  let D := A * (Aᵀ * A)⁻¹
  change (D *ᵥ z) ⬝ᵥ (D *ᵥ w) = _
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec]
  dsimp only [D]
  rw [dual_embedding_gram A hG, dotProduct_comm]

/-- Nonsingularity of the original Gram matrix supplies nondegeneracy of the
inverse-Gram polar form. -/
theorem inverse_gram_nondegenerate (A : Matrix m r (ZMod 2))
    (hG : IsUnit (Aᵀ * A).det) :
    ((Aᵀ * A)⁻¹).toBilin'.Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  exact (Matrix.isUnit_nonsing_inv_det (Aᵀ * A) hG).ne_zero

/-- The formula in the construction notes, with the actual inverse-Gram
Hamming-weight phase and the ordinary input Fourier character. -/
theorem residual_inverse_gram_normal_form (A : Matrix m r (ZMod 2))
    (hG : IsUnit (Aᵀ * A).det) :
    ∃ (eL eR : (r → ZMod 2) ≃ₗ[ZMod 2] (r → ZMod 2))
      (ε : ℂ) (dL dR : (r → ZMod 2) → ℂ),
      ε ^ 4 = 1 ∧ (∀ x, dL x ^ 4 = 1) ∧ (∀ y, dR y ^ 4 = 1) ∧
      ∀ x y,
        (∑ z : r → ZMod 2,
          (phase (quadraticWeight (A *ᵥ ((Aᵀ * A)⁻¹ *ᵥ z))) : ℂ) *
            sign (z ⬝ᵥ (x + y))) / (2 : ℂ) ^ Fintype.card r =
        ε * dL x * tensorKernel (eL x) (eR y) * dR y := by
  classical
  let G := Aᵀ * A
  let B : LinearMap.BilinForm (ZMod 2) (r → ZMod 2) := G⁻¹.toBilin'
  let q : (r → ZMod 2) → ZMod 4 := fun z => quadraticWeight (A *ᵥ (G⁻¹ *ᵥ z))
  have hB : B.Nondegenerate := inverse_gram_nondegenerate A hG
  have hq0 : q 0 = 0 := by simp [q, hamming_weight_zero]
  have hpolar : ∀ z w, q (z + w) = q z + q w + twice (B z w) := by
    intro z w
    dsimp only [q, B, G]
    rw [Matrix.toBilin'_apply']
    exact inverse_gram_weight_polarization A hG z w
  obtain ⟨eL, eR, ε, dL, dR, hε, hdL, hdR, hK⟩ :=
    residual_normal_form B hB q hq0 hpolar (Pi.basisFun (ZMod 2) r)
  have hinj : Function.Injective G.mulVecLin :=
    Matrix.mulVec_injective_of_det_ne_zero hG.ne_zero
  let g := LinearEquiv.ofInjectiveEndo G.mulVecLin hinj
  refine ⟨g.trans eL, g.trans eR, ε, fun x => dL (g x), fun y => dR (g y),
    hε, fun x => hdL (g x), fun y => hdR (g y), ?_⟩
  intro x y
  change (∑ z : r → ZMod 2, (phase (q z) : ℂ) * sign (z ⬝ᵥ (x + y))) /
      (2 : ℂ) ^ Fintype.card r =
    ε * dL (g x) * tensorKernel (eL (g x)) (eR (g y)) * dR (g y)
  rw [← hK (g x) (g y)]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  congr 1
  dsimp only [B]
  rw [Matrix.toBilin'_apply']
  change z ⬝ᵥ (x + y) = z ⬝ᵥ (G⁻¹ *ᵥ (G *ᵥ x + G *ᵥ y))
  rw [← Matrix.mulVec_add, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul G hG, Matrix.one_mulVec]

end IntMul.BinaryPhase


theorem solution
    {m r : Type*} [Fintype m] [Fintype r] [DecidableEq r] (A : Matrix m r (ZMod 2))
    (hG : IsUnit (Aᵀ * A).det) :
    ∃ (eL eR : (r → ZMod 2) ≃ₗ[ZMod 2] (r → ZMod 2))
      (ε : ℂ) (dL dR : (r → ZMod 2) → ℂ),
      ε ^ 4 = 1 ∧ (∀ x, dL x ^ 4 = 1) ∧ (∀ y, dR y ^ 4 = 1) ∧
      ∀ x y,
        (∑ z : r → ZMod 2,
          (phase (quadraticWeight (A *ᵥ ((Aᵀ * A)⁻¹ *ᵥ z))) : ℂ) *
            sign (z ⬝ᵥ (x + y))) / (2 : ℂ) ^ Fintype.card r =
        ε * dL x * tensorKernel (eL x) (eR y) * dR y := by
  exact IntMul.BinaryPhase.residual_inverse_gram_normal_form A hG

#print axioms solution
