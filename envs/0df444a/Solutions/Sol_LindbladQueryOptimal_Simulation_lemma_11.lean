-- Prove2me | solution 1 for LindbladQueryOptimal.Simulation.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T20:50:10.128411+00:00
-- url     : https://prove2.me/submissions/c92e084f-465d-4584-9fc0-bc6e15753052

import Definitions.Def_LindbladQueryOptimal_Simulation_Local

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped ComplexOrder in
theorem aux_isUnit {a : Type} [Fintype a] (L : Op a) : IsUnit (1 + Lᴴ * L) := by
  have h : (1 + Lᴴ * L).PosDef := by
    have := Matrix.PosDef.one (n := a) (R := ℂ)
    exact this.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self L)
  exact h.isUnit

theorem aux_gen (a : Type) [Fintype a] (L : Op a) :
    cayley (dilation L) * (inj0 : Matrix (Sum a a) a ℂ) =
      Matrix.fromRows (realCayley (Lᴴ * L))
        ((-2 * Complex.I) • (L * (1 + Lᴴ * L)⁻¹)) := by
  have hU := aux_isUnit L
  set P := (1 + Lᴴ * L)⁻¹ with hP
  have hPl : P * (1 + Lᴴ * L) = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hPr : (1 + Lᴴ * L) * P = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  set M : Op (Sum a a) := 1 + Complex.I • dilation L with hM
  have hMb : M = Matrix.fromBlocks 1 (Complex.I • Lᴴ) (Complex.I • L) 1 := by
    rw [hM, dilation, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  have hdet : IsUnit M.det := by
    letI hI : Invertible (1 : Op a) := invertibleOne
    rw [hMb, Matrix.det_fromBlocks₂₂]
    simp only [Matrix.det_one, one_mul]
    have : (1 : Op a) - (Complex.I • Lᴴ) * 1 * (Complex.I • L) = 1 + Lᴴ * L := by
      simp [smul_smul]
    rw [invOf_one, this]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hQ : M * (Matrix.fromRows P ((-Complex.I) • (L * P))) = (inj0 : Matrix (Sum a a) a ℂ) := by
    have h0 : (inj0 : Matrix (Sum a a) a ℂ) = Matrix.fromRows 1 0 := by
      ext x y; rcases x with x | x <;> simp [inj0, Matrix.one_apply, eq_comm]
    rw [hMb, h0, Matrix.fromBlocks_mul_fromRows]
    congr 1
    · have h1 : P + Lᴴ * (L * P) = 1 := by
        rw [← Matrix.mul_assoc]
        have := hPr
        rwa [add_mul, Matrix.one_mul] at this
      rw [Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      simpa using h1
    · simp [Matrix.smul_mul, Matrix.one_mul]
  have hinv : M⁻¹ * (inj0 : Matrix (Sum a a) a ℂ) = Matrix.fromRows P ((-Complex.I) • (L * P)) := by
    rw [← hQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  unfold cayley realCayley
  have hD : (1 - Complex.I • dilation L : Op (Sum a a)) =
      Matrix.fromBlocks 1 ((-Complex.I) • Lᴴ) ((-Complex.I) • L) 1 := by
    ext x y; rcases x with x | x <;> rcases y with y | y <;> simp [dilation, Matrix.one_apply]
  rw [Matrix.mul_assoc, hinv, hD, Matrix.fromBlocks_mul_fromRows]
  congr 1
  · have e : Lᴴ * (L * P) = Lᴴ * L * P := (Matrix.mul_assoc _ _ _).symm
    rw [Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, e, smul_smul, sub_mul, Matrix.one_mul]
    have : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg, Complex.I_mul_I]
    rw [this, neg_one_smul, sub_eq_add_neg]
  · rw [Matrix.smul_mul, Matrix.one_mul, ← add_smul]
    congr 1
    ring

theorem lemma_11 (n : ℕ) (L : Op (Bits n)) :
    cayley (dilation L) * (inj0 : Matrix (Sum (Bits n) (Bits n)) (Bits n) ℂ) =
      Matrix.fromRows (realCayley (Lᴴ * L))
        ((-2 * Complex.I) • (L * (1 + Lᴴ * L)⁻¹)) := by convert aux_gen (Bits n) L

end LindbladQueryOptimal.Simulation

open LindbladQueryOptimal.Simulation in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution (n : ℕ) (L : Op (Bits n)) :
    cayley (dilation L) * (inj0 : Matrix (Sum (Bits n) (Bits n)) (Bits n) ℂ) =
      Matrix.fromRows (realCayley (Lᴴ * L))
        ((-2 * Complex.I) • (L * (1 + Lᴴ * L)⁻¹)) := lemma_11 n L
