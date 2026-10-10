-- Prove2me | solution 1 for OAI.DimensionTen.compositeChoi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-10T11:13:18.919224+00:00
-- url     : https://prove2.me/submissions/dfe74999-40d2-4fb5-aeef-657955fd071f

import Mathlib
import Definitions.Def_DimensionTenPair

open Matrix Complex
open scoped Matrix ComplexOrder Kronecker
open OAI.DimensionTen

namespace DimTenNZ

lemma sqrt2_mul_self : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- `S E₀₀ S* = E_{(0,0),(0,0)}`. -/
lemma sym_single :
    symmetricIsometry * Matrix.single (0 : Fin 10) (0 : Fin 10) (1 : ℂ) * symmetricIsometryᴴ =
      Matrix.single ((0 : Fin 4), (0 : Fin 4)) ((0 : Fin 4), (0 : Fin 4)) (1 : ℂ) := by
  ext p q
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, symmetricIsometry,
    symmetricPairs, Fin.sum_univ_succ, Prod.ext_iff]
  by_cases h1 : p.1 = 0 ∧ p.2 = 0 <;> by_cases h2 : q.1 = 0 ∧ q.2 = 0 <;> simp [h1, h2, eq_comm]

/-- The pencil map on `E₀₀` is `36 · I₄`. -/
lemma pencil_single : pencilMap (Matrix.single (0 : Fin 4) (0 : Fin 4) (1 : ℂ)) = (36 : ℂ) • 1 := by
  have h : pencilMap (Matrix.single (0 : Fin 4) (0 : Fin 4) (1 : ℂ)) = (blocks 0)ᵀ * blocks 0 := by
    unfold pencilMap
    simp [Matrix.single_apply, Fin.sum_univ_four]
  rw [h]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blocks, blocksZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      Matrix.map, Matrix.of_apply] <;> norm_num

/-- The tensor map on `E_{(0,0),(0,0)}` is the single Kronecker term. -/
lemma tensor_single :
    tensorMap pencilMap pencilMap
      (Matrix.single ((0 : Fin 4), (0 : Fin 4)) ((0 : Fin 4), (0 : Fin 4)) (1 : ℂ)) =
      Matrix.kronecker (pencilMap (Matrix.single (0 : Fin 4) (0 : Fin 4) (1 : ℂ)))
        (pencilMap (Matrix.single (0 : Fin 4) (0 : Fin 4) (1 : ℂ))) := by
  have hz : ∀ i j : Fin 4, ¬ (i = 0 ∧ j = 0) →
      (fun a b : Fin 4 => Matrix.single ((0 : Fin 4), (0 : Fin 4)) ((0 : Fin 4), (0 : Fin 4))
        (1 : ℂ) (a, i) (b, j)) = (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
    intro i j hij
    ext a b
    simp only [Matrix.single_apply, Prod.ext_iff, Matrix.zero_apply]
    split_ifs with h
    · exact absurd ⟨h.1.2.symm, h.2.2.symm⟩ hij
    · rfl
  have hp0 : pencilMap 0 = 0 := by
    unfold pencilMap; simp
  unfold tensorMap
  rw [Finset.sum_eq_single (0 : Fin 4)]
  · rw [Finset.sum_eq_single (0 : Fin 4)]
    · congr 1
      try (ext a b; simp [Matrix.single_apply, Prod.ext_iff])
    · intro j _ hj
      have h := hz 0 j (fun h => hj h.2)
      simp only [h, hp0, Matrix.kronecker, Matrix.zero_kronecker]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    have h := hz i j (fun h => hi h.1)
    simp only [h, hp0, Matrix.kronecker, Matrix.zero_kronecker]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The exterior isometry has orthonormal columns. -/
lemma W_isometry : exteriorIsometryᴴ * exteriorIsometry = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [exteriorIsometry, exteriorPairs, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply, Prod.ext_iff,
      div_mul_div_comm, sqrt2_mul_self] <;> norm_num [sqrt2_mul_self]

/-- The Hodge complement is unitary. -/
lemma H_unitary : hodgeComplement * hodgeComplementᴴ = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  fin_cases a <;> fin_cases b <;>
    simp [hodgeComplement, Fin.sum_univ_succ, Matrix.one_apply]

/-- The coordinate inclusion is an isometry. -/
lemma J_isometry : firstSixᴴ * firstSix = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [firstSix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
      Matrix.one_apply]

end DimTenNZ

open DimTenNZ in
theorem solution : choi (phiTwo ∘ phiOne) ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h ((0 : Fin 10), (0 : Fin 10))) ((0 : Fin 10), (0 : Fin 10))
  change phiTwo (phiOne (Matrix.single (0 : Fin 10) (0 : Fin 10) (1 : ℂ))) 0 0 = 0 at h00
  have hext : exteriorMap (Matrix.single (0 : Fin 10) (0 : Fin 10) (1 : ℂ)) = (1296 : ℂ) • 1 := by
    unfold exteriorMap
    rw [sym_single, tensor_single, pencil_single]
    simp only [Matrix.kronecker]
    rw [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, W_isometry]
    norm_num
  have ht : (Matrix.single (0 : Fin 10) (0 : Fin 10) (1 : ℂ))ᵀ =
      Matrix.single (0 : Fin 10) (0 : Fin 10) (1 : ℂ) := by
    ext i j; simp [Matrix.single_apply, and_comm]
  have hphi : firstSixᴴ * phiOne (Matrix.single (0 : Fin 10) (0 : Fin 10) (1 : ℂ)) * firstSix =
      (1296 : ℂ) • 1 := by
    unfold phiOne
    rw [ht, hext]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc firstSixᴴ firstSix, J_isometry, Matrix.one_mul, J_isometry]
  have hcm : complementaryMap (Matrix.single (0 : Fin 10) (0 : Fin 10) (1 : ℂ)) =
      (1296 : ℂ) • 1 := by
    unfold complementaryMap
    rw [hext, Matrix.transpose_smul, Matrix.transpose_one]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [H_unitary]
  unfold phiTwo at h00
  rw [hphi] at h00
  unfold hsAdjoint at h00
  simp only [hcm, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_six] at h00
  norm_num [Fin.ext_iff] at h00
