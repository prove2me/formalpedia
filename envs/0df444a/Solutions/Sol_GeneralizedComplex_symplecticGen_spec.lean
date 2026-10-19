-- Prove2me | solution 1 for GeneralizedComplex.symplecticGen_spec
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:39:07.344498+00:00
-- url     : https://prove2.me/submissions/58a68b0c-32a8-45a4-b29b-21f38b316b1c

import Definitions.Def_GeneralizedComplex_Basic

open Matrix GeneralizedComplex

private lemma block_vec {𝕜 : Type*} [Field 𝕜] {N : ℕ}
    (A B C D : Matrix (Fin N) (Fin N) 𝕜) (u : GIdx N → 𝕜) :
    vecPart (fromBlocks A B C D *ᵥ u) = A *ᵥ vecPart u + B *ᵥ formPart u := by
  ext i
  simp [vecPart, formPart, mulVec, dotProduct, Fintype.sum_sum_type]

private lemma block_form {𝕜 : Type*} [Field 𝕜] {N : ℕ}
    (A B C D : Matrix (Fin N) (Fin N) 𝕜) (u : GIdx N → 𝕜) :
    formPart (fromBlocks A B C D *ᵥ u) = C *ᵥ vecPart u + D *ᵥ formPart u := by
  ext i
  simp [vecPart, formPart, mulVec, dotProduct, Fintype.sum_sum_type]

private lemma skew_inv_dot {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hskew : Aᵀ = -A) (hinv : A * A⁻¹ = 1) (X η : Fin N → ℝ) :
    (A *ᵥ X) ⬝ᵥ (A⁻¹ *ᵥ η) = -(X ⬝ᵥ η) := by
  rw [dotProduct_comm (A *ᵥ X), ← dotProduct_transpose_mulVec A, hskew, neg_mulVec,
    mulVec_mulVec, hinv, one_mulVec, dotProduct_neg]

theorem solution {N : ℕ} (ω : Matrix (Fin N) (Fin N) ℝ) (hω : ωᵀ = -ω)
    (hdet : ω.det ≠ 0) :
    IsGenAlmostComplex (symplecticGen ω) ∧ genType (plusIEigenspace (symplecticGen ω)) = 0 := by
  classical
  let A := ωᵀ
  have hskew : Aᵀ = -A := by
    change (ωᵀ)ᵀ = -ωᵀ
    rw [transpose_transpose, hω, neg_neg]
  have hunit : IsUnit A.det := by simpa [A, isUnit_iff_ne_zero] using hdet
  have hl : A⁻¹ * A = 1 := nonsing_inv_mul _ hunit
  have hr : A * A⁻¹ = 1 := mul_nonsing_inv _ hunit
  constructor
  · constructor
    · change fromBlocks 0 (-A⁻¹) A 0 * fromBlocks 0 (-A⁻¹) A 0 = -1
      simp only [fromBlocks_multiply, zero_mul, mul_zero, zero_add, add_zero,
        Matrix.neg_mul, Matrix.mul_neg, hl, hr]
      ext i j; cases i <;> cases j <;> simp [Matrix.one_apply]
    · intro u v
      change pairing (fromBlocks 0 (-A⁻¹) A 0 *ᵥ u)
        (fromBlocks 0 (-A⁻¹) A 0 *ᵥ v) = pairing u v
      simp only [pairing, block_form, block_vec, zero_mulVec, zero_add, add_zero,
        neg_mulVec, dotProduct_neg]
      rw [skew_inv_dot A hskew hr, skew_inv_dot A hskew hr]
      simp only [neg_neg]
      rw [dotProduct_comm (vecPart u), dotProduct_comm (vecPart v)]
      ring
  · let AC : Matrix (Fin N) (Fin N) ℂ := A.map Complex.ofReal
    let BC : Matrix (Fin N) (Fin N) ℂ := A⁻¹.map Complex.ofReal
    have hcl : BC * AC = 1 := by
      change A⁻¹.map Complex.ofRealHom * A.map Complex.ofRealHom = 1
      rw [← Matrix.map_mul, hl]
      simp
    have hmap : (symplecticGen ω).map Complex.ofReal = fromBlocks 0 (-BC) AC 0 := by
      ext i j; cases i <;> cases j <;> simp [symplecticGen, A, AC, BC]
    have hproj : tangentProjection (plusIEigenspace (symplecticGen ω)) = ⊤ := by
      apply top_unique
      intro X _
      let u : GIdx N → ℂ := Sum.elim X ((-Complex.I) • (AC *ᵥ X))
      have hv : vecPart u = X := rfl
      have hf : formPart u = (-Complex.I) • (AC *ᵥ X) := rfl
      refine ⟨u, ?_, ?_⟩
      · change ((symplecticGen ω).map Complex.ofReal) *ᵥ u - Complex.I • u = 0
        rw [sub_eq_zero, hmap]
        have ht : vecPart (fromBlocks 0 (-BC) AC 0 *ᵥ u) = Complex.I • X := by
          rw [block_vec, zero_mulVec, zero_add, hf, neg_mulVec, mulVec_smul,
            mulVec_mulVec, hcl, one_mulVec]
          simp
        have hb : formPart (fromBlocks 0 (-BC) AC 0 *ᵥ u) =
            Complex.I • ((-Complex.I) • (AC *ᵥ X)) := by
          rw [block_form, zero_mulVec, add_zero, hv, smul_smul]
          simp
        ext i
        cases i with
        | inl i => exact congrFun ht i
        | inr i => exact congrFun hb i
      · exact hv
    rw [genType, hproj]
    simp
