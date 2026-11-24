-- Prove2me | solution 1 for GlobalTheory.MatrixGaussian.exists_congr_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:54:37.75211+00:00
-- url     : https://prove2.me/submissions/993a05de-d4cc-4046-8185-bebe25893e5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.MatrixGaussian
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.MatrixGaussian
theorem _root_.solution (A : Matrix ι ι ℂ) (hA : (A + Aᴴ).PosDef) :
    ∃ (M : Matrix ι ι ℂ) (d : ι → ℂ), M.det ≠ 0 ∧ (∀ i, 0 < (d i).re) ∧ Mᴴ * A * M = diagonal d := by
  obtain ⟨B, hB, hBA⟩ : ∃ B : Matrix ι ι ℂ, IsUnit B ∧ A + Aᴴ = star B * B := by
    open scoped MatrixOrder in
    exact CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hA.isStrictlyPositive
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hB
  set C := B⁻¹ with hC
  have h1 : B * C = 1 := Matrix.mul_nonsing_inv B hBd
  set A' := Cᴴ * A * C with hA'
  have h2 : A' + A'ᴴ = 1 := by
    have : A' + A'ᴴ = Cᴴ * (A + Aᴴ) * C := by
      simp only [hA', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_assoc]
    rw [this, hBA, star_eq_conjTranspose]
    calc Cᴴ * (Bᴴ * B) * C = (B * C)ᴴ * (B * C) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h1]; simp
  have hK : (I • (A' - A'ᴴ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    simp only [RCLike.star_def, conj_I, neg_smul, ← smul_neg, neg_sub]
  set U : Matrix ι ι ℂ := (hK.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : Uᴴ * U = 1 := hK.eigenvectorUnitary.2.1
  have hD : Uᴴ * (I • (A' - A'ᴴ)) * U = diagonal (RCLike.ofReal ∘ hK.eigenvalues) := by
    have := hK.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using this
  have h3 : A' = (1 / 2 : ℂ) • (1 - I • (I • (A' - A'ᴴ))) := by
    rw [← h2, smul_smul, I_mul_I]
    module
  refine ⟨C * U, fun i => (1 / 2 : ℂ) * (1 - I * (hK.eigenvalues i : ℂ)), ?_, fun i => by simp, ?_⟩
  · rw [det_mul]
    refine mul_ne_zero ?_ ?_
    · intro h
      have := congrArg det h1
      simp [h] at this
    · intro h
      have := congrArg det hUU
      simp [h] at this
  · calc (C * U)ᴴ * A * (C * U) = Uᴴ * A' * U := by
          simp only [hA', conjTranspose_mul, Matrix.mul_assoc]
      _ = Uᴴ * ((1 / 2 : ℂ) • (1 - I • (I • (A' - A'ᴴ)))) * U := by rw [← h3]
      _ = (1 / 2 : ℂ) • (Uᴴ * U - I • (Uᴴ * (I • (A' - A'ᴴ)) * U)) := by
          generalize I • (A' - A'ᴴ) = K
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      _ = _ := by
          rw [hD, hUU]
          ext i j
          by_cases h : i = j
          · subst h; simp
          · simp [h]
end GlobalTheory.MatrixGaussian
