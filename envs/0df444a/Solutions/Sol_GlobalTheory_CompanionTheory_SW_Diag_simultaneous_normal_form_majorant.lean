-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Diag.simultaneous_normal_form_majorant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:32:15.255918+00:00
-- url     : https://prove2.me/submissions/6c0c9dd1-fed5-40bb-9485-df2b127c0092

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SimultaneousNormalFormMajorant
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Diag_exists_eq_transpose_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Diag
namespace GlobalTheory.CompanionTheory.SW.Diag
theorem _root_.solution :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S P : Matrix ι ι ℝ), S.IsSymm → S.det ≠ 0 →
      P.PosDef → P * S⁻¹ * P = S →
      ∃ (g : Matrix ι ι ℝ) (e : ι → ℝ), g.det ≠ 0 ∧ (∀ i, e i = 1 ∨ e i = -1) ∧
        gᵀ * P * g = 1 ∧ gᵀ * S * g = Matrix.diagonal e := by
  intro ι _ _ S P hS hSdet hP hPS
  obtain ⟨B, hB⟩ := exists_eq_transpose_mul_self hP.posSemidef
  have hPdet : P.det ≠ 0 := hP.det_pos.ne'
  have hBdet : B.det ≠ 0 := by
    intro h
    apply hPdet
    rw [hB, det_mul, det_transpose, h, mul_zero]
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  set C := B⁻¹ with hCdef
  have hBC : B * C = 1 := mul_nonsing_inv B hBu
  have hCB : C * B = 1 := nonsing_inv_mul B hBu
  have hCPC : Cᵀ * P * C = 1 := by
    rw [hB]
    calc Cᵀ * (Bᵀ * B) * C = (B * C)ᵀ * (B * C) := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBC, transpose_one, Matrix.one_mul]
  have hPCC : P * (C * Cᵀ) = 1 := by
    rw [hB]
    calc Bᵀ * B * (C * Cᵀ) = Bᵀ * ((B * C) * Cᵀ) := by simp only [Matrix.mul_assoc]
      _ = (C * B)ᵀ := by rw [hBC, Matrix.one_mul, transpose_mul]
      _ = 1 := by rw [hCB, transpose_one]
  have hCC : C * Cᵀ = P⁻¹ := (inv_eq_right_inv hPCC).symm
  have hSPS : S * P⁻¹ * S = P := by
    calc S * P⁻¹ * S = P * S⁻¹ * P * P⁻¹ * S := by rw [hPS]
      _ = P * S⁻¹ * (P * P⁻¹) * S := by simp only [Matrix.mul_assoc]
      _ = P := by
          rw [mul_nonsing_inv P hPu, Matrix.mul_one, Matrix.mul_assoc, nonsing_inv_mul S hSu,
            Matrix.mul_one]
  set A := Cᵀ * S * C with hAdef
  have hAT : Aᵀ = A := by
    simp only [hAdef, transpose_mul, transpose_transpose, hS.eq, Matrix.mul_assoc]
  have hA : A.IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hAT
  have hA2 : A * A = 1 := by
    calc A * A = Cᵀ * (S * (C * Cᵀ) * S) * C := by simp only [hAdef, Matrix.mul_assoc]
      _ = 1 := by rw [hCC, hSPS, hCPC]
  set U : Matrix ι ι ℝ := (hA.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  set e : ι → ℝ := RCLike.ofReal ∘ hA.eigenvalues with hedef
  have hspec : A = U * diagonal e * star U := hA.spectral_theorem
  have hU1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [hstar] at hspec hU1 hU2
  have hD : Uᵀ * A * U = diagonal e := by
    rw [hspec]
    calc Uᵀ * (U * diagonal e * Uᵀ) * U = (Uᵀ * U) * diagonal e * (Uᵀ * U) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal e := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
  have hDD : diagonal e * diagonal e = 1 := by
    rw [← hD]
    calc Uᵀ * A * U * (Uᵀ * A * U) = Uᵀ * (A * (U * Uᵀ) * A) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU2, Matrix.mul_one, hA2, Matrix.mul_one, hU1]
  have he : ∀ i, e i = 1 ∨ e i = -1 := by
    intro i
    have h := congrFun (congrFun hDD i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at h
    exact mul_self_eq_one_iff.mp h
  refine ⟨C * U, e, ?_, he, ?_, ?_⟩
  · rw [det_mul]
    refine mul_ne_zero ?_ ?_
    · intro h
      have h' := congrArg det hCB
      rw [det_mul, h, zero_mul, det_one] at h'
      exact zero_ne_one h'
    · intro h
      have h' := congrArg det hU1
      rw [det_mul, h, mul_zero, det_one] at h'
      exact zero_ne_one h'
  · calc (C * U)ᵀ * P * (C * U) = Uᵀ * (Cᵀ * P * C) * U := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCPC, Matrix.mul_one, hU1]
  · calc (C * U)ᵀ * S * (C * U) = Uᵀ * A * U := by
          rw [transpose_mul]
          simp only [hAdef, Matrix.mul_assoc]
      _ = diagonal e := hD
end GlobalTheory.CompanionTheory.SW.Diag
