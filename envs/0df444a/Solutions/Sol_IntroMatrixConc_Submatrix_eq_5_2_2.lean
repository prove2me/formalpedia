-- Prove2me | solution 1 for IntroMatrixConc.Submatrix.eq_5_2_2
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T05:26:22.345216+00:00
-- url     : https://prove2.me/submissions/4dc0933a-7ee1-4486-8c40-6bb509e408f5

import Mathlib
import Definitions.Def_IntroMatrixConc_Submatrix_Defs
import Theorems.Thm_IntroMatrixConc_Submatrix_eq_5_2_3
import Theorems.Thm_IntroMatrixConc_Submatrix_eq_5_2_4
import Theorems.Thm_IntroMatrixConc_Submatrix_eq_5_2_5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TroppMatrixConcentration IntroMatrixConc.Submatrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace TroppSubmatrixRoot
lemma max_eq_norm_of_psd {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hp : A.PosSemidef) : lambdaMax A = ‖A‖ := by
  unfold lambdaMax
  have hf : (spectrum ℝ A).Finite := by
    rw [hp.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have hn := CStarAlgebra.norm_mem_spectrum_of_nonneg hp.nonneg
  apply le_antisymm
  · apply csSup_le ⟨‖A‖, hn⟩
    intro x hx
    have hx' := (spectrum.algebraMap_mem_iff ℂ).mpr hx
    have hb := spectrum.norm_le_norm_of_mem hx'
    have hb' : |x| ≤ ‖A‖ := by simpa using hb
    exact (le_abs_self x).trans hb'
  · exact le_csSup hf.bddAbove hn


lemma gram_norm {d n : ℕ} [NeZero n] (B : Matrix (Fin d) (Fin n) ℂ) :
    lambdaMax (B.conjTranspose * B) = spectralNorm B ^ 2 := by
  rw [max_eq_norm_of_psd _ (Matrix.posSemidef_conjTranspose_mul_self B)]
  simpa only [TroppMatrixConcentration.spectralNorm, pow_two] using Matrix.l2_opNorm_conjTranspose_mul_self B

lemma column_nonneg {d n : ℕ} [NeZero n] (B : Matrix (Fin d) (Fin n) ℂ) : 0 ≤ maxColumnSq B := by
  unfold maxColumnSq
  exact (Finset.sum_nonneg (fun j hj => sq_nonneg ‖B j ⟨0,NeZero.pos n⟩‖)).trans
    (le_ciSup (Set.finite_range (fun k : Fin n => ∑ j : Fin d, ‖B j k‖ ^ 2)).bddAbove (⟨0,NeZero.pos n⟩ : Fin n))

lemma row_nonneg {d n : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin n) ℂ) : 0 ≤ maxRowSq B := by
  unfold maxRowSq
  exact (Finset.sum_nonneg (fun k hk => sq_nonneg ‖B ⟨0,NeZero.pos d⟩ k‖)).trans
    (le_ciSup (Set.finite_range (fun j : Fin d => ∑ k : Fin n, ‖B j k‖ ^ 2)).bddAbove (⟨0,NeZero.pos d⟩ : Fin d))

end TroppSubmatrixRoot
open TroppSubmatrixRoot

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d n : ℕ} [NeZero d] [NeZero n]
    (B : Matrix (Fin d) (Fin n) ℂ) (δ : Fin d → Ω → ℝ)
    (ξ : Fin n → Ω → ℝ) (p r : ℝ)
    (hp0 : 0 ≤ p) (hpd : p ≤ (d : ℝ))
    (hr0 : 0 ≤ r) (hrn : r ≤ (n : ℝ))
    (hδMeas : ∀ j, Measurable (δ j)) (hξMeas : ∀ k, Measurable (ξ k))
    (hIndep : iIndepFun (Sum.elim δ ξ) μ)
    (hδ : ∀ j, IsBernoulli μ (δ j) (p / (d : ℝ)))
    (hξ : ∀ k, IsBernoulli μ (ξ k) (r / (n : ℝ))) :
    Integrable (fun ω => spectralNorm (selectedSubmatrix B δ ξ ω) ^ 2) μ ∧
    (∫ ω, spectralNorm (selectedSubmatrix B δ ξ ω) ^ 2 ∂μ) ≤
      (3 : ℝ) * (p / (d : ℝ)) * (r / (n : ℝ)) * spectralNorm B ^ 2 +
      2 * (p * Real.log d / (d : ℝ)) * maxColumnSq B +
      2 * (r * Real.log n / (n : ℝ)) * maxRowSq B +
      Real.log d * Real.log n * maxEntrySq B := by
  classical

  have hd : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.pos n
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hln : 0 ≤ Real.log n := Real.log_nonneg hn
  have hp : 0 ≤ p / (d : ℝ) := div_nonneg hp0 (Nat.cast_nonneg d)
  have hr : 0 ≤ r / (n : ℝ) := div_nonneg hr0 (Nat.cast_nonneg n)
  have hδind : iIndepFun δ μ := by
    simpa only [Sum.elim_inl] using hIndep.precomp (g := Sum.inl) Sum.inl_injective
  have H := eq_5_2_3 μ B δ ξ p r hp0 hpd hr0 hrn hδMeas hξMeas hIndep hδ hξ
  have G := eq_5_2_4 μ B δ p hp0 hpd hδMeas hδind hδ
  have C := eq_5_2_5 μ B δ p hp0 hpd hδMeas hδind hδ
  rw [gram_norm] at G
  refine ⟨H.1, ?_⟩
  have hG := mul_le_mul_of_nonneg_left G.2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1.72) hr)
  have hC := mul_le_mul_of_nonneg_left C.2 hld
  have hsum := H.2.2.2.trans (add_le_add hG hC)
  have hg : 0 ≤ (p / (d : ℝ)) * (r / (n : ℝ)) * spectralNorm B ^ 2 :=
    mul_nonneg (mul_nonneg hp hr) (sq_nonneg _)
  have hc : 0 ≤ (p / (d : ℝ)) * Real.log d * maxColumnSq B :=
    mul_nonneg (mul_nonneg hp hld) (column_nonneg B)
  have hb : 0 ≤ (r / (n : ℝ)) * Real.log n * maxRowSq B :=
    mul_nonneg (mul_nonneg hr hln) (row_nonneg B)
  have hepd : p * Real.log d / (d : ℝ) = (p / (d : ℝ)) * Real.log d := by ring
  have hern : r * Real.log n / (n : ℝ) = (r / (n : ℝ)) * Real.log n := by ring
  rw [hepd, hern]
  nlinarith [hsum]

#print axioms solution
