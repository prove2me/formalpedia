-- Prove2me | solution 1 for IntroMatrixConc.Submatrix.eq_5_1_8
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T04:10:51.969073+00:00
-- url     : https://prove2.me/submissions/dd101505-b722-44f2-b2ec-dbccea6a5919

import Mathlib
import Definitions.Def_IntroMatrixConc_Submatrix_Defs
import Theorems.Thm_TroppMatrixConcentration_ch5_matrix_chernoff
import Theorems.Thm_TroppMatrixConcentration_ch3_expect_extrema_integrable
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace TroppStreamlinedChernoff

lemma spectrum_bounds {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) {x : ℝ} (hx : x ∈ spectrum ℝ A) :
    lambdaMin A ≤ x ∧ x ≤ lambdaMax A := by
  have hf : (spectrum ℝ A).Finite := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  exact ⟨csInf_le hf.bddBelow hx, le_csSup hf.bddAbove hx⟩

lemma norm_bound {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) {L : ℝ} (hL : 0 ≤ L)
    (h0 : 0 ≤ lambdaMin A) (h1 : lambdaMax A ≤ L) : ‖A‖ ≤ L := by
  have h : ‖cfc (fun x : ℝ => x) A‖ ≤ L := by
    apply norm_cfc_le hL
    intro x hx
    obtain ⟨h2, h3⟩ := spectrum_bounds A hA hx
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  rwa [cfc_id' ℝ A hA.isSelfAdjoint] at h

lemma nonneg_of_min {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (h0 : 0 ≤ lambdaMin A) : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ A := by
  apply Matrix.PosSemidef.nonneg
  rw [hA.posSemidef_iff_eigenvalues_nonneg]
  intro i
  exact h0.trans (spectrum_bounds A hA (hA.eigenvalues_mem_spectrum_real i)).1

lemma max_nonneg {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ A) : 0 ≤ lambdaMax A := by
  have hp := Matrix.nonneg_iff_posSemidef.mp hA
  let i : Fin d := ⟨0, NeZero.pos d⟩
  have hn := (hp.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp hp) i
  exact hn.trans (spectrum_bounds A hp.isHermitian (hp.isHermitian.eigenvalues_mem_spectrum_real i)).2

lemma exp_one_constant : Real.exp 1 - 1 ≤ (1.72 : ℝ) := by
  have h := Real.exp_one_lt_d9
  linarith

end TroppStreamlinedChernoff

open TroppStreamlinedChernoff

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (X k)) (hIndep : iIndepFun X μ)
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (X k ω) ∧ lambdaMax (X k ω) ≤ L) :
    let Y := fun ω => ∑ k, X k ω
    Integrable (fun ω => lambdaMax (Y ω)) μ ∧
      (∫ ω, lambdaMax (Y ω) ∂μ) ≤
        (1.72 : ℝ) * lambdaMax (∫ ω, Y ω ∂μ) + L * Real.log d := by
  classical
  let Y := fun ω => ∑ k, X k ω
  change Integrable (fun ω => lambdaMax (Y ω)) μ ∧
    (∫ ω, lambdaMax (Y ω) ∂μ) ≤ (1.72 : ℝ) * lambdaMax (∫ ω, Y ω ∂μ) + L * Real.log d
  have hXi : ∀ k, Integrable (X k) μ := by
    intro k
    apply (integrable_const L).mono' (hMeas k).aestronglyMeasurable
    filter_upwards [hHerm k, hBound k] with ω hh hb
    exact norm_bound _ hh hL hb.1 hb.2
  have hYi : Integrable Y μ := integrable_finset_sum _ (fun k hk => hXi k)
  have hYm : Measurable Y := by unfold Y; fun_prop
  have hYh : ∀ᵐ ω ∂μ, (Y ω).IsHermitian := by
    filter_upwards [ae_all_iff.mpr hHerm] with ω hh
    exact isSelfAdjoint_sum _ (fun k hk => hh k)
  have hXnn : ∀ k, ∀ᵐ ω ∂μ, (0 : Matrix (Fin d) (Fin d) ℂ) ≤ X k ω := by
    intro k
    filter_upwards [hHerm k, hBound k] with ω hh hb
    exact nonneg_of_min _ hh hb.1
  have hYnn : ∀ᵐ ω ∂μ, (0 : Matrix (Fin d) (Fin d) ℂ) ≤ Y ω := by
    filter_upwards [ae_all_iff.mpr hXnn] with ω hh
    exact Finset.sum_nonneg (fun k hk => hh k)
  have hmean : 0 ≤ lambdaMax (∫ ω, Y ω ∂μ) := max_nonneg _ (integral_nonneg_of_ae hYnn)
  have H := TroppMatrixConcentration.ch5_matrix_chernoff μ X L hL hMeas hIndep hHerm hBound
  have hb := H.2.2.1 1 (by norm_num)
  change (1 - Real.exp (-1)) / 1 * lambdaMin (∫ ω, Y ω ∂μ) - L * Real.log d / 1 ≤
      (∫ ω, lambdaMin (Y ω) ∂μ) ∧
    (∫ ω, lambdaMax (Y ω) ∂μ) ≤ (Real.exp 1 - 1) / 1 * lambdaMax (∫ ω, Y ω ∂μ) + L * Real.log d / 1 at hb
  refine ⟨(TroppMatrixConcentration.ch3_expect_extrema_integrable μ Y hYm hYh hYi).1, ?_⟩
  have hn := mul_le_mul_of_nonneg_right exp_one_constant hmean
  have hx := hb.2
  simp only [div_one] at hx
  linarith

#print axioms solution
