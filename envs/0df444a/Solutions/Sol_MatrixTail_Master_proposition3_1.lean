-- Prove2me | solution 1 for MatrixTail.Master.proposition3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:56:03.041832+00:00
-- url     : https://prove2.me/submissions/82f9754e-ee58-4247-9485-1fd0a73382d0

import Mathlib
import Definitions.Def_MatrixTail_Master_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal
open MatrixTail.Master

theorem mta_trExp_eq {d : ℕ} (Z : Matrix (Fin d) (Fin d) ℂ) (hZ : Z.IsHermitian) :
    trExp Z = ∑ i, Real.exp (hZ.eigenvalues i) := by
  unfold trExp mexp
  rw [Matrix.IsHermitian.cfc_eq hZ, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have h : star (hZ.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      (hZ.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hZ.eigenvectorUnitary.2
  rw [Matrix.trace_mul_cycle, h, one_mul, Matrix.trace_diagonal]
  simp [Complex.re_sum, Complex.exp_ofReal_re]

theorem mta_key {d : ℕ} [NeZero d] (Y : Matrix (Fin d) (Fin d) ℂ) (hY : Y.IsHermitian) (θ : ℝ) (hθ : 0 < θ) :
    ∃ hZ : (θ • Y).IsHermitian, Real.exp (θ * lambdaMax Y) ≤ trExp (θ • Y) ∧ 0 ≤ trExp (θ • Y) := by
  have hZ : (θ • Y).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hY.eq]
  refine ⟨hZ, ?_, ?_⟩
  · have hsp : spectrum ℝ Y = Set.range hY.eigenvalues := hY.spectrum_real_eq_range_eigenvalues
    have hne : (spectrum ℝ Y).Nonempty := by
      rw [hsp]; exact Set.range_nonempty _
    have hfin : (spectrum ℝ Y).Finite := by
      rw [hsp]; exact Set.finite_range _
    have hμ : lambdaMax Y ∈ spectrum ℝ Y := hne.csSup_mem hfin
    have hθμ : θ * lambdaMax Y ∈ spectrum ℝ (θ • Y) := by
      rw [spectrum.smul_eq_smul θ Y hne]
      exact ⟨lambdaMax Y, hμ, rfl⟩
    rw [hZ.spectrum_real_eq_range_eigenvalues] at hθμ
    obtain ⟨i, hi⟩ := hθμ
    rw [mta_trExp_eq _ hZ, ← hi]
    exact Finset.single_le_sum (f := fun i => Real.exp (hZ.eigenvalues i))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
  · rw [mta_trExp_eq _ hZ]
    exact Finset.sum_nonneg fun j _ => (Real.exp_pos _).le

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} [NeZero d] (Y : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hY_meas : Measurable Y) (hY_herm : ∀ ω, (Y ω).IsHermitian)
    (t θ : ℝ) (hθ : 0 < θ) (hint : Integrable (fun ω => trExp (θ • Y ω)) P) :
    P.real {ω | t ≤ lambdaMax (Y ω)} ≤ Real.exp (-θ * t) * ∫ ω, trExp (θ • Y ω) ∂P := by
  have hnn : ∀ ω, 0 ≤ trExp (θ • Y ω) := fun ω => (mta_key (Y ω) (hY_herm ω) θ hθ).choose_spec.2
  have hsub : {ω | t ≤ lambdaMax (Y ω)} ⊆ {ω | Real.exp (θ * t) ≤ trExp (θ • Y ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    refine le_trans (Real.exp_le_exp.mpr ?_) (mta_key (Y ω) (hY_herm ω) θ hθ).choose_spec.1
    exact mul_le_mul_of_nonneg_left hω hθ.le
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => trExp (θ • Y ω))
    (Filter.Eventually.of_forall hnn) hint (Real.exp (θ * t))
  have hmono : P.real {ω | t ≤ lambdaMax (Y ω)} ≤ P.real {ω | Real.exp (θ * t) ≤ trExp (θ • Y ω)} :=
    measureReal_mono hsub (measure_ne_top _ _)
  have hpos : 0 < Real.exp (θ * t) := Real.exp_pos _
  have e : Real.exp (-θ * t) = (Real.exp (θ * t))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [e]
  rw [le_inv_mul_iff₀ hpos]
  calc Real.exp (θ * t) * P.real {ω | t ≤ lambdaMax (Y ω)}
      ≤ Real.exp (θ * t) * P.real {ω | Real.exp (θ * t) ≤ trExp (θ • Y ω)} := by gcongr
    _ ≤ _ := hmark
