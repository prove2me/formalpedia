-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:29:55.901511+00:00
-- url     : https://prove2.me/submissions/91db9b78-1d91-48d3-97d1-65f1aee86c91

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
open Matrix
variable {β : Type} [Fintype β] [DecidableEq β]
namespace GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
theorem _root_.solution (d : ℕ) (P : Matrix β β ℂ) (hP : P.det ≠ 0)
    (H : (Fin d → β → ℂ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ C : Fin d → β → ℂ, H (fun k => C k ᵥ* P) =
      ENNReal.ofReal |((Complex.normSq P.det) ^ d)⁻¹| * ∫⁻ D, H D := by
  let T : (β → ℂ) →ₗ[ℝ] (β → ℂ) := (Matrix.toLin' Pᵀ).restrictScalars ℝ
  let L : (Fin d → β → ℂ) →ₗ[ℝ] (Fin d → β → ℂ) := LinearMap.pi fun k => T ∘ₗ LinearMap.proj k
  have hdT : LinearMap.det T = Complex.normSq P.det := by
    simp only [T]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply]
  have hdL : LinearMap.det L = (Complex.normSq P.det) ^ d := by
    simp only [L]
    rw [LinearMap.det_pi, Finset.prod_const, hdT]
    simp
  have hne : LinearMap.det L ≠ 0 := by
    rw [hdL]
    exact pow_ne_zero _ (Complex.normSq_pos.2 hP).ne'
  have hL : (fun C : Fin d → β → ℂ => fun k => C k ᵥ* P) = L := by
    funext C k
    simp [L, T, toLin'_apply, mulVec_transpose]
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  haveI : (volume : Measure (β → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin d → β → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have e : ∫⁻ C : Fin d → β → ℂ, H (fun k => C k ᵥ* P) = ∫⁻ C, H (L C) := by
    rw [← hL]
  rw [e, ← lintegral_map hH hLm, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne,
    lintegral_smul_measure, hdL]
  rfl
end GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
