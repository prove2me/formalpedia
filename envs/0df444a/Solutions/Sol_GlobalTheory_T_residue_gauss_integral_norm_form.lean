-- Prove2me | solution 1 for GlobalTheory.T.residue_gauss_integral_norm_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:04:15.951156+00:00
-- url     : https://prove2.me/submissions/001d4db4-8792-4ab9-a635-37b9c1d107c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGaussIntegralNormForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGaussIntegralNormFormStatement
import Theorems.Thm_GlobalTheory_JR_ResidueGauss_residue_gauss_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → IsField A.K → IsField A.L → ∀ (O : Subring A.L) (ϖ : A.Kˣ), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) → μ {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z} = ENNReal.ofReal (A.absK (ϖ : A.K) ^ 2) * μ (O : Set A.L) → ∀ a : A.K, (∀ s : A.K, algebraMap A.K A.L s ∈ O → A.psiK ψ (a * ϖ * s) = 1) → (∃ s : A.K, algebraMap A.K A.L s ∈ O ∧ A.psiK ψ (a * s) ≠ 1) → ∫ y in (O : Set A.L), A.psiK ψ (a * A.NL y) ∂μ = -((A.absK (ϖ : A.K) : ℝ) : ℂ) * (((μ (O : Set A.L)).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.JR.ResidueGauss.residue_gauss_integral | exact GlobalTheory.JR.ResidueGauss.residue_gauss_integral | (intros; apply GlobalTheory.JR.ResidueGauss.residue_gauss_integral <;> assumption)
end _root_.GlobalTheory.T
