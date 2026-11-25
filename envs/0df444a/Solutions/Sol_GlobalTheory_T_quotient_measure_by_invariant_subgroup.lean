-- Prove2me | solution 1 for GlobalTheory.T.quotient_measure_by_invariant_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:24:44.680697+00:00
-- url     : https://prove2.me/submissions/d19a4522-e4a7-4166-92b6-df8d2c39a0c0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuotientMeasureByInvariantSubgroup
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuotientMeasureByInvariantSubgroupStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Shear_lintegral_shear_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V A : Type) [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V] [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V] (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant] [lam.IsAddRightInvariant] (j : A →+ V), Measurable j → ∀ f : V → A, Measurable f → (∀ v a, f (v + j a) = f v) → ∀ K : Set A, MeasurableSet K → lam K ≠ 0 → lam K ≠ ⊤ → ∀ ψ : V → ℝ≥0∞, Measurable ψ → ∫⁻ v, ψ (v + j (f v)) ∂μ = ∫⁻ v, ψ v ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq | exact GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq | (intros; apply GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq <;> assumption)
end _root_.GlobalTheory.T
