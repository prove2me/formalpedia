-- Prove2me | solution 1 for GlobalTheory.T.unfold_poincareSeries_lattice_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:34:03.389865+00:00
-- url     : https://prove2.me/submissions/695fdc48-8ff9-40c1-ae17-b2ffbc7d39fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnfoldPoincareSeriesLatticeFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnfoldPoincareSeriesLatticeFourierStatement
import Theorems.Thm_GlobalTheory_PoincareUnfold_unfold_poincare_fourier


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Γ : Type) [AddCommGroup Γ] (j : Γ →+ V), Function.Injective j → ∀ C : AddSubgroup Γ, (∀ R : ℝ, {c : Γ | c ∈ C ∧ ‖j c‖ ≤ R}.Finite) → Submodule.span ℝ (j '' (C : Set Γ)) = ⊤ → ∀ (n : ℕ) (t : Fin n → Γ) (Q : Γ → ℂ), (∀ x, Q x ≠ 0 → ∃ k, x - t k ∈ C) → (∀ k k', t k - t k' ∈ C → k = k') → (∀ x, ∀ c ∈ C, Q (x + c) = Q x) → ∀ F : V → ℂ, Integrable F μ → ∀ (a : Γ → ℂ) (l : Γ → V →ₗ[ℝ] ℝ), Summable (fun x => ‖a x‖) → l 0 = 0 → (∀ x, x ≠ 0 → l x ≠ 0) → (∀ x, a x ≠ 0 → ∀ c ∈ C, ∃ z : ℤ, l x (j c) = z) → (∀ v, ∑' x, Q x * F (j x + v) = ∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) → ∃ r : ℝ, 0 < r ∧ (∑ k, Q (t k)) * ∫ v, F v ∂μ = r * a 0 := by
  first | exact @GlobalTheory.PoincareUnfold.unfold_poincare_fourier | exact GlobalTheory.PoincareUnfold.unfold_poincare_fourier | (intros; apply GlobalTheory.PoincareUnfold.unfold_poincare_fourier <;> assumption)
end _root_.GlobalTheory.T
