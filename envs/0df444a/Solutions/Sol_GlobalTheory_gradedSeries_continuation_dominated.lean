-- Prove2me | solution 1 for GlobalTheory.gradedSeries_continuation_dominated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:10:08.603073+00:00
-- url     : https://prove2.me/submissions/23694727-64bc-4a2e-bc4b-1847f6a2533c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GradedSeriesContinuationDominated
import Theorems.Thm_GlobalTheory_gradedSeries_regroup
import Theorems.Thm_GlobalTheory_gradedSeries_continue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Metric Set
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {ι : Type} (deg : ι → ℕ),
    (∀ k, {i | deg i = k}.Finite) → ∀ (a : ι → ℂ) (b : ι → ℝ) (C δ ρ : ℝ) (P P' : ℂ → ℂ),
    0 < δ → (∀ i, 0 ≤ b i) → (∀ i, ‖a i‖ ≤ C * b i) →
    DifferentiableOn ℂ P (Metric.ball 0 ρ) → DifferentiableOn ℂ P' (Metric.ball 0 ρ) →
    (∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => a i * (x : ℂ) ^ deg i) (P x) ∧
      HasSum (fun i => (b i : ℂ) * (x : ℂ) ^ deg i) (P' x)) →
    ∀ X : ℂ, ‖X‖ < ρ → HasSum (fun i => a i * X ^ deg i) (P X) ∧
      Summable (fun i => b i * ‖X‖ ^ deg i) := by
  intro ι deg hfin a b C δ ρ P P' hδ hb hab hP hP' h X hX
  have hA := gradedSeries_continue deg a δ ρ P hδ hP (fun x h1 h2 => (h x h1 h2).1) X hX
  have hB := gradedSeries_continue deg (fun i => (b i : ℂ)) δ ρ P' hδ hP'
    (fun x h1 h2 => (h x h1 h2).2) ((‖X‖ : ℝ) : ℂ) (by simpa using hX)
  have hBr : Summable (fun k => (∑' i : deg ⁻¹' {k}, b i) * ‖X‖ ^ k) := by
    rw [← Complex.summable_ofReal]
    refine hB.summable.congr fun k => ?_
    push_cast [Complex.ofReal_tsum]
    rfl
  have hsb : Summable (fun i => b i * ‖X‖ ^ deg i) := by
    rw [← (Equiv.sigmaFiberEquiv deg).summable_iff]
    rw [summable_sigma_of_nonneg (f := (fun i => b i * ‖X‖ ^ deg i) ∘ (Equiv.sigmaFiberEquiv deg))
      (fun _ => mul_nonneg (hb _) (pow_nonneg (norm_nonneg _) _))]
    refine ⟨fun k => ?_, ?_⟩
    · have : Finite {i // deg i = k} := (hfin k).to_subtype
      exact Summable.of_finite
    · refine hBr.congr fun k => ?_
      rw [← tsum_mul_right]
      exact tsum_congr fun y => by
        simp [Equiv.sigmaFiberEquiv, show deg y.1 = k from y.2]
  have hsa : Summable (fun i => a i * X ^ deg i) := by
    refine Summable.of_norm_bounded (hsb.mul_left C) fun i => ?_
    rw [norm_mul, norm_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hab i) (pow_nonneg (norm_nonneg _) _)
  refine ⟨?_, hsb⟩
  have h3 := hsa.hasSum
  have h4 := (gradedSeries_regroup deg a X _ h3).unique hA
  rw [h4] at h3
  exact h3
end GlobalTheory
