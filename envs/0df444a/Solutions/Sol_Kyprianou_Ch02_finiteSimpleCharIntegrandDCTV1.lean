-- Prove2me | solution 1 for Kyprianou.Ch02.finiteSimpleCharIntegrandDCTV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:42:16.322845+00:00
-- url     : https://prove2.me/submissions/44543d59-ba6e-4e97-955b-a8df677f4ccb

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Characteristic integrands converge by dominated convergence on a finite mark set. -/
theorem solution
    (ν : Measure ℝ) [SigmaFinite ν]
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hf : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 x))
    (ξ : ℝ) :
    Tendsto (fun n => ∫ x in B,
      (Complex.exp (Complex.I * (((ξ * f n x : ℝ) : ℂ))) - 1) ∂ν)
      atTop (𝓝 (∫ x in B,
      (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν)) := by
  haveI : IsFiniteMeasure (ν.restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hfinite
  let g : ℝ → ℂ := fun y =>
    Complex.exp (Complex.I * (((ξ * y : ℝ) : ℂ))) - 1
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun x : ℝ => g (f n x)) (ν.restrict B) :=
    (hg.measurable.comp (f n).measurable).aestronglyMeasurable
  have hbound (n : ℕ) :
      ∀ᵐ x : ℝ ∂(ν.restrict B), ‖g (f n x)‖ ≤ (2 : ℝ) := by
    refine Filter.Eventually.of_forall fun x => ?_
    dsimp [g]
    calc
      ‖Complex.exp (Complex.I * (((ξ * f n x : ℝ) : ℂ))) - 1‖ ≤
          ‖Complex.exp (Complex.I * (((ξ * f n x : ℝ) : ℂ)))‖ +
            ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal]; norm_num
  have hlim :
      ∀ᵐ x : ℝ ∂(ν.restrict B),
        Tendsto (fun n => g (f n x)) atTop (𝓝 (g x)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    exact (hg.tendsto x).comp (hf x)
  exact tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
    hmeas (integrable_const _) hbound hlim
