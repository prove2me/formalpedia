-- Prove2me | solution 1 for Kyprianou.Ch02.realCharFunLimitOfAETendstoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:02:39.910836+00:00
-- url     : https://prove2.me/submissions/64202ee8-9755-471e-9b30-dff61563120f

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Almost-sure convergence of real random variables implies pointwise charFun convergence. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hF : ∀ n, Measurable (F n)) (hX : Measurable X)
    (hlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => F n ω) atTop (𝓝 (X ω)))
    (ξ : ℝ) :
    Tendsto (fun n => charFun (P.map (F n)) ξ) atTop
      (𝓝 (charFun (P.map X) ξ)) := by
  let g : ℝ → ℂ := fun x => Complex.exp ((((ξ * x : ℝ) : ℂ)) * Complex.I)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun ω : Ω => g (F n ω)) P :=
    (hg.measurable.comp (hF n)).aestronglyMeasurable
  have hbound (n : ℕ) :
      ∀ᵐ ω ∂P, ‖g (F n ω)‖ ≤ (1 : ℝ) := by
    refine Filter.Eventually.of_forall fun ω => ?_
    dsimp [g]
    rw [Complex.norm_exp_ofReal_mul_I]
  have hconverge : ∀ᵐ ω ∂P,
      Tendsto (fun n => g (F n ω)) atTop (𝓝 (g (X ω))) :=
    hlim.mono fun ω hω => (hg.tendsto (X ω)).comp hω
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun _ => (1 : ℝ)) hmeas (integrable_const _) hbound hconverge
  have hmap (Z : Ω → ℝ) (hZ : Measurable Z) :
      charFun (P.map Z) ξ = ∫ ω, g (Z ω) ∂P := by
    rw [charFun_apply_real]
    simpa only [g, Complex.ofReal_mul] using
      (integral_map hZ.aemeasurable hg.aestronglyMeasurable)
  have heq :
      (fun n : ℕ => charFun (P.map (F n)) ξ) =
      (fun n : ℕ => ∫ ω, g (F n ω) ∂P) := by
    funext n
    exact hmap (F n) (hF n)
  rw [heq, hmap X hX]
  exact hDCT
