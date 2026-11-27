-- Prove2me | solution 1 for Kyprianou.Ch04.nestedGridPairProbabilityTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:56:41.546151+00:00
-- url     : https://prove2.me/submissions/f9eabbf4-0cec-47ce-a0d2-a7e567894678

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_smallJumpContinuousQuadraticTailV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A nested cutoff maximal bound vanishes uniformly in the mesh. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) (hν : IsLevyMeasure ν) (K : ℝ) (T : NNReal)
    (e : ℕ → ℝ) (he : ∀ m, 0 < e m) (he0 : Tendsto e atTop (𝓝 0))
    (A : ℕ → ℕ → ℕ → ℝ → Set Ω)
    (hB : ∀ m n l, e l < e m → ∀ δ : ℝ, 0 < δ →
      P (A m n l δ) ≤ ENNReal.ofReal (4 * ((K^2 * (T : ℝ) *
        (1 + 4 * (T : ℝ) * (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
        (∫⁻ z in {z : ℝ | |z| ≤ e m}, ENNReal.ofReal (z^2) ∂ν).toReal)) /
        ENNReal.ofReal ((δ/2)^2)) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, ∀ᶠ l in atTop, (P (A m n l δ)).toReal ≤ η := by
  intro δ hδ η hη
  let q : ℝ → ℝ := fun r =>
    (∫⁻ z in {z : ℝ | |z| ≤ r}, ENNReal.ofReal (z^2) ∂ν).toReal
  let C : ℝ := 4 * (K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
    (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) / ((δ/2)^2)
  have hq : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [q,Function.comp_def] using (ENNReal.tendsto_toReal (a := 0) (by simp)).comp
      (Kyprianou.Ch04.smallJumpContinuousQuadraticTailV1 ν hν)
  have he' : Tendsto e atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨he0,Eventually.of_forall he⟩
  have hlim : Tendsto (fun m => C * q (e m)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C)).mul (hq.comp he')
  filter_upwards [hlim.eventually (Iio_mem_nhds hη)] with m hm
  intro n
  filter_upwards [he0.eventually (Iio_mem_nhds (he m))] with l hl
  have h := hB m n l hl δ hδ
  have hr := ENNReal.toReal_mono (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by positivity)) h
  rw [ENNReal.toReal_div,ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at hr
  refine hr.trans ?_
  have heq : 4 * ((K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
      (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
      q (e m)) / ((δ/2)^2) = C * q (e m) := by
    dsimp [C]; ring
  change _ ≤ η
  rw [← heq] at hm
  exact le_of_lt hm
