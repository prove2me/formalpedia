-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionShiftedSimpleApproxLawV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:55:22.17325+00:00
-- url     : https://prove2.me/submissions/648cf8fa-dc20-40ad-a19b-b7ab4ae69971
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkWindowMeasurableAndSameLawV1
import Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkFiniteWindowIntegralAETendstoV1

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Construct stationary simple-mark approximants for shifted finite Poisson windows. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ s t : ℝ≥0, ∃ F G : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Measurable (G n)) ∧
      (∀ n, P.map (F n) = P.map (G n)) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop
        (𝓝 (∫ z in (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop
        (𝓝 (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)))) := by
  let hsm : StronglyMeasurable (fun x : ℝ => x) :=
    measurable_id.stronglyMeasurable
  let f : ℕ → SimpleFunc ℝ ℝ := fun n => hsm.approx n
  have hf : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 x) :=
    fun x => hsm.tendsto_approx x
  intro s t
  let F : ℕ → Ω → ℝ := fun n ω =>
    ∫ z in (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
      f n z.2 ∂(N.N ω)
  let G : ℕ → Ω → ℝ := fun n ω =>
    ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
      f n z.2 ∂(N.N ω)
  have hsimple (n : ℕ) :=
    Kyprianou.Ch02.prmSimpleMarkWindowMeasurableAndSameLawV1
      P ν N B hB hfinite (f n) s t
  have hconvergence :=
    Kyprianou.Ch02.prmSimpleMarkFiniteWindowIntegralAETendstoV1
      P ν N B hB hfinite f hf s t
  refine ⟨F, G, (fun n => (hsimple n).1),
    (fun n => (hsimple n).2.1),
    (fun n => (hsimple n).2.2), ?_, ?_⟩
  · exact hconvergence.mono fun ω hw => hw.1
  · exact hconvergence.mono fun ω hw => hw.2
