-- Prove2me | solution 1 for Kyprianou.Ch04.actualCutoffAdaptedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:23:23.907998+00:00
-- url     : https://prove2.me/submissions/54728074-1845-4f62-bafd-f0ebb9d0da3a

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch04_pastMarkedIntegralMeasurableV1
open MeasureTheory ProbabilityTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The physical finite cutoff state is adapted to every filtration observing past counts. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hPast : ∀ (T : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (T : ℝ) ×ˢ univ →
      Measurable[F T] (fun ω => N.N ω D))
    (b a : ℝ) (Y X2 : NNReal → Ω → ℝ)
    (h2 : ∀ t ω, X2 t ω = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N ω))
    (hY : ∀ t ω, Y t ω = X2 t ω +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | a < |x| ∧ |x| < 1}, z.2 ∂(N.N ω)) -
      (t : ℝ) * ∫ x in {x : ℝ | a < |x| ∧ |x| < 1}, x ∂ν) :
    Adapted F Y := by
  intro t
  let D (B : Set ℝ) := Icc (0 : ℝ) (t : ℝ) ×ˢ B
  have hm (B : Set ℝ) (hB : MeasurableSet B) :
      Measurable[F t] (fun ω => ∫ z in D B, z.2 ∂(N.N ω)) :=
    Kyprianou.Ch04.pastMarkedIntegralMeasurableV1 P ν F N t (D B)
      (measurableSet_Icc.prod hB)
      (fun C hC hCm => hPast t C hCm (hC.trans (Set.prod_mono_right (subset_univ B))))
  have hlarge := hm {x : ℝ | 1 ≤ |x|} (measurableSet_le measurable_const measurable_id.abs)
  have hsmall := hm {x : ℝ | a < |x| ∧ |x| < 1}
    ((measurableSet_lt measurable_const measurable_id.abs).inter
      (measurableSet_lt measurable_id.abs measurable_const))
  have hEq : Y t = fun ω => b * (t : ℝ) +
      (∫ z in D {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N ω)) +
      (∫ z in D {x : ℝ | a < |x| ∧ |x| < 1}, z.2 ∂(N.N ω)) -
      (t : ℝ) * ∫ x in {x : ℝ | a < |x| ∧ |x| < 1}, x ∂ν := by
    funext ω
    rw [hY t ω,h2 t ω]
  rw [hEq]
  letI : MeasurableSpace Ω := F t
  exact ((measurable_const.add hlarge).add hsmall).sub measurable_const
