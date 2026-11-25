-- Prove2me | solution 1 for Kyprianou.Ch04.finiteCutoffWindowStepsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:17:13.4776+00:00
-- url     : https://prove2.me/submissions/812c377b-fec0-4627-80c9-a1268b1b3d81

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_integerValuedFiniteDiracV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteWindowStepFromDiracV1
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_klsWindowIntegerValuedV1
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Simultaneous finite step representations on all compact windows. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ T : ℕ,
      ∃ (large small : Finset (ℝ × ℝ)) (a c : ℝ × ℝ → ℝ),
        ∀ t : NNReal, t ≤ (T : NNReal) →
          (∫ z in (Ioc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}),
            z.2 ∂(N.N ω)) = (∑ p ∈ large, if p.1 ≤ (t : ℝ) then a p else 0) ∧
          (∫ z in (Ioc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | ε < |x| ∧ |x| < 1}),
            z.2 ∂(N.N ω)) = (∑ p ∈ small, if p.1 ≤ (t : ℝ) then c p else 0) := by
  let B : Set ℝ := {x | 1 ≤ |x|}
  let C : Set ℝ := {x | ε < |x| ∧ |x| < 1}
  have hB : MeasurableSet B := measurableSet_le measurable_const measurable_id.abs
  have hC : MeasurableSet C :=
    (measurableSet_lt measurable_const measurable_id.abs).inter
      (measurableSet_lt measurable_id.abs measurable_const)
  have hBfin : ν B < ⊤ := hν.measure_setOf_abs_ge_lt_top (by norm_num)
  have hCfin : ν C < ⊤ :=
    (measure_mono (show C ⊆ {x | ε ≤ |x|} from fun _ h => h.1.le)).trans_lt
      (hν.measure_setOf_abs_ge_lt_top hε)
  have hD (D : Set ℝ) (hD : MeasurableSet D) (hf : ν D < ⊤) :
      ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
        (N.N ω).restrict (Ioc (0 : ℝ) (T : ℝ) ×ˢ D) =
          ∑ p ∈ s, ((N.N ω).restrict (Ioc (0 : ℝ) (T : ℝ) ×ˢ D)) {p} • Measure.dirac p := by
    filter_upwards [Kyprianou.Ch04.klsWindowIntegerValuedV1 P ν N D hD hf] with ω hω
    intro T
    exact Kyprianou.Ch02.integerValuedFiniteDiracV1 _ (hω T)
  have hL := Kyprianou.Ch02.prmFiniteWindowStepFromDiracV1 P ν N B hB hBfin
    (hD B hB hBfin)
  have hS := Kyprianou.Ch02.prmFiniteWindowStepFromDiracV1 P ν N C hC hCfin
    (hD C hC hCfin)
  filter_upwards [hL, hS] with ω hLω hSω
  intro T
  obtain ⟨large, a, ha⟩ := hLω T
  obtain ⟨small, c, hc⟩ := hSω T
  exact ⟨large, small, a, c, fun t ht => ⟨ha t ht, hc t ht⟩⟩
