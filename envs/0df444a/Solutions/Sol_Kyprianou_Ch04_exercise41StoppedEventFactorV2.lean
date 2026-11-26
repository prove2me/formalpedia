-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41StoppedEventFactorV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:37:38.863098+00:00
-- url     : https://prove2.me/submissions/2fe2b5ef-610d-48b6-ad92-353951671161

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (τ : Ω → NNReal)
    (hτ : ∀ s, MeasurableSet[F s] {ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : ∀ s, MeasurableSet[F s] (A ∩ {ω | τ ω ≤ s}))
    (G : Set (NNReal → ℝ)) (hG : MeasurableSet G) :
    P (A ∩ {ω | (fun u => L.X (τ ω + u) ω - L.X (τ ω) ω) ∈ G}) =
      P A * P {ω | (fun u => L.X u ω) ∈ G} := by
  let Y : Ω → (NNReal → ℝ) := fun ω u =>
    L.X (τ ω + u) ω - L.X (τ ω) ω
  let Z : Ω → (NNReal → ℝ) := fun ω u => L.X u ω
  have hstop := isStoppingTime_withTop_of_le_events τ hτ
  have hY : Measurable Y :=
    levy_finiteStopping_stoppedFuturePath_measurable L τ hstop
  have hZ : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro t
    exact (L.adapted t).mono (F.le t) le_rfl
  have hLaw : Measure.map Y (P.restrict A) =
      P A • Measure.map Z P :=
    levy_finiteStopping_restrictedFuturePath_mapLaw L τ hstop A hA
  have heq := congrArg (fun m : Measure (NNReal → ℝ) => m G) hLaw
  rw [Measure.map_apply hY hG, Measure.restrict_apply (hY hG),
    Measure.smul_apply, smul_eq_mul, Measure.map_apply hZ hG] at heq
  rw [Set.inter_comm] at heq
  change P (A ∩ Y ⁻¹' G) = P A * P (Z ⁻¹' G)
  exact heq
