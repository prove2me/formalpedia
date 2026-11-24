-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulSmallJumpCharFunFixedTimeLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:18:53.276817+00:00
-- url     : https://prove2.me/submissions/6fc7a72c-2b69-40bf-8e24-9571be655bd0

import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableAmbientV1
import Theorems.Thm_Kyprianou_Ch02_realCharFunLimitOfAETendstoV1
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ) (hM : ProbabilityTheory.IsLevyProcess M P)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (t : ℝ≥0) (ξ : ℝ)
    (hlim : ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀,
        |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω - M t ω| < δ) :
    Tendsto (fun n => charFun
      (P.map (Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t)) ξ)
      atTop (nhds (charFun (P.map (M t)) ξ)) := by
  let F := fun n => Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t
  have hF : ∀ n, Measurable (F n) := by
    intro n
    apply Measurable.sub _ measurable_const
    apply Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1
    exact measurableSet_Ioc.prod
      ((measurableSet_le measurable_const continuous_abs.measurable).inter
        (measurableSet_lt continuous_abs.measurable measurable_const))
  have hEq : increment M 0 t = M t := by
    funext ω
    change M t ω - M 0 ω = M t ω
    rw [congrFun hM.start_zero ω]
    simp
  have hX : AEMeasurable (M t) P :=
    hEq ▸ (hM.stationary_increments 0 t).aemeasurable_snd
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (nhds (hX.mk (M t) ω)) := by
    filter_upwards [hlim, hX.ae_eq_mk] with ω hω heq
    rw [← heq]
    exact Metric.tendsto_atTop.2 (by simpa [F, Real.dist_eq] using hω)
  rw [Measure.map_congr hX.ae_eq_mk]
  exact Kyprianou.Ch02.realCharFunLimitOfAETendstoV1 P F (hX.mk (M t))
    hF hX.measurable_mk hconv ξ
