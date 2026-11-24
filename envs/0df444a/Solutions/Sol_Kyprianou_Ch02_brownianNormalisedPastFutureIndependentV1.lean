-- Prove2me | solution 1 for Kyprianou.Ch02.brownianNormalisedPastFutureIndependentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:03:25.399462+00:00
-- url     : https://prove2.me/submissions/728473be-1c17-45ce-8aaf-b49268d3b893

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
    (B : LevyStochCalc.Brownian.BrownianMotion P) :
    ∀ {s t : ℝ}, 0 ≤ s → s < t →
      Indep
        (⨆ j ∈ Set.Iic s,
          MeasurableSpace.comap (fun ω => B.W j ω - B.W 0 ω) inferInstance)
        (MeasurableSpace.comap
          (fun ω => (B.W t ω - B.W 0 ω) - (B.W s ω - B.W 0 ω))
          inferInstance)
        P  := by
  intro s t hs hst
  let W : ℝ → Ω → ℝ := B.W
  have hbase : Indep
      (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W j) inferInstance)
      (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance)
      P := B.joint_increment_independent hs hst
  let past : MeasurableSpace Ω :=
    ⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W j) inferInstance
  have hpoint : ∀ j ∈ Set.Iic s,
      @Measurable Ω ℝ past inferInstance (W j) := by
    intro j hj
    exact measurable_iff_comap_le.mpr
      (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  have h0 : @Measurable Ω ℝ past inferInstance (W 0) :=
    hpoint 0 (Set.mem_Iic.mpr hs)
  have hle :
      (⨆ j ∈ Set.Iic s,
        MeasurableSpace.comap
          (fun ω => W j ω - W 0 ω) inferInstance) ≤ past := by
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    exact measurable_iff_comap_le.mp ((hpoint j hj).sub h0)
  have heq : (fun ω : Ω =>
      (W t ω - W 0 ω) - (W s ω - W 0 ω)) =
      (fun ω => W t ω - W s ω) := by
    funext ω
    ring
  rw [heq]
  exact indep_of_indep_of_le_left hbase hle
