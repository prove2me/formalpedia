-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedBandL2MartingaleFixedCompletedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:37:17.39785+00:00
-- url     : https://prove2.me/submissions/4860d6c8-16b1-446c-8d9d-b81876decc9f

import Theorems.Thm_Kyprianou_compensatedBandIsL2MartingaleCorrected
import Theorems.Thm_Kyprianou_Ch02_compensatedFiniteRegionMartingaleUnderCompletedFiltrationV1
import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    MeasureTheory.Martingale
      (Kyprianou.compensatedSmallJumpBand P ν N ε) ℱ P ∧
    ∀ t : ℝ≥0,
      MemLp (Kyprianou.compensatedSmallJumpBand P ν N ε t) 2 P := by
  let B : Set ℝ := {x | ε ≤ |x| ∧ |x| < 1}
  have hB : MeasurableSet B := by
    exact (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hfinite : ν B < ⊤ := by
    have hle : ν B ≤ ν {x : ℝ | ε ≤ |x|} := by
      apply measure_mono
      intro x hx
      exact hx.1
    exact lt_of_le_of_lt hle
      (ProbabilityTheory.IsLevyMeasure.measure_setOf_abs_ge_lt_top hν hε)
  haveI : IsFiniteMeasure (ν.restrict B) :=
    isFiniteMeasure_restrict.mpr hfinite.ne
  have hbound : ∀ᵐ x ∂(ν.restrict B), ‖x‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem hB] with x hx
    simpa only [Real.norm_eq_abs] using (hx.2.le : |x| ≤ 1)
  have hfirst : Integrable (fun x : ℝ => x) (ν.restrict B) :=
    Integrable.of_bound measurable_id.aestronglyMeasurable 1 hbound
  have hmart := Kyprianou.Ch02.compensatedFiniteRegionMartingaleUnderCompletedFiltrationV1
    P ν N B hB hfinite hfirst ℱ hℱ
  obtain ⟨_, _, _, hmem⟩ :=
    Kyprianou.compensatedBandIsL2MartingaleCorrected P ν hν N ε hε hε1
  refine ⟨?_, hmem⟩
  change MeasureTheory.Martingale
    (fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) ℱ P
  exact hmart
