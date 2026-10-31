-- Prove2me | solution 1 for MarkovProcess.IsKolmogorovProcess.ae_eq_continuousShiftedUnitDyadicFloorLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:48:17.691758+00:00
-- url     : https://prove2.me/submissions/b890b89b-8079-4667-8dae-50684c3413d6

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicFloor_a02de258
import Definitions.Def_MarkovProcess_V3H_Continuity_KolmogorovTimeShift_b20f4218
import Definitions.Def_MarkovProcess_V3H_Continuity_ShiftedUnitModification_dfb22f1c
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
open MarkovProcess MarkovProcess.IsKolmogorovProcess

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem solution
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) (k t : NNRat) (ht : t ≤ 1) :
    X (k + t) =ᵐ[P] fun ω ↦
      continuousShiftedUnitDyadicFloorLimit k X ω (unitIccOfNNRat t ht) := by
  have hunit (Y : NNRat → Ω → E)
      (hY : IsKolmogorovProcess Y P p q M) :
      Y t =ᵐ[P] fun ω ↦ continuousUnitDyadicFloorLimit Y ω (unitIccOfNNRat t ht) := by
    filter_upwards
      [IsKolmogorovProcess.p2m_embedded_ccd84d32044074cd hY hγ hγq t ht,
        IsKolmogorovProcess.p2m_embedded_4297f4adce6b27c9 hY hγ hγq]
      with ω hident hcont
    simpa only [continuousUnitDyadicFloorLimit, if_pos hcont] using hident
  simpa only [continuousShiftedUnitDyadicFloorLimit, timeShift_apply] using!
    hunit (timeShift k X) (IsKolmogorovProcess.timeShift hX k)
