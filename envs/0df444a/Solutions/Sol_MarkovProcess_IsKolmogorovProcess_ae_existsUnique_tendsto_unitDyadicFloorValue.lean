-- Prove2me | solution 1 for MarkovProcess.IsKolmogorovProcess.ae_existsUnique_tendsto_unitDyadicFloorValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:44:30.494222+00:00
-- url     : https://prove2.me/submissions/675f943c-45ec-4c78-841f-5fd60d39f93b

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicChaining_a582e42e
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicFloor_a02de258
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

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] [T2Space E] [CompleteSpace E]

theorem solution
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) 1,
      ∃! y : E, Tendsto (fun n : ℕ ↦ X (unitDyadicFloorValue n t) ω) atTop (𝓝 y) := by
  filter_upwards
    [IsKolmogorovProcess.p2m_embedded_37c5ae368c8eddc4 hX hγ hγq] with ω hω
  intro t
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hω t)
  refine ⟨y, hy, fun z hz ↦ ?_⟩
  exact tendsto_nhds_unique hz hy
