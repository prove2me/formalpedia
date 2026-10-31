-- Prove2me | solution 1 for MarkovProcess.tendsto_integral_continuousPath_finiteDenseEvaluation_shift_randomTime_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:31:13.030782+00:00
-- url     : https://prove2.me/submissions/b3926065-43f3-40cb-8ade-d9a886325184

import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
import Definitions.Def_MarkovProcess_V3H_Path_ShiftCompactTestConvergence_fc2b2de1
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dominated convergence for tests along random times

This file records path-side dominated-convergence tools for a sequence of measurable random
times converging pointwise to a limiting random time.  The measure is any finite measure on
continuous-path space; no Markov or kernel assumption is used.  The deterministic-sequence
versions are in `ContinuousPathShiftCompactTestConvergence.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty CompactlySupported

namespace MarkovProcess

noncomputable section

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]





end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dominated convergence for tests along random times

This file records path-side dominated-convergence tools for a sequence of measurable random
times converging pointwise to a limiting random time.  The measure is any finite measure on
continuous-path space; no Markov or kernel assumption is used.  The deterministic-sequence
versions are in `ContinuousPathShiftCompactTestConvergence.lean`.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty CompactlySupported



variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]



namespace MarkovProcess
end MarkovProcess
open MarkovProcess
omit [MeasurableSpace alpha] [BorelSpace alpha] in

theorem solution
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (T : ℕ → ContinuousPath alpha → NNReal) (Tlim : ContinuousPath alpha → NNReal)
    (hT : ∀ n, Measurable (T n))
    (hlim : ∀ omega, Tendsto (fun n ↦ T n omega) atTop (nhds (Tlim omega)))
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    Tendsto (fun n ↦ ∫ omega, f (fun j : J ↦
        omega (T n omega + DenseTime.castOrderEmbedding j)) ∂mu) atTop
      (nhds (∫ omega, f (fun j : J ↦
        omega (Tlim omega + DenseTime.castOrderEmbedding j)) ∂mu)) := by
  let f0 : C₀(J → alpha, ℝ) := PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  have hcont : Continuous (fun p : NNReal × ContinuousPath alpha ↦
      f (fun j : J ↦ p.2 (p.1 + DenseTime.castOrderEmbedding j))) := by
    refine f.continuous.comp (continuous_pi fun j ↦ ?_)
    exact ContinuousEval.continuous_eval.comp
      (continuous_snd.prodMk (continuous_fst.add continuous_const))
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [] with n
    exact (hcont.measurable.comp
      ((hT n).prodMk measurable_id)).stronglyMeasurable.aestronglyMeasurable
  · refine ⟨‖f0‖, Filter.Eventually.of_forall fun n ↦ ?_⟩
    filter_upwards [] with omega
    simpa only [f0, PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply,
      Real.norm_eq_abs] using! f0.toBCF.norm_coe_le_norm
      (fun j : J ↦ omega (T n omega + DenseTime.castOrderEmbedding j))
  · filter_upwards [] with omega
    apply f.continuous.continuousAt.tendsto.comp
    rw [tendsto_pi_nhds]
    intro j
    exact omega.continuous.continuousAt.tendsto.comp
      ((hlim omega).add tendsto_const_nhds)
