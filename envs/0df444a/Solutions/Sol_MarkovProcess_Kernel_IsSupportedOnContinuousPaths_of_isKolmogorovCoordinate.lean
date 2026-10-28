-- Prove2me | solution 1 for MarkovProcess.Kernel.IsSupportedOnContinuousPaths.of_isKolmogorovCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:47:02.157913+00:00
-- url     : https://prove2.me/submissions/7466ffc4-67db-4b9b-929d-1d7e5caac866

import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousLaw
import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_GlobalDyadicFloorModification
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_Polish_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite
import Theorems.Thm_MarkovProcess_IsKolmogorovProcess_ae_eq_continuousGlobalDyadicFloorLimit_nat_add
import Theorems.Thm_MarkovProcess_Kernel_IsSupportedOnContinuousPaths_of_continuousModification
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A global continuous modification assembled from canonical unit paths

The nonnegative real half-line is covered by the closed unit intervals `[n, n + 1]`.  On each
piece we use the canonical dyadic-floor limit of the process shifted by `n`.  Exact endpoint
identities make these pieces compatible, so `Set.liftCover` gives an honest raw global path.
On the simultaneous probability-one event where every canonical unit piece is continuous, local
finiteness of the closed cover makes the raw path continuous.  A single constant global fallback
then gives a total path which is continuous for every sample.

No measurability of the path-valued map, path-space law, Markov property, or Hunt-process claim is
asserted here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]



























omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The globally totalized path is continuous for every sample. -/
theorem continuous_continuousGlobalDyadicFloorLimit
    (X : NNRat → Ω → E) (ω : Ω) :
    Continuous (continuousGlobalDyadicFloorLimit X ω) := by
  by_cases h : Continuous (globalDyadicFloorLimit X ω)
  · simpa only [continuousGlobalDyadicFloorLimit, if_pos h] using h
  · simp only [continuousGlobalDyadicFloorLimit, if_neg h]
    exact continuous_const







theorem nnratNatFloor_le (t : NNRat) : (nnratNatFloor t : NNRat) ≤ t := by
  unfold nnratNatFloor
  exact_mod_cast Nat.floor_le (show 0 ≤ (t : ℝ) by positivity)

theorem nnratNatFloor_add_unitRemainder (t : NNRat) :
    (nnratNatFloor t : NNRat) + nnratUnitRemainder t = t := by
  exact add_tsub_cancel_of_le (nnratNatFloor_le t)

theorem nnratUnitRemainder_le_one (t : NNRat) : nnratUnitRemainder t ≤ 1 := by
  apply le_of_lt
  rw [nnratUnitRemainder, tsub_lt_iff_left (nnratNatFloor_le t)]
  unfold nnratNatFloor
  exact_mod_cast Nat.lt_floor_add_one (t : ℝ)

/-- At every fixed nonnegative rational time, the globally totalized continuous path is a
modification of the original process. -/
theorem IsKolmogorovProcess.ae_eq_continuousGlobalDyadicFloorLimit
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) (t : NNRat) :
    X t =ᵐ[P] fun ω ↦ continuousGlobalDyadicFloorLimit X ω (t : ℝ≥0) := by
  have hdecomp := nnratNatFloor_add_unitRemainder t
  simpa only [hdecomp] using
    IsKolmogorovProcess.ae_eq_continuousGlobalDyadicFloorLimit_nat_add
      hX hγ hγq (nnratNatFloor t) (nnratUnitRemainder t) (nnratUnitRemainder_le_one t)
end
end MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Kolmogorov support for dense-time trajectory kernels

This file applies the global dyadic-floor modification to the coordinate process of a
dense-time trajectory kernel.  A parameterwise Kolmogorov moment condition implies that the
dense-time law is supported on restrictions of continuous paths.

No measurability of the totalized modification as a path-valued map, PDE increment estimate,
Markov property of the resulting paths, or Hunt-process assertion is made here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal


noncomputable section


variable {beta alpha : Type*} [MeasurableSpace beta] [MetricSpace alpha]
  [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha]


theorem solution
    (kappa : Kernel beta (DenseTime → alpha)) [IsMarkovKernel kappa]
    (hK : ∀ b, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r) (kappa b) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p) :
    IsSupportedOnContinuousPaths kappa := by
  apply IsSupportedOnContinuousPaths.of_continuousModification kappa
  intro b
  obtain ⟨p, q, gamma, M, hcoord, hgamma, hgammaq⟩ := hK b
  let X : DenseTime → (DenseTime → alpha) → alpha := fun r omega ↦ omega r
  refine ⟨fun t omega ↦ continuousGlobalDyadicFloorLimit X omega t, ?_, ?_⟩
  · intro omega
    exact continuous_continuousGlobalDyadicFloorLimit X omega
  · intro r
    simpa only [X, DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply] using
      IsKolmogorovProcess.ae_eq_continuousGlobalDyadicFloorLimit
        hcoord hgamma hgammaq r
