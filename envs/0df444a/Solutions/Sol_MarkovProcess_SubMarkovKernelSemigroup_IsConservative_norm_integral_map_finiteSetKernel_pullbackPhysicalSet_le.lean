-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:32:33.826102+00:00
-- url     : https://prove2.me/submissions/858f9aef-96de-49e9-aea6-e2517f07a439

import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalCompactTestTransport_e18ed42b
import Definitions.Def_MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
import Definitions.Def_MarkovProcess_V3H_Feller_FiniteSetCompactTestContinuity_012434c8
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
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
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
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
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Compact-test bounds for finite dense-time laws

Compact-test integrals against a physically indexed finite-set kernel, reindexed by dense-time
labels, are continuous in the starting point. Conservativity also gives a uniform norm bound by
the `C₀` norm of the test. Both statements include the empty coordinate set.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section Continuity

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]



end Continuity

section Bound

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]



end Bound

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Compact-test bounds for finite dense-time laws

Compact-test integrals against a physically indexed finite-set kernel, reindexed by dense-time
labels, are continuous in the starting point. Conservativity also gives a uniform norm bound by
the `C₀` norm of the test. Both statements include the empty coordinate set.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported ZeroAtInfty




variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]

namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) (y : alpha) :
    ‖∫ z, f z ∂(finiteSetKernel P (denseTimePhysicalSet J)).map
        (DenseTimePath.pullbackPhysicalSet J) y‖ ≤
      ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f‖ := by
  let K := (finiteSetKernel P (denseTimePhysicalSet J)).map
    (DenseTimePath.pullbackPhysicalSet J)
  let : IsMarkovKernel K := by
    let : IsMarkovKernel (finiteSetKernel P (denseTimePhysicalSet J)) :=
      hP.isMarkovKernel_finiteSetKernel P (denseTimePhysicalSet J)
    exact Kernel.IsMarkovKernel.map _ (DenseTimePath.measurable_pullbackPhysicalSet J)
  let : IsProbabilityMeasure (K y) := IsMarkovKernel.isProbabilityMeasure y
  let f₀ : C₀(J → alpha, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  change ‖∫ z, f z ∂K y‖ ≤ ‖f₀‖
  calc
    ‖∫ z, f z ∂K y‖ ≤ ‖f₀‖ * (K y).real Set.univ :=
      MeasureTheory.norm_integral_le_of_norm_le_const
        (ae_of_all _ fun z ↦ by
          simpa only [f₀,
            PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply] using!
            f₀.toBCF.norm_coe_le_norm z)
    _ = ‖f₀‖ := by
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]
