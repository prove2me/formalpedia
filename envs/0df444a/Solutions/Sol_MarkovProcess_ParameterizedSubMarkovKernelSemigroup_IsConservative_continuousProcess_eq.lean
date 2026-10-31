-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:27:12.346727+00:00
-- url     : https://prove2.me/submissions/3bf51cdc-11c1-475d-a035-18de3f75cd26

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Continuity_KolmogorovDenseTimeContinuousSupport_e9ca7f43
import Definitions.Def_MarkovProcess_V3H_FiniteTime_MeasureFiniteRestrictionIdentification_470add42
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcess_caf2584d
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimeTrajectory_d8dd1c30
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The continuous-path process of a measurably parameterized semigroup

For a jointly measurable family of sub-Markov kernel semigroups indexed by a measurable parameter
space `Theta`, this file constructs the quenched continuous-path process as a single kernel
`Kernel (Theta × alpha) (ContinuousPath alpha)`: joint measurability in the parameter and the
starting state is carried by the kernel structure, not proved parameter by parameter afterwards.

The construction transports the jointly measurable dense-time trajectory
`parameterizedDenseTimeTrajectory` through the same measurable continuous-extension map that the
unparameterized `continuousProcess` uses, with the same fallback path.  The central result is the
fibre identity: at every parameter and every starting point the parameterized process is
*literally* the unparameterized process of that parameter's semigroup, with no null set and no
regularity hypothesis.  It rests on the corresponding dense-time fibre identity, which is proved
here from the finite enumeration-prefix marginals of the two trajectory kernels.

Fibrewise conservativity, Kolmogorov regularity and Kolmogorov moment bounds are named as
predicates on the parameterized family, so that consumers state hypotheses once.

No Markov, strong Markov, Feller, equivariance, annealed or killed statement is proved here; each
of those is a separate transport through the fibre identity.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

section Conservativity

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]



end Conservativity

section Moments

variable {Theta alpha : Type*} [MeasurableSpace Theta] [PseudoEMetricSpace alpha]
  [MeasurableSpace alpha]



end Moments

section DenseTimeFibre

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]





end DenseTimeFibre

section ContinuousProcess

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)













/-- Under fibrewise Kolmogorov regularity, the jointly measurable dense-time trajectory of `P` is
almost surely supported on the dense-time restrictions of continuous paths, simultaneously for
every parameter and every starting state. -/
theorem IsConservative.isSupportedOnContinuousPaths_parameterizedDenseTimeTrajectory
    (hK : P.KolmogorovRegular hP) :
    Kernel.IsSupportedOnContinuousPaths
      (P.parameterizedDenseTimeTrajectory hP DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding) := by
  let : IsMarkovKernel (P.parameterizedDenseTimeTrajectory hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding) :=
    P.isMarkovKernel_parameterizedDenseTimeTrajectory hP _ _
  refine Kernel.IsSupportedOnContinuousPaths.p2m_embedded_97b706232ed542b0 _ ?_
  rintro ⟨theta, x⟩
  rw [p2m_embedded_6c61c679d0514bbd]
  exact hK theta x



section QuenchedExpectations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



variable [MeasurableSpace E] [BorelSpace E]





end QuenchedExpectations

end ContinuousProcess

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The continuous-path process of a measurably parameterized semigroup

For a jointly measurable family of sub-Markov kernel semigroups indexed by a measurable parameter
space `Theta`, this file constructs the quenched continuous-path process as a single kernel
`Kernel (Theta × alpha) (ContinuousPath alpha)`: joint measurability in the parameter and the
starting state is carried by the kernel structure, not proved parameter by parameter afterwards.

The construction transports the jointly measurable dense-time trajectory
`parameterizedDenseTimeTrajectory` through the same measurable continuous-extension map that the
unparameterized `continuousProcess` uses, with the same fallback path.  The central result is the
fibre identity: at every parameter and every starting point the parameterized process is
*literally* the unparameterized process of that parameter's semigroup, with no null set and no
regularity hypothesis.  It rests on the corresponding dense-time fibre identity, which is proved
here from the finite enumeration-prefix marginals of the two trajectory kernels.

Fibrewise conservativity, Kolmogorov regularity and Kolmogorov moment bounds are named as
predicates on the parameterized family, so that consumers state hypotheses once.

No Markov, strong Markov, Feller, equivariance, annealed or killed statement is proved here; each
of those is a separate transport through the fibre identity.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal







variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)















namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative

end MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative
open MeasureTheory ProbabilityTheory Set
namespace MarkovProcess.Kernel
variable {β alpha : Type*} [MeasurableSpace β] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [T2Space alpha]
variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]
private theorem IsSupportedOnContinuousPaths.p2m_inline_toContinuousPathKernel_eq
    (κ : Kernel β (DenseTime → alpha)) (hκ : IsSupportedOnContinuousPaths κ)
    (default₁ default₂ : ContinuousPath alpha) :
    toContinuousPathKernel κ default₁ = toContinuousPathKernel κ default₂ := by
  rw [toContinuousPathKernel_eq_map, toContinuousPathKernel_eq_map]
  ext x s hs
  rw [Kernel.map_apply' _ (ContinuousPath.measurable_continuousExtension default₁) x hs,
    Kernel.map_apply' _ (ContinuousPath.measurable_continuousExtension default₂) x hs]
  have hfun : ContinuousPath.continuousExtension default₁ =ᵐ[κ x]
      ContinuousPath.continuousExtension default₂ :=
    (hκ x).mono fun path hpath ↦ by
      obtain ⟨omega, rfl⟩ := hpath
      rw [ContinuousPath.continuousExtension_denseRestriction,
        ContinuousPath.continuousExtension_denseRestriction]
  exact measure_congr (hfun.preimage s)

end MarkovProcess.Kernel

open MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative
theorem solution (hK : P.KolmogorovRegular hP)
    (default : ContinuousPath alpha) :
    IsConservative.continuousProcess P hP =
      Kernel.toContinuousPathKernel
        (P.parameterizedDenseTimeTrajectory hP DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding) default :=
  Kernel.IsSupportedOnContinuousPaths.p2m_inline_toContinuousPathKernel_eq _
    (IsConservative.isSupportedOnContinuousPaths_parameterizedDenseTimeTrajectory P hP hK) _ default
