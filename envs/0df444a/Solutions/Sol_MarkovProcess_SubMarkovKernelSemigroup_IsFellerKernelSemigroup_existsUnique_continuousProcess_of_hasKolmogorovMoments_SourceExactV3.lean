-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments_SourceExactV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:59:54.261052+00:00
-- url     : https://prove2.me/submissions/4ef8ba04-333b-4a05-b23d-421d1dd410d1

import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousLaw
import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_GlobalDyadicFloorModification
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PhysicalReindex
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
import Definitions.Def_MarkovProcess_Feller_BackwardC0Recursion
import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductActiveReduction
import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductNormalization
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductStoneWeierstrass
import Definitions.Def_MarkovProcess_FiniteTime_FiniteSetKernelCompactTestTransport
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_C0_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KolmogorovMoments_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_PositiveC0OperatorMeasure
import Definitions.Def_MarkovProcess_Main
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_DenseFiltration
import Definitions.Def_MarkovProcess_Path_Polish_SourceClosedV3
import Definitions.Def_MarkovProcess_Restart_RationalRestart
import Definitions.Def_MarkovProcess_Restart_RationalRestrictedRestart
import Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteDenseApproximationOrdered
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Definitions.Def_MarkovProcess_Trajectory_AllTimeFiniteMarginals
import Definitions.Def_MarkovProcess_Trajectory_Basic
import Definitions.Def_MarkovProcess_Trajectory_FiniteMarginals
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
import Theorems.Thm_MarkovProcess_Kernel_eq_of_map_finiteRestriction_eq
import Theorems.Thm_MarkovProcess_Kernel_map_denseRestriction_injective
import Theorems.Thm_MarkovProcess_Kernel_map_denseRestriction_map_restrict
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_finiteDenseTimeSet
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_finiteTimeSet_of_integral_tendsto
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_isKolmogorovProcess_denseTimeTrajectory
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_tendsto_integral_compactlySupported_finiteDenseApproximationKernel
import Theorems.Thm_MarkovProcess_exists_denseTime_finiteOrderEmbedding_seq_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Intrinsic Kolmogorov moment bounds for a transition semigroup

Kolmogorov's continuity criterion is usually imposed on an already constructed coordinate
process.  This file states the same criterion directly on the transition semigroup: the
`p`-th moment of the displacement accumulated over a time step `h` is at most `M * h ^ q`,
uniformly in the starting point.

The predicate is purely a moment bound on the transition kernels.  It makes no path-space,
continuity, or stochastic-process claim; the transport of this bound to the canonical
dense-time coordinate process is proved elsewhere.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha]



namespace HasKolmogorovMoments

variable {P : SubMarkovKernelSemigroup alpha} {p q : ℝ} {M : ℝ≥0}

/-- The moment exponent of a Kolmogorov moment bound is positive. -/
theorem p_pos (hmom : P.HasKolmogorovMoments p q M) : 0 < p :=
  hmom.1

/-- The time exponent of a Kolmogorov moment bound is strictly larger than one. -/
theorem one_lt_q (hmom : P.HasKolmogorovMoments p q M) : 1 < q :=
  hmom.2.1





/-- A Kolmogorov moment bound admits a strictly positive Hölder exponent below the
Kolmogorov--Chentsov threshold `(q - 1) / p`; the witness `(q - 1) / (2 * p)` is used. -/
theorem exists_holderExponent (hmom : P.HasKolmogorovMoments p q M) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma < (q - 1) / p := by
  have hp : 0 < p := hmom.p_pos
  have hq : 0 < q - 1 := by linarith only [hmom.one_lt_q]
  refine ⟨(q - 1) / (2 * p), div_pos hq (by linarith only [hp]), ?_⟩
  exact div_lt_div_of_pos_left hq hp (by linarith only [hp])
end HasKolmogorovMoments
end SubMarkovKernelSemigroup
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Two-point marginals of the dense-time trajectory, and the intrinsic Kolmogorov bridge

The dense-time trajectory of a conservative sub-Markov kernel semigroup already has identified
one-time marginals.  This file identifies its two-time marginals: at dense times whose physical
images satisfy `iota d < iota d'`, the pair `(path d, path d')` has the law obtained by running
`P` for time `iota d` and then, from the state reached, for the increment `iota d' - iota d`.

The identification is then used to discharge the coordinate Kolmogorov hypothesis that every
trajectory theorem of the library assumes.  Under the intrinsic semigroup bound
`SubMarkovKernelSemigroup.HasKolmogorovMoments`, the canonical dense-time coordinate process is a
Kolmogorov process with a positive Hölder exponent below `(q - 1) / p`.

No continuity, modification, Markov-property, or path-regularity statement is proved here; only
the two-point law and the moment estimate it transports.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

namespace DenseTime







end DenseTime

namespace SubMarkovKernelSemigroup

section CompProd

variable {A B C E : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace E]





end CompProd

section TwoPoint

variable {D alpha : Type*} [MeasurableSpace alpha]



namespace IsConservative



variable [StandardBorelSpace alpha] [Nonempty alpha]





end IsConservative

end TwoPoint

section Bridge

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [StandardBorelSpace alpha] [Nonempty alpha]

namespace IsConservative





/-- An intrinsic Kolmogorov moment bound on the semigroup implies the coordinate Kolmogorov
hypothesis assumed by every trajectory theorem of the library: for each starting state the
canonical dense-time coordinate process is a Kolmogorov process admitting a positive Hölder
exponent strictly below the Kolmogorov--Chentsov threshold. -/
theorem kolmogorovRegular_of_hasKolmogorovMoments
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) :
    ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p := by
  intro x
  obtain ⟨gamma, hgamma0, hgammalt⟩ := hmom.exists_holderExponent
  exact ⟨p, q, gamma, M, isKolmogorovProcess_denseTimeTrajectory P hP hmom x, hgamma0, hgammalt⟩
end IsConservative
end Bridge
end SubMarkovKernelSemigroup
end
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying continuous-path kernels from dense-time restrictions

Restriction to the fixed dense time carrier is injective on kernels whose target is continuous-path
space.  A measurable left inverse is obtained from the total continuous-extension map.  This is a
deterministic property of continuous paths; it makes no stochastic-process, Markov, or regularity
claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace Kernel

noncomputable section

variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]





/-- Equality of continuous-path kernels is equivalent to equality after restriction to the fixed
dense time carrier. -/
theorem map_denseRestriction_eq_iff {kappa eta : Kernel beta (ContinuousPath alpha)} :
    kappa.map ContinuousPath.denseRestriction = eta.map ContinuousPath.denseRestriction ↔
      kappa = eta := by
  constructor
  · intro h
    exact map_denseRestriction_injective (alpha := alpha) (beta := beta) h
  · exact fun h ↦ congrArg
      (fun z : Kernel beta (ContinuousPath alpha) ↦
        z.map ContinuousPath.denseRestriction) h
end
end Kernel
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Arbitrary-time finite marginals of continuous-path trajectories

This file develops the simultaneous rational approximation needed to pass from the already
identified rational finite-dimensional distributions to finite families of arbitrary
nonnegative real times.  It proves the path-side dominated-convergence argument, identifies every
rational approximating law with the existing finite-set kernel, and reduces the desired equality
to compactly-supported-test convergence of those finite-set kernels.

The remaining Feller analytic statement is not claimed here: one must still prove that the
recursively composed finite-time kernels have that convergence under simultaneous convergence of
their strictly ordered time coordinates.  No continuous-time Markov or Hunt property is assumed
or asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section





/-- Every finite set of nonnegative real times has a simultaneous strictly ordered rational
approximation on its fixed subtype of coordinates. -/
theorem exists_denseTime_finset_seq_tendsto (I : Finset NNReal) :
    ∃ q : ℕ → I ↪o DenseTime,
      ∀ t, Tendsto (fun k ↦ DenseTime.castOrderEmbedding (q k t))
        atTop (nhds (t : NNReal)) := by
  simpa only using! exists_denseTime_finiteOrderEmbedding_seq_tendsto
    (OrderEmbedding.subtype (fun t : NNReal ↦ t ∈ I))
end
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Arbitrary-time finite marginals of Feller trajectories

This file removes the compact-test convergence premise from the earlier arbitrary-time
finite-marginal reduction. For a conservative Feller kernel semigroup whose dense trajectory has
the stated Kolmogorov control, every finite family of continuous-path coordinates has exactly the
finite-set-kernel law.

The theorem is stated for an arbitrary such semigroup; no particular semigroup is singled out,
and no Hunt-process property is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [LocallyCompactSpace alpha]

namespace SubMarkovKernelSemigroup

open IsConservative

variable [CompleteSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- A conservative Feller trajectory with the required Kolmogorov control has the prescribed
finite-dimensional law at every finite set of nonnegative-real times. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_map_finiteTimeSet
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (I : Finset NNReal) :
    (continuousPathTrajectory P hP default).map
        (ContinuousPath.finiteEvaluation (fun t : I ↦ (t : NNReal))) =
      finiteSetKernel P I := by
  obtain ⟨q, hq⟩ := exists_denseTime_finset_seq_tendsto I
  apply IsConservative.continuousPathTrajectory_map_finiteTimeSet_of_integral_tendsto
    P hP default hK I q hq
  intro x f
  exact hFeller.tendsto_integral_compactlySupported_finiteDenseApproximationKernel
    hP q hq f x
end SubMarkovKernelSemigroup
end
end MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The continuous-path Markov process of a Feller semigroup

This is the entry point of the library: for a conservative sub-Markov kernel semigroup `P` on a
nonempty, locally compact Polish state space it names the continuous-path process
`continuousProcess P hP`, restates under quotable names the properties proved for that process
elsewhere in the library, and proves that it is the unique Markov kernel into continuous paths
with the finite-dimensional distributions of `P`.

Every statement carries the Kolmogorov regularity hypothesis `P.KolmogorovRegular hP`, which is
what gives the dense-time trajectory of `P` a continuous modification.  The shift and restart
statements carry in addition the Feller hypothesis `P.IsFellerKernelSemigroup`; the uniqueness
statements carry neither Feller continuity nor local compactness.

Nothing here asserts a Hunt-process property, and no statement covers a stopping time that can be
infinite.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal




variable {alpha : Type*} [TopologicalSpace alpha]






noncomputable section DenseFiniteEvaluation

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [MeasurableSpace beta]




variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- A finite kernel into continuous-path space is determined by its evaluations at the finite
sets of physical times carried by rational labels. -/
theorem MarkovProcess.Kernel.eq_of_map_denseFiniteEvaluation_eq
    (kappa eta : Kernel beta (ContinuousPath alpha)) [IsFiniteKernel kappa]
    (h : ∀ I : Finset DenseTime,
      kappa.map (ContinuousPath.finsetEvaluation
          (SubMarkovKernelSemigroup.denseTimePhysicalSet I)) =
        eta.map (ContinuousPath.finsetEvaluation
          (SubMarkovKernelSemigroup.denseTimePhysicalSet I))) :
    kappa = eta := by
  rw [← map_denseRestriction_eq_iff (alpha := alpha) (beta := beta)]
  apply eq_of_map_finiteRestriction_eq
  intro I
  rw [map_denseRestriction_map_restrict kappa I, map_denseRestriction_map_restrict eta I, h I]





noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)













/-- Every finite rational-time marginal of the continuous-path process is the finite-set kernel of
`P` at the corresponding physical times. -/
theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousProcess_map_finiteEvaluation_denseTime
    (hK : P.KolmogorovRegular hP) (I : Finset DenseTime) :
    (continuousProcess P hP).map
        (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I)) =
      finiteSetKernel P (denseTimePhysicalSet I) :=
  continuousPathTrajectory_map_finiteDenseTimeSet P hP _ hK I





variable [LocallyCompactSpace alpha]

/-- Every finite-dimensional distribution of the continuous-path process of a conservative Feller
semigroup is the finite-set kernel of `P` at the same times. -/
theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (I : Finset NNReal) :
    (continuousProcess P hP).map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I :=
  hFeller.continuousPathTrajectory_map_finiteTimeSet P hP _ hK I







variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]







omit [LocallyCompactSpace alpha] in
/-- Uniqueness from rational times: a finite kernel into continuous paths whose evaluations at
the finite sets of physical times carried by rational labels are the finite-set kernels of `P` is
the continuous-path process of `P`.  Neither Feller continuity nor local compactness is used. -/
theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.eq_continuousProcess_of_map_finiteEvaluation_denseTime
    (hK : P.KolmogorovRegular hP) (Q : Kernel alpha (ContinuousPath alpha)) [IsFiniteKernel Q]
    (hQ : ∀ I : Finset DenseTime,
      Q.map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I)) =
        finiteSetKernel P (denseTimePhysicalSet I)) :
    Q = continuousProcess P hP :=
  Kernel.eq_of_map_denseFiniteEvaluation_eq Q _ fun I ↦
    (hQ I).trans (continuousProcess_map_finiteEvaluation_denseTime P hP hK I).symm

omit [LocallyCompactSpace alpha] in
/-- Uniqueness: a finite kernel into continuous paths with the finite-dimensional distributions of
`P` is the continuous-path process of `P`.  Only rational times are read off the hypothesis, so
neither Feller continuity nor local compactness is used. -/
theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.eq_continuousProcess_of_map_finiteEvaluation
    (hK : P.KolmogorovRegular hP) (Q : Kernel alpha (ContinuousPath alpha)) [IsFiniteKernel Q]
    (hQ : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) :
    Q = continuousProcess P hP :=
  IsConservative.eq_continuousProcess_of_map_finiteEvaluation_denseTime P hP hK Q fun I ↦
    hQ (denseTimePhysicalSet I)



/-- **Existence and uniqueness of the continuous-path Markov process.**  Let `P` be a sub-Markov
kernel semigroup on a nonempty, locally compact Polish state space that is conservative (`hP`),
Feller (`hFeller`), and Kolmogorov regular (`hK`).  Then there is exactly one Markov kernel `Q`
from the state space to continuous paths whose finite-dimensional distributions are those of `P`,
and it is `continuousProcess P hP`.

Here "finite-dimensional distributions" means, for each finite set `I` of nonnegative times, the
kernel `finiteSetKernel P I` obtained by composing the transition kernels of `P` along `I` in
increasing order; `ContinuousPath.finsetEvaluation I` reads the coordinates of a path at `I`.

The hypothesis `IsMarkovKernel Q` is not an extra requirement in disguise: it already follows from
the marginal condition at `I = ∅`, by `isMarkovKernel_of_map_finiteEvaluation_empty`. -/
theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.existsUnique_continuousProcess
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I := by
  refine ⟨continuousProcess P hP,
    ⟨inferInstance, hFeller.continuousProcess_map_finiteEvaluation P hP hK⟩, ?_⟩
  rintro Q ⟨hQ, hmarg⟩
  let : IsMarkovKernel Q := hQ
  exact IsConservative.eq_continuousProcess_of_map_finiteEvaluation P hP hK Q hmarg


omit [LocallyCompactSpace alpha] in
/-- Kolmogorov regularity follows from the intrinsic moment criterion on the semigroup. -/
theorem MarkovProcess.SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) : P.KolmogorovRegular hP :=
  IsConservative.kolmogorovRegular_of_hasKolmogorovMoments P hP hmom

include hP in

theorem solution
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I :=
  hFeller.existsUnique_continuousProcess P hP (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)
