-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.rationalPastFutureRestartKernel_map_finitePastDenseFuture_restrict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:14:24.572575+00:00
-- url     : https://prove2.me/submissions/0581ad4e-9b15-4ab0-a1f0-0b5fcaf620e9

import Definitions.Def_MarkovProcess_V3H_Kernel_CompProdReindex_54ebfbc7
import Definitions.Def_MarkovProcess_V3H_Path_MixedFiniteMarginals_61bdbf42
import Definitions.Def_MarkovProcess_V3H_Restart_FinitePastRestart_281c4f1c
import Definitions.Def_MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc
import Definitions.Def_MarkovProcess_V3H_Restart_RationalRestart_9d6a4f09
import Definitions.Def_MarkovProcess_V3H_Restart_RationalRestrictedRestart_3bd46ae7
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
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
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open scoped NNReal

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

theorem solution
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (ContinuousPath.rationalPastFutureRestartKernel
      (continuousPathTrajectory P hP default) S).map
        (I.restrict ∘ Kernel.finitePastDenseFuture) =
      ((finiteTimeKernel P (MixedPastFuture.cutPastOrderedPhysicalTimes S I)) ⊗ₖ
        (finiteTimeKernel P
          (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)).comap
            (splitPastTerminal (alpha := alpha)
              (m := MixedPastFuture.pastPredecessorCard S I))
            measurable_splitPastTerminal).map
        (MixedPastFuture.pullbackCutCoordinates S I ∘
          MixedPastFuture.orderedSplitToCutCoordinates S I) := by
  exact p2m_embedded_7c93df04e6260a9a P hP default hK S I
