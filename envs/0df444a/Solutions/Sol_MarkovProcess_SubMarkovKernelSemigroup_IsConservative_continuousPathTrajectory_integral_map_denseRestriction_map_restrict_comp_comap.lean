-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_integral_map_denseRestriction_map_restrict_comp_comap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:15:02.586158+00:00
-- url     : https://prove2.me/submissions/46de7c65-7d64-4140-a28e-5f1739ade307

import Definitions.Def_MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
import Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
import Definitions.Def_MarkovProcess_V3H_Trajectory_DenseRestrictionMarginals_931e4c17
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_denseRestriction_map_restrict

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite dense-time marginals of a restarted trajectory law

Composing the canonical continuous trajectory kernel with a measurable evaluation of the path
and pushing to a finite set of dense times integrates a compactly supported test through the
mapped finite-set kernel at the evaluated state.  The evaluation is arbitrary, so the identity
serves deterministic coordinates and stopping-time evaluations alike.

This is a kernel-level identity of finite-dimensional integrals.  No conditional or
stopping-time statement is proved here; those are in `Trajectory/FellerConditional.lean` and
`Trajectory/FellerStoppingConditional.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]



end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite dense-time marginals of a restarted trajectory law

Composing the canonical continuous trajectory kernel with a measurable evaluation of the path
and pushing to a finite set of dense times integrates a compactly supported test through the
mapped finite-set kernel at the evaluated state.  The evaluation is arbitrary, so the identity
serves deterministic coordinates and stopping-time evaluations alike.

This is a kernel-level identity of finite-dimensional integrals.  No conditional or
stopping-time statement is proved here; those are in `Trajectory/FellerConditional.lean` and
`Trajectory/FellerStoppingConditional.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported



variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (e : ContinuousPath alpha → alpha) (he : Measurable e)
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    ∫ z, f z ∂(((Kernel.comap (continuousPathTrajectory P hP default) e he ∘ₘ mu).map
        ContinuousPath.denseRestriction).map J.restrict) =
      ∫ omega, (∫ z, f z ∂((finiteSetKernel P (denseTimePhysicalSet J)).map
        (DenseTimePath.pullbackPhysicalSet J)) (e omega)) ∂mu := by
  let Q := continuousPathTrajectory P hP default
  let KJ := (finiteSetKernel P (denseTimePhysicalSet J)).map
    (DenseTimePath.pullbackPhysicalSet J)
  have hdense := ContinuousPath.measurable_denseRestriction (alpha := alpha)
  have hrestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) J
  have hQJ : (Q.map ContinuousPath.denseRestriction).map J.restrict = KJ :=
    continuousPathTrajectory_map_denseRestriction_map_restrict P hP default hK J
  have hkernel :
      ((Kernel.comap Q e he).map ContinuousPath.denseRestriction).map J.restrict =
        Kernel.comap KJ e he := by
    rw [← Kernel.comap_map_comm Q he hdense,
      ← Kernel.comap_map_comm (Q.map ContinuousPath.denseRestriction) he hrestrict, hQJ]
  have hmeasure :
      (((Kernel.comap Q e he ∘ₘ mu).map ContinuousPath.denseRestriction).map J.restrict) =
        Kernel.comap KJ e he ∘ₘ mu := by
    rw [Measure.map_comp mu _ hdense, Measure.map_comp mu _ hrestrict, hkernel]
  rw [hmeasure, Measure.comp_eq_comp_const_apply]
  let : IsMarkovKernel KJ := by
    dsimp only [KJ]
    let : IsMarkovKernel (finiteSetKernel P (denseTimePhysicalSet J)) :=
      hP.isMarkovKernel_finiteSetKernel P (denseTimePhysicalSet J)
    exact Kernel.IsMarkovKernel.map _ (DenseTimePath.measurable_pullbackPhysicalSet J)
  let : IsMarkovKernel (Kernel.comap KJ e he) := inferInstance
  let : IsFiniteMeasure ((Kernel.comap KJ e he ∘ₘ mu)) := inferInstance
  have hfint : Integrable f (Kernel.comap KJ e he ∘ₘ mu) := f.integrable
  rw [Measure.comp_eq_comp_const_apply] at hfint
  have hi := Kernel.integral_comp hfint
  simpa only [Kernel.const_apply, Kernel.comap_apply, Q, KJ] using hi
