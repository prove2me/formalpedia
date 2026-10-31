-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.lintegral_edist_continuousProcess_denseTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:10:19.802596+00:00
-- url     : https://prove2.me/submissions/ec88411e-22fc-411d-8097-b2c491933410

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Continuity_PathModulus_4f3af818
import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_C0SemigroupJoint_9aea0383
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Trajectory_Basic_34bd0835
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
import Mathlib.Topology.EMetricSpace.Basic
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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

namespace DenseTime



/-- The physical embedding of dense time is an isometry for the extended distance. -/
theorem dist_castOrderEmbedding (r r' : DenseTime) :
    dist (castOrderEmbedding r) (castOrderEmbedding r') = dist r r' := by
  have hcoe : ∀ u : DenseTime, ((castOrderEmbedding u : ℝ≥0) : ℝ) = ((u : ℚ) : ℝ) := by
    intro u
    simp only [castOrderEmbedding, NNRat.castOrderEmbedding_apply]
    push_cast
    rfl
  rw [NNReal.dist_eq, hcoe, hcoe, NNRat.dist_eq, ← Rat.dist_cast, Real.dist_eq]

/-- The physical embedding of dense time preserves the extended distance. -/
theorem edist_castOrderEmbedding (r r' : DenseTime) :
    edist (castOrderEmbedding r) (castOrderEmbedding r') = edist r r' := by
  rw [edist_dist, edist_dist, dist_castOrderEmbedding]

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
# The continuous-path process as a Kolmogorov process, and its uniform modulus

The intrinsic moment criterion `HasKolmogorovMoments p q M` is a statement about the transition
kernels.  This file transports it to the continuous-path process itself, at *all* nonnegative
real times and with the very same constants: the coordinate process of `continuousProcess P hP x`
is a Kolmogorov process with exponents `p`, `q` and constant `M`, for every starting point `x`.
Rational times come from the identification of the dense-time projection of the process with the
dense-time trajectory; irrational times follow by path continuity and Fatou's lemma, so no Feller
hypothesis and no local compactness are needed.

Combining this with the quantitative chaining estimate of `Continuity/PathModulus.lean` gives the
modulus statement that tightness on path space consumes: for a horizon `T`, an oscillation
tolerance `r` and a mass tolerance `eps` there is one scale `delta > 0` that works simultaneously
at every starting point.

Main results:

* `IsConservative.map_denseRestriction_continuousProcess`, the dense-time projection of the
  process;
* `IsConservative.isKolmogorovProcess_continuousProcess`, the moment bound at all real times;
* `IsConservative.exists_measure_compl_modulusSet_le`, the modulus estimate uniform in the
  starting point.

No tightness, weak continuity, or Hölder-path statement is proved here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- The dense-time projection of the continuous-path process is the canonical dense-time
trajectory of `P`. -/
theorem IsConservative.map_denseRestriction_continuousProcess (hK : P.KolmogorovRegular hP) :
    (continuousProcess P hP).map ContinuousPath.denseRestriction =
      denseTimeTrajectory P hP DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding := by
  unfold IsConservative.continuousProcess IsConservative.continuousPathTrajectory
  exact Kernel.map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate _ _ hK







end

end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The continuous-path process as a Kolmogorov process, and its uniform modulus

The intrinsic moment criterion `HasKolmogorovMoments p q M` is a statement about the transition
kernels.  This file transports it to the continuous-path process itself, at *all* nonnegative
real times and with the very same constants: the coordinate process of `continuousProcess P hP x`
is a Kolmogorov process with exponents `p`, `q` and constant `M`, for every starting point `x`.
Rational times come from the identification of the dense-time projection of the process with the
dense-time trajectory; irrational times follow by path continuity and Fatou's lemma, so no Feller
hypothesis and no local compactness are needed.

Combining this with the quantitative chaining estimate of `Continuity/PathModulus.lean` gives the
modulus statement that tightness on path space consumes: for a horizon `T`, an oscillation
tolerance `r` and a mass tolerance `eps` there is one scale `delta > 0` that works simultaneously
at every starting point.

Main results:

* `IsConservative.map_denseRestriction_continuousProcess`, the dense-time projection of the
  process;
* `IsConservative.isKolmogorovProcess_continuousProcess`, the moment bound at all real times;
* `IsConservative.exists_measure_compl_modulusSet_le`, the modulus estimate uniform in the
  starting point.

No tightness, weak continuity, or Hölder-path statement is proved here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal




open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) (hK : P.KolmogorovRegular hP)
    (x : alpha) (r r' : DenseTime) :
    ∫⁻ omega, edist (omega (DenseTime.castOrderEmbedding r))
          (omega (DenseTime.castOrderEmbedding r')) ^ p ∂(continuousProcess P hP x) ≤
      (M : ℝ≥0∞) * edist (DenseTime.castOrderEmbedding r)
        (DenseTime.castOrderEmbedding r') ^ q := by
  have hcoord : Measurable
      (fun path : DenseTime → alpha ↦ edist (path r) (path r') ^ p) :=
    ((measurable_pi_apply r).edist (measurable_pi_apply r')).pow_const p
  have hmap := congrArg (fun kappa : Kernel alpha (DenseTime → alpha) ↦ kappa x)
    (IsConservative.map_denseRestriction_continuousProcess P hP hK)
  simp only [Kernel.map_apply _ ContinuousPath.measurable_denseRestriction] at hmap
  calc ∫⁻ omega, edist (omega (DenseTime.castOrderEmbedding r))
          (omega (DenseTime.castOrderEmbedding r')) ^ p ∂(continuousProcess P hP x)
      = ∫⁻ path, edist (path r) (path r') ^ p
          ∂(((continuousProcess P hP) x).map ContinuousPath.denseRestriction) :=
        (lintegral_map hcoord ContinuousPath.measurable_denseRestriction).symm
    _ = ∫⁻ path, edist (path r) (path r') ^ p
          ∂(denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) := by rw [hmap]
    _ ≤ (M : ℝ≥0∞) * edist r r' ^ q :=
        (IsConservative.p2m_embedded_e8d3228da91484fb P hP hmom x).kolmogorovCondition
          r r'
    _ = (M : ℝ≥0∞) * edist (DenseTime.castOrderEmbedding r)
          (DenseTime.castOrderEmbedding r') ^ q := by
        rw [DenseTime.edist_castOrderEmbedding]
