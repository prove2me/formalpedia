-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.isTightMeasureSet_insert_continuousProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:16:09.024003+00:00
-- url     : https://prove2.me/submissions/ad37639e-b3c0-4845-a11d-b65d755f4fbe

import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeConvergence_4d25bc20
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelCompactTestTransport_3904fd05
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Definitions.Def_MarkovProcess_V3H_Semigroup_OrbitContinuity_8cf8e1f5
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_WeakContinuity_59a9cfa0
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Tight
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
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_ContinuousPath_exists_measure_compl_modulusSet_le
import Theorems.Thm_MarkovProcess_ContinuousPath_isTightMeasureSet_of_measure_compl_modulusSet_le
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_isKolmogorovProcess_continuousProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Tightness of the path laws of a continuous-path Markov process

The modulus estimate of `Trajectory/PathModulus.lean` is uniform in the starting point, and the
process starts where it is told, so the laws `continuousProcess P hP x` for `x` in a compact set
of starting points satisfy both hypotheses of the Arzelà--Ascoli tightness criterion of
`Continuity/PathTightness.lean`.  This file records the resulting tightness statement.

Tightness is asserted for the starting points ranging over a *compact* set.  Over all starting
points at once it is false in general already at time zero: the time-zero laws are the Dirac
measures `delta_x`, and `{delta_x : x ∈ alpha}` is tight exactly when `alpha` is compact.  A compact set of starting points is also all that weak continuity in the
starting point needs, since continuity at a point only sees a neighbourhood of it.

The state space is assumed *proper* (closed balls are compact).  This is what discharges the
compact containment condition: the modulus confines a path to a bounded neighbourhood of its
starting point, and over a proper space bounded closed sets are compact.  On a general complete
separable metric state space the compact containment condition has to be supplied separately;
`ContinuousPath.isCompact_moduliSet_of_forall_isCompact` is the interface for that.

Main results:

* `IsConservative.measure_eval_zero_notMem_eq_zero`, the process starts where it is told;
* `IsConservative.isTightMeasureSet_continuousProcess`, tightness of the path laws over a compact
  set of starting points;
* `IsConservative.exists_isCompact_measure_compl_le`, the same in epsilon form.

No compactness theorem for measures (Prokhorov's theorem) is proved or used, and no weak
convergence statement is made here.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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

/-- The process starts where it is told: from a starting point of a measurable set `A`, almost
every path has its time-zero value in `A`. -/
theorem IsConservative.measure_eval_zero_notMem_eq_zero (hK : P.KolmogorovRegular hP)
    {A : Set alpha} (hA : MeasurableSet A) {x : alpha} (hx : x ∈ A) :
    continuousProcess P hP x {omega : ContinuousPath alpha | omega 0 ∉ A} = 0 := by
  have hmeas : Measurable fun omega : ContinuousPath alpha ↦ omega (0 : ℝ≥0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) 0
  have hval : (((continuousProcess P hP) x).map fun omega ↦ omega (0 : ℝ≥0)) Aᶜ = 0 := by
    rw [← Kernel.map_apply _ hmeas, IsConservative.continuousProcess_map_eval_zero P hP hK,
      Kernel.id_apply]
    rw [Measure.dirac_apply' _ hA.compl, Set.indicator_of_notMem (by simpa using hx)]
  rwa [Measure.map_apply hmeas hA.compl, Set.preimage_compl] at hval

variable [ProperSpace alpha]





end

end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Weak convergence of Feller processes on path space

`Trajectory/Convergence.lean` proves that strong convergence of the `C₀` semigroups makes the
finite-dimensional distributions of the continuous-path processes converge.  This file upgrades
that to convergence of the whole path laws, provided the approximating semigroups and the limit
semigroup satisfy **one common** intrinsic Kolmogorov moment bound `HasKolmogorovMoments p q M`.

The common moment bound is what makes the family of path laws at a fixed starting point tight:
the scale in the modulus estimate of `Continuity/PathModulus.lean` depends only on the exponents,
the constant and the tolerances, never on the semigroup, so one compact set of paths carries all
but a prescribed mass of every law of the family at once.  On that compact set Stone--Weierstrass
replaces a bounded continuous functional of the path by a bounded cylinder functional
(`Trajectory/CylinderAlgebra.lean`), whose expectations converge by the finite-dimensional
theorem.  Three epsilons finish the argument; no compactness theorem for measures is used.

Main results:

* `isTightMeasureSet_insert_continuousProcess` and
  `exists_isCompact_measure_compl_le_insert`, tightness of the family of path laws at a fixed
  starting point;
* `tendsto_integral_continuousProcess`, convergence of the expectation of every bounded
  continuous functional of the path;
* `tendsto_pathLaw`, the same statement read in the space of probability measures on path space
  with its topology of convergence in distribution, and
  `tendsto_pathLaw_of_tendsto_resolvent`, its form starting from the resolvents.

The state space is assumed proper, as in `Trajectory/PathTightness.lean`, and the moment bound is
assumed with the same exponents and constant for every member of the family; nothing is asserted
when the constants are allowed to vary, nor for a family whose limit is not itself the process of
a Feller semigroup.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal ZeroAtInfty

namespace MarkovProcess


namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [ProperSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}











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
# Weak convergence of Feller processes on path space

`Trajectory/Convergence.lean` proves that strong convergence of the `C₀` semigroups makes the
finite-dimensional distributions of the continuous-path processes converge.  This file upgrades
that to convergence of the whole path laws, provided the approximating semigroups and the limit
semigroup satisfy **one common** intrinsic Kolmogorov moment bound `HasKolmogorovMoments p q M`.

The common moment bound is what makes the family of path laws at a fixed starting point tight:
the scale in the modulus estimate of `Continuity/PathModulus.lean` depends only on the exponents,
the constant and the tolerances, never on the semigroup, so one compact set of paths carries all
but a prescribed mass of every law of the family at once.  On that compact set Stone--Weierstrass
replaces a bounded continuous functional of the path by a bounded cylinder functional
(`Trajectory/CylinderAlgebra.lean`), whose expectations converge by the finite-dimensional
theorem.  Three epsilons finish the argument; no compactness theorem for measures is used.

Main results:

* `isTightMeasureSet_insert_continuousProcess` and
  `exists_isCompact_measure_compl_le_insert`, tightness of the family of path laws at a fixed
  starting point;
* `tendsto_integral_continuousProcess`, convergence of the expectation of every bounded
  continuous functional of the path;
* `tendsto_pathLaw`, the same statement read in the space of probability measures on path space
  with its topology of convergence in distribution, and
  `tendsto_pathLaw_of_tendsto_resolvent`, its form starting from the resolvents.

The state space is assumed proper, as in `Trajectory/PathTightness.lean`, and the moment bound is
assumed with the same exponents and constant for every member of the family; nothing is asserted
when the constants are allowed to vary, nor for a family whose limit is not itself the process of
a Feller semigroup.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal ZeroAtInfty





open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [ProperSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}

namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
theorem solution
    (hPc : ∀ i, (P i).IsConservative) (hQc : Q.IsConservative) {p q : ℝ} {M : ℝ≥0}
    (hPmom : ∀ i, (P i).HasKolmogorovMoments p q M) (hQmom : Q.HasKolmogorovMoments p q M)
    (x : alpha) :
    IsTightMeasureSet (insert (continuousProcess Q hQc x)
      (Set.range fun i ↦ continuousProcess (P i) (hPc i) x)) := by
  refine ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le
    (isCompact_singleton (x := x)) ?_ ?_
  · rintro mu (rfl | ⟨i, rfl⟩)
    · exact IsConservative.measure_eval_zero_notMem_eq_zero Q hQc
        (KolmogorovRegular.of_hasKolmogorovMoments Q hQc hQmom)
        (measurableSet_singleton x) rfl
    · exact IsConservative.measure_eval_zero_notMem_eq_zero (P i) (hPc i)
        (KolmogorovRegular.of_hasKolmogorovMoments (P i) (hPc i) (hPmom i))
        (measurableSet_singleton x) rfl
  · intro T r hr eps heps
    obtain ⟨gamma, hgamma, hgammaq⟩ := hQmom.exists_holderExponent
    obtain ⟨delta, hdelta, hmu⟩ :=
      ContinuousPath.exists_measure_compl_modulusSet_le (alpha := alpha) (M := M)
        hQmom.p_pos hgamma hgammaq T hr heps
    refine ⟨delta, hdelta, ?_⟩
    rintro mu (rfl | ⟨i, rfl⟩)
    · exact hmu _ (IsConservative.isKolmogorovProcess_continuousProcess Q hQc hQmom
        (KolmogorovRegular.of_hasKolmogorovMoments Q hQc hQmom) x)
    · exact hmu _ (IsConservative.isKolmogorovProcess_continuousProcess (P i) (hPc i) (hPmom i)
        (KolmogorovRegular.of_hasKolmogorovMoments (P i) (hPc i) (hPmom i)) x)
