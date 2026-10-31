-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuous_integral_boundedContinuous_finiteSetKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:38:42.268512+00:00
-- url     : https://prove2.me/submissions/ceb0db01-1ea7-4bd7-8c98-c5a6f0454655

import Definitions.Def_MarkovProcess_V3H_Feller_FiniteSetCompactTestContinuity_012434c8
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
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
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_abs_integral_sub_integral_smul_le
import Theorems.Thm_MarkovProcess_exists_compactlySupported_one_sub_lt_integral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measurable and continuous dependence on the starting point

Two regularity statements for the continuous-path process of a conservative sub-Markov kernel
semigroup, both in the starting point.

*Measurability.*  For a strongly measurable functional `F` of the path, the expectation
`x ↦ ∫ F d(continuousProcess P hP x)` is strongly measurable, hence measurable into a Borel
target: `IsConservative.stronglyMeasurable_integral_continuousProcess` and
`IsConservative.measurable_integral_continuousProcess`.  The same holds for the two functionals
that the strong Markov property produces, the shifted path and the state at a finite stopping
time: `IsConservative.measurable_integral_shift_stoppingTime_continuousProcess` and
`IsConservative.measurable_integral_eval_stoppingTime_continuousProcess`.

*Continuity.*  For a Feller semigroup the finite-dimensional laws depend weakly continuously on
the starting point: `IsFellerKernelSemigroup.continuous_integral_boundedContinuous_finiteSetKernel`
upgrades compact-test continuity to all bounded continuous test functions.  The
upgrade is a tightness argument: a finite-dimensional law on a Polish coordinate space is tight,
so a compactly supported continuous cutoff `g` with `1_K ≤ g ≤ 1` captures all but `epsilon` of the
mass at the reference starting point, the truncated integral `∫ f * g` is continuous by the
compact-test theorem, and the discarded part is bounded by `‖f‖ * (1 - ∫ g)`, itself continuous
and small.  On the process this reads as continuity of cylinder expectations,
`IsFellerKernelSemigroup.continuous_integral_finsetEvaluation_continuousProcess`, with the
one-time case `IsFellerKernelSemigroup.continuous_integral_eval_continuousProcess`.

Nothing here asserts weak continuity of the full path law `x ↦ continuousProcess P hP x` on path
space; that needs tightness on path space itself, which is not proved here.  No statement covers
a stopping time that can be infinite.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction CompactlySupported NNReal

namespace MarkovProcess


namespace SubMarkovKernelSemigroup

section BoundedContinuousTest

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [LocallyCompactSpace alpha]



end BoundedContinuousTest

noncomputable section Process

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

section Measurability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



variable [MeasurableSpace E] [BorelSpace E]







end Measurability

section Continuity

variable [LocallyCompactSpace alpha]





end Continuity

end Process

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
# Measurable and continuous dependence on the starting point

Two regularity statements for the continuous-path process of a conservative sub-Markov kernel
semigroup, both in the starting point.

*Measurability.*  For a strongly measurable functional `F` of the path, the expectation
`x ↦ ∫ F d(continuousProcess P hP x)` is strongly measurable, hence measurable into a Borel
target: `IsConservative.stronglyMeasurable_integral_continuousProcess` and
`IsConservative.measurable_integral_continuousProcess`.  The same holds for the two functionals
that the strong Markov property produces, the shifted path and the state at a finite stopping
time: `IsConservative.measurable_integral_shift_stoppingTime_continuousProcess` and
`IsConservative.measurable_integral_eval_stoppingTime_continuousProcess`.

*Continuity.*  For a Feller semigroup the finite-dimensional laws depend weakly continuously on
the starting point: `IsFellerKernelSemigroup.continuous_integral_boundedContinuous_finiteSetKernel`
upgrades compact-test continuity to all bounded continuous test functions.  The
upgrade is a tightness argument: a finite-dimensional law on a Polish coordinate space is tight,
so a compactly supported continuous cutoff `g` with `1_K ≤ g ≤ 1` captures all but `epsilon` of the
mass at the reference starting point, the truncated integral `∫ f * g` is continuous by the
compact-test theorem, and the discarded part is bounded by `‖f‖ * (1 - ∫ g)`, itself continuous
and small.  On the process this reads as continuity of cylinder expectations,
`IsFellerKernelSemigroup.continuous_integral_finsetEvaluation_continuousProcess`, with the
one-time case `IsFellerKernelSemigroup.continuous_integral_eval_continuousProcess`.

Nothing here asserts weak continuity of the full path law `x ↦ continuousProcess P hP x` on path
space; that needs tightness on path space itself, which is not proved here.  No statement covers
a stopping time that can be infinite.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction CompactlySupported NNReal





variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [LocallyCompactSpace alpha]

namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (I : Finset NNReal) (f : (I → alpha) →ᵇ ℝ) :
    Continuous fun x ↦ ∫ path, f path ∂finiteSetKernel P I x := by
  let : IsMarkovKernel (finiteSetKernel P I) := hP.isMarkovKernel_finiteSetKernel P I
  have hcompact : ∀ g : C_c(I → alpha, ℝ),
      Continuous fun x ↦ ∫ path, g path ∂finiteSetKernel P I x :=
    fun g ↦ hFeller.continuous_integral_compactlySupported_finiteSetKernel hP I g
  refine continuous_iff_continuousAt.mpr fun x0 ↦ Metric.tendsto_nhds.mpr fun eps heps ↦ ?_
  have hnorm : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  have hdpos : 0 < eps / (3 * (‖f‖ + 1)) := by positivity
  obtain ⟨g, hg01, hgint⟩ :=
    exists_compactlySupported_one_sub_lt_integral (finiteSetKernel P I x0) hdpos
  have hsmall : ‖f‖ * (eps / (3 * (‖f‖ + 1))) ≤ eps / 3 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
    have hexpand : eps * (3 * (‖f‖ + 1)) - ‖f‖ * eps * 3 = 3 * eps := by ring
    linarith only [hexpand, heps]
  have htrunc : ∀ᶠ x in nhds x0,
      |(∫ path, (f • g) path ∂finiteSetKernel P I x)
        - ∫ path, (f • g) path ∂finiteSetKernel P I x0| < eps / 3 := by
    have h := Metric.tendsto_nhds.mp ((hcompact (f • g)).continuousAt (x := x0)) (eps / 3)
      (by positivity)
    simpa only [Real.dist_eq] using h
  have hmass : ∀ᶠ x in nhds x0,
      1 - (∫ path, g path ∂finiteSetKernel P I x) < eps / (3 * (‖f‖ + 1)) :=
    Tendsto.eventually_lt_const (by simp only [Pi.sub_apply]; linarith only [hgint])
      ((continuous_const.sub (hcompact g)).continuousAt (x := x0))
  filter_upwards [htrunc, hmass] with x hxtrunc hxmass
  rw [Real.dist_eq]
  have hkey := abs_integral_sub_integral_smul_le (finiteSetKernel P I x) f g hg01
  have hkey0 := abs_integral_sub_integral_smul_le (finiteSetKernel P I x0) f g hg01
  have hbound : ‖f‖ * (1 - ∫ path, g path ∂finiteSetKernel P I x)
      ≤ ‖f‖ * (eps / (3 * (‖f‖ + 1))) :=
    mul_le_mul_of_nonneg_left hxmass.le hnorm
  have hbound0 : ‖f‖ * (1 - ∫ path, g path ∂finiteSetKernel P I x0)
      ≤ ‖f‖ * (eps / (3 * (‖f‖ + 1))) :=
    mul_le_mul_of_nonneg_left (by linarith only [hgint]) hnorm
  have htri := abs_sub_le (∫ path, f path ∂finiteSetKernel P I x)
    (∫ path, (f • g) path ∂finiteSetKernel P I x) (∫ path, f path ∂finiteSetKernel P I x0)
  have htri0 := abs_sub_le (∫ path, (f • g) path ∂finiteSetKernel P I x)
    (∫ path, (f • g) path ∂finiteSetKernel P I x0) (∫ path, f path ∂finiteSetKernel P I x0)
  have hcomm := abs_sub_comm (∫ path, (f • g) path ∂finiteSetKernel P I x0)
    (∫ path, f path ∂finiteSetKernel P I x0)
  linarith only [hkey, hkey0, hxtrunc, hbound, hbound0, hsmall, htri, htri0, hcomm]
