-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.ofReal_feynmanKac_eq_feynmanKacENNReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:38:23.941728+00:00
-- url     : https://prove2.me/submissions/954021f5-8155-4e0e-832c-2923f1a36cd4

import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Definitions.Def_MarkovProcess_V3H_Trajectory_DynkinMartingale_970781f3
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacFunctional_cc8a1986
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
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
import Mathlib.Probability.Martingale.Basic
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Feynman--Kac functionals and semigroups

For the continuous-path process of a conservative Feller semigroup, this file constructs the
Feynman--Kac operators associated with a bounded nonnegative measurable potential.  It proves
measurability and bounds for the accumulated potential and operators, the identity at time zero,
and the Feynman--Kac semigroup law.

Main results: `feynmanKacAdditiveFunctional`,
`stronglyMeasurable_feynmanKacAdditiveFunctional`,
`continuous_feynmanKacAdditiveFunctional`, `feynmanKacAdditiveFunctional_add`,
`IsConservative.feynmanKac`, `IsConservative.feynmanKac_zero`,
`IsConservative.measurable_feynmanKac`, `IsConservative.feynmanKac_nonneg`,
`IsConservative.feynmanKac_le`, `IsConservative.feynmanKac_add_apply`,
`IsConservative.feynmanKac_smul_apply`, and `IsFellerKernelSemigroup.feynmanKac_add`.

The resolvent and perturbation identities are developed in `Trajectory/FeynmanKacResolvent.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]



omit [MeasurableSpace alpha] [BorelSpace alpha] in
/-- The accumulated potential is unfolded as its path integral. -/
theorem feynmanKacAdditiveFunctional_apply (q : alpha → ℝ) (t : NNReal)
    (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q t omega =
      ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s)) :=
  rfl

variable [SecondCountableTopology alpha]



/-- The accumulated potential at a deterministic time is strongly measurable on path space. -/
theorem stronglyMeasurable_feynmanKacAdditiveFunctional {q : alpha → ℝ}
    (hq : Measurable q) (t : NNReal) :
    StronglyMeasurable (feynmanKacAdditiveFunctional q t) :=
  (stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration hq t).mono
    ((ContinuousPath.canonicalFiltration (alpha := alpha)).le t)







omit [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] in
/-- The accumulated potential is nonnegative. -/
theorem feynmanKacAdditiveFunctional_nonneg {q : alpha → ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (t : NNReal) (omega : ContinuousPath alpha) :
    0 ≤ feynmanKacAdditiveFunctional q t omega := by
  rw [feynmanKacAdditiveFunctional_apply]
  exact intervalIntegral.integral_nonneg t.coe_nonneg fun s _ ↦ hq0 _











variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac operator is unfolded as a path expectation. -/
theorem IsConservative.feynmanKac_apply (q : alpha → ℝ) (t : NNReal)
    (f : alpha → ℝ) (x : alpha) :
    IsConservative.feynmanKac P hP q t f x =
      ∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
        ∂(IsConservative.continuousProcess P hP x) :=
  rfl













omit [LocallyCompactSpace alpha] in
/-- The extended-real Feynman--Kac operator is unfolded as a path integral. -/
theorem IsConservative.feynmanKacENNReal_apply (q : alpha → ℝ) (t : NNReal)
    (f : alpha → ℝ≥0∞) (x : alpha) :
    IsConservative.feynmanKacENNReal P hP q t f x =
      ∫⁻ omega, ENNReal.ofReal (Real.exp (-feynmanKacAdditiveFunctional q t omega)) *
        f (omega t) ∂(IsConservative.continuousProcess P hP x) :=
  rfl




















end

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Feynman--Kac functionals and semigroups

For the continuous-path process of a conservative Feller semigroup, this file constructs the
Feynman--Kac operators associated with a bounded nonnegative measurable potential.  It proves
measurability and bounds for the accumulated potential and operators, the identity at time zero,
and the Feynman--Kac semigroup law.

Main results: `feynmanKacAdditiveFunctional`,
`stronglyMeasurable_feynmanKacAdditiveFunctional`,
`continuous_feynmanKacAdditiveFunctional`, `feynmanKacAdditiveFunctional_add`,
`IsConservative.feynmanKac`, `IsConservative.feynmanKac_zero`,
`IsConservative.measurable_feynmanKac`, `IsConservative.feynmanKac_nonneg`,
`IsConservative.feynmanKac_le`, `IsConservative.feynmanKac_add_apply`,
`IsConservative.feynmanKac_smul_apply`, and `IsFellerKernelSemigroup.feynmanKac_add`.

The resolvent and perturbation identities are developed in `Trajectory/FeynmanKacResolvent.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]





variable [SecondCountableTopology alpha]























variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)























namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative
end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
omit [LocallyCompactSpace alpha] in

theorem solution {q : alpha → ℝ}
    (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) (t : NNReal) {f : alpha → ℝ} (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) {D : ℝ} (hfD : ∀ y, f y ≤ D) (x : alpha) :
    ENNReal.ofReal (IsConservative.feynmanKac P hP q t f x) =
      IsConservative.feynmanKacENNReal P hP q t (fun y ↦ ENNReal.ofReal (f y)) x := by
  let g : ContinuousPath alpha → ℝ := fun omega ↦
    Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
  have hg : Integrable g (IsConservative.continuousProcess P hP x) := by
    refine Integrable.of_bound ?_ D (Eventually.of_forall fun omega ↦ ?_)
    · exact ((((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
        (hf.comp (ContinuousPath.measurable_coordinateProcess
          (alpha := alpha) t))).stronglyMeasurable
          ).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hf0 _))]
      exact (mul_le_mul_of_nonneg_right
        ((Real.exp_le_one_iff).mpr
          (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega))) (hf0 _)).trans
        (by simpa only [one_mul] using hfD _)
  rw [IsConservative.feynmanKac_apply, IsConservative.feynmanKacENNReal_apply,
    ofReal_integral_eq_lintegral_ofReal hg
      (Eventually.of_forall fun omega ↦ mul_nonneg (Real.exp_pos _).le (hf0 _))]
  refine lintegral_congr fun omega ↦ ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
