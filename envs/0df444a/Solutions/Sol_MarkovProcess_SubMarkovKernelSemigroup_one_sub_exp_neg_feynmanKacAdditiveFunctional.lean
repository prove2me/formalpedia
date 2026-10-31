-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.one_sub_exp_neg_feynmanKacAdditiveFunctional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:39:33.45499+00:00
-- url     : https://prove2.me/submissions/6f9ba1f8-499b-4b09-a98f-8799c1674288

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
import Theorems.Thm_intervalIntegral_integral_mul_exp_primitive

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







omit [SecondCountableTopology alpha] in
/-- A bounded measurable potential is interval integrable along every continuous path. -/
private theorem intervalIntegrable_potential_path {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (omega : ContinuousPath alpha) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ q (omega (Real.toNNReal s))) volume a b := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (by simpa only [uIoc] using
      (measure_Ioc_lt_top : volume (Ioc (min a b) (max a b)) < ∞))
    (((hq.comp (omega.continuous.measurable.comp measurable_real_toNNReal)).stronglyMeasurable
      ).aestronglyMeasurable.restrict) C ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s _
  rw [Real.norm_eq_abs, abs_of_nonneg (hq0 _)]
  exact hqC _















variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)






































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





















namespace MarkovProcess.SubMarkovKernelSemigroup
end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
omit [SecondCountableTopology alpha] in

theorem solution {q : alpha → ℝ}
    (hq : Measurable q) {C : ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (hqC : ∀ y, q y ≤ C) (t : NNReal) (omega : ContinuousPath alpha) :
    1 - Real.exp (-feynmanKacAdditiveFunctional q t omega) =
      ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s)) *
        Real.exp (-(feynmanKacAdditiveFunctional q t omega -
          feynmanKacAdditiveFunctional q (Real.toNNReal s) omega)) := by
  let a : ℝ → ℝ := fun s ↦ q (omega (Real.toNNReal s))
  have ha : IntegrableOn a (Icc (0 : ℝ) (t : ℝ)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mp
      (intervalIntegrable_potential_path hq hq0 hqC omega 0 t)
  have hprimitive := intervalIntegral.integral_mul_exp_primitive
    (right_mem_Icc.mpr t.coe_nonneg) ha
    (fun s _ ↦ hq0 _) (fun s _ ↦ hqC _)
  have hscaled := congrArg (fun z : ℝ ↦ Real.exp
      (-feynmanKacAdditiveFunctional q t omega) * z) hprimitive
  change Real.exp (-feynmanKacAdditiveFunctional q t omega) *
      (∫ s in (0 : ℝ)..t, a s * Real.exp (∫ r in (0 : ℝ)..s, a r)) =
    Real.exp (-feynmanKacAdditiveFunctional q t omega) *
      (Real.exp (∫ r in (0 : ℝ)..t, a r) - 1) at hscaled
  rw [← intervalIntegral.integral_const_mul] at hscaled
  simp only [a, ← feynmanKacAdditiveFunctional_apply] at hscaled
  calc
    1 - Real.exp (-feynmanKacAdditiveFunctional q t omega) =
        Real.exp (-feynmanKacAdditiveFunctional q t omega) *
          (Real.exp (feynmanKacAdditiveFunctional q t omega) - 1) := by
            rw [mul_sub, ← Real.exp_add]
            simp only [neg_add_cancel, Real.exp_zero, mul_one]
    _ = ∫ s in (0 : ℝ)..t, Real.exp (-feynmanKacAdditiveFunctional q t omega) *
          (q (omega (Real.toNNReal s)) *
            Real.exp (∫ r in (0 : ℝ)..s, q (omega (Real.toNNReal r)))) := hscaled.symm
    _ = ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s)) *
          Real.exp (-(feynmanKacAdditiveFunctional q t omega -
            feynmanKacAdditiveFunctional q (Real.toNNReal s) omega)) := by
            refine intervalIntegral.integral_congr fun s hs ↦ ?_
            have hs0 : 0 ≤ s := by
              rw [uIcc_of_le t.coe_nonneg] at hs
              exact hs.1
            have hAs : feynmanKacAdditiveFunctional q (Real.toNNReal s) omega =
                ∫ r in (0 : ℝ)..s, q (omega (Real.toNNReal r)) := by
              rw [feynmanKacAdditiveFunctional_apply, Real.coe_toNNReal s hs0]
            rw [hAs]
            rw [neg_sub, Real.exp_sub, Real.exp_neg]
            field_simp [Real.exp_ne_zero]
