-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.ofReal_feynmanKacResolventReal_eq_feynmanKacResolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:53:04.694996+00:00
-- url     : https://prove2.me/submissions/79c8f50a-8d54-4518-bba9-5bc75cf20da6

import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacRealResolvent_20f8c260
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacResolvent_ed9736ae
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Exp
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
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
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
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_measurable_feynmanKac_joint
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_norm_feynmanKac_le
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_ofReal_feynmanKac_eq_feynmanKacENNReal

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





variable [SecondCountableTopology alpha]























variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)









omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac operator preserves nonnegativity. -/
theorem IsConservative.feynmanKac_nonneg {q : alpha → ℝ} {t : NNReal}
    {f : alpha → ℝ} (hf0 : ∀ y, 0 ≤ f y) (x : alpha) :
    0 ≤ IsConservative.feynmanKac P hP q t f x := by
  exact integral_nonneg fun omega ↦ mul_nonneg (Real.exp_pos _).le (hf0 _)




























end

end MarkovProcess.SubMarkovKernelSemigroup


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Real Feynman--Kac resolvents

This file defines the real Feynman--Kac resolvent on bounded measurable observables.  It proves
its uniform bound, linearity, the resolvent identity, and the bounded-potential perturbation
identity.

Main results: `IsConservative.feynmanKacResolventReal`,
`IsFellerKernelSemigroup.feynmanKacResolventReal_resolvent_identity`, and
`IsFellerKernelSemigroup.feynmanKacResolventReal_perturbation`.

Together with `perturbed_eq_of_resolventFamilies`, these identities characterize the
Feynman--Kac resolvent among bounded measurable resolvent families solving the same perturbation
equation at all sufficiently large shifts.  No model-specific realization is assumed.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



omit [LocallyCompactSpace alpha] in
private theorem IsConservative.integrableOn_feynmanKacResolventReal_integrand
    {q : alpha → ℝ} (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) {lam : ℝ} (hlam : 0 < lam)
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) f x) (Ioi 0) := by
  apply Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
  · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
      ((IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
        (measurable_real_toNNReal.prodMk measurable_const))).stronglyMeasurable
      ).aestronglyMeasurable.restrict
  · exact Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (IsConservative.norm_feynmanKac_le P hP hq0 (Real.toNNReal t) hfD x)
        (Real.exp_pos _).le



























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
# Real Feynman--Kac resolvents

This file defines the real Feynman--Kac resolvent on bounded measurable observables.  It proves
its uniform bound, linearity, the resolvent identity, and the bounded-potential perturbation
identity.

Main results: `IsConservative.feynmanKacResolventReal`,
`IsFellerKernelSemigroup.feynmanKacResolventReal_resolvent_identity`, and
`IsFellerKernelSemigroup.feynmanKacResolventReal_perturbation`.

Together with `perturbed_eq_of_resolventFamilies`, these identities characterize the
Feynman--Kac resolvent among bounded measurable resolvent families solving the same perturbation
equation at all sufficiently large shifts.  No model-specific realization is assumed.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)













namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative
end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
omit [LocallyCompactSpace alpha] in

theorem solution
    {q : alpha → ℝ} (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    ENNReal.ofReal (IsConservative.feynmanKacResolventReal P hP q lam f x) =
      IsConservative.feynmanKacResolvent P hP q lam
        (fun y ↦ ENNReal.ofReal (f y)) x := by
  have hint := IsConservative.integrableOn_feynmanKacResolventReal_integrand
    P hP hq hq0 hlam hf hfD x
  rw [IsConservative.feynmanKacResolventReal,
    ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun t ↦ mul_nonneg (Real.exp_pos _).le
        (IsConservative.feynmanKac_nonneg P hP hf0 x))]
  unfold IsConservative.feynmanKacResolvent
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  dsimp only
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
    IsConservative.ofReal_feynmanKac_eq_feynmanKacENNReal P hP hq hq0
      (Real.toNNReal t) hf hf0 (fun y ↦ (le_abs_self (f y)).trans (hfD y)) x]
