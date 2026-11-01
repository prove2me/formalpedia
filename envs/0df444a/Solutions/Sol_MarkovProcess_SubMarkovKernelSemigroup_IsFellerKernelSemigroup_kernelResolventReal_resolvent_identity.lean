-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.kernelResolventReal_resolvent_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:24:47.895371+00:00
-- url     : https://prove2.me/submissions/4e60dd06-18f5-4b38-99a1-0913a3c7eef5

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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_feynmanKacResolventReal_resolvent_identity
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_integral_eval_continuousProcess_of_measurable

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
/-- The Feynman--Kac operator is unfolded as a path expectation. -/
theorem IsConservative.feynmanKac_apply (q : alpha → ℝ) (t : NNReal)
    (f : alpha → ℝ) (x : alpha) :
    IsConservative.feynmanKac P hP q t f x =
      ∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
        ∂(IsConservative.continuousProcess P hP x) :=
  rfl


































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
/-- The real Feynman--Kac resolvent of a bounded measurable observable is measurable in the
starting point. -/
theorem IsConservative.measurable_feynmanKacResolventReal {q : alpha → ℝ}
    (hq : Measurable q) (lam : ℝ) {f : alpha → ℝ} (hf : Measurable f) :
    Measurable (IsConservative.feynmanKacResolventReal P hP q lam f) := by
  have hjoint : StronglyMeasurable fun p : ℝ × alpha ↦
      Real.exp (-lam * p.1) *
        IsConservative.feynmanKac P hP q (Real.toNNReal p.1) f p.2 :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
      measurable_fst).mul
      ((IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
      ) |>.stronglyMeasurable
  exact (hjoint.integral_prod_left' (μ := volume.restrict (Ioi 0))).measurable









/-- With zero potential, the real Feynman--Kac resolvent is the real kernel resolvent. -/
theorem IsFellerKernelSemigroup.feynmanKacResolventReal_zero_eq_kernelResolventReal
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (lam : ℝ) {f : alpha → ℝ} (hf : Measurable f) :
    IsConservative.feynmanKacResolventReal P hP (fun _ ↦ 0) lam f =
      P.kernelResolventReal lam f := by
  funext x
  unfold IsConservative.feynmanKacResolventReal SubMarkovKernelSemigroup.kernelResolventReal
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  have heval := hFeller.integral_eval_continuousProcess_of_measurable
    P hP hK (Real.toNNReal t) x hf
  simp only [IsConservative.feynmanKac_apply, feynmanKacAdditiveFunctional,
    intervalIntegral.integral_zero, neg_zero, Real.exp_zero, one_mul]
  rw [heval]
  rfl

/-- The real kernel resolvent of a bounded measurable observable is measurable. -/
theorem IsFellerKernelSemigroup.measurable_kernelResolventReal
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (lam : ℝ) {f : alpha → ℝ} (hf : Measurable f) :
    Measurable (P.kernelResolventReal lam f) := by
  rw [← hFeller.feynmanKacResolventReal_zero_eq_kernelResolventReal P hP hK lam hf]
  exact IsConservative.measurable_feynmanKacResolventReal P hP measurable_const lam hf













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

























namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {mu lam : ℝ} (hmu : 0 < mu) (hlam : 0 < lam) {f : alpha → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    P.kernelResolventReal mu f = P.kernelResolventReal lam f +
      (lam - mu) • P.kernelResolventReal lam (P.kernelResolventReal mu f) := by
  have hmuEq := hFeller.feynmanKacResolventReal_zero_eq_kernelResolventReal
    P hP hK mu hf
  have hlamEq := hFeller.feynmanKacResolventReal_zero_eq_kernelResolventReal
    P hP hK lam hf
  have hRmeas := hFeller.measurable_kernelResolventReal P hP hK mu hf
  have hcompEq := hFeller.feynmanKacResolventReal_zero_eq_kernelResolventReal
    P hP hK lam hRmeas
  calc
    P.kernelResolventReal mu f =
        IsConservative.feynmanKacResolventReal P hP (fun _ ↦ 0) mu f := hmuEq.symm
    _ = IsConservative.feynmanKacResolventReal P hP (fun _ ↦ 0) lam f +
        (lam - mu) • IsConservative.feynmanKacResolventReal P hP (fun _ ↦ 0) lam
          (IsConservative.feynmanKacResolventReal P hP (fun _ ↦ 0) mu f) :=
      hFeller.feynmanKacResolventReal_resolvent_identity P hP hK measurable_const
        (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) hmu hlam hf hfD
    _ = P.kernelResolventReal lam f +
        (lam - mu) • P.kernelResolventReal lam (P.kernelResolventReal mu f) := by
      rw [hlamEq, hmuEq, hcompEq]
