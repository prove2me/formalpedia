-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.feynmanKacResolventReal_resolvent_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:15:24.736375+00:00
-- url     : https://prove2.me/submissions/157cfe95-7d45-4b0f-beac-d665d04377cf

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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_feynmanKac_add
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration
import Theorems.Thm_intervalIntegral_integral_timeTriangle_sub

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















private theorem IsFellerKernelSemigroup.feynmanKac_comp_feynmanKacResolventReal
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C) {mu : ℝ} (hmu : 0 < mu)
    (s : NNReal) {f : alpha → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    IsConservative.feynmanKac P hP q s
        (IsConservative.feynmanKacResolventReal P hP q mu f) x =
      ∫ t in Ioi (0 : ℝ), Real.exp (-mu * t) *
        IsConservative.feynmanKac P hP q (s + Real.toNNReal t) f x := by
  let Qx : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  let H : ContinuousPath alpha × ℝ → ℝ := fun p ↦
    Real.exp (-feynmanKacAdditiveFunctional q s p.1) * Real.exp (-mu * p.2) *
      IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f (p.1 s)
  have hHmeas : StronglyMeasurable H := by
    have hstart : Measurable fun p : ContinuousPath alpha × ℝ ↦ p.1 s :=
      (ContinuousPath.measurable_coordinateProcess (alpha := alpha) s).comp measurable_fst
    have htime : Measurable fun p : ContinuousPath alpha × ℝ ↦ Real.toNNReal p.2 :=
      measurable_real_toNNReal.comp measurable_snd
    have hW : Measurable fun p : ContinuousPath alpha × ℝ ↦
        Real.exp (-feynmanKacAdditiveFunctional q s p.1) :=
      (stronglyMeasurable_feynmanKacAdditiveFunctional hq s).measurable.neg.exp.comp
        measurable_fst
    have hE : Measurable fun p : ContinuousPath alpha × ℝ ↦ Real.exp (-mu * p.2) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_snd
    have hFK : Measurable fun p : ContinuousPath alpha × ℝ ↦
        IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f (p.1 s) :=
      (IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
        (htime.prodMk hstart)
    exact ((hW.mul hE).mul hFK).stronglyMeasurable
  have htimeInt : IntegrableOn (fun t : ℝ ↦ Real.exp (-mu * t) * D) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hmu).mul_const D
  have hdom : Integrable (fun p : ContinuousPath alpha × ℝ ↦
      (1 : ℝ) * (Real.exp (-mu * p.2) * D))
      (Qx.prod (volume.restrict (Ioi 0))) :=
    (integrable_const (μ := Qx) (1 : ℝ)).mul_prod htimeInt
  have hHint : Integrable H (Qx.prod (volume.restrict (Ioi 0))) := by
    apply Integrable.mono' hdom hHmeas.aestronglyMeasurable
    exact Eventually.of_forall fun p ↦ by
      dsimp only [H]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.exp_pos _), one_mul]
      calc
        Real.exp (-feynmanKacAdditiveFunctional q s p.1) *
            Real.exp (-mu * p.2) *
              |IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f (p.1 s)| ≤
            1 * Real.exp (-mu * p.2) * D := by
          calc
            Real.exp (-feynmanKacAdditiveFunctional q s p.1) *
                Real.exp (-mu * p.2) *
                  |IsConservative.feynmanKac P hP q
                    (Real.toNNReal p.2) f (p.1 s)| ≤
                (1 * Real.exp (-mu * p.2)) *
                  |IsConservative.feynmanKac P hP q
                    (Real.toNNReal p.2) f (p.1 s)| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  ((Real.exp_le_one_iff).mpr
                    (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 s p.1)))
                  (Real.exp_pos _).le) (abs_nonneg _)
            _ ≤ (1 * Real.exp (-mu * p.2)) * D :=
              mul_le_mul_of_nonneg_left
                (IsConservative.norm_feynmanKac_le P hP hq0
                  (Real.toNNReal p.2) hfD (p.1 s))
                (mul_nonneg zero_le_one (Real.exp_pos _).le)
        _ = Real.exp (-mu * p.2) * D := by ring
  rw [IsConservative.feynmanKac_apply]
  unfold IsConservative.feynmanKacResolventReal
  change (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q s omega) *
      (∫ t in Ioi (0 : ℝ), Real.exp (-mu * t) *
        IsConservative.feynmanKac P hP q (Real.toNNReal t) f (omega s)) ∂Qx) = _
  calc
    (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q s omega) *
        (∫ t in Ioi (0 : ℝ), Real.exp (-mu * t) *
          IsConservative.feynmanKac P hP q (Real.toNNReal t) f (omega s)) ∂Qx) =
        ∫ omega, (∫ t in Ioi (0 : ℝ), H (omega, t)) ∂Qx := by
      apply integral_congr_ae
      exact Eventually.of_forall fun omega ↦ by
        dsimp only
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _ht
        dsimp only [H]
        ring
    _ = ∫ t in Ioi (0 : ℝ), ∫ omega, H (omega, t) ∂Qx :=
      integral_integral_swap hHint
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _ht
      dsimp only [H]
      calc
        (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q s omega) *
            Real.exp (-mu * t) *
              IsConservative.feynmanKac P hP q (Real.toNNReal t) f (omega s) ∂Qx) =
            ∫ omega, Real.exp (-mu * t) *
              (Real.exp (-feynmanKacAdditiveFunctional q s omega) *
                IsConservative.feynmanKac P hP q (Real.toNNReal t) f (omega s)) ∂Qx := by
          apply integral_congr_ae
          exact Eventually.of_forall fun omega ↦ by ring
        _ = Real.exp (-mu * t) *
            ∫ omega, Real.exp (-feynmanKacAdditiveFunctional q s omega) *
              IsConservative.feynmanKac P hP q (Real.toNNReal t) f (omega s) ∂Qx := by
          rw [integral_const_mul]
        _ = Real.exp (-mu * t) *
            IsConservative.feynmanKac P hP q (s + Real.toNNReal t) f x := by
          rw [← IsConservative.feynmanKac_apply]
          rw [← hFeller.feynmanKac_add P hP hK hq hq0 hqC s
            (Real.toNNReal t) hf hfD x]

private theorem exp_sub_mul_integral_exp_mul_exp_sub (lam mu u : ℝ) (hu : 0 ≤ u) :
    (lam - mu) * (∫ s in Ioo (0 : ℝ) u,
      Real.exp (-lam * s) * Real.exp (-mu * (u - s))) =
      Real.exp (-mu * u) - Real.exp (-lam * u) := by
  let phi : ℝ → ℝ := fun s ↦
    Real.exp (-lam * s) * Real.exp (-mu * (u - s))
  have hderiv (s : ℝ) : HasDerivAt phi ((mu - lam) * phi s) s := by
    dsimp only [phi]
    have hd := (((hasDerivAt_const s (-lam)).mul (hasDerivAt_id s)).exp.mul
      ((hasDerivAt_const s (-mu)).mul
        ((hasDerivAt_const s u).sub (hasDerivAt_id s))).exp)
    convert hd using 1
    all_goals first
      | rfl
      | (simp only [Pi.mul_apply, Pi.sub_apply, id_eq]; ring)
  have hint : IntervalIntegrable (fun s ↦ (mu - lam) * phi s) volume 0 u :=
    (continuous_const.mul
      (continuous_iff_continuousAt.mpr fun s ↦ (hderiv s).continuousAt)).intervalIntegrable 0 u
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _hs ↦ hderiv s) hint
  rw [intervalIntegral.integral_of_le hu, integral_Ioc_eq_integral_Ioo,
    MeasureTheory.integral_const_mul] at hFTC
  dsimp only [phi] at hFTC ⊢
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one, sub_zero, one_mul] at hFTC
  linarith only [hFTC]









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
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {mu lam : ℝ} (hmu : 0 < mu) (hlam : 0 < lam) {f : alpha → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    IsConservative.feynmanKacResolventReal P hP q mu f =
      IsConservative.feynmanKacResolventReal P hP q lam f +
        (lam - mu) • IsConservative.feynmanKacResolventReal P hP q lam
          (IsConservative.feynmanKacResolventReal P hP q mu f) := by
  funext x
  let H : ℝ × ℝ → ℝ := fun p ↦
    Real.exp (-lam * p.1) * Real.exp (-mu * p.2) *
      IsConservative.feynmanKac P hP q
        (Real.toNNReal p.1 + Real.toNNReal p.2) f x
  let K : ℝ → ℝ := fun u ↦ ∫ s in Ioo (0 : ℝ) u, H (s, u - s)
  have hHmeas : Measurable H := by
    exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
      measurable_fst).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_snd)).mul
      ((IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
        (((measurable_real_toNNReal.comp measurable_fst).add
          (measurable_real_toNNReal.comp measurable_snd)).prodMk measurable_const))
  have hQ : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hHquad : Integrable H
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hbase := (exp_neg_integrableOn_Ioi 0 hlam).mul_prod
      ((exp_neg_integrableOn_Ioi 0 hmu).mul_const D)
    apply Integrable.mono' hbase hHmeas.aestronglyMeasurable
    exact Eventually.of_forall fun p ↦ by
      dsimp only [H]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (IsConservative.norm_feynmanKac_le P hP hq0
          (Real.toNNReal p.1 + Real.toNNReal p.2) hfD x)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) |>.trans_eq (by ring)
  have hHind : Integrable ((Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator H)
      (volume.prod volume) := by
    apply (integrable_indicator_iff hQ).2
    change Integrable H ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
    rw [← Measure.prod_restrict]
    exact hHquad
  have htriangle := intervalIntegral.integral_timeTriangle_sub hHmeas hHind
  have hmuInt := IsConservative.integrableOn_feynmanKacResolventReal_integrand
    P hP hq hq0 hmu hf hfD x
  have hlamInt := IsConservative.integrableOn_feynmanKacResolventReal_integrand
    P hP hq hq0 hlam hf hfD x
  have hpoint (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) :
      Real.exp (-mu * u) * IsConservative.feynmanKac P hP q (Real.toNNReal u) f x =
        Real.exp (-lam * u) * IsConservative.feynmanKac P hP q (Real.toNNReal u) f x +
          (lam - mu) * K u := by
    have hK : K u = (∫ s in Ioo (0 : ℝ) u,
        Real.exp (-lam * s) * Real.exp (-mu * (u - s))) *
          IsConservative.feynmanKac P hP q (Real.toNNReal u) f x := by
      dsimp only [K]
      rw [← MeasureTheory.integral_mul_const]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      dsimp only [H]
      have hs0 : 0 ≤ s := hs.1.le
      have hus0 : 0 ≤ u - s := sub_nonneg.mpr hs.2.le
      have htime : Real.toNNReal s + Real.toNNReal (u - s) = Real.toNNReal u := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add, Real.coe_toNNReal s hs0, Real.coe_toNNReal (u - s) hus0,
          Real.coe_toNNReal u hu.le]
        ring
      rw [htime]
    rw [hK]
    have hexp := exp_sub_mul_integral_exp_mul_exp_sub lam mu u hu.le
    calc
      Real.exp (-mu * u) * IsConservative.feynmanKac P hP q (Real.toNNReal u) f x =
          (Real.exp (-lam * u) +
            (lam - mu) * (∫ s in Ioo (0 : ℝ) u,
              Real.exp (-lam * s) * Real.exp (-mu * (u - s)))) *
            IsConservative.feynmanKac P hP q (Real.toNNReal u) f x := by
        rw [hexp]
        ring
      _ = _ := by ring
  have hsecond : IntegrableOn (fun u ↦ (lam - mu) * K u) (Ioi (0 : ℝ)) := by
    apply (hmuInt.sub hlamInt).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change Real.exp (-mu * u) * IsConservative.feynmanKac P hP q (Real.toNNReal u) f x -
      Real.exp (-lam * u) * IsConservative.feynmanKac P hP q (Real.toNNReal u) f x =
        (lam - mu) * K u
    linarith only [hpoint u hu]
  have hcomp : IsConservative.feynmanKacResolventReal P hP q lam
      (IsConservative.feynmanKacResolventReal P hP q mu f) x =
      ∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), H (s, t) := by
    change (∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) *
      IsConservative.feynmanKac P hP q (Real.toNNReal s)
        (IsConservative.feynmanKacResolventReal P hP q mu f) x) = _
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _hs
    dsimp only
    rw [hFeller.feynmanKac_comp_feynmanKacResolventReal
      P hP hK hq hq0 hqC hmu (Real.toNNReal s) hf hfD x]
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _ht
    dsimp only [H]
    ring
  have htriangle' : (∫ u in Ioi (0 : ℝ), K u) =
      ∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), H (s, t) := by
    simpa only [K] using htriangle
  change (∫ u in Ioi (0 : ℝ), Real.exp (-mu * u) *
      IsConservative.feynmanKac P hP q (Real.toNNReal u) f x) =
    (∫ u in Ioi (0 : ℝ), Real.exp (-lam * u) *
      IsConservative.feynmanKac P hP q (Real.toNNReal u) f x) +
      (lam - mu) * IsConservative.feynmanKacResolventReal P hP q lam
        (IsConservative.feynmanKacResolventReal P hP q mu f) x
  rw [hcomp, ← htriangle', ← MeasureTheory.integral_const_mul,
    ← integral_add hlamInt hsecond]
  apply setIntegral_congr_fun measurableSet_Ioi
  exact hpoint
