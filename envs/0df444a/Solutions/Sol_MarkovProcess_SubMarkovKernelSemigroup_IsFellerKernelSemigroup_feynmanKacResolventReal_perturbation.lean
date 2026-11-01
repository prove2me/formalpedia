-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.feynmanKacResolventReal_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:15:21.299656+00:00
-- url     : https://prove2.me/submissions/7884df4b-c6ae-4055-bb25-0677b534027f

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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_integral_eval_continuousProcess_of_measurable
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_integral_sub_feynmanKac_eq_integral_of_norm_le
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























omit [LocallyCompactSpace alpha] in
private theorem IsConservative.kernelIntegral_mul_feynmanKacResolventReal
    {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {lam : ℝ} (hlam : 0 < lam) (s : NNReal) {f : alpha → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    kernelIntegral (P s)
        (fun y ↦ q y * IsConservative.feynmanKacResolventReal P hP q lam f y) x =
      ∫ u in Ioi (0 : ℝ), Real.exp (-lam * u) *
        kernelIntegral (P s)
          (fun y ↦ q y * IsConservative.feynmanKac P hP q (Real.toNNReal u) f y) x := by
  let H : alpha × ℝ → ℝ := fun p ↦
    q p.1 * Real.exp (-lam * p.2) *
      IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f p.1
  have hHmeas : StronglyMeasurable H := by
    exact (((hq.comp measurable_fst).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_snd)).mul
      ((IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
        ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
      )).stronglyMeasurable
  let : IsFiniteKernel (P s) := (P.isSubMarkovKernel s).isFiniteKernel
  have hC0 : 0 ≤ C := (hq0 x).trans (hqC x)
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hbase : Integrable (fun p : alpha × ℝ ↦
      C * (Real.exp (-lam * p.2) * D))
      ((P s x).prod (volume.restrict (Ioi 0))) :=
    (integrable_const (C : ℝ)).mul_prod ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
  have hHint : Integrable H ((P s x).prod (volume.restrict (Ioi 0))) := by
    apply Integrable.mono' hbase hHmeas.aestronglyMeasurable
    exact Eventually.of_forall fun p ↦ by
      dsimp only [H]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hq0 p.1),
        abs_of_pos (Real.exp_pos _)]
      calc
        q p.1 * Real.exp (-lam * p.2) *
            |IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f p.1| ≤
            C * Real.exp (-lam * p.2) * D := by
          exact mul_le_mul
            (mul_le_mul (hqC p.1) le_rfl (Real.exp_pos _).le hC0)
            (IsConservative.norm_feynmanKac_le P hP hq0
              (Real.toNNReal p.2) hfD p.1) (abs_nonneg _)
            (mul_nonneg hC0 (Real.exp_pos _).le)
        _ = C * (Real.exp (-lam * p.2) * D) := by ring
  unfold IsConservative.feynmanKacResolventReal
  change (∫ y, q y * (∫ u in Ioi (0 : ℝ), Real.exp (-lam * u) *
      IsConservative.feynmanKac P hP q (Real.toNNReal u) f y) ∂(P s x)) = _
  calc
    (∫ y, q y * (∫ u in Ioi (0 : ℝ), Real.exp (-lam * u) *
        IsConservative.feynmanKac P hP q (Real.toNNReal u) f y) ∂(P s x)) =
        ∫ y, (∫ u in Ioi (0 : ℝ), H (y, u)) ∂(P s x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y ↦ by
        dsimp only
        rw [← MeasureTheory.integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _hu
        dsimp only [H]
        ring
    _ = ∫ u in Ioi (0 : ℝ), ∫ y, H (y, u) ∂(P s x) :=
      integral_integral_swap hHint
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _hu
      dsimp only [H]
      calc
        (∫ y, q y * Real.exp (-lam * u) *
            IsConservative.feynmanKac P hP q (Real.toNNReal u) f y ∂(P s x)) =
            ∫ y, Real.exp (-lam * u) *
              (q y * IsConservative.feynmanKac P hP q (Real.toNNReal u) f y)
              ∂(P s x) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun y ↦ by ring
        _ = Real.exp (-lam * u) *
            ∫ y, q y * IsConservative.feynmanKac P hP q (Real.toNNReal u) f y
              ∂(P s x) := MeasureTheory.integral_const_mul _ _



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
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    IsConservative.feynmanKacResolventReal P hP q lam f =
      P.kernelResolventReal lam f - P.kernelResolventReal lam
        (fun y ↦ q y * IsConservative.feynmanKacResolventReal P hP q lam f y) := by
  funext x
  let H : ℝ × ℝ → ℝ := fun p ↦
    Real.exp (-lam * (p.1 + p.2)) *
      kernelIntegral (P (Real.toNNReal p.1))
        (fun y ↦ q y * IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f y) x
  have hHmeas : Measurable H := by
    have hintegrand : Measurable fun p : (ℝ × ℝ) × alpha ↦
        q p.2 * IsConservative.feynmanKac P hP q (Real.toNNReal p.1.2) f p.2 :=
      (hq.comp measurable_snd).mul
        ((IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
          (((measurable_real_toNNReal.comp measurable_snd).comp measurable_fst).prodMk
            measurable_snd))
    let K : Kernel (ℝ × ℝ) alpha :=
      { toFun := fun p ↦ P (Real.toNNReal p.1) x
        measurable' := P.measurable_toMeasure.comp
          ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_const) }
    let : IsFiniteKernel K :=
      { exists_univ_le := ⟨1, ENNReal.one_lt_top, fun p ↦ P.measure_univ_le_one _ _⟩ }
    have hkernel : Measurable fun p : ℝ × ℝ ↦
        kernelIntegral (P (Real.toNNReal p.1))
          (fun y ↦ q y * IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f y) x := by
      have hlin := hintegrand.stronglyMeasurable.integral_kernel_prod_right' (κ := K)
      simpa only [K, kernelIntegral] using! hlin.measurable
    exact ((Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.add continuous_snd))).measurable.mul hkernel)
  have hC0 : 0 ≤ C := (hq0 x).trans (hqC x)
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hinnerBound (s u : ℝ) :
      |kernelIntegral (P (Real.toNNReal s))
        (fun y ↦ q y * IsConservative.feynmanKac P hP q (Real.toNNReal u) f y) x| ≤
          C * D := by
    rw [← Real.norm_eq_abs]
    let : IsFiniteKernel (P (Real.toNNReal s)) :=
      (P.isSubMarkovKernel (Real.toNNReal s)).isFiniteKernel
    calc
      ‖kernelIntegral (P (Real.toNNReal s))
          (fun y ↦ q y * IsConservative.feynmanKac P hP q (Real.toNNReal u) f y) x‖ ≤
          ∫ _y, C * D ∂(P (Real.toNNReal s) x) := by
        apply norm_integral_le_of_norm_le (integrable_const (C * D))
        exact Eventually.of_forall fun y ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 y)]
          exact mul_le_mul (hqC y)
            (IsConservative.norm_feynmanKac_le P hP hq0 (Real.toNNReal u) hfD y)
            (abs_nonneg _) hC0
      _ ≤ C * D := by
        rw [integral_const, smul_eq_mul]
        apply mul_le_of_le_one_left (mul_nonneg hC0 hD0)
        rw [measureReal_def, ← ENNReal.toReal_one]
        apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
        exact (P.isSubMarkovKernel (Real.toNNReal s)).measure_le_one x Set.univ
  have hQ : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hHquad : Integrable H
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hbase := (exp_neg_integrableOn_Ioi 0 hlam).mul_prod
      ((exp_neg_integrableOn_Ioi 0 hlam).mul_const (C * D))
    apply Integrable.mono' hbase hHmeas.stronglyMeasurable.aestronglyMeasurable
    exact Eventually.of_forall fun p ↦ by
      dsimp only [H]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-lam * (p.1 + p.2)) *
            |kernelIntegral (P (Real.toNNReal p.1))
              (fun y ↦ q y * IsConservative.feynmanKac P hP q
                (Real.toNNReal p.2) f y) x| ≤
            Real.exp (-lam * (p.1 + p.2)) * (C * D) :=
          mul_le_mul_of_nonneg_left (hinnerBound p.1 p.2) (Real.exp_pos _).le
        _ = Real.exp (-lam * p.1) * (Real.exp (-lam * p.2) * (C * D)) := by
          rw [show -lam * (p.1 + p.2) = -lam * p.1 + -lam * p.2 by ring,
            Real.exp_add]
          ring
  have hHind : Integrable ((Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator H)
      (volume.prod volume) := by
    apply (integrable_indicator_iff hQ).2
    change Integrable H ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
    rw [← Measure.prod_restrict]
    exact hHquad
  have htriangle := intervalIntegral.integral_timeTriangle_sub hHmeas hHind
  have hFKInt := IsConservative.integrableOn_feynmanKacResolventReal_integrand
    P hP hq hq0 hlam hf hfD x
  have hKernelInt : IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x) (Ioi 0) := by
    have hzero := IsConservative.integrableOn_feynmanKacResolventReal_integrand
      P hP measurable_const (fun _ ↦ le_rfl) hlam hf hfD x
    apply hzero.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht
    have heval := hFeller.integral_eval_continuousProcess_of_measurable
      P hP hK (Real.toNNReal t) x hf
    simp only [IsConservative.feynmanKac_apply, feynmanKacAdditiveFunctional,
      intervalIntegral.integral_zero, neg_zero, Real.exp_zero, one_mul]
    rw [heval]
    rfl
  have htime (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      Real.exp (-lam * t) *
        (kernelIntegral (P (Real.toNNReal t)) f x -
          IsConservative.feynmanKac P hP q (Real.toNNReal t) f x) =
        ∫ s in Ioo (0 : ℝ) t, H (s, t - s) := by
    have hfinite := hFeller.integral_sub_feynmanKac_eq_integral_of_norm_le
      P hP hK hq hq0 hqC hf hfD (Real.toNNReal t) x
    rw [intervalIntegral.integral_of_le (Real.toNNReal t).coe_nonneg,
      integral_Ioc_eq_integral_Ioo, Real.coe_toNNReal t ht.le] at hfinite
    change kernelIntegral (P (Real.toNNReal t)) f x -
      IsConservative.feynmanKac P hP q (Real.toNNReal t) f x = _ at hfinite
    calc
      Real.exp (-lam * t) *
          (kernelIntegral (P (Real.toNNReal t)) f x -
            IsConservative.feynmanKac P hP q (Real.toNNReal t) f x) =
          Real.exp (-lam * t) *
            ∫ s in Ioo (0 : ℝ) t, kernelIntegral (P (Real.toNNReal s))
              (fun y ↦ q y * IsConservative.feynmanKac P hP q
                (Real.toNNReal t - Real.toNNReal s) f y) x := by
        rw [hfinite]
        congr 2
      _ = ∫ s in Ioo (0 : ℝ) t, Real.exp (-lam * t) *
            kernelIntegral (P (Real.toNNReal s))
              (fun y ↦ q y * IsConservative.feynmanKac P hP q
                (Real.toNNReal t - Real.toNNReal s) f y) x := by
        rw [MeasureTheory.integral_const_mul]
      _ = ∫ s in Ioo (0 : ℝ) t, H (s, t - s) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro s hs
        have hs0 : 0 ≤ s := hs.1.le
        have hsub0 : 0 ≤ t - s := sub_nonneg.mpr hs.2.le
        have hsub : Real.toNNReal t - Real.toNNReal s = Real.toNNReal (t - s) := by
          apply NNReal.coe_injective
          rw [NNReal.coe_sub (Real.toNNReal_le_toNNReal hs.2.le),
            Real.coe_toNNReal t ht.le, Real.coe_toNNReal s hs0,
            Real.coe_toNNReal (t - s) hsub0]
        dsimp only [H]
        rw [hsub]
        congr 2
        ring
  have hcorr : P.kernelResolventReal lam
      (fun y ↦ q y * IsConservative.feynmanKacResolventReal P hP q lam f y) x =
      ∫ s in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), H (s, u) := by
    unfold SubMarkovKernelSemigroup.kernelResolventReal
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [hP.kernelIntegral_mul_feynmanKacResolventReal
      P hq hq0 hqC hlam (Real.toNNReal s) hf hfD x]
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _hu
    dsimp only [H]
    rw [show -lam * (s + u) = -lam * s + -lam * u by ring, Real.exp_add]
    ring
  have hdiff : P.kernelResolventReal lam f x -
      IsConservative.feynmanKacResolventReal P hP q lam f x =
      P.kernelResolventReal lam
        (fun y ↦ q y * IsConservative.feynmanKacResolventReal P hP q lam f y) x := by
    unfold SubMarkovKernelSemigroup.kernelResolventReal
    unfold IsConservative.feynmanKacResolventReal
    rw [← integral_sub hKernelInt hFKInt]
    calc
      (∫ t in Ioi (0 : ℝ),
          Real.exp (-lam * t) * kernelIntegral (P (Real.toNNReal t)) f x -
            Real.exp (-lam * t) *
              IsConservative.feynmanKac P hP q (Real.toNNReal t) f x) =
          ∫ t in Ioi (0 : ℝ), ∫ s in Ioo (0 : ℝ) t, H (s, t - s) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [← mul_sub]
        exact htime t ht
      _ = ∫ s in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), H (s, u) := htriangle
      _ = _ := hcorr.symm
  simp only [Pi.sub_apply]
  linarith only [hdiff]
