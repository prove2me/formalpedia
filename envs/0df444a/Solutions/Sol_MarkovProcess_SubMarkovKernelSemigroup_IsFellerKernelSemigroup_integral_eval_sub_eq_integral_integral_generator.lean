-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.integral_eval_sub_eq_integral_integral_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:30:43.648377+00:00
-- url     : https://prove2.me/submissions/57cde0d5-2a08-4404-9fbf-254a68143276

import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_C0SemigroupJoint_9aea0383
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Definitions.Def_MarkovProcess_V3H_Trajectory_Basic_34bd0835
import Definitions.Def_MarkovProcess_V3H_Trajectory_Dynkin_eb6ae7c0
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
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
import Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_operator_sub_eq_integral
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_eval_nnreal

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dynkin's formula at deterministic times

For the continuous-path process `Q = continuousProcess P hP` of a conservative Feller semigroup
`P`, the `C₀` semigroup `hFeller.c0Semigroup` acts by `(S t f) x = E_x f(ω_t)`
(`c0Semigroup_apply_eq_integral`, from the one-time marginal `continuousProcess_map_eval_nnreal`
at every real time).  Combining this with the fundamental identity of the generator
`S t f - f = ∫₀ᵗ S s (L f) ds` and Fubini's theorem gives **Dynkin's formula**
(`integral_eval_sub_eq_integral_integral_generator`): for `f` in the generator domain,

  `E_x f(ω_t) - f x = E_x ∫₀ᵗ (L f)(ω_s) ds`.

The evaluation functional `c0EvalCLM x : C₀(α, ℝ) →L[ℝ] ℝ` is the tool that moves the Bochner
integral in `C₀` to a pointwise integral; `evalC0CLM` is the same functional under its original
name, kept for consumers.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section Eval

variable {alpha : Type*} [TopologicalSpace alpha]





end Eval

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- One-time marginal at every real time: evaluating the continuous-path process at time `t`
gives the transition kernel of `P` at `t`. -/
theorem IsFellerKernelSemigroup.continuousProcess_map_eval_nnreal
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (t : NNReal) :
    (IsConservative.continuousProcess P hP).map (fun omega ↦ omega t) = P t :=
  IsConservative.continuousPathTrajectory_map_eval_nnreal P hP hFeller _ hK t

/-- The expectation of a `C₀` function of the position at time `t` is its integral against the
transition measure at time `t`. -/
theorem IsFellerKernelSemigroup.integral_eval_continuousProcess
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (t : NNReal) (x : alpha)
    (f : C₀(alpha, ℝ)) :
    ∫ omega, f (omega t) ∂(IsConservative.continuousProcess P hP x) = ∫ y, f y ∂(P t x) := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  have h := integral_map (μ := IsConservative.continuousProcess P hP x) hmeas.aemeasurable
    (f := fun y ↦ f y) f.continuous.aestronglyMeasurable
  rw [← h, ← Kernel.map_apply _ hmeas, hFeller.continuousProcess_map_eval_nnreal P hP hK t]



/-- The `C₀` semigroup of a Feller semigroup is the expectation semigroup of its continuous-path
process: `(S t f) x = E_x f(ω_t)`. -/
theorem IsFellerKernelSemigroup.c0Semigroup_apply_eq_integral
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (t : NNReal) (x : alpha)
    (f : C₀(alpha, ℝ)) :
    hFeller.c0Semigroup t f x =
      ∫ omega, f (omega t) ∂(IsConservative.continuousProcess P hP x) := by
  rw [IsFellerKernelSemigroup.c0Semigroup_apply_apply, kernelIntegral,
    hFeller.integral_eval_continuousProcess P hP hK t x f]



end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dynkin's formula at deterministic times

For the continuous-path process `Q = continuousProcess P hP` of a conservative Feller semigroup
`P`, the `C₀` semigroup `hFeller.c0Semigroup` acts by `(S t f) x = E_x f(ω_t)`
(`c0Semigroup_apply_eq_integral`, from the one-time marginal `continuousProcess_map_eval_nnreal`
at every real time).  Combining this with the fundamental identity of the generator
`S t f - f = ∫₀ᵗ S s (L f) ds` and Fubini's theorem gives **Dynkin's formula**
(`integral_eval_sub_eq_integral_integral_generator`): for `f` in the generator domain,

  `E_x f(ω_t) - f x = E_x ∫₀ᵗ (L f)(ω_s) ds`.

The evaluation functional `c0EvalCLM x : C₀(α, ℝ) →L[ℝ] ℝ` is the tool that moves the Bochner
integral in `C₀` to a pointwise integral; `evalC0CLM` is the same functional under its original
name, kept for consumers.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty



variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)









namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) (x : alpha) :
    ∫ omega, (f : C₀(alpha, ℝ)) (omega t) ∂(IsConservative.continuousProcess P hP x) -
        (f : C₀(alpha, ℝ)) x =
      ∫ omega, (∫ s in (0 : ℝ)..t, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
        ∂(IsConservative.continuousProcess P hP x) := by
  have hint : IntervalIntegrable
      (fun s : ℝ ↦ hFeller.c0Semigroup (Real.toNNReal s) (hFeller.c0Semigroup.generator f))
      volume 0 t :=
    (hFeller.c0Semigroup.continuous_operator_toNNReal _).intervalIntegrable _ _
  have hstep : ∫ omega, (f : C₀(alpha, ℝ)) (omega t) ∂(IsConservative.continuousProcess P hP x) -
      (f : C₀(alpha, ℝ)) x =
      ∫ s in (0 : ℝ)..t, ∫ omega, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))
        ∂(IsConservative.continuousProcess P hP x) := by
    calc ∫ omega, (f : C₀(alpha, ℝ)) (omega t) ∂(IsConservative.continuousProcess P hP x) -
          (f : C₀(alpha, ℝ)) x
        = c0EvalCLM x (hFeller.c0Semigroup t (f : C₀(alpha, ℝ)) - (f : C₀(alpha, ℝ))) := by
          rw [map_sub, c0EvalCLM_apply, c0EvalCLM_apply,
            hFeller.c0Semigroup_apply_eq_integral P hP hK t x]
      _ = c0EvalCLM x (∫ s in (0 : ℝ)..t,
            hFeller.c0Semigroup (Real.toNNReal s) (hFeller.c0Semigroup.generator f)) := by
          rw [hFeller.c0Semigroup.operator_sub_eq_integral f t]
      _ = ∫ s in (0 : ℝ)..t,
            c0EvalCLM x (hFeller.c0Semigroup (Real.toNNReal s) (hFeller.c0Semigroup.generator f)) :=
          ((c0EvalCLM x).intervalIntegral_comp_comm hint).symm
      _ = ∫ s in (0 : ℝ)..t, ∫ omega, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))
            ∂(IsConservative.continuousProcess P hP x) := by
          refine intervalIntegral.integral_congr fun s _ ↦ ?_
          rw [c0EvalCLM_apply, hFeller.c0Semigroup_apply_eq_integral P hP hK]
  rw [hstep]
  have hcont : Continuous fun p : ℝ × ContinuousPath alpha ↦
      (hFeller.c0Semigroup.generator f) (p.2 (Real.toNNReal p.1)) :=
    (hFeller.c0Semigroup.generator f).continuous.comp
      ((ContinuousEval.continuous_eval.comp continuous_swap).comp
        (continuous_real_toNNReal.fst'.prodMk continuous_snd))
  have hbound : ∀ p : ℝ × ContinuousPath alpha,
      ‖(hFeller.c0Semigroup.generator f) (p.2 (Real.toNNReal p.1))‖ ≤
        ‖hFeller.c0Semigroup.generator f‖ := fun p ↦ by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm (hFeller.c0Semigroup.generator f).toBCF
      (p.2 (Real.toNNReal p.1))
  have hprodint : Integrable
      (Function.uncurry fun (s : ℝ) (omega : ContinuousPath alpha) ↦
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
      ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod (IsConservative.continuousProcess P hP x)) :=
    Integrable.of_bound hcont.aestronglyMeasurable _ (Eventually.of_forall hbound)
  rw [intervalIntegral.integral_of_le t.coe_nonneg, integral_integral_swap hprodint]
  refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
  exact (intervalIntegral.integral_of_le t.coe_nonneg).symm
