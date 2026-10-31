-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.kernelResolvent_eq_killedResolvent_univ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:31:15.01111+00:00
-- url     : https://prove2.me/submissions/257d0682-ae0f-4baf-9902-2b061933f8d4

import Definitions.Def_MarkovProcess_V3H_Kernel_Resolvent_f63a7282
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacFunctional_cc8a1986
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacResolvent_ed9736ae
import Definitions.Def_MarkovProcess_V3H_Trajectory_ResolventExitDecomposition_db489119
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
import Theorems.Thm_MarkovProcess_ContinuousPath_exitTime_eq_top_iff
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_eval_nnreal
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_feynmanKacResolvent_eq_lintegral_path
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_killedResolvent_eq_lintegral

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









end MarkovProcess.SubMarkovKernelSemigroup


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Resolvent decomposition at an exit time

This file splits the whole-space path resolvent at the first exit time from an open set.  The
occupation before exit is the killed resolvent; on finite exit, the remaining occupation is the
discounted whole-space resolvent restarted from the exit location.  The restart step uses the
strong Markov property on `{exitTime U < ⊤}` and is valid for arbitrary nonnegative extended
measurable observables.

Main definitions and results: `ContinuousPath.pathResolvent`,
`ContinuousPath.measurable_pathResolvent`,
`IsConservative.lintegral_pathResolvent_eq_killedResolvent_univ`, and
`IsFellerKernelSemigroup.lintegral_pathResolvent_eq_killedResolvent_add`.

No integrability or almost-sure finiteness of the exit time is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]





end

end ContinuousPath

namespace SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

omit [LocallyCompactSpace alpha] in
/-- Expected discounted path occupation is the killed resolvent for the whole state space. -/
theorem IsConservative.lintegral_pathResolvent_eq_killedResolvent_univ
    (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    ∫⁻ omega, ContinuousPath.pathResolvent lam f omega
        ∂(IsConservative.continuousProcess P hP x) =
      IsConservative.killedResolvent P hP Set.univ isOpen_univ lam f x := by
  rw [IsConservative.killedResolvent_eq_lintegral P hP Set.univ isOpen_univ lam hf x]
  refine lintegral_congr fun omega ↦ setLIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [(ContinuousPath.exitTime_eq_top_iff Set.univ omega).mpr fun _ ↦ Set.mem_univ _]
  have ht : t ∈ {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ⊤} := ENNReal.coe_lt_top
  rw [Set.indicator_of_mem ht]









end

end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Feynman--Kac resolvents

This file Laplace-transforms the nonnegative extended-real Feynman--Kac operators and proves their
path-occupation formula, comparison with killed resolvents, and perturbation identities against
the unperturbed kernel resolvent.

Main results: `IsConservative.feynmanKacResolvent`,
`IsConservative.feynmanKacResolvent_eq_lintegral_path`,
`IsConservative.killedResolvent_le_feynmanKacResolvent`,
`IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral_of_norm_le`,
`IsFellerKernelSemigroup.kernelResolvent_eq_feynmanKacResolvent_add`, and
`IsFellerKernelSemigroup.feynmanKacResolvent_eq_kernelResolvent_sub`.

No uniqueness statement for the associated resolvent equation is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

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
# Feynman--Kac resolvents

This file Laplace-transforms the nonnegative extended-real Feynman--Kac operators and proves their
path-occupation formula, comparison with killed resolvents, and perturbation identities against
the unperturbed kernel resolvent.

Main results: `IsConservative.feynmanKacResolvent`,
`IsConservative.feynmanKacResolvent_eq_lintegral_path`,
`IsConservative.killedResolvent_le_feynmanKacResolvent`,
`IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral_of_norm_le`,
`IsFellerKernelSemigroup.kernelResolvent_eq_feynmanKacResolvent_add`, and
`IsFellerKernelSemigroup.feynmanKacResolvent_eq_kernelResolvent_sub`.

No uniqueness statement for the associated resolvent equation is asserted.
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
    (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    P.kernelResolvent lam f x =
      IsConservative.killedResolvent P hP Set.univ isOpen_univ lam f x := by
  have hzero : P.kernelResolvent lam f x =
      IsConservative.feynmanKacResolvent P hP (fun _ ↦ 0) lam f x := by
    unfold SubMarkovKernelSemigroup.kernelResolvent IsConservative.feynmanKacResolvent
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t _ht
    unfold IsConservative.feynmanKacENNReal
    simp only [feynmanKacAdditiveFunctional, intervalIntegral.integral_zero,
      neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    have heval := ContinuousPath.measurable_coordinateProcess
      (alpha := alpha) (Real.toNNReal t)
    have hin :
      (∫⁻ y, f y ∂(P (Real.toNNReal t) x)) =
        ∫⁻ omega, f (omega (Real.toNNReal t))
          ∂(IsConservative.continuousProcess P hP x) := by
      calc
        (∫⁻ y, f y ∂(P (Real.toNNReal t) x)) =
            ∫⁻ y, f y ∂((IsConservative.continuousProcess P hP).map
              (ContinuousPath.coordinateProcess (alpha := alpha) (Real.toNNReal t))) x := by
          have hmap : (IsConservative.continuousProcess P hP).map
              (ContinuousPath.coordinateProcess (alpha := alpha) (Real.toNNReal t)) =
                P (Real.toNNReal t) := by
            simpa only [ContinuousPath.coordinateProcess] using!
              hFeller.continuousProcess_map_eval_nnreal P hP hK (Real.toNNReal t)
          rw [hmap]
        _ = ∫⁻ omega, f (omega (Real.toNNReal t))
            ∂(IsConservative.continuousProcess P hP x) := by
          rw [Kernel.map_apply _ heval]
          exact lintegral_map hf heval
    exact congrArg (fun z ↦ ENNReal.ofReal (Real.exp (-lam * t)) * z) hin
  calc
    P.kernelResolvent lam f x =
        IsConservative.feynmanKacResolvent P hP (fun _ ↦ 0) lam f x := hzero
    _ = ∫⁻ omega, ContinuousPath.pathResolvent lam f omega
          ∂(IsConservative.continuousProcess P hP x) := by
      simpa only [ContinuousPath.pathResolvent, feynmanKacAdditiveFunctional,
        intervalIntegral.integral_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one,
        one_mul] using
        IsConservative.feynmanKacResolvent_eq_lintegral_path P hP
          (q := fun _ ↦ 0) measurable_const lam hf x
    _ = IsConservative.killedResolvent P hP Set.univ isOpen_univ lam f x :=
      IsConservative.lintegral_pathResolvent_eq_killedResolvent_univ P hP lam hf x
