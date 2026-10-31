-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.integral_discountedDynkinProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:30:09.0792+00:00
-- url     : https://prove2.me/submissions/e07ab303-59c2-4da5-ac84-8c531041d079

import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
import Definitions.Def_MarkovProcess_V3H_Trajectory_DynkinMartingale_970781f3
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
import Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_exp_smul_operator_sub_eq_integral
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_eval_nnreal
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_stronglyMeasurable_integral_discountedGenerator

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


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The Dynkin martingale

For the continuous-path process `Q = continuousProcess P hP` of a conservative Feller semigroup
`P` and a function `f` in the generator domain of the `C₀` semigroup of `P`, with generator
`L f`, the **Dynkin process**

  `M t omega = f (omega t) - ∫₀ᵗ (L f) (omega s) ds`

is a martingale for the canonical filtration under `Q x`, for every starting point `x`
(`IsFellerKernelSemigroup.martingale_dynkinProcess`).

The route is the deterministic-time Dynkin identity
(`integral_eval_sub_eq_integral_integral_generator`), which says exactly that
`E_y M u = f y` for every time `u` and starting point `y` (`integral_dynkinProcess`), together
with the additive decomposition

  `M t omega = M s omega - f (omega s) + M (t - s) (shift s omega)`   (`s ≤ t`)

(`dynkinProcess_eq_add_shift`) and the simple Markov property in conditional-expectation form
(`continuousProcess_condExp_shift`): conditionally on the canonical filtration at time `s`, the
expectation of the last term is `f (omega s)`, which cancels the middle term.

The auxiliary facts proved on the way are of independent use: the Dynkin process is bounded by
`‖f‖ + t ‖L f‖` on `[0, t]` (`norm_dynkinProcess_le`), it is adapted to the canonical filtration
(`adapted_dynkinProcess`), and it is continuous in time along every path
(`continuous_dynkinProcess`).  Adaptedness of the time-integral term comes from progressive
measurability of the coordinate process together with measurability of Bochner integrals in a
parameter.

The exponentially discounted extension is developed in `Trajectory/DiscountedDynkin.lean`;
its zero-discount process is identified with this one by `discountedDynkinProcess_zero`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

section C0Bound

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The `C₀` norm bounds the values of a `C₀` function. -/
theorem norm_c0_apply_le (g : C₀(alpha, ℝ)) (y : alpha) : ‖g y‖ ≤ ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm g.toBCF y

end C0Bound

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

section Definition











end Definition

section Adapted

variable [SecondCountableTopology alpha]













end Adapted

section Decomposition



end Decomposition

section Process

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)

section Expectation





end Expectation

section Martingale



end Martingale

end Process

end

end MarkovProcess.SubMarkovKernelSemigroup


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The discounted Dynkin formula

For the continuous-path process of a conservative Feller semigroup, this file proves that the
Dynkin process with exponential discount is a martingale and applies optional stopping at an exit
time truncated by a deterministic horizon.  At zero discount it agrees with the Dynkin process
of `Trajectory/DynkinMartingale.lean`.

Main results: `IsFellerKernelSemigroup.discountedDynkinProcess`,
`discountedDynkinProcess_apply`, `discountedDynkinProcess_zero`,
`norm_discountedDynkinProcess_le`, `continuous_discountedDynkinProcess`,
`stronglyMeasurable_integral_discountedGenerator`,
`stronglyMeasurable_discountedDynkinProcess_canonicalFiltration`,
`stronglyMeasurable_discountedDynkinProcess`, `adapted_discountedDynkinProcess`,
`integrable_discountedDynkinProcess`, `integral_discountedDynkinProcess`,
`discountedDynkinProcess_eq_add_shift`, `martingale_discountedDynkinProcess`,
`progMeasurable_discountedDynkinProcess`, `measurable_discountedDynkinProcess_stoppingTime`,
`integral_discountedDynkinProcess_stoppingTime`, and
`integral_exp_eval_exitTimeTrunc_sub_eq_integral_integral`.

No assertion is made at an unbounded stopping time or about passage to an infinite horizon.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

section ProcessDefinition







/-- The exponential discount is bounded on a nonnegative bounded interval. -/
private theorem exp_neg_mul_le_exp_abs_mul {lam s v : ℝ} (hs : 0 ≤ s) (hsv : s ≤ v) :
    Real.exp (-lam * s) ≤ Real.exp (|lam| * v) := by
  apply Real.exp_le_exp.mpr
  calc
    -lam * s ≤ |lam| * s :=
      mul_le_mul_of_nonneg_right (neg_le_abs lam) hs
    _ ≤ |lam| * v := mul_le_mul_of_nonneg_left hsv (abs_nonneg lam)





end ProcessDefinition

section Adapted

variable [SecondCountableTopology alpha]











end Adapted

section Expectation

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)





end Expectation

section Decomposition



end Decomposition

section Martingale

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)



end Martingale

section OptionalStopping

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)









end OptionalStopping

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
# The discounted Dynkin formula

For the continuous-path process of a conservative Feller semigroup, this file proves that the
Dynkin process with exponential discount is a martingale and applies optional stopping at an exit
time truncated by a deterministic horizon.  At zero discount it agrees with the Dynkin process
of `Trajectory/DynkinMartingale.lean`.

Main results: `IsFellerKernelSemigroup.discountedDynkinProcess`,
`discountedDynkinProcess_apply`, `discountedDynkinProcess_zero`,
`norm_discountedDynkinProcess_le`, `continuous_discountedDynkinProcess`,
`stronglyMeasurable_integral_discountedGenerator`,
`stronglyMeasurable_discountedDynkinProcess_canonicalFiltration`,
`stronglyMeasurable_discountedDynkinProcess`, `adapted_discountedDynkinProcess`,
`integrable_discountedDynkinProcess`, `integral_discountedDynkinProcess`,
`discountedDynkinProcess_eq_add_shift`, `martingale_discountedDynkinProcess`,
`progMeasurable_discountedDynkinProcess`, `measurable_discountedDynkinProcess_stoppingTime`,
`integral_discountedDynkinProcess_stoppingTime`, and
`integral_exp_eval_exitTimeTrunc_sub_eq_integral_integral`.

No assertion is made at an unbounded stopping time or about passage to an infinite horizon.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}




variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)



namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (lam : ℝ) (t : NNReal) (y : alpha) :
    ∫ omega, hFeller.discountedDynkinProcess f lam t omega
        ∂(IsConservative.continuousProcess P hP y) =
      (f : C₀(alpha, ℝ)) y := by
  let Q : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP y
  let g : C₀(alpha, ℝ) :=
    hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))
  have hterm : Integrable (fun omega : ContinuousPath alpha ↦
      Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t)) Q := by
    have hmeas : Measurable (fun omega : ContinuousPath alpha ↦
        Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t)) :=
      ((f : C₀(alpha, ℝ)).continuous.measurable.comp
        (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t)).const_mul _
    exact Integrable.of_bound hmeas.aestronglyMeasurable _
      (Eventually.of_forall fun omega ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_c0_apply_le _ _) (norm_nonneg _))
  have hcorr : Integrable (fun omega : ContinuousPath alpha ↦
      ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * g (omega (Real.toNNReal s))) Q := by
    have hmeas := (hFeller.stronglyMeasurable_integral_discountedGenerator f lam t).mono
      ((ContinuousPath.canonicalFiltration (alpha := alpha)).le t)
    refine Integrable.of_bound hmeas.aestronglyMeasurable
      ((t : ℝ) * (Real.exp (|lam| * (t : ℝ)) * ‖g‖))
      (Eventually.of_forall fun omega ↦ ?_)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (t : ℝ))
      (C := Real.exp (|lam| * (t : ℝ)) * ‖g‖)
      (f := fun s : ℝ ↦ Real.exp (-lam * s) * g (omega (Real.toNNReal s)))
      (fun s hs ↦ by
        rw [Set.uIoc_of_le t.coe_nonneg] at hs
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (exp_neg_mul_le_exp_abs_mul hs.1.le hs.2)
          (norm_c0_apply_le _ _) (norm_nonneg _) (Real.exp_pos _).le)
    rwa [sub_zero, abs_of_nonneg t.coe_nonneg, mul_comm] at h
  have hstep :
      (∫ omega, Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t) ∂Q) -
          (f : C₀(alpha, ℝ)) y =
        ∫ s in (0 : ℝ)..t, ∫ omega, Real.exp (-lam * s) *
          g (omega (Real.toNNReal s)) ∂Q := by
    calc
      (∫ omega, Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t) ∂Q) -
            (f : C₀(alpha, ℝ)) y
          = c0EvalCLM y (Real.exp (-lam * (t : ℝ)) •
              hFeller.c0Semigroup t (f : C₀(alpha, ℝ)) - f) := by
            rw [map_sub, map_smul, c0EvalCLM_apply, c0EvalCLM_apply,
              smul_eq_mul, hFeller.c0Semigroup_apply_eq_integral P hP hK]
            rw [MeasureTheory.integral_const_mul]
      _ = c0EvalCLM y (∫ s in (0 : ℝ)..t, Real.exp (-lam * s) •
            hFeller.c0Semigroup (Real.toNNReal s) g) := by
          rw [hFeller.c0Semigroup.exp_smul_operator_sub_eq_integral f lam t]
      _ = ∫ s in (0 : ℝ)..t, c0EvalCLM y
            (Real.exp (-lam * s) • hFeller.c0Semigroup (Real.toNNReal s) g) := by
          rw [← (c0EvalCLM y).intervalIntegral_comp_comm]
          exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
            (hFeller.c0Semigroup.continuous_operator_toNNReal g)).intervalIntegrable _ _
      _ = ∫ s in (0 : ℝ)..t, ∫ omega, Real.exp (-lam * s) *
            g (omega (Real.toNNReal s)) ∂Q := by
          refine intervalIntegral.integral_congr fun s _ ↦ ?_
          rw [map_smul, c0EvalCLM_apply, smul_eq_mul,
            hFeller.c0Semigroup_apply_eq_integral P hP hK, MeasureTheory.integral_const_mul]
  have hcont : Continuous fun p : ℝ × ContinuousPath alpha ↦
      Real.exp (-lam * p.1) * g (p.2 (Real.toNNReal p.1)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
      (g.continuous.comp ((ContinuousEval.continuous_eval.comp continuous_swap).comp
        (continuous_real_toNNReal.fst'.prodMk continuous_snd)))
  have hprodint : Integrable
      (Function.uncurry fun (s : ℝ) (omega : ContinuousPath alpha) ↦
        Real.exp (-lam * s) * g (omega (Real.toNNReal s)))
      ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod Q) := by
    let C := Real.exp (|lam| * (t : ℝ)) * ‖g‖
    refine Integrable.of_bound hcont.aestronglyMeasurable C ?_
    change ∀ᵐ p : ℝ × ContinuousPath alpha
      ∂((volume.restrict (Set.Ioc (0 : ℝ) t)).prod Q),
        ‖Real.exp (-lam * p.1) * g (p.2 (Real.toNNReal p.1))‖ ≤ C
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le
      (hcont.norm.measurable) measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact Eventually.of_forall fun omega ↦ by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (exp_neg_mul_le_exp_abs_mul hs.1.le hs.2)
        (norm_c0_apply_le _ _) (norm_nonneg _) (Real.exp_pos _).le
  have hswap :
      ∫ omega, (∫ s in (0 : ℝ)..t, Real.exp (-lam * s) *
          g (omega (Real.toNNReal s))) ∂Q =
        ∫ s in (0 : ℝ)..t, ∫ omega, Real.exp (-lam * s) *
          g (omega (Real.toNNReal s)) ∂Q := by
    calc
      ∫ omega, (∫ s in (0 : ℝ)..t, Real.exp (-lam * s) *
            g (omega (Real.toNNReal s))) ∂Q =
          ∫ omega, (∫ s in Set.Ioc (0 : ℝ) t, Real.exp (-lam * s) *
            g (omega (Real.toNNReal s))) ∂Q := by
        refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
        exact intervalIntegral.integral_of_le t.coe_nonneg
      _ = ∫ s in Set.Ioc (0 : ℝ) t, ∫ omega, Real.exp (-lam * s) *
            g (omega (Real.toNNReal s)) ∂Q := (integral_integral_swap hprodint).symm
      _ = ∫ s in (0 : ℝ)..t, ∫ omega, Real.exp (-lam * s) *
            g (omega (Real.toNNReal s)) ∂Q :=
        (intervalIntegral.integral_of_le t.coe_nonneg).symm
  change ∫ omega, (Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t) -
      ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * g (omega (Real.toNNReal s))) ∂Q = _
  rw [integral_sub hterm hcorr]
  linarith only [hstep, hswap]
