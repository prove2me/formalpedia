-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsLambdaExcessive.supermartingale_discountedValueProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:10:13.946498+00:00
-- url     : https://prove2.me/submissions/7ce478d8-fba6-4d1a-a799-672ba34f0322

import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
import Definitions.Def_MarkovProcess_V3H_Trajectory_DynkinMartingale_970781f3
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExcessiveStopping_8ea33a1f
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.MeasureTheory.Measure.GiryMonad
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
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_ContinuousPath_condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_eval_nnreal
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuousPathTrajectory_restrict_map_shift

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Canonical continuous-path space

This file provides the compact-open space of continuous paths on nonnegative real time, its
coordinate process, and the filtration generated by coordinates up to each time. It constructs
no probability law and makes no stochastic-process association or path-regularity claim.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace MarkovProcess



namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]























/-- The time-`t` coordinate is measurable for the canonical filtration at time `t`. -/
theorem measurable_coordinateProcess_canonicalFiltration
    [MeasurableSpace alpha] [BorelSpace alpha] (t : NNReal) :
    Measurable[canonicalFiltration (alpha := alpha) t]
      (coordinateProcess (alpha := alpha) t) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le (⟨t, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic t) le_rfl

end ContinuousPath

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic-time conditional expectation for the Feller trajectory

At every physical time, the conditional expectation of a bounded strongly measurable functional
of the shifted canonical Feller trajectory, given the canonical filtration at that time, is the
path-kernel expectation started from the current state.  The proof passes the event-restricted
deterministic restart identity through the generic continuous-path conditional-expectation
bridge.

The time here is deterministic.  The corresponding statement at a finite stopping time is in
`Trajectory/FellerStoppingConditional.lean`, and at a stopping time that may be infinite in
`Trajectory/StoppingLtTop.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- At every physical time, the conditional expectation of a bounded functional of the shifted
Feller trajectory given the canonical filtration is its path-kernel expectation started from the
current state. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_condExp_shift
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (s : NNReal)
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift s omega)|
      ContinuousPath.canonicalFiltration (alpha := alpha) s] =ᵐ[
        (continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega s) := by
  apply ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
    (continuousPathTrajectory P hP default) x s
  · exact hFeller.continuousPathTrajectory_restrict_map_shift
      P hP default hK x s
  · exact hF
  · exact hFC

end
end MarkovProcess.SubMarkovKernelSemigroup


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The continuous-path Markov process of a Feller semigroup

This is the entry point of the library: for a conservative sub-Markov kernel semigroup `P` on a
nonempty, locally compact Polish state space it names the continuous-path process
`continuousProcess P hP`, restates under quotable names the properties proved for that process
elsewhere in the library, and proves that it is the unique Markov kernel into continuous paths
with the finite-dimensional distributions of `P`.

Every statement carries the Kolmogorov regularity hypothesis `P.KolmogorovRegular hP`, which is
what gives the dense-time trajectory of `P` a continuous modification.  The shift and restart
statements carry in addition the Feller hypothesis `P.IsFellerKernelSemigroup`; the uniqueness
statements carry neither Feller continuity nor local compactness.

Nothing here asserts a Hunt-process property, and no statement covers a stopping time that can be
infinite.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

section FinsetEvaluation

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]



end ContinuousPath

end FinsetEvaluation

namespace Kernel

noncomputable section DenseFiniteEvaluation

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [MeasurableSpace beta]



section Identification

variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]



end Identification

end DenseFiniteEvaluation

end Kernel

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



















variable [LocallyCompactSpace alpha]









variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- Simple Markov property in conditional-expectation form: given the canonical filtration at a
deterministic time, the conditional expectation of a bounded functional of the shifted path is
that functional's expectation under the process started from the current state. -/
theorem IsFellerKernelSemigroup.continuousProcess_condExp_shift
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (s : NNReal) (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousProcess P hP) x)[fun omega ↦ F (ContinuousPath.shift s omega)|
        ContinuousPath.canonicalFiltration (alpha := alpha) s] =ᵐ[
      (continuousProcess P hP) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousProcess P hP) (omega s) :=
  hFeller.continuousPathTrajectory_condExp_shift P hP _ hK x s F hF C hFC


















end


end SubMarkovKernelSemigroup

end MarkovProcess


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
# Excessive functions and stopping

This file turns the semigroup definition of an exponentially excessive `C₀` function into a
supermartingale along the canonical continuous process.  Continuous-time optional stopping then
gives the corresponding inequality at bounded stopping times and, by Fatou's lemma, at the finite
exit time from an open set.

The exit inequality is the lower-bound half paired with
`IsFellerKernelSemigroup.lintegral_pathResolvent_eq_killedResolvent_add`.  No model-specific
assumptions enter here.

Main results: `IsFellerKernelSemigroup.resolvent_isLambdaExcessive`,
`IsLambdaExcessive.supermartingale_discountedValueProcess`,
`IsLambdaExcessive.integral_discountedValueProcess_stoppingTime_le`, and
`IsLambdaExcessive.lintegral_discountedValue_exitTime_le`.

No converse characterization of excessive functions is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

section Supermedian

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}





end Supermedian

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}







omit [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
/-- The discounted value process is adapted to the canonical filtration. -/
theorem adapted_discountedValueProcess (lam : ℝ) (v : C₀(alpha, ℝ)) :
    StronglyAdapted (ContinuousPath.canonicalFiltration (alpha := alpha))
      (discountedValueProcess lam v) := by
  intro t
  exact ((v.continuous.comp_stronglyMeasurable
    (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
      (alpha := alpha) t).stronglyMeasurable).const_mul _)

omit [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
/-- The discounted value process is uniformly bounded in the path at each time. -/
theorem norm_discountedValueProcess_le (lam : ℝ) (v : C₀(alpha, ℝ))
    (t : NNReal) (omega : ContinuousPath alpha) :
    ‖discountedValueProcess lam v t omega‖ ≤ Real.exp (-lam * (t : ℝ)) * ‖v‖ := by
  rw [discountedValueProcess, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (norm_c0_apply_le v (omega t)) (Real.exp_pos _).le













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
# Excessive functions and stopping

This file turns the semigroup definition of an exponentially excessive `C₀` function into a
supermartingale along the canonical continuous process.  Continuous-time optional stopping then
gives the corresponding inequality at bounded stopping times and, by Fatou's lemma, at the finite
exit time from an open set.

The exit inequality is the lower-bound half paired with
`IsFellerKernelSemigroup.lintegral_pathResolvent_eq_killedResolvent_add`.  No model-specific
assumptions enter here.

Main results: `IsFellerKernelSemigroup.resolvent_isLambdaExcessive`,
`IsLambdaExcessive.supermartingale_discountedValueProcess`,
`IsLambdaExcessive.integral_discountedValueProcess_stoppingTime_le`, and
`IsLambdaExcessive.lintegral_discountedValue_exitTime_le`.

No converse characterization of excessive functions is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty




variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}













namespace MarkovProcess.SubMarkovKernelSemigroup.IsLambdaExcessive

end MarkovProcess.SubMarkovKernelSemigroup.IsLambdaExcessive
open MarkovProcess.SubMarkovKernelSemigroup.IsLambdaExcessive
theorem solution
    (hP : P.IsConservative) (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) {lam : ℝ} {v : C₀(alpha, ℝ)}
    (hv : P.IsLambdaExcessive lam v) (x : alpha) :
    Supermartingale (discountedValueProcess lam v)
      (ContinuousPath.canonicalFiltration (alpha := alpha))
      (IsConservative.continuousProcess P hP x) := by
  refine ⟨adapted_discountedValueProcess lam v, ?_, ?_⟩
  · intro s t hst
    let c : ℝ := Real.exp (-lam * (s : ℝ))
    let F : ContinuousPath alpha → ℝ := fun eta ↦
      Real.exp (-lam * ((t - s : NNReal) : ℝ)) * v (eta (t - s))
    have hdecomp : discountedValueProcess lam v t =
        fun omega ↦ c * F (ContinuousPath.shift s omega) := by
      funext omega
      dsimp only [discountedValueProcess, c, F]
      rw [ContinuousPath.shift_apply, add_tsub_cancel_of_le hst]
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      rw [NNReal.coe_sub hst]
      ring
    have hmeasF : StronglyMeasurable F :=
      (v.continuous.comp_stronglyMeasurable
        (ContinuousPath.measurable_coordinateProcess (t - s)).stronglyMeasurable).const_mul _
    have hboundF : ∀ eta : ContinuousPath alpha, ‖F eta‖ ≤
        Real.exp (-lam * ((t - s : NNReal) : ℝ)) * ‖v‖ := fun eta ↦ by
      exact norm_discountedValueProcess_le lam v (t - s) eta
    have hcond := hFeller.continuousProcess_condExp_shift P hP hK x s F hmeasF _ hboundF
    rw [hdecomp]
    refine (condExp_smul c (fun omega ↦ F (ContinuousPath.shift s omega)) _).trans_le ?_
    refine (EventuallyEq.const_smul hcond c).trans_le (Eventually.of_forall fun omega ↦ ?_)
    change c * (∫ eta, F eta ∂IsConservative.continuousProcess P hP (omega s)) ≤
      discountedValueProcess lam v s omega
    have hinner : ∫ eta, F eta ∂IsConservative.continuousProcess P hP (omega s) ≤
        v (omega s) := by
      dsimp only [F]
      rw [MeasureTheory.integral_const_mul,
        hFeller.integral_eval_continuousProcess P hP hK]
      exact hv.2 (t - s) (omega s)
    dsimp only [c, discountedValueProcess]
    exact mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le
  · intro t
    exact Integrable.of_bound
      ((adapted_discountedValueProcess lam v t).mono
        ((ContinuousPath.canonicalFiltration (alpha := alpha)).le t)).aestronglyMeasurable
      (Real.exp (-lam * (t : ℝ)) * ‖v‖)
      (Eventually.of_forall (norm_discountedValueProcess_le lam v t))
