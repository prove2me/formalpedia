-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsLambdaExcessive.lintegral_discountedValue_exitTime_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:28:22.361978+00:00
-- url     : https://prove2.me/submissions/8f00ada0-75d8-4290-ba0d-17a7d3f8816a

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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsLambdaExcessive_integral_discountedValueProcess_stoppingTime_le

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exit times of open sets on continuous-path space

For an open set `U` this file studies `ContinuousPath.exitTime U`, the first time a continuous
path leaves `U`, in the `WithTop`-valued form `ContinuousPath.exitTimeTop U` demanded by
Mathlib's stopping-time convention.  The main consumer facts are: the exit time is a stopping
time for the canonical filtration; it is finite exactly when the path leaves `U` at some time;
at a finite exit time the path sits on the frontier of `U` when it started inside; and its
truncation `exitTimeTrunc U K` at a deterministic horizon is an `NNReal`-valued stopping time,
which is the form the finite-stopping-time API of this library consumes.  The generic time-set
identities `survivalSet_top`, `survivalSet_ne_top`, and `survivalSet` identify the positive real
times below an extended nonnegative horizon.

The route is the closed-set detection of `Path/ClosedSetDetection.lean`: the event
`{exitTime ≤ t}` is the event of hitting the closed set `Uᶜ` by time `t`, because a path that
stays in the open set `U` throughout `[0, t]` stays in it slightly beyond `t`.

This file constructs no probability law and proves no probabilistic statement; in particular it
does not claim that the exit time is almost surely finite for any process.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MarkovProcess

namespace ContinuousPath

noncomputable section

section SurvivalSets







end SurvivalSets

variable {alpha : Type*} [PseudoMetricSpace alpha]

section Order











end Order

section WithTopValue









/-- The truncated exit time never exceeds its horizon. -/
theorem exitTimeTrunc_le (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha) :
    exitTimeTrunc U K omega ≤ K := by
  rw [← WithTop.coe_le_coe, coe_exitTimeTrunc]
  exact min_le_right _ _

end WithTopValue

section Frontier





end Frontier

section Stopping

variable [MeasurableSpace alpha] [BorelSpace alpha]





end Stopping

end

end ContinuousPath

end MarkovProcess


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
# The expected exit time, untruncated

The expected exit time bound of `Trajectory/DynkinStopping.lean` is stated for the exit time
truncated at a deterministic horizon `K`, uniformly in `K`.  This file removes the truncation by
monotone convergence: under the same hypotheses (`L f ≤ -1` on the open set `U`, `f ≥ m`),

  `E_x τ_U ≤ f x - m`  (`IsFellerKernelSemigroup.lintegral_exitTime_le`),

as an `ℝ≥0∞`-valued integral of the `ℝ≥0∞`-valued exit time, so in particular the exit time from
`U` is almost surely finite from every starting point (`ae_exitTime_lt_top`).

It also records that the truncated exit time of `Path/ExitTime.lean` is the generic truncation
`StoppingTime.truncTime` of `Trajectory/StoppingLtTop.lean` applied to `exitTimeTop`
(`ContinuousPath.exitTimeTrunc_eq_truncTime`), and the monotone limit
`ContinuousPath.iSup_exitTimeTrunc : ⨆ n, exitTimeTrunc U n ω = exitTime U ω`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]



/-- The truncated exit time, read in `ℝ≥0∞`, is the minimum of the exit time and the horizon. -/
theorem coe_exitTimeTrunc_ennreal (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha) :
    ((exitTimeTrunc U K omega : NNReal) : ℝ≥0∞) = min (exitTime U omega) (K : ℝ≥0∞) :=
  coe_exitTimeTrunc U K omega





end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}









end SubMarkovKernelSemigroup

end MarkovProcess


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

















omit [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
private theorem exitTimeTrunc_eq_untopD_of_le (U : Set alpha) (omega : ContinuousPath alpha)
    {K : NNReal} (hfinite : ContinuousPath.exitTime U omega ≠ ⊤)
    (hle : (ContinuousPath.exitTime U omega).toNNReal ≤ K) :
    ContinuousPath.exitTimeTrunc U K omega =
      (ContinuousPath.exitTime U omega).untopD 0 := by
  have hexit : ContinuousPath.exitTime U omega ≤ (K : ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal hfinite]
    exact ENNReal.coe_le_coe.mpr hle
  apply ENNReal.coe_injective
  rw [ContinuousPath.coe_exitTimeTrunc_ennreal, min_eq_left hexit]
  exact (ENNReal.coe_toNNReal hfinite).symm





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
    (hv : P.IsLambdaExcessive lam v) (U : Set alpha) (hU : IsOpen U) (x : alpha) :
    ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦
          ENNReal.ofReal (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
            ENNReal.ofReal (v (omega ((ContinuousPath.exitTime U omega).untopD 0)))) omega
        ∂(IsConservative.continuousProcess P hP x) ≤ ENNReal.ofReal (v x) := by
  let Q : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  let T : ℕ → ContinuousPath alpha → NNReal := fun n omega ↦
    ContinuousPath.exitTimeTrunc U n omega
  let g : ℕ → ContinuousPath alpha → ℝ≥0∞ := fun n omega ↦
    ENNReal.ofReal (Real.exp (-lam * (T n omega : ℝ))) *
      ENNReal.ofReal (v (omega (T n omega)))
  have hTstop : ∀ n, IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T n omega : WithTop NNReal)) := fun n ↦
    ContinuousPath.isStoppingTime_exitTimeTrunc U hU n
  have hTle : ∀ n omega, T n omega ≤ n := fun n omega ↦
    ContinuousPath.exitTimeTrunc_le U n omega
  have hrealMeas : ∀ n, Measurable fun omega ↦
      Real.exp (-lam * (T n omega : ℝ)) * v (omega (T n omega)) := by
    intro n
    have htime : Measurable fun omega : ContinuousPath alpha ↦ (T n omega : ℝ) :=
      measurable_coe_nnreal_real.comp
        (ContinuousPath.measurable_of_isStoppingTime _ (hTstop n))
    exact (Real.continuous_exp.measurable.comp (measurable_const.mul htime)).mul
      (v.continuous.measurable.comp
        (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTstop n)))
  have hgMeas : ∀ n, Measurable (g n) := fun n ↦
    (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul
        (measurable_coe_nnreal_real.comp
          (ContinuousPath.measurable_of_isStoppingTime _ (hTstop n)))))).mul
      (ENNReal.measurable_ofReal.comp (v.continuous.measurable.comp
        (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTstop n))))
  have hnonneg : ∀ n omega,
      0 ≤ Real.exp (-lam * (T n omega : ℝ)) * v (omega (T n omega)) := fun n omega ↦
    mul_nonneg (Real.exp_pos _).le (hv.1 _)
  have hint : ∀ n, Integrable (fun omega ↦
      Real.exp (-lam * (T n omega : ℝ)) * v (omega (T n omega))) Q := by
    intro n
    refine Integrable.of_bound (hrealMeas n).aestronglyMeasurable
      (Real.exp (|lam| * (n : ℝ)) * ‖v‖)
      (Eventually.of_forall fun omega ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-lam * (T n omega : ℝ)) * ‖v (omega (T n omega))‖
          ≤ Real.exp (-lam * (T n omega : ℝ)) * ‖v‖ :=
        mul_le_mul_of_nonneg_left (norm_c0_apply_le v _) (Real.exp_pos _).le
      _ ≤ Real.exp (|lam| * (n : ℝ)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr <| calc
          -lam * (T n omega : ℝ) ≤ |lam| * (T n omega : ℝ) :=
            mul_le_mul_of_nonneg_right (neg_le_abs lam) NNReal.zero_le_coe
          _ ≤ |lam| * (n : ℝ) :=
            mul_le_mul_of_nonneg_left
              (by exact_mod_cast hTle n omega) (abs_nonneg lam)) (norm_nonneg v)
  have hbound : ∀ n, ∫⁻ omega, g n omega ∂Q ≤ ENNReal.ofReal (v x) := by
    intro n
    have hreal : ∫⁻ omega, ENNReal.ofReal
        (Real.exp (-lam * (T n omega : ℝ)) * v (omega (T n omega))) ∂Q ≤
        ENNReal.ofReal (v x) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
        (Eventually.of_forall (hnonneg n))]
      exact ENNReal.ofReal_le_ofReal
        (hv.integral_discountedValueProcess_stoppingTime_le hP hFeller hK
          (T n) (hTstop n) (hTle n) x)
    simpa only [g, ENNReal.ofReal_mul (Real.exp_pos _).le] using hreal
  have htarget : ∀ omega : ContinuousPath alpha,
      ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
          (fun omega ↦
            ENNReal.ofReal (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
              ENNReal.ofReal (v (omega
                ((ContinuousPath.exitTime U omega).untopD 0)))) omega ≤
        liminf (fun n ↦ g n omega) atTop := by
    intro omega
    by_cases hfinite : ContinuousPath.exitTime U omega < ⊤
    · simp only [Set.indicator_of_mem (show omega ∈
          {omega | ContinuousPath.exitTime U omega < ⊤} from hfinite)]
      have hne : ContinuousPath.exitTime U omega ≠ ⊤ := ne_top_of_lt hfinite
      obtain ⟨N, hN⟩ := exists_nat_ge (ContinuousPath.exitTime U omega).toNNReal
      have hevent : ∀ᶠ n : ℕ in atTop,
          g n omega = ENNReal.ofReal
              (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
            ENNReal.ofReal (v (omega
              ((ContinuousPath.exitTime U omega).untopD 0))) := by
        filter_upwards [eventually_ge_atTop N] with n hn
        have htime : T n omega = (ContinuousPath.exitTime U omega).untopD 0 :=
          exitTimeTrunc_eq_untopD_of_le U omega hne (hN.trans (by exact_mod_cast hn))
        dsimp only [g]
        rw [htime]
        rw [show (((ContinuousPath.exitTime U omega).untopD (0 : NNReal) : NNReal) : ℝ) =
          (ContinuousPath.exitTime U omega).toReal by
            rw [← ENNReal.coe_toNNReal hne]
            rfl]
      have htend : Tendsto (fun n ↦ g n omega) atTop
          (𝓝 (ENNReal.ofReal
              (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
            ENNReal.ofReal (v (omega
              ((ContinuousPath.exitTime U omega).untopD 0))))) :=
        tendsto_const_nhds.congr' (hevent.mono fun _ hn ↦ hn.symm)
      exact le_of_eq htend.liminf_eq.symm
    · simp only [Set.indicator_of_notMem (show omega ∉
          {omega | ContinuousPath.exitTime U omega < ⊤} from hfinite)]
      exact zero_le
  calc
    ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
          (fun omega ↦
            ENNReal.ofReal (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
              ENNReal.ofReal (v (omega
                ((ContinuousPath.exitTime U omega).untopD 0)))) omega ∂Q
        ≤ ∫⁻ omega, liminf (fun n ↦ g n omega) atTop ∂Q := lintegral_mono htarget
    _ ≤ liminf (fun n ↦ ∫⁻ omega, g n omega ∂Q) atTop := lintegral_liminf_le hgMeas
    _ ≤ ENNReal.ofReal (v x) :=
      liminf_le_of_frequently_le' (Frequently.of_forall hbound)
