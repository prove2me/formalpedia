-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.dynkinProcess_eq_add_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:35:50.097055+00:00
-- url     : https://prove2.me/submissions/c414e1b9-e052-47c2-84a9-32ab32143dea

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Trajectory_DynkinMartingale_970781f3
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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

section C0Bound

variable {alpha : Type*} [TopologicalSpace alpha]



end C0Bound

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

section Definition



/-- The Dynkin process, written out. -/
theorem IsFellerKernelSemigroup.dynkinProcess_apply (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) (omega : ContinuousPath alpha) :
    hFeller.dynkinProcess f t omega =
      (f : C₀(alpha, ℝ)) (omega t) -
        ∫ s in (0 : ℝ)..t, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)) :=
  rfl

/-- The integrand of the Dynkin correction term is continuous in the time variable. -/
private theorem continuous_generator_path (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (omega : ContinuousPath alpha) :
    Continuous fun s : ℝ ↦ (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)) :=
  (hFeller.c0Semigroup.generator f).continuous.comp
    (omega.continuous.comp continuous_real_toNNReal)





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


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
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




variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}




namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (s t : NNReal) (hst : s ≤ t)
    (omega : ContinuousPath alpha) :
    hFeller.dynkinProcess f t omega =
      hFeller.dynkinProcess f s omega - (f : C₀(alpha, ℝ)) (omega s) +
        hFeller.dynkinProcess f (t - s) (ContinuousPath.shift s omega) := by
  have hcont := continuous_generator_path hFeller f omega
  have hshift : (∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (s + Real.toNNReal u))) =
      ∫ v in (s : ℝ)..(t : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal v)) := by
    have hcongr : (∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ),
          (hFeller.c0Semigroup.generator f) (omega (s + Real.toNNReal u))) =
        ∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ),
          (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal (u + s))) := by
      refine intervalIntegral.integral_congr fun u hu ↦ ?_
      have hu0 : (0 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le (t - s : NNReal).coe_nonneg] at hu
        exact hu.1
      have hcoe : Real.toNNReal (u + s) = s + Real.toNNReal u := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add, Real.coe_toNNReal u hu0,
          Real.coe_toNNReal _ (add_nonneg hu0 s.coe_nonneg)]
        ring
      rw [hcoe]
    rw [hcongr,
      intervalIntegral.integral_comp_add_right
        (fun v : ℝ ↦ (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal v))) (s : ℝ),
      zero_add]
    congr 1
    rw [NNReal.coe_sub hst]
    ring
  have hsplit : (∫ v in (0 : ℝ)..(s : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal v))) +
      (∫ v in (s : ℝ)..(t : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal v))) =
      ∫ v in (0 : ℝ)..(t : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal v)) :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  simp only [IsFellerKernelSemigroup.dynkinProcess_apply, ContinuousPath.shift_apply,
    add_tsub_cancel_of_le hst]
  rw [hshift]
  linarith only [hsplit]
