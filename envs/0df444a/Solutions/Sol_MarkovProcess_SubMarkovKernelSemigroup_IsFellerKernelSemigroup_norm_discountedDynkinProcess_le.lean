-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.norm_discountedDynkinProcess_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:37:38.877276+00:00
-- url     : https://prove2.me/submissions/ba502aca-b643-423d-a695-45662ad7e745

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



/-- The discounted Dynkin process, unfolded. -/
theorem IsFellerKernelSemigroup.discountedDynkinProcess_apply
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (t : NNReal) (omega : ContinuousPath alpha) :
    hFeller.discountedDynkinProcess f lam t omega =
      Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t) -
        ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) *
          (hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ)))
            (omega (Real.toNNReal s)) :=
  rfl



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










namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (t : NNReal) (omega : ContinuousPath alpha) :
    ‖hFeller.discountedDynkinProcess f lam t omega‖ ≤
      Real.exp (|lam| * (t : ℝ)) *
        (‖(f : C₀(alpha, ℝ))‖ + (t : ℝ) *
          ‖hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))‖) := by
  let g : C₀(alpha, ℝ) :=
    hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))
  have hexp : Real.exp (-lam * (t : ℝ)) ≤ Real.exp (|lam| * (t : ℝ)) :=
    exp_neg_mul_le_exp_abs_mul t.coe_nonneg le_rfl
  have hterm : ‖Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t)‖ ≤
      Real.exp (|lam| * (t : ℝ)) * ‖(f : C₀(alpha, ℝ))‖ := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul hexp (norm_c0_apply_le _ _) (norm_nonneg _) (Real.exp_pos _).le)
  have hint : ‖∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * g (omega (Real.toNNReal s))‖ ≤
      (t : ℝ) * (Real.exp (|lam| * (t : ℝ)) * ‖g‖) := by
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
  rw [hFeller.discountedDynkinProcess_apply]
  change ‖_ - ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * g (omega (Real.toNNReal s))‖ ≤ _
  calc
    ‖_ - ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * g (omega (Real.toNNReal s))‖
        ≤ _ := norm_sub_le _ _
    _ ≤ Real.exp (|lam| * (t : ℝ)) * ‖(f : C₀(alpha, ℝ))‖ +
          (t : ℝ) * (Real.exp (|lam| * (t : ℝ)) * ‖g‖) := add_le_add hterm hint
    _ = Real.exp (|lam| * (t : ℝ)) *
          (‖(f : C₀(alpha, ℝ))‖ + (t : ℝ) * ‖g‖) := by ring
