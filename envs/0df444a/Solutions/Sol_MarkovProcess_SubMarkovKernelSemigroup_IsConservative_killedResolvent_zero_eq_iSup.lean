-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedResolvent_zero_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:37:31.973702+00:00
-- url     : https://prove2.me/submissions/e8976ef2-2714-487d-8ac5-d31bece05532

import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_measurable_killedKernel

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying the expected exit time with a Dirichlet resolvent

The killed resolvent of the constant function one at the shift zero is the expected exit time,

  `E_x τ_U = R^U_0 1 (x)`  (`IsConservative.lintegral_exitTime_eq_killedResolvent_zero`),

and the shift zero is the increasing limit of the positive shifts `1 / (n + 1)`
(`IsConservative.killedResolvent_zero_eq_iSup`).  Both statements are unconditional.

Consumers who identify the killed resolvent at positive shifts with an analytically defined
Dirichlet resolvent `RU` then read the expected exit time off the limit of `RU`
(`IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq`): the identification enters only as a
hypothesis, so nothing here depends on how it is established.  Two one-sided corollaries are
recorded, an upper bound from a uniform upper bound on the limit
(`IsConservative.lintegral_exitTime_le_of_killedResolvent_eq`) and a lower bound on a subset from a
uniform lower bound there (`IsConservative.le_lintegral_exitTime_of_killedResolvent_eq`).

The limit of `RU` enters those statements as a supremum along the shifts `1 / (n + 1)`.  A
consumer who instead has a limit as the shift decreases to zero converts it with
`IsConservative.iSup_eq_of_tendsto_nhdsGT_zero`: the killed resolvent is antitone in the shift, so
the identification makes `RU` antitone on `U` too and the sequence increases to its limit.

The consumer-supplied resolvent and its limit are `ℝ≥0∞`-valued, so no integrability or finiteness
hypothesis appears; a consumer working with real-valued solutions bridges with `ENNReal.ofReal`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

/-- The exponential discounts at the shifts `1 / (n + 1)` increase to one on the nonnegative
half-line. -/
private theorem iSup_ofReal_exp_neg_inv_mul (t : ℝ) (ht : 0 ≤ t) :
    ⨆ n : ℕ, ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) = 1 := by
  have hmono : Monotone fun n : ℕ ↦ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) := by
    intro m n hmn
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    refine mul_le_mul_of_nonneg_right ?_ ht
    refine neg_le_neg ?_
    exact inv_anti₀ (by positivity) (add_le_add (Nat.cast_le.mpr hmn) le_rfl)
  have hzero : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simp_rw [one_div] at h
    exact h
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t))) atTop
      (𝓝 1) := by
    have hreal : Tendsto (fun n : ℕ ↦ Real.exp (-((n : ℝ) + 1)⁻¹ * t)) atTop
        (𝓝 (Real.exp (-(0 : ℝ) * t))) :=
      (Real.continuous_exp.tendsto _).comp (((hzero.neg).mul_const t))
    have h := ENNReal.tendsto_ofReal hreal
    simpa only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one] using h
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono) hlim

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)





variable (RU : ℝ → alpha → ℝ≥0∞) (w : alpha → ℝ≥0∞)









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
# Identifying the expected exit time with a Dirichlet resolvent

The killed resolvent of the constant function one at the shift zero is the expected exit time,

  `E_x τ_U = R^U_0 1 (x)`  (`IsConservative.lintegral_exitTime_eq_killedResolvent_zero`),

and the shift zero is the increasing limit of the positive shifts `1 / (n + 1)`
(`IsConservative.killedResolvent_zero_eq_iSup`).  Both statements are unconditional.

Consumers who identify the killed resolvent at positive shifts with an analytically defined
Dirichlet resolvent `RU` then read the expected exit time off the limit of `RU`
(`IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq`): the identification enters only as a
hypothesis, so nothing here depends on how it is established.  Two one-sided corollaries are
recorded, an upper bound from a uniform upper bound on the limit
(`IsConservative.lintegral_exitTime_le_of_killedResolvent_eq`) and a lower bound on a subset from a
uniform lower bound there (`IsConservative.le_lintegral_exitTime_of_killedResolvent_eq`).

The limit of `RU` enters those statements as a supremum along the shifts `1 / (n + 1)`.  A
consumer who instead has a limit as the shift decreases to zero converts it with
`IsConservative.iSup_eq_of_tendsto_nhdsGT_zero`: the killed resolvent is antitone in the shift, so
the identification makes `RU` antitone on `U` too and the sequence increases to its limit.

The consumer-supplied resolvent and its limit are `ℝ≥0∞`-valued, so no integrability or finiteness
hypothesis appears; a consumer working with real-valued solutions bridges with `ENNReal.ofReal`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology





variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution (U : Set alpha) (hU : IsOpen U)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    IsConservative.killedResolvent P hP U hU 0 f x =
      ⨆ n : ℕ, IsConservative.killedResolvent P hP U hU ((n : ℝ) + 1)⁻¹ f x := by
  set G : ℝ → ℝ≥0∞ := fun t ↦
    ∫⁻ y, f y ∂(IsConservative.killedKernel P hP U hU (Real.toNNReal t) x) with hG
  have hGmeas : Measurable G := by
    refine (Measure.measurable_lintegral hf).comp ?_
    exact (IsConservative.measurable_killedKernel P hP U hU).comp
      (measurable_real_toNNReal.prodMk measurable_const)
  have hFmeas : ∀ n : ℕ,
      Measurable fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) * G t := by
    intro n
    exact (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id))).mul hGmeas
  have hFmono : ∀ t ∈ Set.Ioi (0 : ℝ),
      Monotone fun n : ℕ ↦ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) * G t := by
    intro t ht m n hmn
    refine mul_le_mul_left ?_ (G t)
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    refine mul_le_mul_of_nonneg_right (neg_le_neg ?_) (le_of_lt ht)
    exact inv_anti₀ (by positivity) (add_le_add (Nat.cast_le.mpr hmn) le_rfl)
  have hkey : ∀ t ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-0 * t)) * G t =
      ⨆ n : ℕ, ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) * G t := by
    intro t ht
    rw [← ENNReal.iSup_mul, iSup_ofReal_exp_neg_inv_mul t (le_of_lt ht)]
    simp only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one]
  calc
    IsConservative.killedResolvent P hP U hU 0 f x =
        ∫⁻ t in Set.Ioi (0 : ℝ), ⨆ n : ℕ,
          ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) * G t :=
      setLIntegral_congr_fun measurableSet_Ioi hkey
    _ = ⨆ n : ℕ, ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) * G t :=
      lintegral_iSup' (fun n ↦ (hFmeas n).aemeasurable)
        (ae_restrict_of_forall_mem measurableSet_Ioi hFmono)
    _ = ⨆ n : ℕ, IsConservative.killedResolvent P hP U hU ((n : ℝ) + 1)⁻¹ f x := rfl
