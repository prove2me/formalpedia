-- Prove2me | solution 1 for MarkovProcess.expWeight_convolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:28:35.515744+00:00
-- url     : https://prove2.me/submissions/38004e91-d6ed-43fd-a6d3-3dc9203d13ec

import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
import Definitions.Def_MarkovProcess_V3H_Killed_GluingResolventEquation_b19dddc8
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The resolvent equation for a kernel resolvent

The kernel resolvent of a sub-Markov kernel semigroup satisfies the resolvent equation

  `R_lam f = R_mu f + (mu - lam) R_lam (R_mu f)`   for `0 < lam < mu`

(`SubMarkovKernelSemigroup.kernelResolvent_resolventEquation`), as an identity of
extended-nonnegative-real valued observables, so no integrability hypothesis is needed.  The proof
is the convolution identity for exponential weights

  `e^{-mu u} + (mu - lam) ∫_0^u e^{-lam s} e^{-mu (u - s)} ds = e^{-lam u}`

(`expWeight_convolution`) together with the Chapman--Kolmogorov law, which turns the composition
of the two resolvents into a convolution in time.

Main definitions: `expWeight`.

The same double-integral form is symmetric in the two shifts, so the two resolvents commute
(`SubMarkovKernelSemigroup.kernelResolvent_comm`).

Main results: `expWeight_convolution`,
`SubMarkovKernelSemigroup.kernelResolvent_eq_lintegral_expWeight`,
`SubMarkovKernelSemigroup.kernelResolvent_comp_eq_lintegral`,
`SubMarkovKernelSemigroup.kernelResolvent_comm`,
`SubMarkovKernelSemigroup.kernelResolvent_resolventEquation`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess













namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MeasurableSpace alpha] (P : SubMarkovKernelSemigroup alpha)

















end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The resolvent equation for a kernel resolvent

The kernel resolvent of a sub-Markov kernel semigroup satisfies the resolvent equation

  `R_lam f = R_mu f + (mu - lam) R_lam (R_mu f)`   for `0 < lam < mu`

(`SubMarkovKernelSemigroup.kernelResolvent_resolventEquation`), as an identity of
extended-nonnegative-real valued observables, so no integrability hypothesis is needed.  The proof
is the convolution identity for exponential weights

  `e^{-mu u} + (mu - lam) ∫_0^u e^{-lam s} e^{-mu (u - s)} ds = e^{-lam u}`

(`expWeight_convolution`) together with the Chapman--Kolmogorov law, which turns the composition
of the two resolvents into a convolution in time.

Main definitions: `expWeight`.

The same double-integral form is symmetric in the two shifts, so the two resolvents commute
(`SubMarkovKernelSemigroup.kernelResolvent_comm`).

Main results: `expWeight_convolution`,
`SubMarkovKernelSemigroup.kernelResolvent_eq_lintegral_expWeight`,
`SubMarkovKernelSemigroup.kernelResolvent_comp_eq_lintegral`,
`SubMarkovKernelSemigroup.kernelResolvent_comm`,
`SubMarkovKernelSemigroup.kernelResolvent_resolventEquation`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal













namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution {lam mu : ℝ} (hlt : lam < mu) (u : ℝ) :
    expWeight mu u + ENNReal.ofReal (mu - lam) *
        ∫⁻ s, expWeight lam s * expWeight mu (u - s) = expWeight lam u := by
  have hc : (0 : ℝ) < mu - lam := sub_pos.mpr hlt
  have hind : (fun s ↦ expWeight lam s * expWeight mu (u - s)) =
      (Set.Ioo (0 : ℝ) u).indicator
        (fun s ↦ ENNReal.ofReal (Real.exp (-mu * u + (mu - lam) * s))) := by
    funext s
    by_cases hs : s ∈ Set.Ioo (0 : ℝ) u
    · rw [Set.indicator_of_mem hs, expWeight_of_pos hs.1,
        expWeight_of_pos (sub_pos.mpr hs.2), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]
      congr 2
      ring
    · rw [Set.indicator_of_notMem hs]
      rcases le_or_gt s 0 with h | h
      · rw [expWeight_of_nonpos h, zero_mul]
      · have h2 : u ≤ s := by
          by_contra hcon
          exact hs ⟨h, lt_of_not_ge hcon⟩
        rw [expWeight_of_nonpos (sub_nonpos.mpr h2), mul_zero]
  rw [hind, lintegral_indicator measurableSet_Ioo]
  rcases le_or_gt u 0 with hu | hu
  · rw [expWeight_of_nonpos hu, expWeight_of_nonpos hu,
      Set.Ioo_eq_empty (not_lt.mpr hu)]
    simp only [Measure.restrict_empty, neg_mul, lintegral_zero_measure, mul_zero, add_zero]
  · have hcont : Continuous fun s : ℝ ↦ Real.exp (-mu * u + (mu - lam) * s) := by fun_prop
    have hint : IntegrableOn (fun s : ℝ ↦ Real.exp (-mu * u + (mu - lam) * s))
        (Set.Ioo (0 : ℝ) u) :=
      ((hcont.intervalIntegrable 0 u).1).mono_set Set.Ioo_subset_Ioc_self
    have hval : ∫ s in Set.Ioo (0 : ℝ) u, Real.exp (-mu * u + (mu - lam) * s) =
        (Real.exp (-lam * u) - Real.exp (-mu * u)) / (mu - lam) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu.le]
      have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) u, HasDerivAt
          (fun s : ℝ ↦ Real.exp (-mu * u + (mu - lam) * s) / (mu - lam))
          (Real.exp (-mu * u + (mu - lam) * s)) s := by
        intro s _
        have h1 : HasDerivAt (fun s : ℝ ↦ -mu * u + (mu - lam) * s) (mu - lam) s := by
          simpa using ((hasDerivAt_id s).const_mul (mu - lam)).const_add (-mu * u)
        have h2 := (h1.exp).div_const (mu - lam)
        simpa only [neg_mul, mul_div_cancel_right₀ _ hc.ne'] using h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 u)]
      have hexp : Real.exp (-mu * u + (mu - lam) * u) = Real.exp (-lam * u) := by
        congr 1
        ring
      rw [hexp]
      simp only [mul_zero, add_zero]
      ring
    have hmul : (mu - lam) * ((Real.exp (-lam * u) - Real.exp (-mu * u)) / (mu - lam)) =
        Real.exp (-lam * u) - Real.exp (-mu * u) := by
      field_simp
    have hnn : 0 ≤ Real.exp (-lam * u) - Real.exp (-mu * u) := by
      have hle : -mu * u ≤ -lam * u := by nlinarith only [hlt, hu]
      exact sub_nonneg.mpr (Real.exp_le_exp.mpr hle)
    rw [expWeight_of_pos hu, expWeight_of_pos hu,
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun s ↦ (Real.exp_pos _).le),
      hval, ← ENNReal.ofReal_mul hc.le, hmul,
      ← ENNReal.ofReal_add (Real.exp_pos _).le hnn]
    congr 1
    ring
