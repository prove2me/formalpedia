-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.isConservative_of_kernelResolvent_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:42:45.067632+00:00
-- url     : https://prove2.me/submissions/83da38b9-d429-4234-af88-21e20276a217

import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
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
# Sub-Markov transition-kernel semigroups

This file packages jointly measurable, nonnegative-time transition kernels with
the Chapman--Kolmogorov law.  Mathlib writes `η.comp κ` for first applying `κ`
and then `η`; consequently the law below is `K (s + t) = (K t).comp (K s)`.

Conservativity is deliberately a separate predicate.  A killed transition
family has mass at most one, while a conservative family has mass exactly one.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace MarkovProcess

open MeasureTheory ProbabilityTheory



namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]





variable (P : SubMarkovKernelSemigroup α)













/-- Chapman--Kolmogorov evaluated on a measurable set. -/
theorem add_apply' (s t : NNReal) (x : α) {u : Set α} (hu : MeasurableSet u) :
    P (s + t) x u = ∫⁻ y, P t y u ∂P s x := by
  rw [P.add, Kernel.comp_apply' _ _ _ hu]









namespace IsConservative



end IsConservative

end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conservativity from the resolvent of the constant observable

A sub-Markov kernel semigroup loses no mass as soon as its resolvent at one positive shift has
the full mass of the exponential weight,

  `lam * R_lam 1 = 1`   (`SubMarkovKernelSemigroup.isConservative_of_kernelResolvent_one`).

The transition mass is nonincreasing in time (`SubMarkovKernelSemigroup.measure_univ_le_of_le`),
because the Chapman--Kolmogorov law integrates a mass at most one against an earlier transition
law.  The hypothesis says that the Laplace transform of the transition mass equals the Laplace
transform of the constant observable one; both integrands are integrable and ordered, so they
agree at almost every time, and monotonicity in time upgrades this to every time.

The converse is immediate from the mass of the exponential weight
(`SubMarkovKernelSemigroup.IsConservative.kernelResolvent_one`,
`SubMarkovKernelSemigroup.IsConservative.ofReal_mul_kernelResolvent_one`), so the criterion is an
equivalence and not merely a sufficient condition.

No topology on the state space is used.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MeasurableSpace alpha] (P : SubMarkovKernelSemigroup alpha)

/-- **The transition mass is nonincreasing in time.**  A later transition law is an average of
transition masses at most one against an earlier one. -/
theorem measure_univ_le_of_le {u v : NNReal} (huv : u ≤ v) (x : alpha) :
    P v x univ ≤ P u x univ := by
  obtain ⟨w, rfl⟩ := exists_add_of_le huv
  rw [P.add_apply' u w x MeasurableSet.univ]
  calc ∫⁻ y, P w y univ ∂P u x ≤ ∫⁻ _y, 1 ∂P u x :=
        lintegral_mono fun y ↦ P.measure_univ_le_one w y
    _ = P u x univ := lintegral_one

/-- The Laplace transform of the constant observable one at a positive shift. -/
theorem lintegral_expWeight_one {lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) = ENNReal.ofReal lam⁻¹ := by
  have hmass : ∫⁻ _t : ℝ, (1 : ℝ≥0∞) ∂laplaceWeight lam = laplaceWeight lam univ :=
    lintegral_one
  have hweight : ∫⁻ _t : ℝ, (1 : ℝ≥0∞) ∂laplaceWeight lam =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) * 1 :=
    lintegral_laplaceWeight lam measurable_const
  simp only [mul_one] at hweight
  rw [← hweight, hmass, laplaceWeight_univ hlam]







end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conservativity from the resolvent of the constant observable

A sub-Markov kernel semigroup loses no mass as soon as its resolvent at one positive shift has
the full mass of the exponential weight,

  `lam * R_lam 1 = 1`   (`SubMarkovKernelSemigroup.isConservative_of_kernelResolvent_one`).

The transition mass is nonincreasing in time (`SubMarkovKernelSemigroup.measure_univ_le_of_le`),
because the Chapman--Kolmogorov law integrates a mass at most one against an earlier transition
law.  The hypothesis says that the Laplace transform of the transition mass equals the Laplace
transform of the constant observable one; both integrands are integrable and ordered, so they
agree at almost every time, and monotonicity in time upgrades this to every time.

The converse is immediate from the mass of the exponential weight
(`SubMarkovKernelSemigroup.IsConservative.kernelResolvent_one`,
`SubMarkovKernelSemigroup.IsConservative.ofReal_mul_kernelResolvent_one`), so the criterion is an
equivalence and not merely a sufficient condition.

No topology on the state space is used.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [MeasurableSpace alpha] (P : SubMarkovKernelSemigroup alpha)





namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
theorem solution {lam : ℝ} (hlam : 0 < lam)
    (hone : ∀ x, ENNReal.ofReal lam * P.kernelResolvent lam (fun _ ↦ 1) x = 1) :
    P.IsConservative := by
  have hlam0 : ENNReal.ofReal lam ≠ 0 := by
    simpa using hlam
  have hlamtop : ENNReal.ofReal lam ≠ ⊤ := ENNReal.ofReal_ne_top
  intro t x
  -- the resolvent of the constant observable one carries the full weight
  have hmass : P.kernelResolvent lam (fun _ ↦ 1) x = ENNReal.ofReal lam⁻¹ := by
    have hcancel : (ENNReal.ofReal lam)⁻¹ *
        (ENNReal.ofReal lam * P.kernelResolvent lam (fun _ ↦ 1) x) =
        P.kernelResolvent lam (fun _ ↦ 1) x := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hlam0 hlamtop, one_mul]
    rw [← hcancel, hone x, mul_one, ← ENNReal.ofReal_inv_of_pos hlam]
  -- the two integrands: the weighted transition mass and the weight itself
  have hprofile : P.kernelResolvent lam (fun _ ↦ 1) x =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s)) * P (Real.toNNReal s) x univ := by
    unfold kernelResolvent
    exact setLIntegral_congr_fun measurableSet_Ioi fun s _hs ↦ by rw [lintegral_one]
  have hle : ∀ s : ℝ, ENNReal.ofReal (Real.exp (-lam * s)) * P (Real.toNNReal s) x univ ≤
      ENNReal.ofReal (Real.exp (-lam * s)) := by
    intro s
    calc ENNReal.ofReal (Real.exp (-lam * s)) * P (Real.toNNReal s) x univ
        ≤ ENNReal.ofReal (Real.exp (-lam * s)) * 1 :=
          mul_le_mul' le_rfl (P.measure_univ_le_one _ x)
      _ = ENNReal.ofReal (Real.exp (-lam * s)) := mul_one _
  have hFtop : (∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-lam * s)) * P (Real.toNNReal s) x univ) ≠ ⊤ := by
    rw [← hprofile, hmass]
    exact ENNReal.ofReal_ne_top
  have hGF : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s))) ≤
      ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-lam * s)) * P (Real.toNNReal s) x univ := by
    rw [← hprofile, hmass, lintegral_expWeight_one hlam]
  have hFG := ae_eq_of_ae_le_of_lintegral_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (Eventually.of_forall hle) hFtop (measurable_laplaceDensity lam).aemeasurable hGF
  -- almost every positive time carries the full mass
  have hae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), P (Real.toNNReal s) x univ = 1 := by
    filter_upwards [hFG] with s hs
    have hpos : ENNReal.ofReal (Real.exp (-lam * s)) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.exp_pos _
    refine (ENNReal.mul_right_inj hpos ENNReal.ofReal_ne_top).mp ?_
    rw [hs, mul_one]
  -- a later time with the full mass forces the full mass at the given time
  have hinterval : MeasurableSet (Ioo ((t : ℝ) + 1) ((t : ℝ) + 2)) := measurableSet_Ioo
  have hsub : Ioo ((t : ℝ) + 1) ((t : ℝ) + 2) ⊆ Ioi (0 : ℝ) := fun s hs ↦
    lt_trans (by positivity) hs.1
  have haeI : ∀ᵐ s ∂(volume.restrict (Ioo ((t : ℝ) + 1) ((t : ℝ) + 2))),
      P (Real.toNNReal s) x univ = 1 :=
    ae_mono (Measure.restrict_mono hsub le_rfl) hae
  have hne : volume.restrict (Ioo ((t : ℝ) + 1) ((t : ℝ) + 2)) ≠ 0 := by
    intro hzero
    have hmeasure : volume.restrict (Ioo ((t : ℝ) + 1) ((t : ℝ) + 2))
        (Ioo ((t : ℝ) + 1) ((t : ℝ) + 2)) = 0 := by
      rw [hzero]
      rfl
    rw [Measure.restrict_apply_self, Real.volume_Ioo] at hmeasure
    exact absurd hmeasure (by
      simp only [add_sub_add_left_eq_sub, ENNReal.ofReal_eq_zero, tsub_le_iff_right, zero_add,
        Nat.not_ofNat_le_one, not_false_eq_true])
  have : (ae (volume.restrict (Ioo ((t : ℝ) + 1) ((t : ℝ) + 2)))).NeBot :=
    ae_neBot.mpr hne
  obtain ⟨s, hsone, hsmem⟩ := (haeI.and (self_mem_ae_restrict hinterval)).exists
  have hts : t ≤ Real.toNNReal s := by
    have hcoe : Real.toNNReal (t : ℝ) = t := Real.toNNReal_coe
    rw [← hcoe]
    exact Real.toNNReal_le_toNNReal (le_of_lt (lt_trans (by linarith) hsmem.1))
  refine le_antisymm (P.measure_univ_le_one t x) ?_
  calc (1 : ℝ≥0∞) = P (Real.toNNReal s) x univ := hsone.symm
    _ ≤ P t x univ := P.measure_univ_le_of_le hts x
