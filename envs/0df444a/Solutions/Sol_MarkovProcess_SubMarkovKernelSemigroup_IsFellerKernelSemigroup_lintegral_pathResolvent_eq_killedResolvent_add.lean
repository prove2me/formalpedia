-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.lintegral_pathResolvent_eq_killedResolvent_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:26:08.252398+00:00
-- url     : https://prove2.me/submissions/5b27957e-7f29-4a5a-9985-b04c92f53d6b

import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExitLaw_2add356d
import Definitions.Def_MarkovProcess_V3H_Trajectory_ResolventExitDecomposition_db489119
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
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
import Theorems.Thm_MarkovProcess_ContinuousPath_survivalSet_ne_top
import Theorems.Thm_MarkovProcess_StoppingTime_lintegral_mul_indicator_of_restrict_map
import Theorems.Thm_MarkovProcess_StoppingTime_measurableSet_stoppingTime_lt_top
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_killedResolvent_eq_lintegral
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuousProcess_restrict_map_shift_stoppingTime_lt_top

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

/-- The survival set below an infinite extended horizon is the positive half-line. -/
theorem survivalSet_top :
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ⊤} ∩ Set.Ioi 0 = Set.Ioi 0 := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioi]
  exact and_iff_right ENNReal.coe_lt_top





end SurvivalSets

variable {alpha : Type*} [PseudoMetricSpace alpha]

section Order











end Order

section WithTopValue











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
# Measurability of random shifts of continuous paths

Shifting a continuous path by a Borel measurable random time, and evaluating it at that time,
are Borel measurable, because the deterministic shift and the evaluation are jointly continuous
in the time and the path.  A finite `NNReal`-valued stopping time for the canonical filtration is
such a random time.  No countable-range premise is used.

This is ordinary measurability infrastructure.  It proves no restart identity and no conditional
expectation formula; those are in `Trajectory/FellerStoppingRestart.lean` and
`Trajectory/FellerStoppingConditional.lean`.
-/

open MeasureTheory

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Shifting by a Borel measurable random time is Borel measurable. -/
theorem measurable_shift_of_measurable (T : ContinuousPath alpha → NNReal)
    (hT : Measurable T) :
    Measurable (fun omega ↦ shift (T omega) omega) := by
  have hpair : Measurable (fun omega : ContinuousPath alpha ↦ (T omega, omega)) :=
    hT.prodMk measurable_id
  exact (continuous_shift (alpha := alpha)).measurable.comp hpair

variable [MeasurableSpace alpha] [BorelSpace alpha]









end ContinuousPath
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The strong Markov property at a stopping time that may be infinite

Mathlib's stopping times take values in `WithTop ℝ≥0`, so a stopping time of the canonical
filtration on continuous-path space may be infinite, while the strong Markov property of
`MarkovProcess/Main.lean` is stated for finite, `ℝ≥0`-valued stopping times.  This file removes
that restriction on the event `{tau < ⊤}` where the time is finite, writing the finite value as
`(tau omega).untopD 0`:

* `IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top`: the
  restart identity, after restricting the law of the process to `A ∩ {tau < ⊤}` for an event `A`
  of the stopped sigma-algebra;
* `IsFellerKernelSemigroup.continuousProcess_condExp_shift_stoppingTime_lt_top`: the same fact
  in conditional-expectation form, for a bounded strongly measurable functional of the shifted
  path, with the indicator of `{tau < ⊤}` on both sides.
* `StoppingTime.lintegral_mul_indicator_of_restrict_map`: integration of a restricted restart
  identity against a nonnegative weight measurable at the conditioning sigma-algebra.

The route is truncation: `truncTime tau K` is the finite stopping time `min tau K`, and the
slices `stoppingTimeSlice A tau K` partition `A ∩ {tau < ⊤}` into countably many events on which
`tau` is finite and bounded by `K`.  On each slice the finite theorems of `Main.lean` apply, and
both sides of the restart identity are countably additive in the restricted measure; the
conditional-expectation form is then obtained from the slicewise restart identity through a
generic indicator bridge, `condExp_indicator_ae_eq_integral_kernel_of_restrict_map`.

Nothing is asserted about the event `{tau = ⊤}`: on it the shifted path is the path itself, and
neither statement constrains it.  No Hunt-process property is claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Function

namespace MarkovProcess

/-! Generic stopping-time material: truncation at a deterministic horizon, the countable slicing
of the event where a `WithTop`-valued stopping time is finite, and the reassembly of restart
identities over the slices.  Nothing here is specific to path space. -/

namespace StoppingTime

section RestrictedRestartIntegral

variable {Omega beta : Type*} {m mOmega : MeasurableSpace Omega}
  {mBeta : MeasurableSpace beta}



end RestrictedRestartIntegral

section Trunc

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}













end Trunc

section Slices

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {f : Filtration NNReal mOmega}
  {tau : Omega → WithTop NNReal}

















end Slices

section Reassembly

variable {Omega beta : Type*} [MeasurableSpace Omega] [MeasurableSpace beta]



end Reassembly

end StoppingTime

open StoppingTime

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]
  [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]



omit [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha] in
/-- Shifting a path by the untopped value of a stopping time of the canonical filtration is
Borel measurable. -/
theorem measurable_shift_untopD_stoppingTime (tau : ContinuousPath alpha → WithTop NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha)) tau) :
    Measurable (fun omega ↦ shift ((tau omega).untopD 0) omega) :=
  measurable_shift_of_measurable _ (measurable_untopD_stoppingTime tau htau)





end ContinuousPath

namespace StoppingTime

section Bridge

variable {Omega beta E : Type*} {m : MeasurableSpace Omega}
  {mOmega : MeasurableSpace Omega} {mBeta : MeasurableSpace beta}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]





end Bridge

end StoppingTime

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]



end

end SubMarkovKernelSemigroup

end MarkovProcess


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



omit [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
/-- The path resolvent is measurable when its observable is measurable. -/
theorem measurable_pathResolvent (lam : ℝ) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) : Measurable (pathResolvent lam f) := by
  have heval : Measurable fun p : ℝ × ContinuousPath alpha ↦ p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hjoint : Measurable (fun p : ℝ × ContinuousPath alpha ↦
      ENNReal.ofReal (Real.exp (-lam * p.1)) * f (p.2 (Real.toNNReal p.1))) := by
    exact (ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_fst)).mul (hf.comp heval)
  exact hjoint.lintegral_prod_left' (μ := volume.restrict (Set.Ioi 0))

end

end ContinuousPath

namespace SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



/-- Translation of a nonnegative Lebesgue integral on a right half-line. -/
private theorem lintegral_comp_add_right_Ioi (h : ℝ → ℝ≥0∞) (A : ℝ) :
    ∫⁻ s in Set.Ioi (0 : ℝ), h (s + A) = ∫⁻ t in Set.Ioi A, h t := by
  have hcv := (MeasureTheory.measurePreserving_add_right volume A).setLIntegral_comp_emb
    (measurableEmbedding_addRight A) h (Set.Ioi (0 : ℝ))
  simpa only [zero_add, Set.image_add_const_Ioi] using hcv

/-- A nonnegative integral on the positive half-line splits at a nonnegative time. -/
private theorem lintegral_Ioi_zero_eq_Ioo_add_Ioi (h : ℝ → ℝ≥0∞) (A : ℝ) (hA : 0 ≤ A) :
    ∫⁻ t in Set.Ioi (0 : ℝ), h t =
      (∫⁻ t in Set.Ioo (0 : ℝ) A, h t) + ∫⁻ t in Set.Ioi A, h t := by
  rcases hA.eq_or_lt with rfl | hA
  · simp only [lt_self_iff_false, not_false_eq_true, Ioo_eq_empty, Measure.restrict_empty,
      lintegral_zero_measure, zero_add]
  · rw [show volume.restrict (Set.Ioi A) = volume.restrict (Set.Ici A) from
      Measure.restrict_congr_set Ioi_ae_eq_Ici]
    rw [← lintegral_union measurableSet_Ici
      ((Iio_disjoint_Ici le_rfl).mono Set.Ioo_subset_Iio_self le_rfl)]
    rw [Set.Ioo_union_Ici_eq_Ioi hA]

omit [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
/-- Pathwise splitting of discounted occupation into the part before exit and the shifted tail. -/
private theorem pathResolvent_eq_preExit_add_restart
    (U : Set alpha) (lam : ℝ) (f : alpha → ℝ≥0∞)
    (omega : ContinuousPath alpha) :
    ContinuousPath.pathResolvent lam f omega =
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
          ContinuousPath.exitTime U omega}.indicator
          (fun t ↦ f (omega (Real.toNNReal t))) t) +
      ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦ ENNReal.ofReal
            (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
          ContinuousPath.pathResolvent lam f
            (ContinuousPath.shift ((ContinuousPath.exitTime U omega).untopD 0) omega)) omega := by
  let tau := ContinuousPath.exitTime U omega
  let H : ℝ → ℝ≥0∞ := fun t ↦
    ENNReal.ofReal (Real.exp (-lam * t)) * f (omega (Real.toNNReal t))
  let T : Set ℝ := {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}
  have hfun : (fun t ↦ ENNReal.ofReal (Real.exp (-lam * t)) *
        T.indicator (fun t ↦ f (omega (Real.toNNReal t))) t) = T.indicator H := by
    funext t
    by_cases ht : t ∈ T
    · simp only [neg_mul, Set.indicator_of_mem ht, H]
    · simp only [neg_mul, Set.indicator_of_notMem ht, mul_zero, H]
  by_cases htau : tau = ⊤
  · have hnot : omega ∉ {omega | ContinuousPath.exitTime U omega < ⊤} := by
      change ¬tau < ⊤
      rw [htau]
      exact lt_irrefl _
    rw [Set.indicator_of_notMem hnot, add_zero]
    change (∫⁻ t in Set.Ioi (0 : ℝ), H t) = _
    rw [hfun, setLIntegral_indicator]
    · have hT : T ∩ Set.Ioi (0 : ℝ) = Set.Ioi 0 := by
        change {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau} ∩ Set.Ioi 0 = _
        rw [htau]
        exact ContinuousPath.survivalSet_top
      rw [hT]
    · exact measurableSet_lt
        (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal) measurable_const
  · lift tau to NNReal using htau with a ha
    have htau' : tau ≠ ⊤ := by rw [← ha]; exact WithTop.coe_ne_top
    have haReal : tau.toReal = (a : ℝ) := by rw [← ha]; simp only [ENNReal.coe_toReal]
    have hmem : omega ∈ {omega | ContinuousPath.exitTime U omega < ⊤} := by
      change tau < ⊤
      rw [← ha]
      exact WithTop.coe_lt_top a
    rw [Set.indicator_of_mem hmem]
    change (∫⁻ t in Set.Ioi (0 : ℝ), H t) = _
    have hpre : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
          T.indicator (fun t ↦ f (omega (Real.toNNReal t))) t) =
        ∫⁻ t in Set.Ioo (0 : ℝ) (a : ℝ), H t := by
      rw [hfun, setLIntegral_indicator]
      · rw [ContinuousPath.survivalSet_ne_top tau htau', haReal]
      · exact measurableSet_lt
          (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal) measurable_const
    rw [lintegral_Ioi_zero_eq_Ioo_add_Ioi H (a : ℝ) a.coe_nonneg]
    congr 1
    · exact hpre.symm
    · rw [← lintegral_comp_add_right_Ioi H (a : ℝ)]
      have hexit : ContinuousPath.exitTime U omega = (a : ℝ≥0∞) := ha.symm
      rw [hexit]
      simp only [ENNReal.coe_toReal]
      change (∫⁻ s in Set.Ioi (0 : ℝ), H (s + (a : ℝ))) =
        ENNReal.ofReal (Real.exp (-lam * (a : ℝ))) *
          (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s)) *
            f (ContinuousPath.shift a omega (Real.toNNReal s)))
      have hweight_ne_top : ENNReal.ofReal (Real.exp (-lam * (a : ℝ))) ≠ ⊤ :=
        ENNReal.ofReal_ne_top
      rw [← lintegral_const_mul'
        (ENNReal.ofReal (Real.exp (-lam * (a : ℝ)))) _
        hweight_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
      have hs0 : 0 ≤ s := (Set.mem_Ioi.mp hs).le
      simp only [H, ContinuousPath.shift_apply]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      have hexp : -lam * (s + (a : ℝ)) = -lam * (a : ℝ) + -lam * s := by ring
      rw [hexp]
      congr 1
      rw [Real.toNNReal_add hs0 a.coe_nonneg, Real.toNNReal_of_nonneg a.coe_nonneg]
      apply congrArg (fun u : NNReal ↦ f (omega u))
      exact add_comm (Real.toNNReal s) a



end

end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
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





variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)









namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (lam : ℝ)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    ∫⁻ omega, ContinuousPath.pathResolvent lam f omega
        ∂(IsConservative.continuousProcess P hP x) =
      IsConservative.killedResolvent P hP U hU lam f x +
        ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
          (fun omega ↦ ENNReal.ofReal
              (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
            (∫⁻ eta, ContinuousPath.pathResolvent lam f eta
              ∂(IsConservative.continuousProcess P hP
                (omega ((ContinuousPath.exitTime U omega).untopD 0))))) omega
          ∂(IsConservative.continuousProcess P hP x) := by
  let Q : Kernel alpha (ContinuousPath alpha) := IsConservative.continuousProcess P hP
  let tau : ContinuousPath alpha → ℝ≥0∞ := ContinuousPath.exitTime U
  let S : Set (ContinuousPath alpha) := {omega | tau omega < ⊤}
  let W : ContinuousPath alpha → ℝ≥0∞ := fun omega ↦
    ENNReal.ofReal (Real.exp (-lam * (tau omega).toReal))
  let F : ContinuousPath alpha → ℝ≥0∞ := ContinuousPath.pathResolvent lam f
  have htau := ContinuousPath.isStoppingTime_exitTime U hU
  have hS : MeasurableSet[htau.measurableSpace] S := by
    exact StoppingTime.measurableSet_stoppingTime_lt_top htau
  have hW : Measurable[htau.measurableSpace] W := by
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (ENNReal.measurable_toReal.comp htau.measurable)))
  have hF : Measurable F := ContinuousPath.measurable_pathResolvent lam hf
  have hPre : Measurable (fun omega : ContinuousPath alpha ↦
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau omega}.indicator
          (fun t ↦ f (omega (Real.toNNReal t))) t) := by
    have heval : Measurable fun p : ℝ × ContinuousPath alpha ↦
        p.2 (Real.toNNReal p.1) :=
      (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
    have hset : MeasurableSet {p : ℝ × ContinuousPath alpha |
        ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < tau p.2} :=
      measurableSet_lt
        (measurable_coe_nnreal_ennreal.comp
          (measurable_real_toNNReal.comp measurable_fst))
        ((ContinuousPath.measurable_exitTime U hU).comp measurable_snd)
    have hjoint : Measurable (fun p : ℝ × ContinuousPath alpha ↦
        ENNReal.ofReal (Real.exp (-lam * p.1)) *
          {p : ℝ × ContinuousPath alpha |
            ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < tau p.2}.indicator
            (fun p ↦ f (p.2 (Real.toNNReal p.1))) p) := by
      exact (ENNReal.measurable_ofReal.comp
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
          measurable_fst)).mul ((hf.comp heval).indicator hset)
    exact hjoint.lintegral_prod_left' (μ := volume.restrict (Set.Ioi 0))
  have hRestart :
      ∫⁻ omega, W omega * S.indicator
          (fun omega ↦ F (ContinuousPath.shift ((tau omega).untopD 0) omega)) omega ∂Q x =
        ∫⁻ omega, W omega * S.indicator
          (fun omega ↦ ∫⁻ eta, F eta ∂Q (omega ((tau omega).untopD 0))) omega ∂Q x := by
    apply StoppingTime.lintegral_mul_indicator_of_restrict_map
      (mu := Q x)
      (kappa := Kernel.comap Q (fun omega ↦ omega ((tau omega).untopD 0))
        (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau))
      (Y := fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega)
      (m := htau.measurableSpace) (S := S) (F := F) (W := W)
    · exact ContinuousPath.measurable_shift_untopD_stoppingTime tau htau
    · exact htau.measurableSpace_le
    · exact hS
    · intro A hA
      exact hFeller.continuousProcess_restrict_map_shift_stoppingTime_lt_top
        P hP hK x tau htau A hA
    · exact hF
    · exact hW
  have hRestart' :
      ∫⁻ omega, S.indicator
          (fun omega ↦ W omega * F
            (ContinuousPath.shift ((tau omega).untopD 0) omega)) omega ∂Q x =
        ∫⁻ omega, S.indicator
          (fun omega ↦ W omega * ∫⁻ eta, F eta ∂Q
            (omega ((tau omega).untopD 0))) omega ∂Q x := by
    rw [show S.indicator (fun omega ↦ W omega * F
          (ContinuousPath.shift ((tau omega).untopD 0) omega)) =
        fun omega ↦ W omega * S.indicator
          (fun omega ↦ F (ContinuousPath.shift ((tau omega).untopD 0) omega)) omega by
      funext omega
      by_cases hs : omega ∈ S
      · simp only [hs, Set.indicator_of_mem]
      · simp only [hs, not_false_eq_true, Set.indicator_of_notMem, mul_zero]]
    rw [show S.indicator (fun omega ↦ W omega * ∫⁻ eta, F eta ∂Q
          (omega ((tau omega).untopD 0))) =
        fun omega ↦ W omega * S.indicator
          (fun omega ↦ ∫⁻ eta, F eta ∂Q (omega ((tau omega).untopD 0))) omega by
      funext omega
      by_cases hs : omega ∈ S
      · simp only [hs, Set.indicator_of_mem]
      · simp only [hs, not_false_eq_true, Set.indicator_of_notMem, mul_zero]]
    exact hRestart
  change (∫⁻ omega, F omega ∂Q x) = _
  have hSplit : ∀ omega, F omega =
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau omega}.indicator
          (fun t ↦ f (omega (Real.toNNReal t))) t) +
      S.indicator (fun omega ↦ W omega * F
        (ContinuousPath.shift ((tau omega).untopD 0) omega)) omega := by
    intro omega
    exact pathResolvent_eq_preExit_add_restart U lam f omega
  rw [lintegral_congr hSplit, lintegral_add_left hPre]
  rw [← IsConservative.killedResolvent_eq_lintegral P hP U hU lam hf x]
  change IsConservative.killedResolvent P hP U hU lam f x +
      ∫⁻ omega, S.indicator
        (fun omega ↦ W omega * F
          (ContinuousPath.shift ((tau omega).untopD 0) omega)) omega ∂Q x = _
  rw [hRestart']
