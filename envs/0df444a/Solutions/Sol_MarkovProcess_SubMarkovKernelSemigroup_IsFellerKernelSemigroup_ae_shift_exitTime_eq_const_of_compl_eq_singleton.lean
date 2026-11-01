-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.ae_shift_exitTime_eq_const_of_compl_eq_singleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:24:54.956934+00:00
-- url     : https://prove2.me/submissions/6a521736-b5b0-4f70-9dd3-79aeaf02d03b

import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKolmogorov_a805d493
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Killed_Semigroup_8f8ac7bc
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExitLaw_2add356d
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
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
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
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_ContinuousPath_coordinate_exitTime_mem_frontier
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_ae_eq_const_of_absorbing
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_ae_eval_zero_eq
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuousProcess_restrict_map_shift_stoppingTime_lt_top

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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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



/-- The `WithTop`-valued exit time is the exit time. -/
theorem exitTimeTop_apply (U : Set alpha) (omega : ContinuousPath alpha) :
    exitTimeTop U omega = exitTime U omega := rfl







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
# Stopped laws and exit distributions

For the continuous-path process `Q` of a conservative semigroup, this file packages as kernels the
laws that the strong Markov property and the boundary value problems of a domain consume:

* `stoppedLaw T hT : Kernel alpha (NNReal × alpha)`, the joint law of a finite stopping time and
  the position at that time, with its two marginals;
* `exitLawTrunc U hU K : Kernel alpha alpha`, the law of the position at the exit time of an open
  set `U` truncated at the horizon `K`; from a starting point in `U` it lives on the closure of `U`
  (`exitLawTrunc_apply_compl_closure`);
* `exitLaw U hU : Kernel alpha alpha`, the exit distribution (harmonic measure): the law of the
  position at the exit time on the event that the path leaves `U`; its total mass is the exit
  probability, and from a starting point in `U` it lives on the frontier of `U`
  (`exitLaw_apply_compl_frontier`).

The harmonic representation of `Trajectory/HarmonicRepresentation.lean` reads, in these terms,
`∫ f d(exitLawTrunc U hU K x) = f x` whenever `L f = 0` on `U`
(`integral_exitLawTrunc_eq_of_generator_eq_zero`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- The finite value of a finite exit time, read through `untopD`, is its `toNNReal`. -/
theorem untopD_exitTimeTop_eq_toNNReal (U : Set alpha) (omega : ContinuousPath alpha)
    (h : exitTime U omega ≠ ⊤) :
    (exitTimeTop U omega).untopD 0 = (exitTime U omega).toNNReal := by
  rw [exitTimeTop_apply, ← ENNReal.coe_toNNReal h]
  rfl

variable [MeasurableSpace alpha] [BorelSpace alpha]







end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)

section StoppedLaw

variable (T : ContinuousPath alpha → NNReal)
  (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
    (fun omega ↦ (T omega : WithTop NNReal)))











end StoppedLaw

section ExitLaw

variable (U : Set alpha) (hU : IsOpen U)



















variable [LocallyCompactSpace alpha]



end ExitLaw

end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Killing the one-point process at infinity

This file identifies the continuous process of the one-point extension of a positive
`C₀`-contractive resolvent with the process killed on leaving its live part.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]



/-- At an absorbing state the entire continuous-path law is the Dirac mass at the constant
path. -/
theorem IsConservative.continuousProcess_eq_dirac_of_absorbing
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hK : P.KolmogorovRegular hP) (a : alpha)
    (hAbsorb : ∀ t, P t a = Measure.dirac a) :
    IsConservative.continuousProcess P hP a =
      Measure.dirac (ContinuousMap.const NNReal a) := by
  let mu := IsConservative.continuousProcess P hP a
  have hprob : IsProbabilityMeasure mu := by
    dsimp only [mu]
    infer_instance
  calc
    mu = mu.map id := (Measure.map_id).symm
    _ = mu.map (fun _ ↦ ContinuousMap.const NNReal a) :=
      Measure.map_congr (hP.ae_eq_const_of_absorbing P hK a hAbsorb)
    _ = mu Set.univ • Measure.dirac (ContinuousMap.const NNReal a) := Measure.map_const _ _
    _ = Measure.dirac (ContinuousMap.const NNReal a) := by rw [measure_univ, one_smul]

variable [LocallyCompactSpace alpha]







end MarkovProcess.SubMarkovKernelSemigroup

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

































end MarkovProcess.PositiveC0ContractiveResolvent


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Killing the one-point process at infinity

This file identifies the continuous process of the one-point extension of a positive
`C₀`-contractive resolvent with the process killed on leaving its live part.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty



variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]





variable [LocallyCompactSpace alpha]

namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (a : alpha) (hcompl : Uᶜ = {a})
    (hAbsorb : ∀ t, P t a = Measure.dirac a) {x : alpha} (hx : x ∈ U) :
    ∀ᵐ omega ∂IsConservative.continuousProcess P hP x,
      ContinuousPath.exitTime U omega < ⊤ →
        ContinuousPath.shift (ContinuousPath.exitTime U omega).toNNReal omega =
          ContinuousMap.const NNReal a := by
  let Q := IsConservative.continuousProcess P hP
  let tau := ContinuousPath.exitTimeTop U
  let S : Set (ContinuousPath alpha) := {omega | tau omega < ⊤}
  let Y : ContinuousPath alpha → ContinuousPath alpha := fun omega ↦
    ContinuousPath.shift ((tau omega).untopD 0) omega
  have htau := ContinuousPath.isStoppingTime_exitTime U hU
  have hS : MeasurableSet S := by
    simpa only [S, tau, ContinuousPath.exitTimeTop_apply] using!
      ContinuousPath.measurableSet_exitTime_lt_top U hU
  have hY : Measurable Y := ContinuousPath.measurable_shift_untopD_stoppingTime tau htau
  have heval0 : ∀ᵐ omega ∂Q x, omega 0 = x := IsConservative.ae_eval_zero_eq hP hK x
  have hevalExit : ∀ᵐ omega ∂(Q x).restrict S,
      omega ((tau omega).untopD 0) = a := by
    rw [ae_restrict_iff' hS]
    filter_upwards [heval0] with omega hzero homega
    have hfin : ContinuousPath.exitTime U omega ≠ ⊤ := by
      exact ne_of_lt (by simpa only [S, tau, ContinuousPath.exitTimeTop_apply] using! homega)
    rw [ContinuousPath.untopD_exitTimeTop_eq_toNNReal U omega hfin]
    have hfront := ContinuousPath.coordinate_exitTime_mem_frontier U hU omega
      (hzero.symm ▸ hx) hfin
    have hout : omega (ContinuousPath.exitTime U omega).toNNReal ∈ Uᶜ := by
      exact (hU.frontier_eq ▸ hfront).2
    rw [hcompl] at hout
    exact Set.mem_singleton_iff.mp hout
  have hRestart : ((Q x).restrict S).map Y =
      Kernel.comap Q (fun omega ↦ omega ((tau omega).untopD 0))
          (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
        ((Q x).restrict S) := by
    simpa only [Q, S, Y, Set.univ_inter] using
      hFeller.continuousProcess_restrict_map_shift_stoppingTime_lt_top
        P hP hK x tau htau Set.univ MeasurableSet.univ
  have hrhs : ∀ᵐ eta ∂Kernel.comap Q
        (fun omega ↦ omega ((tau omega).untopD 0))
          (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
        ((Q x).restrict S),
      eta = ContinuousMap.const NNReal a := by
    apply Measure.ae_comp_of_ae_ae
      (show MeasurableSet ({eta : ContinuousPath alpha |
        eta = ContinuousMap.const NNReal a}) by
          simpa only [Set.ofPred_eq_eq_singleton] using
            (isClosed_singleton (x := ContinuousMap.const NNReal a)).measurableSet)
    filter_upwards [hevalExit] with omega homega
    rw [Kernel.comap_apply, homega,
      hP.continuousProcess_eq_dirac_of_absorbing P hK a hAbsorb]
    exact (ae_dirac_iff (show MeasurableSet ({eta : ContinuousPath alpha |
      eta = ContinuousMap.const NNReal a}) by
        simpa only [Set.ofPred_eq_eq_singleton] using
          (isClosed_singleton (x := ContinuousMap.const NNReal a)).measurableSet)).mpr rfl
  rw [← hRestart] at hrhs
  have hshift : ∀ᵐ omega ∂(Q x).restrict S,
      Y omega = ContinuousMap.const NNReal a :=
    (ae_map_iff hY.aemeasurable
      (show MeasurableSet ({eta : ContinuousPath alpha |
        eta = ContinuousMap.const NNReal a}) by
          simpa only [Set.ofPred_eq_eq_singleton] using
            (isClosed_singleton (x := ContinuousMap.const NNReal a)).measurableSet)).mp hrhs
  rw [ae_restrict_iff' hS] at hshift
  filter_upwards [hshift] with omega homega hfin
  have hs : omega ∈ S := by
    change tau omega < ⊤
    rw [show tau omega = ContinuousPath.exitTime U omega by
      exact ContinuousPath.exitTimeTop_apply U omega]
    exact hfin
  have h := homega hs
  dsimp only [Y] at h
  rw [show (tau omega).untopD 0 = (ContinuousPath.exitTime U omega).toNNReal by
      exact ContinuousPath.untopD_exitTimeTop_eq_toNNReal U omega (ne_of_lt hfin)] at h
  exact h
