-- Prove2me | solution 1 for MarkovProcess.StoppingTime.setIntegral_integral_kernel_of_restrict_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:18:50.074371+00:00
-- url     : https://prove2.me/submissions/f962db69-fe71-4e74-91c6-95b6db4cbcd6

import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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


open MarkovProcess
open MarkovProcess.StoppingTime
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


/-! Generic stopping-time material: truncation at a deterministic horizon, the countable slicing
of the event where a `WithTop`-valued stopping time is finite, and the reassembly of restart
identities over the slices.  Nothing here is specific to path space. -/


open StoppingTime




variable {Omega beta E : Type*} {m : MeasurableSpace Omega}
  {mOmega : MeasurableSpace Omega} {mBeta : MeasurableSpace beta}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

namespace MarkovProcess.StoppingTime
end MarkovProcess.StoppingTime
open MarkovProcess.StoppingTime
omit [CompleteSpace E] in

theorem solution
    (mu : @Measure Omega mOmega) [IsFiniteMeasure mu]
    (kappa : @Kernel Omega beta mOmega mBeta) [IsMarkovKernel kappa]
    (Y : Omega → beta) (hY : @Measurable Omega beta mOmega mBeta Y) (A : Set Omega)
    (hJoint : (mu.restrict A).map Y = kappa ∘ₘ (mu.restrict A))
    (F : beta → E) (hF : StronglyMeasurable F) (C : Real) (hFC : ∀ y, ‖F y‖ ≤ C) :
    ∫ omega in A, (∫ y, F y ∂kappa omega) ∂mu = ∫ omega in A, F (Y omega) ∂mu := by
  have hfMeas : AEStronglyMeasurable (fun omega ↦ F (Y omega)) mu :=
    (hF.comp_measurable hY).aestronglyMeasurable
  have hfInt : Integrable (fun omega ↦ F (Y omega)) mu :=
    Integrable.of_bound hfMeas C (ae_of_all _ fun omega ↦ hFC (Y omega))
  have hFA : Integrable F ((mu.restrict A).map Y) := by
    rw [integrable_map_measure hF.aestronglyMeasurable hY.aemeasurable]
    exact hfInt.restrict
  have hFAComp : Integrable F (kappa ∘ₘ (mu.restrict A)) := by
    rw [← hJoint]
    exact hFA
  rw [Measure.comp_eq_comp_const_apply] at hFAComp
  have hIntegralComp := Kernel.integral_comp hFAComp
  calc
    ∫ omega in A, (∫ y, F y ∂kappa omega) ∂mu =
        ∫ omega, (∫ y, F y ∂kappa omega) ∂(mu.restrict A) := rfl
    _ = ∫ y, F y ∂(kappa ∘ₘ (mu.restrict A)) := by
      rw [Measure.comp_eq_comp_const_apply]
      simpa only [Kernel.const_apply] using hIntegralComp.symm
    _ = ∫ y, F y ∂((mu.restrict A).map Y) := by rw [hJoint]
    _ = ∫ omega, F (Y omega) ∂(mu.restrict A) := by
      rw [integral_map hY.aemeasurable hF.aestronglyMeasurable]
    _ = ∫ omega in A, F (Y omega) ∂mu := rfl
