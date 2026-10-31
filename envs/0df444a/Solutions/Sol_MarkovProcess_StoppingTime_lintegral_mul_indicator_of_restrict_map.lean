-- Prove2me | solution 1 for MarkovProcess.StoppingTime.lintegral_mul_indicator_of_restrict_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:17:53.822378+00:00
-- url     : https://prove2.me/submissions/c258e8e1-33e8-4f97-85c8-25c8fd65ee0d

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



variable {Omega beta : Type*} {m mOmega : MeasurableSpace Omega}
  {mBeta : MeasurableSpace beta}

namespace MarkovProcess.StoppingTime

end MarkovProcess.StoppingTime
open MarkovProcess.StoppingTime
theorem solution
    (mu : @Measure Omega mOmega) (kappa : @Kernel Omega beta mOmega mBeta)
    (Y : Omega → beta) (hY : @Measurable Omega beta mOmega mBeta Y)
    (hm : m ≤ mOmega) (S : Set Omega) (hS : MeasurableSet[m] S)
    (hJoint : ∀ A : Set Omega, MeasurableSet[m] A →
      (mu.restrict (A ∩ S)).map Y = kappa ∘ₘ (mu.restrict (A ∩ S)))
    (F : beta → ℝ≥0∞) (hF : Measurable F)
    (W : Omega → ℝ≥0∞) (hW : Measurable[m] W) :
    ∫⁻ omega, W omega * S.indicator (fun omega ↦ F (Y omega)) omega ∂mu =
      ∫⁻ omega, W omega * S.indicator
        (fun omega ↦ ∫⁻ y, F y ∂kappa omega) omega ∂mu := by
  have hSm : MeasurableSet S := hm S hS
  have hSet : ∀ A : Set Omega, MeasurableSet[m] A →
      ∫⁻ omega in A ∩ S, F (Y omega) ∂mu =
        ∫⁻ omega in A ∩ S, (∫⁻ y, F y ∂kappa omega) ∂mu := by
    intro A hA
    calc
      ∫⁻ omega in A ∩ S, F (Y omega) ∂mu =
          ∫⁻ y, F y ∂((mu.restrict (A ∩ S)).map Y) := by
            rw [lintegral_map hF hY]
      _ = ∫⁻ y, F y ∂(kappa ∘ₘ (mu.restrict (A ∩ S))) := by rw [hJoint A hA]
      _ = ∫⁻ omega in A ∩ S, (∫⁻ y, F y ∂kappa omega) ∂mu := by
        rw [Measure.comp_eq_comp_const_apply]
        exact Measure.lintegral_bind kappa.aemeasurable hF.aemeasurable
  refine @Measurable.ennreal_induction Omega m
    (fun W ↦ ∫⁻ omega, W omega * S.indicator (fun omega ↦ F (Y omega)) omega ∂mu =
      ∫⁻ omega, W omega * S.indicator
        (fun omega ↦ ∫⁻ y, F y ∂kappa omega) omega ∂mu) ?_ ?_ ?_ W hW
  · intro c A hA
    have hA' : MeasurableSet A := hm A hA
    have hAS : MeasurableSet (A ∩ S) := hA'.inter hSm
    have hleft : (fun omega ↦ A.indicator (fun _ ↦ c) omega *
          S.indicator (fun omega ↦ F (Y omega)) omega) =
        (A ∩ S).indicator (fun omega ↦ c * F (Y omega)) := by
      funext omega
      by_cases ha : omega ∈ A <;> by_cases hs : omega ∈ S <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, ha, hs]
    have hright : (fun omega ↦ A.indicator (fun _ ↦ c) omega *
          S.indicator (fun omega ↦ ∫⁻ y, F y ∂kappa omega) omega) =
        (A ∩ S).indicator (fun omega ↦ c * ∫⁻ y, F y ∂kappa omega) := by
      funext omega
      by_cases ha : omega ∈ A <;> by_cases hs : omega ∈ S <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, ha, hs]
    rw [hleft, hright, lintegral_indicator hAS, lintegral_indicator hAS]
    calc
      ∫⁻ omega in A ∩ S, c * F (Y omega) ∂mu =
          c * ∫⁻ omega in A ∩ S, F (Y omega) ∂mu :=
        lintegral_const_mul c (hF.comp hY)
      _ = c * ∫⁻ omega in A ∩ S, (∫⁻ y, F y ∂kappa omega) ∂mu := by
        rw [hSet A hA]
      _ = ∫⁻ omega in A ∩ S, c * (∫⁻ y, F y ∂kappa omega) ∂mu :=
        (lintegral_const_mul c hF.lintegral_kernel).symm
  · intro W Z _hdisj hWm hZm hWi hZi
    simp_rw [Pi.add_apply, add_mul]
    rw [lintegral_add_left]
    · rw [lintegral_add_left]
      · exact congrArg₂ (· + ·) hWi hZi
      · exact (hWm.mono hm le_rfl).mul (hF.lintegral_kernel.indicator hSm)
    · exact (hWm.mono hm le_rfl).mul ((hF.comp hY).indicator hSm)
  · intro W hWm hmono hWi
    change (∫⁻ omega, (⨆ n, W n omega) *
      S.indicator (fun omega ↦ F (Y omega)) omega ∂mu) = _
    rw [show (fun omega ↦ (⨆ n, W n omega) *
        S.indicator (fun omega ↦ F (Y omega)) omega) =
      fun omega ↦ ⨆ n, W n omega * S.indicator (fun omega ↦ F (Y omega)) omega by
        funext omega; exact ENNReal.iSup_mul (fun n ↦ W n omega) _]
    rw [show (fun omega ↦ (⨆ n, W n omega) * S.indicator
        (fun omega ↦ ∫⁻ y, F y ∂kappa omega) omega) =
      fun omega ↦ ⨆ n, W n omega * S.indicator
        (fun omega ↦ ∫⁻ y, F y ∂kappa omega) omega by
        funext omega; exact ENNReal.iSup_mul (fun n ↦ W n omega) _]
    rw [lintegral_iSup]
    · rw [lintegral_iSup]
      · exact iSup_congr fun n ↦ hWi n
      · exact fun n ↦ (hWm n).mono hm le_rfl |>.mul
          (hF.lintegral_kernel.indicator hSm)
      · exact fun i j hij omega ↦ mul_le_mul_left (hmono hij omega) _
    · exact fun n ↦ (hWm n).mono hm le_rfl |>.mul
        ((hF.comp hY).indicator hSm)
    · exact fun i j hij omega ↦ mul_le_mul_left (hmono hij omega) _
