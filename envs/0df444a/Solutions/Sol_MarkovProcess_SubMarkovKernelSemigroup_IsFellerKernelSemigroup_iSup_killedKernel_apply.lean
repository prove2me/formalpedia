-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.iSup_killedKernel_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:30:07.664705+00:00
-- url     : https://prove2.me/submissions/68991d5c-de64-4267-9679-dfeb397c2c22

import Definitions.Def_MarkovProcess_V3H_Killed_Kernel_adff808d
import Definitions.Def_MarkovProcess_V3H_Path_Exhaustion_e03721f1
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
import Theorems.Thm_MarkovProcess_ContinuousPath_IsOpenExhaustion_exists_lt_exitTime
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_eval_nnreal

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exit times along an exhaustion

For an increasing sequence of open sets `U n` covering the state space (an open exhaustion), the
exit time of a continuous path from `U n` tends to infinity: the path restricted to a compact time
interval has compact range, which lies in some `U N`, and the path therefore stays in `U n` on that
interval for every `n ≥ N` (`tendsto_exitTime_atTop`).  Exit times are monotone in the set
(`exitTime_mono`), as are the truncated exit times.

This is the path-space fact behind nonexplosion arguments: no probability law is involved here.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal NNReal

namespace MarkovProcess.ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- Exit times are monotone in the set: a path leaves a larger set no earlier. -/
theorem exitTime_mono {U V : Set alpha} (hUV : U ⊆ V) (omega : ContinuousPath alpha) :
    exitTime U omega ≤ exitTime V omega := by
  rw [le_exitTime_iff]
  intro v hv
  exact exitTime_le_of_notMem U omega v (fun h ↦ hv (hUV h))















end MarkovProcess.ContinuousPath


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dynkin's formula at deterministic times

For the continuous-path process `Q = continuousProcess P hP` of a conservative Feller semigroup
`P`, the `C₀` semigroup `hFeller.c0Semigroup` acts by `(S t f) x = E_x f(ω_t)`
(`c0Semigroup_apply_eq_integral`, from the one-time marginal `continuousProcess_map_eval_nnreal`
at every real time).  Combining this with the fundamental identity of the generator
`S t f - f = ∫₀ᵗ S s (L f) ds` and Fubini's theorem gives **Dynkin's formula**
(`integral_eval_sub_eq_integral_integral_generator`): for `f` in the generator domain,

  `E_x f(ω_t) - f x = E_x ∫₀ᵗ (L f)(ω_s) ds`.

The evaluation functional `c0EvalCLM x : C₀(α, ℝ) →L[ℝ] ℝ` is the tool that moves the Bochner
integral in `C₀` to a pointwise integral; `evalC0CLM` is the same functional under its original
name, kept for consumers.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section Eval

variable {alpha : Type*} [TopologicalSpace alpha]





end Eval

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- One-time marginal at every real time: evaluating the continuous-path process at time `t`
gives the transition kernel of `P` at `t`. -/
theorem IsFellerKernelSemigroup.continuousProcess_map_eval_nnreal
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (t : NNReal) :
    (IsConservative.continuousProcess P hP).map (fun omega ↦ omega t) = P t :=
  IsConservative.continuousPathTrajectory_map_eval_nnreal P hP hFeller _ hK t









end MarkovProcess.SubMarkovKernelSemigroup


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The semigroup as the limit of its killed parts

Along an open exhaustion `U n ↑ α` of the state space, the killed kernels increase to the
transition kernels of the semigroup: for every time `t`, starting point `x` and measurable set
`B`,

  `⨆ n, killedKernel P hP (U n) _ t x B = P t x B`   (`iSup_killedKernel_apply`),

and the survival probabilities `Q x {t < τ_{U n}}` increase to one. This is the statement that the
whole-space semigroup is the minimal semigroup of its killed parts; it rests on the path-space
fact that exit times along an exhaustion tend to infinity (`Path/Exhaustion.lean`), so the
killed events increase to the whole event `{ω t ∈ B}`.

The killed kernels are monotone in the open set (`killedKernel_mono`); no other structure is
used.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- Killed events are monotone in the set. -/
theorem killedEvent_mono {U V : Set alpha} (hUV : U ⊆ V) (t : NNReal) (B : Set alpha) :
    killedEvent U t B ⊆ killedEvent V t B := by
  rintro omega ⟨hlt, hmem⟩
  exact ⟨lt_of_lt_of_le hlt (exitTime_mono hUV omega), hmem⟩

/-- Along an open exhaustion, the killed events increase to the event that the path is in `B` at
time `t`. -/
theorem IsOpenExhaustion.iUnion_killedEvent {U : ℕ → Set alpha} (hU : IsOpenExhaustion U)
    (t : NNReal) (B : Set alpha) :
    ⋃ n, killedEvent (U n) t B = {omega : ContinuousPath alpha | omega t ∈ B} := by
  ext omega
  simp only [Set.mem_iUnion, mem_killedEvent_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, -, hmem⟩
    exact hmem
  · intro hmem
    obtain ⟨N, hN⟩ := hU.exists_lt_exitTime omega t
    exact ⟨N, hN N le_rfl, hmem⟩



end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)





variable [LocallyCompactSpace alpha]



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
# The semigroup as the limit of its killed parts

Along an open exhaustion `U n ↑ α` of the state space, the killed kernels increase to the
transition kernels of the semigroup: for every time `t`, starting point `x` and measurable set
`B`,

  `⨆ n, killedKernel P hP (U n) _ t x B = P t x B`   (`iSup_killedKernel_apply`),

and the survival probabilities `Q x {t < τ_{U n}}` increase to one. This is the statement that the
whole-space semigroup is the minimal semigroup of its killed parts; it rests on the path-space
fact that exit times along an exhaustion tend to infinity (`Path/Exhaustion.lean`), so the
killed events increase to the whole event `{ω t ∈ B}`.

The killed kernels are monotone in the open set (`killedKernel_mono`); no other structure is
used.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal




variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)





variable [LocallyCompactSpace alpha]

namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) {U : ℕ → Set alpha} (hU : ContinuousPath.IsOpenExhaustion U)
    (t : NNReal) (x : alpha) {B : Set alpha} (hB : MeasurableSet B) :
    ⨆ n, IsConservative.killedKernel P hP (U n) (hU.isOpen n) t x B = P t x B := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  have hmono : Monotone fun n ↦ ContinuousPath.killedEvent (U n) t B :=
    fun m n hmn ↦ ContinuousPath.killedEvent_mono (hU.monotone hmn) t B
  simp_rw [IsConservative.killedKernel_apply P hP _ _ t x hB]
  rw [← Monotone.measure_iUnion hmono, hU.iUnion_killedEvent t B]
  change IsConservative.continuousProcess P hP x
    ((fun omega : ContinuousPath alpha ↦ omega t) ⁻¹' B) = _
  rw [← Measure.map_apply hmeas hB, ← Kernel.map_apply _ hmeas,
    hFeller.continuousProcess_map_eval_nnreal P hP hK t]
