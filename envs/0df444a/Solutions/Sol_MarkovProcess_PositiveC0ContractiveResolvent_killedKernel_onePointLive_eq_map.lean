-- Prove2me | solution 1 for MarkovProcess.PositiveC0ContractiveResolvent.killedKernel_onePointLive_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:36:34.226993+00:00
-- url     : https://prove2.me/submissions/53b959b0-b9e1-46b0-9d95-902fafd0b8ec

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
import Theorems.Thm_MarkovProcess_PositiveC0ContractiveResolvent_onePointKernelSemigroup_absorbing
import Theorems.Thm_MarkovProcess_PositiveC0ContractiveResolvent_onePointKernelSemigroup_apply_coe
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_eval_nnreal
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_ae_lt_exitTime_iff_mem_of_compl_eq_singleton

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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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





variable [LocallyCompactSpace alpha]







end MarkovProcess.SubMarkovKernelSemigroup

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]













/-- For the one-point process, survival to a deterministic time is almost surely equivalent to
the time-`t` coordinate still being a live point. -/
theorem ae_lt_onePoint_exitTime_iff_mem
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hK : letI :=
        OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      letI : CompleteSpace (OnePoint X) :=
        completeSpace_of_isComplete_univ isCompact_univ.isComplete
      R.onePointKernelSemigroup.KolmogorovRegular
      R.isConservative_onePointKernelSemigroup)
    (x : X) (t : NNReal) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    ∀ᵐ omega ∂IsConservative.continuousProcess R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup (x : OnePoint X),
      ((t : ℝ≥0∞) < ContinuousPath.exitTime
          (Set.range ((↑) : X → OnePoint X)) omega ↔
        omega t ∈ Set.range ((↑) : X → OnePoint X)) := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let : CompleteSpace (OnePoint X) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  exact R.isFellerKernelSemigroup_onePointKernelSemigroup
    |>.ae_lt_exitTime_iff_mem_of_compl_eq_singleton R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      hK
      (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe OnePoint.infty
      OnePoint.compl_range_coe R.onePointKernelSemigroup_absorbing
      ⟨x, rfl⟩ t



















end MarkovProcess.PositiveC0ContractiveResolvent


open MarkovProcess
open MarkovProcess.PositiveC0ContractiveResolvent
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




open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

















namespace MarkovProcess.PositiveC0ContractiveResolvent

end MarkovProcess.PositiveC0ContractiveResolvent
open MarkovProcess.PositiveC0ContractiveResolvent
theorem solution
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hK : letI :=
        OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      letI : CompleteSpace (OnePoint X) :=
        completeSpace_of_isComplete_univ isCompact_univ.isComplete
      R.onePointKernelSemigroup.KolmogorovRegular
      R.isConservative_onePointKernelSemigroup)
    (t : NNReal) (x : X) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    IsConservative.killedKernel R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe t
        (x : OnePoint X) =
      (R.kernelSemigroup t x).map ((↑) : X → OnePoint X) := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let : CompleteSpace (OnePoint X) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  let live : Set (OnePoint X) := Set.range ((↑) : X → OnePoint X)
  apply Measure.ext
  intro A hA
  have hAlive : MeasurableSet (A ∩ live) := hA.inter OnePoint.isOpen_range_coe.measurableSet
  have hae := R.ae_lt_onePoint_exitTime_iff_mem rho hrho_cont hrho_pos hrho_lipschitz
    hrho_compact hK x t
  rw [IsConservative.killedKernel_apply R.onePointKernelSemigroup
    R.isConservative_onePointKernelSemigroup live OnePoint.isOpen_range_coe t
    (x : OnePoint X) hA]
  have hevent : ∀ᵐ omega ∂IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup (x : OnePoint X),
      (omega ∈ ContinuousPath.killedEvent live t A ↔ omega t ∈ A ∩ live) := by
    filter_upwards [hae] with omega homega
    have homega' : ((t : ℝ≥0∞) < ContinuousPath.exitTime
        (Set.range ((↑) : X → OnePoint X)) omega ↔
      omega t ∈ Set.range ((↑) : X → OnePoint X)) := homega
    rw [ContinuousPath.mem_killedEvent_iff, homega']
    exact and_comm
  have hmeasure :
      IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (x : OnePoint X)
            (ContinuousPath.killedEvent live t A) =
        IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (x : OnePoint X)
            ((fun omega : ContinuousPath (OnePoint X) ↦ omega t) ⁻¹' (A ∩ live)) := by
    apply measure_congr
    filter_upwards [hevent] with omega homega
    exact propext homega
  rw [hmeasure]
  show (IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup (x : OnePoint X))
      (ContinuousPath.coordinateProcess t ⁻¹' (A ∩ live)) =
    (R.kernelSemigroup t x).map ((↑) : X → OnePoint X) A
  rw [← Kernel.map_apply'
    (IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup) (hf := ContinuousPath.measurable_coordinateProcess t)
    (x : OnePoint X) hAlive]
  show ((IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup).map (fun omega => omega t) (x : OnePoint X))
      (A ∩ live) =
    (R.kernelSemigroup t x).map ((↑) : X → OnePoint X) A
  rw [R.isFellerKernelSemigroup_onePointKernelSemigroup.continuousProcess_map_eval_nnreal
      R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
      hK t,
    R.onePointKernelSemigroup_apply_coe, Measure.add_apply,
    Measure.map_apply OnePoint.continuous_coe.measurable hAlive,
    Measure.smul_apply, Measure.dirac_apply' OnePoint.infty hAlive,
    Measure.map_apply OnePoint.continuous_coe.measurable hA]
  have hinf : OnePoint.infty ∉ A ∩ live := fun h ↦ OnePoint.infty_notMem_range_coe h.2
  rw [Set.indicator_of_notMem hinf, smul_zero, add_zero]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  exact and_iff_left ⟨y, rfl⟩
