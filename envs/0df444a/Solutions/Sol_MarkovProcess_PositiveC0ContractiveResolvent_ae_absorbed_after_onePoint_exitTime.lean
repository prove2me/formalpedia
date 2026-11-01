-- Prove2me | solution 1 for MarkovProcess.PositiveC0ContractiveResolvent.ae_absorbed_after_onePoint_exitTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:32:02.025216+00:00
-- url     : https://prove2.me/submissions/64898243-93ae-4936-b635-ed30b758d13c

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKolmogorov_a805d493
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Killed_Semigroup_8f8ac7bc
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExitLaw_2add356d
import Theorems.Thm_MarkovProcess_PositiveC0ContractiveResolvent_onePointKernelSemigroup_absorbing
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_ae_shift_exitTime_eq_const_of_compl_eq_singleton

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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]





variable [LocallyCompactSpace alpha]



/-- Pathwise absorption after the finite exit time from an open set whose complement is a
single absorbing state. -/
theorem IsFellerKernelSemigroup.ae_absorbed_after_exitTime_of_compl_eq_singleton
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (a : alpha) (hcompl : Uᶜ = {a})
    (hAbsorb : ∀ t, P t a = Measure.dirac a) {x : alpha} (hx : x ∈ U) :
    ∀ᵐ omega ∂IsConservative.continuousProcess P hP x,
      ContinuousPath.exitTime U omega < ⊤ →
        ∀ t : NNReal, (ContinuousPath.exitTime U omega).toNNReal ≤ t → omega t = a := by
  filter_upwards [hFeller.ae_shift_exitTime_eq_const_of_compl_eq_singleton
      P hP hK U hU a hcompl hAbsorb hx] with omega homega hfin t ht
  let s := t - (ContinuousPath.exitTime U omega).toNNReal
  have hadd : (ContinuousPath.exitTime U omega).toNNReal + s = t := by
    exact add_tsub_cancel_of_le ht
  have h := congrArg (fun eta : ContinuousPath alpha ↦ eta s) (homega hfin)
  simpa only [ContinuousPath.shift_apply, ContinuousMap.const_apply, hadd] using h



end MarkovProcess.SubMarkovKernelSemigroup

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

































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
      R.isConservative_onePointKernelSemigroup) (x : X) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    ∀ᵐ omega ∂IsConservative.continuousProcess R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup (x : OnePoint X),
      ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega < ⊤ →
        ∀ t : NNReal,
          (ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega).toNNReal ≤ t →
            omega t = OnePoint.infty := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let : CompleteSpace (OnePoint X) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  exact R.isFellerKernelSemigroup_onePointKernelSemigroup
    |>.ae_absorbed_after_exitTime_of_compl_eq_singleton R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      hK
      (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe OnePoint.infty
      OnePoint.compl_range_coe R.onePointKernelSemigroup_absorbing
      ⟨x, rfl⟩
