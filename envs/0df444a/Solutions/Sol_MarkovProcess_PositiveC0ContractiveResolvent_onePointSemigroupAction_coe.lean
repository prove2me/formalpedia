-- Prove2me | solution 1 for MarkovProcess.PositiveC0ContractiveResolvent.onePointSemigroupAction_coe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:09:03.12259+00:00
-- url     : https://prove2.me/submissions/da22e61c-7dee-48b2-acfa-8fd308157f33

import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointExtension_e4fabfdf
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
import Definitions.Def_MarkovProcess_V3H_Semigroup_ResolventGeneration_96f24647
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Metrizable.Urysohn

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# One-point extension of a positive `C₀` resolvent

A positive contractive resolvent on a locally compact Polish space generates a sub-Markov
semigroup. This file adjoins the genuine Alexandroff point at infinity, extends continuous
functions by splitting off their value there, and lets the generated semigroup evolve only the
part which vanishes at infinity. The resulting positive contractive resolvent has a conservative
Feller kernel semigroup, and the added point is absorbing.

Main results: `PositiveC0ContractiveResolvent.onePointResolvent`,
`PositiveC0ContractiveResolvent.onePointResolvent_operator`,
`PositiveC0ContractiveResolvent.isConservative_onePointKernelSemigroup`, and
`PositiveC0ContractiveResolvent.onePointKernelSemigroup_absorbing`.

This construction does not assert a Kolmogorov moment bound or construct a continuous-path
process.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology TopologicalSpace

noncomputable section

namespace OnePoint

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]















end OnePoint

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction NNReal ZeroAtInfty

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]



























variable [MeasurableSpace X] [BorelSpace X]

variable (R : PositiveC0ContractiveResolvent X)






























































end MarkovProcess.PositiveC0ContractiveResolvent


open MarkovProcess
open MarkovProcess.PositiveC0ContractiveResolvent
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# One-point extension of a positive `C₀` resolvent

A positive contractive resolvent on a locally compact Polish space generates a sub-Markov
semigroup. This file adjoins the genuine Alexandroff point at infinity, extends continuous
functions by splitting off their value there, and lets the generated semigroup evolve only the
part which vanishes at infinity. The resulting positive contractive resolvent has a conservative
Feller kernel semigroup, and the added point is absorbing.

Main results: `PositiveC0ContractiveResolvent.onePointResolvent`,
`PositiveC0ContractiveResolvent.onePointResolvent_operator`,
`PositiveC0ContractiveResolvent.isConservative_onePointKernelSemigroup`, and
`PositiveC0ContractiveResolvent.onePointKernelSemigroup_absorbing`.

This construction does not assert a Kolmogorov moment bound or construct a continuous-path
process.
-/

open Filter Set Topology TopologicalSpace




open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction NNReal ZeroAtInfty

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]



























variable [MeasurableSpace X] [BorelSpace X]

variable (R : PositiveC0ContractiveResolvent X)





namespace MarkovProcess.PositiveC0ContractiveResolvent

end MarkovProcess.PositiveC0ContractiveResolvent
open MarkovProcess.PositiveC0ContractiveResolvent
theorem solution (t : NNReal) (g : C₀(OnePoint X, ℝ)) (x : X) :
    R.onePointSemigroupAction t g (x : OnePoint X) =
      ∫ y, g (y : OnePoint X) ∂R.kernelSemigroup t x +
        (1 - (R.kernelSemigroup t x).real Set.univ) * g OnePoint.infty := by
  rw [onePointSemigroupAction, onePointAssemble_coe,
    ← R.integral_kernelSemigroup t (onePointRemainder g) x]
  let μ := R.kernelSemigroup t x
  have hmassE := R.kernelSemigroup.measure_univ_le_one t x
  have hfin : μ Set.univ < ⊤ :=
    lt_of_le_of_lt hmassE ENNReal.one_lt_top
  let : IsFiniteMeasure μ := ⟨hfin⟩
  let gc : X →ᵇ ℝ := g.toBCF.compContinuous
    ⟨fun x : X ↦ (x : OnePoint X), OnePoint.continuous_coe⟩
  have hg : Integrable (fun y : X ↦ g (y : OnePoint X)) μ := gc.integrable μ
  rw [show (∫ y, onePointRemainder g y ∂μ) =
      ∫ y, (g (y : OnePoint X) - g OnePoint.infty) ∂μ by rfl,
    integral_sub hg (integrable_const _), integral_const]
  change (∫ y, g (y : OnePoint X) ∂μ) - μ.real Set.univ * g OnePoint.infty +
      g OnePoint.infty = _
  ring
