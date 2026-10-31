-- Prove2me | solution 1 for MarkovProcess.PositiveC0OperatorMeasure.measure_compact_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:12:45.679842+00:00
-- url     : https://prove2.me/submissions/a9b72265-f436-4c0a-a402-82cb42234dcb

import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMass_48f724bb
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Total mass of pointwise Riesz measures

A positive contraction on real continuous functions vanishing at infinity induces pointwise
Riesz measures of total mass at most one.  The proof first bounds compact sets using compactly
supported Urysohn cutoff functions, then passes to the whole space by inner regularity.

This file proves only a pointwise total-mass bound and finiteness.  It does not construct a kernel
or prove any regularity in the evaluation point.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty

namespace MarkovProcess.PositiveC0OperatorMeasure

variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [MeasurableSpace α] [BorelSpace α]

variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)







end MarkovProcess.PositiveC0OperatorMeasure


open MarkovProcess
open MarkovProcess.PositiveC0OperatorMeasure
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Total mass of pointwise Riesz measures

A positive contraction on real continuous functions vanishing at infinity induces pointwise
Riesz measures of total mass at most one.  The proof first bounds compact sets using compactly
supported Urysohn cutoff functions, then passes to the whole space by inner regularity.

This file proves only a pointwise total-mass bound and finiteness.  It does not construct a kernel
or prove any regularity in the evaluation point.
-/

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty


variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [MeasurableSpace α] [BorelSpace α]

variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)

namespace MarkovProcess.PositiveC0OperatorMeasure

end MarkovProcess.PositiveC0OperatorMeasure
open MarkovProcess.PositiveC0OperatorMeasure
theorem solution (hT_norm : ‖T‖ ≤ 1) (x : α) {K : Set α} (hK : IsCompact K) :
    measure T hT x K ≤ 1 := by
  obtain ⟨f, hfK, hfcompact, _hf_support, hf⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (Set.subset_univ K)
  let g : C_c(α, ℝ) := ⟨f, hasCompactSupport_def.mpr hfcompact⟩
  have hg_nonneg (y : α) : 0 ≤ g y := (hf y).1
  have hg_le_one (y : α) : g y ≤ 1 := (hf y).2
  have hg_norm : ‖compactlySupportedToC0LinearMap g‖ ≤ 1 := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le zero_le_one).2 fun y ↦ ?_
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(neg_nonpos.mpr zero_le_one).trans (hg_nonneg y), hg_le_one y⟩
  have hfunctional_le_one : functional T hT x g ≤ 1 := by
    calc
      functional T hT x g = T (compactlySupportedToC0LinearMap g) x := rfl
      _ ≤ |T (compactlySupportedToC0LinearMap g) x| := le_abs_self _
      _ ≤ ‖T (compactlySupportedToC0LinearMap g)‖ := by
        exact (T (compactlySupportedToC0LinearMap g)).toBCF.norm_coe_le_norm x
      _ ≤ 1 := by
        simpa only [one_mul] using
          T.le_of_opNorm_le_of_le hT_norm hg_norm
  calc
    measure T hT x K ≤ ENNReal.ofReal (functional T hT x g) := by
      apply RealRMK.rieszMeasure_le_of_eq_one (functional T hT x) hg_nonneg hK
      intro y hy
      exact hfK hy
    _ ≤ 1 := ENNReal.ofReal_le_one.mpr hfunctional_le_one
