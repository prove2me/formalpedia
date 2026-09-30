-- Prove2me | solution 1 for MeasureTheory.Measure.measure_biUnion_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:52.195566+00:00
-- url     : https://prove2.me/submissions/95849943-c00f-44f7-8362-f5ba1016f09e

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.MeasureTheory.Group.Measure

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Measures invariant under addition

This file records measure formulas for finite families of disjoint additive translates.  In
lattice-point counting, the formula turns disjoint translates of a fundamental-domain cell into
measure bounds that can be compared with the number of cells.

## Main results

* `Measure.measure_biUnion_sub_mem`: a finite disjoint union of translates has measure
  equal to the number of translates times the measure of the original set.
-/

 section

open MeasureTheory Set

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

variable {E : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E]

/-- The union of finitely many pairwise disjoint translates of a measurable set has measure equal
to the number of translates times the measure of the set. -/
theorem solution
    (mu : _root_.MeasureTheory.Measure E) [mu.IsAddRightInvariant]
    {G F : _root_.Set E} (hFm : _root_.MeasurableSet F)
    (hdisj : ∀ w₁ ∈ G, ∀ w₂ ∈ G, w₁ ≠ w₂ →
      _root_.Disjoint {y : E | y - w₁ ∈ F} {y : E | y - w₂ ∈ F})
    {T : _root_.Finset E} (hT : ↑T ⊆ G) :
    mu (⋃ w ∈ T, {y : E | y - w ∈ F}) = T.card * mu F := by
  rw [_root_.MeasureTheory.measure_biUnion_finset (fun w₁ h₁ w₂ h₂ h ↦ hdisj w₁ (hT h₁) w₂ (hT h₂) h)
    fun w _ ↦ by
      have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
        ext y
        simp only [_root_.Set.mem_ofPred_eq, _root_.Set.mem_preimage, _root_.sub_eq_add_neg]
      rw [h]
      exact _root_.measurableSet_preimage (measurable_id.add_const (-w)) hFm]
  have htranslate (w : E) : mu {y : E | y - w ∈ F} = mu F := by
    have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
      ext y
      simp only [_root_.Set.mem_ofPred_eq, _root_.Set.mem_preimage, _root_.sub_eq_add_neg]
    rw [h, _root_.MeasureTheory.measure_preimage_add_right]
  simp_rw [htranslate]
  simp

end TauCeti

end
end
