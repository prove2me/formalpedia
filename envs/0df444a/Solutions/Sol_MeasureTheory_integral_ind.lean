-- Prove2me | solution 1 for MeasureTheory.integral_ind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:28:51.367537+00:00
-- url     : https://prove2.me/submissions/29157530-14c0-4a11-81ed-710e3a5d9592

module
public import Definitions.Def_AddUN_CantorMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_AddUN_SecondMoment
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set MeasureTheory
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution {S : Set (ℕ → Bool)} (hS : MeasurableSet S) :
    ∫ w, ind S w ∂cantorMeasure = cantorMeasure.real S := by
  simpa [ind] using integral_indicator_const (μ := cantorMeasure) (1 : ℝ) hS
end MeasureTheory
