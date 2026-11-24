-- Prove2me | solution 1 for MeasureTheory.integrable_ind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:28:49.753258+00:00
-- url     : https://prove2.me/submissions/830cc536-62b0-46d0-87f8-d9efb94578ca

module
public import Definitions.Def_AddUN_CantorMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_AddUN_SecondMoment

set_option autoImplicit false
@[expose] public section
public section
open Set MeasureTheory
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution {S : Set (ℕ → Bool)} (hS : MeasurableSet S) :
    Integrable (ind S) cantorMeasure :=
  (integrable_const (1 : ℝ)).indicator hS
end MeasureTheory
