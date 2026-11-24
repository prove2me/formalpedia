-- Prove2me | solution 1 for MeasureTheory.cantorMeasure_real_inter_cylinderOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:38:15.682806+00:00
-- url     : https://prove2.me/submissions/21bb07d1-c64f-4cce-a47d-e2213edf8053

module
public import Definitions.Def_AddUN_CantorMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_AddUN_SecondMoment
public import Theorems.Thm_MeasureTheory_cantorMeasure_inter_cylinder
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
theorem _root_.solution {E : Set (ℕ → Bool)} (B : Finset ℕ) (v : ℕ → Bool)
    (hE : Determined (↑B)ᶜ E) :
    cantorMeasure.real (E ∩ cylinderOn B v) = cantorMeasure.real E * (1 / 2) ^ B.card := by
  simp [measureReal_def, cantorMeasure_inter_cylinder B v hE, ENNReal.toReal_mul]
end MeasureTheory
