-- Prove2me | solution 1 for MeasureTheory.cantorMeasure_real_cylinderOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:38:48.828279+00:00
-- url     : https://prove2.me/submissions/88a1ac53-c82a-4594-ac38-5bd0e9666202

module
public import Definitions.Def_AddUN_CantorMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_AddUN_SecondMoment
public import Theorems.Thm_MeasureTheory_cantorMeasure_cylinderOn
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
theorem _root_.solution (B : Finset ℕ) (v : ℕ → Bool) :
    cantorMeasure.real (cylinderOn B v) = (1 / 2) ^ B.card := by
  simp [measureReal_def, cantorMeasure_cylinderOn B v]
end MeasureTheory
