-- Prove2me | solution 1 for MeasureTheory.cantorMeasure_inter_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:25.450216+00:00
-- url     : https://prove2.me/submissions/20fe426c-02dd-42b6-8d0f-a51e3a69f28c

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_Determined_mono
public import Theorems.Thm_MeasureTheory_Determined_inter
public import Theorems.Thm_MeasureTheory_Determined_preimage_flip
public import Theorems.Thm_MeasureTheory_determined_cylinderOn
public import Theorems.Thm_MeasureTheory_cylinderOn_insert
public import Theorems.Thm_MeasureTheory_cantorMeasure_inter_coord
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_mono

attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution {E : Set (ℕ → Bool)} (B : Finset ℕ) (v : ℕ → Bool)
    (hE : Determined (↑B)ᶜ E) :
    cantorMeasure (E ∩ cylinderOn B v) = cantorMeasure E * 2⁻¹ ^ B.card := by
  induction B using Finset.induction_on with
  | empty => simp [cylinderOn]
  | insert i B hi ih =>
    have hE' : Determined (↑B)ᶜ E := hE.mono (by simp)
    have hdet : Determined {i}ᶜ (E ∩ cylinderOn B v) :=
      (hE.mono (by simp)).inter (determined_cylinderOn B v (by simpa using hi))
    rw [cylinderOn_insert, ← inter_assoc,
      cantorMeasure_inter_coord (hdet.preimage_flip (by simp)), ih hE',
      Finset.card_insert_of_notMem hi, pow_succ, ENNReal.div_eq_inv_mul]
    ring
end MeasureTheory
