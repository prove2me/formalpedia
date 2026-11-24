-- Prove2me | solution 1 for MeasureTheory.IsUniversallyNull.of_injOn_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:44:23.564684+00:00
-- url     : https://prove2.me/submissions/b31c6bb4-606d-4797-9125-f8e34e71f232

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Transfer
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_of_injOn
public import Theorems.Thm_Set_Countable_isUniversallyNull


set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
namespace MeasureTheory
namespace IsUniversallyNull
theorem _root_.solution {P : Set Y} (hP : IsUniversallyNull P) {Δ : Set X}
    (hΔ : MeasurableSet Δ) {φ : X → Y} (hφ : Measurable (Δ.domRestrict φ)) {A : Set X}
    (hA : A ⊆ Δ) (hinj : InjOn φ A) (himg : φ '' A ⊆ P) : IsUniversallyNull A := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact countable_empty.isUniversallyNull
  classical
  have hψ : Measurable (Δ.piecewise φ fun _ ↦ φ a) :=
    measurable_of_restrict_of_restrict_compl hΔ (by rwa [domRestrict_piecewise])
      (by rw [domRestrict_piecewise_compl]; exact measurable_const)
  have heq : EqOn (Δ.piecewise φ fun _ ↦ φ a) φ A := fun x hx ↦ piecewise_eq_of_mem _ _ _ (hA hx)
  exact hP.of_injOn hψ (hinj.congr heq.symm) (by rwa [heq.image_eq])
end IsUniversallyNull
end MeasureTheory
