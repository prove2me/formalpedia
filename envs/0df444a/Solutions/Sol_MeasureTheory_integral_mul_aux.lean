-- Prove2me | solution 1 for MeasureTheory.integral_mul_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:34:54.611798+00:00
-- url     : https://prove2.me/submissions/1053ba58-088f-4c71-9613-f093eb9fa731

module
public import Definitions.Def_AddUN_CantorMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_AddUN_SecondMoment
public import Theorems.Thm_MeasureTheory_integrable_ind
public import Theorems.Thm_MeasureTheory_integral_ind
public import Theorems.Thm_MeasureTheory_Determined_inter
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
theorem _root_.solution {E E' R R' : Set (ℕ → Bool)} (hE : MeasurableSet E)
    (hE' : MeasurableSet E') (hR : MeasurableSet R) (hR' : MeasurableSet R') (ρ : ℝ) :
    Integrable (fun w ↦ (ρ * ind E w - ind (E ∩ R) w) * (ρ * ind E' w - ind (E' ∩ R') w))
        cantorMeasure ∧
      ∫ w, (ρ * ind E w - ind (E ∩ R) w) * (ρ * ind E' w - ind (E' ∩ R') w) ∂cantorMeasure =
        ρ ^ 2 * cantorMeasure.real (E ∩ E') - ρ * cantorMeasure.real (E ∩ E' ∩ R') -
          ρ * cantorMeasure.real (E ∩ E' ∩ R) + cantorMeasure.real (E ∩ E' ∩ R ∩ R') := by
  have hfun : (fun w ↦ (ρ * ind E w - ind (E ∩ R) w) * (ρ * ind E' w - ind (E' ∩ R') w)) =
      fun w ↦ ρ ^ 2 * ind (E ∩ E') w - ρ * ind (E ∩ E' ∩ R') w - ρ * ind (E ∩ E' ∩ R) w +
        ind (E ∩ E' ∩ R ∩ R') w := by
    funext w
    by_cases h1 : w ∈ E <;> by_cases h2 : w ∈ E' <;> by_cases h3 : w ∈ R <;>
      by_cases h4 : w ∈ R' <;> simp [ind, h1, h2, h3, h4] <;> ring
  have i1 := (integrable_ind (hE.inter hE')).const_mul (ρ ^ 2)
  have i2 := (integrable_ind ((hE.inter hE').inter hR')).const_mul ρ
  have i3 := (integrable_ind ((hE.inter hE').inter hR)).const_mul ρ
  have i4 := integrable_ind (((hE.inter hE').inter hR).inter hR')
  rw [hfun]
  refine ⟨((i1.sub i2).sub i3).add i4, ?_⟩
  rw [integral_add (f := fun w ↦ ρ ^ 2 * ind (E ∩ E') w - ρ * ind (E ∩ E' ∩ R') w -
      ρ * ind (E ∩ E' ∩ R) w) ((i1.sub i2).sub i3) i4,
    integral_sub (f := fun w ↦ ρ ^ 2 * ind (E ∩ E') w - ρ * ind (E ∩ E' ∩ R') w) (i1.sub i2) i3,
    integral_sub i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_ind (hE.inter hE'),
    integral_ind ((hE.inter hE').inter hR'), integral_ind ((hE.inter hE').inter hR),
    integral_ind (((hE.inter hE').inter hR).inter hR')]
end MeasureTheory
