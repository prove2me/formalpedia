-- Prove2me | solution 1 for MeasureTheory.measure_eq_zero_or_one_of_flipSet_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:41:06.588867+00:00
-- url     : https://prove2.me/submissions/8b147e1f-b12e-46f8-b7b5-c766636a5966

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_ZeroOne
public import Theorems.Thm_MeasureTheory_flipSet_apply_of_mem
public import Theorems.Thm_MeasureTheory_flipSet_apply_of_notMem
public import Theorems.Thm_MeasureTheory_Measure_ext_of_initialCylinders
public import Theorems.Thm_MeasureTheory_cantorMeasure_cylinderOn
public import Theorems.Thm_MeasureTheory_cantorMeasure_inter_cylinder
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_measurableSet_cylinderOn
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution {E : Set (ℕ → Bool)} (hE : MeasurableSet E)
    (hinv : ∀ t : Finset ℕ, flipSet t ⁻¹' E = E) :
    cantorMeasure E = 0 ∨ cantorMeasure E = 1 := by
  -- `E` does not depend on the first `n` coordinates.
  have hdet : ∀ n : ℕ, Determined (↑(Finset.range n))ᶜ E := by
    intro n w w' hww' hw
    have hfl : w = flipSet ((Finset.range n).filter fun j ↦ w j ≠ w' j) w' := by
      ext j
      by_cases hj : j ∈ (Finset.range n).filter fun j ↦ w j ≠ w' j
      · rw [flipSet_apply_of_mem hj]
        have hne := (Finset.mem_filter.1 hj).2
        cases hw1 : w j <;> cases hw2 : w' j <;> simp_all
      · rw [flipSet_apply_of_notMem hj]
        by_cases hjn : j ∈ Finset.range n
        · by_contra hne
          exact hj (Finset.mem_filter.2 ⟨hjn, hne⟩)
        · exact hww' j (by simpa using hjn)
    rw [hfl] at hw
    rw [← hinv ((Finset.range n).filter fun j ↦ w j ≠ w' j)]
    exact hw
  -- So `E` is independent of every measurable set, and of itself.
  have hmeas : cantorMeasure.restrict E = cantorMeasure E • cantorMeasure := by
    refine Measure.ext_of_initialCylinders fun n v ↦ ?_
    rw [Measure.restrict_apply (measurableSet_cylinderOn _ _), inter_comm,
      cantorMeasure_inter_cylinder _ _ (hdet n), Measure.smul_apply, cantorMeasure_cylinderOn,
      smul_eq_mul]
  have h2 : cantorMeasure E = cantorMeasure E * cantorMeasure E := by
    have h := congrArg (fun ν : Measure (ℕ → Bool) ↦ ν E) hmeas
    simpa [Measure.restrict_apply hE] using h
  by_cases h0 : cantorMeasure E = 0
  · exact Or.inl h0
  · refine Or.inr ((ENNReal.mul_right_inj h0 (measure_ne_top _ _)).1 ?_)
    rw [mul_one]
    exact h2.symm
end MeasureTheory
