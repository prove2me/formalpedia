-- Prove2me | solution 1 for MeasureTheory.generateFrom_initialCylinders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:57.910494+00:00
-- url     : https://prove2.me/submissions/d0c4628f-5791-44f8-b6d8-8b9f1b6ce9ff

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_InitialCylinder
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_measurableSet_cylinderOn
public import Theorems.Thm_MeasureTheory_mem_cylinderOn
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution :
    (inferInstance : MeasurableSpace (ℕ → Bool)) =
      MeasurableSpace.generateFrom initialCylinders := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · -- Every coordinate map is measurable for the generated σ-algebra.
    refine iSup_le fun i ↦ ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    intro s _
    have hcoord : ∀ b : Bool, MeasurableSet[MeasurableSpace.generateFrom initialCylinders]
        {w : ℕ → Bool | w i = b} := fun b ↦ by
      have h : {w : ℕ → Bool | w i = b} =
          ⋃ (u : Fin (i + 1) → Bool) (_ : u (Fin.last i) = b),
            cylinderOn (Finset.range (i + 1)) fun j ↦ if h : j < i + 1 then u ⟨j, h⟩ else false := by
        ext w
        simp only [mem_ofPred_eq, mem_iUnion, mem_cylinderOn, Finset.mem_range, exists_prop]
        constructor
        · intro hw
          exact ⟨fun j ↦ w j, hw, fun j hj ↦ by simp [hj]⟩
        · rintro ⟨u, hu, hwu⟩
          rw [hwu i (Nat.lt_succ_self i), dif_pos (Nat.lt_succ_self i), ← hu]
          rfl
      rw [h]
      exact .iUnion fun u ↦ .iUnion fun _ ↦ MeasurableSpace.measurableSet_generateFrom ⟨_, _, rfl⟩
    have hs : (fun w : ℕ → Bool ↦ w i) ⁻¹' s = ⋃ (b : Bool) (_ : b ∈ s), {w | w i = b} := by
      ext w
      simp
    change MeasurableSet[MeasurableSpace.generateFrom initialCylinders]
      ((fun w : ℕ → Bool ↦ w i) ⁻¹' s)
    rw [hs]
    exact .iUnion fun b ↦ .iUnion fun _ ↦ hcoord b
  · rintro _ ⟨n, v, rfl⟩
    exact measurableSet_cylinderOn _ _
end MeasureTheory
