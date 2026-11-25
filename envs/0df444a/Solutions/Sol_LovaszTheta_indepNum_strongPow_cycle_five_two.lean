-- Prove2me | solution 1 for LovaszTheta.indepNum_strongPow_cycle_five_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:42:45.796825+00:00
-- url     : https://prove2.me/submissions/d76fc0d8-aeef-4e0a-abe6-045eef975cb5

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Theorems.Thm_LovaszTheta_indepNum_strongPow_cycle_five

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}
namespace LovaszTheta
theorem _root_.solution : (strongPow (cycleGraph 5) 2).indepNum = 5 := by
  have hup := indepNum_strongPow_cycle_five 2
  have hlow : 5 ≤ (strongPow (cycleGraph 5) 2).indepNum := by
    have key : ∀ i j : Fin 5, i ≠ j →
        ¬ ((i = j ∨ i - j = 1 ∨ j - i = 1) ∧ (2 * i = 2 * j ∨ 2 * i - 2 * j = 1 ∨
          2 * j - 2 * i = 1)) := by decide
    have hinj : Function.Injective (fun i : Fin 5 => (![i, 2 * i] : Fin 2 → Fin 5)) := by
      intro i j h
      simpa using congrFun h 0
    have hind : (strongPow (cycleGraph 5) 2).IsIndepSet
        ((Finset.univ.image (fun i : Fin 5 => (![i, 2 * i] : Fin 2 → Fin 5)) : Finset _) :
          Set (Fin 2 → Fin 5)) := by
      intro x hx y hy hxy hadj
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      have hij : i ≠ j := fun h => hxy (by rw [h])
      have h0 := hadj.2 0
      have h1 := hadj.2 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      rw [cycleGraph_adj (n := 3)] at h0 h1
      exact key i j hij ⟨h0, h1⟩
    have := hind.card_le_indepNum
    rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at this
  nlinarith
end LovaszTheta
