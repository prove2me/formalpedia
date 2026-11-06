-- Prove2me | solution 1 for OAI.SevenEighths.EisensteinTheta.cosetConstant_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:40:13.622648+00:00
-- url     : https://prove2.me/submissions/557b4515-2fb0-462a-b251-6e79ec6399ac

import Definitions.Def_OAI_NumberTheory_DirichletL_ThetaProduct
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_P2M_OAI_SevenEighths_EisensteinTheta_parityPair_f__021f9d81f66b
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MeasureTheory
open OAI.SevenEighths OAI.SevenEighths.EisensteinTheta
open ThetaProduct
namespace OAI.SevenEighths.EisensteinTheta
theorem _root_.solution (a b L : ℝ) (hL : 0 < L)
    (ha₀ : 0 ≤ a) (haL : a < L) (hb₀ : 0 ≤ b) (hbL : b < L) :
    cosetConstant a b L hL = if a = 0 ∧ b = 0 then 1 else 0 := by
  have htwo : 0 < 2 * L := by positivity
  have hy1 : yShift b L 1 ∈ Set.Ico (0 : ℝ) 1 := by
    simp only [yShift, Fin.val_one, Nat.cast_one, mul_one, Set.mem_Ico]
    constructor
    · positivity
    · apply (div_lt_one htwo).2
      linarith
  have hy1pos : 0 < yShift b L 1 := by
    simp only [yShift, Fin.val_one, Nat.cast_one, mul_one]
    exact div_pos (by linarith) htwo
  have hy1ne : (yShift b L 1 : UnitAddCircle) ≠ 0 := by
    intro h
    have := (AddCircle.coe_eq_zero_iff_of_mem_Ico hy1).mp h
    linarith
  have hy0 : yShift b L 0 ∈ Set.Ico (0 : ℝ) 1 := by
    simp only [yShift, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero, Set.mem_Ico]
    constructor
    · positivity
    · apply (div_lt_one htwo).2
      linarith
  have hy0iff : (yShift b L 0 : UnitAddCircle) = 0 ↔ b = 0 := by
    rw [AddCircle.coe_eq_zero_iff_of_mem_Ico hy0]
    simp [yShift, div_eq_zero_iff, hL.ne']
  rw [cosetConstant, Fin.sum_univ_two, parityPair_f₀, parityPair_f₀,
    if_neg hy1ne, mul_zero, add_zero]
  by_cases hb : b = 0
  · subst b
    rw [if_pos (hy0iff.mpr rfl), mul_one]
    have hx : xShift a 0 L 0 = a / L := by
      simp only [xShift, sub_zero, Fin.val_zero, Nat.cast_zero, mul_zero]
      field_simp
    have hxmem : a / L ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨div_nonneg ha₀ hL.le, (div_lt_one hL).2 haL⟩
    have hxiff : (xShift a 0 L 0 : UnitAddCircle) = 0 ↔ a = 0 := by
      rw [hx, AddCircle.coe_eq_zero_iff_of_mem_Ico hxmem]
      simp [div_eq_zero_iff, hL.ne']
    simp only [hxiff, and_true]
  · rw [if_neg (fun h => hb (hy0iff.mp h)), mul_zero, if_neg (fun h => hb h.2)]
end OAI.SevenEighths.EisensteinTheta
