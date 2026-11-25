-- Prove2me | solution 1 for GlobalTheory.Nef.LocalIndex.exists_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:53:25.767914+00:00
-- url     : https://prove2.me/submissions/c1df31c8-7ca8-4caf-b579-e2f82d1fcf10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceIsDVRAndResidueEqGroundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceLocalIndexColength
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_det_adj_int
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_nrm_max
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.LocalIndex
open GlobalTheory.Nef.OrdCalc
variable {k F : Type} [Field k] [Field F] [Algebra k F]
namespace GlobalTheory.Nef.LocalIndex
theorem _root_.solution (v : Place k F) {n : ℕ} (a : Matrix (Fin n) (Fin n) F) (hd : a.det ≠ 0)
    (hlt : v.1 a.det < 1) :
    ∃ (c : Fin n → F) (i : Fin n), c i = 1 ∧ (∀ l, v.1 (c l) ≤ 1) ∧ ∀ l, v.1 (a.mulVec c l) < 1 := by
  have hn : ¬ ∀ i j, v.1 (a⁻¹ i j) ≤ 1 := by
    intro h
    have h1 := (det_adj_int v n _ h).1
    have h2 : v.1 (a.det * a⁻¹.det) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' h1) hlt
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv a (isUnit_iff_ne_zero.2 hd)] at h2
    simp at h2
  push Not at hn
  obtain ⟨i0, j, hj⟩ := hn
  have hb : (fun l => a⁻¹ l j) ≠ 0 := by
    intro h
    have := congrFun h i0
    simp only [Pi.zero_apply] at this
    rw [this] at hj
    simp at hj
  obtain ⟨i, hi, -, -, hmax⟩ := nrm_max v n _ hb
  have hvi : 1 < v.1 (a⁻¹ i j) := lt_of_lt_of_le hj (hmax i0)
  have hpos : 0 < v.1 (a⁻¹ i j) := lt_trans zero_lt_one hvi
  refine ⟨(a⁻¹ i j)⁻¹ • fun l => a⁻¹ l j, i, ?_, fun l => ?_, fun l => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hi
  · simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ hpos, mul_one]; exact hmax l
  · rw [Matrix.mulVec_smul]
    have e : a.mulVec (fun l => a⁻¹ l j) l = (1 : Matrix (Fin n) (Fin n) F) l j := by
      rw [← Matrix.mul_nonsing_inv a (isUnit_iff_ne_zero.2 hd)]; rfl
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, e]
    rw [inv_mul_lt_iff₀ hpos, mul_one]
    refine lt_of_le_of_lt ?_ hvi
    by_cases h : l = j <;> simp [Matrix.one_apply, h]
end GlobalTheory.Nef.LocalIndex
