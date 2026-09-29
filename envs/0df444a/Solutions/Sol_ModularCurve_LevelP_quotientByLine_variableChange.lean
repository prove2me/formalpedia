-- Prove2me | solution 1 for ModularCurve.LevelP.quotientByLine_variableChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/509d2f5e-0346-5acc-8449-ae7e5565640f

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPQuotient
import Theorems.Thm_WeierstrassCurve_eval_Phi_variableChange
import Theorems.Thm_WeierstrassCurve_eval_PsiSq_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_quotientByLine_variableChange

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

namespace ModularCurve
p2m_export "ModularCurve" "LevelP.quotientByLine"
namespace LevelP
p2m_export "ModularCurve.LevelP" "smulX veluTLine veluWLine quotientByLine"
namespace VC
p2m_open "ModularCurve.LevelP ModularCurve"

p2m_open "WeierstrassCurve Polynomial ModularCurve.LevelP P2MW.S_ModularCurve_LevelP_quotientByLine_variableChange.ModularCurve.LevelP"

variable {A : Type u} [CommRing A] (W : WeierstrassCurve A) (C : VariableChange A)

theorem smulX_variableChange {a : ℤ} (ha : a ≠ 0) {x : A} (h : IsUnit ((W.ΨSq a).eval x)) :
    smulX (C • W) a (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Aˣ) : A) ^ 2 * (smulX W a x - C.r) := by
  obtain ⟨w, hw⟩ := h
  have hm : 2 * a.natAbs ^ 2 = 2 * (a.natAbs ^ 2 - 1) + 2 := by
    have : 1 ≤ a.natAbs ^ 2 := Nat.one_le_pow _ _ (Int.natAbs_pos.mpr ha)
    omega
  have hΨ : ((C • W).ΨSq a).eval (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r)) =
      (((C.u⁻¹ ^ (2 * (a.natAbs ^ 2 - 1)) * w : Aˣ)) : A) := by
    rw [WeierstrassCurve.eval_PsiSq_variableChange, Units.val_mul, Units.val_pow_eq_pow_val, hw]
  rw [smulX, smulX, hΨ, Ring.inverse_unit, ← hw, Ring.inverse_unit,
    WeierstrassCurve.eval_Phi_variableChange, hm, pow_add, mul_inv, Units.val_mul, ← inv_pow,
    inv_inv, Units.val_pow_eq_pow_val]
  rw [← hw]

  have hu : ((C.u⁻¹ : Aˣ) : A) * (C.u : A) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hw1 : (w : A) * ((w⁻¹ : Aˣ) : A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hum : ((C.u⁻¹ : Aˣ) : A) ^ (2 * (a.natAbs ^ 2 - 1)) * (C.u : A) ^ (2 * (a.natAbs ^ 2 - 1)) = 1 := by
    rw [← mul_pow, hu, one_pow]
  linear_combination
    (((C.u⁻¹ : Aˣ) : A) ^ 2 * ((W.Φ a).eval x - C.r * (w : A)) * ((w⁻¹ : Aˣ) : A)) * hum
      - (((C.u⁻¹ : Aˣ) : A) ^ 2 * C.r) * hw1

theorem veluTLine_variableChange (p : ℕ) {x : A}
    (h : ∀ a ∈ Finset.Icc 1 ((p - 1) / 2), IsUnit ((W.ΨSq a).eval x)) :
    veluTLine (C • W) p (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Aˣ) : A) ^ 4 * veluTLine W p x := by
  simp only [veluTLine, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha0 : (a : ℤ) ≠ 0 := by
    have := (Finset.mem_Icc.mp ha).1; exact_mod_cast (by omega : a ≠ 0)
  rw [smulX_variableChange W C ha0 (h a ha), WeierstrassCurve.variableChange_b₂,
    WeierstrassCurve.variableChange_b₄]
  ring

theorem veluWLine_variableChange (p : ℕ) {x : A}
    (h : ∀ a ∈ Finset.Icc 1 ((p - 1) / 2), IsUnit ((W.ΨSq a).eval x)) :
    veluWLine (C • W) p (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Aˣ) : A) ^ 6 * (veluWLine W p x - C.r * veluTLine W p x) := by
  simp only [veluWLine, veluTLine, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha0 : (a : ℤ) ≠ 0 := by
    have := (Finset.mem_Icc.mp ha).1; exact_mod_cast (by omega : a ≠ 0)
  rw [smulX_variableChange W C ha0 (h a ha), WeierstrassCurve.variableChange_b₂,
    WeierstrassCurve.variableChange_b₄]
  simp only [WeierstrassCurve.Ψ₂Sq, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    WeierstrassCurve.variableChange_b₂, WeierstrassCurve.variableChange_b₄,
    WeierstrassCurve.variableChange_b₆]
  ring

end ModularCurve.LevelP.VC

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LevelP_quotientByLine_variableChange.ModularCurve _root_.ModularCurve.LevelP _root_.P2MW.S_ModularCurve_LevelP_quotientByLine_variableChange.ModularCurve.LevelP WeierstrassCurve in

theorem solution
    {A : Type u} [CommRing A] (W : WeierstrassCurve A) (p : ℕ) (C : WeierstrassCurve.VariableChange A)
    {x : A} (h : ∀ a ∈ Finset.Icc 1 ((p - 1) / 2), IsUnit ((W.ΨSq a).eval x)) :
    ModularCurve.LevelP.quotientByLine (C • W) p (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r)) =
      C • ModularCurve.LevelP.quotientByLine W p x := by
  have hT := ModularCurve.LevelP.VC.veluTLine_variableChange W C p h
  have hWl := ModularCurve.LevelP.VC.veluWLine_variableChange W C p h
  ext
  · simp [LevelP.quotientByLine, WeierstrassCurve.variableChange_a₁]
  · simp [LevelP.quotientByLine, WeierstrassCurve.variableChange_a₂]
  · simp [LevelP.quotientByLine, WeierstrassCurve.variableChange_a₃]
  · simp only [LevelP.quotientByLine, WeierstrassCurve.variableChange_a₄, hT]
    ring
  · simp only [LevelP.quotientByLine, WeierstrassCurve.variableChange_a₆, hT, hWl,
      WeierstrassCurve.b₂, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂]
    ring

end S_ModularCurve_LevelP_quotientByLine_variableChange
end P2MW
export P2MW.S_ModularCurve_LevelP_quotientByLine_variableChange (solution)
