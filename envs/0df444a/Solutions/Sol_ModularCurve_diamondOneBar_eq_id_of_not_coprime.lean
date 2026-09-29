-- Prove2me | solution 1 for ModularCurve.diamondOneBar_eq_id_of_not_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/81564e6a-227c-5147-9a3e-d84971fafed6

import Mathlib
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diamondOneBar_eq_id_of_not_coprime

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

namespace ModularCurve p2m_export "ModularCurve" "IsBaseChangeAutOf baseChangeAut isBaseChangeAutOf_baseChangeAut baseChangeAut_of_not diamondAut diamondAut_of_not_coprime diamondAutBar diamondOneBar diamondOneBar_apply x1FunctionFieldBar laurentBaseChange" namespace DTrivBody end ModularCurve.DTrivBody
p2m_open_scoped "ModularCurve" in
open _root_.ModularCurve in

theorem ModularCurve.DTrivBody.baseChangeAut_refl_apply (L : Type*) [Field L] [Algebra ℚ L]
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (z : ↥(laurentBaseChange L F₀)) :
    baseChangeAut L (AlgEquiv.refl : F₀ ≃ₐ[ℚ] F₀) z = z := by
  rcases Classical.em (∃ σ : ↥(laurentBaseChange L F₀) ≃ₐ[L] ↥(laurentBaseChange L F₀), IsBaseChangeAutOf L (AlgEquiv.refl : F₀ ≃ₐ[ℚ] F₀) σ) with hex | hex
  · have hσ := isBaseChangeAutOf_baseChangeAut hex
    set σ := baseChangeAut L (AlgEquiv.refl : F₀ ≃ₐ[ℚ] F₀) with hσdef
    obtain ⟨z, hz⟩ := z
    apply Subtype.ext
    show ((σ ⟨z, hz⟩ : ↥(laurentBaseChange L F₀)) : LaurentSeries L) = z
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact hσ ⟨y, hy⟩
    | algebraMap a =>
      have : (⟨algebraMap L (LaurentSeries L) a, IntermediateField.algebraMap_mem _ a⟩ : ↥(laurentBaseChange L F₀)) =
          algebraMap L ↥(laurentBaseChange L F₀) a := rfl
      rw [this, AlgEquiv.commutes]
      rfl
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, IntermediateField.add_mem _ hx hy⟩ : ↥(laurentBaseChange L F₀)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, IntermediateField.coe_add, ihx, ihy]
    | inv x hx ihx =>
      have : (⟨x⁻¹, IntermediateField.inv_mem _ hx⟩ : ↥(laurentBaseChange L F₀)) = (⟨x, hx⟩ : ↥(laurentBaseChange L F₀))⁻¹ := rfl
      rw [this, map_inv₀, IntermediateField.coe_inv, ihx]
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, IntermediateField.mul_mem _ hx hy⟩ : ↥(laurentBaseChange L F₀)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, IntermediateField.coe_mul, ihx, ihy]
  · rw [baseChangeAut_of_not hex]
    rfl

theorem solution (M : ℕ) [NeZero M] {d : ℕ} (h : ¬ Nat.Coprime d M) :
    ModularCurve.diamondOneBar M d = LinearMap.id := by
  have h1 : ModularCurve.diamondAut M d = AlgEquiv.refl := ModularCurve.diamondAut_of_not_coprime h
  have h2 : ModularCurve.diamondAutBar M d = AlgEquiv.refl := by
    apply AlgEquiv.ext
    intro z
    show ModularCurve.baseChangeAut (AlgebraicClosure ℚ) (ModularCurve.diamondAut M d) z = z
    rw [h1]
    exact ModularCurve.DTrivBody.baseChangeAut_refl_apply (AlgebraicClosure ℚ) z
  apply LinearMap.ext
  intro x
  rw [ModularCurve.diamondOneBar_apply, h2, LinearMap.id_apply,
    show (AlgEquiv.refl : ↥(ModularCurve.x1FunctionFieldBar M) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M)) = 1 from rfl,
    map_one, one_smul]

end S_ModularCurve_diamondOneBar_eq_id_of_not_coprime
end P2MW
export P2MW.S_ModularCurve_diamondOneBar_eq_id_of_not_coprime (solution)
