-- Prove2me | solution 1 for ModularCurve.isFractionRing_tensorProduct_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/70c7e548-3028-5bd9-8f02-43454b31a07d

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isFractionRing_tensorProduct_laurentBaseChange

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) :
    letI := ((ModularCurve.baseChangeHom L F₀).codRestrict (ModularCurve.laurentBaseChange L F₀).toSubalgebra
      (ModularCurve.baseChangeHom_mem L F₀)).toRingHom.toAlgebra
    IsFractionRing (L ⊗[ℚ] ↥F₀) ↥(ModularCurve.laurentBaseChange L F₀) := by
  letI := ((ModularCurve.baseChangeHom L F₀).codRestrict (ModularCurve.laurentBaseChange L F₀).toSubalgebra
      (ModularCurve.baseChangeHom_mem L F₀)).toRingHom.toAlgebra
  have hφ : ∀ x : L ⊗[ℚ] ↥F₀,
      ((algebraMap (L ⊗[ℚ] ↥F₀) ↥(ModularCurve.laurentBaseChange L F₀) x : ↥(ModularCurve.laurentBaseChange L F₀)) :
        LaurentSeries L) = ModularCurve.baseChangeHom L F₀ x := fun _ => rfl
  haveI : FaithfulSMul (L ⊗[ℚ] ↥F₀) ↥(ModularCurve.laurentBaseChange L F₀) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply ModularCurve.baseChangeHom_injective L F₀
    rw [← hφ, ← hφ, h]
  refine IsFractionRing.of_field (R := L ⊗[ℚ] ↥F₀) (K := ↥(ModularCurve.laurentBaseChange L F₀)) ?_
  rintro ⟨w, hw⟩
  suffices h : ∃ x y : L ⊗[ℚ] ↥F₀,
      w = ModularCurve.baseChangeHom L F₀ x / ModularCurve.baseChangeHom L F₀ y by
    obtain ⟨x, y, h⟩ := h
    refine ⟨x, y, Subtype.ext ?_⟩
    change w = (((algebraMap _ _ x / algebraMap _ _ y : ↥(ModularCurve.laurentBaseChange L F₀))) : LaurentSeries L)
    rw [IntermediateField.coe_div, hφ, hφ]
    exact h
  rw [ModularCurve.mem_laurentBaseChange_iff] at hw
  induction hw using Subfield.closure_induction with
  | mem w hw =>
      rcases hw with ⟨c, rfl⟩ | ⟨f, hf, rfl⟩
      · exact ⟨algebraMap L (L ⊗[ℚ] ↥F₀) c, 1, by rw [map_one, div_one, AlgHom.commutes]⟩
      · exact ⟨(1 : L) ⊗ₜ (⟨f, hf⟩ : ↥F₀), 1, by rw [map_one, div_one, ModularCurve.baseChangeHom_one_tmul]⟩
  | one => exact ⟨1, 1, by rw [map_one, div_one]⟩
  | add a b _ _ ha hb =>
      obtain ⟨x₁, y₁, rfl⟩ := ha
      obtain ⟨x₂, y₂, rfl⟩ := hb
      by_cases hy₁ : ModularCurve.baseChangeHom L F₀ y₁ = 0
      · exact ⟨x₂, y₂, by rw [hy₁, div_zero, zero_add]⟩
      by_cases hy₂ : ModularCurve.baseChangeHom L F₀ y₂ = 0
      · exact ⟨x₁, y₁, by rw [hy₂, div_zero, add_zero]⟩
      exact ⟨x₁ * y₂ + y₁ * x₂, y₁ * y₂, by rw [map_add, map_mul, map_mul, map_mul, div_add_div _ _ hy₁ hy₂]⟩
  | neg a _ ha =>
      obtain ⟨x, y, rfl⟩ := ha
      exact ⟨-x, y, by rw [map_neg, neg_div]⟩
  | inv a _ ha =>
      obtain ⟨x, y, rfl⟩ := ha
      exact ⟨y, x, by rw [inv_div]⟩
  | mul a b _ _ ha hb =>
      obtain ⟨x₁, y₁, rfl⟩ := ha
      obtain ⟨x₂, y₂, rfl⟩ := hb
      exact ⟨x₁ * x₂, y₁ * y₂, by rw [map_mul, map_mul, div_mul_div_comm]⟩

#print axioms solution

end S_ModularCurve_isFractionRing_tensorProduct_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_isFractionRing_tensorProduct_laurentBaseChange (solution)
