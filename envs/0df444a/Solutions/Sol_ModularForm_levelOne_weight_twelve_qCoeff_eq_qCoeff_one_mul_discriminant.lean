-- Prove2me | solution 1 for ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7be5f29a-1076-51f5-8a10-56a56cc887e4

import Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant
set_option Elab.async false
open scoped MatrixGroups

namespace WL12Pen

private theorem exists_coe_eq_smul_discriminant (Z : ModularForm 𝒮ℒ 12)
    (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) :
    ∃ c : ℂ, (⇑Z : UpperHalfPlane → ℂ) = c • ⇑CuspForm.discriminant := by
  obtain ⟨c, hc⟩ :=
    CuspForm.exists_smul_discriminant_of_weight_eq_twelve (ModularForm.toCuspForm Z h0)
  exact ⟨c, (show (c • ⇑CuspForm.discriminant : UpperHalfPlane → ℂ)
    = ⇑(ModularForm.toCuspForm Z h0) from congrArg DFunLike.coe hc).symm⟩

private theorem qExpansion_eq_smul (Z : ModularForm 𝒮ℒ 12) (c : ℂ)
    (hZ : (⇑Z : UpperHalfPlane → ℂ) = c • ⇑CuspForm.discriminant) :
    UpperHalfPlane.qExpansion 1 ⇑Z = c • UpperHalfPlane.qExpansion 1 ModularForm.discriminant := by
  rw [hZ, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c CuspForm.discriminant,
    CuspForm.coe_discriminant]

private theorem qCoeff_eq_mul (Z : ModularForm 𝒮ℒ 12) (c : ℂ)
    (hq : UpperHalfPlane.qExpansion 1 ⇑Z
      = c • UpperHalfPlane.qExpansion 1 ModularForm.discriminant) (n : ℕ) :
    ModularFormClass.qCoeff ⇑Z n = c * ModularFormClass.qCoeff ModularForm.discriminant n := by
  unfold ModularFormClass.qCoeff
  rw [hq, PowerSeries.coeff_smul, smul_eq_mul]

private theorem qCoeff_one_eq (Z : ModularForm 𝒮ℒ 12) (c : ℂ)
    (hq : UpperHalfPlane.qExpansion 1 ⇑Z
      = c • UpperHalfPlane.qExpansion 1 ModularForm.discriminant) :
    ModularFormClass.qCoeff ⇑Z 1 = c := by
  have h1 : ModularFormClass.qCoeff ModularForm.discriminant 1 = 1 := by
    unfold ModularFormClass.qCoeff
    exact ModularForm.discriminant_qExpansion_coeff_one
  rw [qCoeff_eq_mul Z c hq 1, h1, mul_one]

end WL12Pen

namespace ModularForm p2m_export "ModularForm" "toCuspForm discriminant discriminant_qExpansion_coeff_one" end ModularForm
p2m_open_scoped "ModularForm" in
private theorem ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant (Z : ModularForm 𝒮ℒ 12) (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) : ∀ n : ℕ, ModularFormClass.qCoeff ⇑Z n = ModularFormClass.qCoeff ⇑Z 1 * ModularFormClass.qCoeff ModularForm.discriminant n := by
  obtain ⟨c, hZ⟩ := WL12Pen.exists_coe_eq_smul_discriminant Z h0
  have hq := WL12Pen.qExpansion_eq_smul Z c hZ
  intro n
  rw [WL12Pen.qCoeff_eq_mul Z c hq n, WL12Pen.qCoeff_one_eq Z c hq]

theorem solution (Z : ModularForm 𝒮ℒ 12) (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) : ∀ n : ℕ, ModularFormClass.qCoeff ⇑Z n = ModularFormClass.qCoeff ⇑Z 1 * ModularFormClass.qCoeff ModularForm.discriminant n :=
  ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant Z h0

end S_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant
end P2MW
export P2MW.S_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant (solution)
