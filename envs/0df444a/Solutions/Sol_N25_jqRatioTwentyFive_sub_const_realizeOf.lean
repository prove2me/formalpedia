-- Prove2me | solution 1 for N25.jqRatioTwentyFive_sub_const_realizeOf
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:11.253032+00:00
-- url     : https://prove2.me/submissions/7826def1-55a1-4457-b4f9-042f2300ebb0

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_N25_jqTwentyFive_form_ratio
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Theorems.Thm_ModularCurve_realizeOf_eq_div

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane ModularCurve

open scoped MatrixGroups

namespace N25

/-- The actual rational j-ratio minus a constant has the expected analytic realization. -/
theorem _root_.solution (c : ℂ) (τ : UpperHalfPlane)
    (hE : ModularForm.E₄ τ ≠ 0) :
    realizeOf (CohCarrier.GammaH 25 N25.H25)
      (jqNModC ℂ 25 / jqModC ℂ - HahnSeries.C c) τ =
      (ModularForm.E₄ (ModularForm.heckeDiagMatrix 25 • τ) ^ 3 /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix 25 • τ)) /
      (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) - c := by
  let Γ := CohCarrier.GammaH 25 N25.H25
  have hle0 : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
    rintro A ⟨B, _, rfl⟩
    exact ⟨B, rfl⟩
  have hle25 : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤
      (CongruenceSubgroup.Gamma0 25 : Subgroup (GL (Fin 2) ℝ)) := by
    rintro A ⟨B, hB, rfl⟩
    exact ⟨B, CohCarrier.GammaH_le_Gamma0 N25.H25 hB, rfl⟩
  let E : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by norm_num) (ModularForm.E₄.pow 3)
  let D : ModularForm 𝒮ℒ 12 := CuspForm.toModularFormₗ CuspForm.discriminant
  let G0 : ModularForm Γ 12 :=
    { toFun := E
      slash_action_eq' := fun A hA => E.slash_action_eq' A (hle0 hA)
      holo' := E.holo'
      bdd_at_cusps' := fun hc => E.bdd_at_cusps' (hc.mono hle0) }
  let H0 : ModularForm Γ 12 :=
    { toFun := D
      slash_action_eq' := fun A hA => D.slash_action_eq' A (hle0 hA)
      holo' := D.holo'
      bdd_at_cusps' := fun hc => D.bdd_at_cusps' (hc.mono hle0) }
  obtain ⟨G25, H25, hG25, hH25, hH25ne, hq25⟩ := jqTwentyFive_form_ratio
  let G1 : ModularForm Γ 12 :=
    { toFun := G25
      slash_action_eq' := fun A hA => G25.slash_action_eq' A (hle25 hA)
      holo' := G25.holo'
      bdd_at_cusps' := fun hc => G25.bdd_at_cusps' (hc.mono hle25) }
  let H1 : ModularForm Γ 12 :=
    { toFun := H25
      slash_action_eq' := fun A hA => H25.slash_action_eq' A (hle25 hA)
      holo' := H25.holo'
      bdd_at_cusps' := fun hc => H25.bdd_at_cusps' (hc.mono hle25) }
  have hp : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH 25 N25.H25)]
    exact AddSubgroup.mem_zmultiples 1
  have qne (F : ModularForm Γ 12) (hF : F τ ≠ 0) :
      ((qExpansion 1 (F : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    intro hz
    have hF0 := (ModularForm.qExpansion_eq_zero_iff one_pos hp F).mp
      ((HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)) (by simpa using hz))
    exact hF (by rw [hF0]; rfl)
  have hH1τ : H1 τ ≠ 0 := by
    change H25 τ ≠ 0
    rw [hH25]
    exact ModularForm.discriminant_ne_zero _
  have hG0τ : G0 τ ≠ 0 := pow_ne_zero 3 hE
  have hH0τ : H0 τ ≠ 0 := ModularForm.discriminant_ne_zero _
  have hq0 :
      ((qExpansion 1 (G0 : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
        ((qExpansion 1 (H0 : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = jqModC ℂ := by
    have he4 : qExpansion 1 (G0 : UpperHalfPlane → ℂ) =
        qExpansion 1 (ModularForm.E₄ : UpperHalfPlane → ℂ) ^ 3 :=
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL ModularForm.E₄ 3
    rw [he4, PowerSeries.coe_pow, jqModC_eq_qExpansion_E4_cube_div_discriminant]
    rfl
  let G : ModularForm Γ (12 + 12) := G1.mul H0 - c • H1.mul G0
  let H : ModularForm Γ (12 + 12) := H1.mul G0
  have hq : (jqNModC ℂ 25 / jqModC ℂ - HahnSeries.C c) *
      ((qExpansion 1 (H : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (G : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    have h25 : jqNModC ℂ 25 =
      ((qExpansion 1 (G1 : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
        ((qExpansion 1 (H1 : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := hq25.symm
    dsimp only [G, H]
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos hp,
      FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hp,
      PowerSeries.smul_eq_C_mul, PowerSeries.coe_sub, PowerSeries.coe_mul,
      HahnSeries.ofPowerSeries_C,
      ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos hp,
      ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos hp,
      PowerSeries.coe_mul, PowerSeries.coe_mul, h25, ← hq0]
    field_simp [qne H1 hH1τ, qne G0 hG0τ, qne H0 hH0τ]
  rw [realizeOf_eq_div Γ (translation_mem_GammaH 25 N25.H25) G H _ hq τ
    (mul_ne_zero hH1τ hG0τ)]
  change (G25 τ * ModularForm.discriminant τ - c * (H25 τ * ModularForm.E₄ τ ^ 3)) /
    (H25 τ * ModularForm.E₄ τ ^ 3) = _
  rw [hG25, hH25]
  field_simp [ModularForm.discriminant_ne_zero τ,
    ModularForm.discriminant_ne_zero (ModularForm.heckeDiagMatrix 25 • τ), hE]

end N25
