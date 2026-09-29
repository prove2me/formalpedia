-- Prove2me | solution 1 for ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/34fee5c2-69e4-5e37-830f-b0a155cb358e

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Theorems.Thm_ModularCurve_hasSum_jq_qParam
import Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant

open UpperHalfPlane
open scoped MatrixGroups

namespace SolJJ1Aux

private theorem hasSum_int {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m : ℤ =>
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ).coeff m *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ) := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have h0 := UpperHalfPlane.hasSum_qExpansion (f := (f : ℍ → ℂ)) one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) τ
  refine (Function.Injective.hasSum_iff Nat.cast_injective ?_).mp ?_
  · intro m hm
    rcases m with n | n
    · exact absurd ⟨n, rfl⟩ hm
    · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ (Int.negSucc_lt_zero n), zero_mul]
  · have hcomp : ((fun m : ℤ =>
        ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ).coeff m *
          Function.Periodic.qParam 1 (τ : ℂ) ^ m) ∘ (Nat.cast : ℕ → ℤ)) =
        fun n : ℕ => (qExpansion 1 (f : ℍ → ℂ)).coeff n •
          Function.Periodic.qParam 1 (τ : ℂ) ^ n := by
      funext n
      simp only [Function.comp_apply, smul_eq_mul, zpow_natCast,
        LaurentSeries.coeff_coe_powerSeries]
    rw [hcomp]
    exact h0

end SolJJ1Aux

theorem solution : ModularCurve.jqModC ℂ =
    (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 /
      ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by

  have hc : ∀ m : ℤ, (ModularCurve.jqModC ℂ).coeff m = ((ModularCurve.jq.coeff m : ℚ) : ℂ) := by
    intro m
    rw [← ModularCurve.coeffEmb_jq, ModularCurve.coeffEmb_coeff]
    exact eq_ratCast _ _

  have hjq : ∀ τ : ℍ, HasSum (fun m : ℤ => (ModularCurve.jqModC ℂ).coeff m *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) := by
    intro τ
    have h := ModularCurve.hasSum_jq_qParam τ
    simp only [← hc] at h
    exact h

  have hΔ : ∀ τ : ℍ, HasSum (fun m : ℤ =>
      ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) :
        LaurentSeries ℂ).coeff m *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.discriminant τ) := fun τ =>
    SolJJ1Aux.hasSum_int CuspForm.discriminant one_mem_strictPeriods_SL τ

  have hcube : ∀ τ : ℍ, HasSum (fun m : ℤ =>
      (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) :
        LaurentSeries ℂ) ^ 3).coeff m *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.E₄ τ ^ 3) := by
    intro τ
    have h := SolJJ1Aux.hasSum_int (ModularForm.E₄.pow 3) one_mem_strictPeriods_SL τ
    have h1 : qExpansion 1 ((ModularForm.E₄.pow 3) : ℍ → ℂ) =
        (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ 3 :=
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL ModularForm.E₄ 3
    have h2 : (ModularForm.E₄.pow 3) τ = ModularForm.E₄ τ ^ 3 := by
      rw [ModularForm.coe_pow, Pi.pow_apply]
    rw [h1, PowerSeries.coe_pow, h2] at h
    exact h

  have hmul : ∀ τ : ℍ, HasSum (fun m : ℤ =>
      ((ModularCurve.jqModC ℂ *
        ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) :
          LaurentSeries ℂ)).coeff m) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.E₄ τ ^ 3) := by
    intro τ
    have h : HasSum (fun m : ℤ =>
        ((ModularCurve.jqModC ℂ *
          ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) :
            LaurentSeries ℂ)).coeff m) *
          Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ * ModularForm.discriminant τ) :=
      ModularCurve.hasSum_qParam_mul_laurent 1 one_pos _ _ _ _ hjq hΔ τ
    rwa [div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)] at h

  have key : ModularCurve.jqModC ℂ *
      ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 :=
    ModularCurve.laurent_qParam_coeff_unique 1 one_pos
      (fun τ => ModularForm.E₄ τ ^ 3) _ _ hmul hcube

  have hΔne : ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) :
      LaurentSeries ℂ) ≠ 0 := by
    intro h0
    have h1 : qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) = 0 :=
      HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero])
    have h2 := ModularForm.discriminant_qExpansion_coeff_one
    rw [h1] at h2
    simp at h2
  rw [eq_div_iff hΔne]
  exact key

end S_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
end P2MW
export P2MW.S_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant (solution)
