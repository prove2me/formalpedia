-- Prove2me | solution 1 for N25.jqTwentyFive_form_ratio
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:37.158958+00:00
-- url     : https://prove2.me/submissions/b49c6d48-93cc-44fc-907d-92d152be7e64

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique

set_option autoImplicit false

open UpperHalfPlane

open scoped MatrixGroups

namespace N25

private theorem gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private theorem gamma0_one_coe :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  simp [gamma0_one_eq_top, MonoidHom.range_eq_map]

private theorem one_mem_sp (N : ℕ) : (1 : ℝ) ∈
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

private theorem hasSum_int {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m : ℤ =>
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ).coeff m *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ) := by
  let : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
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

private theorem hasSum_qExpand (ℓ : ℕ) [NeZero ℓ] {A : LaurentSeries ℂ} {S : ℂ} {τ : ℍ}
    (h : HasSum (fun m : ℤ => A.coeff m *
      Function.Periodic.qParam 1 (((ModularForm.heckeDiagMatrix ℓ • τ : ℍ)) : ℂ) ^ m) S) :
    HasSum (fun m : ℤ => (ModularCurve.qExpand ℂ ℓ A).coeff m *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) S := by
  have hq : Function.Periodic.qParam 1 (((ModularForm.heckeDiagMatrix ℓ • τ : ℍ)) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ (ℓ : ℕ) := by
    rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne ℓ) τ]
    unfold Function.Periodic.qParam
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [hq] at h
  have hinj : Function.Injective (fun m : ℤ => (ℓ : ℤ) * m) :=
    mul_right_injective₀ (by exact_mod_cast NeZero.ne ℓ)
  refine (Function.Injective.hasSum_iff hinj ?_).mp ?_
  · intro m hm
    have hnd : ¬ ((ℓ : ℕ) : ℤ) ∣ m := by
      rintro ⟨c, rfl⟩
      exact hm ⟨c, rfl⟩
    rw [ModularCurve.qExpand_coeff_of_not_dvd ℓ A hnd, zero_mul]
  · have hcomp : ((fun m : ℤ => (ModularCurve.qExpand ℂ ℓ A).coeff m *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) ∘ (fun m : ℤ => (ℓ : ℤ) * m)) =
        fun m : ℤ => A.coeff m *
          (Function.Periodic.qParam 1 (τ : ℂ) ^ (ℓ : ℕ)) ^ m := by
      funext m
      simp only [Function.comp_apply]
      rw [ModularCurve.qExpand_coeff_mul, zpow_mul, zpow_natCast]
    rw [hcomp]
    exact h

private theorem qExpansion_coe_dilate {ℓ : ℕ} [NeZero ℓ] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 1) k)
    (g : ModularForm (CongruenceSubgroup.Gamma0 ℓ) k)
    (hg : ⇑g = fun τ => f (ModularForm.heckeDiagMatrix ℓ • τ)) :
    ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ModularCurve.qExpand ℂ ℓ
        ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  refine ModularCurve.laurent_qParam_coeff_unique 1 one_pos (g : ℍ → ℂ) _ _
    (hasSum_int g (one_mem_sp ℓ)) ?_
  intro τ
  have h := hasSum_qExpand ℓ (hasSum_int f (one_mem_sp 1) (ModularForm.heckeDiagMatrix ℓ • τ))
  rw [show f (ModularForm.heckeDiagMatrix ℓ • τ) = g τ from by rw [hg]] at h
  exact h

/-- Concrete dilated Eisenstein/discriminant forms realize the exact level-25 j-series. -/
theorem _root_.solution :
    ∃ G H : ModularForm (CongruenceSubgroup.Gamma0 25) 12,
      (∀ τ : UpperHalfPlane, G τ = ModularForm.E₄ (ModularForm.heckeDiagMatrix 25 • τ) ^ 3) ∧
      (∀ τ : UpperHalfPlane, H τ = ModularForm.discriminant (ModularForm.heckeDiagMatrix 25 • τ)) ∧
      H ≠ 0 ∧
      ((qExpansion 1 (G : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
        ((qExpansion 1 (H : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ModularCurve.jqNModC ℂ 25 := by
  let e4cube : ModularForm (CongruenceSubgroup.Gamma0 1) 12 :=
    ModularForm.mcast (by norm_num) (ModularForm.E₄.pow 3) gamma0_one_coe
  let delta1 : ModularForm (CongruenceSubgroup.Gamma0 1) 12 :=
    ModularForm.mcast rfl (CuspForm.toModularFormₗ CuspForm.discriminant) gamma0_one_coe
  obtain ⟨G, hG⟩ := ModularForm.exists_degeneracy_Gamma0
    (show 25 * 1 ∣ 25 by norm_num) e4cube
  obtain ⟨H, hH⟩ := ModularForm.exists_degeneracy_Gamma0
    (show 25 * 1 ∣ 25 by norm_num) delta1
  have hGL := qExpansion_coe_dilate e4cube G hG
  have hHL := qExpansion_coe_dilate delta1 H hH
  refine ⟨G, H, ?_, ?_, ?_, ?_⟩
  · intro τ
    rw [hG]
    rfl
  · intro τ
    rw [hH]
    rfl
  · intro h0
    have h1 := congrFun hH UpperHalfPlane.I
    rw [h0] at h1
    exact ModularForm.discriminant_ne_zero
      (ModularForm.heckeDiagMatrix 25 • UpperHalfPlane.I) h1.symm
  · have he4 : qExpansion 1 (e4cube : UpperHalfPlane → ℂ) =
        (qExpansion 1 (ModularForm.E₄ : UpperHalfPlane → ℂ)) ^ 3 := by
      change qExpansion 1 (ModularForm.E₄.pow 3 : UpperHalfPlane → ℂ) = _
      exact ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL ModularForm.E₄ 3
    have hΔ1 : qExpansion 1 (delta1 : UpperHalfPlane → ℂ) =
        qExpansion 1 (ModularForm.discriminant : UpperHalfPlane → ℂ) := rfl
    rw [hGL, hHL, he4, hΔ1,
      show ModularCurve.jqNModC ℂ 25 = ModularCurve.qExpand ℂ 25 (ModularCurve.jqModC ℂ) from rfl,
      ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, map_div₀,
      PowerSeries.coe_pow]

end N25
