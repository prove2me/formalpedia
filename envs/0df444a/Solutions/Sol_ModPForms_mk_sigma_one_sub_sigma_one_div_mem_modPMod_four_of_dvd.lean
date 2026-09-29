-- Prove2me | solution 1 for ModPForms.mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/bd073271-64e0-53d1-b2b5-406c1e3c9f79

import Definitions.Def_CuspForm_ModPForms
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.FieldTheory.Finite.Basic
import Theorems.Thm_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd
set_option autoImplicit false

namespace R3cB4

open UpperHalfPlane
open scoped MatrixGroups

private theorem natCast_pow_three {F : Type} [Field F] [CharP F 3] (e : ℕ) : (e : F) ^ 3 = (e : F) := by
  have h : ((e : ZMod 3) ^ 3 : ZMod 3) = (e : ZMod 3) := ZMod.pow_card (e : ZMod 3)
  have h' := congrArg (ZMod.castHom (dvd_refl 3) F) h
  simpa only [map_pow, map_natCast] using h'

private theorem sigma_three_cast {F : Type} [Field F] [CharP F 3] (m : ℕ) :
    ((ArithmeticFunction.sigma 3 m : ℕ) : F) = ((ArithmeticFunction.sigma 1 m : ℕ) : F) := by
  simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow, natCast_pow_three, pow_one]

private noncomputable def a4 (m : ℕ) : ℤ := PowerSeries.coeff m ModularCurve.eisenstein4

private theorem a4_eq (m : ℕ) : a4 m = if m = 0 then 1 else 240 * ((ArithmeticFunction.sigma 3 m : ℕ) : ℤ) := by
  unfold a4 ModularCurve.eisenstein4
  rw [PowerSeries.coeff_mk]
  split_ifs
  · rfl
  · simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow]

private theorem hasSum_E4 (τ : ℍ) :
    HasSum (fun m : ℕ => ((a4 m : ℤ) : ℂ) • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.E₄ τ) := by
  haveI : Fact (IsCusp OnePoint.infty (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods_SL⟩
  have h := hasSum_qExpansion (f := ⇑ModularForm.E₄) one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL)
    (ModularFormClass.holo ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄) τ
  simpa only [ModularCurve.qExpansion_E4_eq_map_eisenstein4, PowerSeries.coeff_map, a4,
    Int.coe_castRingHom] using h

private theorem qParam_heckeDiag {d : ℕ} (hd : d ≠ 0) (τ : ℍ) :
    Function.Periodic.qParam 1 ((ModularForm.heckeDiagMatrix d • τ : ℍ) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ d := by
  rw [ModularForm.coe_heckeDiagMatrix_smul hd]
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private noncomputable def c4 (d m : ℕ) : ℤ := if d ∣ m then a4 (m / d) else 0

private theorem hasSum_E4_heckeDiag {d : ℕ} (hd : d ≠ 0) (τ : ℍ) :
    HasSum (fun n : ℕ => ((c4 d n : ℤ) : ℂ) • Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (ModularForm.E₄ (ModularForm.heckeDiagMatrix d • τ)) := by
  have h := hasSum_E4 (ModularForm.heckeDiagMatrix d • τ)
  simp only [qParam_heckeDiag hd, ← pow_mul] at h
  have hinj : Function.Injective (fun m : ℕ => d * m) := mul_right_injective₀ hd
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro n hn
    have hdn : ¬ d ∣ n := fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
    simp [c4, hdn]
  · convert h using 1
    funext m
    simp [Function.comp, c4, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hd)]

private theorem coef_eq {d n : ℕ} (hd : d ≠ 0) :
    (240 : ℂ)⁻¹ * (((a4 n : ℤ) : ℂ) - ((c4 d n : ℤ) : ℂ)) =
      (((((ArithmeticFunction.sigma 3 n : ℕ) : ℤ) -
      (if d ∣ n then ((ArithmeticFunction.sigma 3 (n / d) : ℕ) : ℤ) else 0) : ℤ) : ℤ) : ℂ) := by
  unfold c4
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a4_eq]
  · have hn0 : n ≠ 0 := hn.ne'
    by_cases hdn : d ∣ n
    · have hq : n / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn hdn) (Nat.pos_of_ne_zero hd)).ne'
      simp only [hdn, if_true, a4_eq, hn0, hq, if_false]
      push_cast
      ring
    · simp only [hdn, if_false, a4_eq, hn0]
      push_cast
      ring

end R3cB4

open ModPForms in
theorem solution (N' : ℕ) [NeZero N'] (d : ℕ) (hd : d ∣ N')
    (F : Type) [Field F] [CharP F 3] :
    let B : PowerSeries F := PowerSeries.mk fun n : ℕ =>
      ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
        (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ) : F)
    B ∈ modPMod N' 4 F := by
  intro B
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact NeZero.ne N' (zero_dvd_iff.mp hd)
  obtain ⟨G1, hG1⟩ := ModularForm.exists_gamma0_qExpansion_eq_of_levelOne 1 ModularForm.E₄
  obtain ⟨GN, hGN⟩ := ModularForm.exists_gamma0_qExpansion_eq_of_levelOne N' ModularForm.E₄
  obtain ⟨g, hg⟩ := ModularForm.exists_degeneracy_Gamma0 (N := N') (M := 1) (d := d) (by rwa [mul_one]) G1
  set W : ModularForm (CongruenceSubgroup.Gamma0 N') 4 := (240 : ℂ)⁻¹ • (GN - g) with hW
  have hsum : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => ((240 : ℂ)⁻¹ * (((R3cB4.a4 n : ℤ) : ℂ) - ((R3cB4.c4 d n : ℤ) : ℂ))) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ n) (W τ) := by
    intro τ
    have h := ((R3cB4.hasSum_E4 τ).sub (R3cB4.hasSum_E4_heckeDiag hd0 τ)).const_smul ((240 : ℂ)⁻¹)
    have hGNτ : GN τ = ModularForm.E₄ τ := congrFun hGN τ
    have hgτ : g τ = ModularForm.E₄ (ModularForm.heckeDiagMatrix d • τ) := by
      rw [congrFun hg τ, congrFun hG1]
    convert h using 1 <;> try with_reducible_and_instances rfl
    · funext n
      simp only [smul_eq_mul]
      ring
    · rw [hW]
      simp [hGNτ, hgτ]
  have hΓ : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N' : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hcoef : ∀ n : ℕ, ModularFormClass.qCoeff W n = (((((ArithmeticFunction.sigma 3 n : ℕ) : ℤ) -
      (if d ∣ n then ((ArithmeticFunction.sigma 3 (n / d) : ℕ) : ℤ) else 0) : ℤ) : ℤ) : ℂ) := by
    intro n
    rw [ModularFormClass.qCoeff, ← ModularFormClass.qExpansion_coeff_unique (f := W) one_pos hΓ hsum n,
      R3cB4.coef_eq hd0]
  refine Submodule.subset_span ⟨W, fun n => (((ArithmeticFunction.sigma 3 n : ℕ) : ℤ) -
      (if d ∣ n then ((ArithmeticFunction.sigma 3 (n / d) : ℕ) : ℤ) else 0) : ℤ), hcoef, ?_⟩
  show PowerSeries.mk _ = PowerSeries.mk _
  congr 1
  funext n
  split_ifs with hdn <;> simp [hdn, R3cB4.sigma_three_cast]

end S_ModPForms_mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd
end P2MW
export P2MW.S_ModPForms_mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd (solution)
