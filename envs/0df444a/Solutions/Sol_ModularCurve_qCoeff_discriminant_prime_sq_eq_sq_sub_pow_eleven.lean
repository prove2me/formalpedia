-- Prove2me | solution 1 for ModularCurve.qCoeff_discriminant_prime_sq_eq_sq_sub_pow_eleven
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/02f05f99-387e-5ec7-a094-5ace01760dbb

import Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.ModularForms.Discriminant
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix
import Theorems.Thm_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant
import Theorems.Thm_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qCoeff_discriminant_prime_sq_eq_sq_sub_pow_eleven
set_option autoImplicit false
set_option Elab.async false
open scoped ModularForm MatrixGroups

namespace S09CH

private lemma hp0 {p : ℕ} [Fact p.Prime] : p ≠ 0 := (Fact.out : p.Prime).ne_zero

private scoped instance instNeZeroOfFactPrime {p : ℕ} [Fact p.Prime] : NeZero p := ⟨hp0⟩

private lemma hΓ0 (p : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

private lemma tau_zero : ModularFormClass.qCoeff ModularForm.discriminant 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL

private lemma tau_one : ModularFormClass.qCoeff ModularForm.discriminant 1 = 1 :=
  ModularForm.discriminant_qExpansion_coeff_one

section DCoeff

variable {p : ℕ} [Fact p.Prime] (D : ModularForm (CongruenceSubgroup.Gamma0 p) 12)
  (hD : ⇑D = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p)

include hD

private lemma coe_D_eq :
    ⇑D = (p : ℂ) ^ 11 •
      fun τ : UpperHalfPlane => ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ) := by
  rw [hD]
  funext τ
  rw [ModularForm.slash_heckeDiagMatrix_apply _ (hp0 (p := p)), Pi.smul_apply, smul_eq_mul,
    show (12 : ℤ) - 1 = ((11 : ℕ) : ℤ) by norm_num, zpow_natCast]

private lemma qCoeff_D_eq (n : ℕ) :
    ModularFormClass.qCoeff ⇑D n = (p : ℂ) ^ 11 * ModularFormClass.qCoeff
      (fun τ : UpperHalfPlane => ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ)) n := by
  have hc : (p : ℂ) ^ 11 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (hp0 (p := p)))
  have hg : (fun τ : UpperHalfPlane => ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ))
      = ((p : ℂ) ^ 11)⁻¹ • ⇑D := by
    rw [coe_D_eq D hD, inv_smul_smul₀ hc]
  rw [hg]
  unfold ModularFormClass.qCoeff
  rw [ModularForm.qExpansion_smul one_pos (hΓ0 p) ((p : ℂ) ^ 11)⁻¹ D, map_smul, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

private lemma qCoeff_D_of_dvd {n : ℕ} (hn : p ∣ n) :
    ModularFormClass.qCoeff ⇑D n
      = (p : ℂ) ^ 11 * ModularFormClass.qCoeff ModularForm.discriminant (n / p) := by
  rw [qCoeff_D_eq D hD n]
  have h := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul CuspForm.discriminant
    one_mem_strictPeriods_SL (hp0 (p := p)) n
  rw [if_pos hn, CuspForm.coe_discriminant] at h
  exact congrArg (fun x => (p : ℂ) ^ 11 * x) h

private lemma qCoeff_D_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) : ModularFormClass.qCoeff ⇑D n = 0 := by
  rw [qCoeff_D_eq D hD n]
  have h := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul CuspForm.discriminant
    one_mem_strictPeriods_SL (hp0 (p := p)) n
  rw [if_neg hn, CuspForm.coe_discriminant] at h
  exact (congrArg (fun x => (p : ℂ) ^ 11 * x) h).trans (mul_zero _)

end DCoeff

private noncomputable def WF (p : ℕ) [Fact p.Prime] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (p : ℝ), 0] (by
    rw [Matrix.det_fin_two_of]
    have : (p : ℝ) ≠ 0 := by exact_mod_cast (hp0 (p := p))
    simpa using this)

private lemma WF_coe (p : ℕ) [Fact p.Prime] :
    ((WF p : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0] :=
  rfl

private lemma S_mapGL_coe :
    ((Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, ModularGroup.coe_S]
  ext i l
  fin_cases i <;> fin_cases l <;> simp [Matrix.map_apply]

private lemma heckeDiagMatrix_mul_WF (p : ℕ) [Fact p.Prime] (hpu : (p : ℝ) ≠ 0) :
    ModularForm.heckeDiagMatrix p * WF p
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) hpu)
        * Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeDiagMatrix (hp0 (p := p)), WF_coe]
  rw [show ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) hpu) :
      Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = Matrix.scalar (Fin 2) (p : ℝ) from rfl]
  rw [S_mapGL_coe, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]

private lemma slash_scalar {p : ℕ} {k : ℤ} (hpu : (p : ℝ) ≠ 0) (g : UpperHalfPlane → ℂ) :
    g ∣[k] (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) hpu))
      = (p : ℂ) ^ (k - 2) • g := by
  ext τ
  have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) hpu)).det.val : ℝ)
      = (p : ℝ) ^ 2 := by
    rw [Matrix.GeneralLinearGroup.det_scalar]
    simp [Fintype.card_fin]
  have hpos :
      0 < ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) hpu)).det.val : ℝ) := by
    rw [hdet]
    exact pow_two_pos_of_ne_zero hpu
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast (by exact_mod_cast hpu : p ≠ 0)
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hpos, hdet,
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar,
    abs_of_nonneg (sq_nonneg (p : ℝ))]
  simp only [ContinuousAlgEquiv.refl_apply, Units.val_mk0, Complex.ofReal_pow,
    Complex.ofReal_natCast, Pi.smul_apply, smul_eq_mul]
  have key : ((p : ℂ) ^ 2) ^ (k - 1) * (p : ℂ) ^ (-k) = (p : ℂ) ^ (k - 2) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hpc]
    congr 1
    push_cast
    ring
  rw [mul_assoc, key, mul_comm]

private lemma zpow_twelve_sub_two (p : ℕ) : (p : ℂ) ^ ((12 : ℤ) - 2) = (p : ℂ) ^ 10 := by
  rw [show (12 : ℤ) - 2 = ((10 : ℕ) : ℤ) by norm_num, zpow_natCast]

private lemma coe_D_slash_WF {p : ℕ} [Fact p.Prime]
    (D : ModularForm (CongruenceSubgroup.Gamma0 p) 12)
    (hD : ⇑D = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p) :
    ⇑D ∣[(12 : ℤ)] WF p = (p : ℂ) ^ 10 • ModularForm.discriminant := by
  have hpu : (p : ℝ) ≠ 0 := by exact_mod_cast (hp0 (p := p))
  rw [hD, ← SlashAction.slash_mul, heckeDiagMatrix_mul_WF p hpu, SlashAction.slash_mul,
    slash_scalar, zpow_twelve_sub_two]
  have h := ModularForm.SL_smul_slash (12 : ℤ) ModularGroup.S ModularForm.discriminant
    ((p : ℂ) ^ 10)
  rw [ModularForm.discriminant_S_invariant] at h
  exact h

private lemma trace12_coeff {p : ℕ} [Fact p.Prime]
    (D : ModularForm (CongruenceSubgroup.Gamma0 p) 12)
    (hDW : ⇑D ∣[(12 : ℤ)] WF p = (p : ℂ) ^ 10 • ModularForm.discriminant) :
    ∃ Y : ModularForm 𝒮ℒ 12, ∀ n : ℕ, ModularFormClass.qCoeff ⇑Y n
      = (p : ℂ) ^ 10 * ModularFormClass.qCoeff ⇑D n
        + (p : ℂ) ^ 10 * ModularFormClass.qCoeff ModularForm.discriminant (n * p) := by
  obtain ⟨Y, hY⟩ := ModularForm.exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke p 12 D
    (WF p) (WF_coe p)
  rw [hDW, zpow_twelve_sub_two] at hY
  refine ⟨Y, fun n => ?_⟩
  have hlaw := ModularFormClass.qCoeff_heckeU ((p : ℂ) ^ 10 • CuspForm.discriminant)
    one_mem_strictPeriods_SL (hp0 (p := p)) n
  rw [CuspForm.IsGLPos.coe_smul, CuspForm.coe_discriminant, ModularForm.coeffHeckeU_apply] at hlaw
  have hU : ModularForm.heckeU 12 p ((p : ℂ) ^ 10 • ModularForm.discriminant)
      = ⇑Y - (p : ℂ) ^ 10 • ⇑D := by
    rw [hY, add_sub_cancel_left]
  rw [hU] at hlaw
  have hYa := ModularFormClass.analyticAt_cuspFunction_zero Y one_pos one_mem_strictPeriods_SL
  have hsDa : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ((p : ℂ) ^ 10 • ⇑D)) 0 := by
    have h := ModularFormClass.analyticAt_cuspFunction_zero ((p : ℂ) ^ 10 • D) one_pos (hΓ0 p)
    rwa [ModularForm.IsGLPos.coe_smul] at h
  have hDelta : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
      one_mem_strictPeriods_SL
  unfold ModularFormClass.qCoeff at hlaw ⊢
  rw [UpperHalfPlane.qExpansion_sub hYa hsDa, map_sub,
    ModularForm.qExpansion_smul one_pos (hΓ0 p) ((p : ℂ) ^ 10) D, map_smul, smul_eq_mul,
    UpperHalfPlane.qExpansion_smul hDelta, map_smul, smul_eq_mul] at hlaw
  linear_combination hlaw

private lemma mordell_complex (p : ℕ) [Fact p.Prime] :
    ModularFormClass.qCoeff ModularForm.discriminant (p ^ 2)
      = ModularFormClass.qCoeff ModularForm.discriminant p ^ 2 - (p : ℂ) ^ 11 := by
  obtain ⟨D, hD⟩ := ModularCurve.exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix p
  obtain ⟨Y, hY⟩ := trace12_coeff D (coe_D_slash_WF D hD)

  have h0 : ModularFormClass.qCoeff ⇑Y 0 = 0 := by
    rw [hY 0, qCoeff_D_of_dvd D hD (dvd_zero p), Nat.zero_div, Nat.zero_mul, tau_zero]
    ring
  have hWL := ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant Y h0

  have h1 : ModularFormClass.qCoeff ⇑Y 1
      = (p : ℂ) ^ 10 * ModularFormClass.qCoeff ModularForm.discriminant p := by
    rw [hY 1, qCoeff_D_of_not_dvd D hD (Fact.out : p.Prime).not_dvd_one, Nat.one_mul]
    ring

  have hp' := hWL p
  rw [hY p, qCoeff_D_of_dvd D hD dvd_rfl, Nat.div_self (Nat.pos_of_ne_zero (hp0 (p := p))), tau_one,
    h1, show p * p = p ^ 2 from (sq p).symm] at hp'
  have hpc : (p : ℂ) ^ 10 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (hp0 (p := p)))
  have hkey : (p : ℂ) ^ 10 * (ModularFormClass.qCoeff ModularForm.discriminant (p ^ 2)
      - (ModularFormClass.qCoeff ModularForm.discriminant p ^ 2 - (p : ℂ) ^ 11)) = 0 := by
    linear_combination hp'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hkey).resolve_left hpc)

end S09CH
p2m_reactivate "P2MW.S_ModularCurve_qCoeff_discriminant_prime_sq_eq_sq_sub_pow_eleven.S09CH"

namespace ModularCurve p2m_export "ModularCurve" "exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix" end ModularCurve
p2m_open_scoped "ModularCurve" in
open S09CH in
private theorem ModularCurve.qCoeff_discriminant_prime_sq_eq_sq_sub_pow_eleven (p : ℕ) [Fact p.Prime] (t : ℕ → ℤ) (ht : ∀ n : ℕ, (t n : ℂ) = ModularFormClass.qCoeff ModularForm.discriminant n) : t (p ^ 2) = t p ^ 2 - (p : ℤ) ^ 11 := by
  have hC : (t (p ^ 2) : ℂ) = (t p : ℂ) ^ 2 - (p : ℂ) ^ 11 := by
    rw [ht, ht]
    exact mordell_complex p
  exact_mod_cast hC

theorem solution (p : ℕ) [Fact p.Prime] (t : ℕ → ℤ) (ht : ∀ n : ℕ, (t n : ℂ) = ModularFormClass.qCoeff ModularForm.discriminant n) : t (p ^ 2) = t p ^ 2 - (p : ℤ) ^ 11 :=
  ModularCurve.qCoeff_discriminant_prime_sq_eq_sq_sub_pow_eleven p t ht

end S_ModularCurve_qCoeff_discriminant_prime_sq_eq_sq_sub_pow_eleven
end P2MW
export P2MW.S_ModularCurve_qCoeff_discriminant_prime_sq_eq_sq_sub_pow_eleven (solution)
