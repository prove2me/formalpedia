-- Prove2me | solution 1 for ModularForm.exists_gamma0_four_apply_eq_apply_two_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/65c6cd09-999c-5540-a83d-d6f2c468fb62

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul
set_option autoImplicit false

p2m_open_scoped "MatrixGroups ModularForm P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.ModularForm Pointwise"
open UpperHalfPlane

noncomputable section

namespace ModularForm
p2m_export "ModularForm" "translate holo' slash_def ext IsGLPos.smul_apply smul_apply bdd_at_cusps' coe_translate"
namespace LevelTwoDegeneracy
p2m_open "ModularForm"

def restrict {k : ℤ} {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (F : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := F
  slash_action_eq' γ hγ := SlashInvariantForm.slash_action_eqn F γ (h hγ)
  holo' := F.holo'
  bdd_at_cusps' hc := F.bdd_at_cusps' (hc.mono h)

@[scoped simp] theorem coe_restrict {k : ℤ} {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ)
    (F : ModularForm Γ k) : ⇑(restrict h F) = ⇑F := rfl

def gTwo : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(2 : ℝ), 0; 0, 1] (by norm_num [Matrix.det_fin_two_of])

@[scoped simp] theorem val_gTwo : (gTwo : Matrix (Fin 2) (Fin 2) ℝ) = !![(2 : ℝ), 0; 0, 1] := rfl

theorem det_gTwo : (Matrix.GeneralLinearGroup.det gTwo : ℝ) = 2 := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]

theorem Gamma0_four_le :
    ((CongruenceSubgroup.Gamma0 4 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct gTwo⁻¹ • (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
  rintro _ ⟨A, hA, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  have h4 : (4 : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp (CongruenceSubgroup.Gamma0_mem.mp hA)
  obtain ⟨c', hc'⟩ : (2 : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := (by norm_num : (2:ℤ) ∣ 4).trans h4
  have hdet : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    rw [← Matrix.det_fin_two, A.det_coe]
  let B : SL(2, ℤ) := ⟨!![(A : Matrix (Fin 2) (Fin 2) ℤ) 0 0, 2 * (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      c', (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hc'⟩
  refine ⟨B, ?_⟩
  show Matrix.SpecialLinearGroup.mapGL ℝ B = gTwo * Matrix.SpecialLinearGroup.mapGL ℝ A * gTwo⁻¹
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  simp only [Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix, val_gTwo]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, B, hc', mul_comm]

theorem gTwo_smul (z : ℍ) : gTwo • z = (⟨2, two_pos⟩ : {x : ℝ // 0 < x}) • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [det_gTwo]; norm_num), UpperHalfPlane.coe_pos_real_smul]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom]

theorem slash_gTwo_apply (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] gTwo) z = (2 : ℂ) ^ (k - 1) * f ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) • z) := by
  rw [ModularForm.slash_def]
  simp only [← gTwo_smul]
  have hden : UpperHalfPlane.denom gTwo (z : ℂ) = 1 := by simp [UpperHalfPlane.denom]
  rw [hden, one_zpow, mul_one, det_gTwo]
  have : (UpperHalfPlane.σ gTwo) (f (gTwo • z)) = f (gTwo • z) := by
    rw [UpperHalfPlane.σ, if_pos (show (0:ℝ) < ↑(Matrix.GeneralLinearGroup.det gTwo) by rw [det_gTwo]; norm_num)]
    rfl
  rw [this, mul_comm]
  norm_num

end ModularForm.LevelTwoDegeneracy
p2m_reactivate "P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.ModularForm P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.ModularForm.LevelTwoDegeneracy"
p2m_reactivate "P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.ModularForm"

end
p2m_reactivate "P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.ModularForm P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.ModularForm.LevelTwoDegeneracy"

open ModularForm.LevelTwoDegeneracy in
theorem solution {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 4) k,
      ∀ z : UpperHalfPlane, g z = f ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) • z) := by
  have h2k : ((2 : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ two_ne_zero
  refine ⟨((2 : ℂ) ^ (k - 1))⁻¹ • restrict Gamma0_four_le (ModularForm.translate f gTwo), fun z => ?_⟩
  rw [ModularForm.IsGLPos.smul_apply, coe_restrict, ModularForm.coe_translate, slash_gTwo_apply,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h2k, one_mul]

end S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul
end P2MW
export P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul (solution)
