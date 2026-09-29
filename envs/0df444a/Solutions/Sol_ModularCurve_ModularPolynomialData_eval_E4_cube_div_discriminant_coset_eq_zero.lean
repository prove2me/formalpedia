-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9fda4869-e363-5b9e-a9c7-640238431521

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero
import Theorems.Thm_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero.ModularCurve UpperHalfPlane Polynomial"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "ModularPolynomialData primCosetReps mem_primCosetReps ModularPolynomialData.eval_E4_cube_div_discriminant_smul_eq_zero"
namespace CosetRootAux
p2m_open "ModularCurve"

def jt (z : ℍ) : ℂ := (ModularForm.E₄ : ℍ → ℂ) z ^ 3 / ModularForm.discriminant z

theorem sl_mem (γ : SL(2, ℤ)) : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩

theorem jt_smul (γ : SL(2, ℤ)) (z : ℍ) : jt ((γ : GL (Fin 2) ℝ) • z) = jt z := by
  unfold jt
  have h4 := SlashInvariantForm.slash_action_eqn'' (ModularForm.E₄) (sl_mem γ) z
  have h12 := SlashInvariantForm.slash_action_eqn'' (CuspForm.discriminant) (sl_mem γ) z
  rw [CuspForm.coe_discriminant] at h12
  have hd : denom (γ : GL (Fin 2) ℝ) (z : ℂ) ≠ 0 := UpperHalfPlane.denom_ne_zero _ z
  have hΔ : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  rw [show (ModularForm.E₄ : ℍ → ℂ) ((γ : GL (Fin 2) ℝ) • z) = ModularForm.E₄ ((γ : GL (Fin 2) ℝ) • z) from rfl, h4, h12]
  field_simp

theorem upperTriangularGL_eq {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (γ₁ γ₂ : SL(2, ℤ))
    (hM : !![(a : ℤ), b; 0, d] = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ))
    (had' : (a : ℝ) * d ≠ 0) :
    ModularForm.upperTriangularGL a b d had' = (γ₁ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix N * (γ₂ : GL (Fin 2) ℝ) := by
  apply Units.ext
  have hmap := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℝ)) hM
  simp only [Matrix.map_mul] at hmap
  rw [Units.val_mul, Units.val_mul, ModularForm.val_upperTriangularGL, ModularForm.val_heckeDiagMatrix hN]
  convert hmap using 3 <;> first | rfl | (ext i j; fin_cases i <;> fin_cases j <;> simp) | (ext i j; fin_cases i <;> fin_cases j <;> rfl)

theorem coe_upperTriangularGL_smul {a b d : ℕ} (ha : 0 < a) (hd : 0 < d) (had' : (a : ℝ) * d ≠ 0) (τ : ℍ) :
    ((ModularForm.upperTriangularGL a b d had' • τ : ℍ) : ℂ) = ((a : ℂ) * τ + b) / d := by
  have hdet : 0 < ((ModularForm.upperTriangularGL (a : ℝ) b d had').det : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ModularForm.val_upperTriangularGL, Matrix.det_fin_two_of]
    have : (0 : ℝ) < a * d := mul_pos (by exact_mod_cast ha) (by exact_mod_cast hd)
    linarith
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, ModularForm.val_upperTriangularGL]

end ModularCurve.CosetRootAux

open ModularCurve.CosetRootAux in
theorem solution (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) {a b d : ℕ} (habd : (a, b, d) ∈ ModularCurve.primCosetReps N)
    (τ τ' : ℍ) (hτ' : (τ' : ℂ) = ((a : ℂ) * τ + b) / d) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        ((ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ))).eval
      ((ModularForm.E₄ : ℍ → ℂ) τ' ^ 3 / ModularForm.discriminant τ') = 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  rw [mem_primCosetReps hN] at habd
  obtain ⟨had, hbd, hgcd⟩ := habd
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; exact hN (by simpa using had.symm))
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact hN (by simpa using had.symm))
  have had' : (a : ℝ) * d ≠ 0 := by exact_mod_cast (mul_pos ha hd).ne'
  obtain ⟨γ₁, γ₂, hM⟩ := Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one hN had hgcd
  set g : GL (Fin 2) ℝ := ModularForm.upperTriangularGL a b d had' with hg
  have hgeq : g = (γ₁ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix N * (γ₂ : GL (Fin 2) ℝ) :=
    upperTriangularGL_eq hN had γ₁ γ₂ hM had'
  have hτ'pt : τ' = g • τ := UpperHalfPlane.ext (by rw [hτ', hg, coe_upperTriangularGL_smul ha hd had'])
  set σ : ℍ := (γ₂ : GL (Fin 2) ℝ) • τ with hσ
  have h1 : τ' = (γ₁ : GL (Fin 2) ℝ) • (ModularForm.heckeDiagMatrix N • σ) := by
    rw [hτ'pt, hgeq, mul_smul, mul_smul]

  change (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (jt τ))).eval (jt τ') = 0
  rw [h1, jt_smul, show jt τ = jt σ from by rw [hσ, jt_smul]]
  exact ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_smul_eq_zero N data σ _
    (ModularForm.coe_heckeDiagMatrix_smul hN σ)

end

end S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero (solution)
