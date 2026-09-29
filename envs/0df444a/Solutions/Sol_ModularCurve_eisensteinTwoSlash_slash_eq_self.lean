-- Prove2me | solution 1 for ModularCurve.eisensteinTwoSlash_slash_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/1434e3ad-06a2-5979-9f6f-67d247014c76

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisensteinTwoSlash_slash_eq_self
set_option autoImplicit false
open UpperHalfPlane Matrix MatrixGroups
open scoped ModularForm

namespace S09RD

theorem sub_slash (k : ℤ) (B : Matrix.GeneralLinearGroup (Fin 2) ℝ) (f g : ℍ → ℂ) :
    (f - g) ∣[k] B = f ∣[k] B - g ∣[k] B := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]

theorem slash_mapGL (k : ℤ) (f : ℍ → ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = f ∣[k] γ := rfl

theorem conj_det (p : ℕ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hc : (p : ℤ) ∣ γ 1 0) :
    Matrix.det !![γ 0 0, (p : ℤ) * γ 0 1; γ 1 0 / (p : ℤ), γ 1 1] = 1 := by
  have h1 : (p : ℤ) * (γ 1 0 / (p : ℤ)) = γ 1 0 := Int.mul_ediv_cancel' hc
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h2 := γ.2
    rwa [Matrix.det_fin_two] at h2
  rw [Matrix.det_fin_two_of]
  have hb : (p : ℤ) * γ 0 1 * (γ 1 0 / (p : ℤ)) = γ 0 1 * γ 1 0 := by
    rw [mul_comm (p : ℤ) (γ 0 1), mul_assoc, h1]
  omega

theorem val_heckeDiagMatrix_eq_map (p : ℕ) (hp : p ≠ 0) :
    ((ModularForm.heckeDiagMatrix p : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (!![(p : ℤ), 0; 0, 1]).map (algebraMap ℤ ℝ) := by
  rw [ModularForm.val_heckeDiagMatrix hp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_mapGL_eq_map (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ((γ : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ ℝ) := rfl

theorem heckeDiag_mul_mapGL (p : ℕ) (hp : p ≠ 0) (γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hZ : !![(p : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ)
        = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(p : ℤ), 0; 0, 1]) :
    ModularForm.heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ γ
      = Matrix.SpecialLinearGroup.mapGL ℝ γ' * ModularForm.heckeDiagMatrix p := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeDiagMatrix_eq_map p hp,
    coe_mapGL_eq_map, coe_mapGL_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, hZ]

theorem D2_slash_heckeDiag (p : ℕ) (hp : p ≠ 0) (γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h10 : (γ' 1 0 : ℤ) = γ 1 0 / (p : ℤ)) (h11 : (γ' 1 1 : ℤ) = γ 1 1)
    (hc : (p : ℤ) ∣ γ 1 0) :
    (EisensteinSeries.D2 γ') ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p = EisensteinSeries.D2 γ := by
  ext τ
  rw [ModularForm.slash_heckeDiagMatrix_apply _ hp]
  simp only [EisensteinSeries.D2]
  rw [ModularGroup.denom_apply, ModularGroup.denom_apply, ModularForm.coe_heckeDiagMatrix_smul hp]
  have hdiv : ((γ 1 0 / (p : ℤ) : ℤ) : ℂ) * (p : ℂ) = ((γ 1 0 : ℤ) : ℂ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (Int.ediv_mul_cancel hc)
  have h10' : ((γ' 1 0 : ℤ) : ℂ) = ((γ 1 0 / (p : ℤ) : ℤ) : ℂ) := by exact_mod_cast h10
  have h11' : ((γ' 1 1 : ℤ) : ℂ) = ((γ 1 1 : ℤ) : ℂ) := by exact_mod_cast h11
  rw [h10', h11', show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one, ← mul_assoc, hdiv,
    mul_div_assoc']
  congr 1
  linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hdiv

end S09RD

private theorem ModularCurve.eisensteinTwoSlash_slash_eq_self (p : ℕ) [NeZero p] :
    ∀ γ ∈ ((CongruenceSubgroup.Gamma0 p : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      (EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - EisensteinSeries.E2) ∣[(2 : ℤ)] γ
        = EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - EisensteinSeries.E2 := by
  have hp : p ≠ 0 := NeZero.ne p
  intro γ hγ
  obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
  have hc : (p : ℤ) ∣ γ₀ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (CongruenceSubgroup.Gamma0_mem.mp hγ₀)
  obtain ⟨γ', h10, h11, hval⟩ :
      ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        (γ' 1 0 : ℤ) = γ₀ 1 0 / (p : ℤ) ∧ (γ' 1 1 : ℤ) = γ₀ 1 1 ∧
          (γ' : Matrix (Fin 2) (Fin 2) ℤ)
            = !![γ₀ 0 0, (p : ℤ) * γ₀ 0 1; γ₀ 1 0 / (p : ℤ), γ₀ 1 1] :=
    ⟨⟨!![γ₀ 0 0, (p : ℤ) * γ₀ 0 1; γ₀ 1 0 / (p : ℤ), γ₀ 1 1], S09RD.conj_det p γ₀ hc⟩,
      rfl, rfl, rfl⟩
  have hZ : !![(p : ℤ), 0; 0, 1] * (γ₀ : Matrix (Fin 2) (Fin 2) ℤ)
      = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(p : ℤ), 0; 0, 1] := by
    rw [hval]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Int.ediv_mul_cancel hc, mul_comm]
  have hconj := S09RD.heckeDiag_mul_mapGL p hp γ₀ γ' hZ
  rw [S09RD.sub_slash, ← SlashAction.slash_mul, hconj, SlashAction.slash_mul,
    S09RD.slash_mapGL, S09RD.slash_mapGL,
    EisensteinSeries.E2_slash_action γ', EisensteinSeries.E2_slash_action γ₀,
    S09RD.sub_slash, ModularForm.smul_slash, ModularForm.σ_heckeDiagMatrix,
    S09RD.D2_slash_heckeDiag p hp γ₀ γ' h10 h11 hc]
  simp only [ContinuousAlgEquiv.refl_apply]
  abel

open scoped ModularForm in
theorem solution : ∀ (p : ℕ) [NeZero p], ∀ γ ∈ ((CongruenceSubgroup.Gamma0 p : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), (EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - EisensteinSeries.E2) ∣[(2 : ℤ)] γ = EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - EisensteinSeries.E2 :=
  @ModularCurve.eisensteinTwoSlash_slash_eq_self

end S_ModularCurve_eisensteinTwoSlash_slash_eq_self
end P2MW
export P2MW.S_ModularCurve_eisensteinTwoSlash_slash_eq_self (solution)
