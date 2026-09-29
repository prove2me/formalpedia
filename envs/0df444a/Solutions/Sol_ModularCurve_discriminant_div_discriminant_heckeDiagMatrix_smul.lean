-- Prove2me | solution 1 for ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/770d0625-92a8-5cd1-b933-e875da2cf6a9

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Discriminant
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "exists_sl2_heckeDiagMatrix_smul_eq"
p2m_open "ModularCurve"

namespace QexpN

theorem discriminant_div_discriminant_heckeDiagMatrix_smul' (N : ℕ) [NeZero N]
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (τ : UpperHalfPlane) :
    ModularForm.discriminant (γ • τ)
        / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • γ • τ)
      = ModularForm.discriminant τ
        / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) := by
  obtain ⟨γ', hact, hden⟩ := ModularCurve.exists_sl2_heckeDiagMatrix_smul_eq N γ hγ
  have hγSL : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hγ'SL : (mapGL ℝ γ' : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ', rfl⟩
  have hΔγ : ModularForm.discriminant (γ • τ)
      = UpperHalfPlane.denom (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (τ : ℂ) ^ (12 : ℤ)
        * ModularForm.discriminant τ := by
    have h := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγSL τ
    simp [CuspForm.coe_discriminant] at h
    exact h
  have hΔγ' : ModularForm.discriminant (γ' • ModularForm.heckeDiagMatrix N • τ)
      = UpperHalfPlane.denom (γ' : Matrix.GeneralLinearGroup (Fin 2) ℝ)
          (((ModularForm.heckeDiagMatrix N • τ : UpperHalfPlane)) : ℂ) ^ (12 : ℤ)
        * ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) := by
    have h := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ'SL
        (ModularForm.heckeDiagMatrix N • τ)
    simp [CuspForm.coe_discriminant] at h
    exact h
  rw [hact τ, hΔγ, hΔγ', hden τ,
    mul_div_mul_left _ _ (zpow_ne_zero 12 (UpperHalfPlane.denom_ne_zero _ _))]

end QexpN

end ModularCurve

end

theorem solution (N : ℕ) [NeZero N] (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) : ModularForm.discriminant (γ • τ) / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • γ • τ) = ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) :=
  ModularCurve.QexpN.discriminant_div_discriminant_heckeDiagMatrix_smul' N γ hγ τ

end S_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul
end P2MW
export P2MW.S_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul (solution)
