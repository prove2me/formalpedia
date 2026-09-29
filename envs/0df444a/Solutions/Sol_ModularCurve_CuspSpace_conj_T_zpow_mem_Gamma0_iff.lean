-- Prove2me | solution 1 for ModularCurve.CuspSpace.conj_T_zpow_mem_Gamma0_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9909b6ef-b22e-518e-86d3-0ed46e3f3d82

import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CuspSpace_conj_T_zpow_mem_Gamma0_iff

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup ModularGroup
open scoped MatrixGroups
p2m_open "ModularCurve P2MW.S_ModularCurve_CuspSpace_conj_T_zpow_mem_Gamma0_iff.ModularCurve ModularCurve.CuspSpace P2MW.S_ModularCurve_CuspSpace_conj_T_zpow_mem_Gamma0_iff.ModularCurve.CuspSpace"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "mapGL_smul_infty CuspSpace CuspSpace.mk CuspSpace.cuspWidth"
namespace CuspSpace
p2m_export "ModularCurve.CuspSpace" "mk cuspWidth cuspWidth_mk_ratPoint"
p2m_open "ModularCurve.CuspSpace ModularCurve"

variable {N : ℕ}

theorem natCast_dvd_mul_iff_div_gcd_dvd {N K : ℕ} (hN : N ≠ 0) (m : ℤ) :
    (N : ℤ) ∣ (K : ℤ) * m ↔ ((N / Nat.gcd N K : ℕ) : ℤ) ∣ m := by
  set g : ℕ := Nat.gcd N K with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left K (Nat.pos_of_ne_zero hN)
  have hgN : g ∣ N := Nat.gcd_dvd_left N K
  have hgK : g ∣ K := Nat.gcd_dvd_right N K
  have hcop : Nat.Coprime (N / g) (K / g) := Nat.coprime_div_gcd_div_gcd hg0
  have hcopZ : IsCoprime ((N / g : ℕ) : ℤ) ((K / g : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop
  have hNg : (N : ℤ) = (g : ℤ) * ((N / g : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' hgN).symm
  have hKg : (K : ℤ) = (g : ℤ) * ((K / g : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' hgK).symm
  have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
  constructor
  · intro h
    rw [hNg, hKg, mul_assoc, mul_dvd_mul_iff_left hgZ] at h
    exact hcopZ.dvd_of_dvd_mul_left h
  · intro h
    rw [hNg, hKg, mul_assoc, mul_dvd_mul_iff_left hgZ]
    exact Dvd.dvd.mul_left h _

theorem conj_T_zpow_apply_one_zero (σ : SL(2, ℤ)) (m : ℤ) :
    (σ * T ^ m * σ⁻¹ : SL(2, ℤ)) 1 0 = -(σ 1 0 ^ 2 * m) := by
  have hinv : ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![σ 1 1, -σ 0 1; -σ 1 0, σ 0 0] := by
    rw [SL2_inv_expl σ]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hT : ((T ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, m; 0, 1] := coe_T_zpow m
  show ((σ * T ^ m * σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = _
  rw [coe_mul, coe_mul, hinv, hT]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem conj_T_zpow_mem_Gamma0_iff_raw (hN : N ≠ 0) (σ : SL(2, ℤ)) (m : ℤ) :
    σ * T ^ m * σ⁻¹ ∈ Gamma0 N ↔
      ((N / Nat.gcd ((σ 1 0).natAbs ^ 2) N : ℕ) : ℤ) ∣ m := by
  have hsq : (σ 1 0 : ℤ) ^ 2 = (((σ 1 0).natAbs ^ 2 : ℕ) : ℤ) := by
    rcases Int.natAbs_eq (σ 1 0) with h | h
    · conv_lhs => rw [h]
      push_cast
      ring
    · conv_lhs => rw [h]
      push_cast
      ring
  rw [Gamma0_mem_iff_dvd, conj_T_zpow_apply_one_zero, dvd_neg, hsq,
    natCast_dvd_mul_iff_div_gcd_dvd hN, Nat.gcd_comm N]

end ModularCurve.CuspSpace

end

theorem solution {N : ℕ} (hN : N ≠ 0) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (m : ℤ) :
    σ * ModularGroup.T ^ m * σ⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      (ModularCurve.CuspSpace.cuspWidth (ModularCurve.CuspSpace.mk N (Matrix.SpecialLinearGroup.mapGL ℚ σ • (∞ : OnePoint ℚ))) : ℤ) ∣ m := by

  have hdet : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have h := σ.2
    rw [Matrix.det_fin_two] at h
    exact h
  have hcol : IsCoprime (σ 0 0) (σ 1 0) := ⟨σ 1 1, -σ 0 1, by linear_combination hdet⟩
  rw [conj_T_zpow_mem_Gamma0_iff_raw hN σ m, mapGL_smul_infty, cuspWidth_mk_ratPoint hcol]

end S_ModularCurve_CuspSpace_conj_T_zpow_mem_Gamma0_iff
end P2MW
export P2MW.S_ModularCurve_CuspSpace_conj_T_zpow_mem_Gamma0_iff (solution)
