-- Prove2me | solution 1 for HeckeEis.exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/366cfae1-47bc-538a-be49-9d1ca67982e6

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Theorems.Thm_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self

set_option autoImplicit false

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binarySubst_X binaryFormRepSL binaryFormRepSL_apply_coe exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self"
p2m_open "HeckeEis"

open MvPolynomial
open scoped MatrixGroups

theorem UnipotentFixedAux.eq_S_mul_T_zpow_neg_mul_S_inv {h : ℤ} (g : SL(2, ℤ))
    (hg : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; h, 1]) :
    g = ModularGroup.S * ModularGroup.T ^ (-h) * ModularGroup.S⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, ModularGroup.coe_T_zpow, ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem UnipotentFixedAux.binarySubst_S_X_zero_pow (R : Type*) [CommRing R] (n : ℕ) :
    binarySubst R ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (MvPolynomial.X 0 ^ n)
      = (MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) R) := by
  rw [map_pow, binarySubst_X, ModularGroup.coe_S]
  simp [Fin.sum_univ_two]

open UnipotentFixedAux in

theorem SolMain.A3 {R : Type*} [CommRing R] [IsDomain R] (n : ℕ)
    {h : ℤ} (hh : (h : R) ≠ 0) (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0)
    (g : SL(2, ℤ)) (hg : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; h, 1])
    (P : ↥(BinaryForm R n)) (hP : binaryFormRepSL R n g P = P) :
    ∃ c : R, (P : MvPolynomial (Fin 2) R) = c • MvPolynomial.X 1 ^ n := by
  have hgS := eq_S_mul_T_zpow_neg_mul_S_inv g hg
  set Q : ↥(BinaryForm R n) := binaryFormRepSL R n ModularGroup.S⁻¹ P with hQ
  have hQfix : binaryFormRepSL R n (ModularGroup.T ^ (-h)) Q = Q := by
    have h1 : binaryFormRepSL R n ModularGroup.S⁻¹ (binaryFormRepSL R n g P) = Q := by rw [hP]
    rwa [hgS, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (binaryFormRepSL R n _),
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
  have hh' : ((-h : ℤ) : R) ≠ 0 := by rw [Int.cast_neg]; exact neg_ne_zero.mpr hh
  obtain ⟨c, hc⟩ := exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self n hh' hn Q hQfix
  refine ⟨c, ?_⟩
  have hPQ : P = binaryFormRepSL R n ModularGroup.S Q := by
    rw [hQ, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hPQ, binaryFormRepSL_apply_coe, hc, map_smul, binarySubst_S_X_zero_pow]

end HeckeEis

open scoped MatrixGroups in
theorem solution {R : Type*} [CommRing R] [IsDomain R] (n : ℕ)
    {h : ℤ} (hh : (h : R) ≠ 0) (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0)
    (g : SL(2, ℤ)) (hg : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; h, 1])
    (P : ↥(HeckeEis.BinaryForm R n)) (hP : HeckeEis.binaryFormRepSL R n g P = P) :
    ∃ c : R, (P : MvPolynomial (Fin 2) R) = c • MvPolynomial.X 1 ^ n :=
  HeckeEis.SolMain.A3 n hh hn g hg P hP

#print axioms solution

end S_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self
end P2MW
export P2MW.S_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self (solution)
