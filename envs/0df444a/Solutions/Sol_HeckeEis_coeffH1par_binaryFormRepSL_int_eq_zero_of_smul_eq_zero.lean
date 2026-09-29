-- Prove2me | solution 1 for HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/946f2acf-dae8-5c62-a2c7-f5ead815e7b5

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Theorems.Thm_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self
import Theorems.Thm_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero

set_option autoImplicit false

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst_C binaryFormRepSL binaryFormRepSL_apply_coe mem_coeffCoboundaries_iff coeffH1par coeffH1parMk_surjective coeffH1parMk_eq_zero_iff exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self"
p2m_open "HeckeEis"

open MvPolynomial CongruenceSubgroup
open scoped MatrixGroups

namespace TorsionFreeAux

def gammaT (N : ℕ) : Gamma0 N := ⟨ModularGroup.T, by rw [Gamma0_mem]; simp [ModularGroup.coe_T]⟩

@[scoped simp] theorem coe_gammaT (N : ℕ) : ((gammaT N : Gamma0 N) : SL(2, ℤ)) = ModularGroup.T := rfl

def lowerSL (N : ℕ) : SL(2, ℤ) := ⟨!![1, 0; (N : ℤ), 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] theorem coe_lowerSL (N : ℕ) : ((lowerSL N : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; (N : ℤ), 1] := rfl

def gammaL (N : ℕ) : Gamma0 N := ⟨lowerSL N, by rw [Gamma0_mem]; simp [lowerSL]⟩

@[scoped simp] theorem coe_gammaL (N : ℕ) : ((gammaL N : Gamma0 N) : SL(2, ℤ)) = lowerSL N := rfl

theorem trace_sq_gammaT (N : ℕ) : (((gammaT N : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [coe_gammaT, ModularGroup.coe_T, Matrix.trace_fin_two_of]; norm_num

theorem trace_sq_gammaL (N : ℕ) : (((gammaL N : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [coe_gammaL, coe_lowerSL, Matrix.trace_fin_two_of]; norm_num

theorem binaryFormRepSL_apply_of_zero {R : Type*} [CommRing R] (g : SL(2, ℤ)) (P : ↥(BinaryForm R 0)) :
    binaryFormRepSL R 0 g P = P := by
  apply Subtype.ext
  rw [binaryFormRepSL_apply_coe]
  have hP : (P : MvPolynomial (Fin 2) R) = MvPolynomial.C (MvPolynomial.coeff 0 (P : MvPolynomial (Fin 2) R)) := by
    have h := (MvPolynomial.mem_homogeneousSubmodule 0 (P : MvPolynomial (Fin 2) R)).mp P.2
    rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous] at h
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h)
  rw [hP, binarySubst_C]

theorem aux_fix {M : Type*} [AddCommGroup M] (f : M →+ M) (m : ℤ) (v w z : M)
    (hv : f v - v = m • z) (hw : f w - w = z) : f (v - m • w) = v - m • w := by
  rw [map_sub, map_zsmul, sub_eq_iff_eq_add.mp hv, ← hw, zsmul_sub]
  abel

theorem aux_div {M : Type*} [AddCommGroup M] (cf : M →+ ℤ) (m c₁ : ℤ) (v w₁ w₂ e : M)
    (he : cf e = 1) (h1 : v - m • w₁ = c₁ • e) (h2 : cf (v - m • w₂) = 0) :
    v = m • (w₁ + (cf w₂ - cf w₁) • e) := by
  have k1 : cf v - m * cf w₁ = c₁ := by
    have := congrArg cf h1
    rwa [map_sub, map_zsmul, map_zsmul, he, zsmul_eq_mul, zsmul_eq_mul, mul_one] at this
  have k2 : cf v - m * cf w₂ = 0 := by rwa [map_sub, map_zsmul, zsmul_eq_mul] at h2
  have hc : c₁ = m * (cf w₂ - cf w₁) := by linear_combination -k1 + k2
  rw [sub_eq_iff_eq_add'.mp h1, hc, zsmul_add, mul_zsmul]

theorem aux_cancel {M : Type*} [AddCommGroup M] (f : M →+ M) (m : ℤ) (hinj : ∀ x : M, m • x = 0 → x = 0)
    (v' z : M) (h : f (m • v') - m • v' = m • z) : f v' - v' = z := by
  rw [map_zsmul, ← zsmul_sub] at h
  have h0 : m • (f v' - v' - z) = 0 := by rw [zsmul_sub, h, sub_self]
  exact sub_eq_zero.mp (hinj _ h0)

end TorsionFreeAux
p2m_reactivate "P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero.HeckeEis.TorsionFreeAux"

open TorsionFreeAux in

theorem SolMain.A4 (n N : ℕ) [NeZero N] (m : ℤ) (hm : m ≠ 0)
    (x : coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)) (hx : m • x = 0) : x = 0 := by
  classical
  obtain ⟨z, rfl⟩ := coeffH1parMk_surjective _ x
  rw [← map_zsmul, coeffH1parMk_eq_zero_iff, mem_coeffCoboundaries_iff] at hx
  obtain ⟨v, hv⟩ := hx

  have hv' : ∀ g : Gamma0 N, binaryFormRepSL ℤ n (g : SL(2, ℤ)) v - v = m • (z : Gamma0 N → ↥(BinaryForm ℤ n)) g :=
    fun g => by simpa using congrFun hv g
  rw [coeffH1parMk_eq_zero_iff, mem_coeffCoboundaries_iff]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  ·
    subst hn0
    refine ⟨0, funext fun g => ?_⟩
    have h1 : m • (z : Gamma0 N → ↥(BinaryForm ℤ 0)) g = 0 := by
      rw [← hv' g, sub_eq_zero]
      exact binaryFormRepSL_apply_of_zero _ _
    have h2 : (z : Gamma0 N → ↥(BinaryForm ℤ 0)) g = 0 := (smul_eq_zero.mp h1).resolve_left hm
    rw [h2, sub_eq_zero]
    exact binaryFormRepSL_apply_of_zero _ _
  ·
    obtain ⟨w₁, hw₁⟩ := z.2.2 (gammaT N) (trace_sq_gammaT N)
    obtain ⟨w₂, hw₂⟩ := z.2.2 (gammaL N) (trace_sq_gammaL N)

    have hfix : ∀ (γ : Gamma0 N) (w : ↥(BinaryForm ℤ n)), (((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) γ - 1) w = (z : Gamma0 N → _) γ →
        binaryFormRepSL ℤ n (γ : SL(2, ℤ)) (v - m • w) = v - m • w :=
      fun γ w hw => aux_fix (binaryFormRepSL ℤ n (γ : SL(2, ℤ))).toAddMonoidHom m v w _ (hv' γ)
        (by rw [LinearMap.sub_apply, Module.End.one_apply] at hw; exact hw)
    have hjR : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : ℤ) ≠ 0 := fun j hj _ => by exact_mod_cast Nat.one_le_iff_ne_zero.mp hj
    obtain ⟨c₁, hc₁⟩ := exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self (R := ℤ) n (h := 1) (by norm_num) hjR
      (v - m • w₁) (by simpa using hfix (gammaT N) w₁ hw₁)
    have hN : ((N : ℤ) : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    obtain ⟨c₂, hc₂⟩ := exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self (R := ℤ) n (h := (N : ℤ)) hN hjR
      (lowerSL N) (coe_lowerSL N) (v - m • w₂) (hfix (gammaL N) w₂ hw₂)

    have hX0 : MvPolynomial.X 0 ^ n ∈ BinaryForm ℤ n :=
      (MvPolynomial.mem_homogeneousSubmodule n _).mpr (MvPolynomial.isHomogeneous_X_pow 0 n)
    set e : ↥(BinaryForm ℤ n) := ⟨MvPolynomial.X 0 ^ n, hX0⟩ with he
    have hc₁' : v - m • w₁ = c₁ • e := Subtype.ext (by rw [hc₁]; rfl)

    set cf : ↥(BinaryForm ℤ n) →ₗ[ℤ] ℤ := (MvPolynomial.lcoeff ℤ (Finsupp.single 0 n)).comp (BinaryForm ℤ n).subtype with hcf
    have hcf_apply : ∀ Q : ↥(BinaryForm ℤ n), cf Q = MvPolynomial.coeff (Finsupp.single 0 n) (Q : MvPolynomial (Fin 2) ℤ) :=
      fun Q => rfl
    have hcfe : cf e = 1 := by rw [hcf_apply]; simp [e, MvPolynomial.coeff_X_pow]
    have h2 : cf (v - m • w₂) = 0 := by
      rw [hcf_apply, hc₂, MvPolynomial.coeff_smul, MvPolynomial.coeff_X_pow, if_neg, smul_zero]
      intro h; have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h; simp at this; omega
    have hvm := aux_div cf.toAddMonoidHom m c₁ v w₁ w₂ e hcfe hc₁' h2
    have hinj : ∀ y : ↥(BinaryForm ℤ n), m • y = 0 → y = 0 := fun y hy => (smul_eq_zero.mp hy).resolve_left hm
    refine ⟨w₁ + (cf w₂ - cf w₁) • e, funext fun g =>
      aux_cancel (binaryFormRepSL ℤ n (g : SL(2, ℤ))).toAddMonoidHom m hinj _ _ ?_⟩
    have h1 := hv' g
    rw [hvm] at h1
    exact h1

end HeckeEis
p2m_reactivate "P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero.HeckeEis.TorsionFreeAux P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero.HeckeEis"

open scoped MatrixGroups in
theorem solution (n N : ℕ) [NeZero N] (m : ℤ) (hm : m ≠ 0)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hx : m • x = 0) : x = 0 :=
  HeckeEis.SolMain.A4 n N m hm x hx

#print axioms solution

end S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero
end P2MW
export P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero (solution)
