-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_Q5
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T08:59:47.388834+00:00
-- url     : https://prove2.me/submissions/f7457241-6847-4721-9560-3b9acda602df

import Definitions.Def_HodgeComputerSSR_CoverParams
import Definitions.Def_HodgeComputerSSR_CoverFactors
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace SymmetricSexticResidual.CoverAlgebra
open SymmetricSexticResidual.K5Field QuadraticCovers Polynomial
open scoped BigOperators

noncomputable section CoverCoprimeQ5Proof

namespace Poly1009
lemma check_bez_Q5_Q5d : checkBez Q5_m_list 5 (pderiv Q5_m_list) bez_Q5_Q5d = true := by decide +kernel
lemma check_bez_Q5_Q7 : checkBez Q5_m_list 5 c_Q7 bez_Q5_Q7 = true := by decide +kernel
lemma check_bez_Q5_X : checkBez Q5_m_list 5 [0, 1] bez_Q5_X = true := by decide +kernel
lemma check_bez_Q5_Xm1 : checkBez Q5_m_list 5 [-1, 1] bez_Q5_Xm1 = true := by decide +kernel
lemma check_bez_Q5_cbh : checkBez Q5_m_list 5 c_cb_h bez_Q5_cbh = true := by decide +kernel
lemma check_bez_Q5_cah : checkBez Q5_m_list 5 c_ca_h bez_Q5_cah = true := by decide +kernel
lemma check_bez_Q5_nmWU : checkBez Q5_m_list 5 c_nm_WU bez_Q5_nmWU = true := by decide +kernel
lemma check_bez_Q5_discE0 : checkBez Q5_m_list 5 c_disc_E0 bez_Q5_discE0 = true := by decide +kernel

end Poly1009

lemma isCoprime_Q5_Q5_deriv : IsCoprime k5Params.Q5_z k5Params.Q5_z.derivative := by
  have hc := LocK5.ne_zero_of_evLoc Q5_lc_evLoc_ne
  rw [Q5_K5_eq_mul_monic, Polynomial.derivative_C_mul,
    isCoprime_C_mul_left_iff hc, isCoprime_C_mul_right_iff hc]
  have hcop : IsCoprime (Q5_m_loc.map evLoc) (Q5_m_loc.derivative.map evLoc) := by
    rw [← Polynomial.derivative_map, Q5_m_loc_spec.2.2.1, ← Poly1009.toPoly_pderiv]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_Q5_Q5d
  simpa only [Q5_m_K5, Polynomial.derivative_map] using
    isCoprime_of_evLoc_monic Q5_m_loc_spec.1 hcop

lemma isCoprime_Q5_Q7 : IsCoprime k5Params.Q5_z k5Params.Q7_z := by
  rw [Q5_K5_eq_mul_monic, isCoprime_C_mul_left_iff (LocK5.ne_zero_of_evLoc Q5_lc_evLoc_ne)]
  have hcop : IsCoprime (Q5_m_loc.map evLoc) (locParams.Q7_z.map evLoc) := by
    rw [Q5_m_loc_spec.2.2.1, CoverParams.map_Q7_z, locParams_map_evLoc, ← Poly1009.toPoly_c_Q7]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_Q5_Q7
  simpa only [Q5_m_K5, CoverParams.map_Q7_z, k5Params] using
    isCoprime_of_evLoc_monic Q5_m_loc_spec.1 hcop

lemma isCoprime_Q5_X : IsCoprime k5Params.Q5_z (X : K5[X]) := by
  rw [Q5_K5_eq_mul_monic, isCoprime_C_mul_left_iff (LocK5.ne_zero_of_evLoc Q5_lc_evLoc_ne)]
  have hcop : IsCoprime (Q5_m_loc.map evLoc) ((X : LocK5[X]).map evLoc) := by
    rw [Q5_m_loc_spec.2.2.1, Polynomial.map_X]
    simpa [Poly1009.toPoly] using Poly1009.isCoprime_of_checkBez Poly1009.check_bez_Q5_X
  simpa only [Q5_m_K5, Polynomial.map_X] using isCoprime_of_evLoc_monic Q5_m_loc_spec.1 hcop

lemma isCoprime_Q5_X_sub_1 : IsCoprime k5Params.Q5_z (X - 1 : K5[X]) := by
  rw [Q5_K5_eq_mul_monic, isCoprime_C_mul_left_iff (LocK5.ne_zero_of_evLoc Q5_lc_evLoc_ne)]
  have hcop : IsCoprime (Q5_m_loc.map evLoc) ((X - 1 : LocK5[X]).map evLoc) := by
    rw [Q5_m_loc_spec.2.2.1, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
    have hX1 : Poly1009.toPoly [-1, 1] = (X - 1 : (ZMod 1009)[X]) := by simp [Poly1009.toPoly]; ring
    rw [← hX1]; exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_Q5_Xm1
  simpa only [Q5_m_K5, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one] using
    isCoprime_of_evLoc_monic Q5_m_loc_spec.1 hcop

lemma isCoprime_Q5_cb_h : IsCoprime k5Params.Q5_z k5Params.cb_h := by
  rw [Q5_K5_eq_mul_monic, isCoprime_C_mul_left_iff (LocK5.ne_zero_of_evLoc Q5_lc_evLoc_ne)]
  have hcop : IsCoprime (Q5_m_loc.map evLoc) (locParams.cb_h.map evLoc) := by
    rw [Q5_m_loc_spec.2.2.1, CoverParams.map_cb_h, locParams_map_evLoc, ← Poly1009.toPoly_c_cb_h]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_Q5_cbh
  simpa only [Q5_m_K5, CoverParams.map_cb_h, k5Params] using
    isCoprime_of_evLoc_monic Q5_m_loc_spec.1 hcop

lemma isCoprime_Q5_ca_h : IsCoprime k5Params.Q5_z k5Params.ca_h := by
  rw [Q5_K5_eq_mul_monic, isCoprime_C_mul_left_iff (LocK5.ne_zero_of_evLoc Q5_lc_evLoc_ne)]
  have hcop : IsCoprime (Q5_m_loc.map evLoc) (locParams.ca_h.map evLoc) := by
    rw [Q5_m_loc_spec.2.2.1, CoverParams.map_ca_h, locParams_map_evLoc, ← Poly1009.toPoly_c_ca_h]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_Q5_cah
  simpa only [Q5_m_K5, CoverParams.map_ca_h, k5Params] using
    isCoprime_of_evLoc_monic Q5_m_loc_spec.1 hcop

lemma isCoprime_Q5_nm_WU : IsCoprime k5Params.Q5_z k5Params.nm_WU := by
  rw [Q5_K5_eq_mul_monic, isCoprime_C_mul_left_iff (LocK5.ne_zero_of_evLoc Q5_lc_evLoc_ne)]
  have hcop : IsCoprime (Q5_m_loc.map evLoc) (locParams.nm_WU.map evLoc) := by
    rw [Q5_m_loc_spec.2.2.1, CoverParams.map_nm_WU, locParams_map_evLoc, ← Poly1009.toPoly_c_nm_WU]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_Q5_nmWU
  simpa only [Q5_m_K5, CoverParams.map_nm_WU, k5Params] using
    isCoprime_of_evLoc_monic Q5_m_loc_spec.1 hcop

lemma isCoprime_Q5_disc_E0 : IsCoprime k5Params.Q5_z k5Params.disc_E0 := by
  rw [Q5_K5_eq_mul_monic, isCoprime_C_mul_left_iff (LocK5.ne_zero_of_evLoc Q5_lc_evLoc_ne)]
  have hcop : IsCoprime (Q5_m_loc.map evLoc) (locParams.disc_E0.map evLoc) := by
    rw [Q5_m_loc_spec.2.2.1, CoverParams.map_disc_E0, locParams_map_evLoc, ← Poly1009.toPoly_c_disc_E0]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_Q5_discE0
  simpa only [Q5_m_K5, CoverParams.map_disc_E0, k5Params] using
    isCoprime_of_evLoc_monic Q5_m_loc_spec.1 hcop

-- 4. All 11 lifted coprimalities for `P34_K5`!

private theorem cover_coprimalities_Q5_proof : CoverCoprimalityQ5Spec :=
  ⟨isCoprime_Q5_Q5_deriv, isCoprime_Q5_Q7, isCoprime_Q5_X, isCoprime_Q5_X_sub_1,
   isCoprime_Q5_cb_h, isCoprime_Q5_ca_h, isCoprime_Q5_nm_WU, isCoprime_Q5_disc_E0⟩

end CoverCoprimeQ5Proof
end SymmetricSexticResidual.CoverAlgebra

theorem solution : SymmetricSexticResidual.CoverAlgebra.CoverCoprimalityQ5Spec :=
  SymmetricSexticResidual.CoverAlgebra.cover_coprimalities_Q5_proof
