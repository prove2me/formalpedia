-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T08:48:43.565372+00:00
-- url     : https://prove2.me/submissions/2d2dcebd-6a87-4eac-afc9-264a90c60a11

import Definitions.Def_HodgeComputerFormal_LaurentJets
import Definitions.Def_HodgeComputerSSR_K5Field
import Definitions.Def_HodgeComputerSSR_CoverParams
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_deg_bounds
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_X15_dvd
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace SymmetricSexticResidual.CoverAlgebra
open SymmetricSexticResidual.K5Field QuadraticCovers Polynomial
open scoped BigOperators LaurentSeries PowerSeries

noncomputable section CoverFactorProof

private lemma k5Params_Q5_z_natDegree_le : k5Params.Q5_z.natDegree ≤ 5 :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_deg_bounds.1
private lemma k5Params_Q7_z_natDegree_le : k5Params.Q7_z.natDegree ≤ 7 :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_deg_bounds.2.1
private lemma nm_z_K5_natDegree_le : k5Params.nm_z.natDegree ≤ 73 :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_deg_bounds.2.2
private lemma X_pow_15_dvd_nm_z_K5 : (X : K5[X]) ^ 15 ∣ k5Params.nm_z :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_X15_dvd

namespace Poly1009
lemma check_nm_z_factor :
    peq c_nm_z (psmul 946 (pshift 15 (pmul (ppow cb_h_m_list 12) P34_m_list))) = true := by
  decide +kernel

end Poly1009

lemma k5Params_nm_z_elim_symm :
    k5Params.ca_h ^ 12 * k5Params.nm_z = k5Params.cb_h ^ 12 * k5Params.nm_w := by
  apply evalInvT_injective
  have hcb_ne : evalInvT k5Params.cb_h ≠ 0 := by
    intro h0
    have hcb0 : k5Params.cb_h = 0 := evalInvT_injective (h0.trans (map_zero _).symm)
    have hloc : locParams.cb_h = 0 :=
      Polynomial.map_injective LocK5.subtype Subtype.val_injective (by
        rw [CoverParams.map_cb_h, Polynomial.map_zero]; exact hcb0)
    have hev : Poly1009.toPoly Poly1009.c_cb_h = 0 := by
      rw [Poly1009.toPoly_c_cb_h, ← locParams_map_evLoc, ← CoverParams.map_cb_h, hloc, Polynomial.map_zero]
    have h82 := Poly1009.toPoly_eq_of_peq Poly1009.check_cb_h_monic
    rw [hev, Poly1009.toPoly_psmul] at h82
    have hc2 := congrArg (fun p => p.coeff 2) h82
    rw [Polynomial.coeff_zero, Polynomial.coeff_C_mul, Poly1009.toPoly_coeff_getD] at hc2
    exact (by decide : (0 : ZMod 1009) ≠ 82 * Poly1009.cb_h_m_list.getD 2 0) hc2
  have hbranch (w : LaurentSeries K5)
      (hw_eq : w ^ 2 + evalInvT k5Params.bW * w + evalInvT k5Params.cW = 0) :
      evalInvT k5Params.ca_h ^ 6 * PairAlg.evalAt w (PairAlg.map evalInvT k5Params.res_z) =
        evalInvT k5Params.cb_h ^ 6 * PairAlg.evalAt w (PairAlg.map evalInvT k5Params.res_w) := by
    apply mul_left_cancel₀ (pow_ne_zero 6 hcb_ne)
    rw [CoverParams.res_z, CoverParams.res_w, map_syl5Pair, map_syl5Pair,
      evalAt_syl5Pair _ _ _ _ _ _ _ _ _ w hw_eq, evalAt_syl5Pair _ _ _ _ _ _ _ _ _ w hw_eq]
    have haux := syl5_elim_symm_aux
      (evalInvT k5Params.ca_h) (evalInvT k5Params.cb_h)
      (PairAlg.evalAt w (PairAlg.map evalInvT k5Params.c0W))
      (evalInvT k5Params.q20) (evalInvT k5Params.q11) (evalInvT k5Params.q02)
      (w * PairAlg.evalAt w (PairAlg.map evalInvT k5Params.k2W))
      (evalInvT k5Params.c30) (evalInvT k5Params.c21) (evalInvT k5Params.c12) (evalInvT k5Params.c03)
      (w * w * PairAlg.evalAt w (PairAlg.map evalInvT k5Params.k3W))
    have hd2_2 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.d2_2) =
        evalInvT k5Params.q20 * evalInvT k5Params.cb_h ^ 2 -
        evalInvT k5Params.q11 * evalInvT k5Params.ca_h * evalInvT k5Params.cb_h +
        evalInvT k5Params.q02 * evalInvT k5Params.ca_h ^ 2 := by
      simp only [CoverParams.d2_2, CoverParams.Q5_z, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar,
        map_add, map_sub, map_mul, map_pow]
    have hd2_1 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.d2_1) =
        (-evalInvT k5Params.q11 * evalInvT k5Params.cb_h + 2 * evalInvT k5Params.q02 * evalInvT k5Params.ca_h) *
          PairAlg.evalAt w (PairAlg.map evalInvT k5Params.c0W) := by
      simp only [CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul, map_add, map_mul, map_neg, map_ofNat]
    have hd2_0 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.d2_0) =
        evalInvT k5Params.q02 * PairAlg.evalAt w (PairAlg.map evalInvT k5Params.c0W) ^ 2 +
        evalInvT k5Params.cb_h ^ 2 * (w * PairAlg.evalAt w (PairAlg.map evalInvT k5Params.k2W)) := by
      simp only [CoverParams.d2_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul, PairAlg.map_mul,
        PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ w hw_eq,
        PairAlg.evalAt_W, map_pow]; ring
    have hd3_3 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.d3_3) =
        evalInvT k5Params.c30 * evalInvT k5Params.cb_h ^ 3 -
        evalInvT k5Params.c21 * evalInvT k5Params.ca_h * evalInvT k5Params.cb_h ^ 2 +
        evalInvT k5Params.c12 * evalInvT k5Params.ca_h ^ 2 * evalInvT k5Params.cb_h -
        evalInvT k5Params.c03 * evalInvT k5Params.ca_h ^ 3 := by
      simp only [CoverParams.d3_3, CoverParams.Q7_z, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar,
        map_add, map_sub, map_mul, map_pow]
    have hd3_2 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.d3_2) =
        (-evalInvT k5Params.c21 * evalInvT k5Params.cb_h ^ 2 +
         2 * evalInvT k5Params.c12 * evalInvT k5Params.ca_h * evalInvT k5Params.cb_h -
         3 * evalInvT k5Params.c03 * evalInvT k5Params.ca_h ^ 2) *
          PairAlg.evalAt w (PairAlg.map evalInvT k5Params.c0W) := by
      simp only [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul, map_add, map_sub, map_mul,
        map_pow, map_neg, map_ofNat]
    have hd3_1 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.d3_1) =
        (evalInvT k5Params.c12 * evalInvT k5Params.cb_h - 3 * evalInvT k5Params.c03 * evalInvT k5Params.ca_h) *
          PairAlg.evalAt w (PairAlg.map evalInvT k5Params.c0W) ^ 2 := by
      simp only [CoverParams.d3_1, CoverParams.pmul, PairAlg.map_smul, PairAlg.map_mul,
        PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ w hw_eq, map_sub, map_mul, map_ofNat]; ring
    have hd3_0 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.d3_0) =
        -evalInvT k5Params.c03 * PairAlg.evalAt w (PairAlg.map evalInvT k5Params.c0W) ^ 3 +
        evalInvT k5Params.cb_h ^ 3 * (w * w * PairAlg.evalAt w (PairAlg.map evalInvT k5Params.k3W)) := by
      simp only [CoverParams.d3_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul, PairAlg.map_mul,
        PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ w hw_eq,
        PairAlg.evalAt_W, map_neg, map_pow]; ring
    have he2_2 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.e2_2) =
        evalInvT k5Params.q20 * evalInvT k5Params.cb_h ^ 2 -
        evalInvT k5Params.q11 * evalInvT k5Params.ca_h * evalInvT k5Params.cb_h +
        evalInvT k5Params.q02 * evalInvT k5Params.ca_h ^ 2 := by
      simp only [CoverParams.e2_2, CoverParams.Q5_z, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar,
        map_add, map_sub, map_mul, map_pow]
    have he2_1 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.e2_1) =
        (-evalInvT k5Params.q11 * evalInvT k5Params.ca_h + 2 * evalInvT k5Params.q20 * evalInvT k5Params.cb_h) *
          PairAlg.evalAt w (PairAlg.map evalInvT k5Params.c0W) := by
      simp only [CoverParams.e2_1, PairAlg.map_smul, PairAlg.evalAt_smul, map_add, map_mul, map_neg, map_ofNat]
    have he2_0 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.e2_0) =
        evalInvT k5Params.q20 * PairAlg.evalAt w (PairAlg.map evalInvT k5Params.c0W) ^ 2 +
        evalInvT k5Params.ca_h ^ 2 * (w * PairAlg.evalAt w (PairAlg.map evalInvT k5Params.k2W)) := by
      simp only [CoverParams.e2_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul, PairAlg.map_mul,
        PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ w hw_eq,
        PairAlg.evalAt_W, map_pow]; ring
    have he3_3 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.e3_3) =
        -evalInvT k5Params.c30 * evalInvT k5Params.cb_h ^ 3 +
        evalInvT k5Params.c21 * evalInvT k5Params.ca_h * evalInvT k5Params.cb_h ^ 2 -
        evalInvT k5Params.c12 * evalInvT k5Params.ca_h ^ 2 * evalInvT k5Params.cb_h +
        evalInvT k5Params.c03 * evalInvT k5Params.ca_h ^ 3 := by
      simp only [CoverParams.e3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar,
        map_add, map_sub, map_mul, map_pow, map_neg]
    have he3_2 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.e3_2) =
        (-3 * evalInvT k5Params.c30 * evalInvT k5Params.cb_h ^ 2 +
         2 * evalInvT k5Params.c21 * evalInvT k5Params.ca_h * evalInvT k5Params.cb_h -
         evalInvT k5Params.c12 * evalInvT k5Params.ca_h ^ 2) *
          PairAlg.evalAt w (PairAlg.map evalInvT k5Params.c0W) := by
      simp only [CoverParams.e3_2, PairAlg.map_smul, PairAlg.evalAt_smul, map_add, map_sub, map_mul,
        map_pow, map_neg, map_ofNat]
    have he3_1 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.e3_1) =
        (-3 * evalInvT k5Params.c30 * evalInvT k5Params.cb_h + evalInvT k5Params.c21 * evalInvT k5Params.ca_h) *
          PairAlg.evalAt w (PairAlg.map evalInvT k5Params.c0W) ^ 2 := by
      simp only [CoverParams.e3_1, CoverParams.pmul, PairAlg.map_smul, PairAlg.map_mul,
        PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ w hw_eq, map_add, map_mul, map_neg, map_ofNat]; ring
    have he3_0 : PairAlg.evalAt w (PairAlg.map evalInvT k5Params.e3_0) =
        -evalInvT k5Params.c30 * PairAlg.evalAt w (PairAlg.map evalInvT k5Params.c0W) ^ 3 +
        evalInvT k5Params.ca_h ^ 3 * (w * w * PairAlg.evalAt w (PairAlg.map evalInvT k5Params.k3W)) := by
      simp only [CoverParams.e3_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul, PairAlg.map_mul,
        PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ w hw_eq,
        PairAlg.evalAt_W, map_neg, map_pow]; ring
    rw [hd2_2, hd2_1, hd2_0, hd3_3, hd3_2, hd3_1, hd3_0,
        he2_2, he2_1, he2_0, he3_3, he3_2, he3_1, he3_0]
    exact haux
  have h1 := hbranch W1_inf W1_inf_eq
  have h2 := hbranch W2_inf W2_inf_eq
  rw [map_mul, map_mul, map_pow, map_pow, CoverParams.nm_z, CoverParams.nm_w,
    CoverParams.pnm, CoverParams.pnm, PairAlg.map_nm, PairAlg.map_nm,
    PairAlg.evalAt_nm _ _ W1_inf W2_inf W1_W2_inf_sum W1_W2_inf_prod,
    PairAlg.evalAt_nm _ _ W1_inf W2_inf W1_W2_inf_sum W1_W2_inf_prod]
  calc evalInvT k5Params.ca_h ^ 12 *
        (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z) *
         PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z))
      = (evalInvT k5Params.ca_h ^ 6 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z)) *
        (evalInvT k5Params.ca_h ^ 6 * PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)) := by ring
    _ = (evalInvT k5Params.cb_h ^ 6 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_w)) *
        (evalInvT k5Params.cb_h ^ 6 * PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_w)) := by rw [h1, h2]
    _ = _ := by ring

/-- Normalize `f : LocK5[X]` of degree `≤ d` whose `evLoc`-image is `C c * M` (`M` monic of
degree `d`, `c ≠ 0`) into a monic degree-`d` polynomial in `LocK5[X]`. -/
lemma monicOfEvLoc {f : LocK5[X]} {d : ℕ} {c : ZMod 1009} {M : (ZMod 1009)[X]}
    (hdeg : f.natDegree ≤ d) (hc : c ≠ 0) (hMm : M.Monic) (hMd : M.natDegree = d)
    (hev : f.map evLoc = C c * M) :
    ∃ (lc : LocK5) (hlc : evLoc lc ≠ 0),
      let fm := C (LocK5.invOfNe lc hlc) * f
      fm.Monic ∧ fm.natDegree = d ∧ fm.map evLoc = M ∧ f = C lc * fm := by
  have hev_d : evLoc (f.coeff d) = c := by
    rw [← Polynomial.coeff_map, hev, Polynomial.coeff_C_mul, ← hMd, hMm.coeff_natDegree, mul_one]
  have hlc : evLoc (f.coeff d) ≠ 0 := hev_d.symm ▸ hc
  refine ⟨f.coeff d, hlc, ?_, ?_, ?_, ?_⟩
  · have hle : (C (LocK5.invOfNe (f.coeff d) hlc) * f).natDegree ≤ d :=
      (Polynomial.natDegree_C_mul_le _ _).trans hdeg
    have hcd : (C (LocK5.invOfNe (f.coeff d) hlc) * f).coeff d = 1 := by
      rw [Polynomial.coeff_C_mul, LocK5.invOfNe_mul]
    have hge : d ≤ (C (LocK5.invOfNe (f.coeff d) hlc) * f).natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hcd]; exact one_ne_zero)
    rw [Polynomial.Monic, Polynomial.leadingCoeff, le_antisymm hle hge, hcd]
  · have hle : (C (LocK5.invOfNe (f.coeff d) hlc) * f).natDegree ≤ d :=
      (Polynomial.natDegree_C_mul_le _ _).trans hdeg
    have hcd : (C (LocK5.invOfNe (f.coeff d) hlc) * f).coeff d = 1 := by
      rw [Polynomial.coeff_C_mul, LocK5.invOfNe_mul]
    exact le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (by rw [hcd]; exact one_ne_zero))
  · rw [Polynomial.map_mul, Polynomial.map_C, LocK5.evLoc_invOfNe, hev_d, hev,
      ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  · rw [← mul_assoc, ← map_mul, LocK5.mul_invOfNe, map_one, one_mul]

private lemma locParams_natDegree_le_of_K5 {f : LocK5[X]} {d : ℕ}
    (h : (f.map LocK5.subtype).natDegree ≤ d) : f.natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero] at h ⊢
  intro n hn
  apply Subtype.ext
  have := h n hn
  rwa [Polynomial.coeff_map] at this


lemma M39_loc_dvd_nm_z : M39_loc ∣ locParams.nm_z := by
  have hcb_dvd : k5Params.cb_h ^ 12 ∣ k5Params.nm_z := by
    have hcop12 : IsCoprime (k5Params.cb_h ^ 12) (k5Params.ca_h ^ 12) :=
      (isCoprime_cb_h_ca_h.pow_left).pow_right
    exact hcop12.dvd_of_dvd_mul_left ⟨k5Params.nm_w, k5Params_nm_z_elim_symm⟩
  have hcbm_dvd : cb_h_m_K5 ^ 12 ∣ k5Params.nm_z := by
    rw [cb_h_K5_eq_mul_monic, mul_pow] at hcb_dvd
    exact (dvd_mul_left _ _).trans hcb_dvd
  have hcopX : IsCoprime ((X : K5[X]) ^ 15) (cb_h_m_K5 ^ 12) := by
    have h1 : IsCoprime (X : K5[X]) cb_h_m_K5 := by
      have h := isCoprime_cb_h_X.symm
      rwa [cb_h_K5_eq_mul_monic, isCoprime_C_mul_right_iff (LocK5.ne_zero_of_evLoc cb_h_lc_evLoc_ne)] at h
    exact (h1.pow_left).pow_right
  have hM_dvd_K5 : M39_K5 ∣ k5Params.nm_z := by
    have hM_eq : M39_K5 = (X : K5[X]) ^ 15 * cb_h_m_K5 ^ 12 := by
      simp [M39_K5, M39_loc, cb_h_m_K5]
    rw [hM_eq]
    exact hcopX.mul_dvd X_pow_15_dvd_nm_z_K5 hcbm_dvd
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd M39_loc_monic]
  apply Polynomial.map_injective LocK5.subtype Subtype.val_injective
  rw [Polynomial.map_zero, Polynomial.map_modByMonic LocK5.subtype M39_loc_monic,
    CoverParams.map_nm_z]
  exact (Polynomial.modByMonic_eq_zero_iff_dvd (M39_loc_monic.map LocK5.subtype)).mpr hM_dvd_K5


lemma nm_z_loc_eq_M39_mul_Q34 : locParams.nm_z = M39_loc * Q34_loc := by
  have hdiv := Polynomial.modByMonic_add_div locParams.nm_z M39_loc
  have hrem : locParams.nm_z %ₘ M39_loc = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd M39_loc_monic).mpr M39_loc_dvd_nm_z
  rw [hrem, zero_add] at hdiv
  exact hdiv.symm

lemma Q34_loc_evLoc : Q34_loc.map evLoc = C 946 * Poly1009.toPoly Poly1009.P34_m_list := by
  have hnm := congrArg (Polynomial.map evLoc) nm_z_loc_eq_M39_mul_Q34
  rw [Polynomial.map_mul, CoverParams.map_nm_z, locParams_map_evLoc, ← Poly1009.toPoly_c_nm_z,
    Poly1009.toPoly_eq_of_peq Poly1009.check_nm_z_factor, Poly1009.toPoly_psmul,
    Poly1009.toPoly_pshift, Poly1009.toPoly_pmul, Poly1009.toPoly_ppow] at hnm
  have hM_ev : M39_loc.map evLoc = X ^ 15 * (Poly1009.toPoly Poly1009.cb_h_m_list) ^ 12 := by
    simp only [M39_loc, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, cb_h_m_loc_spec.2.2.1]
  have hM_ne : M39_loc.map evLoc ≠ 0 := (M39_loc_monic.map evLoc).ne_zero
  apply mul_left_cancel₀ hM_ne
  rw [← hnm, hM_ev]; ring

lemma Q34_loc_natDegree_le : Q34_loc.natDegree ≤ 34 := by
  have hnm73 : locParams.nm_z.natDegree ≤ 73 :=
    locParams_natDegree_le_of_K5 (by rw [CoverParams.map_nm_z]; exact nm_z_K5_natDegree_le)
  have hQ34_ne : Q34_loc ≠ 0 := by
    intro h0
    have := Q34_loc_evLoc
    rw [h0, Polynomial.map_zero] at this
    have hc := congrArg (fun p => p.coeff 34) this
    rw [Polynomial.coeff_zero, Polynomial.coeff_C_mul, ← Poly1009.P34_m_list_monic.2,
      Poly1009.P34_m_list_monic.1.coeff_natDegree, mul_one] at hc
    exact (by decide : (0 : ZMod 1009) ≠ 946) hc
  have hdeg_mul : locParams.nm_z.natDegree = 39 + Q34_loc.natDegree := by
    rw [nm_z_loc_eq_M39_mul_Q34, M39_loc_monic.natDegree_mul' hQ34_ne, M39_loc_natDegree]
  omega

lemma Q34_lc_evLoc_ne : evLoc (Q34_loc.coeff 34) ≠ 0 := by
  rw [← Polynomial.coeff_map, Q34_loc_evLoc, Polynomial.coeff_C_mul,
    ← Poly1009.P34_m_list_monic.2, Poly1009.P34_m_list_monic.1.coeff_natDegree, mul_one]
  decide


lemma Q5_m_loc_spec :
    Q5_m_loc.Monic ∧ Q5_m_loc.natDegree = 5 ∧
    Q5_m_loc.map evLoc = Poly1009.toPoly Poly1009.Q5_m_list ∧
    locParams.Q5_z = C (locParams.Q5_z.coeff 5) * Q5_m_loc := by
  have hdeg : locParams.Q5_z.natDegree ≤ 5 :=
    locParams_natDegree_le_of_K5 (by rw [CoverParams.map_Q5_z]; exact k5Params_Q5_z_natDegree_le)
  have hev_d : evLoc (locParams.Q5_z.coeff 5) = 909 := by
    rw [← Polynomial.coeff_map, Q5_evLoc, Polynomial.coeff_C_mul,
      ← Poly1009.Q5_m_list_monic.2, Poly1009.Q5_m_list_monic.1.coeff_natDegree, mul_one]
  have hcd : Q5_m_loc.coeff 5 = 1 := by
    rw [Q5_m_loc, Polynomial.coeff_C_mul, LocK5.invOfNe_mul]
  have hnd : Q5_m_loc.natDegree = 5 :=
    le_antisymm ((Polynomial.natDegree_C_mul_le _ _).trans hdeg)
      (Polynomial.le_natDegree_of_ne_zero (by rw [hcd]; exact one_ne_zero))
  refine ⟨by rw [Polynomial.Monic, Polynomial.leadingCoeff, hnd, hcd], hnd, ?_, ?_⟩
  · rw [Q5_m_loc, Polynomial.map_mul, Polynomial.map_C, LocK5.evLoc_invOfNe, hev_d, Q5_evLoc,
      ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by decide : (909 : ZMod 1009) ≠ 0), map_one, one_mul]
  · rw [Q5_m_loc, ← mul_assoc, ← map_mul, LocK5.mul_invOfNe, map_one, one_mul]

lemma Q5_K5_eq_mul_monic :
    k5Params.Q5_z = C ((locParams.Q5_z.coeff 5 : LocK5) : K5) * Q5_m_K5 := by
  have h := congrArg (Polynomial.map LocK5.subtype) Q5_m_loc_spec.2.2.2
  simpa only [CoverParams.map_Q5_z, k5Params, Polynomial.map_mul, Polynomial.map_C, Q5_m_K5,
    Subring.coe_subtype] using h

lemma Q5_K5_natDegree : k5Params.Q5_z.natDegree = 5 := by
  rw [Q5_K5_eq_mul_monic, Polynomial.natDegree_C_mul (LocK5.ne_zero_of_evLoc Q5_lc_evLoc_ne),
    Q5_m_K5, Q5_m_loc_spec.1.natDegree_map, Q5_m_loc_spec.2.1]


private theorem cover_factorization_proof : CoverFactorSpec :=
  ⟨k5Params_Q5_z_natDegree_le, k5Params_Q7_z_natDegree_le, X_pow_15_dvd_nm_z_K5,
   k5Params_nm_z_elim_symm, M39_loc_dvd_nm_z, nm_z_loc_eq_M39_mul_Q34,
   Q34_loc_evLoc, Q34_loc_natDegree_le, Q34_lc_evLoc_ne,
   Q5_m_loc_spec, Q5_K5_eq_mul_monic, Q5_K5_natDegree⟩

end CoverFactorProof
end SymmetricSexticResidual.CoverAlgebra

theorem solution : SymmetricSexticResidual.CoverAlgebra.CoverFactorSpec :=
  SymmetricSexticResidual.CoverAlgebra.cover_factorization_proof
