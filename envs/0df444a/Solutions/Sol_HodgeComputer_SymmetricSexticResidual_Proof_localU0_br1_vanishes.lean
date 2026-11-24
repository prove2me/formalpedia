-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localU0_br1_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T12:25:23.343891+00:00
-- url     : https://prove2.me/submissions/01ba4e43-5d11-40c7-a66a-625afa0a5e56

import Definitions.Def_HodgeComputerSSR_BranchHelpers
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_reg_identities
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_W2_res_dual
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_br1_g_scaled

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  PolynomialEncoding.KroneckerCheck QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators LaurentSeries PowerSeries

private abbrev P18_of_isPolyDeg4 := @HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.P18_deg4

private lemma res_z_W1_0_val_ne :
    HasValGe 13 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z)) ∧
    (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z)).coeff 13 ≠ 0 :=
  HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_res_dual.2

private abbrev br1_0_g_scaled := @HodgeComputer.SymmetricSexticResidual.Proof.localU0_br1_g_scaled

lemma br1_0_eta_AC_coeff_neg_one : (br1_0 eta_AC).coeff (-1) = 0 := by
  let U := HahnSeries.single (1 : ℤ) (1 : K5)
  let V := W1_0 / U
  let ca := evalT k5Params.ca_h
  let cb := evalT k5Params.cb_h
  let c0W := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.c0W)
  let d2_2 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d2_2)
  let d2_1 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d2_1)
  let d2_0 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d2_0)
  let d1 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d1_z)
  let d0 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d0_z)
  let res := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z)
  let g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K)
      (z / W1_0) (-(ca * z + c0W) / (W1_0 * cb)) U V
  let p := interp4 g
  let P1 := remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1
  let P0 := remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2
  have hbr : br1_0 eta_AC =
      (-(P1 * d0 - P0 * d1) * U ^ 3 * W1_0 * cb ^ 4) /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W1_0 + evalT k5Params.bW) * evalT k5Params.Q5_z ^ 3 * res) :=
    branchHom_eta_AC_of_eq ψ0 ψ0_C W1_0 W1_0_eq_ψ0 U ψ0_X evalT (RingHom.ext ψ0_toRat)
      V ca cb c0W d2_2 d2_1 d2_0 d1 d0 res g p P1 P0
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [hbr]
  have hp_def : p = interp4 g := rfl
  have hP1_def : P1 = remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1 := rfl
  have hP0_def : P0 = remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2 := rfl
  clear_value P1 P0 p
  -- Show `HasValGe 13` on denominator with nonzero coeff 13, and `HasValGe 13` on numerator!
  have hS := S_K_ne_zero; have hT := T_K_ne_zero
  have hA := fiveS_sub_9Q_ne; have hC := fiveT_sub_9_ne
  set w2 : K5 := -(k5Params.Cv0 / k5Params.Bv0)
  have hw2_ne : w2 ≠ 0 := neg_ne_zero.mpr (div_ne_zero k5Params_Cv0_ne k5Params_Bv0_ne)
  have hw2_L : ValLead 2 W1_0 w2 := ⟨HasValGe_W1_0, W1_0_coeff2⟩
  have hU_L : ValLead 1 U 1 := ValLead.of_single 1 1
  have hV_L : ValLead 1 V w2 := (hw2_L.div_of_ne hU_L one_ne_zero).eq_k (by omega) |>.eq_c (div_one w2)
  have hca_L : ValLead 0 ca (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) :=
    (ValLead.of_evalT _).eq_c (by
      simp only [CoverParams.ca_h, quadU_coeff_zero, CoverParams.inv81, CoverParams.inv27, k5Params_inv3, k5Params_S, k5Params_Q]; ring)
  have hcb_L : ValLead 0 cb ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) :=
    (ValLead.of_evalT _).eq_c (by
      simp only [CoverParams.cb_h, quadU_coeff_zero, CoverParams.inv27, CoverParams.inv9, k5Params_inv3, k5Params_S, k5Params_Q]; ring)
  have hcb0_ne : (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (div_ne_zero (by exact_mod_cast (by decide : (50 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (27 : ℕ) ≠ 0))) hS) hA
  have hQ5_L : ValLead 0 (evalT k5Params.Q5_z) ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) :=
    (ValLead.of_evalT _).eq_c (by
      simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.Q5_z, CoverParams.q20, CoverParams.q11,
        CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
        CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
        eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]; ring)
  have hQ50_ne : (15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (div_ne_zero (by exact_mod_cast (by decide : (15625 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (59049 : ℕ) ≠ 0))) hS) (pow_ne_zero 4 hA)
  have h2W_L : ValLead 0 (2 * W1_0 + evalT k5Params.bW) (k5Params.Bv0 * k5Params.Av0_inv) := by
    have hbW0 : ValLead 0 (evalT k5Params.bW) (k5Params.Bv0 * k5Params.Av0_inv) :=
      (ValLead.of_evalT _).eq_c (by
        simp only [CoverParams.bW, CoverParams.Bv, coeff_C_mul, quadU_coeff_zero]; ring)
    have h2w : HasValGe 1 (2 * W1_0) := ((HasValGe.of_nat 2).mul HasValGe_W1_0).mono (by omega)
    rw [add_comm]
    exact hbW0.add_high h2w
  have h2W0_ne : k5Params.Bv0 * k5Params.Av0_inv ≠ 0 := by
    have hAi : k5Params.Av0_inv ≠ 0 := fun h => by
      have := k5Params_Av0_mul_inv; rw [h, mul_zero] at this; exact zero_ne_one this
    exact mul_ne_zero k5Params_Bv0_ne hAi
  -- Denominator has `HasValGe 13` and nonzero coeff 13!
  obtain ⟨hres_val, hres_ne⟩ : HasValGe 13 res ∧ res.coeff 13 ≠ 0 := res_z_W1_0_val_ne
  clear_value res
  have hden_L : ValLead 13
      (81 * HahnSeries.C k5Params.Av0 * (2 * W1_0 + evalT k5Params.bW) *
        evalT k5Params.Q5_z ^ 3 * res)
      (81 * k5Params.Av0 * (k5Params.Bv0 * k5Params.Av0_inv) *
        ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) ^ 3 * res.coeff 13) := by
    have h := ((((ValLead.of_nat 81).mul (ValLead.of_C k5Params.Av0)).mul h2W_L).mul
      (hQ5_L.pow 3)).mul ⟨hres_val, rfl⟩
    exact h.eq_k (by omega) |>.eq_c (by push_cast; rfl)
  have hden_ne : (81 * HahnSeries.C k5Params.Av0 * (2 * W1_0 + evalT k5Params.bW) *
      evalT k5Params.Q5_z ^ 3 * res).coeff 13 ≠ 0 := by
    rw [hden_L.c0]
    have h81 : (81 : K5) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h81 k5Params_Av0_ne) h2W0_ne)
      (pow_ne_zero 3 hQ50_ne)) hres_ne
  -- Helper `toUW` along `W1_0`: `ValLead 2 (toUW v0 v1 v2) v0`!
  have htoUW_1 (v0 v1 v2 : K5) :
      ValLead 2 (PairAlg.evalAt W1_0 (PairAlg.map evalT (k5Params.toUW v0 v1 v2))) v0 := by
    have heq : PairAlg.evalAt W1_0 (PairAlg.map evalT (k5Params.toUW v0 v1 v2)) =
        HahnSeries.C v0 * HahnSeries.single 2 1 +
        (HahnSeries.C v2 * W1_0 ^ 2 + HahnSeries.C v1 * HahnSeries.single 1 1 * W1_0) := by
      simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
        evalT_C, evalT_X, HahnSeries.single_pow]
      have h2p : (2 : ℕ) • (1 : ℤ) = 2 := by decide
      simp only [one_pow, h2p]
      linear_combination -HahnSeries.C v2 * W1_0_eq
    rw [heq]
    have ht0 : ValLead 2 (HahnSeries.C v0 * HahnSeries.single 2 1) v0 :=
      ((ValLead.of_C v0).mul (ValLead.of_single 2 1)).eq_k (by omega) |>.eq_c (mul_one v0)
    have ht1 : HasValGe 3 (HahnSeries.C v2 * W1_0 ^ 2 + HahnSeries.C v1 * HahnSeries.single 1 1 * W1_0) :=
      (((HasValGe.of_C v2).mul (HasValGe_W1_0.pow 2)).mono (by omega)).add
        ((((HasValGe.of_C v1).mul (HasValGe.single 1 1)).mul HasValGe_W1_0).mono (by omega))
    exact ht0.add_high ht1
  have hc0W_L : ValLead 2 c0W k5Params.c0_V0 := htoUW_1 _ _ _
  have hk2W_L : ValLead 2 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.k2W)) k5Params.k2_V0 :=
    htoUW_1 _ _ _
  have hk3W_L : ValLead 2 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.k3W)) k5Params.k3_V0 :=
    htoUW_1 _ _ _
  -- Valuations of `d2_2..0, d3_3..0, d1, d0` along `W1_0`!
  have hd2_2_L : ValLead 0 d2_2 ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) := by
    simpa only [d2_2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ5_L
  have hd2_1_L : ValLead 2 d2_1 (-(1250 / 729 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 * k5Params.c0_V0) := by
    simp only [d2_1, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
    have hsc : ValLead 0 (evalT (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h))
        (-(1250 / 729 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2) := (ValLead.of_evalT _).eq_c (by
      simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.q11, CoverParams.q02,
        CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
        CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
        eval_add, eval_neg, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]; ring)
    exact (hsc.mul hc0W_L).eq_k (by omega)
  have hd2_0_L : ValLead 4 d2_0
      (-(25 / 3 : K5) * S_K * k5Params.c0_V0 ^ 2 +
       ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) ^ 2 * (w2 * k5Params.k2_V0)) := by
    simp only [d2_0, CoverParams.d2_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul,
      PairAlg.map_mul, PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul,
      PairAlg.evalAt_mul _ _ W1_0 W1_0_eq, PairAlg.evalAt_W, map_pow]
    have hq02 : ValLead 0 (evalT k5Params.q02) (-(25 / 3 : K5) * S_K) := (ValLead.of_evalT _).eq_c (by
      simp only [CoverParams.q02, quadU_coeff_zero, k5Params_inv3, k5Params_S]; ring)
    exact ((hq02.mul (hc0W_L.mul hc0W_L)).eq_k (by omega) |>.eq_c (by ring)).add
      (((hcb_L.pow 2).mul (hw2_L.mul hk2W_L)).eq_k (by omega))
  have hd3_3_L : ValLead 0 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3))
      (-(781250 / 4782969 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 5) := by
    simp only [CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar]
    exact (ValLead.of_evalT _).eq_c (by
      simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.Q7_z, CoverParams.c30,
        CoverParams.c21, CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h,
        CoverParams.quadU, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, CoverParams.inv243,
        k5Params_inv3, k5Params_S, k5Params_Q, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]; ring)
  have hd3_2_L : ValLead 2 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2))
      ((62500 / 19683 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 3 * k5Params.c0_V0) := by
    simp only [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
    have hsc : ValLead 0 (evalT (-k5Params.c21 * k5Params.cb_h ^ 2 +
        2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h ^ 2))
        ((62500 / 19683 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 3) := (ValLead.of_evalT _).eq_c (by
      simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.c21, CoverParams.c12, CoverParams.c03,
        CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU, CoverParams.inv9, CoverParams.inv27,
        CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
        eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]; ring)
    exact (hsc.mul hc0W_L).eq_k (by omega)
  have hd3_1_L : ValLead 4 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_1))
      (-(1250 / 81 : K5) * S_K * (5 * S_K - 9 * Q_K) * k5Params.c0_V0 ^ 2) := by
    simp only [CoverParams.d3_1, CoverParams.pmul, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W1_0 W1_0_eq]
    have hsc : ValLead 0 (evalT (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h))
        (-(1250 / 81 : K5) * S_K * (5 * S_K - 9 * Q_K)) := (ValLead.of_evalT _).eq_c (by
      simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.c12, CoverParams.c03,
        CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU, CoverParams.inv9, CoverParams.inv27,
        CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
        eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]; ring)
    exact (hsc.mul (hc0W_L.mul hc0W_L)).eq_k (by omega) |>.eq_c (by ring)
  have hd3_0_L : ValLead 6 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_0))
      (((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) ^ 3 * (w2 ^ 2 * k5Params.k3_V0)) := by
    simp only [CoverParams.d3_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W1_0 W1_0_eq,
      PairAlg.evalAt_W, map_neg, map_pow]
    have hc03 : HasValGe 1 (evalT k5Params.c03) :=
      (HasValGe.evalT _).inc (by
        change (evalT k5Params.c03).coeff (0 : ℕ) = 0
        rw [evalT_coeff]; simp [CoverParams.c03, CoverParams.quadU])
    have ht7 : HasValGe 7 (-evalT k5Params.c03 * (c0W * (c0W * c0W))) :=
      (hc03.neg.mul (hc0W_L.val.mul (hc0W_L.val.mul hc0W_L.val))).mono (by omega)
    rw [add_comm]
    exact (((hcb_L.pow 3).mul ((hw2_L.mul hw2_L).mul hk3W_L)).eq_k (by omega) |>.eq_c (by ring)).add_high ht7
  have hd1_val : HasValGe 4 d1 := by
    simp only [d1, CoverParams.d1_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W1_0 W1_0_eq]
    exact ((hd2_2_L.val.mul ((hd2_2_L.val.mul hd3_1_L.val).sub (hd2_0_L.val.mul hd3_3_L.val))).mono (by omega)).sub
      ((hd2_1_L.val.mul ((hd2_2_L.val.mul hd3_2_L.val).sub (hd2_1_L.val.mul hd3_3_L.val))).mono (by omega))
  have hd0_val : HasValGe 6 d0 := by
    simp only [d0, CoverParams.d0_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W1_0 W1_0_eq]
    exact ((hd2_2_L.val.mul (hd2_2_L.val.mul hd3_0_L.val)).mono (by omega)).sub
      ((hd2_0_L.val.mul ((hd2_2_L.val.mul hd3_2_L.val).sub (hd2_1_L.val.mul hd3_3_L.val))).mono (by omega))
  have hd1_eq : remDeg3_d1 d2_2 d2_1 d2_0
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_1)) = d1 := by
    simp only [d1, CoverParams.d1_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W1_0 W1_0_eq, remDeg3_d1]; rfl
  have hd0_eq : remDeg3_d0 d2_2 d2_1 d2_0
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_0)) = d0 := by
    simp only [d0, CoverParams.d0_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W1_0 W1_0_eq, remDeg3_d0]; rfl
  clear_value d2_2 d2_1 d2_0 d1 d0
  -- Common leading root `z1 = w2 * S_K / T_K` (`(5S - 9Q)^2 * z1 = -(5T - 9)^2`)!
  set z1 : K5 := w2 * S_K / T_K
  have hw2_eq : S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2 = -T_K * (5 * T_K - 9) ^ 2 := by
    dsimp only [w2]
    rw [mul_neg, mul_div_assoc', neg_eq_iff_eq_neg, div_eq_iff k5Params_Bv0_ne]
    simp only [CoverParams.Cv0, CoverParams.Bv0, CoverParams.inv243, k5Params_inv3,
      k5Params_S, k5Params_Q, k5Params_T]; ring
  have hz1_mul : (5 * S_K - 9 * Q_K) ^ 2 * z1 = -(5 * T_K - 9) ^ 2 := by
    apply mul_left_cancel₀ hT
    have h1 : T_K * ((5 * S_K - 9 * Q_K) ^ 2 * z1) = S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2 := by
      dsimp only [z1]; field_simp [hT]
    rw [h1, hw2_eq]; ring
  -- Show `HasValGe 3 (g (single 2 c))` for all `c : K5`, AND `(g (single 2 z1)).coeff 3 = 0`!
  have hg_scaled : ∀ c : K5, HasValGe 3 (g (HahnSeries.single 2 c)) ∧
      (c = z1 → (g (HahnSeries.single 2 c)).coeff 3 = 0) :=
    br1_0_g_scaled hw2_ne hcb0_ne hw2_L hU_L hV_L hca_L hcb_L hc0W_L rfl hw2_eq hz1_mul
  -- Apply `HasValGe.interp4_scaled` (`s = 2, k = 3`) -> `p4..p0` have `val ≥ -5, -3, -1, 1, 3`!
  have hg_deg4 : IsPolyDeg 4 g := by
    have h := P18_of_isPolyDeg4 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V (1 / W1_0) 0 (-ca / (W1_0 * cb)) (-c0W / (W1_0 * cb))
    refine h.congr (fun z => ?_)
    dsimp only [g]
    have hW_ne : W1_0 ≠ 0 := fun h0 => hw2_ne (by rw [← hw2_L.c0, h0]; rfl)
    have hcb_ne : cb ≠ 0 := fun h0 => hcb0_ne (by rw [← hcb_L.c0, h0]; rfl)
    congr 1
    · ring
    · field_simp [hW_ne, hcb_ne]; ring
  obtain ⟨hp4, hp3, hp2, hp1, hp0⟩ : HasValGe (-5) p.1 ∧ HasValGe (-3) p.2.1 ∧
      HasValGe (-1) p.2.2.1 ∧ HasValGe 1 p.2.2.2.1 ∧ HasValGe 3 p.2.2.2.2 :=
    hp_def.symm ▸ HasValGe.interp4_scaled (s := 2) (k := 3) hg_deg4 (fun c => (hg_scaled c).1)
  -- Hence `HasValGe 1 P1` and `HasValGe 3 P0`!
  have hP1_val : HasValGe 1 P1 := by
    rw [hP1_def]; simp only [remDeg4_P1]
    have hr3 : HasValGe (-3) (d2_2 * p.2.1 - d2_1 * p.1) :=
      ((hd2_2_L.val.mul hp3).mono (by omega)).sub ((hd2_1_L.val.mul hp4).mono (by omega))
    have hr2 : HasValGe (-1) (d2_2 * p.2.2.1 - d2_0 * p.1) :=
      ((hd2_2_L.val.mul hp2).mono (by omega)).sub ((hd2_0_L.val.mul hp4).mono (by omega))
    have hs2 : HasValGe (-1) (d2_2 * (d2_2 * p.2.2.1 - d2_0 * p.1) - d2_1 * (d2_2 * p.2.1 - d2_1 * p.1)) :=
      ((hd2_2_L.val.mul hr2).mono (by omega)).sub ((hd2_1_L.val.mul hr3).mono (by omega))
    have hs1 : HasValGe 1 (d2_2 ^ 2 * p.2.2.2.1 - d2_0 * (d2_2 * p.2.1 - d2_1 * p.1)) :=
      (((hd2_2_L.val.pow 2).mul hp1).mono (by omega)).sub ((hd2_0_L.val.mul hr3).mono (by omega))
    exact ((hd2_2_L.val.mul hs1).mono (by omega)).sub ((hd2_1_L.val.mul hs2).mono (by omega))
  have hP0_val : HasValGe 3 P0 := by
    rw [hP0_def]; simp only [remDeg4_P0]
    have hr3 : HasValGe (-3) (d2_2 * p.2.1 - d2_1 * p.1) :=
      ((hd2_2_L.val.mul hp3).mono (by omega)).sub ((hd2_1_L.val.mul hp4).mono (by omega))
    have hr2 : HasValGe (-1) (d2_2 * p.2.2.1 - d2_0 * p.1) :=
      ((hd2_2_L.val.mul hp2).mono (by omega)).sub ((hd2_0_L.val.mul hp4).mono (by omega))
    have hs2 : HasValGe (-1) (d2_2 * (d2_2 * p.2.2.1 - d2_0 * p.1) - d2_1 * (d2_2 * p.2.1 - d2_1 * p.1)) :=
      ((hd2_2_L.val.mul hr2).mono (by omega)).sub ((hd2_1_L.val.mul hr3).mono (by omega))
    exact (((hd2_2_L.val.pow 3).mul hp0).mono (by omega)).sub ((hd2_0_L.val.mul hs2).mono (by omega))
  -- Evaluate `E2(single 2 z1)` (`HasValGe 5`), `E3(single 2 z1)` (`HasValGe 7`), and `g(single 2 z1)` (`HasValGe 4`)!
  set β : LaurentSeries K5 := HahnSeries.single 2 z1
  have hβ_L : ValLead 2 β z1 := ValLead.of_single 2 z1
  have hE2_β : HasValGe 5 (d2_2 * β ^ 2 + d2_1 * β + d2_0) := by
    have hL := (((hd2_2_L.mul (hβ_L.pow 2)).eq_k (by omega)).add ((hd2_1_L.mul hβ_L).eq_k (by omega))).add hd2_0_L
    refine (hL.eq_c ?_).hasValGe_succ
    apply mul_left_cancel₀ (mul_ne_zero hS (pow_ne_zero 4 hA))
    rw [mul_zero]
    have hstep :
        S_K * (5 * S_K - 9 * Q_K) ^ 4 *
          ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4 * z1 ^ 2 +
           -(1250 / 729) * S_K * (5 * S_K - 9 * Q_K) ^ 2 * k5Params.c0_V0 * z1 +
           (-(25 / 3) * S_K * k5Params.c0_V0 ^ 2 + ((50 / 27) * S_K * (5 * S_K - 9 * Q_K)) ^ 2 * (w2 * k5Params.k2_V0))) =
        (15625 / 59049 : K5) * S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 4 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) ^ 2 -
        (1250 / 729) * S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 4 * k5Params.c0_V0 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) -
        (25 / 3) * S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 4 * k5Params.c0_V0 ^ 2 +
        (2500 / 729) * S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 4 * k5Params.k2_V0 * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) := by ring
    rw [hstep, hz1_mul, hw2_eq]
    simp only [CoverParams.c0_V0, CoverParams.k2_V0, CoverParams.inv81, k5Params_inv3, k5Params_T]
    generalize 5 * S_K - 9 * Q_K = A'
    ring
  have hE3_β : HasValGe 7 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3) * β ^ 3 +
      PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2) * β ^ 2 +
      PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_1) * β +
      PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_0)) := by
    have hL := ((((hd3_3_L.mul (hβ_L.pow 3)).eq_k (by omega)).add
      ((hd3_2_L.mul (hβ_L.pow 2)).eq_k (by omega))).add ((hd3_1_L.mul hβ_L).eq_k (by omega))).add hd3_0_L
    refine (hL.eq_c ?_).hasValGe_succ
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hS) (pow_ne_zero 6 hA))
    rw [mul_zero]
    have hstep :
        S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 6 *
          (-(781250 / 4782969 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 5 * z1 ^ 3 +
           (62500 / 19683) * S_K * (5 * S_K - 9 * Q_K) ^ 3 * k5Params.c0_V0 * z1 ^ 2 +
           -(1250 / 81) * S_K * (5 * S_K - 9 * Q_K) * k5Params.c0_V0 ^ 2 * z1 +
           ((50 / 27) * S_K * (5 * S_K - 9 * Q_K)) ^ 3 * (w2 ^ 2 * k5Params.k3_V0)) =
        -(781250 / 4782969 : K5) * S_K ^ 3 * (5 * S_K - 9 * Q_K) ^ 5 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) ^ 3 +
        (62500 / 19683) * S_K ^ 3 * (5 * S_K - 9 * Q_K) ^ 5 * k5Params.c0_V0 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) ^ 2 -
        (1250 / 81) * S_K ^ 3 * (5 * S_K - 9 * Q_K) ^ 5 * k5Params.c0_V0 ^ 2 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) +
        (125000 / 19683) * S_K ^ 3 * (5 * S_K - 9 * Q_K) ^ 5 * k5Params.k3_V0 * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) ^ 2 := by ring
    rw [hstep, hz1_mul, hw2_eq]
    simp only [CoverParams.c0_V0, CoverParams.k3_V0, CoverParams.inv81, CoverParams.inv243, k5Params_inv3, k5Params_T]
    generalize 5 * S_K - 9 * Q_K = A'
    ring
  -- By `remDeg4_eq` and `remDeg3_eq` at `β`: `P1.coeff 1 * z1 + P0.coeff 3 = 0` AND `d1.coeff 4 * z1 + d0.coeff 6 = 0`!
  have hP_lin : P1.coeff 1 * z1 + P0.coeff 3 = 0 := by
    have hrem := remDeg4_eq d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 β
    rw [← hP1_def, ← hP0_def] at hrem
    conv_lhs at hrem => rw [hp_def]; dsimp only [interp4]; rw [← hg_deg4.eq_deg4 β]
    have hβ_def : β = HahnSeries.single 2 z1 := rfl
    have hgβ : HasValGe 4 (g β) := hβ_def.symm ▸ ((hg_scaled z1).1.inc ((hg_scaled z1).2 rfl))
    have hlhs : HasValGe 4 (d2_2 ^ 3 * g β) := ((hd2_2_L.val.pow 3).mul hgβ).mono (by omega)
    have hQ : HasValGe (-1) (d2_2 ^ 2 * p.1 * β ^ 2 + d2_2 * (d2_2 * p.2.1 - d2_1 * p.1) * β +
        (d2_2 * (d2_2 * p.2.2.1 - d2_0 * p.1) - d2_1 * (d2_2 * p.2.1 - d2_1 * p.1))) := by
      have ha : HasValGe (-1) _ := (((hd2_2_L.val.pow 2).mul hp4).mul (hβ_L.val.pow 2)).mono (by omega)
      have hb : HasValGe (-1) _ := ((hd2_2_L.val.mul (((hd2_2_L.val.mul hp3).mono (k2 := -3) (by omega)).sub
        ((hd2_1_L.val.mul hp4).mono (k2 := -3) (by omega)))).mul hβ_L.val).mono (by omega)
      have hc : HasValGe (-1) _ := ((hd2_2_L.val.mul (((hd2_2_L.val.mul hp2).mono (k2 := -1) (by omega)).sub
        ((hd2_0_L.val.mul hp4).mono (k2 := -1) (by omega)))).mono (k2 := -1) (by omega)).sub
        ((hd2_1_L.val.mul (((hd2_2_L.val.mul hp3).mono (k2 := -3) (by omega)).sub
        ((hd2_1_L.val.mul hp4).mono (k2 := -3) (by omega)))).mono (k2 := -1) (by omega))
      exact (ha.add hb).add hc
    have hmul4 : HasValGe 4 ((d2_2 ^ 2 * p.1 * β ^ 2 + d2_2 * (d2_2 * p.2.1 - d2_1 * p.1) * β +
        (d2_2 * (d2_2 * p.2.2.1 - d2_0 * p.1) - d2_1 * (d2_2 * p.2.1 - d2_1 * p.1))) *
        (d2_2 * β ^ 2 + d2_1 * β + d2_0)) := (hQ.mul hE2_β).mono (by omega)
    have hc3 := congrArg (fun f : LaurentSeries K5 => f.coeff 3) hrem
    rw [hlhs 3 (by omega), HahnSeries.coeff_add, hmul4 3 (by omega), zero_add, HahnSeries.coeff_add,
      show (3 : ℤ) = 1 + 2 by omega, hP1_val.coeff_mul_min hβ_L.val, hβ_L.c0] at hc3
    exact hc3.symm
  have hd_lin : d1.coeff 4 * z1 + d0.coeff 6 = 0 := by
    have hrem := remDeg3_eq d2_2 d2_1 d2_0
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_1))
      (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_0)) β
    rw [hd1_eq, hd0_eq] at hrem
    have hlhs : HasValGe 7 (d2_2 ^ 2 * _) := ((hd2_2_L.val.pow 2).mul hE3_β).mono (by omega)
    have hQ : HasValGe 2 (d2_2 * PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3) * β +
        (d2_2 * PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2) -
         d2_1 * PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3))) :=
      (((hd2_2_L.val.mul hd3_3_L.val).mul hβ_L.val).mono (by omega)).add
        (((hd2_2_L.val.mul hd3_2_L.val).mono (by omega)).sub ((hd2_1_L.val.mul hd3_3_L.val).mono (by omega)))
    have hmul7 : HasValGe 7 ((d2_2 * PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3) * β +
        (d2_2 * PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2) -
         d2_1 * PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3))) *
        (d2_2 * β ^ 2 + d2_1 * β + d2_0)) := (hQ.mul hE2_β).mono (by omega)
    have hc6 := congrArg (fun f : LaurentSeries K5 => f.coeff 6) hrem
    rw [hlhs 6 (by omega), HahnSeries.coeff_add, hmul7 6 (by omega), zero_add, HahnSeries.coeff_add,
      show (6 : ℤ) = 4 + 2 by omega, hd1_val.coeff_mul_min hβ_L.val, hβ_L.c0] at hc6
    exact hc6.symm
  -- Therefore `(P1 * d0 - P0 * d1)` jumps from 7 to 8, numerator jumps to 13, and quotient has `HasValGe 0`!
  have hcomb_8 : HasValGe 8 (P1 * d0 - P0 * d1) := by
    have h7 : HasValGe 7 (P1 * d0 - P0 * d1) :=
      ((hP1_val.mul hd0_val).mono (by omega)).sub ((hP0_val.mul hd1_val).mono (by omega))
    apply h7.inc
    rw [HahnSeries.coeff_sub, show (7 : ℤ) = 1 + 6 by omega, hP1_val.coeff_mul_min hd0_val,
      show (1 + 6 : ℤ) = 3 + 4 by omega, hP0_val.coeff_mul_min hd1_val]
    linear_combination P1.coeff 1 * hd_lin - d1.coeff 4 * hP_lin
  have hnum_13 : HasValGe 13 (-(P1 * d0 - P0 * d1) * U ^ 3 * W1_0 * cb ^ 4) :=
    (((hcomb_8.neg.mul (hU_L.val.pow 3)).mul HasValGe_W1_0).mul (hcb_L.val.pow 4)).mono (by omega)
  have hquot_0 : HasValGe 0
      ((-(P1 * d0 - P0 * d1) * U ^ 3 * W1_0 * cb ^ 4) /
        (81 * HahnSeries.C k5Params.Av0 * (2 * W1_0 + evalT k5Params.bW) *
          evalT k5Params.Q5_z ^ 3 * res)) :=
    (hnum_13.div_of_lead_ne hden_L.val hden_ne).1.mono (by omega)
  exact hquot_0 (-1) (by omega)


end SymmetricSexticResidual.LocalResidueU0

theorem solution :
    (SymmetricSexticResidual.LocalResidueU0.br1_0 SymmetricSexticResidual.CoverResidue.eta_AC).coeff (-1) = 0 :=
  SymmetricSexticResidual.LocalResidueU0.br1_0_eta_AC_coeff_neg_one
