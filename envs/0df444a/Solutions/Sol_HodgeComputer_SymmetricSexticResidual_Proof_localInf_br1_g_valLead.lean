-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_g_valLead
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T20:36:02.098981+00:00
-- url     : https://prove2.me/submissions/97a23711-9d45-40d6-a118-755c1bdc183a

import Definitions.Def_HodgeComputerSSR_LocalInfCore
import Definitions.Def_HodgeComputerSSR_LocalInfBiv
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_branch_jet_helpers
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_sheet_splits
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_weights_and_jets
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_biv_bridges

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueInf
open Polynomial
open scoped LaurentSeries PowerSeries
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.VerticalIdentity SymmetricSexticResidual.LocalResidueU0
  SymmetricSexticResidual.LocalResidueInfAlg QuadraticCovers
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

private abbrev EB_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.EB_bilinear
private abbrev QY_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.QY_bilinear
private abbrev QX_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.QX_bilinear
private abbrev A0V_ValLead_of := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.A0V_ValLead
private abbrev numM_split_UV := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.1
private abbrev AY_t3_U3_eq_zero := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.1
private abbrev A_0V_split_UV := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.2.1
private abbrev QY_10_u1_zero := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.2.2.2.2.2.2.2.2.2
private abbrev numM_Uk_valLead := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_weights_and_jets.numM_Uk_valLead
private abbrev ringEval_H0_7_inf := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.1
private abbrev ringEval_dH0_7_inf := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.1
private abbrev evalBivK5_QY10 := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.1
private abbrev evalBivK5_QX10 := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.1
private abbrev evalBivK5_EB10 := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.2.2.2.2.2.1

private lemma br1_inf_EB_valLead {U V : LaurentSeries K5} {w0 : K5}
    (hU_L : ValLead (-1) U 1) (hV_L : ValLead 1 V w0) :
    ValLead (-1) (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) (evalBivK5 EB10_biv / 243) := by
  have hlinU {a00 a01 a10 a11 : K5} :
      ValLead (-1) (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V) a10 := by
    have hre : HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V =
        HahnSeries.C a10 * U + (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a11 * U * V) := by ring
    rw [hre]
    exact (((ValLead.of_C a10).mul hU_L).eq_k (by omega) |>.eq_c (mul_one _)).add_high
      ((((HasValGe.of_C a00).add (((HasValGe.of_C a01).mul hV_L.val).mono (by omega))).add
        ((((HasValGe.of_C a11).mul hU_L.val).mul hV_L.val).mono (by omega))))
  have hbi := EB_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
    (HahnSeries.C x_K) (HahnSeries.C y_K) U V
  have hmap (u0 v0 : K5) : (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) : LaurentSeries K5) =
      HahnSeries.C (EB_of S_K Q_K T_K x_K y_K u0 v0) := by
    simp only [EB_of, W2_of, DX2_of, DY2_of, dF5_fn, br_fn, LX_of, LY_of,
      dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_zero, map_one]
  have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
  simp only [map_zero, map_one] at h00 h01 h10 h11
  rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
  exact hlinU.eq_c (by rw [evalBivK5_EB10]; ring)

private lemma br1_inf_QY_valLead {U V : LaurentSeries K5} {w0 : K5}
    (hU_L : ValLead (-1) U 1) (hV_L : ValLead 1 V w0) (i : Fin 3) :
    ValLead (-1)
      (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      (evalBivK5 (QY10_biv i) / 1701) := by
  have hlinU {a00 a01 a10 a11 : K5} :
      ValLead (-1) (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V) a10 := by
    have hre : HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V =
        HahnSeries.C a10 * U + (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a11 * U * V) := by ring
    rw [hre]
    exact (((ValLead.of_C a10).mul hU_L).eq_k (by omega) |>.eq_c (mul_one _)).add_high
      ((((HasValGe.of_C a00).add (((HasValGe.of_C a01).mul hV_L.val).mono (by omega))).add
        ((((HasValGe.of_C a11).mul hU_L.val).mul hV_L.val).mono (by omega))))
  have hbi := QY_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
    (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
  have hmap (u0 v0 : K5) : (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) i : LaurentSeries K5) =
      HahnSeries.C (QY_num S_K Q_K T_K x_K y_K u0 v0 i) := by
    fin_cases i <;> simp only [QY_num, Omega_F, dDX2_F, F_contract, dF5_fn, dH0_fn, dDX2_fn, DX2_of, DY2_of,
      om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]
  have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
  simp only [map_zero, map_one] at h00 h01 h10 h11
  rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
  exact hlinU.eq_c (by rw [evalBivK5_QY10]; ring)

private lemma br1_inf_QX_valLead {U V : LaurentSeries K5} {w0 : K5}
    (hU_L : ValLead (-1) U 1) (hV_L : ValLead 1 V w0) (i : Fin 3) :
    ValLead (-1)
      (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      (evalBivK5 (QX10_biv i) / 1701) := by
  have hlinU {a00 a01 a10 a11 : K5} :
      ValLead (-1) (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V) a10 := by
    have hre : HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V =
        HahnSeries.C a10 * U + (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a11 * U * V) := by ring
    rw [hre]
    exact (((ValLead.of_C a10).mul hU_L).eq_k (by omega) |>.eq_c (mul_one _)).add_high
      ((((HasValGe.of_C a00).add (((HasValGe.of_C a01).mul hV_L.val).mono (by omega))).add
        ((((HasValGe.of_C a11).mul hU_L.val).mul hV_L.val).mono (by omega))))
  have hbi := QX_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
    (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
  have hmap (u0 v0 : K5) : (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C u0) (HahnSeries.C v0) i : LaurentSeries K5) =
      HahnSeries.C (QX_num S_K Q_K T_K x_K y_K u0 v0 i) := by
    fin_cases i <;> simp only [QX_num, Omega_F, dDY2_F, F_contract, dF5_fn, dH0_fn, dDY2_fn, DX2_of, DY2_of,
      om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]
  have h00 := hmap 0 0; have h01 := hmap 0 1; have h10 := hmap 1 0; have h11 := hmap 1 1
  simp only [map_zero, map_one] at h00 h01 h10 h11
  rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
  exact hlinU.eq_c (by rw [evalBivK5_QX10]; ring)

-- Standalone Branch 1 (`W1_inf`) `ValLead (-3)` for `g (C z)` (gives `p4[-3], p3[-3], p2[-3]` and `HasValGe (-3)` for `p0..p4`)!
private lemma br1_inf_g_valLead {W1s U V ca cb c0W : LaurentSeries K5} {w0 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * T_K * (5 * T_K - 9) ^ 2 / (S_K - 3 * Q_K) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hW_L : ValLead 0 W1s w0) (hU_L : ValLead (-1) U 1) (hV_L : ValLead 1 V w0)
    (hca_L : ValLead (-2) ca (-(4 / 81 : K5) * (S_K - 3 * Q_K) ^ 2))
    (hcb_L : ValLead (-2) cb ((4 / 27 : K5) * (S_K - 3 * Q_K) ^ 2))
    (hc0W_L : ValLead (-2) c0W (-(25 / 81 : K5) * (5 * T_K - 9) * (5 * T_K - 3))) :
    ∀ z : K5, ValLead (-3)
      (P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) (HahnSeries.C z / W1s) (-(ca * HahnSeries.C z + c0W) / (W1s * cb)) U V)
      ((w0 * A0V_Uk 3 (z / w0) (z / w0 / 3 + -(S_K - 3 * Q_K) * (5 * T_K - 3) / (3 * T_K * (5 * T_K - 9)))
        (S_K - z / w0 * T_K) (Q_K - (z / w0 / 3 + -(S_K - 3 * Q_K) * (5 * T_K - 3) / (3 * T_K * (5 * T_K - 9))) * T_K)) *
       ((evalBivK5 q1_m1_u1_biv / 107163) * (z / w0) + (evalBivK5 q1_m1_u0_biv / (3 * T_K * (5 * T_K - 9) * 107163)))) := by
  intro z
  set S3Q := S_K - 3 * Q_K; set T59 := 5 * T_K - 9
  set c0_num := -S3Q * (5 * T_K - 3)
  have hS3Q : S3Q ≠ 0 := S_K_sub_3Q_ne; have hT : T_K ≠ 0 := T_K_ne_zero; have hT59 : T59 ≠ 0 := fiveT_sub_9_ne
  have hS3Q_def : S_K - 3 * Q_K = S3Q := rfl
  have hT59_def : 5 * T_K - 9 = T59 := rfl
  have hw0_eq' : w0 = -(25 / 4 : K5) * T_K * T59 ^ 2 / S3Q ^ 3 := hw0_eq
  have h9_ne : (9 : K5) ≠ 0 := ofNat_ne_zero 9
  have hcb_ne : (4 / 27 : K5) * S3Q ^ 2 ≠ 0 :=
    mul_ne_zero (div_ne_zero (ofNat_ne_zero 4) (ofNat_ne_zero 27)) (pow_ne_zero 2 hS3Q)
  set zL : LaurentSeries K5 := HahnSeries.C z
  rw [P18_of_HahnC_eq]
  set a_s := zL / W1s
  set b_s := -(ca * zL + c0W) / (W1s * cb)
  set u : K5 := z / w0
  set β : K5 := c0_num / (3 * T_K * T59)
  set b0 : K5 := u / 3 + β
  have hz_L : ValLead 0 zL z := ValLead.of_C z
  have ha_L : ValLead 0 a_s u := (hz_L.div_of_ne hW_L hw0_ne).eq_k (by omega)
  have hb_L : ValLead 0 b_s b0 := by
    have hnum : ValLead (-2) _ _ := (((hca_L.mul hz_L).eq_k (by omega)).add hc0W_L).neg
    have hden : ValLead (-2) _ _ := (hW_L.mul hcb_L).eq_k (by omega)
    refine ((hnum.div_of_ne hden (mul_ne_zero hw0_ne hcb_ne)).eq_k (by omega)).eq_c ?_
    dsimp only [b0, u, β, c0_num]; rw [hw0_eq']
    field_simp [hS3Q, hT, hT59]; ring
  set ξS_s := HahnSeries.C S_K - a_s * HahnSeries.C T_K
  set ξQ_s := HahnSeries.C Q_K - b_s * HahnSeries.C T_K
  set ξS0 : K5 := S_K - u * T_K
  set ξQ0 : K5 := Q_K - b0 * T_K
  have hξS_L : ValLead 0 ξS_s ξS0 := (ValLead.of_C S_K).sub ((ha_L.mul (ValLead.of_C T_K)).eq_k (by omega))
  have hξQ_L : ValLead 0 ξQ_s ξQ0 := (ValLead.of_C Q_K).sub ((hb_L.mul (ValLead.of_C T_K)).eq_k (by omega))
  have hUk_L (k : Fin 4) (mi : Fin 10) :
      ValLead 0 (numM_Uk k mi a_s b_s ξS_s ξQ_s) (numM_Uk k mi u b0 ξS0 ξQ0) :=
    numM_Uk_valLead k mi ha_L hb_L hξS_L hξQ_L
  have hnumM_L (mi : Fin 10) : ValLead (-1) (numM mi a_s b_s ξS_s ξQ_s U V) (w0 ^ 2 * numM_Uk 3 mi u b0 ξS0 ξQ0) := by
    rw [numM_split_UV]
    have hmain : ValLead (-1) (V ^ 2 * (U ^ 3 * numM_Uk 3 mi a_s b_s ξS_s ξQ_s))
        (w0 ^ 2 * numM_Uk 3 mi u b0 ξS0 ξQ0) :=
      (((hV_L.pow 2).mul ((hU_L.pow 3).mul (hUk_L 3 mi))).eq_k (by omega)).eq_c (by ring)
    have hhi : HasValGe 0 (V ^ 2 * (U ^ 2 * numM_Uk 2 mi a_s b_s ξS_s ξQ_s +
        U * numM_Uk 1 mi a_s b_s ξS_s ξQ_s + numM_Uk 0 mi a_s b_s ξS_s ξQ_s)) := by
      have h2 := ((hU_L.val.pow 2).mul (hUk_L 2 mi).val).mono (k2 := -2) (by omega)
      have h1 := (hU_L.val.mul (hUk_L 1 mi).val).mono (k2 := -2) (by omega)
      have h0 := (hUk_L 0 mi).val.mono (k2 := -2) (by omega)
      exact ((hV_L.val.pow 2).mul ((h2.add h1).add h0)).mono (by omega)
    have hre : V ^ 2 * (U ^ 3 * numM_Uk 3 mi a_s b_s ξS_s ξQ_s + U ^ 2 * numM_Uk 2 mi a_s b_s ξS_s ξQ_s +
        U * numM_Uk 1 mi a_s b_s ξS_s ξQ_s + numM_Uk 0 mi a_s b_s ξS_s ξQ_s) =
        V ^ 2 * (U ^ 3 * numM_Uk 3 mi a_s b_s ξS_s ξQ_s) +
        V ^ 2 * (U ^ 2 * numM_Uk 2 mi a_s b_s ξS_s ξQ_s + U * numM_Uk 1 mi a_s b_s ξS_s ξQ_s +
          numM_Uk 0 mi a_s b_s ξS_s ξQ_s) := by ring
    rw [hre]; exact hmain.add_high hhi
  have hm1 (i : Fin 10) : HasValGe (-1) (numM i a_s b_s ξS_s ξQ_s U V) := (hnumM_L i).val
  have hsc1 (r : K5) {f : LaurentSeries K5} (hf : HasValGe (-1) f) : HasValGe (-1) (HahnSeries.C r * f) :=
    ((HasValGe.of_C r).mul hf).mono (by omega)
  have hnat1 (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} (hf : HasValGe (-1) f) :
      HasValGe (-1) ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) :=
    ((HasValGe.of_ofNat n).mul hf).mono (by omega)
  have hp1 (i j : Fin 10) : HasValGe (-1) (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V) :=
    (hnat1 5 (hm1 i)).sub (hnat1 9 (hm1 j))
  have hA0U_0 : HasValGe 0 (A_0U a_s b_s ξS_s ξQ_s U V / U) := by
    have hA0U_1 : HasValGe (-1) (A_0U a_s b_s ξS_s ξQ_s U V) := by
      unfold A_0U; simpa only [map_div₀, map_neg, map_ofNat] using
        (((hsc1 (-(19708 / 1257375 : K5)) (hp1 0 1)).add (hsc1 (1472 / 1257375 : K5) (hp1 1 2))).sub
          (hsc1 (16 / 729 : K5) (hp1 3 5))).add (hsc1 (188 / 2025 : K5) (hp1 4 6))
    exact (hA0U_1.div_of_lead_ne hU_L.val (hU_L.c0.symm ▸ one_ne_zero)).1.mono (by omega)
  have hA0V_L : ValLead (-2) (A_0V a_s b_s ξS_s ξQ_s U V / V) (w0 * A0V_Uk 3 u b0 ξS0 ξQ0) := by
    have hV_m1 : ValLead (-1) (A_0V a_s b_s ξS_s ξQ_s U V) (w0 ^ 2 * A0V_Uk 3 u b0 ξS0 ξQ0) := by
      refine (A0V_ValLead_of hnumM_L).eq_c ?_
      simp only [A0V_Uk]; ring
    exact (hV_m1.div_of_ne hV_L hw0_ne).eq_k (by omega) |>.eq_c (by field_simp [hw0_ne])
  have hM0_L : ValLead (-2) (A_0U a_s b_s ξS_s ξQ_s U V / U + A_0V a_s b_s ξS_s ξQ_s U V / V)
      (w0 * A0V_Uk 3 u b0 ξS0 ξQ0) := by
    rw [add_comm]; exact hA0V_L.add_high (hA0U_0.mono (by omega))
  have hAX_2 : HasValGe (-2) (A_X a_s b_s ξS_s ξQ_s U V) := by
    unfold A_X
    refine (hU_L.val.mul (?_ : HasValGe (-1) _)).mono (by omega)
    simpa only [map_div₀, map_neg, map_ofNat] using
      ((hsc1 (-(8 / 405 : K5)) (hp1 3 4)).sub (hsc1 (476 / 7185 : K5) (hp1 7 8))).add
        (hsc1 (6916 / 35925 : K5) (hp1 8 9))
  have hAY_1 : HasValGe (-1) (A_Y a_s b_s ξS_s ξQ_s U V) := by
    unfold A_Y
    refine (HasValGe.add (HasValGe.add ?_ ?_) ?_)
    · simpa only [map_div₀, map_neg, map_ofNat] using
        hsc1 (-(100 / 243 : K5)) ((((hnat1 25 (hm1 3)).sub (hnat1 45 (hm1 4))).sub (hnat1 45 (hm1 5))).add (hnat1 81 (hm1 6)))
    · refine (hV_L.val.mul (?_ : HasValGe (-1) _)).mono (by omega)
      simpa only [map_div₀, map_neg, map_ofNat] using
        (((hsc1 (-(907876 / 33949125 : K5)) (hp1 0 1)).add (hsc1 (2258324 / 33949125 : K5) (hp1 1 2))).add
          (hsc1 (8 / 243 : K5) (hp1 3 5))).sub (hsc1 (64 / 675 : K5) (hp1 4 6))
    · refine ((hU_L.val.mul hV_L.val).mul (?_ : HasValGe (-1) _)).mono (by omega)
      simpa only [map_div₀, map_neg, map_ofNat] using
        (hsc1 (-(123236 / 24249375 : K5)) ((((hm1 0).add (hsc1 (2790 / 77 : K5) (hm1 6))).add (hnat1 28 (hm1 8))).sub
          (hsc1 (5904 / 77 : K5) (hm1 9)))).add
        (hsc1 (492944 / 33949125 : K5) ((((hm1 1).add (hsc1 (927 / 77 : K5) (hm1 6))).add (hsc1 (49 / 5 : K5) (hm1 8))).sub
          (hsc1 (21159 / 770 : K5) (hm1 9))))
  have hu_L : ValLead (-1) (u_of U) (1 / 9 : K5) := by
    unfold u_of
    simpa only [sub_eq_add_neg, map_neg, map_one] using
      ((hU_L.add_high (HasValGe.of_C (-1 : K5))).div_of_ne (ValLead.of_ofNat 9) h9_ne).eq_k (by omega)
  have hv_L : ValLead 0 (v_of V) (-(1 / 9 : K5)) := by
    unfold v_of
    have hV0 : ValLead 0 V 0 := ValLead.of_hasValGe_succ (k := 0) (hV_L.val.mono (by omega))
    exact ((hV0.sub (ValLead.of_C 1)).div_of_ne (ValLead.of_ofNat 9) h9_ne).eq_k (by omega) |>.eq_c (by ring)
  have hneg19_ne : (-(1 / 9 : K5)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero one_ne_zero h9_ne)
  have hEB_L := br1_inf_EB_valLead hU_L hV_L
  have hQY_L := br1_inf_QY_valLead hU_L hV_L
  have hQX_L := br1_inf_QX_valLead hU_L hV_L
  have hqY_L : ValLead (-1)
      (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V)
      (-9 * ((evalBivK5 (QY10_biv 1) * c0_num + 3 * T_K * T59 * evalBivK5 (QY10_biv 2)) / (3 * T_K * T59 * 1701))) := by
    have hdot := ((((hQY_L 0).mul ha_L).eq_k (k' := -1) (by omega)).add (((hQY_L 1).mul hb_L).eq_k (k' := -1) (by omega))).add (hQY_L 2)
    refine valLead_eq_fc ((hdot.div_of_ne hv_L hneg19_ne).eq_k (k' := -1) (by omega)) (by simp only [dot_ab]) ?_
    have hqy0 : 3 * evalBivK5 (QY10_biv 0) + evalBivK5 (QY10_biv 1) = 0 := by
      rw [evalBivK5_QY10, evalBivK5_QY10]; linear_combination 1701 * QY_10_u1_zero S_K Q_K T_K x_K y_K
    generalize evalBivK5 (QY10_biv 0) = y0 at hqy0 ⊢
    generalize evalBivK5 (QY10_biv 1) = y1 at hqy0 ⊢
    generalize evalBivK5 (QY10_biv 2) = y2
    have hy1 : y1 = -(3 * y0) := by linear_combination hqy0
    rw [hy1]; dsimp only [b0, β]; field_simp [hT, hT59]; ring
  have hqX_L : ValLead 0
      (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U)
      (9 * (evalBivK5 cQX_0_biv / 5103 * u +
        (evalBivK5 (QX10_biv 1) * c0_num + 3 * T_K * T59 * evalBivK5 (QX10_biv 2)) / (3 * T_K * T59 * 1701))) := by
    have hdot := ((((hQX_L 0).mul ha_L).eq_k (k' := -1) (by omega)).add (((hQX_L 1).mul hb_L).eq_k (k' := -1) (by omega))).add (hQX_L 2)
    refine valLead_eq_fc ((hdot.div_of_ne hu_L (div_ne_zero one_ne_zero h9_ne)).eq_k (k' := 0) (by omega)) (by simp only [dot_ab]) ?_
    simp only [cQX_0_biv, evalBivK5_bivAdd, evalBivK5_bivScale, b0, β]
    generalize evalBivK5 (QX10_biv 0) = x0
    generalize evalBivK5 (QX10_biv 1) = x1
    generalize evalBivK5 (QX10_biv 2) = x2
    push_cast; field_simp [hT, hT59]; ring
  have hA1_L : ValLead 0 (A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) ((25 / 27 : K5) * T_K * T59 ^ 2) := by
    have hre : A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
        -(4 / 27 : LaurentSeries K5) * HahnSeries.C S3Q ^ 3 * (U * V) +
        (25 / 27 : LaurentSeries K5) * HahnSeries.C (S_K * (5 * S_K - 9 * Q_K) ^ 2) * V := by
      simp only [A1_of, S3Q, map_sub, map_mul, map_pow, map_ofNat]; ring
    rw [hre]
    have hmain : ValLead 0 (-(4 / 27 : LaurentSeries K5) * HahnSeries.C S3Q ^ 3 * (U * V)) ((25 / 27 : K5) * T_K * T59 ^ 2) := by
      rw [show -(4 / 27 : LaurentSeries K5) = HahnSeries.C (-(4 / 27 : K5)) by simp only [map_div₀, map_neg, map_ofNat]]
      exact (((ValLead.of_C _).mul ((ValLead.of_C S3Q).pow 3)).mul (hU_L.mul hV_L)).eq_k (by omega) |>.eq_c (by
        rw [hw0_eq']; field_simp [hS3Q])
    have hhi : HasValGe 1 ((25 / 27 : LaurentSeries K5) * HahnSeries.C (S_K * (5 * S_K - 9 * Q_K) ^ 2) * V) := by
      rw [show (25 / 27 : LaurentSeries K5) = HahnSeries.C (25 / 27 : K5) by simp only [map_div₀, map_ofNat]]
      exact (((HasValGe.of_C _).mul (HasValGe.of_C _)).mul hV_L.val).mono (by omega)
    exact hmain.add_high hhi
  have hB1_L : ValLead (-1) (B1_of (HahnSeries.C T_K) U V) ((25 / 27 : K5) * T_K * T59 ^ 2) := by
    have hre : B1_of (HahnSeries.C T_K) U V =
        HahnSeries.C ((25 / 27 : K5) * T_K * T59 ^ 2) * U +
        HahnSeries.C (-(4 / 27 : K5) * (T_K - 3) ^ 3) * (U * V) := by
      simp only [B1_of, T59, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
    rw [hre]
    exact (((ValLead.of_C _).mul hU_L).eq_k (by omega) |>.eq_c (mul_one _)).add_high
      (((HasValGe.of_C _).mul (hU_L.val.mul hV_L.val)).mono (by omega))
  have hH0_L : ValLead 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) (ringEval vK5 H0_int_e / 7) := by
    rw [show H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (H0_of S_K Q_K T_K) by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact (ValLead.of_C _).eq_c (by rw [ringEval_H0_7_inf]; ring)
  have hcA1_L : ValLead 0 (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V)
      ((ringEval vK5 H0_int_e / 7) * ((25 / 9 : K5) * T59 * (5 * T_K - 3)) -
       ((25 / 27 : K5) * T_K * T59 ^ 2) * (ringEval vK5 dH0_301_21_e / 21 * u +
         (ringEval vK5 (dH0_7_inf_e 1) * c0_num + 3 * T_K * T59 * ringEval vK5 (dH0_7_inf_e 2)) / (21 * T_K * T59))) := by
    have hdA1_0 : ValLead 0 (dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) ((25 / 9 : K5) * T_K * T59 ^ 2 / S3Q) := by
      have hre : dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
          HahnSeries.C (-(4 / 9 : K5) * S3Q ^ 2) * (U * V) +
          HahnSeries.C ((25 / 27 : K5) * (5 * S_K - 9 * Q_K) * (15 * S_K - 9 * Q_K)) * V := by
        simp only [dA1_fn, S3Q, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
      rw [hre]
      exact (((ValLead.of_C _).mul (hU_L.mul hV_L)).eq_k (by omega) |>.eq_c (by rw [hw0_eq']; field_simp [hS3Q])).add_high
        (((HasValGe.of_C _).mul hV_L.val).mono (by omega))
    have hdA1_1 : ValLead 0 (dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) (-(25 / 3 : K5) * T_K * T59 ^ 2 / S3Q) := by
      have hre : dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
          HahnSeries.C ((4 / 3 : K5) * S3Q ^ 2) * (U * V) +
          HahnSeries.C (-(450 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * V := by
        simp only [dA1_fn, S3Q, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]; ring
      rw [hre]
      exact (((ValLead.of_C _).mul (hU_L.mul hV_L)).eq_k (by omega) |>.eq_c (by rw [hw0_eq']; field_simp [hS3Q])).add_high
        (((HasValGe.of_C _).mul hV_L.val).mono (by omega))
    have hdH0_L (k : Fin 3) : ValLead 0 (dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K))
        (ringEval vK5 (dH0_7_inf_e k) / 7) := by
      rw [show dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (dH0_fn k S_K Q_K T_K) by
        fin_cases k <;> simp only [dH0_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
      exact (ValLead.of_C _).eq_c (by rw [ringEval_dH0_7_inf]; ring)
    have ht0 : ValLead 0 _ _ := (((hH0_L.mul hdA1_0).sub (hA1_L.mul (hdH0_L 0))).mul ha_L).eq_k (by omega)
    have ht1 : ValLead 0 _ _ := (((hH0_L.mul hdA1_1).sub (hA1_L.mul (hdH0_L 1))).mul hb_L).eq_k (by omega)
    have ht2 : ValLead 0 _ _ := (((hH0_L.mul (ValLead.of_C 0)).sub (hA1_L.mul (hdH0_L 2)))).eq_k (by omega)
    have hre0 : dA1_fn 2 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V = HahnSeries.C 0 := by simp [dA1_fn]
    refine valLead_eq_fc ((ht0.add ht1).add ht2) (by unfold cA1_of; rw [hre0]) ?_
    simp only [dH0_301_21_e, ringEval, b0, β, c0_num]
    field_simp [hS3Q, hT, hT59]; ring
  have hq1_L : ValLead (-1)
      (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
       H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) * B1_of (HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) +
       (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V / v_of V) *
        EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V)
      ((evalBivK5 q1_m1_u1_biv / 107163) * u + (evalBivK5 q1_m1_u0_biv / (3 * T_K * T59 * 107163))) := by
    have ht1 : ValLead (-1) _ _ := ((hH0_L.mul hA1_L).mul hqY_L).eq_k (by omega)
    have ht2 : ValLead (-1) _ _ := ((hH0_L.mul hB1_L).mul hqX_L).eq_k (by omega)
    have ht3 : ValLead (-1) _ _ := ((hcA1_L.div_of_ne hv_L hneg19_ne).mul hEB_L).eq_k (by omega)
    refine valLead_eq_fc ((ht1.add ht2).add ht3) rfl ?_
    have hS3Q_e : ringEval vK5 S3Q_e = S3Q := rfl
    have hT59_e : ringEval vK5 T59_e = T59 := rfl
    simp only [q1_m1_u1_biv, q1_m1_u0_biv, evalBivK5_bscE, evalBivK5_bivAdd, ringEval,
      hT59_e, hS3Q_e, T53_e, c0_num_e, eT, vK5, c0_num]
    field_simp [hT, hT59]; ring
  have hrest : HasValGe (-2)
      ((A_Y a_s b_s ξS_s ξQ_s U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
        A_X a_s b_s ξS_s ξQ_s U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U)) *
       H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2) :=
    hasValGe_eq_f (((((hAY_1.mul hqY_L.val).mono (k2 := -2) (by omega)).add
      ((hAX_2.mul hqX_L.val).mono (k2 := -2) (by omega))).mul (hH0_L.val.pow 2)).mono (k2 := -2) (by omega))
      rfl
  exact valLead_eq_fc (((hM0_L.mul hq1_L).eq_k (k' := -3) (by omega)).add_high hrest) rfl
    (by dsimp only [u, b0, β, c0_num, S3Q, T59, ξS0, ξQ0])


end SymmetricSexticResidual.LocalResidueInf

open scoped LaurentSeries in
theorem solution
    {W1s U V ca cb c0W : LaurentSeries SymmetricSexticResidual.K5Field.K5}
    {w0 : SymmetricSexticResidual.K5Field.K5}
    (hw0_eq : w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9) ^ 2 /
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hW_L : QuadraticCovers.ValLead 0 W1s w0)
    (hU_L : QuadraticCovers.ValLead (-1) U 1)
    (hV_L : QuadraticCovers.ValLead 1 V w0)
    (hca_L : QuadraticCovers.ValLead (-2) ca (-(4 / 81 : SymmetricSexticResidual.K5Field.K5) *
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 2))
    (hcb_L : QuadraticCovers.ValLead (-2) cb ((4 / 27 : SymmetricSexticResidual.K5Field.K5) *
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 2))
    (hc0W_L : QuadraticCovers.ValLead (-2) c0W (-(25 / 81 : SymmetricSexticResidual.K5Field.K5) *
      (5 * SymmetricSexticResidual.K5Field.T_K - 9) * (5 * SymmetricSexticResidual.K5Field.T_K - 3))) :
    ∀ z : SymmetricSexticResidual.K5Field.K5, QuadraticCovers.ValLead (-3)
      (SymmetricSexticResidual.SheetCalculus.P18_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.y_K)
        (HahnSeries.C z / W1s) (-(ca * HahnSeries.C z + c0W) / (W1s * cb)) U V)
      ((w0 * SymmetricSexticResidual.LocalResidueInfAlg.A0V_Uk 3 (z / w0)
        (z / w0 / 3 + -(SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
          (5 * SymmetricSexticResidual.K5Field.T_K - 3) /
          (3 * SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9)))
        (SymmetricSexticResidual.K5Field.S_K - z / w0 * SymmetricSexticResidual.K5Field.T_K)
        (SymmetricSexticResidual.K5Field.Q_K - (z / w0 / 3 +
          -(SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
          (5 * SymmetricSexticResidual.K5Field.T_K - 3) /
          (3 * SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9))) *
          SymmetricSexticResidual.K5Field.T_K)) *
       ((SymmetricSexticResidual.LocalResidueU0.evalBivK5
          SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163) * (z / w0) +
        (SymmetricSexticResidual.LocalResidueU0.evalBivK5
          SymmetricSexticResidual.LocalResidueInf.q1_m1_u0_biv /
          (3 * SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9) * 107163)))) :=
  SymmetricSexticResidual.LocalResidueInf.br1_inf_g_valLead hw0_eq hw0_ne hW_L hU_L hV_L hca_L hcb_L hc0W_L
