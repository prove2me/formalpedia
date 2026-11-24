-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localInf_br2_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T19:03:22.053894+00:00
-- url     : https://prove2.me/submissions/0fc3dbd5-4a54-4662-9d02-1953cdf93d1e

import Definitions.Def_HodgeComputerSSR_LocalInfCore
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_reg_identities
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_branch_jet_helpers
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_sheet_splits
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_weights_and_jets

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueInf
open Polynomial
open scoped LaurentSeries PowerSeries
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.LocalResidueU0 SymmetricSexticResidual.LocalResidueInfAlg
  QuadraticCovers

private abbrev P18_of_isPolyDeg4 := @HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities.P18_deg4
private abbrev EB_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.EB_bilinear
private abbrev QY_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.QY_bilinear
private abbrev QX_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.QX_bilinear
private abbrev A0V_ValLead_of := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.A0V_ValLead
private abbrev numM_split_UV := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.1
private abbrev AY_t3_U3_eq_zero := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.1
private abbrev res_z_W2_inf_val_ne := HodgeComputer.SymmetricSexticResidual.Proof.localInf_weights_and_jets.res_W2_val_ne
private abbrev numM_Uk_valLead := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_weights_and_jets.numM_Uk_valLead

lemma quadU_mul3_coeff5 {R : Type*} [CommRing R] (a0 a1 a2 b0 b1 b2 c0 c1 c2 : R) :
    (CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 * CoverParams.quadU c0 c1 c2).coeff 5 =
      a1 * b2 * c2 + a2 * b1 * c2 + a2 * b2 * c1 := by
  have heq : CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 * CoverParams.quadU c0 c1 c2 =
      C (a0 * b0 * c0) +
      C (a0 * b0 * c1 + a0 * b1 * c0 + a1 * b0 * c0) * X +
      C (a0 * b0 * c2 + a0 * b1 * c1 + a0 * b2 * c0 + a1 * b0 * c1 + a1 * b1 * c0 + a2 * b0 * c0) * X ^ 2 +
      C (a0 * b1 * c2 + a0 * b2 * c1 + a1 * b0 * c2 + a1 * b1 * c1 + a1 * b2 * c0 + a2 * b0 * c1 + a2 * b1 * c0) * X ^ 3 +
      C (a0 * b2 * c2 + a1 * b1 * c2 + a1 * b2 * c1 + a2 * b0 * c2 + a2 * b1 * c1 + a2 * b2 * c0) * X ^ 4 +
      C (a1 * b2 * c2 + a2 * b1 * c2 + a2 * b2 * c1) * X ^ 5 +
      C (a2 * b2 * c2) * X ^ 6 := by
    simp only [CoverParams.quadU, map_add, map_mul]; ring
  rw [heq]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, Nat.reduceEqDiff, ↓reduceIte, mul_zero,
    zero_add, add_zero, mul_one]


lemma k5Params_Q5_c5_eq : k5Params.Q5_z.coeff 5 = Q5_c5 S_K Q_K := by
  have h : k5Params.Q5_z =
      k5Params.q20 * k5Params.cb_h * k5Params.cb_h -
      k5Params.q11 * k5Params.ca_h * k5Params.cb_h +
      k5Params.q02 * k5Params.ca_h * k5Params.ca_h := by
    unfold CoverParams.Q5_z; ring
  rw [h, Polynomial.coeff_add, Polynomial.coeff_sub]
  simp only [CoverParams.q20, CoverParams.q11, CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h,
    quadU_mul3_coeff5, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
    k5Params_inv7, k5Params_S, k5Params_Q, Q5_c5]
  ring


private lemma br2_inf_g_scaled {W2s U V ca cb c0W : LaurentSeries K5} {w_m2 ca_m2 cb_m2 c0W_m4 : K5}
    (hw_ne : w_m2 ≠ 0) (hcb_ne : cb_m2 ≠ 0)
    (hW_L : ValLead (-2) W2s w_m2) (hU_L : ValLead (-1) U 1) (hV_L : ValLead (-1) V w_m2)
    (hca_L : ValLead (-2) ca ca_m2) (hcb_L : ValLead (-2) cb cb_m2) (hc0W_L : ValLead (-4) c0W c0W_m4) :
    let g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) (z / W2s) (-(ca * z + c0W) / (W2s * cb)) U V
    ∀ c : K5, HasValGe (-7) (g (HahnSeries.single (-2) c)) := by
  intro g c
  set z : LaurentSeries K5 := HahnSeries.single (-2) c
  dsimp only [g]
  rw [P18_of_HahnC_eq]
  set a_s := z / W2s
  set b_s := -(ca * z + c0W) / (W2s * cb)
  set a0 : K5 := c / w_m2
  set b0 : K5 := -(ca_m2 * c + c0W_m4) / (w_m2 * cb_m2)
  have hz_L : ValLead (-2) z c := ValLead.of_single (-2) c
  have ha_L : ValLead 0 a_s a0 := (hz_L.div_of_ne hW_L hw_ne).eq_k (by omega)
  have hb_L : ValLead 0 b_s b0 := by
    have hnum : ValLead (-4) _ _ := (((hca_L.mul hz_L).eq_k (by omega)).add hc0W_L).neg
    have hden : ValLead (-4) _ _ := (hW_L.mul hcb_L).eq_k (by omega)
    exact (hnum.div_of_ne hden (mul_ne_zero hw_ne hcb_ne)).eq_k (by omega)
  set ξS_s := HahnSeries.C S_K - a_s * HahnSeries.C T_K
  set ξQ_s := HahnSeries.C Q_K - b_s * HahnSeries.C T_K
  set ξS0 : K5 := S_K - a0 * T_K
  set ξQ0 : K5 := Q_K - b0 * T_K
  have hξS_L : ValLead 0 ξS_s ξS0 := (ValLead.of_C S_K).sub ((ha_L.mul (ValLead.of_C T_K)).eq_k (by omega))
  have hξQ_L : ValLead 0 ξQ_s ξQ0 := (ValLead.of_C Q_K).sub ((hb_L.mul (ValLead.of_C T_K)).eq_k (by omega))
  -- By `numM_split_UV`, every `numM mi` has `ValLead (-5) (w_m2^2 * numM_Uk 3 mi a0 b0 ξS0 ξQ0)`!
  have hUk_L (k : Fin 4) (mi : Fin 10) :
      ValLead 0 (numM_Uk k mi a_s b_s ξS_s ξQ_s) (numM_Uk k mi a0 b0 ξS0 ξQ0) :=
    numM_Uk_valLead k mi ha_L hb_L hξS_L hξQ_L
  have hnumM_L (mi : Fin 10) : ValLead (-5) (numM mi a_s b_s ξS_s ξQ_s U V) (w_m2 ^ 2 * numM_Uk 3 mi a0 b0 ξS0 ξQ0) := by
    rw [numM_split_UV]
    have hmain : ValLead (-5) (V ^ 2 * (U ^ 3 * numM_Uk 3 mi a_s b_s ξS_s ξQ_s))
        (w_m2 ^ 2 * numM_Uk 3 mi a0 b0 ξS0 ξQ0) :=
      (((hV_L.pow 2).mul ((hU_L.pow 3).mul (hUk_L 3 mi))).eq_k (by omega)).eq_c (by ring)
    have hhi : HasValGe (-4) (V ^ 2 * (U ^ 2 * numM_Uk 2 mi a_s b_s ξS_s ξQ_s +
        U * numM_Uk 1 mi a_s b_s ξS_s ξQ_s + numM_Uk 0 mi a_s b_s ξS_s ξQ_s)) := by
      have h2 := ((hU_L.val.pow 2).mul (hUk_L 2 mi).val).mono (by omega : (-2 : ℤ) ≤ _)
      have h1 := (hU_L.val.mul (hUk_L 1 mi).val).mono (by omega : (-2 : ℤ) ≤ _)
      have h0 := (hUk_L 0 mi).val.mono (by omega : (-2 : ℤ) ≤ _)
      exact ((hV_L.val.pow 2).mul ((h2.add h1).add h0)).mono (by omega)
    have hre : V ^ 2 * (U ^ 3 * numM_Uk 3 mi a_s b_s ξS_s ξQ_s + U ^ 2 * numM_Uk 2 mi a_s b_s ξS_s ξQ_s +
        U * numM_Uk 1 mi a_s b_s ξS_s ξQ_s + numM_Uk 0 mi a_s b_s ξS_s ξQ_s) =
        V ^ 2 * (U ^ 3 * numM_Uk 3 mi a_s b_s ξS_s ξQ_s) +
        V ^ 2 * (U ^ 2 * numM_Uk 2 mi a_s b_s ξS_s ξQ_s + U * numM_Uk 1 mi a_s b_s ξS_s ξQ_s +
          numM_Uk 0 mi a_s b_s ξS_s ξQ_s) := by ring
    rw [hre]; exact hmain.add_high hhi
  have hm5 (i : Fin 10) : HasValGe (-5) (numM i a_s b_s ξS_s ξQ_s U V) := (hnumM_L i).val
  have hsc5 (r : K5) {f : LaurentSeries K5} (hf : HasValGe (-5) f) : HasValGe (-5) (HahnSeries.C r * f) :=
    ((HasValGe.of_C r).mul hf).mono (by omega)
  have hnat5 (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} (hf : HasValGe (-5) f) :
      HasValGe (-5) ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) :=
    ((HasValGe.of_ofNat n).mul hf).mono (by omega)
  have hp5 (i j : Fin 10) : HasValGe (-5) (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V) :=
    (hnat5 5 (hm5 i)).sub (hnat5 9 (hm5 j))
  have hA0U_5 : HasValGe (-5) (A_0U a_s b_s ξS_s ξQ_s U V) := by
    unfold A_0U
    simpa only [map_div₀, map_neg, map_ofNat] using
      (((hsc5 (-(19708 / 1257375 : K5)) (hp5 0 1)).add (hsc5 (1472 / 1257375 : K5) (hp5 1 2))).sub
        (hsc5 (16 / 729 : K5) (hp5 3 5))).add (hsc5 (188 / 2025 : K5) (hp5 4 6))
  have hA0V_5 : HasValGe (-5) (A_0V a_s b_s ξS_s ξQ_s U V) := by
    unfold A_0V
    simpa only [map_div₀, map_neg, map_ofNat] using
      (((hsc5 (-(892 / 3645 : K5)) (hp5 3 4)).add (hsc5 (40 / 81 : K5) (hp5 5 6))).sub
        (hsc5 (112 / 2395 : K5) (hp5 7 8))).add (hsc5 (392 / 11975 : K5) (hp5 8 9))
  have hM0_4 : HasValGe (-4) (A_0U a_s b_s ξS_s ξQ_s U V / U + A_0V a_s b_s ξS_s ξQ_s U V / V) :=
    ((hA0U_5.div_of_lead_ne hU_L.val (hU_L.c0.symm ▸ one_ne_zero)).1.mono (by omega)).add
      ((hA0V_5.div_of_lead_ne hV_L.val (hV_L.c0.symm ▸ hw_ne)).1.mono (by omega))
  have hAX_6 : HasValGe (-6) (A_X a_s b_s ξS_s ξQ_s U V) := by
    unfold A_X
    refine (hU_L.val.mul (?_ : HasValGe (-5) _)).mono (by omega)
    simpa only [map_div₀, map_neg, map_ofNat] using
      ((hsc5 (-(8 / 405 : K5)) (hp5 3 4)).sub (hsc5 (476 / 7185 : K5) (hp5 7 8))).add
        (hsc5 (6916 / 35925 : K5) (hp5 8 9))
  have hAY_6 : HasValGe (-6) (A_Y a_s b_s ξS_s ξQ_s U V) := by
    unfold A_Y
    refine (HasValGe.add (HasValGe.add ?_ ?_) ?_)
    · refine HasValGe.mono (by omega) (?_ : HasValGe (-5) _)
      simpa only [map_div₀, map_neg, map_ofNat] using
        hsc5 (-(100 / 243 : K5)) ((((hnat5 25 (hm5 3)).sub (hnat5 45 (hm5 4))).sub (hnat5 45 (hm5 5))).add (hnat5 81 (hm5 6)))
    · refine (hV_L.val.mul (?_ : HasValGe (-5) _)).mono (by omega)
      simpa only [map_div₀, map_neg, map_ofNat] using
        (((hsc5 (-(907876 / 33949125 : K5)) (hp5 0 1)).add (hsc5 (2258324 / 33949125 : K5) (hp5 1 2))).add
          (hsc5 (8 / 243 : K5) (hp5 3 5))).sub (hsc5 (64 / 675 : K5) (hp5 4 6))
    · have hL5 (r : K5) {f : LaurentSeries K5} {v : K5} (hf : ValLead (-5) f v) :
          ValLead (-5) (HahnSeries.C r * f) (r * v) := ((ValLead.of_C r).mul hf).eq_k (by omega)
      have hN5 (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} {v : K5} (hf : ValLead (-5) f v) :
          ValLead (-5) ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) ((no_index (OfNat.ofNat n) : K5) * v) :=
        ((ValLead.of_ofNat n).mul hf).eq_k (by omega)
      have hcomb : ValLead (-5)
          (-(123236 / 24249375 : LaurentSeries K5) * (numM 0 a_s b_s ξS_s ξQ_s U V +
            (2790 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + 28 * numM 8 a_s b_s ξS_s ξQ_s U V -
            (5904 / 77) * numM 9 a_s b_s ξS_s ξQ_s U V) +
           (492944 / 33949125) * (numM 1 a_s b_s ξS_s ξQ_s U V +
            (927 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + (49 / 5) * numM 8 a_s b_s ξS_s ξQ_s U V -
            (21159 / 770) * numM 9 a_s b_s ξS_s ξQ_s U V)) 0 := by
        have hraw := (hL5 (-(123236 / 24249375 : K5))
          (((((hnumM_L 0).add (hL5 (2790 / 77 : K5) (hnumM_L 6))).add (hN5 28 (hnumM_L 8))).sub
            (hL5 (5904 / 77 : K5) (hnumM_L 9))))).add
          (hL5 (492944 / 33949125 : K5)
          (((((hnumM_L 1).add (hL5 (927 / 77 : K5) (hnumM_L 6))).add (hL5 (49 / 5 : K5) (hnumM_L 8))).sub
            (hL5 (21159 / 770 : K5) (hnumM_L 9)))))
        simp only [map_div₀, map_neg, map_ofNat] at hraw
        refine hraw.eq_c ?_
        have hz := AY_t3_U3_eq_zero a0 b0 ξS0 ξQ0
        linear_combination w_m2 ^ 2 * hz
      exact ((hU_L.val.mul hV_L.val).mul hcomb.hasValGe_succ).mono (by omega)
  -- Now `qX, qY` (`HasValGe (-1)`), `A1, B1, cA1, EB` (`HasValGe (-2)`), `u_of U, v_of V` (`ValLead (-1)`) -> `q1` (`HasValGe (-3)`)!
  have h9_ne : (9 : K5) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  have hu_L : ValLead (-1) (u_of U) (1 / 9 : K5) := by
    unfold u_of
    exact ((hU_L.add_high (HasValGe.of_C (-1 : K5))).div_of_ne (ValLead.of_ofNat 9) h9_ne).eq_k (by omega)
      |> fun h => by simpa only [sub_eq_add_neg, map_neg, map_one] using h
  have hv_L : ValLead (-1) (v_of V) (w_m2 / 9) := by
    unfold v_of
    exact ((hV_L.add_high (HasValGe.of_C (-1 : K5))).div_of_ne (ValLead.of_ofNat 9) h9_ne).eq_k (by omega)
      |> fun h => by simpa only [sub_eq_add_neg, map_neg, map_one] using h
  have hbi2 (a00 a01 a10 a11 : K5) :
      HasValGe (-2) (HahnSeries.C a00 + HahnSeries.C a01 * V + HahnSeries.C a10 * U + HahnSeries.C a11 * U * V) :=
    ((((HasValGe.of_C a00).mono (by omega)).add (((HasValGe.of_C a01).mul hV_L.val).mono (by omega))).add
      (((HasValGe.of_C a10).mul hU_L.val).mono (by omega))).add
      ((((HasValGe.of_C a11).mul hU_L.val).mul hV_L.val).mono (by omega))
  have hEB_2 : HasValGe (-2) (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) := by
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
    exact hbi2 _ _ _ _
  have hQY_2 (i : Fin 3) : HasValGe (-2) (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i) := by
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
    exact hbi2 _ _ _ _
  have hQX_2 (i : Fin 3) : HasValGe (-2) (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i) := by
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
    exact hbi2 _ _ _ _
  have hqY_1 : HasValGe (-1) (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) := by
    have hdot : HasValGe (-2) (dot_ab _ a_s b_s) :=
      ((((hQY_2 0).mul ha_L.val).mono (by omega)).add (((hQY_2 1).mul hb_L.val).mono (by omega))).add (hQY_2 2)
    exact (hdot.div_of_lead_ne hv_L.val (hv_L.c0.symm ▸ div_ne_zero hw_ne h9_ne)).1.mono (by omega)
  have hqX_1 : HasValGe (-1) (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) := by
    have hdot : HasValGe (-2) (dot_ab _ a_s b_s) :=
      ((((hQX_2 0).mul ha_L.val).mono (by omega)).add (((hQX_2 1).mul hb_L.val).mono (by omega))).add (hQX_2 2)
    exact (hdot.div_of_lead_ne hu_L.val (hu_L.c0.symm ▸ div_ne_zero one_ne_zero h9_ne)).1.mono (by omega)
  have hA1_2 : HasValGe (-2) (A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) := by
    have heq : A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
        HahnSeries.C 0 + HahnSeries.C (A1_of S_K Q_K 0 1) * V + HahnSeries.C 0 * U +
        HahnSeries.C (A1_of S_K Q_K 1 1 - A1_of S_K Q_K 0 1) * U * V := by
      simp only [A1_of, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one, map_zero]; ring
    rw [heq]; exact hbi2 _ _ _ _
  have hB1_2 : HasValGe (-2) (B1_of (HahnSeries.C T_K) U V) := by
    have heq : B1_of (HahnSeries.C T_K) U V =
        HahnSeries.C 0 + HahnSeries.C 0 * V + HahnSeries.C (B1_of T_K 1 0) * U +
        HahnSeries.C (B1_of T_K 1 1 - B1_of T_K 1 0) * U * V := by
      simp only [B1_of, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one, map_zero]; ring
    rw [heq]; exact hbi2 _ _ _ _
  have hH0_0 : HasValGe 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
    rw [show H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (H0_of S_K Q_K T_K) by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
    exact HasValGe.of_C _
  have hcA1_2 : HasValGe (-2) (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V) := by
    have hdA1 (k : Fin 3) : HasValGe (-2) (dA1_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) := by
      fin_cases k
      · change HasValGe (-2) (dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V)
        have heq : dA1_fn 0 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
            HahnSeries.C 0 + HahnSeries.C (dA1_fn 0 S_K Q_K 0 1) * V + HahnSeries.C 0 * U +
            HahnSeries.C (dA1_fn 0 S_K Q_K 1 1 - dA1_fn 0 S_K Q_K 0 1) * U * V := by
          simp only [dA1_fn, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one, map_zero]; ring
        rw [heq]; exact hbi2 _ _ _ _
      · change HasValGe (-2) (dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V)
        have heq : dA1_fn 1 (HahnSeries.C S_K) (HahnSeries.C Q_K) U V =
            HahnSeries.C 0 + HahnSeries.C (dA1_fn 1 S_K Q_K 0 1) * V + HahnSeries.C 0 * U +
            HahnSeries.C (dA1_fn 1 S_K Q_K 1 1 - dA1_fn 1 S_K Q_K 0 1) * U * V := by
          simp only [dA1_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_one, map_zero]; ring
        rw [heq]; exact hbi2 _ _ _ _
      · exact HasValGe.zero (-2)
    have hdH0 (k : Fin 3) : HasValGe 0 (dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
      rw [show dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) = HahnSeries.C (dH0_fn k S_K Q_K T_K) by
        fin_cases k <;> simp only [dH0_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]]
      exact HasValGe.of_C _
    unfold cA1_of
    exact (((((hH0_0.mul (hdA1 0)).mono (k2 := -2) (by omega)).sub ((hA1_2.mul (hdH0 0)).mono (k2 := -2) (by omega))).mul ha_L.val |>.mono (k2 := -2) (by omega)).add
      (((((hH0_0.mul (hdA1 1)).mono (k2 := -2) (by omega)).sub ((hA1_2.mul (hdH0 1)).mono (k2 := -2) (by omega))).mul hb_L.val |>.mono (k2 := -2) (by omega)))).add
      ((((hH0_0.mul (hdA1 2)).mono (k2 := -2) (by omega)).sub ((hA1_2.mul (hdH0 2)).mono (k2 := -2) (by omega))))
  have hq1_3 : HasValGe (-3) _ :=
    (((hH0_0.mul hA1_2).mul hqY_1).mono (k2 := -3) (by omega)).add (((hH0_0.mul hB1_2).mul hqX_1).mono (k2 := -3) (by omega)) |>.add
      (((hcA1_2.div_of_lead_ne hv_L.val (hv_L.c0.symm ▸ div_ne_zero hw_ne h9_ne)).1.mul hEB_2).mono (k2 := -3) (by omega))
  exact ((hM0_4.mul hq1_3).mono (k2 := -7) (by omega)).add
    ((((hAY_6.mul hqY_1).mono (k2 := -7) (by omega)).add ((hAX_6.mul hqX_1).mono (k2 := -7) (by omega))).mul (hH0_0.pow 2) |>.mono (k2 := -7) (by omega))

lemma br2_inf_eta_AC_coeff_one : (br2_inf eta_AC).coeff 1 = 0 := by
  let U := HahnSeries.single (-1 : ℤ) (1 : K5)
  let V := W2_inf / U
  let ca := evalInvT k5Params.ca_h
  let cb := evalInvT k5Params.cb_h
  let c0W := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.c0W)
  let d2_2 := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_2)
  let d2_1 := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_1)
  let d2_0 := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_0)
  let d1 := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d1_z)
  let d0 := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d0_z)
  let res := PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)
  let g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
    P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) (z / W2_inf) (-(ca * z + c0W) / (W2_inf * cb)) U V
  let p := interp4 g
  let P1 := remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1
  let P0 := remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2
  have hbr : br2_inf eta_AC =
      (-(P1 * d0 - P0 * d1) * U ^ 3 * W2_inf * cb ^ 4) /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W2_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res) :=
    branchHom_eta_AC_of_eq ψinf ψinf_C W2_inf W2_inf_eq_ψinf U ψinf_X evalInvT (RingHom.ext ψinf_toRat)
      V ca cb c0W d2_2 d2_1 d2_0 d1 d0 res g p P1 P0
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [hbr]
  set w_m2 : K5 := -(k5Params.Bv2 * k5Params.Av0_inv)
  have hAi_ne : k5Params.Av0_inv ≠ 0 := fun h => by
    have := k5Params_Av0_mul_inv; rw [h, mul_zero] at this; exact zero_ne_one this
  have hw_ne : w_m2 ≠ 0 := neg_ne_zero.mpr (mul_ne_zero k5Params_Bv2_ne hAi_ne)
  have hw_c : W2_inf.coeff (-2) = w_m2 := by
    rw [W2_inf, HahnSeries.coeff_sub, HahnSeries.coeff_neg, HasValGe_W1_inf (-2) (by omega), sub_zero,
      evalInvT_bW_eq]
    have hmul := (HasValGe.single (-2 : ℤ) (1 : K5)).coeff_mul_min (HasValGe.of_powerSeries bInfPS)
    simp only [add_zero] at hmul
    rw [hmul, HahnSeries.coeff_single_same, one_mul]
    change -(HahnSeries.coeff ((bInfPS : PowerSeries K5) : LaurentSeries K5) (0 : ℕ)) = _
    rw [LaurentSeries.coeff_coe_powerSeries, bInfPS_coeff0]
  have hW_L : ValLead (-2) W2_inf w_m2 := ⟨HasValGe_W2_inf, hw_c⟩
  have hU_L : ValLead (-1) U 1 := ValLead.of_single (-1) 1
  have hV_L : ValLead (-1) V w_m2 := (hW_L.div_of_ne hU_L one_ne_zero).eq_k (by omega) |>.eq_c (div_one w_m2)
  have hca_L : ValLead (-2) ca (k5Params.ca_h.coeff 2) := (ValDual.of_evalInvT _ deg2_ca (by omega)).toValLead
  have hcb_L : ValLead (-2) cb (k5Params.cb_h.coeff 2) := (ValDual.of_evalInvT _ deg2_cb (by omega)).toValLead
  have hcb_ne : k5Params.cb_h.coeff 2 ≠ 0 := by
    have heq : k5Params.cb_h.coeff 2 = (4 / 27 : K5) * (S_K - 3 * Q_K) ^ 2 := by
      simp only [CoverParams.cb_h, coeff_quadU, CoverParams.inv27, CoverParams.inv9, k5Params_inv3, k5Params_S, k5Params_Q]; ring
    rw [heq]
    exact mul_ne_zero (div_ne_zero (by exact_mod_cast (by decide : (4 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (27 : ℕ) ≠ 0))) (pow_ne_zero 2 S_K_sub_3Q_ne)
  have htoUW (v0 v1 v2 : K5) :
      ValLead (-4) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2))) (v2 * w_m2 ^ 2) := by
    have heq : PairAlg.evalAt W2_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2)) =
        HahnSeries.C v2 * W2_inf ^ 2 +
        (HahnSeries.C v1 * HahnSeries.single (-1) 1 * W2_inf + HahnSeries.C v0 * HahnSeries.single (-2) 1) := by
      simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
        evalInvT_C, evalInvT_X, HahnSeries.single_pow]
      have h2p : (2 : ℕ) • (-1 : ℤ) = -2 := by decide
      simp only [one_pow, h2p]; linear_combination -HahnSeries.C v2 * W2_inf_eq
    rw [heq]
    exact (((ValLead.of_C v2).mul (hW_L.pow 2)).eq_k (by omega)).add_high
      (((((HasValGe.of_C v1).mul (HasValGe.single (-1) 1)).mul HasValGe_W2_inf).mono (by omega)).add
        (((HasValGe.of_C v0).mul (HasValGe.single (-2) 1)).mono (by omega)))
  have hc0W_L : ValLead (-4) c0W (k5Params.c0_V2 * w_m2 ^ 2) := htoUW _ _ _
  have hk2W_L := htoUW k5Params.k2_V0 k5Params.k2_V1 k5Params.k2_V2
  have hk3W_L := htoUW k5Params.k3_V0 k5Params.k3_V1 k5Params.k3_V2
  have hg_scaled : ∀ c : K5, HasValGe (-7) (g (HahnSeries.single (-2) c)) :=
    br2_inf_g_scaled hw_ne hcb_ne hW_L hU_L hV_L hca_L hcb_L hc0W_L
  have hg_deg4 : IsPolyDeg 4 g := by
    have h := P18_of_isPolyDeg4 (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V (1 / W2_inf) 0 (-ca / (W2_inf * cb)) (-c0W / (W2_inf * cb))
    refine h.congr (fun z => ?_)
    dsimp only [g]
    have hW_ne' : W2_inf ≠ 0 := fun h0 => hw_ne (by rw [← hw_c, h0]; rfl)
    have hcb_ne' : cb ≠ 0 := fun h0 => hcb_ne (by rw [← hcb_L.c0, h0]; rfl)
    have h1 : z / W2_inf = 1 / W2_inf * z + 0 := by ring
    have h2 : -(ca * z + c0W) / (W2_inf * cb) = -ca / (W2_inf * cb) * z + -c0W / (W2_inf * cb) := by
      field_simp [hW_ne', hcb_ne']; ring
    rw [h1, h2]
  obtain ⟨hp4, hp3, hp2, hp1, hp0⟩ := HasValGe.interp4_scaled (s := -2) (k := -7) hg_deg4 hg_scaled
  -- Valuations of `d2_2..0, d3_3..0, d1, d0` along `W2_inf`:
  have hQ5_L : ValLead (-5) (evalInvT k5Params.Q5_z) (Q5_c5 S_K Q_K) :=
    (ValDual.of_evalInvT _ k5Params_Q5_z_natDegree_le (by omega)).toValLead.eq_c k5Params_Q5_c5_eq
  have hq2 : HasValGe (-5) d2_2 := by
    simpa [d2_2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ5_L.val
  have hq1 : HasValGe (-7) d2_1 := by
    rw [show d2_1 = evalInvT (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h) * c0W by
      simp only [d2_1, c0W, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]]
    exact ((HasValGe.evalInvT_of_natDegree_le _ k5Params_p21_natDegree_le).mul hc0W_L.val).mono (by omega)
  have hq02 : ValLead (-2) (evalInvT k5Params.q02) (k5Params.q02.coeff 2) := (ValDual.of_evalInvT _ deg2_q02 (by omega)).toValLead
  have hc03 : ValLead (-2) (evalInvT k5Params.c03) (k5Params.c03.coeff 2) := (ValDual.of_evalInvT _ deg2_c03 (by omega)).toValLead
  have hq0 : HasValGe (-9) d2_0 := by
    dsimp only [d2_0]
    rw [CoverParams.d2_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
      PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
      PairAlg.map_mul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq,
      PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq, PairAlg.map_W, PairAlg.evalAt_W, map_pow]
    have hL : ValLead (-10) _ _ := ((hq02.mul (hc0W_L.mul hc0W_L)).eq_k (by omega)).add
      (((hcb_L.pow 2).mul (hW_L.mul hk2W_L)).eq_k (by omega))
    refine (hL.eq_c ?_).hasValGe_succ
    simp only [CoverParams.q02, CoverParams.cb_h, CoverParams.c0_V2, CoverParams.k2_V2,
      CoverParams.Bv2, CoverParams.Av0_inv, coeff_quadU, CoverParams.inv4, CoverParams.inv9,
      CoverParams.inv27, CoverParams.inv81, CoverParams.inv243, k5Params_inv2, k5Params_inv3,
      k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T, w_m2]
    have hT := T_K_sub_3_ne; field_simp [hT]; ring
  have he3 : HasValGe (-7) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_3)) := by
    simpa [CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using
      HasValGe.evalInvT_of_natDegree_le _ k5Params_Q7_z_natDegree_le
  have he2 : HasValGe (-9) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_2)) := by
    rw [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
    exact ((HasValGe.evalInvT_of_natDegree_le _ k5Params_p32_natDegree_le).mul hc0W_L.val).mono (by omega)
  have he1 : HasValGe (-11) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_1)) := by
    rw [CoverParams.d3_1, PairAlg.map_smul, PairAlg.evalAt_smul, CoverParams.pmul,
      PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq]
    exact ((HasValGe.evalInvT_of_natDegree_le _ k5Params_p31_natDegree_le).mul (hc0W_L.val.mul hc0W_L.val)).mono (by omega)
  have he0 : HasValGe (-13) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_0)) := by
    rw [CoverParams.d3_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
      PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
      CoverParams.pmul, CoverParams.pmul, PairAlg.map_mul, PairAlg.map_mul, PairAlg.map_mul,
      PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq,
      PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq, PairAlg.map_W,
      PairAlg.evalAt_W, map_neg, map_pow]
    have hL : ValLead (-14) _ _ := ((hc03.neg.mul (hc0W_L.mul (hc0W_L.mul hc0W_L))).eq_k (by omega)).add
      (((hcb_L.pow 3).mul ((hW_L.mul hW_L).mul hk3W_L)).eq_k (by omega))
    refine (hL.eq_c ?_).hasValGe_succ
    simp only [CoverParams.c03, CoverParams.cb_h, CoverParams.c0_V2, CoverParams.k3_V2,
      CoverParams.Bv2, CoverParams.Av0_inv, coeff_quadU, CoverParams.inv4, CoverParams.inv9,
      CoverParams.inv27, CoverParams.inv81, CoverParams.inv243, k5Params_inv2, k5Params_inv3,
      k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T, w_m2]
    have hT := T_K_sub_3_ne; field_simp [hT]; ring
  have hd1 : HasValGe (-21) d1 := by
    simp only [d1, CoverParams.d1_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq]
    have t1 : HasValGe (-16) _ := ((hq2.mul he1).mono (by omega)).sub ((hq0.mul he3).mono (by omega))
    have t2 : HasValGe (-14) _ := ((hq2.mul he2).mono (by omega)).sub ((hq1.mul he3).mono (by omega))
    exact ((hq2.mul t1).mono (by omega)).sub ((hq1.mul t2).mono (by omega))
  have hd0 : HasValGe (-23) d0 := by
    simp only [d0, CoverParams.d0_z, CoverParams.pmul, PairAlg.map_sub, PairAlg.map_mul,
      PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W2_inf W2_inf_eq]
    have t1 : HasValGe (-18) _ := (hq2.mul he0).mono (by omega)
    have t2 : HasValGe (-14) _ := ((hq2.mul he2).mono (by omega)).sub ((hq1.mul he3).mono (by omega))
    exact ((hq2.mul t1).mono (by omega)).sub ((hq0.mul t2).mono (by omega))
  have hP1 : HasValGe (-20) P1 := by
    simp only [P1, remDeg4_P1]
    have hr3 : HasValGe (-6) (d2_2 * p.2.1 - d2_1 * p.1) :=
      ((hq2.mul hp3).mono (by omega)).sub ((hq1.mul hp4).mono (by omega))
    have hr2 : HasValGe (-8) (d2_2 * p.2.2.1 - d2_0 * p.1) :=
      ((hq2.mul hp2).mono (by omega)).sub ((hq0.mul hp4).mono (by omega))
    have hs2 : HasValGe (-13) (d2_2 * (d2_2 * p.2.2.1 - d2_0 * p.1) - d2_1 * (d2_2 * p.2.1 - d2_1 * p.1)) :=
      ((hq2.mul hr2).mono (by omega)).sub ((hq1.mul hr3).mono (by omega))
    have hs1 : HasValGe (-15) (d2_2 ^ 2 * p.2.2.2.1 - d2_0 * (d2_2 * p.2.1 - d2_1 * p.1)) :=
      (((hq2.pow 2).mul hp1).mono (by omega)).sub ((hq0.mul hr3).mono (by omega))
    exact ((hq2.mul hs1).mono (by omega)).sub ((hq1.mul hs2).mono (by omega))
  have hP0 : HasValGe (-22) P0 := by
    simp only [P0, remDeg4_P0]
    have hr3 : HasValGe (-6) (d2_2 * p.2.1 - d2_1 * p.1) :=
      ((hq2.mul hp3).mono (by omega)).sub ((hq1.mul hp4).mono (by omega))
    have hr2 : HasValGe (-8) (d2_2 * p.2.2.1 - d2_0 * p.1) :=
      ((hq2.mul hp2).mono (by omega)).sub ((hq0.mul hp4).mono (by omega))
    have hs2 : HasValGe (-13) (d2_2 * (d2_2 * p.2.2.1 - d2_0 * p.1) - d2_1 * (d2_2 * p.2.1 - d2_1 * p.1)) :=
      ((hq2.mul hr2).mono (by omega)).sub ((hq1.mul hr3).mono (by omega))
    exact (((hq2.pow 3).mul hp0).mono (by omega)).sub ((hq0.mul hs2).mono (by omega))
  have hnum : HasValGe (-56) (-(P1 * d0 - P0 * d1) * U ^ 3 * W2_inf * cb ^ 4) := by
    have hsub : HasValGe (-43) (P1 * d0 - P0 * d1) :=
      ((hP1.mul hd0).mono (by omega)).sub ((hP0.mul hd1).mono (by omega))
    exact (((hsub.neg.mul (hU_L.val.pow 3)).mul hW_L.val).mul (hcb_L.val.pow 4)).mono (by omega)
  obtain ⟨hres_val, hres_ne⟩ := res_z_W2_inf_val_ne
  have h2W_L : ValLead (-2) (2 * W2_inf + evalInvT k5Params.bW) w_m2 := by
    have hbW : ValLead (-2) (evalInvT k5Params.bW) (-w_m2) := by
      have hdeg : k5Params.bW.natDegree ≤ 2 := by
        rw [CoverParams.bW]; exact (Polynomial.natDegree_C_mul_le _ _).trans (natDegree_quadU_le _ _ _)
      exact (ValDual.of_evalInvT _ hdeg (by omega)).toValLead.eq_c (by
        simp only [CoverParams.bW, CoverParams.Bv, Polynomial.coeff_C_mul, coeff_quadU, w_m2]; ring)
    exact ((((ValLead.of_ofNat 2).mul hW_L).eq_k (by omega)).add hbW).eq_c (by ring)
  have hden_L : ValLead (-58)
      (81 * HahnSeries.C k5Params.Av0 * (2 * W2_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res)
      (81 * k5Params.Av0 * w_m2 * Q5_c5 S_K Q_K ^ 3 * res.coeff (-41)) :=
    (((((ValLead.of_ofNat 81).mul (ValLead.of_C k5Params.Av0)).mul h2W_L).mul (hQ5_L.pow 3)).mul ⟨hres_val, rfl⟩).eq_k
      (by omega)
  have hQ5_ne : Q5_c5 S_K Q_K ≠ 0 := by
    have hfac : Q5_c5 S_K Q_K = (16 / 413343 : K5) * L_K * (S_K - 3 * Q_K) ^ 4 := by
      simp only [Q5_c5, L_K]; ring
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero (div_ne_zero (by exact_mod_cast (by decide : (16 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (413343 : ℕ) ≠ 0))) L_K_ne_zero) (pow_ne_zero 4 S_K_sub_3Q_ne)
  have hden_ne : (81 * HahnSeries.C k5Params.Av0 * (2 * W2_inf + evalInvT k5Params.bW) *
      evalInvT k5Params.Q5_z ^ 3 * res).coeff (-58) ≠ 0 := by
    rw [hden_L.c0]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by exact_mod_cast (by decide : (81 : ℕ) ≠ 0))
      k5Params_Av0_ne) hw_ne) (pow_ne_zero 3 hQ5_ne)) hres_ne
  have hquot : HasValGe 2 (-(P1 * d0 - P0 * d1) * U ^ 3 * W2_inf * cb ^ 4 /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W2_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res)) :=
    (hnum.div_of_lead_ne hden_L.val hden_ne).1.mono (by omega)
  exact hquot 1 (by omega)


end SymmetricSexticResidual.LocalResidueInf

theorem solution :
    (SymmetricSexticResidual.LocalResidueInf.br2_inf SymmetricSexticResidual.CoverResidue.eta_AC).coeff 1 = 0 :=
  SymmetricSexticResidual.LocalResidueInf.br2_inf_eta_AC_coeff_one
