-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_combine_K5
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:45:22.370856+00:00
-- url     : https://prove2.me/submissions/6f08664b-72e5-4a2b-b257-f6e9d83ac994

import Definitions.Def_HodgeComputerFormal_LaurentJets
import Definitions.Def_HodgeComputerSSR_LocalInfAlgDefs
import Definitions.Def_HodgeComputerSSR_LocalInfBivId
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_biv_bridges
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_biv_identity

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueInf
open SymmetricSexticResidual.K5Field
  SymmetricSexticResidual.LocalResidueData SymmetricSexticResidual.VerticalIdentity
  SymmetricSexticResidual.LocalResidueU0 SymmetricSexticResidual.LocalResidueInfAlg
  QuadraticCovers
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

private abbrev ringEval_P44_e := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.2.2.2.2.2.2.2.1
private abbrev ringEval_M01_q_e := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.2.2.2.2.2.2.2.2.1
private abbrev ringEval_A32_2_q_e := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.2.2.2.2.2.2.2.2.2.1
private abbrev ringEval_A32_1_q_e := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges.2.2.2.2.2.2.2.2.2.2.2.2.2
private abbrev Uinf_biv_identity := HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_identity

private lemma br1_inf_combine_K5 {w0 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * T_K * (5 * T_K - 9) ^ 2 / (S_K - 3 * Q_K) ^ 3)
    (hS3Q_ne : S_K - 3 * Q_K ≠ 0) (hT59_ne : 5 * T_K - 9 ≠ 0) (hL_ne : L_K ≠ 0) :
    let S3Q := S_K - 3 * Q_K
    let T59 := 5 * T_K - 9
    let q1_1 : K5 := evalBivK5 q1_m1_u1_biv / 107163
    let q1_0 : K5 := evalBivK5 q1_m1_u0_biv / (3 * T_K * T59 * 107163)
    let c3_A : K5 := (73 / 7971615 : K5) * T59 * S3Q ^ 2
    let c2_A : K5 := A32_2_q_fn S_K Q_K T_K * T59 * S3Q / (14849347275 * (3 * T_K * T59))
    let c1_A : K5 := A32_1_q_fn S_K Q_K T_K * T59 * S3Q / (4949782425 * (3 * T_K * T59) ^ 2)
    ({ val := -(279006525 / 64 : K5) * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K),
        eps := (13286025 / 12544 : K5) * T_K * T59 ^ 2 * P44_fn S_K Q_K T_K / (S3Q ^ 11 * L_K ^ 2) } *
      { val := w0⁻¹ ^ 3 * (73 / 7971615 * T59 * S3Q ^ 2) * (evalBivK5 q1_m1_u1_biv / 107163),
        eps :=
          w0⁻¹ ^ 3 * (73 / 7971615 * T59 * S3Q ^ 2) * (evalBivK5 q1_0_u1_biv / (28 * 107163 * S3Q ^ 3)) +
          w0⁻¹ ^ 3 * (M01_q_fn S_K Q_K T_K * T59 * S3Q / (267288250950 * S3Q ^ 3)) * (evalBivK5 q1_m1_u1_biv / 107163) +
          w0⁻¹ ^ 2 * (2 / 885735 * T59 * S3Q ^ 2) * (evalBivK5 cQX_0_biv / 567) * (ringEval vK5 H0_int_e / 7) ^ 2 } +
      { val := 0,
        eps :=
          (531441 / 448 : K5) * T_K * T59 * (35 * S_K * T_K + 133 * S_K - 420 * Q_K + 225 * T_K - 45) / S3Q ^ 8 *
            (w0⁻¹ ^ 2 * (c3_A * q1_0 + c2_A * q1_1)) +
          -(177147 / 400 : K5) * T_K / S3Q ^ 5 * (w0⁻¹ * (c2_A * q1_0 + c1_A * q1_1)) } : Dual K5).eps =
      -toK5_RInf / L_K ^ 2 := by
  intro S3Q T59 q1_1 q1_0 c3_A c2_A c1_A
  have hS3Q : S3Q ≠ 0 := hS3Q_ne; have hT : T_K ≠ 0 := T_K_ne_zero
  have hT59 : T59 ≠ 0 := hT59_ne; have hL : L_K ≠ 0 := hL_ne
  have hw0_eq' : w0 = -(25 / 4 : K5) * T_K * T59 ^ 2 / S3Q ^ 3 := hw0_eq
  have hid := Uinf_biv_identity
  rw [LHS_Uinf_biv, evalBivK5_bivReduceX2, evalBivK5_bivReduceX2, RHS_Uinf_biv, evalBivK5_bscE] at hid
  have h21S : (21 * S_K) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero (by exact_mod_cast (by decide : (21 : ℕ) ≠ 0)) S_K_ne_zero)
  have hraw_eq : evalBivK5 LHS_Uinf_raw_biv = -40500 * S3Q * T_K ^ 2 * T59 ^ 3 * evalBivK5 RInf_biv := by
    apply mul_left_cancel₀ h21S
    have h1 : (21 * S_K) ^ 2 * evalBivK5 LHS_Uinf_raw_biv = (21 * S_K) * ((21 * S_K) * evalBivK5 LHS_Uinf_raw_biv) := by ring
    rw [h1, hid]
    simp only [ringEval, S3Q_e, T59_e, eS, eQ, eT, vK5, S3Q, T59, Int.cast_neg, Int.cast_ofNat]; ring
  simp only [LHS_Uinf_raw_biv, evalBivK5_bivAdd, evalBivK5_bscE, ringEval_P44_e, ringEval_M01_q_e,
    ringEval_A32_2_q_e, ringEval_A32_1_q_e, ringEval, L5_e, S3Q_e, w0_sc4_e, T59_e, lin_A3_e,
    eS, eQ, eT, vK5, Int.cast_neg, Int.cast_ofNat] at hraw_eq
  simp only [Dual.add_eps, Dual.mul_eps, toK5_RInf, D_RInf, Int.cast_ofNat, c3_A, c2_A, c1_A, q1_1, q1_0]
  have hw0_inv : w0⁻¹ = -(4 / 25 : K5) * S3Q ^ 3 / (T_K * T59 ^ 2) := by
    rw [hw0_eq']; field_simp [hS3Q, hT, hT59]
  rw [hw0_inv]
  have hL_def : (77 * S_K - 210 * Q_K + 45 : K5) = L_K := rfl
  have hS3Q_def : (S_K - 3 * Q_K : K5) = S3Q := rfl
  have hT59_def : (5 * T_K - 9 : K5) = T59 := rfl
  have hlin_def : (35 * (S_K * T_K) + 133 * S_K - 420 * Q_K + 225 * T_K - 45 : K5) =
      35 * S_K * T_K + 133 * S_K - 420 * Q_K + 225 * T_K - 45 := by ring
  rw [hL_def, hS3Q_def, hT59_def, hlin_def] at hraw_eq
  have hM_ne : ((244535547375 : K5) * 40500) ≠ 0 :=
    mul_ne_zero (ofNat_ne_zero 244535547375) (ofNat_ne_zero 40500)
  have hK_ne : ((244535547375 : K5) * 40500) * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hM_ne hS3Q) (pow_ne_zero 2 hT))
      (pow_ne_zero 3 hT59)) (pow_ne_zero 2 hL)
  apply mul_left_cancel₀ hK_ne
  have hs1 : ((244535547375 : K5) * 40500) *
      (-(279006525 / 64 : K5)) * (-(4 / 25 : K5)) ^ 3 * (73 / 7971615 : K5) / (28 * 107163 : K5) = 539715645 := by
    have hq : (244535547375 : ℚ) * 40500 * (-(279006525 / 64)) * (-(4 / 25)) ^ 3 * (73 / 7971615) / (28 * 107163) = 539715645 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs2 : ((244535547375 : K5) * 40500) *
      (-(279006525 / 64 : K5)) * (-(4 / 25 : K5)) ^ 3 / (267288250950 * 107163 : K5) = 6174 := by
    have hq : (244535547375 : ℚ) * 40500 * (-(279006525 / 64)) * (-(4 / 25)) ^ 3 / (267288250950 * 107163) = 6174 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs3 : ((244535547375 : K5) * 40500) *
      (-(279006525 / 64 : K5)) * (-(4 / 25 : K5)) ^ 2 * (2 / 885735 : K5) / (567 * 49 : K5) = 3593175390 * (-25) := by
    have hq : (244535547375 : ℚ) * 40500 * (-(279006525 / 64)) * (-(4 / 25)) ^ 2 * (2 / 885735) / (567 * 49) = 3593175390 * (-25) := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs4 : ((244535547375 : K5) * 40500) *
      (13286025 / 12544 : K5) * (-(4 / 25 : K5)) ^ 3 * (73 / 7971615 : K5) / 107163 = -3671535 := by
    have hq : (244535547375 : ℚ) * 40500 * (13286025 / 12544) * (-(4 / 25)) ^ 3 * (73 / 7971615) / 107163 = -3671535 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs5 : ((244535547375 : K5) * 40500) *
      (531441 / 448 : K5) * (-(4 / 25 : K5)) ^ 2 * (73 / 7971615 : K5) / (3 * 107163 : K5) = 8566915 := by
    have hq : (244535547375 : ℚ) * 40500 * (531441 / 448) * (-(4 / 25)) ^ 2 * (73 / 7971615) / (3 * 107163) = 8566915 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs6 : ((244535547375 : K5) * 40500) *
      (531441 / 448 : K5) * (-(4 / 25 : K5)) ^ 2 / (14849347275 * 3 * 107163 : K5) = 63 := by
    have hq : (244535547375 : ℚ) * 40500 * (531441 / 448) * (-(4 / 25)) ^ 2 / (14849347275 * 3 * 107163) = 63 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs7 : ((244535547375 : K5) * 40500) *
      (-(177147 / 400 : K5)) * (-(4 / 25 : K5)) / (14849347275 * 3 * 3 * 107163 : K5) = 49 := by
    have hq : (244535547375 : ℚ) * 40500 * (-(177147 / 400)) * (-(4 / 25)) / (14849347275 * 3 * 3 * 107163) = 49 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hs8 : ((244535547375 : K5) * 40500) *
      (-(177147 / 400 : K5)) * (-(4 / 25 : K5)) / (4949782425 * 9 * 107163 : K5) = 147 := by
    have hq : (244535547375 : ℚ) * 40500 * (-(177147 / 400)) * (-(4 / 25)) / (4949782425 * 9 * 107163) = 147 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_neg, map_pow, map_ofNat] using hc
  have hrhs : ((244535547375 : K5) * 40500) / (244535547375 : K5) = 40500 := by
    have hq : ((244535547375 : ℚ) * 40500) / 244535547375 = 40500 := by norm_num
    have hc := congrArg (Rat.castHom K5) hq; simpa only [map_mul, map_div₀, map_ofNat] using hc
  set M_c : K5 := ((244535547375 : K5) * 40500)
  have h28 : (28 : K5) ≠ 0 := ofNat_ne_zero 28
  have h107 : (107163 : K5) ≠ 0 := ofNat_ne_zero 107163
  have h267 : (267288250950 : K5) ≠ 0 := ofNat_ne_zero 267288250950
  have h567 : (567 : K5) ≠ 0 := ofNat_ne_zero 567
  have h7 : (7 : K5) ≠ 0 := ofNat_ne_zero 7
  have h3 : (3 : K5) ≠ 0 := ofNat_ne_zero 3
  have h148 : (14849347275 : K5) ≠ 0 := ofNat_ne_zero 14849347275
  have h494 : (4949782425 : K5) ≠ 0 := ofNat_ne_zero 4949782425
  have h244 : (244535547375 : K5) ≠ 0 := ofNat_ne_zero 244535547375
  have h49 : (49 : K5) = 7 ^ 2 := by norm_num
  have h9 : (9 : K5) = 3 ^ 2 := by norm_num
  rw [h49] at hs3; rw [h9] at hs8
  set cA4v : K5 := -(279006525 / 64 : K5)
  set cA4e : K5 := (13286025 / 12544 : K5)
  set cA3 : K5 := (531441 / 448 : K5)
  set cA2 : K5 := -(177147 / 400 : K5)
  set cwi : K5 := -(4 / 25 : K5)
  set c73 : K5 := (73 / 7971615 : K5)
  set c2_88 : K5 := (2 / 885735 : K5)
  set eP44 := P44_fn S_K Q_K T_K
  set eM01 := M01_q_fn S_K Q_K T_K
  set eA32_2 := A32_2_q_fn S_K Q_K T_K
  set eA32_1 := A32_1_q_fn S_K Q_K T_K
  set eLin := 35 * S_K * T_K + 133 * S_K - 420 * Q_K + 225 * T_K - 45
  set eQ1_0 := evalBivK5 q1_0_u1_biv
  set eQ1_1 := evalBivK5 q1_m1_u1_biv
  set eQ1_u0 := evalBivK5 q1_m1_u0_biv
  set eQX0 := evalBivK5 cQX_0_biv
  set eH0 := ringEval vK5 H0_int_e
  set eRInf := evalBivK5 RInf_biv
  change M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      ((cA4v * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K) *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (c73 * T59 * S3Q ^ 2) * (eQ1_0 / (28 * 107163 * S3Q ^ 3)) +
           (cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (eM01 * T59 * S3Q / (267288250950 * S3Q ^ 3)) * (eQ1_1 / 107163) +
           (cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 * (c2_88 * T59 * S3Q ^ 2) * (eQX0 / 567) * (eH0 / 7) ^ 2) +
        cA4e * T_K * T59 ^ 2 * eP44 / (S3Q ^ 11 * L_K ^ 2) *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (c73 * T59 * S3Q ^ 2) * (eQ1_1 / 107163))) +
       (cA3 * T_K * T59 * eLin / S3Q ^ 8 *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 *
            (c73 * T59 * S3Q ^ 2 * (eQ1_u0 / (3 * T_K * T59 * 107163)) +
             eA32_2 * T59 * S3Q / (14849347275 * (3 * T_K * T59)) * (eQ1_1 / 107163))) +
        cA2 * T_K / S3Q ^ 5 *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) *
            (eA32_2 * T59 * S3Q / (14849347275 * (3 * T_K * T59)) * (eQ1_u0 / (3 * T_K * T59 * 107163)) +
             eA32_1 * T59 * S3Q / (4949782425 * (3 * T_K * T59) ^ 2) * (eQ1_1 / 107163))))) =
      M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 * (-(eRInf / 244535547375) / L_K ^ 2)
  have ht1 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA4v * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K) *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (c73 * T59 * S3Q ^ 2) * (eQ1_0 / (28 * 107163 * S3Q ^ 3)))) =
      539715645 * L_K * S3Q * eQ1_0 := by
    rw [← hs1]; generalize M_c = vM; generalize cA4v = vA; generalize cwi = vw; generalize c73 = v7
    generalize (28 : K5) = d28 at h28 ⊢; generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h28, h107]
  have ht2 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA4v * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K) *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (eM01 * T59 * S3Q / (267288250950 * S3Q ^ 3)) * (eQ1_1 / 107163))) =
      6174 * L_K * eM01 * eQ1_1 := by
    rw [← hs2]; generalize M_c = vM; generalize cA4v = vA; generalize cwi = vw
    generalize (267288250950 : K5) = d267 at h267 ⊢; generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h267, h107]
  have ht3 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA4v * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K) *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 * (c2_88 * T59 * S3Q ^ 2) * (eQX0 / 567) * (eH0 / 7) ^ 2)) =
      3593175390 * L_K * (-25 * T_K * T59 ^ 2) * S3Q * eH0 ^ 2 * eQX0 := by
    have h3' : 3593175390 * L_K * (-25 * T_K * T59 ^ 2) * S3Q * eH0 ^ 2 * eQX0 =
        (3593175390 * (-25)) * L_K * T_K * T59 ^ 2 * S3Q * eH0 ^ 2 * eQX0 := by ring
    rw [h3', ← hs3]; generalize M_c = vM; generalize cA4v = vA; generalize cwi = vw; generalize c2_88 = v2
    generalize (567 : K5) = d567 at h567 ⊢; generalize (7 : K5) = d7 at h7 ⊢
    field_simp [hS3Q, hT, hT59, hL, h567, h7]
  have ht4 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA4e * T_K * T59 ^ 2 * eP44 / (S3Q ^ 11 * L_K ^ 2) *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (c73 * T59 * S3Q ^ 2) * (eQ1_1 / 107163))) =
      (-3671535) * eP44 * S3Q * eQ1_1 := by
    rw [← hs4]; generalize M_c = vM; generalize cA4e = vA; generalize cwi = vw; generalize c73 = v7
    generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h107]
  have ht5 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA3 * T_K * T59 * eLin / S3Q ^ 8 *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 * (c73 * T59 * S3Q ^ 2 * (eQ1_u0 / (3 * T_K * T59 * 107163))))) =
      8566915 * L_K ^ 2 * eLin * S3Q * eQ1_u0 := by
    rw [← hs5]; generalize M_c = vM; generalize cA3 = vA; generalize cwi = vw; generalize c73 = v7
    generalize (3 : K5) = d3 at h3 ⊢; generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h3, h107]
  have ht6 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA3 * T_K * T59 * eLin / S3Q ^ 8 *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 * (eA32_2 * T59 * S3Q / (14849347275 * (3 * T_K * T59)) * (eQ1_1 / 107163)))) =
      63 * L_K ^ 2 * eLin * eA32_2 * eQ1_1 := by
    rw [← hs6]; generalize M_c = vM; generalize cA3 = vA; generalize cwi = vw
    generalize (14849347275 : K5) = d148 at h148 ⊢; generalize (3 : K5) = d3 at h3 ⊢
    generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h148, h3, h107]
  have ht7 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA2 * T_K / S3Q ^ 5 *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) *
          (eA32_2 * T59 * S3Q / (14849347275 * (3 * T_K * T59)) * (eQ1_u0 / (3 * T_K * T59 * 107163))))) =
      49 * L_K ^ 2 * eA32_2 * eQ1_u0 := by
    rw [← hs7]; generalize M_c = vM; generalize cA2 = vA; generalize cwi = vw
    generalize (14849347275 : K5) = d148 at h148 ⊢; generalize (3 : K5) = d3 at h3 ⊢
    generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h148, h3, h107]
  have ht8 : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      (cA2 * T_K / S3Q ^ 5 *
        ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) *
          (eA32_1 * T59 * S3Q / (4949782425 * (3 * T_K * T59) ^ 2) * (eQ1_1 / 107163)))) =
      147 * L_K ^ 2 * eA32_1 * eQ1_1 := by
    rw [← hs8]; generalize M_c = vM; generalize cA2 = vA; generalize cwi = vw
    generalize (4949782425 : K5) = d494 at h494 ⊢; generalize (3 : K5) = d3 at h3 ⊢
    generalize (107163 : K5) = d107 at h107 ⊢
    field_simp [hS3Q, hT, hT59, hL, h494, h3, h107]
  have htr : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 * (-(eRInf / 244535547375) / L_K ^ 2) =
      -40500 * S3Q * T_K ^ 2 * T59 ^ 3 * eRInf := by
    have hr' : -40500 * S3Q * T_K ^ 2 * T59 ^ 3 * eRInf = -(40500 * S3Q * T_K ^ 2 * T59 ^ 3 * eRInf) := by ring
    rw [hr', ← hrhs]; generalize M_c = vM; generalize (244535547375 : K5) = d244 at h244 ⊢
    field_simp [hL, h244]
  rw [htr]
  have hexp : M_c * S3Q * T_K ^ 2 * T59 ^ 3 * L_K ^ 2 *
      ((cA4v * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K) *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (c73 * T59 * S3Q ^ 2) * (eQ1_0 / (28 * 107163 * S3Q ^ 3)) +
           (cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (eM01 * T59 * S3Q / (267288250950 * S3Q ^ 3)) * (eQ1_1 / 107163) +
           (cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 * (c2_88 * T59 * S3Q ^ 2) * (eQX0 / 567) * (eH0 / 7) ^ 2) +
        cA4e * T_K * T59 ^ 2 * eP44 / (S3Q ^ 11 * L_K ^ 2) *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 3 * (c73 * T59 * S3Q ^ 2) * (eQ1_1 / 107163))) +
       (cA3 * T_K * T59 * eLin / S3Q ^ 8 *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) ^ 2 *
            (c73 * T59 * S3Q ^ 2 * (eQ1_u0 / (3 * T_K * T59 * 107163)) +
             eA32_2 * T59 * S3Q / (14849347275 * (3 * T_K * T59)) * (eQ1_1 / 107163))) +
        cA2 * T_K / S3Q ^ 5 *
          ((cwi * S3Q ^ 3 / (T_K * T59 ^ 2)) *
            (eA32_2 * T59 * S3Q / (14849347275 * (3 * T_K * T59)) * (eQ1_u0 / (3 * T_K * T59 * 107163)) +
             eA32_1 * T59 * S3Q / (4949782425 * (3 * T_K * T59) ^ 2) * (eQ1_1 / 107163))))) =
      ((539715645 * L_K * S3Q * eQ1_0 + 6174 * L_K * eM01 * eQ1_1) +
       (3593175390 * L_K * (-25 * T_K * T59 ^ 2) * S3Q * eH0 ^ 2 * eQX0 + (-3671535) * eP44 * S3Q * eQ1_1)) +
      ((8566915 * L_K ^ 2 * eLin * S3Q * eQ1_u0 + 63 * L_K ^ 2 * eLin * eA32_2 * eQ1_1) +
       (49 * L_K ^ 2 * eA32_2 * eQ1_u0 + 147 * L_K ^ 2 * eA32_1 * eQ1_1)) := by
    rw [← ht1, ← ht2, ← ht3, ← ht4, ← ht5, ← ht6, ← ht7, ← ht8]
    generalize M_c = vM; generalize cA4v = vA4v; generalize cA4e = vA4e; generalize cA3 = vA3; generalize cA2 = vA2
    generalize cwi = vw; generalize c73 = v73; generalize c2_88 = v288
    generalize eP44 = vP44; generalize eM01 = vM01; generalize eA32_2 = vA32_2; generalize eA32_1 = vA32_1
    generalize eLin = vLin; generalize eQ1_0 = vQ1_0; generalize eQ1_1 = vQ1_1; generalize eQ1_u0 = vQ1_u0
    generalize eQX0 = vQX0; generalize eH0 = vH0; generalize S3Q = vS3Q; generalize T59 = vT59
    generalize (28 : K5) = d28; generalize (107163 : K5) = d107; generalize (267288250950 : K5) = d267
    generalize (567 : K5) = d567; generalize (7 : K5) = d7; generalize (3 : K5) = d3
    generalize (14849347275 : K5) = d148; generalize (4949782425 : K5) = d494
    ring
  rw [hexp]
  simpa only [Int.cast_neg, Int.cast_ofNat] using hraw_eq



end SymmetricSexticResidual.LocalResidueInf

theorem solution
    {w0 : SymmetricSexticResidual.K5Field.K5}
    (hw0_eq : w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9) ^ 2 / (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)
    (hS3Q_ne : SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K ≠ 0)
    (hT59_ne : 5 * SymmetricSexticResidual.K5Field.T_K - 9 ≠ 0)
    (hL_ne : SymmetricSexticResidual.LocalResidueU0.L_K ≠ 0) :
    let S3Q := SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K
    let T59 := 5 * SymmetricSexticResidual.K5Field.T_K - 9
    let q1_1 : SymmetricSexticResidual.K5Field.K5 := SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163
    let q1_0 : SymmetricSexticResidual.K5Field.K5 := SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_m1_u0_biv / (3 * SymmetricSexticResidual.K5Field.T_K * T59 * 107163)
    let c3_A : SymmetricSexticResidual.K5Field.K5 := (73 / 7971615 : SymmetricSexticResidual.K5Field.K5) * T59 * S3Q ^ 2
    let c2_A : SymmetricSexticResidual.K5Field.K5 := SymmetricSexticResidual.LocalResidueInfAlg.A32_2_q_fn SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K * T59 * S3Q / (14849347275 * (3 * SymmetricSexticResidual.K5Field.T_K * T59))
    let c1_A : SymmetricSexticResidual.K5Field.K5 := SymmetricSexticResidual.LocalResidueInfAlg.A32_1_q_fn SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K * T59 * S3Q / (4949782425 * (3 * SymmetricSexticResidual.K5Field.T_K * T59) ^ 2)
    ({ val := -(279006525 / 64 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.T_K * T59 ^ 2 / (S3Q ^ 8 * SymmetricSexticResidual.LocalResidueU0.L_K),
        eps := (13286025 / 12544 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.T_K * T59 ^ 2 * SymmetricSexticResidual.LocalResidueInfAlg.P44_fn SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K / (S3Q ^ 11 * SymmetricSexticResidual.LocalResidueU0.L_K ^ 2) } *
      { val := w0⁻¹ ^ 3 * (73 / 7971615 * T59 * S3Q ^ 2) * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163),
        eps :=
          w0⁻¹ ^ 3 * (73 / 7971615 * T59 * S3Q ^ 2) * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_0_u1_biv / (28 * 107163 * S3Q ^ 3)) +
          w0⁻¹ ^ 3 * (SymmetricSexticResidual.LocalResidueInfAlg.M01_q_fn SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K * T59 * S3Q / (267288250950 * S3Q ^ 3)) * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163) +
          w0⁻¹ ^ 2 * (2 / 885735 * T59 * S3Q ^ 2) * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.cQX_0_biv / 567) *
            (PolynomialEncoding.SignedExpressions.ringEval SymmetricSexticResidual.LocalResidueU0.vK5 SymmetricSexticResidual.VerticalIdentity.H0_int_e / 7) ^ 2 } +
      { val := 0,
        eps :=
          (531441 / 448 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.T_K * T59 * (35 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.T_K + 133 * SymmetricSexticResidual.K5Field.S_K - 420 * SymmetricSexticResidual.K5Field.Q_K + 225 * SymmetricSexticResidual.K5Field.T_K - 45) / S3Q ^ 8 *
            (w0⁻¹ ^ 2 * (c3_A * q1_0 + c2_A * q1_1)) +
          -(177147 / 400 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.T_K / S3Q ^ 5 * (w0⁻¹ * (c2_A * q1_0 + c1_A * q1_1)) } : QuadraticCovers.Dual SymmetricSexticResidual.K5Field.K5).eps =
      -SymmetricSexticResidual.LocalResidueU0.toK5_RInf / SymmetricSexticResidual.LocalResidueU0.L_K ^ 2 :=
  SymmetricSexticResidual.LocalResidueInf.br1_inf_combine_K5 hw0_eq hS3Q_ne hT59_ne hL_ne
