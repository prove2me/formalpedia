-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.global_residue_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:53:35.070648+00:00
-- url     : https://prove2.me/submissions/299478b9-56c0-4f15-b6e3-7d01e3feb1fd

import Definitions.Def_HodgeComputerSSR_GlobalBiv
import Theorems.Thm_HodgeComputer_Formal_KroneckerCheck_biv_denote_eq_of_kronecker3
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_global_biv_x0

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.VerticalData
  SymmetricSexticResidual.VerticalIdentity SymmetricSexticResidual.LocalResidueData
  SymmetricSexticResidual.LocalResidueU0
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

private lemma global_biv_identity : evalBivK5 LHS_glob_biv = 0 := by
  have hx1 : evalBivK5 (bivFilterX1 LHS_glob_biv) = 0 := by
    have h := HodgeComputer.Formal.KroneckerCheck.biv_denote_eq_of_kronecker3
      vK5 x_K y_K 18 16 16 (2 ^ 105) (bivFilterX1 LHS_glob_biv) .nil (by decide +kernel)
    simpa only [evalBivK5, denote] using h
  rw [evalBivK5_bivFilter_add, HodgeComputer.SymmetricSexticResidual.Proof.global_biv_x0, hx1, add_zero]

theorem global_residue_cancellation :
    toK5 P_horiz_5 = -toK5_RInf / L_K ^ 2 - toK5_RU - toK5_RQ5 / L_K ^ 2 := by
  have hid := global_biv_identity
  rw [LHS_glob_biv, evalBivK5_bivAdd, evalBivK5_bivAdd, evalBivK5_scale, evalBivK5_bivAdd,
    evalBivK5_scale, evalBivK5_scale, evalBivK5_scale] at hid
  have hL5 : ringEval vK5 (.pow L5_glob_e 2) = L_K ^ 2 := by
    simp only [L5_glob_e, ringEval, vK5, L_K, Int.cast_neg, Int.cast_ofNat]; ring
  have hP : evalBivK5 P_horiz_biv = (D_P : K5) * toK5 P_horiz_5 := by
    have hDP_ne : (D_P : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by unfold D_P; decide)
    have hCmul : (D_P : K5) * toK5 (MvPolynomial.C (1 / (D_P : ℂ))) = 1 := by
      have h1 : (D_P : K5) = toK5 (MvPolynomial.C (D_P : ℂ)) := by
        have hC : MvPolynomial.C (D_P : ℂ) = (D_P : MvPolynomial (Fin 5) ℂ) :=
          map_intCast (MvPolynomial.C (σ := Fin 5) (R := ℂ)) D_P
        rw [hC, map_intCast]
      rw [h1, ← map_mul, ← map_mul, mul_one_div_cancel hDP_ne, map_one, map_one]
    have hev : toK5 (evalBiv5 P_horiz_biv) = evalBivK5 P_horiz_biv := by
      have hgen : ∀ b : Biv, toK5 (evalBiv5 b) = evalBivK5 b := by
        intro b; induction b with
        | nil => simp [evalBiv5, evalBivK5, denote]
        | cons e i j rest ih =>
            simp only [evalBiv5, evalBivK5, denote, map_add, map_mul, map_pow] at ih ⊢
            rw [ih]
            have hv : toK5 (ringEval vSQT e) = ringEval vK5 e := by
              induction e with
              | num c => simp [ringEval]
              | natCast n => simp [ringEval]
              | intCast z => simp [ringEval]
              | var k =>
                  match k with
                  | 0 => simp [ringEval, vSQT, vK5, toK5]
                  | 1 => simp [ringEval, vSQT, vK5, toK5]
                  | 2 => simp [ringEval, vSQT, vK5, toK5]
                  | _ + 3 => simp [ringEval, vSQT, vK5]
              | neg a ha => simp [ringEval] at ha ⊢; rw [ha]
              | add a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
              | sub a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
              | mul a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
              | pow a k ha => simp [ringEval] at ha ⊢; rw [ha]
            have hx3 : toK5 (MvPolynomial.X 3) = x_K := by simp [toK5]
            have hx4 : toK5 (MvPolynomial.X 4) = y_K := by simp [toK5]
            rw [hv, hx3, hx4]
      exact hgen P_horiz_biv
    rw [P_horiz_5, map_mul, hev, ← mul_assoc, hCmul, one_mul]
  have hRU : evalBivK5 RU_biv = (D_RU : K5) * toK5_RU := evalBivK5_RU
  have hRInf : evalBivK5 RInf_biv = (D_RInf : K5) * toK5_RInf := by
    rw [toK5_RInf, mul_div_cancel₀ _ (Int.cast_ne_zero.mpr (by unfold D_RInf; decide))]
  have hRQ5 : evalBivK5 RQ5_biv = (D_RQ5 : K5) * toK5_RQ5 := by
    rw [toK5_RQ5, mul_div_cancel₀ _ (Int.cast_ne_zero.mpr (by unfold D_RQ5; decide))]
  have hD_rels : (105 : K5) * (D_RU : K5) = (D_P : K5) ∧
      (5 : K5) * (D_RInf : K5) = (D_P : K5) ∧ (147 : K5) * (D_RQ5 : K5) = (D_P : K5) := by
    refine ⟨?_, ?_, ?_⟩
    · have hZ : (105 : ℤ) * D_RU = D_P := by unfold D_P D_RU; decide
      exact_mod_cast hZ
    · have hZ : (5 : ℤ) * D_RInf = D_P := by unfold D_P D_RInf; decide
      exact_mod_cast hZ
    · have hZ : (147 : ℤ) * D_RQ5 = D_P := by unfold D_P D_RQ5; decide
      exact_mod_cast hZ
  have hDP_ne : (D_P : K5) ≠ 0 := Int.cast_ne_zero.mpr (by unfold D_P; decide)
  have hL_ne : L_K ≠ 0 := by
    have hL : L_K = poly4ToK5 (77 * MvPolynomial.X 0 - 210 * MvPolynomial.X 1 + 45) := by
      simp only [map_add, map_sub, map_mul, map_ofNat]; rfl
    rw [hL]; apply poly4ToK5_ne_zero; intro h0
    have hv := congrArg (MvPolynomial.eval (0 : Fin 4 → ℂ)) h0
    simp only [map_add, map_sub, map_mul, map_ofNat, map_zero, MvPolynomial.eval_X, Pi.zero_apply, mul_zero, sub_zero, zero_add] at hv
    exact (by norm_num : (45 : ℂ) ≠ 0) hv
  rw [hL5, hP, hRU, hRInf, hRQ5] at hid
  simp only [ringEval, pow_zero, mul_one, Int.cast_ofNat] at hid
  have hfact : (D_P : K5) * (L_K ^ 2 * (toK5 P_horiz_5 + toK5_RU) + toK5_RInf + toK5_RQ5) = 0 := by
    linear_combination hid - L_K ^ 2 * toK5_RU * hD_rels.1 - toK5_RInf * hD_rels.2.1 - toK5_RQ5 * hD_rels.2.2
  have hsum0 : L_K ^ 2 * (toK5 P_horiz_5 + toK5_RU) + toK5_RInf + toK5_RQ5 = 0 :=
    (mul_eq_zero.mp hfact).resolve_left hDP_ne
  apply mul_left_cancel₀ (pow_ne_zero 2 hL_ne)
  field_simp [hL_ne]
  linear_combination hsum0

end SymmetricSexticResidual.LocalResidueQ5

theorem solution :
    SymmetricSexticResidual.K5Field.toK5 SymmetricSexticResidual.VerticalIdentity.P_horiz_5 =
      -SymmetricSexticResidual.LocalResidueU0.toK5_RInf /
          SymmetricSexticResidual.LocalResidueU0.L_K ^ 2 -
        SymmetricSexticResidual.LocalResidueU0.toK5_RU -
        SymmetricSexticResidual.LocalResidueU0.toK5_RQ5 /
          SymmetricSexticResidual.LocalResidueU0.L_K ^ 2 :=
  SymmetricSexticResidual.LocalResidueQ5.global_residue_cancellation
