-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_bridges
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T19:39:55.574099+00:00
-- url     : https://prove2.me/submissions/7dda0431-fce2-42ef-8c90-5716b1f817a6

import Definitions.Def_HodgeComputerSSR_SheetCalculus
import Definitions.Def_HodgeComputerSSR_LocalInfAlgDefs
import Definitions.Def_HodgeComputerSSR_LocalInfBiv
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_sheet_splits

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueInf
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.VerticalData SymmetricSexticResidual.VerticalIdentity
  SymmetricSexticResidual.LocalResidueU0 SymmetricSexticResidual.LocalResidueInfAlg
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

private abbrev br_10_eq := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.2.2.2.1
private abbrev br_00_eq := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.2.2.2.2.1
private abbrev br_11_eq := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.2.2.2.2.2.1
private abbrev om_10_eq := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.2.2.2.2.2.2.1
private abbrev om_00_eq := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.2.2.2.2.2.2.2.1
private abbrev om_11_eq := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits.2.2.2.2.2.2.2.2.2.2.1

private lemma ringEval_H0_7_inf : ringEval vK5 H0_int_e = 7 * H0_of S_K Q_K T_K := by
  rw [ringEval_vK5_H0_int_e]
  have hH0 : H0_K = H0_of S_K Q_K T_K := by
    have h := H0_of_L (L := K5)
    simpa only [SL, QL, TL, ιL, Algebra.algebraMap_self, RingHom.id_apply] using h.symm
  rw [hH0]

private lemma evalBivK5_DX2_inf : evalBivK5 DX2_biv = DX2_of S_K Q_K x_K := by
  simp only [evalBivK5, denote, DX2_biv, ringEval, eS, eQ, vK5, DX2_of, u3_of]; ring

private lemma evalBivK5_DY2_inf : evalBivK5 DY2_biv = DY2_of T_K y_K := by
  simp only [evalBivK5, denote, DY2_biv, ringEval, eT, vK5, DY2_of, v3_of]; ring

private lemma evalBivK5_W2_inf : evalBivK5 W2_biv = W2_of S_K Q_K T_K x_K y_K := by
  simp only [W2_biv, evalBivK5_bivMul, evalBivK5_scale, evalBivK5_DX2_inf, evalBivK5_DY2_inf, W2_of]
  simp only [ringEval, eS, eT, vK5, pow_zero, mul_one]

private lemma ringEval_dH0_7_inf (k : Fin 3) :
    ringEval vK5 (dH0_7_inf_e k) = 7 * dH0_fn k S_K Q_K T_K := by
  fin_cases k <;> (simp only [dH0_7_inf_e, ringEval, eS, eQ, eT, vK5, dH0_fn]; ring)

private lemma evalBivK5_dF5_7_inf (k : Fin 5) :
    evalBivK5 (dF5_7_inf_biv k) = 7 * dF5_fn k S_K Q_K T_K x_K y_K := by
  fin_cases k <;> (simp only [dF5_7_inf_biv, evalBivK5, denote, ringEval_dH0_7_inf, ringEval,
    eS, eT, vK5, dF5_fn, dH0_fn]; ring)

private lemma evalBivK5_dDX2_inf (k : Fin 5) :
    evalBivK5 (dDX2_inf_biv k) = dDX2_fn k S_K Q_K x_K := by
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, dDX2_inf_biv, evalBivK5, denote, ringEval, eS, eQ, vK5, dDX2_fn, u3_of]
  all_goals ring

private lemma evalBivK5_dDY2_inf (k : Fin 5) :
    evalBivK5 (dDY2_inf_biv k) = dDY2_fn k T_K y_K := by
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, dDY2_inf_biv, evalBivK5, denote, ringEval, eT, vK5, dDY2_fn, v3_of]
  all_goals ring

private lemma evalBivK5_br_10 (k : Fin 5) :
    evalBivK5 (br_10_243_biv k) = 243 * (br_fn k S_K Q_K T_K x_K y_K 1 0 - br_fn k S_K Q_K T_K x_K y_K 0 0) := by
  rw [br_10_eq]
  fin_cases k <;> (
    simp only [br_10_243_biv, evalBivK5_bscE]
    simp only [LX1_9_biv, LX1_27_biv, T59_e, T53_e, evalBivK5, denote, ringEval, eS, eQ, eT, vK5])
  all_goals ring

private lemma evalBivK5_br_00 (k : Fin 5) :
    evalBivK5 (br_00_243_biv k) = 243 * br_fn k S_K Q_K T_K x_K y_K 0 0 := by
  rw [br_00_eq]
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, br_00_243_biv, T59_e, T53_e, evalBivK5, denote, ringEval, eS, eQ, eT, vK5]
  all_goals ring

private lemma evalBivK5_br_11 (k : Fin 5) :
    evalBivK5 (br_11_243_biv k) = 243 * (br_fn k S_K Q_K T_K x_K y_K 1 1 - br_fn k S_K Q_K T_K x_K y_K 1 0 -
      br_fn k S_K Q_K T_K x_K y_K 0 1 + br_fn k S_K Q_K T_K x_K y_K 0 0) := by
  rw [br_11_eq]
  fin_cases k <;> (
    simp only [br_11_243_biv, evalBivK5_bscE, evalBivK5_bivMul]
    simp only [LX1_9_biv, LX1_27_biv, LY1_9_biv, LY1_27_biv, evalBivK5, denote, ringEval, eS, eQ, eT, vK5]; ring)

private lemma evalBivK5_om_10 (p q : Fin 5) :
    evalBivK5 (om_10_81_biv p q) = 81 * (om_fn p q S_K Q_K T_K x_K y_K 1 0 - om_fn p q S_K Q_K T_K x_K y_K 0 0) := by
  have h := om_10_eq p q S_K Q_K T_K x_K y_K
  simp only [Nat.cast_ofNat] at h
  rw [h]
  fin_cases p <;> fin_cases q <;> (
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, om_10_81_biv, om_10_raw, evalBivK5_bivSub, evalBivK5_bscE]
    simp only [LX1_9_biv, T53_e, evalBivK5, denote, ringEval, eS, eQ, eT, vK5])
  all_goals ring

private lemma evalBivK5_om_00 (p q : Fin 5) :
    evalBivK5 (om_00_81_biv p q) = 81 * om_fn p q S_K Q_K T_K x_K y_K 0 0 := by
  have h := om_00_eq p q S_K Q_K T_K x_K y_K
  simp only [Nat.cast_ofNat] at h
  rw [h]
  fin_cases p <;> fin_cases q <;> (
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, om_00_81_biv, om_00_raw, evalBivK5_bivSub]
    simp only [T53_e, evalBivK5, denote, ringEval, eS, eQ, eT, vK5])
  all_goals ring

private lemma evalBivK5_om_11 (p q : Fin 5) :
    evalBivK5 (om_11_81_biv p q) = 81 * (om_fn p q S_K Q_K T_K x_K y_K 1 1 - om_fn p q S_K Q_K T_K x_K y_K 1 0 -
      om_fn p q S_K Q_K T_K x_K y_K 0 1 + om_fn p q S_K Q_K T_K x_K y_K 0 0) := by
  have h := om_11_eq p q S_K Q_K T_K x_K y_K
  simp only [Nat.cast_ofNat] at h
  rw [h]
  fin_cases p <;> fin_cases q <;> (
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, om_11_81_biv, om_11_raw, evalBivK5_bivSub, evalBivK5_bscE, evalBivK5_bivMul]
    simp only [LX1_9_biv, LY1_9_biv, evalBivK5, denote, ringEval, eS, eQ, eT, vK5])
  all_goals ring

private lemma evalBivK5_F_c_inf (f2 : Fin 5 → Fin 5 → Biv) (g2 : Fin 5 → Fin 5 → K5)
    (hf : ∀ a b, evalBivK5 (f2 a b) = g2 a b) (i : Fin 3) :
    evalBivK5 (F_c_inf_biv f2 i) = 7 * F_contract S_K Q_K T_K x_K y_K g2 i := by
  fin_cases i <;> (simp only [F_c_inf_biv, F_contract,
    evalBivK5_bivAdd, evalBivK5_bivMul, evalBivK5_dF5_7_inf, hf]; ring)

private lemma evalBivK5_QY10 (i : Fin 3) :
    evalBivK5 (QY10_biv i) = 1701 * (QY_num S_K Q_K T_K x_K y_K 1 0 i - QY_num S_K Q_K T_K x_K y_K 0 0 i) := by
  simp only [QY10_biv, make_QY_biv, evalBivK5_bivMul, evalBivK5_bivSub, evalBivK5_bivScale,
    evalBivK5_DX2_inf, evalBivK5_DY2_inf]
  rw [evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (81 * (om_fn a b S_K Q_K T_K x_K y_K 1 0 - om_fn a b S_K Q_K T_K x_K y_K 0 0)))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_om_10]; simp only [ringEval, eS, eT, vK5]) i,
    evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (dDX2_fn a S_K Q_K x_K * (243 * (br_fn b S_K Q_K T_K x_K y_K 1 0 - br_fn b S_K Q_K T_K x_K y_K 0 0)) -
      dDX2_fn b S_K Q_K x_K * (243 * (br_fn a S_K Q_K T_K x_K y_K 1 0 - br_fn a S_K Q_K T_K x_K y_K 0 0))))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_bivSub, evalBivK5_bivMul, evalBivK5_bivMul,
      evalBivK5_dDX2_inf, evalBivK5_dDX2_inf, evalBivK5_br_10, evalBivK5_br_10]; simp only [ringEval, eS, eT, vK5]) i]
  simp only [QY_num, Omega_F, dDX2_F, F_contract]; push_cast; ring

private lemma evalBivK5_QX10 (i : Fin 3) :
    evalBivK5 (QX10_biv i) = 1701 * (QX_num S_K Q_K T_K x_K y_K 1 0 i - QX_num S_K Q_K T_K x_K y_K 0 0 i) := by
  simp only [QX10_biv, make_QX_biv, evalBivK5_bivMul, evalBivK5_bivAdd, evalBivK5_bivScale,
    evalBivK5_DX2_inf, evalBivK5_DY2_inf]
  rw [evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (81 * (om_fn a b S_K Q_K T_K x_K y_K 1 0 - om_fn a b S_K Q_K T_K x_K y_K 0 0)))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_om_10]; simp only [ringEval, eS, eT, vK5]) i,
    evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (dDY2_fn a T_K y_K * (243 * (br_fn b S_K Q_K T_K x_K y_K 1 0 - br_fn b S_K Q_K T_K x_K y_K 0 0)) -
      dDY2_fn b T_K y_K * (243 * (br_fn a S_K Q_K T_K x_K y_K 1 0 - br_fn a S_K Q_K T_K x_K y_K 0 0))))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_bivSub, evalBivK5_bivMul, evalBivK5_bivMul,
      evalBivK5_dDY2_inf, evalBivK5_dDY2_inf, evalBivK5_br_10, evalBivK5_br_10]; simp only [ringEval, eS, eT, vK5]) i]
  simp only [QX_num, Omega_F, dDY2_F, F_contract]; push_cast; ring

private lemma evalBivK5_QY00 (i : Fin 3) :
    evalBivK5 (QY00_biv i) = 1701 * QY_num S_K Q_K T_K x_K y_K 0 0 i := by
  simp only [QY00_biv, make_QY_biv, evalBivK5_bivMul, evalBivK5_bivSub, evalBivK5_bivScale,
    evalBivK5_DX2_inf, evalBivK5_DY2_inf]
  rw [evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (81 * om_fn a b S_K Q_K T_K x_K y_K 0 0))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_om_00]; simp only [ringEval, eS, eT, vK5]) i,
    evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (dDX2_fn a S_K Q_K x_K * (243 * br_fn b S_K Q_K T_K x_K y_K 0 0) -
      dDX2_fn b S_K Q_K x_K * (243 * br_fn a S_K Q_K T_K x_K y_K 0 0)))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_bivSub, evalBivK5_bivMul, evalBivK5_bivMul,
      evalBivK5_dDX2_inf, evalBivK5_dDX2_inf, evalBivK5_br_00, evalBivK5_br_00]; simp only [ringEval, eS, eT, vK5]) i]
  simp only [QY_num, Omega_F, dDX2_F, F_contract]; push_cast; ring

private lemma evalBivK5_QX00 (i : Fin 3) :
    evalBivK5 (QX00_biv i) = 1701 * QX_num S_K Q_K T_K x_K y_K 0 0 i := by
  simp only [QX00_biv, make_QX_biv, evalBivK5_bivMul, evalBivK5_bivAdd, evalBivK5_bivScale,
    evalBivK5_DX2_inf, evalBivK5_DY2_inf]
  rw [evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (81 * om_fn a b S_K Q_K T_K x_K y_K 0 0))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_om_00]; simp only [ringEval, eS, eT, vK5]) i,
    evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (dDY2_fn a T_K y_K * (243 * br_fn b S_K Q_K T_K x_K y_K 0 0) -
      dDY2_fn b T_K y_K * (243 * br_fn a S_K Q_K T_K x_K y_K 0 0)))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_bivSub, evalBivK5_bivMul, evalBivK5_bivMul,
      evalBivK5_dDY2_inf, evalBivK5_dDY2_inf, evalBivK5_br_00, evalBivK5_br_00]; simp only [ringEval, eS, eT, vK5]) i]
  simp only [QX_num, Omega_F, dDY2_F, F_contract]; push_cast; ring

private lemma evalBivK5_QY11 (i : Fin 3) :
    evalBivK5 (QY11_biv i) = 1701 * (QY_num S_K Q_K T_K x_K y_K 1 1 i - QY_num S_K Q_K T_K x_K y_K 1 0 i -
      QY_num S_K Q_K T_K x_K y_K 0 1 i + QY_num S_K Q_K T_K x_K y_K 0 0 i) := by
  simp only [QY11_biv, make_QY_biv, evalBivK5_bivMul, evalBivK5_bivSub, evalBivK5_bivScale,
    evalBivK5_DX2_inf, evalBivK5_DY2_inf]
  rw [evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (81 * (om_fn a b S_K Q_K T_K x_K y_K 1 1 - om_fn a b S_K Q_K T_K x_K y_K 1 0 -
      om_fn a b S_K Q_K T_K x_K y_K 0 1 + om_fn a b S_K Q_K T_K x_K y_K 0 0)))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_om_11]; simp only [ringEval, eS, eT, vK5]) i,
    evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (dDX2_fn a S_K Q_K x_K * (243 * (br_fn b S_K Q_K T_K x_K y_K 1 1 - br_fn b S_K Q_K T_K x_K y_K 1 0 -
        br_fn b S_K Q_K T_K x_K y_K 0 1 + br_fn b S_K Q_K T_K x_K y_K 0 0)) -
      dDX2_fn b S_K Q_K x_K * (243 * (br_fn a S_K Q_K T_K x_K y_K 1 1 - br_fn a S_K Q_K T_K x_K y_K 1 0 -
        br_fn a S_K Q_K T_K x_K y_K 0 1 + br_fn a S_K Q_K T_K x_K y_K 0 0))))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_bivSub, evalBivK5_bivMul, evalBivK5_bivMul,
      evalBivK5_dDX2_inf, evalBivK5_dDX2_inf, evalBivK5_br_11, evalBivK5_br_11]; simp only [ringEval, eS, eT, vK5]) i]
  simp only [QY_num, Omega_F, dDX2_F, F_contract]; push_cast; ring

private lemma evalBivK5_QX11 (i : Fin 3) :
    evalBivK5 (QX11_biv i) = 1701 * (QX_num S_K Q_K T_K x_K y_K 1 1 i - QX_num S_K Q_K T_K x_K y_K 1 0 i -
      QX_num S_K Q_K T_K x_K y_K 0 1 i + QX_num S_K Q_K T_K x_K y_K 0 0 i) := by
  simp only [QX11_biv, make_QX_biv, evalBivK5_bivMul, evalBivK5_bivAdd, evalBivK5_bivScale,
    evalBivK5_DX2_inf, evalBivK5_DY2_inf]
  rw [evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (81 * (om_fn a b S_K Q_K T_K x_K y_K 1 1 - om_fn a b S_K Q_K T_K x_K y_K 1 0 -
      om_fn a b S_K Q_K T_K x_K y_K 0 1 + om_fn a b S_K Q_K T_K x_K y_K 0 0)))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_om_11]; simp only [ringEval, eS, eT, vK5]) i,
    evalBivK5_F_c_inf _ (fun a b => S_K * T_K * (dDY2_fn a T_K y_K * (243 * (br_fn b S_K Q_K T_K x_K y_K 1 1 - br_fn b S_K Q_K T_K x_K y_K 1 0 -
        br_fn b S_K Q_K T_K x_K y_K 0 1 + br_fn b S_K Q_K T_K x_K y_K 0 0)) -
      dDY2_fn b T_K y_K * (243 * (br_fn a S_K Q_K T_K x_K y_K 1 1 - br_fn a S_K Q_K T_K x_K y_K 1 0 -
        br_fn a S_K Q_K T_K x_K y_K 0 1 + br_fn a S_K Q_K T_K x_K y_K 0 0))))
    (fun a b => by rw [evalBivK5_bscE, evalBivK5_bivSub, evalBivK5_bivMul, evalBivK5_bivMul,
      evalBivK5_dDY2_inf, evalBivK5_dDY2_inf, evalBivK5_br_11, evalBivK5_br_11]; simp only [ringEval, eS, eT, vK5]) i]
  simp only [QX_num, Omega_F, dDY2_F, F_contract]; push_cast; ring

private lemma evalBivK5_EB10 :
    evalBivK5 EB10_biv = 243 * (EB_of S_K Q_K T_K x_K y_K 1 0 - EB_of S_K Q_K T_K x_K y_K 0 0) := by
  have h1 : evalBivK5 (scale eT 0 1 (br_10_243_biv 3)) =
      T_K * y_K * evalBivK5 (br_10_243_biv 3) := by
    simpa only [pow_zero, pow_one, mul_one, ringEval, eT, vK5] using evalBivK5_scale eT 0 1 (br_10_243_biv 3)
  have h2 : evalBivK5 (scale eS 1 0 (br_10_243_biv 4)) =
      S_K * x_K * evalBivK5 (br_10_243_biv 4) := by
    simpa only [pow_zero, pow_one, mul_one, ringEval, eS, vK5] using evalBivK5_scale eS 1 0 (br_10_243_biv 4)
  simp only [EB10_biv, evalBivK5_bivScale, evalBivK5_bivMul, evalBivK5_bivSub, evalBivK5_W2_inf, h1, h2,
    evalBivK5_br_10, EB_of, dF5_fn]; push_cast; ring

private lemma evalBivK5_EB11 :
    evalBivK5 EB11_biv = 243 * (EB_of S_K Q_K T_K x_K y_K 1 1 - EB_of S_K Q_K T_K x_K y_K 1 0 -
      EB_of S_K Q_K T_K x_K y_K 0 1 + EB_of S_K Q_K T_K x_K y_K 0 0) := by
  have h1 : evalBivK5 (scale eT 0 1 (br_11_243_biv 3)) =
      T_K * y_K * evalBivK5 (br_11_243_biv 3) := by
    simpa only [pow_zero, pow_one, mul_one, ringEval, eT, vK5] using evalBivK5_scale eT 0 1 (br_11_243_biv 3)
  have h2 : evalBivK5 (scale eS 1 0 (br_11_243_biv 4)) =
      S_K * x_K * evalBivK5 (br_11_243_biv 4) := by
    simpa only [pow_zero, pow_one, mul_one, ringEval, eS, vK5] using evalBivK5_scale eS 1 0 (br_11_243_biv 4)
  simp only [EB11_biv, evalBivK5_bivScale, evalBivK5_bivMul, evalBivK5_bivSub, evalBivK5_W2_inf, h1, h2,
    evalBivK5_br_11, EB_of, dF5_fn]; push_cast; ring

private lemma ringEval_P44_e : ringEval vK5 P44_e = P44_fn S_K Q_K T_K := by
  simp only [P44_e, P44_fn, ringEval, eS, eQ, eT, vK5]; ring

private lemma ringEval_M01_q_e : ringEval vK5 M01_q_e = M01_q_fn S_K Q_K T_K := by
  simp only [M01_q_e, M01_q_fn, ringEval, eS, eQ, eT, vK5]; ring

private lemma ringEval_A32_2_q_e : ringEval vK5 A32_2_q_e = A32_2_q_fn S_K Q_K T_K := by
  simp only [A32_2_q_e, A32_2_q_fn, ringEval, eS, eQ, eT, vK5]; ring

private lemma ringEval_A32_1_q_e : ringEval vK5 A32_1_q_e = A32_1_q_fn S_K Q_K T_K := by
  simp only [A32_1_q_e, A32_1_q_fn, ringEval, eS, eQ, eT, vK5]; ring

-- `interp4_p4_mul` & `interp4_add_p4`:

end SymmetricSexticResidual.LocalResidueInf

theorem solution :
    (PolynomialEncoding.SignedExpressions.ringEval
        SymmetricSexticResidual.LocalResidueU0.vK5
        SymmetricSexticResidual.VerticalIdentity.H0_int_e =
      7 * SymmetricSexticResidual.SheetCalculus.H0_of
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K) ∧
    (∀ k : Fin 3,
      PolynomialEncoding.SignedExpressions.ringEval
        SymmetricSexticResidual.LocalResidueU0.vK5
        (SymmetricSexticResidual.LocalResidueInf.dH0_7_inf_e k) =
      7 * SymmetricSexticResidual.SheetCalculus.dH0_fn k
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K) ∧
    (∀ i : Fin 3,
      SymmetricSexticResidual.LocalResidueU0.evalBivK5
        (SymmetricSexticResidual.LocalResidueInf.QY10_biv i) =
      1701 * (SymmetricSexticResidual.SheetCalculus.QY_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 0 i -
        SymmetricSexticResidual.SheetCalculus.QY_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 0 i)) ∧
    (∀ i : Fin 3,
      SymmetricSexticResidual.LocalResidueU0.evalBivK5
        (SymmetricSexticResidual.LocalResidueInf.QX10_biv i) =
      1701 * (SymmetricSexticResidual.SheetCalculus.QX_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 0 i -
        SymmetricSexticResidual.SheetCalculus.QX_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 0 i)) ∧
    (∀ i : Fin 3,
      SymmetricSexticResidual.LocalResidueU0.evalBivK5
        (SymmetricSexticResidual.LocalResidueInf.QY00_biv i) =
      1701 * SymmetricSexticResidual.SheetCalculus.QY_num
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
        SymmetricSexticResidual.K5Field.y_K 0 0 i) ∧
    (∀ i : Fin 3,
      SymmetricSexticResidual.LocalResidueU0.evalBivK5
        (SymmetricSexticResidual.LocalResidueInf.QX00_biv i) =
      1701 * SymmetricSexticResidual.SheetCalculus.QX_num
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
        SymmetricSexticResidual.K5Field.y_K 0 0 i) ∧
    (∀ i : Fin 3,
      SymmetricSexticResidual.LocalResidueU0.evalBivK5
        (SymmetricSexticResidual.LocalResidueInf.QY11_biv i) =
      1701 * (SymmetricSexticResidual.SheetCalculus.QY_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 1 i -
        SymmetricSexticResidual.SheetCalculus.QY_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 0 i -
        SymmetricSexticResidual.SheetCalculus.QY_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 1 i +
        SymmetricSexticResidual.SheetCalculus.QY_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 0 i)) ∧
    (∀ i : Fin 3,
      SymmetricSexticResidual.LocalResidueU0.evalBivK5
        (SymmetricSexticResidual.LocalResidueInf.QX11_biv i) =
      1701 * (SymmetricSexticResidual.SheetCalculus.QX_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 1 i -
        SymmetricSexticResidual.SheetCalculus.QX_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 0 i -
        SymmetricSexticResidual.SheetCalculus.QX_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 1 i +
        SymmetricSexticResidual.SheetCalculus.QX_num
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 0 i)) ∧
    (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.EB10_biv =
      243 * (SymmetricSexticResidual.SheetCalculus.EB_of
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 0 -
        SymmetricSexticResidual.SheetCalculus.EB_of
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 0)) ∧
    (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.EB11_biv =
      243 * (SymmetricSexticResidual.SheetCalculus.EB_of
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 1 -
        SymmetricSexticResidual.SheetCalculus.EB_of
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 1 0 -
        SymmetricSexticResidual.SheetCalculus.EB_of
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 1 +
        SymmetricSexticResidual.SheetCalculus.EB_of
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
          SymmetricSexticResidual.K5Field.y_K 0 0)) ∧
    (PolynomialEncoding.SignedExpressions.ringEval
        SymmetricSexticResidual.LocalResidueU0.vK5 SymmetricSexticResidual.LocalResidueInf.P44_e =
      SymmetricSexticResidual.LocalResidueInfAlg.P44_fn
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K) ∧
    (PolynomialEncoding.SignedExpressions.ringEval
        SymmetricSexticResidual.LocalResidueU0.vK5 SymmetricSexticResidual.LocalResidueInf.M01_q_e =
      SymmetricSexticResidual.LocalResidueInfAlg.M01_q_fn
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K) ∧
    (PolynomialEncoding.SignedExpressions.ringEval
        SymmetricSexticResidual.LocalResidueU0.vK5 SymmetricSexticResidual.LocalResidueInf.A32_2_q_e =
      SymmetricSexticResidual.LocalResidueInfAlg.A32_2_q_fn
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K) ∧
    (PolynomialEncoding.SignedExpressions.ringEval
        SymmetricSexticResidual.LocalResidueU0.vK5 SymmetricSexticResidual.LocalResidueInf.A32_1_q_e =
      SymmetricSexticResidual.LocalResidueInfAlg.A32_1_q_fn
        SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
        SymmetricSexticResidual.K5Field.T_K) :=
  ⟨SymmetricSexticResidual.LocalResidueInf.ringEval_H0_7_inf,
   SymmetricSexticResidual.LocalResidueInf.ringEval_dH0_7_inf,
   SymmetricSexticResidual.LocalResidueInf.evalBivK5_QY10,
   SymmetricSexticResidual.LocalResidueInf.evalBivK5_QX10,
   SymmetricSexticResidual.LocalResidueInf.evalBivK5_QY00,
   SymmetricSexticResidual.LocalResidueInf.evalBivK5_QX00,
   SymmetricSexticResidual.LocalResidueInf.evalBivK5_QY11,
   SymmetricSexticResidual.LocalResidueInf.evalBivK5_QX11,
   SymmetricSexticResidual.LocalResidueInf.evalBivK5_EB10,
   SymmetricSexticResidual.LocalResidueInf.evalBivK5_EB11,
   SymmetricSexticResidual.LocalResidueInf.ringEval_P44_e,
   SymmetricSexticResidual.LocalResidueInf.ringEval_M01_q_e,
   SymmetricSexticResidual.LocalResidueInf.ringEval_A32_2_q_e,
   SymmetricSexticResidual.LocalResidueInf.ringEval_A32_1_q_e⟩
