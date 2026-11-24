-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_BTot_dot_W
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:46:20.558392+00:00
-- url     : https://prove2.me/submissions/9c319d88-c884-44b7-9682-c8cd0ec8c287

import Definitions.Def_HodgeComputerSSR_Q5K5Master
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_cache_rel

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.Q5WeightsData
  SymmetricSexticResidual.LocalResidueData SymmetricSexticResidual.LocalResidueU0
  PolynomialEncoding.KroneckerCheck Polynomial
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len
open scoped BigOperators

private abbrev evalACache_rel := @HodgeComputer.SymmetricSexticResidual.Proof.localQ5_cache_rel.1
private abbrev evalGeomSQ_rel := @HodgeComputer.SymmetricSexticResidual.Proof.localQ5_cache_rel.2.1
private abbrev evalGeomT_rel := @HodgeComputer.SymmetricSexticResidual.Proof.localQ5_cache_rel.2.2.2.1

lemma fac_4_eq_neg_L : evalSQ_K5 fac_4 = -L_K := by
  simp only [fac_4, evalSQ_K5, ringEval, vK5_SQ, L_K, Int.cast_neg, Int.cast_ofNat]; ring

-- Exact identification of `k5Params.Q5_z` and `k5Params.Q7_z` with `Q5WeightsData.Q5_c`, `Q7_c`!
lemma dq_pow_chain_eq (f0 f1 f2 f3 f4 f5 f6 : K5) :
    let f2_2 := f2 * f2; let f2_4 := f2_2 * f2_2; let f2_6 := f2_4 * f2_2; let f2_7 := f2_6 * f2
    let f3_3 := f3 * f3 * f3; let f3_6 := f3_3 * f3_3; let f3_9 := f3_6 * f3_3
    let f3_12 := f3_9 * f3_3; let f3_13 := f3_12 * f3
    let f4_2 := f4 * f4
    (f3_13 * f4_2 = f3 ^ 13 * f4 ^ 2) ∧
    (f1 * f2_2 * f3_13 * f4_2 = f1 * f2 ^ 2 * f3 ^ 13 * f4 ^ 2) ∧
    (f1 * f2_4 * f3_13 * f4_2 = f1 * f2 ^ 4 * f3 ^ 13 * f4 ^ 2) ∧
    (f1 * f2_6 * f3_13 * f4_2 = f1 * f2 ^ 6 * f3 ^ 13 * f4 ^ 2) ∧
    (f1 * f2_7 * f3_13 * f4_2 = f1 * f2 ^ 7 * f3 ^ 13 * f4 ^ 2) ∧
    (f1 * f2_7 * f3_12 * f4_2 = f1 * f2 ^ 7 * f3 ^ 12 * f4 ^ 2) ∧
    (f1 * f2_7 * f3_9 * f4_2 = f1 * f2 ^ 7 * f3 ^ 9 * f4 ^ 2) ∧
    (f1 * f2_7 * f3_6 * f4_2 = f1 * f2 ^ 7 * f3 ^ 6 * f4 ^ 2) ∧
    (f1 * f2_7 * f3_3 * f4 = f1 * f2 ^ 7 * f3 ^ 3 * f4) ∧
    (f1 * f2_7 = f1 * f2 ^ 7) ∧
    (f0 * f1 * f2_7 * f3_9 * f4 * f5 ^ 4 * f6 = f0 * f1 * f2 ^ 7 * f3 ^ 9 * f4 * f5 ^ 4 * f6) ∧
    (f0 * f1 * f2_7 * f3_13 * f5 ^ 4 * f6 * f4 ^ 2 = f0 * f1 * f2 ^ 7 * f3 ^ 13 * f4 ^ 2 * f5 ^ 4 * f6) := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩

lemma fac_K5_eqs :
    Q_K = evalSQ_K5 fac_0 ∧ S_K = evalSQ_K5 fac_1 ∧
    (-5 : K5) * S_K + 9 * Q_K = evalSQ_K5 fac_2 ∧
    -S_K + 3 * Q_K = evalSQ_K5 fac_3 ∧
    -45 + (-77 : K5) * S_K + 210 * Q_K = evalSQ_K5 fac_4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [fac_0, fac_1, fac_2, fac_3, fac_4, evalSQ_K5, ringEval, vK5_SQ, Int.cast_neg, Int.cast_ofNat]
  all_goals ring


lemma cacheK_props :
    cacheK.ac = evalACache k5Ops S_K Q_K ∧
    cacheK.gsq = evalGeomSQ k5Ops S_K Q_K ∧
    cacheK.W =
      [evalSQ_K5 (W_num_expr 0), evalSQ_K5 (W_num_expr 1), evalSQ_K5 (W_num_expr 2),
       evalSQ_K5 (W_num_expr 3), evalSQ_K5 (W_num_expr 4), evalSQ_K5 (W_num_expr 5),
       evalSQ_K5 (W_num_expr 6), evalSQ_K5 (W_num_expr 7), evalSQ_K5 (W_num_expr 8),
       evalSQ_K5 (W_num_expr 9), evalSQ_K5 (W_num_expr 10), evalSQ_K5 (W_num_expr 11),
       evalSQ_K5 (W_num_expr 12)] ∧
    evalSQ_K5 D_all_expr = cacheK.D_div_L2 * L_K ^ 2 ∧
    evalBivLK5 (cacheK.RQ5_T.map fun row => row.map fun p => uEval k5Ops p T_K) = evalBivK5 RQ5_biv ∧
    (cacheK.d_A0U_t0 = dotW k5Ops (uTail cacheK.ac.A0U_t0) cacheK.W 1 ∧
     cacheK.d_A0U_t1 = dotW k5Ops (uTail cacheK.ac.A0U_t1) cacheK.W 1 ∧
     cacheK.d_A0V_t0 = dotW k5Ops cacheK.ac.A0V_t0 cacheK.W 0 ∧
     cacheK.d_A0V_t1 = dotW k5Ops cacheK.ac.A0V_t1 cacheK.W 0 ∧
     cacheK.d_A0V_t2 = dotW k5Ops cacheK.ac.A0V_t2 cacheK.W 0 ∧
     cacheK.d_A0V_U_t0 = dotW k5Ops cacheK.ac.A0V_t0 cacheK.W 1 ∧
     cacheK.d_A0V_U_t1 = dotW k5Ops cacheK.ac.A0V_t1 cacheK.W 1 ∧
     cacheK.d_A0V_U_t2 = dotW k5Ops cacheK.ac.A0V_t2 cacheK.W 1 ∧
     cacheK.d_A0VBv_t0 = dotW k5Ops (uMul k5Ops cacheK.ac.A0V_t0 cacheK.ac.Bv_SQ) cacheK.W 0 ∧
     cacheK.d_A0VBv_t1 = dotW k5Ops (uMul k5Ops cacheK.ac.A0V_t1 cacheK.ac.Bv_SQ) cacheK.W 0 ∧
     cacheK.d_A0VBv_t2 = dotW k5Ops (uMul k5Ops cacheK.ac.A0V_t2 cacheK.ac.Bv_SQ) cacheK.W 0 ∧
     cacheK.d_AY2_t0 = dotW k5Ops cacheK.ac.AY2_t0 cacheK.W 0 ∧
     cacheK.d_AY2_t1 = dotW k5Ops cacheK.ac.AY2_t1 cacheK.W 0 ∧
     cacheK.d_AY3_t0 = dotW k5Ops cacheK.ac.AY3_t0 cacheK.W 1 ∧
     cacheK.d_AY3_t1 = dotW k5Ops cacheK.ac.AY3_t1 cacheK.W 1 ∧
     cacheK.d_AX2_t0 = dotW k5Ops cacheK.ac.AX2_t0 cacheK.W 0 ∧
     cacheK.d_AX2_t1 = dotW k5Ops cacheK.ac.AX2_t1 cacheK.W 0 ∧
     cacheK.d_AX2_t2 = dotW k5Ops cacheK.ac.AX2_t2 cacheK.W 0) := by
  let P : SQCache K5 → Prop := fun c =>
    c.ac = evalACache k5Ops S_K Q_K ∧
    c.gsq = evalGeomSQ k5Ops S_K Q_K ∧
    c.W =
      [evalSQ_K5 (W_num_expr 0), evalSQ_K5 (W_num_expr 1), evalSQ_K5 (W_num_expr 2),
       evalSQ_K5 (W_num_expr 3), evalSQ_K5 (W_num_expr 4), evalSQ_K5 (W_num_expr 5),
       evalSQ_K5 (W_num_expr 6), evalSQ_K5 (W_num_expr 7), evalSQ_K5 (W_num_expr 8),
       evalSQ_K5 (W_num_expr 9), evalSQ_K5 (W_num_expr 10), evalSQ_K5 (W_num_expr 11),
       evalSQ_K5 (W_num_expr 12)] ∧
    evalSQ_K5 D_all_expr = c.D_div_L2 * L_K ^ 2 ∧
    evalBivLK5 (c.RQ5_T.map fun row => row.map fun p => uEval k5Ops p T_K) = evalBivK5 RQ5_biv ∧
    (c.d_A0U_t0 = dotW k5Ops (uTail c.ac.A0U_t0) c.W 1 ∧
     c.d_A0U_t1 = dotW k5Ops (uTail c.ac.A0U_t1) c.W 1 ∧
     c.d_A0V_t0 = dotW k5Ops c.ac.A0V_t0 c.W 0 ∧
     c.d_A0V_t1 = dotW k5Ops c.ac.A0V_t1 c.W 0 ∧
     c.d_A0V_t2 = dotW k5Ops c.ac.A0V_t2 c.W 0 ∧
     c.d_A0V_U_t0 = dotW k5Ops c.ac.A0V_t0 c.W 1 ∧
     c.d_A0V_U_t1 = dotW k5Ops c.ac.A0V_t1 c.W 1 ∧
     c.d_A0V_U_t2 = dotW k5Ops c.ac.A0V_t2 c.W 1 ∧
     c.d_A0VBv_t0 = dotW k5Ops (uMul k5Ops c.ac.A0V_t0 c.ac.Bv_SQ) c.W 0 ∧
     c.d_A0VBv_t1 = dotW k5Ops (uMul k5Ops c.ac.A0V_t1 c.ac.Bv_SQ) c.W 0 ∧
     c.d_A0VBv_t2 = dotW k5Ops (uMul k5Ops c.ac.A0V_t2 c.ac.Bv_SQ) c.W 0 ∧
     c.d_AY2_t0 = dotW k5Ops c.ac.AY2_t0 c.W 0 ∧
     c.d_AY2_t1 = dotW k5Ops c.ac.AY2_t1 c.W 0 ∧
     c.d_AY3_t0 = dotW k5Ops c.ac.AY3_t0 c.W 1 ∧
     c.d_AY3_t1 = dotW k5Ops c.ac.AY3_t1 c.W 1 ∧
     c.d_AX2_t0 = dotW k5Ops c.ac.AX2_t0 c.W 0 ∧
     c.d_AX2_t1 = dotW k5Ops c.ac.AX2_t1 c.W 0 ∧
     c.d_AX2_t2 = dotW k5Ops c.ac.AX2_t2 c.W 0)
  suffices h : P (evalSQCache k5Ops S_K Q_K) from h
  unfold evalSQCache
  refine letB_intro fun pS hpS => letB_intro fun pQ hpQ =>
    letB_intro fun f2 hf2 => letB_intro fun f3 hf3 => letB_intro fun f4 hf4 =>
    letB_intro fun f2_2 hf2_2 => letB_intro fun f2_4 hf2_4 => letB_intro fun f2_6 hf2_6 => letB_intro fun f2_7 hf2_7 =>
    letB_intro fun f3_3 hf3_3 => letB_intro fun f3_6 hf3_6 => letB_intro fun f3_9 hf3_9 =>
    letB_intro fun f3_12 hf3_12 => letB_intro fun f3_13 hf3_13 => letB_intro fun f4_2 hf4_2 =>
    letB_intro fun d0 hd0 => letB_intro fun d1 hd1 => letB_intro fun d2 hd2 => letB_intro fun d3 hd3 =>
    letB_intro fun d4 hd4 => letB_intro fun d8 hd8 => letB_intro fun d9 hd9 => letB_intro fun d10 hd10 =>
    letB_intro fun d11 hd11 => letB_intro fun d12 hd12 => letB_intro fun W hW =>
    letB_intro fun D_div_L2 hDdiv => letB_intro fun ac hac => letB_intro fun gsq hgsq => ?_
  dsimp only [P]
  have hX0 : evalP3K5 (MvPolynomial.X 0) = S_K := by simp [evalP3K5, v3K5]
  have hX1 : evalP3K5 (MvPolynomial.X 1) = Q_K := by simp [evalP3K5, v3K5]
  have hX2 : evalP3K5 (MvPolynomial.X 2) = T_K := by simp [evalP3K5, v3K5]
  have hev2 (e : Expr) : evalExpr2 k5Ops S_K Q_K pS pQ e = evalSQ_K5 e := by
    rw [hpS, hpQ]
    have h := evalExpr2_rel poly3ToK5Rel hX0 hX1
      (powList_rel poly3ToK5Rel hX0 30 (poly3ToK5Rel.rel_ofInt 1))
      (powList_rel poly3ToK5Rel hX1 37 (poly3ToK5Rel.rel_ofInt 1)) e
    rw [evalExpr2_poly3_eq, evalP3K5_ringEval_SQ] at h; exact h.symm
  have hevT (e : Expr) : uEval k5Ops (evalExpr3PolyT k5Ops S_K Q_K pS pQ e) T_K = ringEval vK5 e := by
    rw [hpS, hpQ]
    have h := uEval_rel poly3ToK5Rel hX2
      (evalExpr3PolyT_rel poly3ToK5Rel hX0 hX1
        (powList_rel poly3ToK5Rel hX0 30 (poly3ToK5Rel.rel_ofInt 1))
        (powList_rel poly3ToK5Rel hX1 37 (poly3ToK5Rel.rel_ofInt 1)) e)
    rw [uEval_evalExpr3PolyT_P3Z, evalP3K5_ringEval_SQT] at h; exact h.symm
  have hf := fac_K5_eqs
  have hf2' : f2 = evalSQ_K5 fac_2 := by rw [hf2]; dsimp only [k5Ops, ringOps]; rw [← hf.2.2.1]; push_cast; ring
  have hf3' : f3 = evalSQ_K5 fac_3 := by rw [hf3]; dsimp only [k5Ops, ringOps]; rw [← hf.2.2.2.1]; push_cast; ring
  have hf4' : f4 = evalSQ_K5 fac_4 := by rw [hf4]; dsimp only [k5Ops, ringOps]; rw [← hf.2.2.2.2]; push_cast; ring
  have hf2_2' : f2_2 = evalSQ_K5 fac_2 ^ 2 := by rw [hf2_2, hf2']; dsimp only [k5Ops, ringOps]; ring
  have hf2_4' : f2_4 = evalSQ_K5 fac_2 ^ 4 := by rw [hf2_4, hf2_2']; dsimp only [k5Ops, ringOps]; ring
  have hf2_6' : f2_6 = evalSQ_K5 fac_2 ^ 6 := by rw [hf2_6, hf2_4', hf2_2']; dsimp only [k5Ops, ringOps]; ring
  have hf2_7' : f2_7 = evalSQ_K5 fac_2 ^ 7 := by rw [hf2_7, hf2_6', hf2']; dsimp only [k5Ops, ringOps]; ring
  have hf3_3' : f3_3 = evalSQ_K5 fac_3 ^ 3 := by rw [hf3_3, hf3']; dsimp only [k5Ops, ringOps]; ring
  have hf3_6' : f3_6 = evalSQ_K5 fac_3 ^ 6 := by rw [hf3_6, hf3_3']; dsimp only [k5Ops, ringOps]; ring
  have hf3_9' : f3_9 = evalSQ_K5 fac_3 ^ 9 := by rw [hf3_9, hf3_6', hf3_3']; dsimp only [k5Ops, ringOps]; ring
  have hf3_12' : f3_12 = evalSQ_K5 fac_3 ^ 12 := by rw [hf3_12, hf3_9', hf3_3']; dsimp only [k5Ops, ringOps]; ring
  have hf3_13' : f3_13 = evalSQ_K5 fac_3 ^ 13 := by rw [hf3_13, hf3_12', hf3']; dsimp only [k5Ops, ringOps]; ring
  have hf4_2' : f4_2 = evalSQ_K5 fac_4 ^ 2 := by rw [hf4_2, hf4']; dsimp only [k5Ops, ringOps]; ring
  have hS1 : S_K = evalSQ_K5 fac_1 := hf.2.1
  have hQ0 : Q_K = evalSQ_K5 fac_0 := hf.1
  have hd0' : d0 = evalSQ_K5 (D_quot_expr 0) := by rw [hd0, hf3_13', hf4_2']; rfl
  have hd1' : d1 = evalSQ_K5 (D_quot_expr 1) := by rw [hd1, hf2_2', hf3_13', hf4_2', hS1]; rfl
  have hd2' : d2 = evalSQ_K5 (D_quot_expr 2) := by rw [hd2, hf2_4', hf3_13', hf4_2', hS1]; rfl
  have hd3' : d3 = evalSQ_K5 (D_quot_expr 3) := by rw [hd3, hf2_6', hf3_13', hf4_2', hS1]; rfl
  have hd4' : d4 = evalSQ_K5 (D_quot_expr 4) := by rw [hd4, hf2_7', hf3_13', hf4_2', hS1]; rfl
  have hd8' : d8 = evalSQ_K5 (D_quot_expr 8) := by rw [hd8, hf2_7', hf3_12', hf4_2', hS1]; rfl
  have hd9' : d9 = evalSQ_K5 (D_quot_expr 9) := by rw [hd9, hf2_7', hf3_9', hf4_2', hS1]; rfl
  have hd10' : d10 = evalSQ_K5 (D_quot_expr 10) := by rw [hd10, hf2_7', hf3_6', hf4_2', hS1]; rfl
  have hd11' : d11 = evalSQ_K5 (D_quot_expr 11) := by rw [hd11, hf2_7', hf3_3', hf4', hS1]; rfl
  have hd12' : d12 = evalSQ_K5 (D_quot_expr 12) := by rw [hd12, hf2_7', hS1]; rfl
  refine ⟨hac, hgsq, ?_, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · rw [hW]; simp only [hev2, hd0', hd1', hd2', hd3', hd4', hd8', hd9', hd10', hd11', hd12']; rfl
  · have hL2 : L_K ^ 2 = evalSQ_K5 fac_4 ^ 2 := by rw [fac_4_eq_neg_L, neg_sq]
    have hDall : evalSQ_K5 D_all_expr =
        evalSQ_K5 fac_0 * evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 13 *
        evalSQ_K5 fac_4 ^ 2 * evalSQ_K5 fac_5 ^ 4 * evalSQ_K5 fac_6 := rfl
    rw [hDall, hL2, hDdiv, hev2, hev2, hf2_7', hf3_13', hS1, hQ0]; dsimp only [k5Ops, ringOps]; ring
  · simp only [List.map_cons, List.map_nil, hevT, evalBivLK5, evalBivL, evalYList, evalBivK5, RQ5_biv, denote]; ring


lemma acUnit_lens :
    (uTail acUnit.A0U_t0).length ≤ 9 ∧ (uTail acUnit.A0U_t1).length ≤ 9 ∧
    acUnit.A0V_t0.length ≤ 10 ∧ acUnit.A0V_t1.length ≤ 10 ∧ acUnit.A0V_t2.length ≤ 10 ∧
    (uMul uOps acUnit.A0V_t0 acUnit.Bv_SQ).length ≤ 12 ∧
    (uMul uOps acUnit.A0V_t1 acUnit.Bv_SQ).length ≤ 12 ∧
    (uMul uOps acUnit.A0V_t2 acUnit.Bv_SQ).length ≤ 12 ∧
    acUnit.AY2_t0.length ≤ 10 ∧ acUnit.AY2_t1.length ≤ 10 ∧
    acUnit.AY3_t0.length ≤ 11 ∧ acUnit.AY3_t1.length ≤ 11 ∧
    acUnit.AX2_t0.length ≤ 11 ∧ acUnit.AX2_t1.length ≤ 11 ∧ acUnit.AX2_t2.length ≤ 11 ∧
    acUnit.Bv_SQ.length ≤ 3 := by decide +kernel

lemma gtUnit_lens :
    (ubSub uOps gtUnit.q1_0_div_sc gtUnit.q1_2_div_sc).length ≤ 3 ∧
    gtUnit.DY2_qE_63.length ≤ 2 ∧ gtUnit.q1_1_sc.length ≤ 5 ∧
    gtUnit.qY_0_321489.length ≤ 4 ∧ gtUnit.qX_0_sc.length ≤ 3 ∧ gtUnit.q1_0_div_sc.length ≤ 3 ∧
    gtUnit.q1_2_div_sc.length ≤ 3 := by decide +kernel


lemma cacheK_ac_lens :
    (uTail cacheK.ac.A0U_t0).length ≤ 9 ∧ (uTail cacheK.ac.A0U_t1).length ≤ 9 ∧
    cacheK.ac.A0V_t0.length ≤ 10 ∧ cacheK.ac.A0V_t1.length ≤ 10 ∧ cacheK.ac.A0V_t2.length ≤ 10 ∧
    (uMul k5Ops cacheK.ac.A0V_t0 cacheK.ac.Bv_SQ).length ≤ 12 ∧
    (uMul k5Ops cacheK.ac.A0V_t1 cacheK.ac.Bv_SQ).length ≤ 12 ∧
    (uMul k5Ops cacheK.ac.A0V_t2 cacheK.ac.Bv_SQ).length ≤ 12 ∧
    cacheK.ac.AY2_t0.length ≤ 10 ∧ cacheK.ac.AY2_t1.length ≤ 10 ∧
    cacheK.ac.AY3_t0.length ≤ 11 ∧ cacheK.ac.AY3_t1.length ≤ 11 ∧
    cacheK.ac.AX2_t0.length ≤ 11 ∧ cacheK.ac.AX2_t1.length ≤ 11 ∧ cacheK.ac.AX2_t2.length ≤ 11 ∧
    cacheK.ac.Bv_SQ.length ≤ 3 := by
  have htriv : PolyOpsRel k5Ops uOps (fun _ _ => True) :=
    ⟨trivial, fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial, fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩
  have hrel := evalACache_rel htriv (S1 := S_K) (Q1 := Q_K) (S2 := ()) (Q2 := ()) trivial trivial
  have hu : ∀ {l1 : UPoly K5} {l2 : UPoly Unit}, URel (fun _ _ => True) l1 l2 → l1.length = l2.length :=
    fun h => h.length_eq
  rw [cacheK_props.1, hu (uTail_rel hrel.A0U_t0), hu (uTail_rel hrel.A0U_t1),
    hu hrel.A0V_t0, hu hrel.A0V_t1, hu hrel.A0V_t2,
    hu (uMul_rel htriv hrel.A0V_t0 hrel.Bv_SQ), hu (uMul_rel htriv hrel.A0V_t1 hrel.Bv_SQ),
    hu (uMul_rel htriv hrel.A0V_t2 hrel.Bv_SQ), hu hrel.AY2_t0, hu hrel.AY2_t1,
    hu hrel.AY3_t0, hu hrel.AY3_t1, hu hrel.AX2_t0, hu hrel.AX2_t1, hu hrel.AX2_t2, hu hrel.Bv_SQ]
  exact acUnit_lens

lemma gtK_lens :
    (ubSub k5Ops gtK.q1_0_div_sc gtK.q1_2_div_sc).length ≤ 3 ∧
    gtK.DY2_qE_63.length ≤ 2 ∧ gtK.q1_1_sc.length ≤ 5 ∧
    gtK.qY_0_321489.length ≤ 4 ∧ gtK.qX_0_sc.length ≤ 3 ∧ gtK.q1_0_div_sc.length ≤ 3 ∧
    gtK.q1_2_div_sc.length ≤ 3 := by
  have htriv : PolyOpsRel k5Ops uOps (fun _ _ => True) :=
    ⟨trivial, fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial, fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩
  have hac := evalACache_rel htriv (S1 := S_K) (Q1 := Q_K) (S2 := ()) (Q2 := ()) trivial trivial
  have hgsq := evalGeomSQ_rel htriv (S1 := S_K) (Q1 := Q_K) (S2 := ()) (Q2 := ()) trivial trivial
  have hrel := evalGeomT_rel htriv (S1 := S_K) (T1 := T_K) (S2 := ()) (T2 := ()) trivial hac.ca_p hac.cb_p hgsq trivial
  have hub : ∀ {l1 : UBivL K5} {l2 : UBivL Unit}, UBRel (fun _ _ => True) l1 l2 → l1.length = l2.length :=
    fun h => h.length_eq
  unfold gtK acK gsqK
  rw [ hub (ubSub_rel htriv hrel.q1_0_div_sc hrel.q1_2_div_sc),
    hub hrel.DY2_qE_63, hub hrel.q1_1_sc, hub hrel.qY_0_321489, hub hrel.qX_0_sc,
    hub hrel.q1_0_div_sc, hub hrel.q1_2_div_sc]
  exact gtUnit_lens

-- Prove `evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) = ∑ k : Fin 13, R12_int_p.coeff k.val * evalSQ_K5 (W_num_expr k)`!
lemma evalBivLK5_BTot_eq_dot_W :
    evalBivLK5 (evalBTot k5Ops cacheK gtK T_K) =
      ∑ k : Fin 13, R12_int_p.coeff k.val * evalSQ_K5 (W_num_expr k) := by
  have hW_list := cacheK_props.2.2.1
  have hW_get (k : Fin 13) : cacheK.W.getD k.val 0 = evalSQ_K5 (W_num_expr k) := by
    rw [hW_list]; fin_cases k <;> rfl
  have hlen_ac := cacheK_ac_lens
  have hlen_gt := gtK_lens
  -- Expand `evalBTot` via `letB_intro` (zero DAG expansion!)
  let P_btot : BivL K5 → Prop := fun b => evalBivLK5 b = ∑ k : Fin 13, R12_int_p.coeff k.val * evalSQ_K5 (W_num_expr k)
  suffices h : P_btot (evalBTot k5Ops cacheK gtK T_K) from h
  unfold evalBTot
  refine letB_intro fun T2 hT2 => letB_intro fun d_A0U hdU => letB_intro fun d_A0V hdV =>
    letB_intro fun d_A0V_U hdVU => letB_intro fun d_A0VBv hdVB => letB_intro fun d_AY2 hdY2 =>
    letB_intro fun d_AY3 hdY3 => letB_intro fun d_AX2 hdX2 => ?_
  dsimp only [P_btot]
  have hd := cacheK_props.2.2.2.2.2
  rw [hdU, hdV, hdVB, hdVU, hdY2, hdY3, hdX2, hT2,
    hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.1,
    hd.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.1,
    hd.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
  simp only [evalBivLK5_bivAdd, evalBivLK5_bivNeg, evalBivLK5_bivSc,
    evalBivLK5_combineBivDot_uSc, evalBivLK5_combineBivDot_uAdd]
  rw [evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 0 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega),
      evalBivLK5_combineBivDot_dotW _ _ _ 1 (by omega) (by omega)]
  have hmul : ∀ a b : K5, k5Ops.mul a b = a * b := fun _ _ => rfl
  have hof : ∀ n : ℤ, k5Ops.ofInt n = (n : K5) := fun _ => rfl
  simp only [hmul, hof, Int.cast_ofNat]
  simp_rw [hW_get]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro k _
  have hR12c : R12_int_p.coeff k.val = R13_int_p.coeff (k.val + 1) := by
    simp [R12_int_p, Polynomial.coeff_divX]
  rw [hR12c]
  have hcoeff_eq : R13_int_p.coeff (k.val + 1) =
      7 * gtK.Cv0_243 * ((Polynomial.X ^ 1 * evalUPolyK5 (uTail cacheK.ac.A0U_t0) * evalUBivLK5 (ubSub k5Ops gtK.q1_0_div_sc gtK.q1_2_div_sc)).coeff (k.val + 1) +
        T_K * (Polynomial.X ^ 1 * evalUPolyK5 (uTail cacheK.ac.A0U_t1) * evalUBivLK5 (ubSub k5Ops gtK.q1_0_div_sc gtK.q1_2_div_sc)).coeff (k.val + 1)) +
      45927 * (gtK.Cv0_243 * gtK.H0_7_2) * ((Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.AY3_t0 * evalUBivLK5 gtK.DY2_qE_63).coeff (k.val + 1) +
        T_K * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.AY3_t1 * evalUBivLK5 gtK.DY2_qE_63).coeff (k.val + 1)) +
      7 * ((Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.A0V_t0 * evalUBivLK5 gtK.q1_1_sc).coeff (k.val + 1) +
        T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.A0V_t1 * evalUBivLK5 gtK.q1_1_sc).coeff (k.val + 1) +
        T_K * T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.A0V_t2 * evalUBivLK5 gtK.q1_1_sc).coeff (k.val + 1)) +
      243 * gtK.H0_7_2 * (((Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AY2_t0 * evalUBivLK5 gtK.qY_0_321489).coeff (k.val + 1) +
        T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AY2_t1 * evalUBivLK5 gtK.qY_0_321489).coeff (k.val + 1)) +
        ((Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AX2_t0 * evalUBivLK5 gtK.qX_0_sc).coeff (k.val + 1) +
        T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AX2_t1 * evalUBivLK5 gtK.qX_0_sc).coeff (k.val + 1) +
        T_K * T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AX2_t2 * evalUBivLK5 gtK.qX_0_sc).coeff (k.val + 1))) -
      ((Polynomial.X ^ 0 * evalUPolyK5 (uMul k5Ops cacheK.ac.A0V_t0 cacheK.ac.Bv_SQ) * evalUBivLK5 gtK.q1_0_div_sc).coeff (k.val + 1) +
        T_K * (Polynomial.X ^ 0 * evalUPolyK5 (uMul k5Ops cacheK.ac.A0V_t1 cacheK.ac.Bv_SQ) * evalUBivLK5 gtK.q1_0_div_sc).coeff (k.val + 1) +
        T_K * T_K * (Polynomial.X ^ 0 * evalUPolyK5 (uMul k5Ops cacheK.ac.A0V_t2 cacheK.ac.Bv_SQ) * evalUBivLK5 gtK.q1_0_div_sc).coeff (k.val + 1) +
        gtK.Bv1_T_1701 * ((Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.A0V_t0 * evalUBivLK5 gtK.q1_0_div_sc).coeff (k.val + 1) +
          T_K * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.A0V_t1 * evalUBivLK5 gtK.q1_0_div_sc).coeff (k.val + 1) +
          T_K * T_K * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.A0V_t2 * evalUBivLK5 gtK.q1_0_div_sc).coeff (k.val + 1))) := by
    have hpoly : R13_int_p =
        Polynomial.C (7 * gtK.Cv0_243) * (Polynomial.X ^ 1 * evalUPolyK5 (uTail cacheK.ac.A0U_t0) * evalUBivLK5 (ubSub k5Ops gtK.q1_0_div_sc gtK.q1_2_div_sc) +
          Polynomial.C T_K * (Polynomial.X ^ 1 * evalUPolyK5 (uTail cacheK.ac.A0U_t1) * evalUBivLK5 (ubSub k5Ops gtK.q1_0_div_sc gtK.q1_2_div_sc))) +
        Polynomial.C (45927 * (gtK.Cv0_243 * gtK.H0_7_2)) * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.AY3_t0 * evalUBivLK5 gtK.DY2_qE_63 +
          Polynomial.C T_K * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.AY3_t1 * evalUBivLK5 gtK.DY2_qE_63)) +
        Polynomial.C 7 * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.A0V_t0 * evalUBivLK5 gtK.q1_1_sc +
          Polynomial.C T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.A0V_t1 * evalUBivLK5 gtK.q1_1_sc) +
          Polynomial.C (T_K * T_K) * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.A0V_t2 * evalUBivLK5 gtK.q1_1_sc)) +
        Polynomial.C (243 * gtK.H0_7_2) * ((Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AY2_t0 * evalUBivLK5 gtK.qY_0_321489 +
          Polynomial.C T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AY2_t1 * evalUBivLK5 gtK.qY_0_321489)) +
          (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AX2_t0 * evalUBivLK5 gtK.qX_0_sc +
          Polynomial.C T_K * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AX2_t1 * evalUBivLK5 gtK.qX_0_sc) +
          Polynomial.C (T_K * T_K) * (Polynomial.X ^ 0 * evalUPolyK5 cacheK.ac.AX2_t2 * evalUBivLK5 gtK.qX_0_sc))) -
        (Polynomial.X ^ 0 * evalUPolyK5 (uMul k5Ops cacheK.ac.A0V_t0 cacheK.ac.Bv_SQ) * evalUBivLK5 gtK.q1_0_div_sc +
          Polynomial.C T_K * (Polynomial.X ^ 0 * evalUPolyK5 (uMul k5Ops cacheK.ac.A0V_t1 cacheK.ac.Bv_SQ) * evalUBivLK5 gtK.q1_0_div_sc) +
          Polynomial.C (T_K * T_K) * (Polynomial.X ^ 0 * evalUPolyK5 (uMul k5Ops cacheK.ac.A0V_t2 cacheK.ac.Bv_SQ) * evalUBivLK5 gtK.q1_0_div_sc) +
          Polynomial.C gtK.Bv1_T_1701 * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.A0V_t0 * evalUBivLK5 gtK.q1_0_div_sc +
            Polynomial.C T_K * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.A0V_t1 * evalUBivLK5 gtK.q1_0_div_sc) +
            Polynomial.C (T_K * T_K) * (Polynomial.X ^ 1 * evalUPolyK5 cacheK.ac.A0V_t2 * evalUBivLK5 gtK.q1_0_div_sc))) := by
      simp only [cacheK_props.1, acK, R13_int_p, A0U_U_p, A0V_p, AY2_p, AY3_p, AX2_p, Bv_1701_p,
        evalUBivLK5_ubSub, evalUPolyK5_uMul, pow_zero, pow_one, one_mul, map_mul, pow_two]
      ring
    rw [hpoly]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rw [hcoeff_eq]; ring

lemma R12_int_p_natDegree_le : R12_int_p.natDegree ≤ 12 := by
  have h13 : R13_int_p.natDegree ≤ 13 := by
    have hac := cacheK_ac_lens
    have hgt := gtK_lens
    have hUdeg : ∀ (l : UPoly K5) (n : ℕ), l.length ≤ n + 1 → (evalUPolyK5 l).natDegree ≤ n := fun l n h =>
      Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => evalUPolyK5_natDegree_le l m (by omega)
    have hUBdeg : ∀ (l : UBivL K5) (n : ℕ), l.length ≤ n + 1 → (evalUBivLK5 l).natDegree ≤ n := fun l n h =>
      Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => by
        rw [evalUBivLK5_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [cacheK_props.1] at hac
    have hA0U : A0U_U_p.natDegree ≤ 8 := (Polynomial.natDegree_add_le _ _).trans (max_le
      (hUdeg _ 8 hac.1)
      ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 8 hac.2.1)))
    have hA0V : A0V_p.natDegree ≤ 9 := (Polynomial.natDegree_add_le _ _).trans (max_le
      ((Polynomial.natDegree_add_le _ _).trans (max_le
        (hUdeg _ 9 hac.2.2.1)
        ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 9 hac.2.2.2.1))))
      ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 9 hac.2.2.2.2.1)))
    have hAY2 : AY2_p.natDegree ≤ 9 := (Polynomial.natDegree_add_le _ _).trans (max_le
      (hUdeg _ 9 hac.2.2.2.2.2.2.2.2.1)
      ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 9 hac.2.2.2.2.2.2.2.2.2.1)))
    have hAY3 : AY3_p.natDegree ≤ 10 := (Polynomial.natDegree_add_le _ _).trans (max_le
      (hUdeg _ 10 hac.2.2.2.2.2.2.2.2.2.2.1)
      ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 10 hac.2.2.2.2.2.2.2.2.2.2.2.1)))
    have hAX2 : AX2_p.natDegree ≤ 10 := (Polynomial.natDegree_add_le _ _).trans (max_le
      ((Polynomial.natDegree_add_le _ _).trans (max_le
        (hUdeg _ 10 hac.2.2.2.2.2.2.2.2.2.2.2.2.1)
        ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 10 hac.2.2.2.2.2.2.2.2.2.2.2.2.2.1))))
      ((Polynomial.natDegree_C_mul_le _ _).trans (hUdeg _ 10 hac.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)))
    have hBv : Bv_1701_p.natDegree ≤ 2 := (Polynomial.natDegree_add_le _ _).trans (max_le
      (hUdeg _ 2 hac.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
      ((Polynomial.natDegree_mul_le).trans (by simp)))
    have hq10 : (evalUBivLK5 gtK.q1_0_div_sc).natDegree ≤ 2 := hUBdeg _ 2 hgt.2.2.2.2.2.1
    have hq12 : (evalUBivLK5 gtK.q1_2_div_sc).natDegree ≤ 2 := hUBdeg _ 2 hgt.2.2.2.2.2.2
    have hq11 : (evalUBivLK5 gtK.q1_1_sc).natDegree ≤ 4 := hUBdeg _ 4 hgt.2.2.1
    have hDYqE : (evalUBivLK5 gtK.DY2_qE_63).natDegree ≤ 1 := hUBdeg _ 1 hgt.2.1
    have hqY0 : (evalUBivLK5 gtK.qY_0_321489).natDegree ≤ 3 := hUBdeg _ 3 hgt.2.2.2.1
    have hqX0 : (evalUBivLK5 gtK.qX_0_sc).natDegree ≤ 2 := hUBdeg _ 2 hgt.2.2.2.2.1
    have hXmul : ∀ P : K5[X], (Polynomial.X * P).natDegree ≤ 1 + P.natDegree := fun P =>
      Polynomial.natDegree_mul_le.trans (by simp)
    unfold R13_int_p
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
          · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_mul_le.trans (by
              have := hXmul A0U_U_p; have := Polynomial.natDegree_sub_le (evalUBivLK5 gtK.q1_0_div_sc) (evalUBivLK5 gtK.q1_2_div_sc); omega))
          · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_mul_le.trans (by
              have := hXmul AY3_p; omega))
        · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_mul_le.trans (by omega))
      · exact (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_add_le _ _).trans (max_le
          (Polynomial.natDegree_mul_le.trans (by omega)) (Polynomial.natDegree_mul_le.trans (by omega))))
    · exact Polynomial.natDegree_mul_le.trans (by
        have := Polynomial.natDegree_mul_le (p := A0V_p) (q := Bv_1701_p); omega)
  exact (natDegree_divX_le_pred R13_int_p).trans (by omega)


end SymmetricSexticResidual.LocalResidueQ5

open scoped BigOperators in
theorem solution :
    (SymmetricSexticResidual.LocalResidueQ5.cacheK.ac = SymmetricSexticResidual.LocalResidueQ5.acK) ∧
    (SymmetricSexticResidual.LocalResidueQ5.cacheK.gsq = SymmetricSexticResidual.LocalResidueQ5.gsqK) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.D_all_expr =
      SymmetricSexticResidual.LocalResidueQ5.cacheK.D_div_L2 *
      SymmetricSexticResidual.LocalResidueU0.L_K ^ 2) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalBivLK5
        (SymmetricSexticResidual.LocalResidueQ5.cacheK.RQ5_T.map fun row =>
          row.map fun p => PolynomialEncoding.PolyOps.uEval
            SymmetricSexticResidual.LocalResidueQ5.k5Ops p SymmetricSexticResidual.K5Field.T_K) =
      SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueData.RQ5_biv) ∧
    (SymmetricSexticResidual.LocalResidueQ5.R12_int_p.natDegree ≤ 12) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalBivLK5
        (SymmetricSexticResidual.LocalResidueQ5.evalBTot
          SymmetricSexticResidual.LocalResidueQ5.k5Ops
          SymmetricSexticResidual.LocalResidueQ5.cacheK
          SymmetricSexticResidual.LocalResidueQ5.gtK
          SymmetricSexticResidual.K5Field.T_K) =
      ∑ k : Fin 13,
        SymmetricSexticResidual.LocalResidueQ5.R12_int_p.coeff k.val *
        SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5
          (SymmetricSexticResidual.LocalResidueQ5.W_num_expr k)) :=
  ⟨SymmetricSexticResidual.LocalResidueQ5.cacheK_props.1,
   SymmetricSexticResidual.LocalResidueQ5.cacheK_props.2.1,
   SymmetricSexticResidual.LocalResidueQ5.cacheK_props.2.2.2.1,
   SymmetricSexticResidual.LocalResidueQ5.cacheK_props.2.2.2.2.1,
   SymmetricSexticResidual.LocalResidueQ5.R12_int_p_natDegree_le,
   SymmetricSexticResidual.LocalResidueQ5.evalBivLK5_BTot_eq_dot_W⟩
