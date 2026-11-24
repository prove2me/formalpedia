-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_recurrences_K5
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:41:59.882835+00:00
-- url     : https://prove2.me/submissions/261c36c4-7e14-46b3-b5d9-006cde69764f

import Definitions.Def_HodgeComputerSSR_Q5K5Master
import Theorems.Thm_HodgeComputer_Formal_KroneckerCheck_mvPoly3_eq_zero_of_kronecker_grid
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_q5q7_0
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_q5q7_1
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_q5q7_2
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_q5q7_3
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_q5q7_4
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_q5q7_rel

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.Q5WeightsData
  PolynomialEncoding.KroneckerCheck
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len
open scoped BigOperators

private lemma q5q7_bounds_ok : checkQ5Q7Bounds = true :=
  HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_0.1
private lemma q5q7_chunk_0 : checkQ5Q7Chunk (-24) 10 = true :=
  HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_0.2
private lemma q5q7_chunk_1 : checkQ5Q7Chunk (-14) 10 = true :=
  HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_1
private lemma q5q7_chunk_2 : checkQ5Q7Chunk (-4) 10 = true :=
  HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_2
private lemma q5q7_chunk_3 : checkQ5Q7Chunk 6 10 = true :=
  HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_3
private lemma q5q7_chunk_4 : checkQ5Q7Chunk 16 10 = true :=
  HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_4
private abbrev q5q7RecList_rel := @HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_rel

lemma q5q7_values_ok : checkQ5Q7Chunk (-24) 50 = true := by
  rw [show (50 : ℕ) = 10 + 40 from rfl, checkQ5Q7Chunk_append, q5q7_chunk_0, Bool.true_and]
  rw [show ((-24 : ℤ) + (10 : ℕ)) = -14 from rfl, show (40 : ℕ) = 10 + 30 from rfl, checkQ5Q7Chunk_append, q5q7_chunk_1, Bool.true_and]
  rw [show ((-14 : ℤ) + (10 : ℕ)) = -4 from rfl, show (30 : ℕ) = 10 + 20 from rfl, checkQ5Q7Chunk_append, q5q7_chunk_2, Bool.true_and]
  rw [show ((-4 : ℤ) + (10 : ℕ)) = 6 from rfl, show (20 : ℕ) = 10 + 10 from rfl, checkQ5Q7Chunk_append, q5q7_chunk_3, Bool.true_and]
  exact q5q7_chunk_4

lemma q5q7RecList_poly3_zero :
    ∀ p ∈ q5q7RecList poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1), p = 0 := by
  have hb_ok : checkQ5Q7Bounds = true := q5q7_bounds_ok
  have hv_ok : checkQ5Q7Chunk (-24) 50 = true := q5q7_values_ok
  unfold checkQ5Q7Bounds at hb_ok
  unfold checkQ5Q7Chunk at hv_ok
  have hrelB := q5q7RecList_rel (respectsBoundRel 25 0) (respectsBound_X0 25 0) (respectsBound_X1 25 0)
  have hrelV : ∀ q ∈ rangeInt (-24) 50,
      List.Forall₂ (fun p z => MvPolynomial.eval (v3Int q5q7Lim q 0) p = z)
        (q5q7RecList poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1))
        (q5q7RecList intOps q5q7B q) := fun q _ =>
    q5q7RecList_rel (poly3ToIntRel q5q7Lim q 0) (by rw [MvPolynomial.eval_X, v3Int]; rfl) (by rw [MvPolynomial.eval_X, v3Int])
  have hallB : ∀ b ∈ q5q7RecList pbOps ⟨1, 0, 0, 1⟩ ⟨0, 1, 0, 25⟩, b.dQ < 50 ∧ b.dT = 0 ∧ b.M < q5q7Lim := by
    intro b hb
    have h := List.all_eq_true.mp hb_ok b hb
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hallV : ∀ q ∈ rangeInt (-24) 50, ∀ z ∈ q5q7RecList intOps q5q7B q, z = 0 := by
    intro q hq z hz
    have h1 := allRange_spec (-24) 50 _ hv_ok q hq
    exact beq_iff_eq.mp (List.all_eq_true.mp h1 z hz)
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hlenB := hrelB.length_eq
  have hb_rel : RespectsBound 25 0
      ((q5q7RecList poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1))[i])
      ((q5q7RecList pbOps ⟨1, 0, 0, 1⟩ ⟨0, 1, 0, 25⟩)[i]'(hlenB ▸ hi)) :=
    list_forall₂_getElem hrelB i hi (hlenB ▸ hi)
  obtain ⟨hdQ, hdT, hM⟩ := hallB _ (List.getElem_mem _)
  apply HodgeComputer.Formal.KroneckerCheck.mvPoly3_eq_zero_of_kronecker_grid _ _ 25 0 q5q7Lim (rangeInt (-24) 50) {0}
    hb_rel (by rw [rangeInt_card]; exact hdQ)
    (rangeInt_natAbs_le (-24) 50 25 (by decide) (by decide))
    (by simp [hdT]) (fun t ht => by simp at ht; subst ht; simp) hM
  intro q hq t ht
  simp only [Finset.mem_singleton] at ht; subst ht
  have hrv := hrelV q hq
  have hlenV := hrv.length_eq
  have heq := list_forall₂_getElem hrv i hi (hlenV ▸ hi)
  rw [heq]
  exact hallV q hq _ (List.getElem_mem _)

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

lemma Q5_Q7_recurrences_K5 :
    (∀ k : Fin 8, ∑ j : Fin 6, evalSQ_K5 (Q5_c j) * evalSQ_K5 (W_num_expr ⟨k.val + j.val, by omega⟩) = 0) ∧
    (∀ m : Fin 4, ∑ j : Fin 8, evalSQ_K5 (Q7_c j) * evalSQ_K5 (W_num_expr ⟨m.val + j.val, by omega⟩) = 0) ∧
    ((lc5_const : K5) * ∑ j : Fin 8, evalSQ_K5 (Q7_c j) * evalSQ_K5 (W_num_expr ⟨4 + j.val, by omega⟩) =
      (D_int_all : K5) * evalSQ_K5 D_all_div_lc5_expr) := by
  have hrelK : List.Forall₂ (fun p x => evalP3K5 p = x)
      (q5q7RecList poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1))
      (q5q7RecList k5Ops S_K Q_K) :=
    q5q7RecList_rel poly3ToK5Rel (by simp [evalP3K5, v3K5]) (by simp [evalP3K5, v3K5])
  have hallK : ∀ x ∈ q5q7RecList k5Ops S_K Q_K, x = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hlen := hrelK.length_eq
    have heq := list_forall₂_getElem hrelK i (hlen.symm ▸ hi) hi
    rw [← heq, q5q7RecList_poly3_zero _ (List.getElem_mem _), map_zero]
  have hev_eq (e : Expr) :
      evalExpr2 k5Ops S_K Q_K (powList k5Ops S_K 30 (k5Ops.ofInt 1)) (powList k5Ops Q_K 37 (k5Ops.ofInt 1)) e =
      evalSQ_K5 e := by
    have hX0 : evalP3K5 (MvPolynomial.X 0) = S_K := by simp [evalP3K5, v3K5]
    have hX1 : evalP3K5 (MvPolynomial.X 1) = Q_K := by simp [evalP3K5, v3K5]
    have h := evalExpr2_rel poly3ToK5Rel hX0 hX1
      (powList_rel poly3ToK5Rel hX0 30 (poly3ToK5Rel.rel_ofInt 1))
      (powList_rel poly3ToK5Rel hX1 37 (poly3ToK5Rel.rel_ofInt 1)) e
    rw [evalExpr2_poly3_eq, evalP3K5_ringEval_SQ] at h
    exact h.symm
  -- Rewrite `q5q7RecList k5Ops S_K Q_K` using `letB_step` (O(N), zero DAG expansion)!
  have hlist_eq : q5q7RecList k5Ops S_K Q_K =
      let w : Fin 13 → K5 := fun k => evalSQ_K5 (W_num_expr k)
      let q5 : Fin 6 → K5 := fun j => evalSQ_K5 (Q5_c j)
      let q7 : Fin 8 → K5 := fun j => evalSQ_K5 (Q7_c j)
      let r5 := fun a0 a1 a2 a3 a4 a5 =>
        (q5 0 * a0 + q5 1 * a1 + (q5 2 * a2 + q5 3 * a3)) + (q5 4 * a4 + q5 5 * a5)
      let r7 := fun a0 a1 a2 a3 a4 a5 a6 a7 =>
        (q7 0 * a0 + q7 1 * a1 + (q7 2 * a2 + q7 3 * a3)) +
          ((q7 4 * a4 + q7 5 * a5) + (q7 6 * a6 + q7 7 * a7))
      [ r5 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5),
        r5 (w 1) (w 2) (w 3) (w 4) (w 5) (w 6),
        r5 (w 2) (w 3) (w 4) (w 5) (w 6) (w 7),
        r5 (w 3) (w 4) (w 5) (w 6) (w 7) (w 8),
        r5 (w 4) (w 5) (w 6) (w 7) (w 8) (w 9),
        r5 (w 5) (w 6) (w 7) (w 8) (w 9) (w 10),
        r5 (w 6) (w 7) (w 8) (w 9) (w 10) (w 11),
        r5 (w 7) (w 8) (w 9) (w 10) (w 11) (w 12),
        r7 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7),
        r7 (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8),
        r7 (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9),
        r7 (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9) (w 10),
        (lc5_const : K5) * r7 (w 4) (w 5) (w 6) (w 7) (w 8) (w 9) (w 10) (w 11) -
          (D_int_all : K5) * evalSQ_K5 D_all_div_lc5_expr ] := by
    have hf := fac_K5_eqs
    have hW (k : Fin 13) : evalSQ_K5 (W_num_expr k) =
        (N_k_mul k : K5) * (evalSQ_K5 (D_quot_expr k) * evalSQ_K5 (N_k_expr k)) := rfl
    have hD0 : evalSQ_K5 (D_quot_expr 0) = evalSQ_K5 fac_3 ^ 13 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD1 : evalSQ_K5 (D_quot_expr 1) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 2 * evalSQ_K5 fac_3 ^ 13 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD2 : evalSQ_K5 (D_quot_expr 2) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 4 * evalSQ_K5 fac_3 ^ 13 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD3 : evalSQ_K5 (D_quot_expr 3) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 6 * evalSQ_K5 fac_3 ^ 13 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD4 : evalSQ_K5 (D_quot_expr 4) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 13 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD5 : evalSQ_K5 (D_quot_expr 5) = evalSQ_K5 (D_quot_expr 4) := rfl
    have hD6 : evalSQ_K5 (D_quot_expr 6) = evalSQ_K5 (D_quot_expr 4) := rfl
    have hD7 : evalSQ_K5 (D_quot_expr 7) = evalSQ_K5 (D_quot_expr 4) := rfl
    have hD8 : evalSQ_K5 (D_quot_expr 8) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 12 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD9 : evalSQ_K5 (D_quot_expr 9) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 9 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD10 : evalSQ_K5 (D_quot_expr 10) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 6 * evalSQ_K5 fac_4 ^ 2 := rfl
    have hD11 : evalSQ_K5 (D_quot_expr 11) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 3 * evalSQ_K5 fac_4 := rfl
    have hD12 : evalSQ_K5 (D_quot_expr 12) = evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 := rfl
    have hDlc5 : evalSQ_K5 D_all_div_lc5_expr =
        evalSQ_K5 fac_0 * evalSQ_K5 fac_1 * evalSQ_K5 fac_2 ^ 7 * evalSQ_K5 fac_3 ^ 9 *
        evalSQ_K5 fac_4 * evalSQ_K5 fac_5 ^ 4 * evalSQ_K5 fac_6 := rfl
    unfold q5q7RecList
    rw [letB, letB]
    refine letB_step (y := evalSQ_K5 fac_2) (by simpa [k5Ops, ringOps] using hf.2.2.1) ?_
    refine letB_step (y := evalSQ_K5 fac_3) (by simpa [k5Ops, ringOps] using hf.2.2.2.1) ?_
    refine letB_step (y := evalSQ_K5 fac_4) (by simpa [k5Ops, ringOps] using hf.2.2.2.2) ?_
    refine letB_step (hev_eq fac_5) ?_
    refine letB_step (hev_eq fac_6) ?_
    refine letB_step (y := evalSQ_K5 fac_2 ^ 2) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_2 ^ 4) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_2 ^ 6) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_2 ^ 7) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 3) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 6) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 9) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 12) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_3 ^ 13) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 fac_4 ^ 2) (by dsimp [k5Ops, ringOps]; ring) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 0)) (by dsimp [k5Ops, ringOps]; rw [hD0]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 1)) (by dsimp [k5Ops, ringOps]; rw [hD1, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 2)) (by dsimp [k5Ops, ringOps]; rw [hD2, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 3)) (by dsimp [k5Ops, ringOps]; rw [hD3, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 4)) (by dsimp [k5Ops, ringOps]; rw [hD4, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 8)) (by dsimp [k5Ops, ringOps]; rw [hD8, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 9)) (by dsimp [k5Ops, ringOps]; rw [hD9, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 10)) (by dsimp [k5Ops, ringOps]; rw [hD10, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 11)) (by dsimp [k5Ops, ringOps]; rw [hD11, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (D_quot_expr 12)) (by dsimp [k5Ops, ringOps]; rw [hD12, ← hf.2.1]) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 0)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 1)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 2)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 3)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 4)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 5)) (by rw [hev_eq, hW, hD5]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 6)) (by rw [hev_eq, hW, hD6]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 7)) (by rw [hev_eq, hW, hD7]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 8)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 9)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 10)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 11)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (y := evalSQ_K5 (W_num_expr 12)) (by rw [hev_eq, hW]; rfl) ?_
    refine letB_step (hev_eq Q5_c0) ?_
    refine letB_step (hev_eq Q5_c1) ?_
    refine letB_step (hev_eq Q5_c2) ?_
    refine letB_step (hev_eq Q5_c3) ?_
    refine letB_step (hev_eq Q5_c4) ?_
    refine letB_step (hev_eq Q5_c5) ?_
    refine letB_step (hev_eq Q7_c0) ?_
    refine letB_step (hev_eq Q7_c1) ?_
    refine letB_step (hev_eq Q7_c2) ?_
    refine letB_step (hev_eq Q7_c3) ?_
    refine letB_step (hev_eq Q7_c4) ?_
    refine letB_step (hev_eq Q7_c5) ?_
    refine letB_step (hev_eq Q7_c6) ?_
    refine letB_step (hev_eq Q7_c7) ?_
    refine letB_step (y := evalSQ_K5 D_all_div_lc5_expr) (by dsimp [k5Ops, ringOps]; rw [hDlc5, ← hf.1, ← hf.2.1]) ?_
    simp only [q5Dot, q7Dot, k5Ops, ringOps]; rfl
  rw [hlist_eq] at hallK
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have hk : ∀ i : Fin 8,
        ((evalSQ_K5 (Q5_c 0) * evalSQ_K5 (W_num_expr ⟨i.val + 0, by omega⟩) +
          evalSQ_K5 (Q5_c 1) * evalSQ_K5 (W_num_expr ⟨i.val + 1, by omega⟩) +
         (evalSQ_K5 (Q5_c 2) * evalSQ_K5 (W_num_expr ⟨i.val + 2, by omega⟩) +
          evalSQ_K5 (Q5_c 3) * evalSQ_K5 (W_num_expr ⟨i.val + 3, by omega⟩))) +
         (evalSQ_K5 (Q5_c 4) * evalSQ_K5 (W_num_expr ⟨i.val + 4, by omega⟩) +
          evalSQ_K5 (Q5_c 5) * evalSQ_K5 (W_num_expr ⟨i.val + 5, by omega⟩))) = 0 := fun i => by
      fin_cases i <;> exact hallK _ (by simp)
    have h0 := hk k
    rw [Fin.sum_univ_six]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
      show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl, show (5 : Fin 6).val = 5 from rfl]
    linear_combination h0
  · intro m
    have hm : ∀ i : Fin 4,
        ((evalSQ_K5 (Q7_c 0) * evalSQ_K5 (W_num_expr ⟨i.val + 0, by omega⟩) +
          evalSQ_K5 (Q7_c 1) * evalSQ_K5 (W_num_expr ⟨i.val + 1, by omega⟩) +
         (evalSQ_K5 (Q7_c 2) * evalSQ_K5 (W_num_expr ⟨i.val + 2, by omega⟩) +
          evalSQ_K5 (Q7_c 3) * evalSQ_K5 (W_num_expr ⟨i.val + 3, by omega⟩))) +
        ((evalSQ_K5 (Q7_c 4) * evalSQ_K5 (W_num_expr ⟨i.val + 4, by omega⟩) +
          evalSQ_K5 (Q7_c 5) * evalSQ_K5 (W_num_expr ⟨i.val + 5, by omega⟩)) +
         (evalSQ_K5 (Q7_c 6) * evalSQ_K5 (W_num_expr ⟨i.val + 6, by omega⟩) +
          evalSQ_K5 (Q7_c 7) * evalSQ_K5 (W_num_expr ⟨i.val + 7, by omega⟩)))) = 0 := fun i => by
      fin_cases i <;> exact hallK _ (by simp)
    have h0 := hm m
    rw [Fin.sum_univ_eight]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
      show (3 : Fin 8).val = 3 from rfl, show (4 : Fin 8).val = 4 from rfl, show (5 : Fin 8).val = 5 from rfl,
      show (6 : Fin 8).val = 6 from rfl, show (7 : Fin 8).val = 7 from rfl]
    linear_combination h0
  · have h12 : (lc5_const : K5) *
        ((evalSQ_K5 (Q7_c 0) * evalSQ_K5 (W_num_expr 4) +
          evalSQ_K5 (Q7_c 1) * evalSQ_K5 (W_num_expr 5) +
         (evalSQ_K5 (Q7_c 2) * evalSQ_K5 (W_num_expr 6) +
          evalSQ_K5 (Q7_c 3) * evalSQ_K5 (W_num_expr 7))) +
        ((evalSQ_K5 (Q7_c 4) * evalSQ_K5 (W_num_expr 8) +
          evalSQ_K5 (Q7_c 5) * evalSQ_K5 (W_num_expr 9)) +
         (evalSQ_K5 (Q7_c 6) * evalSQ_K5 (W_num_expr 10) +
          evalSQ_K5 (Q7_c 7) * evalSQ_K5 (W_num_expr 11)))) -
        (D_int_all : K5) * evalSQ_K5 D_all_div_lc5_expr = 0 := hallK _ (by simp)
    rw [Fin.sum_univ_eight]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
      show (3 : Fin 8).val = 3 from rfl, show (4 : Fin 8).val = 4 from rfl, show (5 : Fin 8).val = 5 from rfl,
      show (6 : Fin 8).val = 6 from rfl, show (7 : Fin 8).val = 7 from rfl,
      show ∀ h : 4 + 0 < 13, (⟨4 + 0, h⟩ : Fin 13) = 4 from fun _ => rfl,
      show ∀ h : 4 + 1 < 13, (⟨4 + 1, h⟩ : Fin 13) = 5 from fun _ => rfl,
      show ∀ h : 4 + 2 < 13, (⟨4 + 2, h⟩ : Fin 13) = 6 from fun _ => rfl,
      show ∀ h : 4 + 3 < 13, (⟨4 + 3, h⟩ : Fin 13) = 7 from fun _ => rfl,
      show ∀ h : 4 + 4 < 13, (⟨4 + 4, h⟩ : Fin 13) = 8 from fun _ => rfl,
      show ∀ h : 4 + 5 < 13, (⟨4 + 5, h⟩ : Fin 13) = 9 from fun _ => rfl,
      show ∀ h : 4 + 6 < 13, (⟨4 + 6, h⟩ : Fin 13) = 10 from fun _ => rfl,
      show ∀ h : 4 + 7 < 13, (⟨4 + 7, h⟩ : Fin 13) = 11 from fun _ => rfl]
    linear_combination h12

-- Rational Q5 weight `W_K5 k = W_num_K5 k / (D_int_all * D_all_K5)` (for integer polynomials `Q5_pol`, `Q7_pol`)

end SymmetricSexticResidual.LocalResidueQ5

open scoped BigOperators in
theorem solution :
    (∀ k : Fin 8, ∑ j : Fin 6,
      SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 (SymmetricSexticResidual.Q5WeightsData.Q5_c j) *
      SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5
        (SymmetricSexticResidual.LocalResidueQ5.W_num_expr ⟨k.val + j.val, by omega⟩) = 0) ∧
    (∀ m : Fin 4, ∑ j : Fin 8,
      SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 (SymmetricSexticResidual.Q5WeightsData.Q7_c j) *
      SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5
        (SymmetricSexticResidual.LocalResidueQ5.W_num_expr ⟨m.val + j.val, by omega⟩) = 0) ∧
    ((SymmetricSexticResidual.Q5WeightsData.lc5_const : SymmetricSexticResidual.K5Field.K5) *
      ∑ j : Fin 8,
        SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 (SymmetricSexticResidual.Q5WeightsData.Q7_c j) *
        SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5
          (SymmetricSexticResidual.LocalResidueQ5.W_num_expr ⟨4 + j.val, by omega⟩) =
      (SymmetricSexticResidual.Q5WeightsData.D_int_all : SymmetricSexticResidual.K5Field.K5) *
        SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5
          SymmetricSexticResidual.Q5WeightsData.D_all_div_lc5_expr) :=
  SymmetricSexticResidual.LocalResidueQ5.Q5_Q7_recurrences_K5
