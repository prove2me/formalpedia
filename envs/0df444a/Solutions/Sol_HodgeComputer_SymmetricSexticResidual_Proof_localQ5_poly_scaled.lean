-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_poly_scaled
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:43:42.321191+00:00
-- url     : https://prove2.me/submissions/d88dfbf0-e20a-4e98-97d5-309a774875f5

import Definitions.Def_HodgeComputerSSR_CoverParams
import Definitions.Def_HodgeComputerSSR_Q5K5Master

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.CoverAlgebra
  SymmetricSexticResidual.LocalResidueU0 SymmetricSexticResidual.Q5WeightsData
  Polynomial
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions
open scoped BigOperators

def vLoc_SQ : ℕ → LocK5
  | 0 => S_loc
  | 1 => Q_loc
  | _ => 0

def v1009_SQ : ℕ → ZMod 1009
  | 0 => 2
  | 1 => 3
  | _ => 0

lemma evalSQ_K5_ne_zero_of_mod1009 (e : Expr) (h : ringEval v1009_SQ e ≠ 0) :
    evalSQ_K5 e ≠ 0 := by
  have hsub : ∀ e' : Expr, LocK5.subtype (ringEval vLoc_SQ e') = evalSQ_K5 e' := by
    intro e'
    induction e' with
    | num c => simp [evalSQ_K5, ringEval]
    | natCast n => simp [evalSQ_K5, ringEval]
    | intCast z => simp [evalSQ_K5, ringEval]
    | var j =>
      match j with
      | 0 => rfl
      | 1 => rfl
      | _ + 2 => simp [evalSQ_K5, ringEval, vLoc_SQ, vK5_SQ]
    | neg a ha => simp [evalSQ_K5, ringEval] at ha ⊢; rw [ha]
    | add a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
    | sub a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
    | mul a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
    | pow a k ha => simp [evalSQ_K5, ringEval] at ha ⊢; rw [ha]
  have hev : ∀ e' : Expr, evLoc (ringEval vLoc_SQ e') = ringEval v1009_SQ e' := by
    intro e'
    induction e' with
    | num c => simp [ringEval]
    | natCast n => simp [ringEval]
    | intCast z => simp [ringEval]
    | var j =>
      match j with
      | 0 => exact evLoc_S
      | 1 => exact evLoc_Q
      | _ + 2 => simp [ringEval, vLoc_SQ, v1009_SQ]
    | neg a ha => simp [ringEval] at ha ⊢; rw [ha]
    | add a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
    | sub a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
    | mul a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
    | pow a k ha => simp [ringEval] at ha ⊢; rw [ha]
  rw [← hsub e]
  exact LocK5.ne_zero_of_evLoc (by rw [hev e]; exact h)

lemma fac_0_ne : evalSQ_K5 fac_0 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_0 (by decide)
lemma fac_1_ne : evalSQ_K5 fac_1 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_1 (by decide)
lemma fac_2_ne : evalSQ_K5 fac_2 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_2 (by decide)
lemma fac_3_ne : evalSQ_K5 fac_3 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_3 (by decide)
lemma fac_4_ne : evalSQ_K5 fac_4 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_4 (by decide)
lemma fac_5_ne : evalSQ_K5 fac_5 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_5 (by decide)
lemma fac_6_ne : evalSQ_K5 fac_6 ≠ 0 := evalSQ_K5_ne_zero_of_mod1009 fac_6 (by decide)

lemma D_all_K5_ne : evalSQ_K5 D_all_expr ≠ 0 := by
  simp only [D_all_expr, evalSQ_K5, ringEval]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero fac_0_ne fac_1_ne) (pow_ne_zero 7 fac_2_ne)) (pow_ne_zero 13 fac_3_ne))
    (pow_ne_zero 2 fac_4_ne)) (pow_ne_zero 4 fac_5_ne)) fac_6_ne

lemma fac_4_eq_neg_L : evalSQ_K5 fac_4 = -L_K := by
  simp only [fac_4, evalSQ_K5, ringEval, vK5_SQ, L_K, Int.cast_neg, Int.cast_ofNat]; ring

-- Exact identification of `k5Params.Q5_z` and `k5Params.Q7_z` with `Q5WeightsData.Q5_c`, `Q7_c`!
lemma Q5_poly_eval_eq {R : Type*} [Field R] [CharZero R] (S Q U : R) :
    let ca := (-625 / 81 * S ^ 2 + 500 / 27 * S * Q - 25 / 3 * Q ^ 2) +
              (143 / 81 * S ^ 2 - 184 / 27 * S * Q + 52 / 9 * Q ^ 2) * U +
              (-4 / 81 * S ^ 2 + 8 / 27 * S * Q - 4 / 9 * Q ^ 2) * U ^ 2
    let cb := (250 / 27 * S ^ 2 - 50 / 3 * S * Q) +
              (-92 / 27 * S ^ 2 + 104 / 9 * S * Q - 22 / 3 * Q ^ 2 + 10 / 7 * Q + 10 / 7) * U +
              (4 / 27 * S ^ 2 - 8 / 9 * S * Q + 4 / 3 * Q ^ 2) * U ^ 2
    let q20 := (-625 / 81 * S + 250 / 27 * Q) + (143 / 81 * S - 92 / 27 * Q) * U + (-4 / 81 * S + 4 / 27 * Q) * U ^ 2
    let q11 := (500 / 27 * S - 50 / 3 * Q) + (-184 / 27 * S + 104 / 9 * Q) * U + (8 / 27 * S - 8 / 9 * Q) * U ^ 2
    let q02 := (-25 / 3 * S) + (52 / 9 * S - 22 / 3 * Q + 5 / 7) * U + (-4 / 9 * S + 4 / 3 * Q) * U ^ 2
    let v : ℕ → R := fun | 0 => S | 1 => Q | _ => 0
    2893401 * (q20 * cb ^ 2 - q11 * ca * cb + q02 * ca ^ 2) =
      ringEval v Q5_c0 + ringEval v Q5_c1 * U + ringEval v Q5_c2 * U ^ 2 +
      ringEval v Q5_c3 * U ^ 3 + ringEval v Q5_c4 * U ^ 4 + ringEval v Q5_c5 * U ^ 5 := by
  simp only [Q5_c0, Q5_c1, Q5_c2, Q5_c3, Q5_c4, Q5_c5, ringEval, Int.cast_neg, Int.cast_ofNat]
  ring

lemma Q7_poly_eval_eq {R : Type*} [Field R] [CharZero R] (S Q U : R) :
    let ca := (-625 / 81 * S ^ 2 + 500 / 27 * S * Q - 25 / 3 * Q ^ 2) +
              (143 / 81 * S ^ 2 - 184 / 27 * S * Q + 52 / 9 * Q ^ 2) * U +
              (-4 / 81 * S ^ 2 + 8 / 27 * S * Q - 4 / 9 * Q ^ 2) * U ^ 2
    let cb := (250 / 27 * S ^ 2 - 50 / 3 * S * Q) +
              (-92 / 27 * S ^ 2 + 104 / 9 * S * Q - 22 / 3 * Q ^ 2 + 10 / 7 * Q + 10 / 7) * U +
              (4 / 27 * S ^ 2 - 8 / 9 * S * Q + 4 / 3 * Q ^ 2) * U ^ 2
    let c30 := (-625 / 243 : R) + 143 / 243 * U - 4 / 243 * U ^ 2
    let c21 := (250 / 27 : R) - 92 / 27 * U + 4 / 27 * U ^ 2
    let c12 := (-25 / 3 : R) + 52 / 9 * U - 4 / 9 * U ^ 2
    let c03 := (-22 / 9 : R) * U + 4 / 9 * U ^ 2
    let v : ℕ → R := fun | 0 => S | 1 => Q | _ => 0
    1640558367 * (c30 * cb ^ 3 - c21 * ca * cb ^ 2 + c12 * ca ^ 2 * cb - c03 * ca ^ 3) =
      2 * (ringEval v Q7_c0 + ringEval v Q7_c1 * U + ringEval v Q7_c2 * U ^ 2 +
        ringEval v Q7_c3 * U ^ 3 + ringEval v Q7_c4 * U ^ 4 + ringEval v Q7_c5 * U ^ 5 +
        ringEval v Q7_c6 * U ^ 6 + ringEval v Q7_c7 * U ^ 7) := by
  simp only [Q7_c0, Q7_c1, Q7_c2, Q7_c3, Q7_c4, Q7_c5, Q7_c6, Q7_c7, ringEval, Int.cast_neg, Int.cast_ofNat]
  ring


lemma Q5_K5_eq_scaled :
    Polynomial.C (2893401 : K5) * k5Params.Q5_z = Q5_pol_K5 := by
  have hinf : Infinite K5 := Infinite.of_injective (Nat.cast : ℕ → K5) Nat.cast_injective
  apply Polynomial.funext; intro u
  have hring := Q5_poly_eval_eq S_K Q_K u
  have hv : ∀ e : Expr, (∀ k ≥ 2, e ≠ .var k) → True := fun _ _ => trivial
  have hQ5_ev : (Polynomial.C (2893401 : K5) * k5Params.Q5_z).eval u =
      2893401 * (
        ((-625 / 81 * S_K + 250 / 27 * Q_K) + (143 / 81 * S_K - 92 / 27 * Q_K) * u + (-4 / 81 * S_K + 4 / 27 * Q_K) * u ^ 2) *
          ((250 / 27 * S_K ^ 2 - 50 / 3 * S_K * Q_K) +
            (-92 / 27 * S_K ^ 2 + 104 / 9 * S_K * Q_K - 22 / 3 * Q_K ^ 2 + 10 / 7 * Q_K + 10 / 7) * u +
            (4 / 27 * S_K ^ 2 - 8 / 9 * S_K * Q_K + 4 / 3 * Q_K ^ 2) * u ^ 2) ^ 2 -
        ((500 / 27 * S_K - 50 / 3 * Q_K) + (-184 / 27 * S_K + 104 / 9 * Q_K) * u + (8 / 27 * S_K - 8 / 9 * Q_K) * u ^ 2) *
          ((-625 / 81 * S_K ^ 2 + 500 / 27 * S_K * Q_K - 25 / 3 * Q_K ^ 2) +
            (143 / 81 * S_K ^ 2 - 184 / 27 * S_K * Q_K + 52 / 9 * Q_K ^ 2) * u +
            (-4 / 81 * S_K ^ 2 + 8 / 27 * S_K * Q_K - 4 / 9 * Q_K ^ 2) * u ^ 2) *
          ((250 / 27 * S_K ^ 2 - 50 / 3 * S_K * Q_K) +
            (-92 / 27 * S_K ^ 2 + 104 / 9 * S_K * Q_K - 22 / 3 * Q_K ^ 2 + 10 / 7 * Q_K + 10 / 7) * u +
            (4 / 27 * S_K ^ 2 - 8 / 9 * S_K * Q_K + 4 / 3 * Q_K ^ 2) * u ^ 2) +
        ((-25 / 3 * S_K) + (52 / 9 * S_K - 22 / 3 * Q_K + 5 / 7) * u + (-4 / 9 * S_K + 4 / 3 * Q_K) * u ^ 2) *
          ((-625 / 81 * S_K ^ 2 + 500 / 27 * S_K * Q_K - 25 / 3 * Q_K ^ 2) +
            (143 / 81 * S_K ^ 2 - 184 / 27 * S_K * Q_K + 52 / 9 * Q_K ^ 2) * u +
            (-4 / 81 * S_K ^ 2 + 8 / 27 * S_K * Q_K - 4 / 9 * Q_K ^ 2) * u ^ 2) ^ 2) := by
    simp only [CoverParams.Q5_z, CoverParams.q20, CoverParams.q11, CoverParams.q02,
      CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
      k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [hQ5_ev, hring]
  have hsum : Q5_pol_K5.eval u =
      evalSQ_K5 Q5_c0 + evalSQ_K5 Q5_c1 * u + evalSQ_K5 Q5_c2 * u ^ 2 +
      evalSQ_K5 Q5_c3 * u ^ 3 + evalSQ_K5 Q5_c4 * u ^ 4 + evalSQ_K5 Q5_c5 * u ^ 5 := by
    simp only [Q5_pol_K5, Fin.sum_univ_six, Q5_c, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    change evalSQ_K5 Q5_c0 * u ^ 0 + evalSQ_K5 Q5_c1 * u ^ 1 + evalSQ_K5 Q5_c2 * u ^ 2 +
      evalSQ_K5 Q5_c3 * u ^ 3 + evalSQ_K5 Q5_c4 * u ^ 4 + evalSQ_K5 Q5_c5 * u ^ 5 = _
    ring
  rw [hsum]; rfl

lemma Q7_K5_eq_scaled :
    Polynomial.C (1640558367 : K5) * k5Params.Q7_z = Polynomial.C (2 : K5) * Q7_pol_K5 := by
  have hinf : Infinite K5 := Infinite.of_injective (Nat.cast : ℕ → K5) Nat.cast_injective
  apply Polynomial.funext; intro u
  have hring := Q7_poly_eval_eq S_K Q_K u
  have hQ7_ev : (Polynomial.C (1640558367 : K5) * k5Params.Q7_z).eval u =
      1640558367 * (
        ((-625 / 243 : K5) + 143 / 243 * u - 4 / 243 * u ^ 2) *
          ((250 / 27 * S_K ^ 2 - 50 / 3 * S_K * Q_K) +
            (-92 / 27 * S_K ^ 2 + 104 / 9 * S_K * Q_K - 22 / 3 * Q_K ^ 2 + 10 / 7 * Q_K + 10 / 7) * u +
            (4 / 27 * S_K ^ 2 - 8 / 9 * S_K * Q_K + 4 / 3 * Q_K ^ 2) * u ^ 2) ^ 3 -
        ((250 / 27 : K5) - 92 / 27 * u + 4 / 27 * u ^ 2) *
          ((-625 / 81 * S_K ^ 2 + 500 / 27 * S_K * Q_K - 25 / 3 * Q_K ^ 2) +
            (143 / 81 * S_K ^ 2 - 184 / 27 * S_K * Q_K + 52 / 9 * Q_K ^ 2) * u +
            (-4 / 81 * S_K ^ 2 + 8 / 27 * S_K * Q_K - 4 / 9 * Q_K ^ 2) * u ^ 2) *
          ((250 / 27 * S_K ^ 2 - 50 / 3 * S_K * Q_K) +
            (-92 / 27 * S_K ^ 2 + 104 / 9 * S_K * Q_K - 22 / 3 * Q_K ^ 2 + 10 / 7 * Q_K + 10 / 7) * u +
            (4 / 27 * S_K ^ 2 - 8 / 9 * S_K * Q_K + 4 / 3 * Q_K ^ 2) * u ^ 2) ^ 2 +
        ((-25 / 3 : K5) + 52 / 9 * u - 4 / 9 * u ^ 2) *
          ((-625 / 81 * S_K ^ 2 + 500 / 27 * S_K * Q_K - 25 / 3 * Q_K ^ 2) +
            (143 / 81 * S_K ^ 2 - 184 / 27 * S_K * Q_K + 52 / 9 * Q_K ^ 2) * u +
            (-4 / 81 * S_K ^ 2 + 8 / 27 * S_K * Q_K - 4 / 9 * Q_K ^ 2) * u ^ 2) ^ 2 *
          ((250 / 27 * S_K ^ 2 - 50 / 3 * S_K * Q_K) +
            (-92 / 27 * S_K ^ 2 + 104 / 9 * S_K * Q_K - 22 / 3 * Q_K ^ 2 + 10 / 7 * Q_K + 10 / 7) * u +
            (4 / 27 * S_K ^ 2 - 8 / 9 * S_K * Q_K + 4 / 3 * Q_K ^ 2) * u ^ 2) -
        ((-22 / 9 : K5) * u + 4 / 9 * u ^ 2) *
          ((-625 / 81 * S_K ^ 2 + 500 / 27 * S_K * Q_K - 25 / 3 * Q_K ^ 2) +
            (143 / 81 * S_K ^ 2 - 184 / 27 * S_K * Q_K + 52 / 9 * Q_K ^ 2) * u +
            (-4 / 81 * S_K ^ 2 + 8 / 27 * S_K * Q_K - 4 / 9 * Q_K ^ 2) * u ^ 2) ^ 3) := by
    simp only [CoverParams.Q7_z, CoverParams.c30, CoverParams.c21, CoverParams.c12, CoverParams.c03,
      CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, CoverParams.inv243,
      k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [hQ7_ev, hring]
  have hsum : (Polynomial.C (2 : K5) * Q7_pol_K5).eval u =
      2 * (evalSQ_K5 Q7_c0 + evalSQ_K5 Q7_c1 * u + evalSQ_K5 Q7_c2 * u ^ 2 +
        evalSQ_K5 Q7_c3 * u ^ 3 + evalSQ_K5 Q7_c4 * u ^ 4 + evalSQ_K5 Q7_c5 * u ^ 5 +
        evalSQ_K5 Q7_c6 * u ^ 6 + evalSQ_K5 Q7_c7 * u ^ 7) := by
    simp only [Q7_pol_K5, Fin.sum_univ_eight, Q7_c, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    change 2 * (evalSQ_K5 Q7_c0 * u ^ 0 + evalSQ_K5 Q7_c1 * u ^ 1 + evalSQ_K5 Q7_c2 * u ^ 2 +
      evalSQ_K5 Q7_c3 * u ^ 3 + evalSQ_K5 Q7_c4 * u ^ 4 + evalSQ_K5 Q7_c5 * u ^ 5 +
      evalSQ_K5 Q7_c6 * u ^ 6 + evalSQ_K5 Q7_c7 * u ^ 7) = _
    ring
  rw [hsum]; rfl

lemma Q5_c5_eq_fac :
    evalSQ_K5 (Q5_c 5) = (lc5_const : K5) * evalSQ_K5 lc5_fac_expr := by
  simp only [Q5_c, Q5_c5, lc5_const, lc5_fac_expr, fac_3, fac_4, evalSQ_K5, ringEval, vK5_SQ,
    Int.cast_neg, Int.cast_ofNat]
  ring

lemma D_all_eq_lc5_mul :
    evalSQ_K5 D_all_expr = evalSQ_K5 lc5_fac_expr * evalSQ_K5 D_all_div_lc5_expr := by
  simp only [D_all_expr, lc5_fac_expr, D_all_div_lc5_expr, evalSQ_K5, ringEval]
  ring

-- Fast `PolyOps` evaluator for the 13 `Q5`/`Q7` recurrence & duality polynomials!

end SymmetricSexticResidual.LocalResidueQ5

theorem solution :
    (SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.fac_4 ≠ 0) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.D_all_expr ≠ 0) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.fac_4 =
      -SymmetricSexticResidual.LocalResidueU0.L_K) ∧
    (Polynomial.C (2893401 : SymmetricSexticResidual.K5Field.K5) *
        SymmetricSexticResidual.CoverAlgebra.k5Params.Q5_z =
      SymmetricSexticResidual.LocalResidueQ5.Q5_pol_K5) ∧
    (Polynomial.C (1640558367 : SymmetricSexticResidual.K5Field.K5) *
        SymmetricSexticResidual.CoverAlgebra.k5Params.Q7_z =
      Polynomial.C (2 : SymmetricSexticResidual.K5Field.K5) *
        SymmetricSexticResidual.LocalResidueQ5.Q7_pol_K5) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 (SymmetricSexticResidual.Q5WeightsData.Q5_c 5) =
      (SymmetricSexticResidual.Q5WeightsData.lc5_const : SymmetricSexticResidual.K5Field.K5) *
        SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.lc5_fac_expr) ∧
    (SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.D_all_expr =
      SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.lc5_fac_expr *
      SymmetricSexticResidual.LocalResidueQ5.evalSQ_K5 SymmetricSexticResidual.Q5WeightsData.D_all_div_lc5_expr) :=
  ⟨SymmetricSexticResidual.LocalResidueQ5.fac_4_ne,
   SymmetricSexticResidual.LocalResidueQ5.D_all_K5_ne,
   SymmetricSexticResidual.LocalResidueQ5.fac_4_eq_neg_L,
   SymmetricSexticResidual.LocalResidueQ5.Q5_K5_eq_scaled,
   SymmetricSexticResidual.LocalResidueQ5.Q7_K5_eq_scaled,
   SymmetricSexticResidual.LocalResidueQ5.Q5_c5_eq_fac,
   SymmetricSexticResidual.LocalResidueQ5.D_all_eq_lc5_mul⟩
