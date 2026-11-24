-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_ac_bridge
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:22:40.982705+00:00
-- url     : https://prove2.me/submissions/3137495e-9a61-431a-bcb7-4d39bfbdf258

import Definitions.Def_HodgeComputerSSR_Q5ACDefs

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  QuadraticCovers CrossedRationalResidue Polynomial PolynomialEncoding.KroneckerCheck
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len
open scoped BigOperators

section PureRingAC
variable {R : Type*} [Field R] [CharZero R]
lemma dHS_243_ring (a b U : R) :
    -25 * ((5 * a - 9 * b) * (15 * a - 9 * b)) +
    U * (429 * (a * a) - 1656 * (a * b) + 1404 * (b * b)) +
    U * (U * (-12 * ((a - 3 * b) * (a - 3 * b)))) = 243 * q1_a2 a b U 1 := by
  simp only [q1_a2, dH_dS]; ring

lemma dHQ0_27_ring (a b U : R) :
    50 * (a * (5 * a - 9 * b)) +
    U * (-92 * (a * a) + 312 * (a * b) - 198 * (b * b)) +
    U * (U * (4 * ((a - 3 * b) * (a - 3 * b)))) = 27 * q2_b2 a b U 1 := by
  simp only [q2_b2, dH_dQ]; ring

lemma dHS_bi_243_ring (S Q a b U : R) :
    -25 * ((15 * S - 9 * Q) * (5 * a - 9 * b) + (5 * S - 9 * Q) * (15 * a - 9 * b)) +
    U * (858 * S * a - 1656 * (S * b + Q * a) + 2808 * Q * b) +
    U * (U * (-24 * (S - 3 * Q) * (a - 3 * b))) = 243 * q1_a1 a b S Q U 1 := by
  simp only [q1_a1, dH_dS]; ring

lemma dHQ1_bi_189_ring (S Q a b U : R) :
    350 * ((10 * S - 9 * Q) * a - 9 * S * b) +
    U * (7 * (-184 * S * a + 312 * (S * b + Q * a) - 396 * Q * b) + 270 * b) +
    U * (U * (56 * (S - 3 * Q) * (a - 3 * b))) = 189 * q2_b1 a b S Q U 1 := by
  simp only [q2_b1, dH_dQ]; ring

end PureRingAC

lemma evalACache_K5_props :
    let m := fun mi : Fin 10 => numM_lead3 mi (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)
      (polyC k5Params.cb_h) (-polyC k5Params.ca_h) U_C 1
    let Cscale : A_C := 16 * 45927 * 567 ^ 4
    let T := ιC_K5 T_K
    (evalUPolyK5 acK.ca_p = Polynomial.C 567 * k5Params.ca_h) ∧
    (evalUPolyK5 acK.cb_p = Polynomial.C 567 * k5Params.cb_h) ∧
    ((evalUPolyK5 acK.ca_p).eval 0 = -175 * ((5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K))) ∧
    ((evalUPolyK5 acK.cb_p).eval 0 = 1050 * (S_K * (5 * S_K - 9 * Q_K))) ∧
    (acK.A0U_t0.headD 0 = 0 ∧ acK.A0U_t1.headD 0 = 0) ∧
    ((evalUPolyK5 acK.AY2_t0).eval 0 = 0 ∧ (evalUPolyK5 acK.AY2_t1).eval 0 = 0) ∧
    ((evalUPolyK5 acK.AX2_t0).eval 0 = 0 ∧ (evalUPolyK5 acK.AX2_t1).eval 0 = 0 ∧
      (evalUPolyK5 acK.AX2_t2).eval 0 = 0) ∧
    (polyC (evalUPolyK5 acK.Bv_SQ) =
      ιC_K5 (-175 * (S_K * (5 * S_K - 9 * Q_K) ^ 2)) +
      U_C * ιC_K5 (7 * (143 * S_K ^ 3 - 828 * S_K ^ 2 * Q_K + 1404 * S_K * Q_K ^ 2 - 594 * Q_K ^ 3) +
        1215 * Q_K ^ 2 + 2430 * Q_K) +
      U_C ^ 2 * ιC_K5 (-28 * (S_K - 3 * Q_K) ^ 3)) ∧
    (polyC (evalUPolyK5 acK.A0U_t0 + Polynomial.C T_K * evalUPolyK5 acK.A0U_t1) =
        ((-19708 * 187110 : ℤ) : A_C) * (5 * (Cscale * m 0) - 9 * (Cscale * m 1)) +
        ((1472 * 187110 : ℤ) : A_C) * (5 * (Cscale * m 1) - 9 * (Cscale * m 2)) +
        ((188 * 116181450 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) +
        T * (((-16 * 322726250 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) ∧
     polyC (evalUPolyK5 acK.A0V_t0 + Polynomial.C T_K * evalUPolyK5 acK.A0V_t1 +
          Polynomial.C (T_K ^ 2) * evalUPolyK5 acK.A0V_t2) =
        (((-892 * (-9) * 64545250 : ℤ) : A_C) * (Cscale * m 4) + ((40 * (-9) * 2904536250 : ℤ) : A_C) * (Cscale * m 6) +
          ((392 * (-9) * 19646550 : ℤ) : A_C) * (Cscale * m 9)) +
        T * (((-892 * 5 * 64545250 : ℤ) : A_C) * (Cscale * m 4) + ((40 * 5 * 2904536250 : ℤ) : A_C) * (Cscale * m 6) +
          ((-112 * (-9) * 98232750 : ℤ) : A_C) * (Cscale * m 9) + ((392 * 5 * 19646550 : ℤ) : A_C) * (Cscale * m 9)) +
        T ^ 2 * (((-112 * 5 * 98232750 : ℤ) : A_C) * (Cscale * m 9)) ∧
     polyC (evalUPolyK5 acK.AY2_t0 + Polynomial.C T_K * evalUPolyK5 acK.AY2_t1) =
        ((-9 : ℤ) : A_C) * (((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) +
        T * ((5 : ℤ) : A_C) * (((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) ∧
     polyC (evalUPolyK5 acK.AY3_t0 + Polynomial.C T_K * evalUPolyK5 acK.AY3_t1) =
        (((-907876 * 6930 : ℤ) : A_C) * (5 * (Cscale * m 0) - 9 * (Cscale * m 1)) +
          ((2258324 * 6930 : ℤ) : A_C) * (5 * (Cscale * m 1) - 9 * (Cscale * m 2)) -
          ((64 * 348544350 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) +
          U_C * (((-123236 * 126 : ℤ) : A_C) * (77 * (Cscale * m 0) + 2790 * (Cscale * m 6) - 5904 * (Cscale * m 9)) +
            ((492944 * 9 : ℤ) : A_C) * (770 * (Cscale * m 1) + 9270 * (Cscale * m 6) - 21159 * (Cscale * m 9)))) +
        T * (((8 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) +
          U_C * (((-123236 * 126 : ℤ) : A_C) * (2156 * (Cscale * m 9)) +
            ((492944 * 9 : ℤ) : A_C) * (7546 * (Cscale * m 9)))) ∧
     polyC (evalUPolyK5 acK.AX2_t0 + Polynomial.C T_K * evalUPolyK5 acK.AX2_t1 +
          Polynomial.C (T_K ^ 2) * evalUPolyK5 acK.AX2_t2) =
        U_C * (((-8 * (-9) * 580907250 : ℤ) : A_C) * (Cscale * m 4) + ((6916 * (-9) * 6548850 : ℤ) : A_C) * (Cscale * m 9)) +
        T * (U_C * (((-8 * 5 * 580907250 : ℤ) : A_C) * (Cscale * m 4) +
          ((-476 * (-9) * 32744250 : ℤ) : A_C) * (Cscale * m 9) + ((6916 * 5 * 6548850 : ℤ) : A_C) * (Cscale * m 9))) +
        T ^ 2 * (U_C * (((-476 * 5 * 32744250 : ℤ) : A_C) * (Cscale * m 9)))) := by
  intro m Cscale T
  let P : ACache K5 → Prop := fun ac =>
    (evalUPolyK5 ac.ca_p = Polynomial.C 567 * k5Params.ca_h) ∧
    (evalUPolyK5 ac.cb_p = Polynomial.C 567 * k5Params.cb_h) ∧
    ((evalUPolyK5 ac.ca_p).eval 0 = -175 * ((5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K))) ∧
    ((evalUPolyK5 ac.cb_p).eval 0 = 1050 * (S_K * (5 * S_K - 9 * Q_K))) ∧
    (ac.A0U_t0.headD 0 = 0 ∧ ac.A0U_t1.headD 0 = 0) ∧
    ((evalUPolyK5 ac.AY2_t0).eval 0 = 0 ∧ (evalUPolyK5 ac.AY2_t1).eval 0 = 0) ∧
    ((evalUPolyK5 ac.AX2_t0).eval 0 = 0 ∧ (evalUPolyK5 ac.AX2_t1).eval 0 = 0 ∧
      (evalUPolyK5 ac.AX2_t2).eval 0 = 0) ∧
    (polyC (evalUPolyK5 ac.Bv_SQ) =
      ιC_K5 (-175 * (S_K * (5 * S_K - 9 * Q_K) ^ 2)) +
      U_C * ιC_K5 (7 * (143 * S_K ^ 3 - 828 * S_K ^ 2 * Q_K + 1404 * S_K * Q_K ^ 2 - 594 * Q_K ^ 3) +
        1215 * Q_K ^ 2 + 2430 * Q_K) +
      U_C ^ 2 * ιC_K5 (-28 * (S_K - 3 * Q_K) ^ 3)) ∧
    (polyC (evalUPolyK5 ac.A0U_t0 + Polynomial.C T_K * evalUPolyK5 ac.A0U_t1) =
        ((-19708 * 187110 : ℤ) : A_C) * (5 * (Cscale * m 0) - 9 * (Cscale * m 1)) +
        ((1472 * 187110 : ℤ) : A_C) * (5 * (Cscale * m 1) - 9 * (Cscale * m 2)) +
        ((188 * 116181450 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) +
        T * (((-16 * 322726250 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) ∧
     polyC (evalUPolyK5 ac.A0V_t0 + Polynomial.C T_K * evalUPolyK5 ac.A0V_t1 +
          Polynomial.C (T_K ^ 2) * evalUPolyK5 ac.A0V_t2) =
        (((-892 * (-9) * 64545250 : ℤ) : A_C) * (Cscale * m 4) + ((40 * (-9) * 2904536250 : ℤ) : A_C) * (Cscale * m 6) +
          ((392 * (-9) * 19646550 : ℤ) : A_C) * (Cscale * m 9)) +
        T * (((-892 * 5 * 64545250 : ℤ) : A_C) * (Cscale * m 4) + ((40 * 5 * 2904536250 : ℤ) : A_C) * (Cscale * m 6) +
          ((-112 * (-9) * 98232750 : ℤ) : A_C) * (Cscale * m 9) + ((392 * 5 * 19646550 : ℤ) : A_C) * (Cscale * m 9)) +
        T ^ 2 * (((-112 * 5 * 98232750 : ℤ) : A_C) * (Cscale * m 9)) ∧
     polyC (evalUPolyK5 ac.AY2_t0 + Polynomial.C T_K * evalUPolyK5 ac.AY2_t1) =
        ((-9 : ℤ) : A_C) * (((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) +
        T * ((5 : ℤ) : A_C) * (((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) ∧
     polyC (evalUPolyK5 ac.AY3_t0 + Polynomial.C T_K * evalUPolyK5 ac.AY3_t1) =
        (((-907876 * 6930 : ℤ) : A_C) * (5 * (Cscale * m 0) - 9 * (Cscale * m 1)) +
          ((2258324 * 6930 : ℤ) : A_C) * (5 * (Cscale * m 1) - 9 * (Cscale * m 2)) -
          ((64 * 348544350 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) +
          U_C * (((-123236 * 126 : ℤ) : A_C) * (77 * (Cscale * m 0) + 2790 * (Cscale * m 6) - 5904 * (Cscale * m 9)) +
            ((492944 * 9 : ℤ) : A_C) * (770 * (Cscale * m 1) + 9270 * (Cscale * m 6) - 21159 * (Cscale * m 9)))) +
        T * (((8 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) +
          U_C * (((-123236 * 126 : ℤ) : A_C) * (2156 * (Cscale * m 9)) +
            ((492944 * 9 : ℤ) : A_C) * (7546 * (Cscale * m 9)))) ∧
     polyC (evalUPolyK5 ac.AX2_t0 + Polynomial.C T_K * evalUPolyK5 ac.AX2_t1 +
          Polynomial.C (T_K ^ 2) * evalUPolyK5 ac.AX2_t2) =
        U_C * (((-8 * (-9) * 580907250 : ℤ) : A_C) * (Cscale * m 4) + ((6916 * (-9) * 6548850 : ℤ) : A_C) * (Cscale * m 9)) +
        T * (U_C * (((-8 * 5 * 580907250 : ℤ) : A_C) * (Cscale * m 4) +
          ((-476 * (-9) * 32744250 : ℤ) : A_C) * (Cscale * m 9) + ((6916 * 5 * 6548850 : ℤ) : A_C) * (Cscale * m 9))) +
        T ^ 2 * (U_C * (((-476 * 5 * 32744250 : ℤ) : A_C) * (Cscale * m 9))))
  suffices h : P (evalACache k5Ops S_K Q_K) from h
  unfold evalACache
  refine letB_intro fun S2 hS2 => letB_intro fun SQ hSQ => letB_intro fun Q2 hQ2 =>
    letB_intro fun S3 hS3 => letB_intro fun Q3 hQ3 => letB_intro fun Sm3Q hSm3Q =>
    letB_intro fun Sm3Q2 hSm3Q2 => letB_intro fun A5 hA5 =>
    letB_intro fun ca0 hca0 => letB_intro fun ca1 hca1 => letB_intro fun ca2 hca2 => letB_intro fun ca_p hca_p =>
    letB_intro fun cb0 hcb0 => letB_intro fun cb1 hcb1 => letB_intro fun cb2 hcb2 => letB_intro fun cb_p hcb_p =>
    letB_intro fun b_p hb_p => letB_intro fun am3b_p ham3b_p =>
    letB_intro fun a5m9b ha5m9b => letB_intro fun a15m9b ha15m9b =>
    letB_intro fun aa haa => letB_intro fun ab hab => letB_intro fun bb hbb => letB_intro fun am3b2 ham3b2 =>
    letB_intro fun A2 hA2 => letB_intro fun B2 hB2 => letB_intro fun S15m9Q hS15m9Q => letB_intro fun sbqa hsbqa =>
    letB_intro fun A1 hA1 => letB_intro fun B1 hB1 =>
    letB_intro fun D21 hD21 => letB_intro fun D20 hD20 => letB_intro fun D10 hD10 =>
    letB_intro fun m0 hm0 => letB_intro fun m1 hm1 => letB_intro fun m2 hm2 => letB_intro fun m4 hm4 => letB_intro fun m6 hm6 =>
    letB_intro fun l01 hl01 => letB_intro fun l12 hl12 => letB_intro fun l46 hl46 => letB_intro fun AY2_base hAY2_base =>
    letB_intro fun Bv0_1701 hBv0 => letB_intro fun Bv1_243_S hBv1S =>
    letB_intro fun Bv1_SQ_1701 hBv1SQ => letB_intro fun Bv2_1701 hBv2 => ?_
  dsimp only [P]
  have hS2' : S2 = S_K * S_K := hS2
  have hSQ' : SQ = S_K * Q_K := hSQ
  have hQ2' : Q2 = Q_K * Q_K := hQ2
  have hS3' : S3 = S_K ^ 3 := by rw [hS3, hS2']; dsimp only [k5Ops, ringOps]; ring
  have hQ3' : Q3 = Q_K ^ 3 := by rw [hQ3, hQ2']; dsimp only [k5Ops, ringOps]; ring
  have hSm3Q' : Sm3Q = S_K - 3 * Q_K := by rw [hSm3Q]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hSm3Q2' : Sm3Q2 = (S_K - 3 * Q_K) ^ 2 := by rw [hSm3Q2, hSm3Q']; dsimp only [k5Ops, ringOps]; ring
  have hA5' : A5 = 5 * S_K - 9 * Q_K := by rw [hA5]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hS15m9Q' : S15m9Q = 15 * S_K - 9 * Q_K := by rw [hS15m9Q]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hca0' : ca0 = -175 * ((5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) := by
    rw [hca0, hA5']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hca1' : ca1 = 7 * (143 * S_K ^ 2 - 552 * (S_K * Q_K) + 468 * Q_K ^ 2) := by
    rw [hca1, hS2', hSQ', hQ2']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hca2' : ca2 = -28 * (S_K - 3 * Q_K) ^ 2 := by rw [hca2, hSm3Q2']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hcb0' : cb0 = 1050 * (S_K * (5 * S_K - 9 * Q_K)) := by rw [hcb0, hA5']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hcb1' : cb1 = 21 * (-92 * S_K ^ 2 + 312 * (S_K * Q_K) - 198 * Q_K ^ 2) + 810 * Q_K + 810 := by
    rw [hcb1, hS2', hSQ', hQ2']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hcb2' : cb2 = 84 * (S_K - 3 * Q_K) ^ 2 := by rw [hcb2, hSm3Q2']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hca_K : evalUPolyK5 ca_p = Polynomial.C 567 * k5Params.ca_h := by
    have hinf : Infinite K5 := Infinite.of_injective (Nat.cast : ℕ → K5) Nat.cast_injective
    apply Polynomial.funext; intro u
    rw [hca_p]; simp only [evalUPolyK5, evalUPoly, hca0', hca1', hca2', CoverParams.ca_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero]; ring
  have hcb_K : evalUPolyK5 cb_p = Polynomial.C 567 * k5Params.cb_h := by
    have hinf : Infinite K5 := Infinite.of_injective (Nat.cast : ℕ → K5) Nat.cast_injective
    apply Polynomial.funext; intro u
    rw [hcb_p]; simp only [evalUPolyK5, evalUPoly, hcb0', hcb1', hcb2', CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero]; ring
  have hca_e0 : (evalUPolyK5 ca_p).eval 0 = ca0 := by rw [hca_p]; simp [evalUPolyK5, evalUPoly]
  have hcb_e0 : (evalUPolyK5 cb_p).eval 0 = cb0 := by rw [hcb_p]; simp [evalUPolyK5, evalUPoly]
  -- Evaluate `l01, l12, l46` at `U = 0` in O(N) steps!
  have he0_b : (evalUPolyK5 b_p).eval 0 = -ca0 := by rw [hb_p, evalUPolyK5_uNeg, Polynomial.eval_neg, hca_e0]
  have he0_a5 : (evalUPolyK5 a5m9b).eval 0 = 5 * cb0 - 9 * (-ca0) := by
    rw [ha5m9b, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]; simp [k5Ops, ringOps, hcb_e0, he0_b]
  have he0_a15 : (evalUPolyK5 a15m9b).eval 0 = 15 * cb0 - 9 * (-ca0) := by
    rw [ha15m9b, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]; simp [k5Ops, ringOps, hcb_e0, he0_b]
  have he0_aa : (evalUPolyK5 aa).eval 0 = cb0 * cb0 := by rw [haa, evalUPolyK5_uMul]; simp [hcb_e0]
  have he0_ab : (evalUPolyK5 ab).eval 0 = cb0 * (-ca0) := by rw [hab, evalUPolyK5_uMul]; simp [hcb_e0, he0_b]
  have he0_bb : (evalUPolyK5 bb).eval 0 = (-ca0) * (-ca0) := by rw [hbb, evalUPolyK5_uMul]; simp [he0_b]
  have he0_sbqa : (evalUPolyK5 sbqa).eval 0 = S_K * (-ca0) + Q_K * cb0 := by
    rw [hsbqa, evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uSc]; simp [hcb_e0, he0_b]
  set A2_0 : K5 := -25 * ((5 * cb0 - 9 * (-ca0)) * (15 * cb0 - 9 * (-ca0)))
  set B2_0 : K5 := 50 * (cb0 * (5 * cb0 - 9 * (-ca0)))
  set A1_0 : K5 := -25 * ((15 * S_K - 9 * Q_K) * (5 * cb0 - 9 * (-ca0)) + A5 * (15 * cb0 - 9 * (-ca0)))
  set B1_0 : K5 := 350 * ((10 * S_K - 9 * Q_K) * cb0 - 9 * S_K * (-ca0))
  set D21_0 : K5 := 567 * (A2_0 * B1_0 - 7 * (A1_0 * B2_0))
  set D20_0 : K5 := 189 * (A2_0 * cb0) - 1701 * (ca0 * B2_0)
  set D10_0 : K5 := 189 * (A1_0 * cb0) - 243 * (ca0 * B1_0)
  have he0_A2 : (evalUPolyK5 A2).eval 0 = A2_0 := by
    rw [hA2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uMul, evalUPolyK5_uShift,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, 
      he0_a5, he0_a15]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, mul_zero, zero_mul, add_zero]; rfl
  have he0_B2 : (evalUPolyK5 B2).eval 0 = B2_0 := by
    rw [hB2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uMul, evalUPolyK5_uShift,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, 
      hcb_e0, he0_a5]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, mul_zero, zero_mul, add_zero]; rfl
  have he0_A1 : (evalUPolyK5 A1).eval 0 = A1_0 := by
    rw [hA1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uShift,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, 
      he0_a5, he0_a15, hS15m9Q']; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, mul_zero, zero_mul, add_zero]; rfl
  have he0_B1 : (evalUPolyK5 B1).eval 0 = B1_0 := by
    rw [hB1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      hcb_e0, he0_b]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, mul_zero, zero_mul, add_zero]; rfl
  have he0_D21 : (evalUPolyK5 D21).eval 0 = D21_0 := by
    rw [hD21]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, he0_A2, he0_B1, he0_A1, he0_B2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat]; rfl
  have he0_D20 : (evalUPolyK5 D20).eval 0 = D20_0 := by
    rw [hD20]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, he0_A2, hcb_e0, hca_e0, he0_B2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat]; rfl
  have he0_D10 : (evalUPolyK5 D10).eval 0 = D10_0 := by
    rw [hD10]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, he0_A1, hcb_e0, hca_e0, he0_B1]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat]; rfl
  have he0_m0 : (evalUPolyK5 m0).eval 0 = cb0 * cb0 * D10_0 - 2 * S_K * (cb0 * D20_0) + S_K * S_K * D21_0 := by
    rw [hm0]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      he0_aa, he0_D10, hcb_e0, he0_D20, hS2', he0_D21]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat]
  have he0_m1 : (evalUPolyK5 m1).eval 0 = cb0 * (-ca0) * D10_0 - (S_K * (-ca0) + Q_K * cb0) * D20_0 + S_K * Q_K * D21_0 := by
    rw [hm1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      he0_ab, he0_D10, he0_sbqa, he0_D20, hSQ', he0_D21]
  have he0_m2 : (evalUPolyK5 m2).eval 0 = (-ca0) * (-ca0) * D10_0 - 2 * Q_K * ((-ca0) * D20_0) + Q_K * Q_K * D21_0 := by
    rw [hm2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      he0_bb, he0_D10, he0_b, he0_D20, hQ2', he0_D21]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat]
  have he0_m4 : (evalUPolyK5 m4).eval 0 = S_K * D21_0 - cb0 * D20_0 := by
    rw [hm4]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hcb_e0, he0_D21, he0_D20]
  have he0_m6 : (evalUPolyK5 m6).eval 0 = Q_K * D21_0 - (-ca0) * D20_0 := by
    rw [hm6]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, he0_b, he0_D21, he0_D20]
  have h5a9b : 5 * cb0 - 9 * (-ca0) = -525 * A5 ^ 2 := by rw [hcb0', hca0', hA5']; ring
  have hD20_0 : D20_0 = -525 * A5 * D10_0 := by
    dsimp only [D20_0, D10_0, A2_0, B2_0, A1_0, B1_0]; rw [hcb0', hca0', hA5']; ring
  have hD21_0 : D21_0 = -525 * A5 * D20_0 := by
    dsimp only [D21_0, D20_0, A2_0, B2_0, A1_0, B1_0]; rw [hcb0', hca0', hA5']; ring
  have he0_l46 : (evalUPolyK5 l46).eval 0 = 0 := by
    rw [hl46]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, he0_m4, he0_m6]; dsimp only [k5Ops, ringOps]; push_cast
    linear_combination A5 * hD21_0 - D20_0 * h5a9b + D21_0 * hA5'.symm
  have he0_l01 : (evalUPolyK5 l01).eval 0 = 0 := by
    rw [hl01]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, he0_m0, he0_m1]; dsimp only [k5Ops, ringOps]; push_cast
    linear_combination (cb0 * D10_0 - S_K * D20_0) * h5a9b - cb0 * A5 * hD20_0 +
      S_K * A5 * hD21_0 + (S_K * D21_0 - cb0 * D20_0) * hA5'.symm
  have he0_l12 : (evalUPolyK5 l12).eval 0 = 0 := by
    rw [hl12]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, he0_m1, he0_m2]; dsimp only [k5Ops, ringOps]; push_cast
    linear_combination ((-ca0) * D10_0 - Q_K * D20_0) * h5a9b - (-ca0) * A5 * hD20_0 +
      Q_K * A5 * hD21_0 + (Q_K * D21_0 - (-ca0) * D20_0) * hA5'.symm
  have hhead : ∀ (p : UPoly K5), p.headD 0 = (evalUPolyK5 p).eval 0 := fun p => by cases p <;> simp [evalUPolyK5, evalUPoly]
  -- Evaluate every node in `A_C` in O(N) steps!
  set S := ιC_K5 S_K; set Q := ιC_K5 Q_K
  set ca := polyC k5Params.ca_h; set cb := polyC k5Params.cb_h
  set a := (567 : A_C) * cb; set b := -((567 : A_C) * ca)
  have hp_ca : polyC (evalUPolyK5 ca_p) = 567 * ca := by rw [hca_K, polyC_mul, polyC_C]; simp [ca, map_ofNat]
  have hp_cb : polyC (evalUPolyK5 cb_p) = a := by rw [hcb_K, polyC_mul, polyC_C]; simp [a, cb, map_ofNat]
  have hp_b : polyC (evalUPolyK5 b_p) = b := by rw [hb_p, evalUPolyK5_uNeg, polyC_neg, hp_ca]
  have hp_am3b : polyC (evalUPolyK5 am3b_p) = a - 3 * b := by
    have hca_ex : polyC (evalUPolyK5 ca_p) = ιC_K5 ca0 + U_C * (ιC_K5 ca1 + U_C * ιC_K5 ca2) := by
      rw [hca_p]; simp only [evalUPolyK5, evalUPoly, polyC_add, polyC_mul, polyC_C, polyC_X, mul_zero, add_zero]
    have hcb_ex : polyC (evalUPolyK5 cb_p) = ιC_K5 cb0 + U_C * (ιC_K5 cb1 + U_C * ιC_K5 cb2) := by
      rw [hcb_p]; simp only [evalUPolyK5, evalUPoly, polyC_add, polyC_mul, polyC_C, polyC_X, mul_zero, add_zero]
    have h2 : cb2 - 3 * (-ca2) = 0 := by rw [hcb2', hca2']; ring
    have h2C : ιC_K5 cb2 + 3 * ιC_K5 ca2 = 0 := by
      have := congrArg ιC_K5 h2; simp only [map_sub, map_mul, map_neg, map_ofNat, map_zero] at this
      linear_combination this
    rw [ham3b_p]; simp only [evalUPolyK5, evalUPoly, k5Ops, ringOps, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_C, polyC_X, polyC_ofNat,
      map_sub, map_mul, map_neg, map_ofNat, mul_zero, add_zero, Int.cast_ofNat]
    rw [← hp_cb, ← hp_b, hb_p, evalUPolyK5_uNeg, polyC_neg, hca_ex, hcb_ex]
    linear_combination -U_C ^ 2 * h2C
  have hp_a5 : polyC (evalUPolyK5 a5m9b) = 5 * a - 9 * b := by
    rw [ha5m9b, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_cb, hp_b]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]
  have hp_a15 : polyC (evalUPolyK5 a15m9b) = 15 * a - 9 * b := by
    rw [ha15m9b, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_cb, hp_b]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]
  have hp_aa : polyC (evalUPolyK5 aa) = a * a := by rw [haa, evalUPolyK5_uMul, polyC_mul, hp_cb]
  have hp_ab : polyC (evalUPolyK5 ab) = a * b := by rw [hab, evalUPolyK5_uMul, polyC_mul, hp_cb, hp_b]
  have hp_bb : polyC (evalUPolyK5 bb) = b * b := by rw [hbb, evalUPolyK5_uMul, polyC_mul, hp_b]
  have hp_am3b2 : polyC (evalUPolyK5 am3b2) = (a - 3 * b) * (a - 3 * b) := by
    rw [ham3b2, evalUPolyK5_uMul, polyC_mul, hp_am3b]
  have hp_sbqa : polyC (evalUPolyK5 sbqa) = S * b + Q * a := by
    rw [hsbqa, evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uSc]; simp [polyC_add, polyC_mul, polyC_C, hp_cb, hp_b, S, Q]
  set A2_v : A_C := 243 * q1_a2 a b U_C 1
  set B2_v : A_C := 27 * q2_b2 a b U_C 1
  set A1_v : A_C := 243 * q1_a1 a b S Q U_C 1
  set B1_v : A_C := 189 * q2_b1 a b S Q U_C 1
  set D21_v : A_C := 567 * (A2_v * B1_v - 7 * (A1_v * B2_v))
  set D20_v : A_C := 189 * (A2_v * a) - 1701 * (567 * ca * B2_v)
  set D10_v : A_C := 189 * (A1_v * a) - 243 * (567 * ca * B1_v)
  have hp_A2 : polyC (evalUPolyK5 A2) = A2_v := by
    rw [hA2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift, evalUPolyK5_uMul, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, 
      hp_a5, hp_a15, hp_aa, hp_ab, hp_bb, hp_am3b2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_ofNat]
    exact dHS_243_ring a b U_C
  have hp_B2 : polyC (evalUPolyK5 B2) = B2_v := by
    rw [hB2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift, evalUPolyK5_uMul, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, 
      hp_cb, hp_a5, hp_aa, hp_ab, hp_bb, hp_am3b2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_ofNat]
    exact dHQ0_27_ring a b U_C
  have hp_A1 : polyC (evalUPolyK5 A1) = A1_v := by
    rw [hA1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, polyC_ofNat, hS15m9Q', hA5', hSm3Q',
      map_sub, map_mul, map_ofNat, 
      hp_a5, hp_a15, hp_cb, hp_sbqa, hp_b, hp_am3b]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_sub, map_ofNat]
    change _ = 243 * q1_a1 a b S Q U_C 1
    rw [← dHS_bi_243_ring S Q a b U_C]
  have hp_B1 : polyC (evalUPolyK5 B1) = B1_v := by
    rw [hB1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, hSm3Q',
      hp_cb, hp_b, hp_sbqa, hp_am3b]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_sub, map_ofNat]
    change _ = 189 * q2_b1 a b S Q U_C 1
    rw [← dHQ1_bi_189_ring S Q a b U_C]
  have hp_D21 : polyC (evalUPolyK5 D21) = D21_v := by
    rw [hD21]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, hp_A2, hp_B1, hp_A1, hp_B2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]; rfl
  have hp_D20 : polyC (evalUPolyK5 D20) = D20_v := by
    rw [hD20]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, hp_A2, hp_cb, hp_ca, hp_B2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]; rfl
  have hp_D10 : polyC (evalUPolyK5 D10) = D10_v := by
    rw [hD10]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, hp_A1, hp_cb, hp_ca, hp_B1]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]; rfl
  have ha2_eq : q1_a2 a b U_C 1 = (567 : A_C) ^ 2 * q1_a2 cb (-ca) U_C 1 := by simp only [a, b, q1_a2, dH_dS]; ring
  have hb2_eq : q2_b2 a b U_C 1 = (567 : A_C) ^ 2 * q2_b2 cb (-ca) U_C 1 := by simp only [a, b, q2_b2, dH_dQ]; ring
  have ha1_eq : q1_a1 a b S Q U_C 1 = (567 : A_C) * q1_a1 cb (-ca) S Q U_C 1 := by simp only [a, b, q1_a1, dH_dS]; ring
  have hb1_eq : q2_b1 a b S Q U_C 1 = (567 : A_C) * q2_b1 cb (-ca) S Q U_C 1 := by simp only [a, b, q2_b1, dH_dQ]; ring
  have hca_q : ca = q1_a0 S Q U_C 1 := polyC_ca_cb_eq_q10_q20.1
  have hcb_q : cb = q2_b0 S Q U_C 1 := polyC_ca_cb_eq_q10_q20.2
  have hD21_m : D21_v = Cscale * m 9 := by
    simp only [D21_v, A2_v, B2_v, A1_v, B1_v, ha2_eq, hb2_eq, ha1_eq, hb1_eq, Cscale, m, numM_lead3]; ring
  have hD20_m : D20_v = 45927 * 567 ^ 3 * (q1_a2 cb (-ca) U_C 1 * q2_b0 S Q U_C 1 - q1_a0 S Q U_C 1 * q2_b2 cb (-ca) U_C 1) := by
    dsimp only [D20_v, A2_v, B2_v]; rw [ha2_eq, hb2_eq]; simp only [a, hca_q, hcb_q]; ring
  have hD10_m : D10_v = 45927 * 567 ^ 2 * (q1_a1 cb (-ca) S Q U_C 1 * q2_b0 S Q U_C 1 - q1_a0 S Q U_C 1 * q2_b1 cb (-ca) S Q U_C 1) := by
    dsimp only [D10_v, A1_v, B1_v]; rw [ha1_eq, hb1_eq]; simp only [a, hca_q, hcb_q]; ring
  have hp_m0 : polyC (evalUPolyK5 m0) = Cscale * m 0 := by
    rw [hm0]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_add, polyC_sub, polyC_mul, polyC_C, hS2', map_mul, 
      hp_aa, hp_D10, hp_cb, hp_D20, hp_D21, hD21_m, hD20_m, hD10_m, Cscale, m, numM_lead3, a, S]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_mul, map_ofNat]; ring
  have hp_m1 : polyC (evalUPolyK5 m1) = Cscale * m 1 := by
    rw [hm1]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_add, polyC_sub, polyC_mul, polyC_C, hSQ', map_mul,
      hp_ab, hp_D10, hp_sbqa, hp_D20, hp_D21, hD21_m, hD20_m, hD10_m, Cscale, m, numM_lead3, a, b, S, Q]; ring
  have hp_m2 : polyC (evalUPolyK5 m2) = Cscale * m 2 := by
    rw [hm2]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_add, polyC_sub, polyC_mul, polyC_C, hQ2', map_mul, 
      hp_bb, hp_D10, hp_b, hp_D20, hp_D21, hD21_m, hD20_m, hD10_m, Cscale, m, numM_lead3, b, Q]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_mul, map_ofNat]; ring
  have hp_m4 : polyC (evalUPolyK5 m4) = Cscale * m 4 := by
    rw [hm4]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, hp_D21, hp_cb, hp_D20, hD21_m, hD20_m, Cscale, m, numM_lead3, a, S]; ring
  have hp_m6 : polyC (evalUPolyK5 m6) = Cscale * m 6 := by
    rw [hm6]; simp only [evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uMul,
      polyC_sub, polyC_mul, polyC_C, hp_D21, hp_b, hp_D20, hD21_m, hD20_m, Cscale, m, numM_lead3, b, Q]; ring
  have hp_l01 : polyC (evalUPolyK5 l01) = 5 * (Cscale * m 0) - 9 * (Cscale * m 1) := by
    rw [hl01, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_m0, hp_m1]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]
  have hp_l12 : polyC (evalUPolyK5 l12) = 5 * (Cscale * m 1) - 9 * (Cscale * m 2) := by
    rw [hl12, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_m1, hp_m2]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]
  have hp_l46 : polyC (evalUPolyK5 l46) = 5 * (Cscale * m 4) - 9 * (Cscale * m 6) := by
    rw [hl46, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uSc]
    simp only [polyC_sub, polyC_mul, polyC_C, hp_m4, hp_m6]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_ofNat]
  have hp_AY2b : polyC (evalUPolyK5 AY2_base) = ((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6)) := by
    rw [hAY2_base, evalUPolyK5_uSc, polyC_mul, polyC_C, hp_l46]; dsimp only [k5Ops, ringOps]; simp only [map_intCast]
  refine ⟨hca_K, hcb_K, by rw [hca_e0, hca0'], by rw [hcb_e0, hcb0'], ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hhead]; simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, he0_l01, he0_l12, he0_l46, mul_zero, add_zero]
  · rw [hhead]; simp only [evalUPolyK5_uSc, Polynomial.eval_mul, Polynomial.eval_C, he0_l46, mul_zero]
  · simp only [evalUPolyK5_uSc, hAY2_base, Polynomial.eval_mul, Polynomial.eval_C, he0_l46, mul_zero]
  · simp only [evalUPolyK5_uSc, hAY2_base, Polynomial.eval_mul, Polynomial.eval_C, he0_l46, mul_zero]
  · simp [evalUPolyK5_uShift]
  · simp [evalUPolyK5_uShift]
  · simp [evalUPolyK5_uShift]
  · simp only [evalUPolyK5, evalUPoly, polyC_add, polyC_mul, polyC_C, polyC_X, mul_zero, add_zero]
    have h0 : Bv0_1701 = -175 * (S_K * (5 * S_K - 9 * Q_K) ^ 2) := by rw [hBv0, hA5']; dsimp only [k5Ops, ringOps]; push_cast; ring
    have h1 : Bv1_SQ_1701 = 7 * (143 * S_K ^ 3 - 828 * S_K ^ 2 * Q_K + 1404 * S_K * Q_K ^ 2 - 594 * Q_K ^ 3) +
        1215 * Q_K ^ 2 + 2430 * Q_K := by
      rw [hBv1SQ, hBv1S, hS3', hS2', hQ2', hQ3']; dsimp only [k5Ops, ringOps]; push_cast; ring
    have h2 : Bv2_1701 = -28 * (S_K - 3 * Q_K) ^ 3 := by rw [hBv2, hSm3Q2', hSm3Q']; dsimp only [k5Ops, ringOps]; push_cast; ring
    rw [h0, h1, h2]; ring
  · simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, polyC_add, polyC_mul, polyC_C,
      hp_l01, hp_l12, hp_l46]; dsimp only [k5Ops, ringOps, T]; simp only [map_intCast]
  · simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, polyC_add, polyC_mul, polyC_pow, polyC_C,
      map_pow, hp_m4, hp_m6, hp_D21, hD21_m]; dsimp only [k5Ops, ringOps, T]; simp only [map_intCast]
  · simp only [evalUPolyK5_uSc, polyC_add, polyC_mul, polyC_C, hp_AY2b]; dsimp only [k5Ops, ringOps, T]; simp only [map_intCast]
    generalize (((-100 * 968178750 : ℤ) : A_C) * (5 * (Cscale * m 4) - 9 * (Cscale * m 6))) = Z
    generalize ιC_K5 T_K = t; ring
  · simp only [evalUPolyK5_uAdd, evalUPolyK5_uSub, evalUPolyK5_uSc, evalUPolyK5_uShift,
      polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X,
      hp_l01, hp_l12, hp_l46, hp_m0, hp_m1, hp_m6, hp_D21, hD21_m]; dsimp only [k5Ops, ringOps, T]; simp only [map_intCast, Int.cast_ofNat, map_ofNat]
  · simp only [evalUPolyK5_uAdd, evalUPolyK5_uSc, evalUPolyK5_uShift,
      polyC_add, polyC_mul, polyC_pow, polyC_C, polyC_X, map_pow, hp_m4, hp_D21, hD21_m]; dsimp only [k5Ops, ringOps, T]; simp only [map_intCast]

lemma evalUPolyK5_ca_cb :
    evalUPolyK5 acK.ca_p = Polynomial.C 567 * k5Params.ca_h ∧
    evalUPolyK5 acK.cb_p = Polynomial.C 567 * k5Params.cb_h :=
  ⟨evalACache_K5_props.1, evalACache_K5_props.2.1⟩

lemma A0U_head_zero :
    acK.A0U_t0.headD 0 = 0 ∧ acK.A0U_t1.headD 0 = 0 :=
  evalACache_K5_props.2.2.2.2.1

lemma evalACache_AC_bridge :
    let m := fun mi : Fin 10 => numM_lead3 mi (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)
      (polyC k5Params.cb_h) (-polyC k5Params.ca_h) U_C 1
    let MA : A_C := (M_A_int : A_C)
    (U_C * polyC A0U_U_p = MA * (-(19708 / 1257375 : A_C) * (5 * m 0 - 9 * m 1) +
        (1472 / 1257375 : A_C) * (5 * m 1 - 9 * m 2) - (16 / 729 : A_C) * (5 * m 3 - 9 * m 5) +
        (188 / 2025 : A_C) * (5 * m 4 - 9 * m 6))) ∧
    (polyC A0V_p = MA * (-(892 / 3645 : A_C) * (5 * m 3 - 9 * m 4) + (40 / 81 : A_C) * (5 * m 5 - 9 * m 6) -
        (112 / 2395 : A_C) * (5 * m 7 - 9 * m 8) + (392 / 11975 : A_C) * (5 * m 8 - 9 * m 9))) ∧
    (polyC AY2_p = MA * (-(100 / 243 : A_C) * (25 * m 3 - 45 * m 4 - 45 * m 5 + 81 * m 6))) ∧
    (polyC AY3_p = MA * (-(907876 / 33949125 : A_C) * (5 * m 0 - 9 * m 1) +
        (2258324 / 33949125 : A_C) * (5 * m 1 - 9 * m 2) + (8 / 243 : A_C) * (5 * m 3 - 9 * m 5) -
        (64 / 675 : A_C) * (5 * m 4 - 9 * m 6) +
        U_C * (-(123236 / 24249375 : A_C) * (m 0 + (2790 / 77 : A_C) * m 6 + 28 * m 8 - (5904 / 77 : A_C) * m 9) +
          (492944 / 33949125 : A_C) * (m 1 + (927 / 77 : A_C) * m 6 + (49 / 5 : A_C) * m 8 - (21159 / 770 : A_C) * m 9)))) ∧
    (polyC AX2_p = MA * (U_C * (-(8 / 405 : A_C) * (5 * m 3 - 9 * m 4) -
        (476 / 7185 : A_C) * (5 * m 7 - 9 * m 8) + (6916 / 35925 : A_C) * (5 * m 8 - 9 * m 9)))) := by
  intro m MA
  have hA0U_eq : Polynomial.X * A0U_U_p = evalUPolyK5 acK.A0U_t0 + Polynomial.C T_K * evalUPolyK5 acK.A0U_t1 := by
    have h0 := evalUPolyK5_uTail acK.A0U_t0
    have h1 := evalUPolyK5_uTail acK.A0U_t1
    rw [A0U_head_zero.1, map_zero, zero_add] at h0
    rw [A0U_head_zero.2, map_zero, zero_add] at h1
    simp only [A0U_U_p, h0, h1]; ring
  rw [show U_C * polyC A0U_U_p = polyC (evalUPolyK5 acK.A0U_t0 + Polynomial.C T_K * evalUPolyK5 acK.A0U_t1) by
    rw [← polyC_X, ← polyC_mul, hA0U_eq]]
  set T := ιC_K5 T_K
  set Cscale : A_C := 16 * 45927 * 567 ^ 4
  have hrat_L (p q r : ℤ) (hq : q ≠ 0) (hmul : p * L_all_A = r * q) :
      ((p : A_C) / (q : A_C)) * (L_all_A : A_C) = (r : A_C) := by
    have hqA : (q : A_C) ≠ 0 := Int.cast_ne_zero.mpr hq
    have hZ : (p : A_C) * (L_all_A : A_C) = (r : A_C) * (q : A_C) := by exact_mod_cast hmul
    rw [div_mul_eq_mul_div, hZ, mul_div_cancel_right₀ _ hqA]
  have hMA_split : MA = (L_all_A : A_C) * Cscale := by
    simp only [MA, M_A_int, Cscale, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]; ring
  have hm3 : m 3 = T * m 4 := by simp [m, numM_lead3, T]; ring
  have hm5 : m 5 = T * m 6 := by simp [m, numM_lead3, T]; ring
  have hm8 : m 8 = T * m 9 := by simp [m, numM_lead3, T]; ring
  have hm7 : m 7 = T ^ 2 * m 9 := by simp [m, numM_lead3, T]; ring
  have hA_eval := evalACache_K5_props.2.2.2.2.2.2.2.2
  dsimp only [A0V_p, AY2_p, AY3_p, AX2_p]
  rw [hA_eval.1, hA_eval.2.1, hA_eval.2.2.1, hA_eval.2.2.2.1, hA_eval.2.2.2.2,
    hMA_split, hm3, hm5, hm8, hm7]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 := hrat_L (-19708) 1257375 (-19708 * 187110) (by decide) (by unfold L_all_A; decide)
    have h2 := hrat_L 1472 1257375 (1472 * 187110) (by decide) (by unfold L_all_A; decide)
    have h3 := hrat_L (-16) 729 (-16 * 322726250) (by decide) (by unfold L_all_A; decide)
    have h4 := hrat_L 188 2025 (188 * 116181450) (by decide) (by unfold L_all_A; decide)
    rw [← h1, ← h2, ← h3, ← h4]
    simp only [Int.cast_neg, Int.cast_ofNat, neg_div]
    generalize (L_all_A : A_C) = Lc
    generalize (19708 / 1257375 : A_C) = c1; generalize (1472 / 1257375 : A_C) = c2
    generalize (16 / 729 : A_C) = c3; generalize (188 / 2025 : A_C) = c4
    ring
  · have h1 := hrat_L (-892) 3645 (-892 * 64545250) (by decide) (by unfold L_all_A; decide)
    have h2 := hrat_L 40 81 (40 * 2904536250) (by decide) (by unfold L_all_A; decide)
    have h3 := hrat_L (-112) 2395 (-112 * 98232750) (by decide) (by unfold L_all_A; decide)
    have h4 := hrat_L 392 11975 (392 * 19646550) (by decide) (by unfold L_all_A; decide)
    have hsc : ∀ (a b c : ℤ), ((a * b * c : ℤ) : A_C) = (b : A_C) * ((a * c : ℤ) : A_C) := fun a b c => by
      push_cast; ring
    rw [hsc (-892) (-9) 64545250, hsc 40 (-9) 2904536250, hsc 392 (-9) 19646550,
        hsc (-892) 5 64545250, hsc 40 5 2904536250, hsc (-112) (-9) 98232750,
        hsc 392 5 19646550, hsc (-112) 5 98232750, ← h1, ← h2, ← h3, ← h4]
    simp only [Int.cast_neg, Int.cast_ofNat, neg_div]
    generalize (L_all_A : A_C) = Lc
    generalize (892 / 3645 : A_C) = c1; generalize (40 / 81 : A_C) = c2
    generalize (112 / 2395 : A_C) = c3; generalize (392 / 11975 : A_C) = c4
    ring
  · have h1 := hrat_L (-100) 243 (-100 * 968178750) (by decide) (by unfold L_all_A; decide)
    rw [← h1]
    simp only [Int.cast_neg, Int.cast_ofNat, neg_div]
    generalize (L_all_A : A_C) = Lc; generalize (100 / 243 : A_C) = c1
    ring
  · have h1 := hrat_L (-907876) 33949125 (-907876 * 6930) (by decide) (by unfold L_all_A; decide)
    have h2 := hrat_L 2258324 33949125 (2258324 * 6930) (by decide) (by unfold L_all_A; decide)
    have h3 := hrat_L 8 243 (8 * 968178750) (by decide) (by unfold L_all_A; decide)
    have h4 := hrat_L (-64) 675 (-64 * 348544350) (by decide) (by unfold L_all_A; decide)
    have h5 := hrat_L (-123236) (24249375 * 77) (-123236 * 126) (by decide) (by unfold L_all_A; decide)
    have h6 := hrat_L 492944 (33949125 * 770) (492944 * 9) (by decide) (by unfold L_all_A; decide)
    have h4' : ((64 * 348544350 : ℤ) : A_C) = -((-64 * 348544350 : ℤ) : A_C) := by
      have : ((64 * 348544350 : ℤ) : A_C) = ((-(-64 * 348544350) : ℤ) : A_C) := by congr 1
      rw [this, Int.cast_neg]
    rw [h4', ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
    rw [show (((-123236 : ℤ) : A_C) / (((24249375 * 77 : ℤ) : A_C))) = -(123236 / 24249375 : A_C) / 77 by
      simp only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, neg_div, div_mul_eq_div_div]]
    rw [show (((492944 : ℤ) : A_C) / (((33949125 * 770 : ℤ) : A_C))) = (492944 / 33949125 : A_C) / 770 by
      simp only [Int.cast_mul, Int.cast_ofNat, div_mul_eq_div_div]]
    simp only [Int.cast_neg, Int.cast_ofNat, neg_div]
    generalize (L_all_A : A_C) = Lc
    generalize (907876 / 33949125 : A_C) = c1; generalize (2258324 / 33949125 : A_C) = c2
    generalize (8 / 243 : A_C) = c3; generalize (64 / 675 : A_C) = c4
    generalize (123236 / 24249375 : A_C) = c5; generalize (492944 / 33949125 : A_C) = c6
    ring
  · have h1 := hrat_L (-8) 405 (-8 * 580907250) (by decide) (by unfold L_all_A; decide)
    have h2 := hrat_L (-476) 7185 (-476 * 32744250) (by decide) (by unfold L_all_A; decide)
    have h3 := hrat_L 6916 35925 (6916 * 6548850) (by decide) (by unfold L_all_A; decide)
    have hsc : ∀ (a b c : ℤ), ((a * b * c : ℤ) : A_C) = (b : A_C) * ((a * c : ℤ) : A_C) := fun a b c => by
      push_cast; ring
    rw [hsc (-8) (-9) 580907250, hsc 6916 (-9) 6548850, hsc (-8) 5 580907250,
        hsc (-476) (-9) 32744250, hsc 6916 5 6548850, hsc (-476) 5 32744250, ← h1, ← h2, ← h3]
    simp only [Int.cast_neg, Int.cast_ofNat, neg_div]
    generalize (L_all_A : A_C) = Lc
    generalize (8 / 405 : A_C) = c1; generalize (476 / 7185 : A_C) = c2; generalize (6916 / 35925 : A_C) = c3
    ring


private theorem localQ5_ac_bridge_proof : Q5ACBridgeSpec :=
  ⟨evalACache_K5_props.1, evalACache_K5_props.2.1,
   evalACache_K5_props.2.2.1, evalACache_K5_props.2.2.2.1,
   evalACache_K5_props.2.2.2.2.2.1, evalACache_K5_props.2.2.2.2.2.2.1,
   evalACache_K5_props.2.2.2.2.2.2.2.1, evalACache_AC_bridge⟩

end SymmetricSexticResidual.LocalResidueQ5

theorem solution : SymmetricSexticResidual.LocalResidueQ5.Q5ACBridgeSpec :=
  SymmetricSexticResidual.LocalResidueQ5.localQ5_ac_bridge_proof
