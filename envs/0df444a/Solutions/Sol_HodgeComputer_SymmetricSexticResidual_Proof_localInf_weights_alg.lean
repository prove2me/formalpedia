-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localInf_weights_alg
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T16:26:43.053907+00:00
-- url     : https://prove2.me/submissions/c6f3268b-de3c-43f9-8658-0b86d65b7090

import Definitions.Def_HodgeComputerSSR_LocalInfAlgDefs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace SymmetricSexticResidual.LocalResidueInfAlg
open Polynomial QuadraticCovers

lemma W1_inf_log_deriv {R : Type*} [Field R] [CharZero R]
    (Bv2 Bv1 : R) (WD cbD D22 D20 D33 : Dual R)
    (d21v d1s ress p1d0 A43 A44 ratio : R)
    (hBv2 : Bv2 ≠ 0) (hcb : cbD.val ≠ 0) (hd22 : D22.val ≠ 0) (hd20 : D20.val ≠ 0) (hd33 : D33.val ≠ 0)
    (hw_rel : WD.eps * Bv2 = -WD.val * Bv1)
    (hA4_ratio : A44 = A43 * ratio)
    (hval : (-(WD.val * cbD.val ^ 4)) * (D22.val ^ 2 * D20.val ^ 3 * D33.val) =
      (81 * Bv2 * D22.val ^ 3 * (D20.val ^ 3 * D33.val ^ 2)) * A43)
    (hsum : (-2 * Bv1 / Bv2 + 4 * cbD.eps / cbD.val - D22.eps / D22.val - D33.eps / D33.val -
      d21v ^ 2 / (D22.val * D20.val) - d1s / (D22.val * D20.val * D33.val) -
      ress / (D20.val ^ 3 * D33.val ^ 2) + p1d0 / (D22.val ^ 2 * D20.val ^ 3 * D33.val)) - ratio = 0)
    (num_pref d1_D res_D den_pref P0_4_D C4_D : Dual R)
    (hnum : num_pref = -(WD * cbD ^ 4))
    (hd1 : d1_D = ⟨(-(D22 * D20 * D33)).val, (-(D22 * D20 * D33)).eps + d1s⟩)
    (hres : res_D = ⟨(D20 ^ 3 * D33 ^ 2).val, (D20 ^ 3 * D33 ^ 2).eps + ress⟩)
    (hden : den_pref = Dual.C (81 : R) * ⟨Bv2, Bv1⟩ * D22 ^ 3 * res_D)
    (hP0 : P0_4_D = ⟨(D22 * D20 ^ 2).val, (D22 * D20 ^ 2).eps - d21v ^ 2 * D20.val⟩)
    (hC4 : C4_D = ⟨(-(P0_4_D * d1_D)).val, (-(P0_4_D * d1_D)).eps + p1d0⟩) :
    num_pref.val * C4_D.eps + num_pref.eps * C4_D.val = den_pref.val * A44 + den_pref.eps * A43 := by
  subst hnum hden hC4 hP0 hd1 hres
  rcases WD with ⟨w0, w1⟩
  rcases cbD with ⟨cbv, cbe⟩
  rcases D22 with ⟨d22v, d22e⟩
  rcases D20 with ⟨d20v, d20e⟩
  rcases D33 with ⟨d33v, d33e⟩
  have h81 : (81 : R) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
  have hw1_eq : w1 = -w0 * Bv1 / Bv2 := by rw [eq_div_iff hBv2]; exact hw_rel
  have hA43_eq : A43 = -(w0 * cbv ^ 4) / (81 * Bv2 * d22v * d33v) := by
    have hden_ne : (81 : R) * Bv2 * d22v * d33v ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero h81 hBv2) hd22) hd33
    rw [eq_div_iff hden_ne]
    apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hd22) (pow_ne_zero 3 hd20)) hd33)
    linear_combination hval.symm
  have hdiff :
      ((-(w0 * cbv ^ 4)) * (-(d22v * d20v ^ 2 * (-(d22v * d20v * d33e + (d22v * d20e + d22e * d20v) * d33v) + d1s) +
        (d22v * (2 * d20v * d20e) + d22e * d20v ^ 2 - d21v ^ 2 * d20v) * (-(d22v * d20v * d33v))) + p1d0) +
       (-(w0 * (4 * cbv ^ 3 * cbe) + w1 * cbv ^ 4)) * (-(d22v * d20v ^ 2 * (-(d22v * d20v * d33v))))) -
      ((81 * Bv2 * d22v ^ 3 * (d20v ^ 3 * d33v ^ 2)) * A44 +
       ((81 * Bv2 * d22v ^ 3) * (d20v ^ 3 * (2 * d33v * d33e) + 3 * d20v ^ 2 * d20e * d33v ^ 2 + ress) +
        ((81 * Bv2) * (3 * d22v ^ 2 * d22e) + 81 * Bv1 * d22v ^ 3) * (d20v ^ 3 * d33v ^ 2)) * A43) =
      (81 * Bv2 * d22v ^ 3 * (d20v ^ 3 * d33v ^ 2)) * A43 *
        ((-2 * Bv1 / Bv2 + 4 * cbe / cbv - d22e / d22v - d33e / d33v -
          d21v ^ 2 / (d22v * d20v) - d1s / (d22v * d20v * d33v) -
          ress / (d20v ^ 3 * d33v ^ 2) + p1d0 / (d22v ^ 2 * d20v ^ 3 * d33v)) - ratio) := by
    rw [hA4_ratio, hw1_eq, hA43_eq]
    field_simp [hBv2, hcb, hd22, hd20, hd33, h81]
    ring
  rw [hsum, mul_zero] at hdiff
  simp only [Dual.neg_val, Dual.neg_eps, Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps,
    Dual.pow_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  linear_combination hdiff

lemma W1_inf_r5678_alg {R : Type*} [Field R] [CharZero R]
    (d22 d20 d33 d21 d32 d31 d30 : R) (hd22 : d22 ≠ 0) (hd20 : d20 ≠ 0) (hd33 : d33 ≠ 0) :
    -d21 ^ 2 / (d22 * d20) - (d22 ^ 2 * d31 - d21 * (d22 * d32 - d21 * d33)) / (d22 * d20 * d33) -
      (-d21 * d20 ^ 2 * d33 * d32 + d22 * d20 ^ 2 * d32 ^ 2 - 2 * d22 * d20 ^ 2 * d33 * d31 +
       3 * d22 * d21 * d20 * d33 * d30 - 2 * d22 ^ 2 * d20 * d32 * d30 + d22 ^ 3 * d30 ^ 2) / (d20 ^ 3 * d33 ^ 2) +
      (2 * d22 * d21 * d20 * (d22 ^ 2 * d30 - d20 * (d22 * d32 - d21 * d33))) / (d22 ^ 2 * d20 ^ 3 * d33) =
    (d22 / d20) * (d31 / d33) - (d22 / d20) * (d32 / d33) ^ 2 - (d22 / d33) * (d21 / d20) * (d30 / d20) +
      2 * (d22 / d33) * (d22 / d20) * (d32 / d33) * (d30 / d20) - (d22 / d33) ^ 2 * (d22 / d20) * (d30 / d20) ^ 2 := by
  field_simp [hd22, hd20, hd33]; ring


lemma W1_inf_weights_consts {R : Type*} [Field R] [CharZero R] :
    ((-(2500 / 6561 : R)) ^ 3 * (64 / 4782969 : R) ^ 2 =
      -(64000000000000 / 6461081889226673298932241 : R)) ∧
    (-(-(25 / 4 : R) * (4 / 27 : R) ^ 4) =
      81 * (-(4 / 243 : R)) * (16 / 413343 : R) * (64 / 4782969 : R) * (-(279006525 / 64 : R))) ∧
    (-(-(25 / 4 : R) * (4 / 27 : R) ^ 4) /
        (81 * (-(4 / 243 : R)) * (-(2500 / 6561 : R)) * (64 / 4782969 : R)) =
      (177147 / 400 : R)) ∧
    (-(25 / 4 : R) * (4 / 27 : R) ^ 4 =
      81 * (-(4 / 243 : R)) * (-(2500 / 6561 : R)) * (64 / 4782969 : R) * (-(177147 / 400 : R))) := by
  have hd1_a : (4 : R) * 27 ^ 4 ≠ 0 := mul_ne_zero (ofNat_ne_zero 4) (pow_ne_zero 4 (ofNat_ne_zero 27))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hZ : ((-2500 : ℤ) ^ 3 * 64 ^ 2) * 6461081889226673298932241 =
        (-64000000000000 : ℤ) * (6561 ^ 3 * 4782969 ^ 2) := by decide
    have hR := congrArg (Int.castRingHom R) hZ
    have hd1 : (6561 : R) ^ 3 * (4782969 : R) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 3 (ofNat_ne_zero 6561)) (pow_ne_zero 2 (ofNat_ne_zero 4782969))
    have hd2 : (6461081889226673298932241 : R) ≠ 0 := ofNat_ne_zero 6461081889226673298932241
    rw [← neg_div, div_pow, div_pow, div_mul_div_comm, ← neg_div, div_eq_div_iff hd1 hd2]
    simpa only [map_mul, map_pow, map_neg, map_ofNat] using hR
  · have hZ : (25 * 4 ^ 4 : ℤ) * (243 * 413343 * 4782969 * 64) =
        (81 * 4 * 16 * 64 * 279006525 : ℤ) * (4 * 27 ^ 4) := by decide
    have hR := congrArg (Int.castRingHom R) hZ
    have hd2 : (243 : R) * 413343 * 4782969 * 64 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (ofNat_ne_zero 243) (ofNat_ne_zero 413343))
        (ofNat_ne_zero 4782969)) (ofNat_ne_zero 64)
    have h1 : -(-(25 / 4 : R) * (4 / 27 : R) ^ 4) = (25 * 4 ^ 4 : R) / (4 * 27 ^ 4) := by
      field_simp [hd1_a]
    have h2 : 81 * (-(4 / 243 : R)) * (16 / 413343 : R) * (64 / 4782969 : R) * (-(279006525 / 64 : R)) =
        (81 * 4 * 16 * 64 * 279006525 : R) / (243 * 413343 * 4782969 * 64) := by
      field_simp [hd2]
    rw [h1, h2, div_eq_div_iff hd1_a hd2]
    simpa only [map_mul, map_pow, map_ofNat] using hR
  · have hZ : (25 * 4 ^ 4 : ℤ) * (400 * (243 * 6561 * 4782969)) =
        (177147 * (81 * 4 * 2500 * 64) : ℤ) * (4 * 27 ^ 4) := by decide
    have hR := congrArg (Int.castRingHom R) hZ
    have hnz2 : (243 : R) * 6561 * 4782969 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (ofNat_ne_zero 243) (ofNat_ne_zero 6561)) (ofNat_ne_zero 4782969)
    have hnz4 : (400 : R) ≠ 0 := ofNat_ne_zero 400
    have hden_ne : (81 : R) * -(4 / 243 : R) * -(2500 / 6561 : R) * (64 / 4782969 : R) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (ofNat_ne_zero 81)
        (neg_ne_zero.mpr (div_ne_zero (ofNat_ne_zero 4) (ofNat_ne_zero 243))))
        (neg_ne_zero.mpr (div_ne_zero (ofNat_ne_zero 2500) (ofNat_ne_zero 6561))))
        (div_ne_zero (ofNat_ne_zero 64) (ofNat_ne_zero 4782969))
    rw [div_eq_iff hden_ne]
    have h1 : -(-(25 / 4 : R) * (4 / 27 : R) ^ 4) = (25 * 4 ^ 4 : R) / (4 * 27 ^ 4) := by
      field_simp [hd1_a]
    have h2 : (177147 / 400 : R) * (81 * -(4 / 243 : R) * -(2500 / 6561 : R) * (64 / 4782969 : R)) =
        (177147 * (81 * 4 * 2500 * 64) : R) / (400 * (243 * 6561 * 4782969)) := by
      field_simp [hnz2, hnz4]
    rw [h1, h2, div_eq_div_iff hd1_a (mul_ne_zero hnz4 hnz2)]
    simpa only [map_mul, map_pow, map_ofNat] using hR
  · have hZ : ((-25 : ℤ) * 4 ^ 4) * (243 * 6561 * 4782969 * 400) =
        (81 * (-4) * (-2500) * 64 * (-177147) : ℤ) * (4 * 27 ^ 4) := by decide
    have hR := congrArg (Int.castRingHom R) hZ
    have hd2 : (243 : R) * 6561 * 4782969 * 400 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (ofNat_ne_zero 243) (ofNat_ne_zero 6561))
        (ofNat_ne_zero 4782969)) (ofNat_ne_zero 400)
    have h1 : -(25 / 4 : R) * (4 / 27 : R) ^ 4 = ((-25 : R) * 4 ^ 4) / (4 * 27 ^ 4) := by
      field_simp [hd1_a]
    have h2 : 81 * (-(4 / 243 : R)) * (-(2500 / 6561 : R)) * (64 / 4782969 : R) * (-(177147 / 400 : R)) =
        (81 * (-4) * (-2500) * 64 * (-177147) : R) / (243 * 6561 * 4782969 * 400) := by
      field_simp [hd2]
    rw [h1, h2, div_eq_div_iff hd1_a hd2]
    simpa only [map_mul, map_pow, map_neg, map_ofNat] using hR

private lemma P44_fn_split {R : Type*} [Field R] (S Q T : R) :
    P44_fn S Q T =
      ((20510415 : R) + (-496300770) * Q + 1510998300 * Q ^ 2 + 4883417910 * Q ^ 3 +
        (-20513855880) * Q ^ 4 + 141076404 * S + (-1013761980) * S * Q + (-4586695470) * S * Q ^ 2 +
        28084223286 * S * Q ^ 3 + 161280315 * S ^ 2 + 1449439110 * S ^ 2 * Q +
        (-14449808646) * S ^ 2 * Q ^ 2 + (-155306970) * S ^ 3 + 3313480842 * S ^ 3 * Q + (-285894273) * S ^ 4) +
      ((-45278190 : R) + 1002263220 * Q + (-9227925000) * Q ^ 2 + 25838190000 * Q ^ 3 +
        (-302433264) * S + 6278958000 * S * Q + (-28116396000) * S * Q ^ 2 + 2593080000 * S * Q ^ 3 +
        (-1055687850) * S ^ 2 + 10141721100 * S ^ 2 * Q + (-2722734000) * S ^ 2 * Q ^ 2 +
        (-1212264900) * S ^ 3 + 950796000 * S ^ 3 * Q + (-110397980) * S ^ 4) * T +
      ((-135184545 : R) + 1619567460 * Q + (-4613962500) * Q ^ 2 + (-657628902) * S +
        3978922500 * S * Q + (-1389150000) * S * Q ^ 2 + (-843577875) * S ^ 2 +
        1065015000 * S ^ 2 * Q + (-108045000) * S ^ 2 * Q ^ 2 + (-203742000) * S ^ 3 +
        79233000 * S ^ 3 * Q + (-14526050) * S ^ 4) * T ^ 2 +
      ((-13243230 : R) + 61801740 * Q + (-22660638) * S) * T ^ 3 := by
  dsimp only [P44_fn]; ring

private lemma W1_inf_hsum8_poly {R : Type*} [CommRing R] (S Q T : R) :
    let S3Q : R := S - 3 * Q
    let L : R := 77 * S - 210 * Q + 45
    294 * L * (1001 * S ^ 3 - 5796 * S ^ 2 * Q + 9828 * S * Q ^ 2 - 4158 * Q ^ 3 +
        1001 * T ^ 3 - 5796 * T ^ 2 + 9828 * T - 4158 + 1215 * Q ^ 2 + 2430 * Q) +
      588 * S3Q * L * (-644 * S ^ 2 + 2184 * S * Q - 1386 * Q ^ 2 + 270 * Q + 270) +
      (-147) * (238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
        1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
        124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) +
      (-294) * S3Q * L * (13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) +
      (-21) * L ^ 2 * (5 * T - 3) ^ 2 * (-49 * S ^ 2 + 140 * S * Q - 90 * Q - 90) +
      14700 * S3Q ^ 2 * L ^ 2 * (5 * T - 3) ^ 2 +
      14 * L ^ 2 * (5 * T - 3) * (5 * T - 1) * (-77 * S ^ 2 + 210 * S * Q - 45 * S - 135 * Q - 270) +
      (-420) * S3Q * L ^ 3 * (5 * T - 3) * (5 * T - 1) +
      3 * L ^ 4 * (5 * T - 1) ^ 2 +
      (((20510415 : R) + (-496300770) * Q + 1510998300 * Q ^ 2 + 4883417910 * Q ^ 3 +
        (-20513855880) * Q ^ 4 + 141076404 * S + (-1013761980) * S * Q + (-4586695470) * S * Q ^ 2 +
        28084223286 * S * Q ^ 3 + 161280315 * S ^ 2 + 1449439110 * S ^ 2 * Q +
        (-14449808646) * S ^ 2 * Q ^ 2 + (-155306970) * S ^ 3 + 3313480842 * S ^ 3 * Q + (-285894273) * S ^ 4) +
      ((-45278190 : R) + 1002263220 * Q + (-9227925000) * Q ^ 2 + 25838190000 * Q ^ 3 +
        (-302433264) * S + 6278958000 * S * Q + (-28116396000) * S * Q ^ 2 + 2593080000 * S * Q ^ 3 +
        (-1055687850) * S ^ 2 + 10141721100 * S ^ 2 * Q + (-2722734000) * S ^ 2 * Q ^ 2 +
        (-1212264900) * S ^ 3 + 950796000 * S ^ 3 * Q + (-110397980) * S ^ 4) * T +
      ((-135184545 : R) + 1619567460 * Q + (-4613962500) * Q ^ 2 + (-657628902) * S +
        3978922500 * S * Q + (-1389150000) * S * Q ^ 2 + (-843577875) * S ^ 2 +
        1065015000 * S ^ 2 * Q + (-108045000) * S ^ 2 * Q ^ 2 + (-203742000) * S ^ 3 +
        79233000 * S ^ 3 * Q + (-14526050) * S ^ 4) * T ^ 2 +
      ((-13243230 : R) + 61801740 * Q + (-22660638) * S) * T ^ 3) = 0 := by
  intro S3Q L
  set p5 : R := -49 * S ^ 2 + 140 * S * Q - 90 * Q - 90
  set p7 : R := -77 * S ^ 2 + 210 * S * Q - 45 * S - 135 * Q - 270
  set A : R := -21 * L ^ 2 * p5 + 14700 * S3Q ^ 2 * L ^ 2
  set B : R := 14 * L ^ 2 * p7 - 420 * S3Q * L ^ 3
  set C : R := 3 * L ^ 4
  have hc3 : 294 * L * 1001 + ((-13243230 : R) + 61801740 * Q + (-22660638) * S) = 0 := by
    dsimp only [L]; ring
  have hc2 : 294 * L * (-5796) + 25 * (A + B + C) +
      ((-135184545 : R) + 1619567460 * Q + (-4613962500) * Q ^ 2 + (-657628902) * S +
        3978922500 * S * Q + (-1389150000) * S * Q ^ 2 + (-843577875) * S ^ 2 +
        1065015000 * S ^ 2 * Q + (-108045000) * S ^ 2 * Q ^ 2 + (-203742000) * S ^ 3 +
        79233000 * S ^ 3 * Q + (-14526050) * S ^ 4) = 0 := by
    dsimp only [A, B, C, L, S3Q, p5, p7]; ring
  have hc1 : 294 * L * 9828 + (-30 * A - 20 * B - 10 * C) +
      ((-45278190 : R) + 1002263220 * Q + (-9227925000) * Q ^ 2 + 25838190000 * Q ^ 3 +
        (-302433264) * S + 6278958000 * S * Q + (-28116396000) * S * Q ^ 2 + 2593080000 * S * Q ^ 3 +
        (-1055687850) * S ^ 2 + 10141721100 * S ^ 2 * Q + (-2722734000) * S ^ 2 * Q ^ 2 +
        (-1212264900) * S ^ 3 + 950796000 * S ^ 3 * Q + (-110397980) * S ^ 4) = 0 := by
    dsimp only [A, B, C, L, S3Q, p5, p7]; ring
  have hc0 : 294 * L * (1001 * S ^ 3 - 5796 * S ^ 2 * Q + 9828 * S * Q ^ 2 - 4158 * Q ^ 3 -
        4158 + 1215 * Q ^ 2 + 2430 * Q) +
      588 * S3Q * L * (-644 * S ^ 2 + 2184 * S * Q - 1386 * Q ^ 2 + 270 * Q + 270) -
      147 * (238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
        1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
        124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) -
      294 * S3Q * L * (13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) +
      (9 * A + 3 * B + C) +
      ((20510415 : R) + (-496300770) * Q + 1510998300 * Q ^ 2 + 4883417910 * Q ^ 3 +
        (-20513855880) * Q ^ 4 + 141076404 * S + (-1013761980) * S * Q + (-4586695470) * S * Q ^ 2 +
        28084223286 * S * Q ^ 3 + 161280315 * S ^ 2 + 1449439110 * S ^ 2 * Q +
        (-14449808646) * S ^ 2 * Q ^ 2 + (-155306970) * S ^ 3 + 3313480842 * S ^ 3 * Q + (-285894273) * S ^ 4) = 0 := by
    dsimp only [A, B, C, L, S3Q, p5, p7]; ring
  have hgrp :
      294 * L * (1001 * S ^ 3 - 5796 * S ^ 2 * Q + 9828 * S * Q ^ 2 - 4158 * Q ^ 3 +
          1001 * T ^ 3 - 5796 * T ^ 2 + 9828 * T - 4158 + 1215 * Q ^ 2 + 2430 * Q) +
        588 * S3Q * L * (-644 * S ^ 2 + 2184 * S * Q - 1386 * Q ^ 2 + 270 * Q + 270) +
        (-147) * (238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
          1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
          124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) +
        (-294) * S3Q * L * (13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) +
        (-21) * L ^ 2 * (5 * T - 3) ^ 2 * p5 +
        14700 * S3Q ^ 2 * L ^ 2 * (5 * T - 3) ^ 2 +
        14 * L ^ 2 * (5 * T - 3) * (5 * T - 1) * p7 +
        (-420) * S3Q * L ^ 3 * (5 * T - 3) * (5 * T - 1) +
        3 * L ^ 4 * (5 * T - 1) ^ 2 =
      (294 * L * 1001) * T ^ 3 +
      (294 * L * (-5796) + 25 * (A + B + C)) * T ^ 2 +
      (294 * L * 9828 + (-30 * A - 20 * B - 10 * C)) * T +
      (294 * L * (1001 * S ^ 3 - 5796 * S ^ 2 * Q + 9828 * S * Q ^ 2 - 4158 * Q ^ 3 -
          4158 + 1215 * Q ^ 2 + 2430 * Q) +
        588 * S3Q * L * (-644 * S ^ 2 + 2184 * S * Q - 1386 * Q ^ 2 + 270 * Q + 270) -
        147 * (238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
          1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
          124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) -
        294 * S3Q * L * (13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) +
        (9 * A + 3 * B + C)) := by
    dsimp only [A, B, C]
    generalize (-644 * S ^ 2 + 2184 * S * Q - 1386 * Q ^ 2 + 270 * Q + 270 : R) = gcb
    generalize (238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
          1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
          124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900 : R) = gp3
    generalize (13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455 : R) = gp4
    ring
  change (294 * L * _ + _ + _ + _ + (-21) * L ^ 2 * (5 * T - 3) ^ 2 * p5 + _ + 14 * L ^ 2 * (5 * T - 3) * (5 * T - 1) * p7 + _ + _) + _ = 0
  rw [hgrp]
  linear_combination hc3 * T ^ 3 + hc2 * T ^ 2 + hc1 * T + hc0

private lemma mul_dist10 {R : Type*} [CommRing R] (M a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : R) :
    M * ((a1 + a2 + a3 + a4) + (a5 - a6 - a7 + a8 - a9) - a10) =
      (M * a1) + (M * a2) + (M * a3) + (M * a4) + (M * a5) +
      (M * (-a6)) + (M * (-a7)) + (M * a8) + (M * (-a9)) + (M * (-a10)) := by ring

lemma W1_inf_weights_hsum8 {R : Type*} [Field R] [CharZero R] (S Q T : R)
    (hS3Q : S - 3 * Q ≠ 0) (hL : 77 * S - 210 * Q + 45 ≠ 0) (hT59 : 5 * T - 9 ≠ 0) :
    let S3Q := S - 3 * Q; let T59 := 5 * T - 9; let L := 77 * S - 210 * Q + 45
    let Bv2 : R := -(4 / 243 : R) * S3Q ^ 3
    let Bv1 : R := (143 / 243 : R) * S ^ 3 - (92 / 27) * S ^ 2 * Q + (52 / 9) * S * Q ^ 2 - (22 / 9) * Q ^ 3 +
      (143 / 243) * T ^ 3 - (92 / 27) * T ^ 2 + (52 / 9) * T - (22 / 9) + (5 / 7) * Q ^ 2 + (10 / 7) * Q
    let cbD_val : R := (4 / 27 : R) * S3Q ^ 2
    let cbD_eps : R := -(92 / 27 : R) * S ^ 2 + (104 / 9) * S * Q - (22 / 3) * Q ^ 2 + (10 / 7) * Q + (10 / 7)
    let r3 : R := -(238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
      1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
      124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) / (28 * S3Q ^ 3 * L)
    let r4 : R := -(13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) / (14 * S3Q ^ 2)
    let q22_33 : R := (81 / 28 : R) * L / S3Q ^ 2
    let q32_33 : R := -(375 / 2 : R) * T59 * (5 * T - 3) / S3Q ^ 2
    let q31_33 : R := (5625 / 112 : R) * T59 ^ 2 * (5 * T - 3) ^ 2 *
      (-49 * S ^ 2 + 140 * S * Q - 90 * Q - 90) / S3Q ^ 6
    let q21_20 : R := (2 / 1575 : R) * (5 * T - 3) / T59 *
      (-77 * S ^ 2 + 210 * S * Q - 45 * S - 135 * Q - 270)
    let q30_20 : R := -(25 / 27 : R) * (5 * T - 1) * T59 / S3Q
    let q22_20 : R := -(4 / 39375 : R) * L * S3Q ^ 3 / T59 ^ 2
    (-2 * Bv1 / Bv2 + 4 * cbD_eps / cbD_val + r3 + r4) +
      (q22_20 * q31_33 - q22_20 * q32_33 ^ 2 - q22_33 * q21_20 * q30_20 +
       2 * q22_33 * q22_20 * q32_33 * q30_20 - q22_33 ^ 2 * q22_20 * q30_20 ^ 2) -
      (-(1 / 4116 : R) * P44_fn S Q T / (S3Q ^ 3 * L)) = 0 := by
  intro S3Q T59 L Bv2 Bv1 cbD_val cbD_eps r3 r4 q22_33 q32_33 q31_33 q21_20 q30_20 q22_20
  have hS3Q' : S3Q ≠ 0 := hS3Q; have hL' : L ≠ 0 := hL; have hT59' : T59 ≠ 0 := hT59
  have hM : (4116 : R) * S3Q ^ 3 * L ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ofNat_ne_zero 4116) (pow_ne_zero 3 hS3Q')) hL'
  apply mul_left_cancel₀ hM
  rw [mul_zero, mul_dist10]
  have ht1 : (4116 : R) * S3Q ^ 3 * L * (-2 * Bv1 / Bv2) =
      294 * L * (1001 * S ^ 3 - 5796 * S ^ 2 * Q + 9828 * S * Q ^ 2 - 4158 * Q ^ 3 +
        1001 * T ^ 3 - 5796 * T ^ 2 + 9828 * T - 4158 + 1215 * Q ^ 2 + 2430 * Q) := by
    have h1 : (4116 : R) * S3Q ^ 3 * L * (-2 * Bv1 / Bv2) = 294 * L * (1701 * Bv1) := by
      dsimp only [Bv2]; field_simp [hS3Q']; ring
    rw [h1]; congr 1; dsimp only [Bv1]; ring
  have ht2 : (4116 : R) * S3Q ^ 3 * L * (4 * cbD_eps / cbD_val) =
      588 * S3Q * L * (-644 * S ^ 2 + 2184 * S * Q - 1386 * Q ^ 2 + 270 * Q + 270) := by
    have h1 : (4116 : R) * S3Q ^ 3 * L * (4 * cbD_eps / cbD_val) = 588 * S3Q * L * (189 * cbD_eps) := by
      dsimp only [cbD_val]; field_simp [hS3Q']; ring
    rw [h1]; congr 1; dsimp only [cbD_eps]; ring
  have ht3 : (4116 : R) * S3Q ^ 3 * L * r3 =
      (-147) * (238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
        1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
        124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) := by
    dsimp only [r3]; field_simp [hS3Q', hL']; ring
  have ht4 : (4116 : R) * S3Q ^ 3 * L * r4 =
      (-294) * S3Q * L * (13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) := by
    dsimp only [r4]; field_simp [hS3Q']; ring
  have ht5 : (4116 : R) * S3Q ^ 3 * L * (q22_20 * q31_33) =
      (-21) * L ^ 2 * (5 * T - 3) ^ 2 * (-49 * S ^ 2 + 140 * S * Q - 90 * Q - 90) := by
    dsimp only [q22_20, q31_33]; field_simp [hS3Q', hT59']; ring
  have ht6 : (4116 : R) * S3Q ^ 3 * L * (-(q22_20 * q32_33 ^ 2)) =
      14700 * S3Q ^ 2 * L ^ 2 * (5 * T - 3) ^ 2 := by
    dsimp only [q22_20, q32_33]; field_simp [hS3Q', hT59']; ring
  have ht7 : (4116 : R) * S3Q ^ 3 * L * (-(q22_33 * q21_20 * q30_20)) =
      14 * L ^ 2 * (5 * T - 3) * (5 * T - 1) * (-77 * S ^ 2 + 210 * S * Q - 45 * S - 135 * Q - 270) := by
    dsimp only [q22_33, q21_20, q30_20]; field_simp [hS3Q', hT59']; ring
  have ht8 : (4116 : R) * S3Q ^ 3 * L * (2 * q22_33 * q22_20 * q32_33 * q30_20) =
      (-420) * S3Q * L ^ 3 * (5 * T - 3) * (5 * T - 1) := by
    dsimp only [q22_33, q22_20, q32_33, q30_20]; field_simp [hS3Q', hT59']; ring
  have ht9 : (4116 : R) * S3Q ^ 3 * L * (-(q22_33 ^ 2 * q22_20 * q30_20 ^ 2)) =
      3 * L ^ 4 * (5 * T - 1) ^ 2 := by
    dsimp only [q22_33, q22_20, q30_20]; field_simp [hS3Q', hT59']; ring
  have ht10 : (4116 : R) * S3Q ^ 3 * L * (-(-(1 / 4116 : R) * P44_fn S Q T / (S3Q ^ 3 * L))) =
      P44_fn S Q T := by
    field_simp [hS3Q', hL']
  rw [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, P44_fn_split]
  exact W1_inf_hsum8_poly S Q T


lemma W1_inf_weights_alg {R : Type*} [Field R] [CharZero R] (S Q T d20e : R)
    (hS3Q : S - 3 * Q ≠ 0) (hL : 77 * S - 210 * Q + 45 ≠ 0) (hT59 : 5 * T - 9 ≠ 0) :
    (w1_res_D S Q T d20e).val =
      -(64000000000000 / 6461081889226673298932241 : R) * (5 * T - 9) ^ 6 * (S - 3 * Q) ^ 15 ∧
    (w1_den_pref S Q T d20e).val ≠ 0 ∧
    w1_num_pref S Q T * w1_C4_D S Q T d20e =
      w1_den_pref S Q T d20e * ⟨w1_A4_3 S Q T, w1_A4_4 S Q T⟩ ∧
    (w1_num_pref S Q T).val * w1_C3_v S Q T d20e =
      (w1_den_pref S Q T d20e).val * w1_A3_4 S Q T ∧
    (w1_num_pref S Q T).val * w1_C2_v S Q T d20e =
      (w1_den_pref S Q T d20e).val * w1_A2_4 S Q T := by
  obtain ⟨hres_c, hsc_A4, hsc_A3, hsc_A2⟩ := W1_inf_weights_consts (R := R)
  have hBv2_ne : w1_Bv2 S Q ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (ofNat_ne_zero 4) (ofNat_ne_zero 243))) (pow_ne_zero 3 hS3Q)
  have hw0_s : w1_w0 S Q T = -(25 / 4 : R) * T * (5 * T - 9) ^ 2 / (S - 3 * Q) ^ 3 := by
    simp only [w1_w0, w1_Cv0, w1_Bv2]; field_simp [hS3Q]
  have hQ5_5 : (w1_D22 S Q).val = (16 / 413343 : R) * (77 * S - 210 * Q + 45) * (S - 3 * Q) ^ 4 := by
    simp only [w1_D22, Q5_c5]; ring
  have hQ7_7 : (w1_D33 S Q).val = (64 / 4782969 : R) * (S - 3 * Q) ^ 6 := by
    simp only [w1_D33, Q7_c7]; ring
  have hD20_v : w1_D20_v S Q T = -(2500 / 6561 : R) * (S - 3 * Q) * (5 * T - 9) ^ 2 := by
    simp only [w1_D20_v, w1_c0_0, w1_k2_0, w1_cbD]; rw [hw0_s]; field_simp [hS3Q]; ring
  have hD30_v : w1_D30_v S Q T = (62500 / 177147 : R) * (5 * T - 1) * (5 * T - 9) ^ 3 := by
    simp only [w1_D30_v, w1_c0_0, w1_k3_0, w1_cbD]; rw [hw0_s]
    have hcancel : ((4 / 27 : R) * (S - 3 * Q) ^ 2) ^ 3 *
        ((-(25 / 4 : R) * T * (5 * T - 9) ^ 2 / (S - 3 * Q) ^ 3) ^ 2 * -(625 / 243 : R)) =
        -(1562500 / 4782969 : R) * T ^ 2 * (5 * T - 9) ^ 4 := by
      field_simp [hS3Q]; ring
    rw [hcancel]; ring
  have hD21_v : w1_D21_v S Q T = -(200 / 413343 : R) * (5 * T - 9) * (5 * T - 3) * (S - 3 * Q) *
      (-77 * S ^ 2 + 210 * S * Q - 45 * S - 135 * Q - 270) := by
    simp only [w1_D21_v, p21_c3, w1_c0_0]; ring
  have hD32_v : w1_D32_v S Q T = -(4000 / 1594323 : R) * (5 * T - 9) * (5 * T - 3) * (S - 3 * Q) ^ 4 := by
    simp only [w1_D32_v, p32_c5, w1_c0_0]; ring
  have hD31_v : w1_D31_v S Q T = (2500 / 3720087 : R) * (5 * T - 9) ^ 2 * (5 * T - 3) ^ 2 *
      (-49 * S ^ 2 + 140 * S * Q - 90 * Q - 90) := by
    simp only [w1_D31_v, p31_c3, w1_c0_0]; ring
  have hres_fac : (w1_res_D S Q T d20e).val = w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val ^ 2 := by
    simp only [w1_res_D, w1_res_main, Dual.mul_val, Dual.pow_eq, w1_D20]
  have hd1_fac : (w1_d1_main S Q T d20e).val = -((w1_D22 S Q).val * w1_D20_v S Q T * (w1_D33 S Q).val) := by
    simp only [w1_d1_main, Dual.neg_val, Dual.mul_val, w1_D20]
  have hres_v : (w1_res_D S Q T d20e).val =
      -(64000000000000 / 6461081889226673298932241 : R) * (5 * T - 9) ^ 6 * (S - 3 * Q) ^ 15 := by
    rw [hres_fac, hD20_v, hQ7_7, ← hres_c]
    generalize (-(2500 / 6561 : R)) = c1; generalize (64 / 4782969 : R) = c2; ring
  have hD22_ne : (w1_D22 S Q).val ≠ 0 := by
    rw [hQ5_5]; exact mul_ne_zero (mul_ne_zero (div_ne_zero (ofNat_ne_zero 16) (ofNat_ne_zero 413343)) hL) (pow_ne_zero 4 hS3Q)
  have hD20_ne : w1_D20_v S Q T ≠ 0 := by
    rw [hD20_v]; exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (ofNat_ne_zero 2500) (ofNat_ne_zero 6561))) hS3Q) (pow_ne_zero 2 hT59)
  have hD33_ne : (w1_D33 S Q).val ≠ 0 := by
    rw [hQ7_7]; exact mul_ne_zero (div_ne_zero (ofNat_ne_zero 64) (ofNat_ne_zero 4782969)) (pow_ne_zero 6 hS3Q)
  have hden_v : (w1_den_pref S Q T d20e).val = 81 * w1_Bv2 S Q * (w1_D22 S Q).val ^ 3 * (w1_res_D S Q T d20e).val := by
    simp only [w1_den_pref, Dual.mul_val, Dual.C_val, Dual.pow_eq]
  have hden_ne : (w1_den_pref S Q T d20e).val ≠ 0 := by
    rw [hden_v, hres_fac]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (ofNat_ne_zero 81) hBv2_ne) (pow_ne_zero 3 hD22_ne))
      (mul_ne_zero (pow_ne_zero 3 hD20_ne) (pow_ne_zero 2 hD33_ne))
  have hnum_v : (w1_num_pref S Q T).val = -(w1_w0 S Q T * (w1_cbD S Q).val ^ 4) := by
    simp only [w1_num_pref, w1_WD, Dual.neg_val, Dual.mul_val, Dual.pow_eq]
  have hC4_v : (w1_C4_D S Q T d20e).val = -((w1_D22 S Q).val * w1_D20_v S Q T ^ 2 * (w1_d1_main S Q T d20e).val) := by
    simp only [w1_C4_D, w1_P0_4_D, w1_d1_D, Dual.neg_val, Dual.mul_val, Dual.pow_eq, w1_D20]
  have hq32_33 : w1_D32_v S Q T / (w1_D33 S Q).val = -(375 / 2 : R) * (5 * T - 9) * (5 * T - 3) / (S - 3 * Q) ^ 2 := by
    rw [hD32_v, hQ7_7]; field_simp [hS3Q]; ring
  have hq22_20 : (w1_D22 S Q).val / w1_D20_v S Q T = -(4 / 39375 : R) * (77 * S - 210 * Q + 45) * (S - 3 * Q) ^ 3 / (5 * T - 9) ^ 2 := by
    rw [hQ5_5, hD20_v]; field_simp [hS3Q, hT59]; ring
  have hq30_33 : w1_D30_v S Q T / (w1_D33 S Q).val = (1687500 / 64 : R) * (5 * T - 1) * (5 * T - 9) ^ 3 / (S - 3 * Q) ^ 6 := by
    rw [hD30_v, hQ7_7]; field_simp [hS3Q]; ring
  have hA4_3 : (w1_num_pref S Q T).val * (w1_C4_D S Q T d20e).val = (w1_den_pref S Q T d20e).val * w1_A4_3 S Q T := by
    have hcore : -(w1_w0 S Q T * (w1_cbD S Q).val ^ 4) =
        81 * w1_Bv2 S Q * (w1_D22 S Q).val * (w1_D33 S Q).val * w1_A4_3 S Q T := by
      rw [hw0_s, hQ5_5, hQ7_7]; simp only [w1_cbD, w1_Bv2, w1_A4_3]
      have hfac : -((-(25 / 4 : R) * T * (5 * T - 9) ^ 2 / (S - 3 * Q) ^ 3) * ((4 / 27 : R) * (S - 3 * Q) ^ 2) ^ 4) =
          (-(-(25 / 4 : R) * (4 / 27 : R) ^ 4)) * (T * (5 * T - 9) ^ 2 * (S - 3 * Q) ^ 5) := by
        field_simp [hS3Q]
      have hfac2 : 81 * (-(4 / 243 : R) * (S - 3 * Q) ^ 3) * ((16 / 413343 : R) * (77 * S - 210 * Q + 45) * (S - 3 * Q) ^ 4) *
          ((64 / 4782969 : R) * (S - 3 * Q) ^ 6) *
          (-(279006525 / 64 : R) * T * (5 * T - 9) ^ 2 / ((S - 3 * Q) ^ 8 * (77 * S - 210 * Q + 45))) =
          (81 * (-(4 / 243 : R)) * (16 / 413343 : R) * (64 / 4782969 : R) * (-(279006525 / 64 : R))) *
            (T * (5 * T - 9) ^ 2 * (S - 3 * Q) ^ 5) := by
        generalize (S - 3 * Q) = S3Q at hS3Q ⊢
        generalize (77 * S - 210 * Q + 45) = L at hL ⊢
        field_simp [hS3Q, hL]
      rw [hfac, hfac2, hsc_A4]
    rw [hnum_v, hC4_v, hden_v, hd1_fac, hres_fac]
    linear_combination ((w1_D22 S Q).val ^ 2 * w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val) * hcore
  have hA3_4 : (w1_num_pref S Q T).val * w1_C3_v S Q T d20e = (w1_den_pref S Q T d20e).val * w1_A3_4 S Q T := by
    have hC3_simp : w1_C3_v S Q T d20e =
        (w1_D22 S Q).val ^ 3 * w1_D20_v S Q T * (w1_D20_v S Q T * w1_D32_v S Q T - (w1_D22 S Q).val * w1_D30_v S Q T) := by
      simp only [w1_C3_v, w1_d0_v, w1_diff12_v]; rw [hd1_fac]; ring
    have hcore : (-(w1_w0 S Q T * (w1_cbD S Q).val ^ 4)) *
        (w1_D20_v S Q T * w1_D32_v S Q T - (w1_D22 S Q).val * w1_D30_v S Q T) =
        81 * w1_Bv2 S Q * w1_D20_v S Q T ^ 2 * (w1_D33 S Q).val ^ 2 * w1_A3_4 S Q T := by
      have hbr : w1_D20_v S Q T * w1_D32_v S Q T - (w1_D22 S Q).val * w1_D30_v S Q T =
          w1_D20_v S Q T * (w1_D33 S Q).val *
            (w1_D32_v S Q T / (w1_D33 S Q).val - ((w1_D22 S Q).val / w1_D20_v S Q T) * (w1_D30_v S Q T / (w1_D33 S Q).val)) := by
        field_simp [hD20_ne, hD33_ne]
      have hsc_pref : -(w1_w0 S Q T * (w1_cbD S Q).val ^ 4) / (81 * w1_Bv2 S Q * w1_D20_v S Q T * (w1_D33 S Q).val) =
          (177147 / 400 : R) * T / (S - 3 * Q) ^ 5 := by
        rw [hw0_s, hD20_v, hQ7_7]; simp only [w1_cbD, w1_Bv2]
        have hfac : -((-(25 / 4 : R) * T * (5 * T - 9) ^ 2 / (S - 3 * Q) ^ 3) * ((4 / 27 : R) * (S - 3 * Q) ^ 2) ^ 4) /
            (81 * (-(4 / 243 : R) * (S - 3 * Q) ^ 3) * (-(2500 / 6561 : R) * (S - 3 * Q) * (5 * T - 9) ^ 2) *
              ((64 / 4782969 : R) * (S - 3 * Q) ^ 6)) =
            (-(-(25 / 4 : R) * (4 / 27 : R) ^ 4) / (81 * (-(4 / 243 : R)) * (-(2500 / 6561 : R)) * (64 / 4782969 : R))) *
              (T / (S - 3 * Q) ^ 5) := by
          generalize (S - 3 * Q) = S3Q at hS3Q ⊢
          generalize (5 * T - 9) = T59 at hT59 ⊢
          field_simp [hS3Q, hT59]
        rw [hfac, hsc_A3]; ring
      have hden0 : (81 : R) * w1_Bv2 S Q * w1_D20_v S Q T * (w1_D33 S Q).val ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (ofNat_ne_zero 81) hBv2_ne) hD20_ne) hD33_ne
      rw [hbr]
      have hdiv_eq : (-(w1_w0 S Q T * (w1_cbD S Q).val ^ 4)) *
          (w1_D20_v S Q T * (w1_D33 S Q).val *
            (w1_D32_v S Q T / (w1_D33 S Q).val - (w1_D22 S Q).val / w1_D20_v S Q T * (w1_D30_v S Q T / (w1_D33 S Q).val))) =
          (81 * w1_Bv2 S Q * w1_D20_v S Q T * (w1_D33 S Q).val) * (w1_D20_v S Q T * (w1_D33 S Q).val) *
            ((-(w1_w0 S Q T * (w1_cbD S Q).val ^ 4) / (81 * w1_Bv2 S Q * w1_D20_v S Q T * (w1_D33 S Q).val)) *
              (w1_D32_v S Q T / (w1_D33 S Q).val - (w1_D22 S Q).val / w1_D20_v S Q T * (w1_D30_v S Q T / (w1_D33 S Q).val))) := by
        field_simp [hden0]
      rw [hdiv_eq, hsc_pref, hq32_33, hq22_20, hq30_33]
      have hfin : ((177147 / 400 : R) * T / (S - 3 * Q) ^ 5) *
          (-(375 / 2 : R) * (5 * T - 9) * (5 * T - 3) / (S - 3 * Q) ^ 2 -
            (-(4 / 39375 : R) * (77 * S - 210 * Q + 45) * (S - 3 * Q) ^ 3 / (5 * T - 9) ^ 2) *
              ((1687500 / 64 : R) * (5 * T - 1) * (5 * T - 9) ^ 3 / (S - 3 * Q) ^ 6)) = w1_A3_4 S Q T := by
        simp only [w1_A3_4]; field_simp [hS3Q, hT59]; ring
      rw [hfin]; ring
    rw [hnum_v, hC3_simp, hden_v, hres_fac]
    linear_combination ((w1_D22 S Q).val ^ 3 * w1_D20_v S Q T) * hcore
  have hA2_4 : (w1_num_pref S Q T).val * w1_C2_v S Q T d20e = (w1_den_pref S Q T d20e).val * w1_A2_4 S Q T := by
    have hC2_simp : w1_C2_v S Q T d20e = -((w1_D22 S Q).val ^ 3 * w1_D20_v S Q T ^ 2 * (w1_D33 S Q).val) := by
      simp only [w1_C2_v]; rw [hd1_fac]; ring
    have hcore : w1_w0 S Q T * (w1_cbD S Q).val ^ 4 =
        81 * w1_Bv2 S Q * w1_D20_v S Q T * (w1_D33 S Q).val * w1_A2_4 S Q T := by
      rw [hw0_s, hD20_v, hQ7_7]; simp only [w1_cbD, w1_Bv2, w1_A2_4]
      have hfac1 : (-(25 / 4 : R) * T * (5 * T - 9) ^ 2 / (S - 3 * Q) ^ 3) * ((4 / 27 : R) * (S - 3 * Q) ^ 2) ^ 4 =
          (-(25 / 4 : R) * (4 / 27 : R) ^ 4) * (T * (5 * T - 9) ^ 2 * (S - 3 * Q) ^ 5) := by field_simp [hS3Q]
      have hfac2 : 81 * (-(4 / 243 : R) * (S - 3 * Q) ^ 3) * (-(2500 / 6561 : R) * (S - 3 * Q) * (5 * T - 9) ^ 2) *
          ((64 / 4782969 : R) * (S - 3 * Q) ^ 6) * (-(177147 / 400 : R) * T / (S - 3 * Q) ^ 5) =
          (81 * (-(4 / 243 : R)) * (-(2500 / 6561 : R)) * (64 / 4782969 : R) * (-(177147 / 400 : R))) *
            (T * (5 * T - 9) ^ 2 * (S - 3 * Q) ^ 5) := by field_simp [hS3Q]
      rw [hfac1, hfac2, hsc_A2]
    rw [hnum_v, hC2_simp, hden_v, hres_fac]
    linear_combination ((w1_D22 S Q).val ^ 3 * w1_D20_v S Q T ^ 2 * (w1_D33 S Q).val) * hcore
  have hA4_dual : w1_num_pref S Q T * w1_C4_D S Q T d20e =
      w1_den_pref S Q T d20e * ⟨w1_A4_3 S Q T, w1_A4_4 S Q T⟩ := by
    ext
    · simp only [Dual.mul_val]; exact hA4_3
    · simp only [Dual.mul_eps]
      have hcb2_ne : (w1_cbD S Q).val ≠ 0 :=
        mul_ne_zero (div_ne_zero (ofNat_ne_zero 4) (ofNat_ne_zero 27)) (pow_ne_zero 2 hS3Q)
      have hw_rel : (w1_WD S Q T).eps * w1_Bv2 S Q = -(w1_WD S Q T).val * w1_Bv1 S Q T := by
        simp only [w1_WD, w1_w0, w1_w1]; field_simp [hBv2_ne]
      have hA4_ratio : w1_A4_4 S Q T =
          w1_A4_3 S Q T * (-(1 / 4116 : R) * P44_fn S Q T / ((S - 3 * Q) ^ 3 * (77 * S - 210 * Q + 45))) := by
        simp only [w1_A4_3, w1_A4_4]; field_simp [hS3Q, hL]; ring
      have hval_sym : (-((w1_WD S Q T).val * (w1_cbD S Q).val ^ 4)) *
            ((w1_D22 S Q).val ^ 2 * (w1_D20 S Q T d20e).val ^ 3 * (w1_D33 S Q).val) =
          (81 * w1_Bv2 S Q * (w1_D22 S Q).val ^ 3 * ((w1_D20 S Q T d20e).val ^ 3 * (w1_D33 S Q).val ^ 2)) * w1_A4_3 S Q T := by
        have h1 : (w1_C4_D S Q T d20e).val = (w1_D22 S Q).val ^ 2 * w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val := by
          rw [hC4_v, hd1_fac]; ring
        have h2 : (w1_den_pref S Q T d20e).val =
            81 * w1_Bv2 S Q * (w1_D22 S Q).val ^ 3 * (w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val ^ 2) := by
          rw [hden_v, hres_fac]
        change (-((w1_w0 S Q T) * (w1_cbD S Q).val ^ 4)) * ((w1_D22 S Q).val ^ 2 * w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val) =
          (81 * w1_Bv2 S Q * (w1_D22 S Q).val ^ 3 * (w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val ^ 2)) * w1_A4_3 S Q T
        rw [← hnum_v, ← h1, ← h2]; exact hA4_3
      have hr5678' := W1_inf_r5678_alg (w1_D22 S Q).val (w1_D20_v S Q T) (w1_D33 S Q).val
        (w1_D21_v S Q T) (w1_D32_v S Q T) (w1_D31_v S Q T) (w1_D30_v S Q T) hD22_ne hD20_ne hD33_ne
      have hq22_33 : (w1_D22 S Q).val / (w1_D33 S Q).val = (81 / 28 : R) * (77 * S - 210 * Q + 45) / (S - 3 * Q) ^ 2 := by
        rw [hQ5_5, hQ7_7]; field_simp [hS3Q]; ring
      have hq31_33 : w1_D31_v S Q T / (w1_D33 S Q).val = (5625 / 112 : R) * (5 * T - 9) ^ 2 * (5 * T - 3) ^ 2 *
          (-49 * S ^ 2 + 140 * S * Q - 90 * Q - 90) / (S - 3 * Q) ^ 6 := by
        rw [hD31_v, hQ7_7]; field_simp [hS3Q]; ring
      have hq21_20 : w1_D21_v S Q T / w1_D20_v S Q T = (2 / 1575 : R) * (5 * T - 3) / (5 * T - 9) *
          (-77 * S ^ 2 + 210 * S * Q - 45 * S - 135 * Q - 270) := by
        rw [hD21_v, hD20_v]; field_simp [hS3Q, hT59]; ring
      have hq30_20 : w1_D30_v S Q T / w1_D20_v S Q T = -(25 / 27 : R) * (5 * T - 1) * (5 * T - 9) / (S - 3 * Q) := by
        rw [hD30_v, hD20_v]; field_simp [hS3Q, hT59]; ring
      have hr3 : -(w1_D22 S Q).eps / (w1_D22 S Q).val =
          -(238140 * Q ^ 4 + 1063692 * Q ^ 3 * S + 1224720 * Q ^ 3 - 1363572 * Q ^ 2 * S ^ 2 -
            1462860 * Q ^ 2 * S + 267300 * Q ^ 2 + 525084 * Q * S ^ 3 + 618030 * Q * S ^ 2 -
            124740 * Q * S - 145800 * Q - 65905 * S ^ 4 - 90090 * S ^ 3 - 72900) /
            (28 * (S - 3 * Q) ^ 3 * (77 * S - 210 * Q + 45)) := by
        rw [div_eq_div_iff hD22_ne (mul_ne_zero (mul_ne_zero (ofNat_ne_zero 28) (pow_ne_zero 3 hS3Q)) hL)]
        rw [hQ5_5]; simp only [w1_D22, Q5_c4]; ring
      have hr4 : -(w1_D33 S Q).eps / (w1_D33 S Q).val =
          -(13671 * Q ^ 2 - 13524 * Q * S + 4455 * Q + 2989 * S ^ 2 + 4455) / (14 * (S - 3 * Q) ^ 2) := by
        rw [div_eq_div_iff hD33_ne (mul_ne_zero (ofNat_ne_zero 14) (pow_ne_zero 2 hS3Q))]
        rw [hQ7_7]; simp only [w1_D33, Q7_c6]; ring
      have hsum8 :
          (-2 * w1_Bv1 S Q T / w1_Bv2 S Q + 4 * (w1_cbD S Q).eps / (w1_cbD S Q).val -
           (w1_D22 S Q).eps / (w1_D22 S Q).val - (w1_D33 S Q).eps / (w1_D33 S Q).val -
           w1_D21_v S Q T ^ 2 / ((w1_D22 S Q).val * (w1_D20 S Q T d20e).val) -
           w1_d1_sub_v S Q T / ((w1_D22 S Q).val * (w1_D20 S Q T d20e).val * (w1_D33 S Q).val) -
           w1_res_sub_v S Q T / ((w1_D20 S Q T d20e).val ^ 3 * (w1_D33 S Q).val ^ 2) +
           (w1_P1_4_v S Q T * w1_d0_v S Q T) / ((w1_D22 S Q).val ^ 2 * (w1_D20 S Q T d20e).val ^ 3 * (w1_D33 S Q).val)) -
          (-(1 / 4116 : R) * P44_fn S Q T / ((S - 3 * Q) ^ 3 * (77 * S - 210 * Q + 45))) = 0 := by
        change (-2 * w1_Bv1 S Q T / w1_Bv2 S Q + 4 * (w1_cbD S Q).eps / (w1_cbD S Q).val -
           (w1_D22 S Q).eps / (w1_D22 S Q).val - (w1_D33 S Q).eps / (w1_D33 S Q).val -
           w1_D21_v S Q T ^ 2 / ((w1_D22 S Q).val * w1_D20_v S Q T) -
           w1_d1_sub_v S Q T / ((w1_D22 S Q).val * w1_D20_v S Q T * (w1_D33 S Q).val) -
           w1_res_sub_v S Q T / (w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val ^ 2) +
           (w1_P1_4_v S Q T * w1_d0_v S Q T) / ((w1_D22 S Q).val ^ 2 * w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val)) - _ = 0
        have hre := ring_regroup8 (-2 * w1_Bv1 S Q T / w1_Bv2 S Q) (4 * (w1_cbD S Q).eps / (w1_cbD S Q).val)
          (w1_D22 S Q).eps (w1_D22 S Q).val (w1_D33 S Q).eps (w1_D33 S Q).val
          (w1_D21_v S Q T ^ 2 / ((w1_D22 S Q).val * w1_D20_v S Q T))
          (w1_d1_sub_v S Q T / ((w1_D22 S Q).val * w1_D20_v S Q T * (w1_D33 S Q).val))
          (w1_res_sub_v S Q T / (w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val ^ 2))
          ((w1_P1_4_v S Q T * w1_d0_v S Q T) / ((w1_D22 S Q).val ^ 2 * w1_D20_v S Q T ^ 3 * (w1_D33 S Q).val))
        rw [hre]
        simp only [w1_d1_sub_v, w1_res_sub_v, w1_P1_4_v, w1_d0_v, w1_diff12_v]
        rw [neg_div] at hr5678'
        rw [hr5678', hr3, hr4, hq22_33, hq32_33, hq31_33, hq21_20, hq30_20, hq22_20]
        simpa only [w1_Bv2, w1_Bv1, w1_cbD] using W1_inf_weights_hsum8 S Q T hS3Q hL hT59
      exact W1_inf_log_deriv (w1_Bv2 S Q) (w1_Bv1 S Q T) (w1_WD S Q T) (w1_cbD S Q)
        (w1_D22 S Q) (w1_D20 S Q T d20e) (w1_D33 S Q)
        (w1_D21_v S Q T) (w1_d1_sub_v S Q T) (w1_res_sub_v S Q T) (w1_P1_4_v S Q T * w1_d0_v S Q T)
        (w1_A4_3 S Q T) (w1_A4_4 S Q T)
        (-(1 / 4116 : R) * P44_fn S Q T / ((S - 3 * Q) ^ 3 * (77 * S - 210 * Q + 45)))
        hBv2_ne hcb2_ne hD22_ne hD20_ne hD33_ne hw_rel hA4_ratio hval_sym hsum8
        (w1_num_pref S Q T) (w1_d1_D S Q T d20e) (w1_res_D S Q T d20e)
        (w1_den_pref S Q T d20e) (w1_P0_4_D S Q T d20e) (w1_C4_D S Q T d20e)
        rfl rfl rfl rfl rfl rfl
  exact ⟨hres_v, hden_ne, hA4_dual, hA3_4, hA2_4⟩



private theorem localInf_weights_alg_proof : LocalInfWeightsAlgSpec :=
  ⟨fun S Q T d20e hS3Q hL hT59 => W1_inf_weights_alg S Q T d20e hS3Q hL hT59⟩

end SymmetricSexticResidual.LocalResidueInfAlg

theorem solution : SymmetricSexticResidual.LocalResidueInfAlg.LocalInfWeightsAlgSpec :=
  SymmetricSexticResidual.LocalResidueInfAlg.localInf_weights_alg_proof
