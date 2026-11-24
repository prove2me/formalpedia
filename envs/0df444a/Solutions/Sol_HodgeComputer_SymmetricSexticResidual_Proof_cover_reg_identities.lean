-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.cover_reg_identities
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T09:27:18.569833+00:00
-- url     : https://prove2.me/submissions/845fca58-9b78-4fa5-8093-1b408def6ef2

import Definitions.Def_HodgeComputerFormal_CoverResidues
import Definitions.Def_HodgeComputerSSR_SheetCalculus
import Definitions.Def_HodgeComputerSSR_CoverParams
import Definitions.Def_HodgeComputerSSR_CoverFactors
import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.CoverResidue
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators Matrix Classical

lemma numM_shear_inv {F : Type*} [Field F] [CharZero F] (mi : Fin 10) (S Q T a b U V : F) :
    numM mi a b (S - a * T) (Q - b * T) U V =
      let a2' := dH_dS a b U V
      let a0' := dH_dS S Q U V
      let a1' := dH_dS (a + S) (b + Q) U V - a2' - a0'
      let b2' := dH_dQ a b 0 U V
      let b0' := dH_dQ S Q 1 U V
      let b1' := (dH_dQ (a + S) (b + Q) 0 U V - b2' - dH_dQ S Q 0 U V) + (10 / 7) * b * U * V
      let d20' := a2' * b0' - a0' * b2'
      let d21' := a2' * b1' - a1' * b2'
      let d10' := a1' * b0' - a0' * b1'
      let (m2', m1', m0') : F × F × F := match mi with
        | 0 => (a ^ 2, 2 * a * S, S ^ 2)
        | 1 => (a * b, a * Q + b * S, S * Q)
        | 2 => (b ^ 2, 2 * b * Q, Q ^ 2)
        | 3 => (a, a * T + S, S * T)
        | 4 => (0, a, S)
        | 5 => (b, b * T + Q, Q * T)
        | 6 => (0, b, Q)
        | 7 => (1, 2 * T, T ^ 2)
        | 8 => (0, 1, T)
        | 9 => (0, 0, 1)
      (1 / 16) * (m2' * d10' - m1' * d20' + m0' * d21') := by
  have hshear (a2 a1 a0 b2 b1 b0 m2 m1 m0 : F) :
      let a1' := a1 + 2 * T * a2; let a0' := a0 + T * a1 + T ^ 2 * a2
      let b1' := b1 + 2 * T * b2; let b0' := b0 + T * b1 + T ^ 2 * b2
      let m1' := m1 + 2 * T * m2; let m0' := m0 + T * m1 + T ^ 2 * m2
      m2 * (a1 * b0 - a0 * b1) - m1 * (a2 * b0 - a0 * b2) + m0 * (a2 * b1 - a1 * b2) =
      m2 * (a1' * b0' - a0' * b1') - m1' * (a2 * b0' - a0' * b2) + m0' * (a2 * b1' - a1' * b2) := by
    ring
  have ha1' : q1_a1 a b (S - a * T) (Q - b * T) U V + 2 * T * q1_a2 a b U V =
      dH_dS (a + S) (b + Q) U V - dH_dS a b U V - dH_dS S Q U V := by
    simp only [q1_a1, q1_a2, dH_dS]; ring
  have ha0' : q1_a0 (S - a * T) (Q - b * T) U V + T * q1_a1 a b (S - a * T) (Q - b * T) U V +
      T ^ 2 * q1_a2 a b U V = dH_dS S Q U V := by
    simp only [q1_a0, q1_a1, q1_a2, dH_dS]; ring
  have hb1' : q2_b1 a b (S - a * T) (Q - b * T) U V + 2 * T * q2_b2 a b U V =
      (dH_dQ (a + S) (b + Q) 0 U V - dH_dQ a b 0 U V - dH_dQ S Q 0 U V) + (10 / 7) * b * U * V := by
    simp only [q2_b1, q2_b2, dH_dQ]; ring
  have hb0' : q2_b0 (S - a * T) (Q - b * T) U V + T * q2_b1 a b (S - a * T) (Q - b * T) U V +
      T ^ 2 * q2_b2 a b U V = dH_dQ S Q 1 U V := by
    simp only [q2_b0, q2_b1, q2_b2, dH_dQ]; ring
  dsimp only [numM]
  fin_cases mi <;>
    (dsimp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk];
     rw [hshear (q1_a2 a b U V) (q1_a1 a b (S - a * T) (Q - b * T) U V) (q1_a0 (S - a * T) (Q - b * T) U V)
       (q2_b2 a b U V) (q2_b1 a b (S - a * T) (Q - b * T) U V) (q2_b0 (S - a * T) (Q - b * T) U V)];
     rw [ha1', ha0', hb1', hb0'];
     dsimp only [q1_a2, q2_b2];
     ring)

/-- Every `numM mi` along any affine line `(a(z), b(z))` has degree `≤ 3` in `z`. -/
lemma numM_isPolyDeg3 {F : Type*} [Field F] [CharZero F]
    (mi : Fin 10) (S Q T U V a1 a0 b1 b0 : F) :
    IsPolyDeg 3 (fun z => numM mi (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V) := by
  have hfun : (fun z => numM mi (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V) = fun z =>
      let a := a1 * z + a0; let b := b1 * z + b0
      let a2' := dH_dS a b U V
      let a0' := dH_dS S Q U V
      let a1' := dH_dS (a + S) (b + Q) U V - a2' - a0'
      let b2' := dH_dQ a b 0 U V
      let b0' := dH_dQ S Q 1 U V
      let b1' := (dH_dQ (a + S) (b + Q) 0 U V - b2' - dH_dQ S Q 0 U V) + (10 / 7) * b * U * V
      let d20' := a2' * b0' - a0' * b2'
      let d21' := a2' * b1' - a1' * b2'
      let d10' := a1' * b0' - a0' * b1'
      let (m2', m1', m0') : F × F × F := match mi with
        | 0 => (a ^ 2, 2 * a * S, S ^ 2)
        | 1 => (a * b, a * Q + b * S, S * Q)
        | 2 => (b ^ 2, 2 * b * Q, Q ^ 2)
        | 3 => (a, a * T + S, S * T)
        | 4 => (0, a, S)
        | 5 => (b, b * T + Q, Q * T)
        | 6 => (0, b, Q)
        | 7 => (1, 2 * T, T ^ 2)
        | 8 => (0, 1, T)
        | 9 => (0, 0, 1)
      (1 / 16) * (m2' * d10' - m1' * d20' + m0' * d21') :=
    funext (fun z => numM_shear_inv mi S Q T (a1 * z + a0) (b1 * z + b0) U V)
  rw [hfun]
  have ha : IsPolyDeg 1 (fun z => a1 * z + a0) := IsPolyDeg.linear a1 a0
  have hb : IsPolyDeg 1 (fun z => b1 * z + b0) := IsPolyDeg.linear b1 b0
  have ha2' : IsPolyDeg 2 (fun z => dH_dS (a1 * z + a0) (b1 * z + b0) U V) := by
    have h1 := ((ha.sub (hb.smul_left 3)).sq).smul_left (-(4 / 81)) |>.smul_right (U ^ 2) |>.smul_right V
    have h2 := (((ha.sq.smul_left (143 / 81)).sub ((ha.mul hb).smul_left (184 / 27))).add
      (hb.sq.smul_left (52 / 9))).smul_right U |>.smul_right V
    have h3 := (((ha.smul_left 5).sub (hb.smul_left 9)).mul
      ((ha.smul_left 15).sub (hb.smul_left 9))).smul_left (25 / 243) |>.smul_right V
    exact ((h1.add h2).sub h3).congr (fun z => by simp only [dH_dS]; ring)
  have hb2' : IsPolyDeg 2 (fun z => dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V) := by
    have h1 := ((ha.sub (hb.smul_left 3)).sq).smul_left (4 / 27) |>.smul_right (U ^ 2) |>.smul_right V
    have h2 := (((ha.sq.smul_left (-(92 / 27))).add ((ha.mul hb).smul_left (104 / 9))).sub
      (hb.sq.smul_left (22 / 3))).smul_right U |>.smul_right V
    have h3 := (ha.mul ((ha.smul_left 5).sub (hb.smul_left 9))).smul_left (50 / 27) |>.smul_right V
    exact ((h1.add h2).add h3).congr (fun z => by simp only [dH_dQ]; ring)
  -- Notice `a1'` and `b1'` are linear in `(a, b)`!
  have ha1'_eq : ∀ z : F, dH_dS ((a1 * z + a0) + S) ((b1 * z + b0) + Q) U V -
      dH_dS (a1 * z + a0) (b1 * z + b0) U V - dH_dS S Q U V =
      (a1 * z + a0) * (-(8 / 81) * (S - 3 * Q) * U ^ 2 * V + ((286 / 81) * S - (184 / 27) * Q) * U * V -
        (25 / 243) * (150 * S - 180 * Q) * V) +
      (b1 * z + b0) * ((24 / 81) * (S - 3 * Q) * U ^ 2 * V + (-(184 / 27) * S + (104 / 9) * Q) * U * V -
        (25 / 243) * (-180 * S + 162 * Q) * V) := by
    intro z; simp only [dH_dS]; ring
  have hb1'_eq : ∀ z : F, (dH_dQ ((a1 * z + a0) + S) ((b1 * z + b0) + Q) 0 U V -
      dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V - dH_dQ S Q 0 U V) + (10 / 7) * (b1 * z + b0) * U * V =
      (a1 * z + a0) * ((8 / 27) * (S - 3 * Q) * U ^ 2 * V + (-(184 / 27) * S + (104 / 9) * Q) * U * V +
        (50 / 27) * (10 * S - 9 * Q) * V) +
      (b1 * z + b0) * (-(24 / 27) * (S - 3 * Q) * U ^ 2 * V + ((104 / 9) * S - (44 / 3) * Q + 10 / 7) * U * V +
        (50 / 27) * (-9 * S) * V) := by
    intro z; simp only [dH_dQ]; ring
  have ha1' : IsPolyDeg 1 (fun z => dH_dS ((a1 * z + a0) + S) ((b1 * z + b0) + Q) U V -
      dH_dS (a1 * z + a0) (b1 * z + b0) U V - dH_dS S Q U V) := by
    simp_rw [ha1'_eq]; exact (ha.smul_right _).add (hb.smul_right _)
  have hb1' : IsPolyDeg 1 (fun z => (dH_dQ ((a1 * z + a0) + S) ((b1 * z + b0) + Q) 0 U V -
      dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V - dH_dQ S Q 0 U V) + (10 / 7) * (b1 * z + b0) * U * V) := by
    simp_rw [hb1'_eq]; exact (ha.smul_right _).add (hb.smul_right _)
  have hd10 : IsPolyDeg 1 (fun z =>
      (dH_dS ((a1 * z + a0) + S) ((b1 * z + b0) + Q) U V - dH_dS (a1 * z + a0) (b1 * z + b0) U V - dH_dS S Q U V) *
        dH_dQ S Q 1 U V -
      dH_dS S Q U V * ((dH_dQ ((a1 * z + a0) + S) ((b1 * z + b0) + Q) 0 U V -
        dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V - dH_dQ S Q 0 U V) + (10 / 7) * (b1 * z + b0) * U * V)) :=
    (ha1'.smul_right _).sub (hb1'.smul_left _)
  have hd20 : IsPolyDeg 2 (fun z =>
      dH_dS (a1 * z + a0) (b1 * z + b0) U V * dH_dQ S Q 1 U V -
      dH_dS S Q U V * dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V) :=
    (ha2'.smul_right _).sub (hb2'.smul_left _)
  have hd21 : IsPolyDeg 3 (fun z =>
      dH_dS (a1 * z + a0) (b1 * z + b0) U V * ((dH_dQ ((a1 * z + a0) + S) ((b1 * z + b0) + Q) 0 U V -
        dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V - dH_dQ S Q 0 U V) + (10 / 7) * (b1 * z + b0) * U * V) -
      (dH_dS ((a1 * z + a0) + S) ((b1 * z + b0) + Q) U V - dH_dS (a1 * z + a0) (b1 * z + b0) U V - dH_dS S Q U V) *
        dH_dQ (a1 * z + a0) (b1 * z + b0) 0 U V) :=
    (ha2'.mul hb1').sub ((ha1'.mul hb2').mono (by omega))
  have hcomb {m2 m1 : F → F} {m0 : F} (hm2 : IsPolyDeg 2 m2) (hm1 : IsPolyDeg 1 m1) :
      IsPolyDeg 3 (fun z => (1 / 16 : F) * (m2 z * _ - m1 z * _ + m0 * _)) :=
    (((hm2.mul hd10).sub ((hm1.mul hd20).mono (by omega))).add (hd21.smul_left m0)).smul_left (1 / 16)
  fin_cases mi
  · exact hcomb ha.sq ((ha.smul_left 2).smul_right S)
  · exact hcomb (ha.mul hb) ((ha.smul_right Q).add (hb.smul_right S))
  · exact hcomb hb.sq ((hb.smul_left 2).smul_right Q)
  · exact hcomb (ha.mono (by omega)) ((ha.smul_right T).add ((IsPolyDeg.const S).mono (by omega)))
  · exact hcomb ((IsPolyDeg.const 0).mono (by omega)) ha
  · exact hcomb (hb.mono (by omega)) ((hb.smul_right T).add ((IsPolyDeg.const Q).mono (by omega)))
  · exact hcomb ((IsPolyDeg.const 0).mono (by omega)) hb
  · exact hcomb ((IsPolyDeg.const 1).mono (by omega)) ((IsPolyDeg.const (2 * T)).mono (by omega))
  · exact hcomb ((IsPolyDeg.const 0).mono (by omega)) ((IsPolyDeg.const 1).mono (by omega))
  · exact hcomb ((IsPolyDeg.const 0).mono (by omega)) ((IsPolyDeg.const 0).mono (by omega))

/-- `SheetCalculus.P18_of` along any affine line `(a(z), b(z))` has degree `≤ 4` in `z`. -/
lemma P18_of_isPolyDeg4 {F : Type*} [Field F] [CharZero F]
    (S Q T x y U V a1 a0 b1 b0 : F) :
    IsPolyDeg 4 (fun z => SheetCalculus.P18_of S Q T x y (a1 * z + a0) (b1 * z + b0) U V) := by
  have ha : IsPolyDeg 1 (fun z => a1 * z + a0) := IsPolyDeg.linear a1 a0
  have hb : IsPolyDeg 1 (fun z => b1 * z + b0) := IsPolyDeg.linear b1 b0
  have hm := fun i => numM_isPolyDeg3 i S Q T U V a1 a0 b1 b0
  have hA0U : IsPolyDeg 3 (fun z => A_0U (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V) := by
    refine ((((((hm 0).smul_left 5).sub ((hm 1).smul_left 9)).smul_left (-(19708 / 1257375))).add
      ((((hm 1).smul_left 5).sub ((hm 2).smul_left 9)).smul_left (1472 / 1257375))).sub
      ((((hm 3).smul_left 5).sub ((hm 5).smul_left 9)).smul_left (16 / 729)) |>.add
      ((((hm 4).smul_left 5).sub ((hm 6).smul_left 9)).smul_left (188 / 2025))).congr
      (fun z => by simp only [A_0U])
  have hA0V : IsPolyDeg 3 (fun z => A_0V (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V) := by
    refine ((((((hm 3).smul_left 5).sub ((hm 4).smul_left 9)).smul_left (-(892 / 3645))).add
      ((((hm 5).smul_left 5).sub ((hm 6).smul_left 9)).smul_left (40 / 81))).sub
      ((((hm 7).smul_left 5).sub ((hm 8).smul_left 9)).smul_left (112 / 2395)) |>.add
      ((((hm 8).smul_left 5).sub ((hm 9).smul_left 9)).smul_left (392 / 11975))).congr
      (fun z => by simp only [A_0V])
  have hAY : IsPolyDeg 3 (fun z => A_Y (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V) := by
    have t1 := (((((hm 3).smul_left 25).sub ((hm 4).smul_left 45)).sub ((hm 5).smul_left 45)).add
      ((hm 6).smul_left 81)).smul_left (-(100 / 243))
    have t2 := (((((((hm 0).smul_left 5).sub ((hm 1).smul_left 9)).smul_left (-(907876 / 33949125))).add
      ((((hm 1).smul_left 5).sub ((hm 2).smul_left 9)).smul_left (2258324 / 33949125))).add
      ((((hm 3).smul_left 5).sub ((hm 5).smul_left 9)).smul_left (8 / 243))).sub
      ((((hm 4).smul_left 5).sub ((hm 6).smul_left 9)).smul_left (64 / 675))).smul_left V
    have t3 := (((((hm 0).add ((hm 6).smul_left (2790 / 77))).add ((hm 8).smul_left 28)).sub
      ((hm 9).smul_left (5904 / 77))).smul_left (-(123236 / 24249375)) |>.add
      (((((hm 1).add ((hm 6).smul_left (927 / 77))).add ((hm 8).smul_left (49 / 5))).sub
      ((hm 9).smul_left (21159 / 770))).smul_left (492944 / 33949125))).smul_left (U * V)
    exact ((t1.add t2).add t3).congr (fun z => by simp only [A_Y])
  have hAX : IsPolyDeg 3 (fun z => A_X (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V) := by
    refine ((((((hm 3).smul_left 5).sub ((hm 4).smul_left 9)).smul_left (-(8 / 405))).sub
      ((((hm 7).smul_left 5).sub ((hm 8).smul_left 9)).smul_left (476 / 7185))).add
      ((((hm 8).smul_left 5).sub ((hm 9).smul_left 9)).smul_left (6916 / 35925))).smul_left U |>.congr
      (fun z => by simp only [A_X])
  have hM0 : IsPolyDeg 3 (fun z => A_0U (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V / U +
      A_0V (a1 * z + a0) (b1 * z + b0) (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V / V) :=
    (hA0U.div_const U).add (hA0V.div_const V)
  have hdot (v : Fin 3 → F) : IsPolyDeg 1 (fun z => dot_ab v (a1 * z + a0) (b1 * z + b0)) := by
    unfold dot_ab
    exact ((ha.smul_left (v 0)).add (hb.smul_left (v 1))).add ((IsPolyDeg.const (v 2)).mono (by omega))
  have hqY : IsPolyDeg 1 (fun z => dot_ab (QY_num S Q T x y U V) (a1 * z + a0) (b1 * z + b0) / v_of V) :=
    (hdot _).div_const _
  have hqX : IsPolyDeg 1 (fun z => dot_ab (QX_num S Q T x y U V) (a1 * z + a0) (b1 * z + b0) / u_of U) :=
    (hdot _).div_const _
  have hcA1 : IsPolyDeg 1 (fun z => cA1_of S Q T (a1 * z + a0) (b1 * z + b0) U V) := by
    unfold cA1_of
    exact ((ha.smul_left _).add (hb.smul_left _)).add ((IsPolyDeg.const _).mono (by omega))
  have hq1 : IsPolyDeg 1 (fun z =>
      H0_of S Q T * A1_of S Q U V * (dot_ab (QY_num S Q T x y U V) (a1 * z + a0) (b1 * z + b0) / v_of V) +
      H0_of S Q T * B1_of T U V * (dot_ab (QX_num S Q T x y U V) (a1 * z + a0) (b1 * z + b0) / u_of U) +
      (cA1_of S Q T (a1 * z + a0) (b1 * z + b0) U V / v_of V) * EB_of S Q T x y U V) :=
    ((hqY.smul_left _).add (hqX.smul_left _)).add ((hcA1.div_const _).smul_right _)
  unfold P18_of
  exact (hM0.mul hq1).add (((hAY.mul hqY).add (hAX.mul hqX)).smul_right _)


section CoverEqRest
variable {F : Type*} [Field F] [CharZero F] (φ : K5 →+* F)
lemma E1_of_cover (a b U W : F) (hU : U ≠ 0)
    (hW : W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0) :
    U * E_fn 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pU φ k5Params.ca_h U * (W * a) + pU φ k5Params.cb_h U * (W * b) +
      pUW φ k5Params.c0W U W := by
  have hc0W_eq : pUW φ k5Params.c0W U W =
      φ k5Params.c0_V2 * W ^ 2 + φ k5Params.c0_V1 * U * W + φ k5Params.c0_V0 * U ^ 2 := by
    simp only [pUW_eq, CoverParams.c0W, CoverParams.toUW, pU,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination -φ k5Params.c0_V2 * hW
  rw [hc0W_eq]
  simp only [E_fn, H_cub, pU, CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
    CoverParams.c0_V2, CoverParams.c0_V1, CoverParams.c0_V0,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
    k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

lemma E2_of_cover (a b U W : F) (hU : U ≠ 0)
    (hW : W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0) :
    U * W * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pU φ k5Params.q20 U * (W * a) ^ 2 + pU φ k5Params.q11 U * (W * a) * (W * b) +
      pU φ k5Params.q02 U * (W * b) ^ 2 + W * pUW φ k5Params.k2W U W := by
  have hk2W_eq : pUW φ k5Params.k2W U W =
      φ k5Params.k2_V2 * W ^ 2 + φ k5Params.k2_V1 * U * W + φ k5Params.k2_V0 * U ^ 2 := by
    simp only [pUW_eq, CoverParams.k2W, CoverParams.toUW, pU,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination -φ k5Params.k2_V2 * hW
  rw [hk2W_eq]
  simp only [E_fn, H_cub, pU, CoverParams.q20, CoverParams.q11, CoverParams.q02, CoverParams.quadU,
    CoverParams.k2_V2, CoverParams.k2_V1, CoverParams.k2_V0,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
    k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

lemma E3_of_cover (a b U W : F) (hU : U ≠ 0)
    (hW : W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0) :
    U * W ^ 2 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pU φ k5Params.c30 U * (W * a) ^ 3 + pU φ k5Params.c21 U * (W * a) ^ 2 * (W * b) +
      pU φ k5Params.c12 U * (W * a) * (W * b) ^ 2 + pU φ k5Params.c03 U * (W * b) ^ 3 +
      W ^ 2 * pUW φ k5Params.k3W U W := by
  have hk3W_eq : pUW φ k5Params.k3W U W =
      φ k5Params.k3_V2 * W ^ 2 + φ k5Params.k3_V1 * U * W + φ k5Params.k3_V0 * U ^ 2 := by
    simp only [pUW_eq, CoverParams.k3W, CoverParams.toUW, pU,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination -φ k5Params.k3_V2 * hW
  rw [hk3W_eq]
  simp only [E_fn, H_cub, pU, CoverParams.c30, CoverParams.c21, CoverParams.c12, CoverParams.c03,
    CoverParams.quadU, CoverParams.k3_V2, CoverParams.k3_V1, CoverParams.k3_V0,
    CoverParams.inv9, CoverParams.inv27, CoverParams.inv243, k5Params_inv3,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_zero,
    eval_add, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat, eval_zero,
    map_zero, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU]; ring

lemma E2_z_of_cover (z U W : F) (hU : U ≠ 0) (hW0 : W ≠ 0) (hcb : pU φ k5Params.cb_h U ≠ 0)
    (hW : W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0) :
    let a := z / W
    let b := -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) / (W * pU φ k5Params.cb_h U)
    U * W * pU φ k5Params.cb_h U ^ 2 * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pUW φ k5Params.d2_2 U W * z ^ 2 + pUW φ k5Params.d2_1 U W * z + pUW φ k5Params.d2_0 U W := by
  intro a b
  have h2 := E2_of_cover φ a b U W hU hW
  have hWa : W * a = z := mul_div_cancel₀ z hW0
  have hWb : pU φ k5Params.cb_h U * (W * b) = -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) := by
    dsimp only [b]; field_simp [hW0, hcb]
  have hd22 : pUW φ k5Params.d2_2 U W = pU φ k5Params.Q5_z U := by
    simp [pUW, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, pU]
  have hd21 : pUW φ k5Params.d2_1 U W =
      (-pU φ k5Params.q11 U * pU φ k5Params.cb_h U + 2 * pU φ k5Params.q02 U * pU φ k5Params.ca_h U) *
      pUW φ k5Params.c0W U W := by
    simp [pUW, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul, pU]
  have hd20 : pUW φ k5Params.d2_0 U W =
      pU φ k5Params.q02 U * pUW φ k5Params.c0W U W ^ 2 +
      pU φ k5Params.cb_h U ^ 2 * (W * pUW φ k5Params.k2W U W) := by
    simp only [pUW, CoverParams.d2_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul,
      PairAlg.map_mul, PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul,
      RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom,
      Polynomial.map_pow, eval_pow, pU]
    rw [PairAlg.evalAt_mul _ _ W hW, PairAlg.evalAt_mul _ _ W hW, PairAlg.evalAt_W]
    ring
  rw [hd22, hd21, hd20]
  have hQ5 : pU φ k5Params.Q5_z U =
      pU φ k5Params.q20 U * pU φ k5Params.cb_h U ^ 2 -
      pU φ k5Params.q11 U * pU φ k5Params.ca_h U * pU φ k5Params.cb_h U +
      pU φ k5Params.q02 U * pU φ k5Params.ca_h U ^ 2 := by
    simp [pU, CoverParams.Q5_z]
  rw [hQ5]
  calc U * W * pU φ k5Params.cb_h U ^ 2 * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U)
      = pU φ k5Params.cb_h U ^ 2 * (U * W * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U)) := by ring
    _ = pU φ k5Params.cb_h U ^ 2 * (pU φ k5Params.q20 U * (W * a) ^ 2 +
        pU φ k5Params.q11 U * (W * a) * (W * b) + pU φ k5Params.q02 U * (W * b) ^ 2 +
        W * pUW φ k5Params.k2W U W) := by rw [h2]
    _ = _ := by
      rw [hWa]
      linear_combination (pU φ k5Params.q11 U * z * pU φ k5Params.cb_h U +
        pU φ k5Params.q02 U * (pU φ k5Params.cb_h U * (W * b) - (pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W))) * hWb

lemma E3_z_of_cover (z U W : F) (hU : U ≠ 0) (hW0 : W ≠ 0) (hcb : pU φ k5Params.cb_h U ≠ 0)
    (hW : W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0) :
    let a := z / W
    let b := -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) / (W * pU φ k5Params.cb_h U)
    U * W ^ 2 * pU φ k5Params.cb_h U ^ 3 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pUW φ k5Params.d3_3 U W * z ^ 3 + pUW φ k5Params.d3_2 U W * z ^ 2 +
      pUW φ k5Params.d3_1 U W * z + pUW φ k5Params.d3_0 U W := by
  intro a b
  have h3 := E3_of_cover φ a b U W hU hW
  have hWa : W * a = z := mul_div_cancel₀ z hW0
  have hWb : pU φ k5Params.cb_h U * (W * b) = -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) := by
    dsimp only [b]; field_simp [hW0, hcb]
  have hd33 : pUW φ k5Params.d3_3 U W = pU φ k5Params.Q7_z U := by
    simp [pUW, CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, pU]
  have hd32 : pUW φ k5Params.d3_2 U W =
      (-pU φ k5Params.c21 U * pU φ k5Params.cb_h U ^ 2 +
       2 * pU φ k5Params.c12 U * pU φ k5Params.ca_h U * pU φ k5Params.cb_h U -
       3 * pU φ k5Params.c03 U * pU φ k5Params.ca_h U ^ 2) * pUW φ k5Params.c0W U W := by
    simp [pUW, CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul, pU]
  have hd31 : pUW φ k5Params.d3_1 U W =
      (pU φ k5Params.c12 U * pU φ k5Params.cb_h U - 3 * pU φ k5Params.c03 U * pU φ k5Params.ca_h U) *
      pUW φ k5Params.c0W U W ^ 2 := by
    simp only [pUW, CoverParams.d3_1, CoverParams.pmul, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.evalAt_smul, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, eval_sub, eval_mul, eval_ofNat, pU]
    rw [PairAlg.evalAt_mul _ _ W hW]; ring
  have hd30 : pUW φ k5Params.d3_0 U W =
      -pU φ k5Params.c03 U * pUW φ k5Params.c0W U W ^ 3 +
      pU φ k5Params.cb_h U ^ 3 * (W ^ 2 * pUW φ k5Params.k3W U W) := by
    simp only [pUW, CoverParams.d3_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul,
      PairAlg.map_mul, PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul,
      RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom,
      Polynomial.map_neg, Polynomial.map_pow, eval_neg, eval_pow, pU]
    rw [PairAlg.evalAt_mul _ _ W hW, PairAlg.evalAt_mul _ _ W hW,
      PairAlg.evalAt_mul _ _ W hW, PairAlg.evalAt_mul _ _ W hW, PairAlg.evalAt_W]
    ring
  rw [hd33, hd32, hd31, hd30]
  have hQ7 : pU φ k5Params.Q7_z U =
      pU φ k5Params.c30 U * pU φ k5Params.cb_h U ^ 3 -
      pU φ k5Params.c21 U * pU φ k5Params.ca_h U * pU φ k5Params.cb_h U ^ 2 +
      pU φ k5Params.c12 U * pU φ k5Params.ca_h U ^ 2 * pU φ k5Params.cb_h U -
      pU φ k5Params.c03 U * pU φ k5Params.ca_h U ^ 3 := by
    simp [pU, CoverParams.Q7_z]
  rw [hQ7]
  set Y := pU φ k5Params.cb_h U * (W * b)
  set Z := -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W)
  have hstep : U * W ^ 2 * pU φ k5Params.cb_h U ^ 3 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pU φ k5Params.c30 U * pU φ k5Params.cb_h U ^ 3 * z ^ 3 +
      pU φ k5Params.c21 U * pU φ k5Params.cb_h U ^ 2 * z ^ 2 * Y +
      pU φ k5Params.c12 U * pU φ k5Params.cb_h U * z * Y ^ 2 +
      pU φ k5Params.c03 U * Y ^ 3 +
      pU φ k5Params.cb_h U ^ 3 * (W ^ 2 * pUW φ k5Params.k3W U W) := by
    have hmul : U * W ^ 2 * pU φ k5Params.cb_h U ^ 3 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
        pU φ k5Params.cb_h U ^ 3 * (U * W ^ 2 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U)) := by ring
    rw [hmul, h3, hWa]; dsimp only [Y]; ring
  rw [hstep, hWb]; dsimp only [Z]; ring

end CoverEqRest

section RegIdProof
lemma nine_U_G_AC_eq :
    9 * U_C * G_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C =
      pairC P_G_pair := by
  have hDX : DX2_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K) = ιC_K5 DX2_K := by
    have h := congrArg ιC_K5 (DX2_of_L (L := K5))
    simpa only [DX2_of, u3_of, SL, QL, xL, ιL, Algebra.algebraMap_self, RingHom.id_apply,
      map_add, map_sub, map_mul, map_pow, map_ofNat] using h
  have hDY : DY2_of (ιC_K5 T_K) (ιC_K5 y_K) = ιC_K5 DY2_K := by
    have h := congrArg ιC_K5 (DY2_of_L (L := K5))
    simpa only [DY2_of, v3_of, TL, yL, ιL, Algebra.algebraMap_self, RingHom.id_apply,
      map_add, map_sub, map_mul, map_pow, map_ofNat] using h
  have h9 : (9 : A_C) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  rw [G_of, hDX, hDY, u_of, v_of, V_C, pairC, P_G_pair, evalAC]
  simp only [PairAlg.map, map_sub, map_mul, map_one, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  change 9 * U_C * ((U_C - 1) / 9 * ιC_K5 DX2_K + (W_C / U_C - 1) / 9 * ιC_K5 DY2_K) =
    (ιC_K5 DX2_K * U_C * (U_C - 1) - ιC_K5 DY2_K * U_C) + ιC_K5 DY2_K * W_C
  have h1 : (9 : A_C) * ((U_C - 1) / 9) = U_C - 1 := mul_div_cancel₀ _ h9
  have h2 : (9 : A_C) * ((W_C / U_C - 1) / 9) = W_C / U_C - 1 := mul_div_cancel₀ _ h9
  have h3 : U_C * (W_C / U_C - 1) = W_C - U_C := by
    rw [mul_sub, mul_div_cancel₀ _ U_C_ne_zero, mul_one]
  linear_combination U_C * ιC_K5 DX2_K * h1 + U_C * ιC_K5 DY2_K * h2 + ιC_K5 DY2_K * h3

lemma pnm_P_G_eval_one {L : Type*} [Field L] [Algebra K5 L] :
    ((k5Params.pnm P_G_pair).map (algebraMap K5 L)).eval 1 =
      (algebraMap K5 L DY2_K) ^ 2 * (k5Params.nm_WU.map (algebraMap K5 L)).eval 1 := by
  simp only [CoverParams.pnm, P_G_pair, CoverParams.nm_WU, PairAlg.nm,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_one,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_one]
  ring

lemma G_of_AC_ne_zero :
    G_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C ≠ 0 := by
  have hpnm_ne : k5Params.pnm P_G_pair ≠ 0 := by
    intro h0
    have h1 := pnm_P_G_eval_one (L := K5)
    rw [h0, Polynomial.map_zero, eval_zero] at h1
    exact mul_ne_zero (pow_ne_zero 2 DY2_K_ne_zero) (nm_WU_eval_one_ne (L := K5)) h1.symm
  have h9UG : 9 * U_C * G_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C ≠ 0 := by
    rw [nine_U_G_AC_eq]; exact pairC_ne_zero_of_pnm hpnm_ne
  exact right_ne_zero_of_mul h9UG

lemma F5_of_AC : F5_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) = 0 := by
  have h := congrArg ιC_K5 (F5_of_L (L := K5))
  simpa only [F5_of, H0_of, SL, QL, TL, xL, yL, ιL, Algebra.algebraMap_self, RingHom.id_apply,
    map_zero, map_add, map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat] using h

-- Pure-ring `cB1_of` complement for `v_of V = 0` regularity.
lemma u_cA1_add_v_cB1 {F : Type*} [Field F] [CharZero F] (S Q T a b U V : F) :
    u_of U * cA1_of S Q T a b U V + v_of V * cB1_of S Q T a b U V =
      H0_of S Q T * E_fn 1 S Q T a b U V -
      (dH0_fn 0 S Q T * a + dH0_fn 1 S Q T * b + dH0_fn 2 S Q T) * E_fn 0 S Q T a b U V := by
  simp only [u_of, v_of, cA1_of, cB1_of, dA1_fn, dB1_dT, A1_of, B1_of, H0_of, dH0_fn, E_fn, H_cub]
  ring

/-- Regularized `P18_of` at `U = 1` (`qX = dot_ab CX_of / G^2`). -/
lemma P18_eq_regX {F : Type*} [Field F] [CharZero F] (S Q T x y a b U V : F)
    (hF : F5_of S Q T x y = 0) (hE0 : E_fn 0 S Q T a b U V = 0)
    (hE1 : E_fn 1 S Q T a b U V = 0) (hU : U ≠ 0) (hV : V ≠ 0)
    (hu : u_of U ≠ 0) (hG : G_of S Q T x y U V ≠ 0) :
    P18_of S Q T x y a b U V = P18_regX_of S Q T x y a b U V := by
  have hCX := (G_sq_cancellation S Q T x y a b U V hF hE0 hE1 hU hV).2
  have hqX : dot_ab (QX_num S Q T x y U V) a b / u_of U =
      dot_ab (CX_of S Q T x y U V) a b / G_of S Q T x y U V ^ 2 := by
    rw [div_eq_div_iff hu (pow_ne_zero 2 hG)]
    linear_combination -hCX
  simp only [P18_of, P18_regX_of, hqX]

lemma P18_eq_regY {F : Type*} [Field F] [CharZero F] (S Q T x y a b U V : F)
    (hF : F5_of S Q T x y = 0) (hE0 : E_fn 0 S Q T a b U V = 0)
    (hE1 : E_fn 1 S Q T a b U V = 0) (hU : U ≠ 0) (hV : V ≠ 0)
    (hu : u_of U ≠ 0) (hv : v_of V ≠ 0) (hG : G_of S Q T x y U V ≠ 0) :
    P18_of S Q T x y a b U V = P18_regY_of S Q T x y a b U V := by
  have hCY := (G_sq_cancellation S Q T x y a b U V hF hE0 hE1 hU hV).1
  have hqY : dot_ab (QY_num S Q T x y U V) a b / v_of V =
      dot_ab (CY_of S Q T x y U V) a b / G_of S Q T x y U V ^ 2 := by
    rw [div_eq_div_iff hv (pow_ne_zero 2 hG)]
    linear_combination -hCY
  have hcA : cA1_of S Q T a b U V / v_of V = -cB1_of S Q T a b U V / u_of U := by
    have h := u_cA1_add_v_cB1 S Q T a b U V
    rw [hE0, hE1, mul_zero, mul_zero, sub_self] at h
    rw [div_eq_div_iff hv hu]
    linear_combination h
  simp only [P18_of, P18_regY_of, hqY, hcA]

lemma pU_ιC_K5 (P : K5[X]) : pU ιC_K5 P U_C = polyC P := by
  simp only [pU, polyC, U_C, ιC_K5, ← Polynomial.eval₂_eq_eval_map]
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, map_mul, map_pow,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X, RingHom.comp_apply]; rfl

lemma pUW_ιC_K5 (x : PairAlg K5[X]) : pUW ιC_K5 x U_C W_C = pairC x := by
  rw [pUW_eq, pU_ιC_K5, pU_ιC_K5, pairC, evalAC]; rfl

lemma E0_AC_zero (a b : A_C) :
    E_fn 0 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) a b U_C V_C = 0 := by
  have h0 := E0_of_cover ιC_K5 U_C W_C U_C_ne_zero
  have hW_eq : W_C ^ 2 + pU ιC_K5 k5Params.bW U_C * W_C + pU ιC_K5 k5Params.cW U_C = 0 := by
    rw [pU_ιC_K5, pU_ιC_K5]; exact W_C_relation
  rw [hW_eq, mul_zero] at h0
  exact (mul_eq_zero.mp h0).resolve_left U_C_ne_zero

lemma E1_AC_zero (z : A_C) :
    E_fn 1 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)
      (z / W_C) (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h))
      U_C V_C = 0 := by
  have hW : W_C ^ 2 + pU ιC_K5 k5Params.bW U_C * W_C + pU ιC_K5 k5Params.cW U_C = 0 := by
    rw [pU_ιC_K5, pU_ιC_K5]; exact W_C_relation
  have h1 := E1_of_cover ιC_K5 (z / W_C)
    (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h))
    U_C W_C U_C_ne_zero hW
  rw [pU_ιC_K5, pU_ιC_K5, pUW_ιC_K5] at h1
  have hcb : polyC k5Params.cb_h ≠ 0 := polyC_ne_zero cb_h_K5_ne_zero
  have hrhs : polyC k5Params.ca_h * (W_C * (z / W_C)) +
      polyC k5Params.cb_h * (W_C * (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) /
        (W_C * polyC k5Params.cb_h))) + pairC k5Params.c0W = 0 := by
    field_simp [W_C_ne_zero, hcb]; ring
  rw [hrhs] at h1
  exact (mul_eq_zero.mp h1).resolve_left U_C_ne_zero

lemma P18_z_AC_eq_regX (z : A_C) :
    P18_z_AC z = P18_regX_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K)
      (z / W_C) (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h))
      U_C V_C :=
  P18_eq_regX _ _ _ _ _ _ _ U_C V_C F5_of_AC (E0_AC_zero _ _) (E1_AC_zero z)
    U_C_ne_zero V_C_ne_zero u_of_U_C_ne_zero G_of_AC_ne_zero

lemma P18_z_AC_eq_regY (z : A_C) :
    P18_z_AC z = P18_regY_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K)
      (z / W_C) (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h))
      U_C V_C :=
  P18_eq_regY _ _ _ _ _ _ _ U_C V_C F5_of_AC (E0_AC_zero _ _) (E1_AC_zero z)
    U_C_ne_zero V_C_ne_zero u_of_U_C_ne_zero v_of_V_C_ne_zero G_of_AC_ne_zero


/-- Exact algebraic equality of `eta_AC` with its mirror `a`-elimination form (no `cb_h` denominator). -/
lemma eta_AC_eq_a_elim :
    eta_AC = eta_AC_num_w /
      (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
        polyC k5Params.Q5_z ^ 3 * pairC k5Params.res_w) := by
  dsimp only [eta_AC, eta_AC_num, eta_AC_num_w]
  set p := interp4 P18_z_AC with hp_def
  set q := interp4 P18_w_AC with hq_def
  set P1z := remDeg4_P1 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0) p.1 p.2.1 p.2.2.1 p.2.2.2.1
  set P0z := remDeg4_P0 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0) p.1 p.2.1 p.2.2.1 p.2.2.2.2
  set P1w := remDeg4_P1 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0) q.1 q.2.1 q.2.2.1 q.2.2.2.1
  set P0w := remDeg4_P0 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0) q.1 q.2.1 q.2.2.1 q.2.2.2.2
  set d1w := remDeg3_d1 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0)
    (pairC k5Params.e3_3) (pairC k5Params.e3_2) (pairC k5Params.e3_1)
  set d0w := remDeg3_d0 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0)
    (pairC k5Params.e3_3) (pairC k5Params.e3_2) (pairC k5Params.e3_0)
  have hcb : polyC k5Params.cb_h ≠ 0 := polyC_ne_zero cb_h_K5_ne_zero
  have hca : polyC k5Params.ca_h ≠ 0 := polyC_ne_zero ca_h_K5_ne_zero
  have hQ5 : polyC k5Params.Q5_z ≠ 0 := polyC_ne_zero Q5_K5_ne_zero
  have hres_z : pairC k5Params.res_z ≠ 0 := pairC_ne_zero_of_pnm nm_z_K5_ne_zero
  have hdisc_E2z : pairC k5Params.disc_E2z ≠ 0 := pairC_ne_zero_of_pnm nm_disc_E2z_K5_ne_zero
  have pairC_pmul (x y : PairAlg K5[X]) : pairC (k5Params.pmul x y) = pairC x * pairC y := by
    simp only [pairC, CoverParams.pmul, PairAlg.map_mul, evalAC_mul]
  have pairC_add (x y : PairAlg K5[X]) : pairC (PairAlg.add x y) = pairC x + pairC y := by
    simp only [pairC, PairAlg.map_add, evalAC_add]
  have pairC_sub (x y : PairAlg K5[X]) : pairC (PairAlg.sub x y) = pairC x - pairC y := by
    simp only [pairC, PairAlg.map_sub, evalAC_sub]
  have pairC_smul (s : K5[X]) (x : PairAlg K5[X]) : pairC (PairAlg.smul s x) = polyC s * pairC x := by
    simp only [pairC, polyC, PairAlg.map_smul, evalAC_smul]
  have pairC_ofScalar (s : K5[X]) : pairC (PairAlg.ofScalar s) = polyC s := by
    simp only [pairC, polyC, PairAlg.map_ofScalar, evalAC_ofScalar]
  have pairC_W : pairC PairAlg.W = W_C := by simp [pairC, PairAlg.map_W, evalAC_W]
  have polyC_add (P Q : K5[X]) : polyC (P + Q) = polyC P + polyC Q := by simp only [polyC, map_add]
  have polyC_sub (P Q : K5[X]) : polyC (P - Q) = polyC P - polyC Q := by simp only [polyC, map_sub]
  have polyC_neg (P : K5[X]) : polyC (-P) = -polyC P := by simp only [polyC, map_neg]
  have polyC_mul (P Q : K5[X]) : polyC (P * Q) = polyC P * polyC Q := by simp only [polyC, map_mul]
  have polyC_pow (P : K5[X]) (n : ℕ) : polyC (P ^ n) = polyC P ^ n := by simp only [polyC, map_pow]
  have polyC_ofNat (n : ℕ) [n.AtLeastTwo] : polyC (OfNat.ofNat n) = OfNat.ofNat n := by
    simp only [polyC, map_ofNat]
  -- Step 1: `ca_h^6 * res_z = cb_h^6 * res_w` via `syl5_elim_symm_aux`!
  have hres_symm : polyC k5Params.ca_h ^ 6 * pairC k5Params.res_z =
      polyC k5Params.cb_h ^ 6 * pairC k5Params.res_w := by
    apply mul_left_cancel₀ (pow_ne_zero 6 hcb)
    have haux := syl5_elim_symm_aux
      (polyC k5Params.ca_h) (polyC k5Params.cb_h) (pairC k5Params.c0W)
      (polyC k5Params.q20) (polyC k5Params.q11) (polyC k5Params.q02) (W_C * pairC k5Params.k2W)
      (polyC k5Params.c30) (polyC k5Params.c21) (polyC k5Params.c12) (polyC k5Params.c03)
      (W_C * W_C * pairC k5Params.k3W)
    have hpairC_evalAt (x : PairAlg K5[X]) :
        pairC x = PairAlg.evalAt W_C (PairAlg.map (ιC_rat.comp toRat) x) := rfl
    have hpair_syl5 (a2 a1 a0 b3 b2 b1 b0 : PairAlg K5[X]) :
        pairC (syl5Pair k5Params.bW k5Params.cW a2 a1 a0 b3 b2 b1 b0) =
          syl5 (pairC a2) (pairC a1) (pairC a0) (pairC b3) (pairC b2) (pairC b1) (pairC b0) := by
      simp only [hpairC_evalAt, map_syl5Pair]
      exact evalAt_syl5Pair _ _ _ _ _ _ _ _ _ W_C W_C_relation
    have hresz_eq : pairC k5Params.res_z = syl5 (pairC k5Params.d2_2) (pairC k5Params.d2_1)
        (pairC k5Params.d2_0) (pairC k5Params.d3_3) (pairC k5Params.d3_2)
        (pairC k5Params.d3_1) (pairC k5Params.d3_0) := hpair_syl5 ..
    have hresw_eq : pairC k5Params.res_w = syl5 (pairC k5Params.e2_2) (pairC k5Params.e2_1)
        (pairC k5Params.e2_0) (pairC k5Params.e3_3) (pairC k5Params.e3_2)
        (pairC k5Params.e3_1) (pairC k5Params.e3_0) := hpair_syl5 ..
    rw [hresz_eq, hresw_eq]
    have hQ5_eq : pairC k5Params.d2_2 =
        polyC k5Params.q20 * polyC k5Params.cb_h ^ 2 -
        polyC k5Params.q11 * polyC k5Params.ca_h * polyC k5Params.cb_h +
        polyC k5Params.q02 * polyC k5Params.ca_h ^ 2 := by
      simp only [CoverParams.d2_2, CoverParams.Q5_z, pairC_ofScalar, polyC_add, polyC_sub,
        polyC_mul, polyC_pow]
    have he22_eq : pairC k5Params.e2_2 = pairC k5Params.d2_2 := rfl
    have hQ7_eq : pairC k5Params.d3_3 =
        polyC k5Params.c30 * polyC k5Params.cb_h ^ 3 -
        polyC k5Params.c21 * polyC k5Params.ca_h * polyC k5Params.cb_h ^ 2 +
        polyC k5Params.c12 * polyC k5Params.ca_h ^ 2 * polyC k5Params.cb_h -
        polyC k5Params.c03 * polyC k5Params.ca_h ^ 3 := by
      simp only [CoverParams.d3_3, CoverParams.Q7_z, pairC_ofScalar, polyC_add, polyC_sub,
        polyC_mul, polyC_pow]
    have hd21 : pairC k5Params.d2_1 = (-polyC k5Params.q11 * polyC k5Params.cb_h +
        2 * polyC k5Params.q02 * polyC k5Params.ca_h) * pairC k5Params.c0W := by
      simp only [CoverParams.d2_1, pairC_smul, polyC_add, polyC_neg, polyC_mul, polyC_ofNat]
    have hd20 : pairC k5Params.d2_0 = polyC k5Params.q02 * pairC k5Params.c0W ^ 2 +
        polyC k5Params.cb_h ^ 2 * (W_C * pairC k5Params.k2W) := by
      simp only [CoverParams.d2_0, pairC_add, pairC_smul, pairC_pmul, pairC_W, polyC_pow]; ring
    have hd32 : pairC k5Params.d3_2 = (-polyC k5Params.c21 * polyC k5Params.cb_h ^ 2 +
        2 * polyC k5Params.c12 * polyC k5Params.ca_h * polyC k5Params.cb_h -
        3 * polyC k5Params.c03 * polyC k5Params.ca_h ^ 2) * pairC k5Params.c0W := by
      simp only [CoverParams.d3_2, pairC_smul, polyC_add, polyC_sub, polyC_neg, polyC_mul,
        polyC_pow, polyC_ofNat]
    have hd31 : pairC k5Params.d3_1 = (polyC k5Params.c12 * polyC k5Params.cb_h -
        3 * polyC k5Params.c03 * polyC k5Params.ca_h) * pairC k5Params.c0W ^ 2 := by
      simp only [CoverParams.d3_1, pairC_smul, pairC_pmul, polyC_sub, polyC_mul, polyC_ofNat]; ring
    have hd30 : pairC k5Params.d3_0 = -polyC k5Params.c03 * pairC k5Params.c0W ^ 3 +
        polyC k5Params.cb_h ^ 3 * (W_C * W_C * pairC k5Params.k3W) := by
      simp only [CoverParams.d3_0, pairC_add, pairC_smul, pairC_pmul, pairC_W, polyC_neg, polyC_pow]; ring
    have he21 : pairC k5Params.e2_1 = (-polyC k5Params.q11 * polyC k5Params.ca_h +
        2 * polyC k5Params.q20 * polyC k5Params.cb_h) * pairC k5Params.c0W := by
      simp only [CoverParams.e2_1, pairC_smul, polyC_add, polyC_neg, polyC_mul, polyC_ofNat]
    have he20 : pairC k5Params.e2_0 = polyC k5Params.q20 * pairC k5Params.c0W ^ 2 +
        polyC k5Params.ca_h ^ 2 * (W_C * pairC k5Params.k2W) := by
      simp only [CoverParams.e2_0, pairC_add, pairC_smul, pairC_pmul, pairC_W, polyC_pow]; ring
    have he33 : pairC k5Params.e3_3 = -polyC k5Params.c30 * polyC k5Params.cb_h ^ 3 +
        polyC k5Params.c21 * polyC k5Params.ca_h * polyC k5Params.cb_h ^ 2 -
        polyC k5Params.c12 * polyC k5Params.ca_h ^ 2 * polyC k5Params.cb_h +
        polyC k5Params.c03 * polyC k5Params.ca_h ^ 3 := by
      simp only [CoverParams.e3_3, pairC_ofScalar, polyC_add, polyC_sub, polyC_neg,
        polyC_mul, polyC_pow]
    have he32 : pairC k5Params.e3_2 = (-3 * polyC k5Params.c30 * polyC k5Params.cb_h ^ 2 +
        2 * polyC k5Params.c21 * polyC k5Params.ca_h * polyC k5Params.cb_h -
        polyC k5Params.c12 * polyC k5Params.ca_h ^ 2) * pairC k5Params.c0W := by
      simp only [CoverParams.e3_2, pairC_smul, polyC_add, polyC_sub, polyC_neg, polyC_mul,
        polyC_pow, polyC_ofNat]
    have he31 : pairC k5Params.e3_1 = (-3 * polyC k5Params.c30 * polyC k5Params.cb_h +
        polyC k5Params.c21 * polyC k5Params.ca_h) * pairC k5Params.c0W ^ 2 := by
      simp only [CoverParams.e3_1, pairC_smul, pairC_pmul, polyC_add, polyC_neg,
        polyC_mul, polyC_ofNat]; ring
    have he30 : pairC k5Params.e3_0 = -polyC k5Params.c30 * pairC k5Params.c0W ^ 3 +
        polyC k5Params.ca_h ^ 3 * (W_C * W_C * pairC k5Params.k3W) := by
      simp only [CoverParams.e3_0, pairC_add, pairC_smul, pairC_pmul, pairC_W, polyC_neg, polyC_pow]; ring
    rw [he22_eq, hQ5_eq, hQ7_eq, hd21, hd20, hd32, hd31, hd30, he21, he20, he33, he32, he31, he30]
    exact haux
  have hres_w : pairC k5Params.res_w ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hres_symm
    exact mul_ne_zero (pow_ne_zero 6 hca) hres_z hres_symm
  -- Step 2: `-(P1z * d0z - P0z * d1z) * ca_h^2 = (P1w * d0w - P0w * d1w) * cb_h^2` in SplittingField!
  have hcomb_symm :
      -(P1z * pairC k5Params.d0_z - P0z * pairC k5Params.d1_z) * polyC k5Params.ca_h ^ 2 =
        (P1w * d0w - P0w * d1w) * polyC k5Params.cb_h ^ 2 := by
    let Qz : A_C[X] := C (pairC k5Params.d2_2) * X ^ 2 + C (pairC k5Params.d2_1) * X +
      C (pairC k5Params.d2_0)
    let j : A_C →+* Qz.SplittingField := algebraMap A_C Qz.SplittingField
    have : CharZero Qz.SplittingField := charZero_of_injective_ringHom j.injective
    apply j.injective
    have hQz_deg : Qz.natDegree = 2 := by
      have h2 : pairC k5Params.d2_2 ≠ 0 := by
        simpa [CoverParams.d2_2, pairC_ofScalar] using hQ5
      have hlt : (C (pairC k5Params.d2_1) * X + C (pairC k5Params.d2_0)).natDegree <
          (C (pairC k5Params.d2_2) * X ^ 2).natDegree := by
        rw [Polynomial.natDegree_C_mul_X_pow 2 (pairC k5Params.d2_2) h2]
        refine (natDegree_add_le _ _).trans_lt (max_lt ?_ (by simp))
        exact (natDegree_C_mul_le _ _).trans_lt (by simp)
      rw [show Qz = C (pairC k5Params.d2_2) * X ^ 2 +
          (C (pairC k5Params.d2_1) * X + C (pairC k5Params.d2_0)) by simp [Qz, add_assoc],
        natDegree_add_eq_left_of_natDegree_lt hlt,
        Polynomial.natDegree_C_mul_X_pow 2 (pairC k5Params.d2_2) h2]
    have hQz_lc : Qz.leadingCoeff = pairC k5Params.d2_2 := by
      rw [Polynomial.leadingCoeff, hQz_deg]
      simp [Qz, Polynomial.coeff_X_pow]
    have hsplit : (Qz.map j).Splits := Polynomial.SplittingField.splits Qz
    have hcard : (Qz.map j).roots.card = 2 := by
      rw [← Polynomial.Splits.natDegree_eq_card_roots hsplit, Polynomial.natDegree_map, hQz_deg]
    obtain ⟨z1, z2, hroots⟩ := Multiset.card_eq_two.mp hcard
    have hfac : Qz.map j = C (j (pairC k5Params.d2_2)) * (X - C z1) * (X - C z2) := by
      have hprod := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
        (show (Qz.map j).roots.card = (Qz.map j).natDegree by rw [hcard, Polynomial.natDegree_map, hQz_deg])
      rw [hroots, Polynomial.leadingCoeff_map, hQz_lc] at hprod
      simpa [mul_assoc] using hprod.symm
    have hq1_eq : j (pairC k5Params.d2_1) = -j (pairC k5Params.d2_2) * (z1 + z2) := by
      have h1 := congrArg (fun f : Qz.SplittingField[X] => f.coeff 1) hfac
      have hexp : C (j (pairC k5Params.d2_2)) * (X - C z1) * (X - C z2) =
          C (j (pairC k5Params.d2_2) * z1 * z2) +
          C (-j (pairC k5Params.d2_2) * (z1 + z2)) * X +
          C (j (pairC k5Params.d2_2)) * X ^ 2 := by
        simp only [map_add, map_mul, map_neg]; ring
      rw [hexp] at h1
      simp only [Qz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        Polynomial.map_pow, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_X_pow] at h1
      simpa using h1
    have hq0_eq : j (pairC k5Params.d2_0) = j (pairC k5Params.d2_2) * z1 * z2 := by
      have h0 := congrArg (fun f : Qz.SplittingField[X] => f.coeff 0) hfac
      have hexp : C (j (pairC k5Params.d2_2)) * (X - C z1) * (X - C z2) =
          C (j (pairC k5Params.d2_2) * z1 * z2) +
          C (-j (pairC k5Params.d2_2) * (z1 + z2)) * X +
          C (j (pairC k5Params.d2_2)) * X ^ 2 := by
        simp only [map_add, map_mul, map_neg]; ring
      rw [hexp] at h0
      simp only [Qz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        Polynomial.map_pow, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_X_pow] at h0
      simpa using h0
    have hz12_ne : z1 - z2 ≠ 0 := by
      intro h0
      have hd_eq : j (pairC k5Params.disc_E2z) =
          j (pairC k5Params.d2_2) ^ 2 * (z1 - z2) ^ 2 := by
        have hd : pairC k5Params.disc_E2z = pairC k5Params.d2_1 ^ 2 -
            4 * pairC k5Params.d2_2 * pairC k5Params.d2_0 := by
          simp only [CoverParams.disc_E2z, pairC_sub, pairC_smul, pairC_pmul, polyC_ofNat]; ring
        rw [hd, map_sub, map_pow, map_mul, map_mul, map_ofNat, hq1_eq, hq0_eq]; ring
      rw [h0, zero_pow (by omega), mul_zero] at hd_eq
      exact hdisc_E2z (j.injective (by simpa using hd_eq))
    let w1 : Qz.SplittingField := -(j (polyC k5Params.ca_h) * z1 + j (pairC k5Params.c0W)) / j (polyC k5Params.cb_h)
    let w2 : Qz.SplittingField := -(j (polyC k5Params.ca_h) * z2 + j (pairC k5Params.c0W)) / j (polyC k5Params.cb_h)
    have hcbE : j (polyC k5Params.cb_h) ≠ 0 := (map_ne_zero_iff j j.injective).mpr hcb
    have hcaE : j (polyC k5Params.ca_h) ≠ 0 := (map_ne_zero_iff j j.injective).mpr hca
    have hw12 : w1 - w2 = -(j (polyC k5Params.ca_h) / j (polyC k5Params.cb_h)) * (z1 - z2) := by
      dsimp only [w1, w2]; field_simp [hcbE]; ring
    have he21_eq : j (pairC k5Params.e2_1) = -j (pairC k5Params.e2_2) * (w1 + w2) := by
      have hrel : polyC k5Params.cb_h ^ 2 * pairC k5Params.e2_1 =
          2 * pairC k5Params.d2_2 * (-polyC k5Params.cb_h) * (-pairC k5Params.c0W) +
          polyC k5Params.ca_h * pairC k5Params.d2_1 * (-polyC k5Params.cb_h) := by
        simp only [CoverParams.e2_1, CoverParams.d2_2, CoverParams.d2_1, CoverParams.Q5_z,
          pairC_smul, pairC_ofScalar, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow,
          polyC_ofNat]; ring
      have hrelE := congrArg j hrel
      simp only [map_add, map_mul, map_pow, map_neg, map_ofNat] at hrelE
      rw [hq1_eq] at hrelE
      have he22 : j (pairC k5Params.e2_2) = j (pairC k5Params.d2_2) := rfl
      rw [he22]
      dsimp only [w1, w2]
      apply mul_left_cancel₀ (pow_ne_zero 2 hcbE)
      field_simp [hcbE] at hrelE ⊢
      linear_combination hrelE
    have he20_eq : j (pairC k5Params.e2_0) = j (pairC k5Params.e2_2) * w1 * w2 := by
      have hrel : polyC k5Params.cb_h ^ 2 * pairC k5Params.e2_0 =
          pairC k5Params.d2_2 * (-pairC k5Params.c0W) ^ 2 +
          polyC k5Params.ca_h * pairC k5Params.d2_1 * (-pairC k5Params.c0W) +
          polyC k5Params.ca_h ^ 2 * pairC k5Params.d2_0 := by
        simp only [CoverParams.e2_0, CoverParams.d2_2, CoverParams.d2_1, CoverParams.d2_0,
          CoverParams.Q5_z, pairC_add, pairC_smul, pairC_pmul, pairC_ofScalar, pairC_W,
          polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_ofNat]; ring
      have hrelE := congrArg j hrel
      simp only [map_add, map_mul, map_pow, map_neg] at hrelE
      rw [hq1_eq, hq0_eq] at hrelE
      have he22 : j (pairC k5Params.e2_2) = j (pairC k5Params.d2_2) := rfl
      rw [he22]
      dsimp only [w1, w2]
      apply mul_left_cancel₀ (pow_ne_zero 2 hcbE)
      field_simp [hcbE] at hrelE ⊢
      linear_combination hrelE
    have hE3_rel (z : Qz.SplittingField) :
        let w := -(j (polyC k5Params.ca_h) * z + j (pairC k5Params.c0W)) / j (polyC k5Params.cb_h)
        j (polyC k5Params.cb_h) ^ 3 *
          (j (pairC k5Params.e3_3) * w ^ 3 + j (pairC k5Params.e3_2) * w ^ 2 +
           j (pairC k5Params.e3_1) * w + j (pairC k5Params.e3_0)) =
        j (polyC k5Params.ca_h) ^ 3 *
          (j (pairC k5Params.d3_3) * z ^ 3 + j (pairC k5Params.d3_2) * z ^ 2 +
           j (pairC k5Params.d3_1) * z + j (pairC k5Params.d3_0)) := by
      intro w
      have h33 : polyC k5Params.cb_h ^ 3 * pairC k5Params.e3_3 =
          pairC k5Params.d3_3 * (-polyC k5Params.cb_h) ^ 3 := by
        simp only [CoverParams.e3_3, CoverParams.d3_3, CoverParams.Q7_z, pairC_ofScalar,
          polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow]; ring
      have h32 : polyC k5Params.cb_h ^ 3 * pairC k5Params.e3_2 =
          3 * pairC k5Params.d3_3 * (-polyC k5Params.cb_h) ^ 2 * (-pairC k5Params.c0W) +
          polyC k5Params.ca_h * pairC k5Params.d3_2 * (-polyC k5Params.cb_h) ^ 2 := by
        simp only [CoverParams.e3_2, CoverParams.d3_3, CoverParams.d3_2, CoverParams.Q7_z,
          pairC_smul, pairC_ofScalar, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow,
          polyC_ofNat]; ring
      have h31 : polyC k5Params.cb_h ^ 3 * pairC k5Params.e3_1 =
          3 * pairC k5Params.d3_3 * (-polyC k5Params.cb_h) * (-pairC k5Params.c0W) ^ 2 +
          2 * (polyC k5Params.ca_h * pairC k5Params.d3_2) * (-polyC k5Params.cb_h) * (-pairC k5Params.c0W) +
          polyC k5Params.ca_h ^ 2 * pairC k5Params.d3_1 * (-polyC k5Params.cb_h) := by
        simp only [CoverParams.e3_1, CoverParams.d3_3, CoverParams.d3_2, CoverParams.d3_1,
          CoverParams.Q7_z, pairC_smul, pairC_pmul, pairC_ofScalar, polyC_add, polyC_sub,
          polyC_neg, polyC_mul, polyC_pow, polyC_ofNat]; ring
      have h30 : polyC k5Params.cb_h ^ 3 * pairC k5Params.e3_0 =
          pairC k5Params.d3_3 * (-pairC k5Params.c0W) ^ 3 +
          polyC k5Params.ca_h * pairC k5Params.d3_2 * (-pairC k5Params.c0W) ^ 2 +
          polyC k5Params.ca_h ^ 2 * pairC k5Params.d3_1 * (-pairC k5Params.c0W) +
          polyC k5Params.ca_h ^ 3 * pairC k5Params.d3_0 := by
        simp only [CoverParams.e3_0, CoverParams.d3_3, CoverParams.d3_2, CoverParams.d3_1,
          CoverParams.d3_0, CoverParams.Q7_z, pairC_add, pairC_smul, pairC_pmul, pairC_ofScalar,
          pairC_W, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_ofNat]; ring
      have j33 := congrArg j h33; have j32 := congrArg j h32
      have j31 := congrArg j h31; have j30 := congrArg j h30
      simp only [map_add, map_mul, map_pow, map_neg, map_ofNat] at j33 j32 j31 j30
      dsimp only [w]
      have hbw : j (polyC k5Params.cb_h) * (-(j (polyC k5Params.ca_h) * z + j (pairC k5Params.c0W)) /
          j (polyC k5Params.cb_h)) = -(j (polyC k5Params.ca_h) * z + j (pairC k5Params.c0W)) :=
        mul_div_cancel₀ _ hcbE
      linear_combination w ^ 3 * j33 + w ^ 2 * j32 + w * j31 + j30 +
        (j (pairC k5Params.d3_3) * ((-j (polyC k5Params.cb_h) * w - j (pairC k5Params.c0W)) ^ 2 +
          (-j (polyC k5Params.cb_h) * w - j (pairC k5Params.c0W)) * (j (polyC k5Params.ca_h) * z) +
          (j (polyC k5Params.ca_h) * z) ^ 2) +
         j (polyC k5Params.ca_h) * j (pairC k5Params.d3_2) *
          ((-j (polyC k5Params.cb_h) * w - j (pairC k5Params.c0W)) + j (polyC k5Params.ca_h) * z) +
         j (polyC k5Params.ca_h) ^ 2 * j (pairC k5Params.d3_1)) * (-hbw)
    -- Evaluate degree-4 polynomials `P18_z` and `P18_w` in `E` and match at `(z1, w1)` and `(z2, w2)`!
    let P18_z_E : Qz.SplittingField → Qz.SplittingField := fun z =>
      P18_of (j (ιC_K5 S_K)) (j (ιC_K5 Q_K)) (j (ιC_K5 T_K)) (j (ιC_K5 x_K)) (j (ιC_K5 y_K))
        (z / j W_C) (-(j (polyC k5Params.ca_h) * z + j (pairC k5Params.c0W)) /
          (j W_C * j (polyC k5Params.cb_h))) (j U_C) (j V_C)
    let P18_w_E : Qz.SplittingField → Qz.SplittingField := fun w =>
      P18_of (j (ιC_K5 S_K)) (j (ιC_K5 Q_K)) (j (ιC_K5 T_K)) (j (ιC_K5 x_K)) (j (ιC_K5 y_K))
        (-(j (polyC k5Params.cb_h) * w + j (pairC k5Params.c0W)) /
          (j W_C * j (polyC k5Params.ca_h))) (w / j W_C) (j U_C) (j V_C)
    have hmap_P18 (S Q T x y a b U V : A_C) :
        j (P18_of S Q T x y a b U V) = P18_of (j S) (j Q) (j T) (j x) (j y) (j a) (j b) (j U) (j V) := by
      simp only [P18_of, A_0U, A_0V, A_Y, A_X, numM, q1_a2, q1_a1, q1_a0, q2_b2, q2_b1, q2_b0,
        dH_dS, dH_dQ, H0_of, A1_of, B1_of, u_of, v_of, cA1_of, dA1_fn, dH0_fn, EB_of, W2_of,
        DX2_of, DY2_of, u3_of, v3_of, dF5_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn,
        dot_ab, QY_num, QX_num, Omega_F, dDX2_F, dDY2_F, F_contract, om_fn, dDX2_fn, dDY2_fn,
        map_add, map_sub, map_mul, map_div₀, map_pow, map_neg, map_ofNat, map_one, map_zero]
    have hp_E : (j p.1, j p.2.1, j p.2.2.1, j p.2.2.2.1, j p.2.2.2.2) = interp4 P18_z_E := by
      simpa [hp_def] using map_interp4 j P18_z_AC P18_z_E (fun z => by
        simp only [P18_z_AC, P18_z_E, hmap_P18, map_div₀, map_neg, map_add, map_mul])
    have hq_E : (j q.1, j q.2.1, j q.2.2.1, j q.2.2.2.1, j q.2.2.2.2) = interp4 P18_w_E := by
      simpa [hq_def] using map_interp4 j P18_w_AC P18_w_E (fun w => by
        simp only [P18_w_AC, P18_w_E, hmap_P18, map_div₀, map_neg, map_add, map_mul])
    have hP18z_deg4 : IsPolyDeg 4 P18_z_E := by
      refine (P18_of_isPolyDeg4 (j (ιC_K5 S_K)) (j (ιC_K5 Q_K)) (j (ιC_K5 T_K))
        (j (ιC_K5 x_K)) (j (ιC_K5 y_K)) (j U_C) (j V_C)
        (j W_C)⁻¹ 0 (-j (polyC k5Params.ca_h) / (j W_C * j (polyC k5Params.cb_h)))
        (-j (pairC k5Params.c0W) / (j W_C * j (polyC k5Params.cb_h)))).congr (fun z => ?_)
      dsimp only [P18_z_E]; congr 1 <;> ring
    have hP18w_deg4 : IsPolyDeg 4 P18_w_E := by
      refine (P18_of_isPolyDeg4 (j (ιC_K5 S_K)) (j (ιC_K5 Q_K)) (j (ιC_K5 T_K))
        (j (ιC_K5 x_K)) (j (ιC_K5 y_K)) (j U_C) (j V_C)
        (-j (polyC k5Params.cb_h) / (j W_C * j (polyC k5Params.ca_h)))
        (-j (pairC k5Params.c0W) / (j W_C * j (polyC k5Params.ca_h)))
        (j W_C)⁻¹ 0).congr (fun w => ?_)
      dsimp only [P18_w_E]; congr 1 <;> ring
    have hPz_eval : ∀ z : Qz.SplittingField, P18_z_E z =
        j p.1 * z ^ 4 + j p.2.1 * z ^ 3 + j p.2.2.1 * z ^ 2 + j p.2.2.2.1 * z + j p.2.2.2.2 := by
      have h := hP18z_deg4.eq_deg4; rw [← hp_E] at h; exact h
    have hPw_eval : ∀ w : Qz.SplittingField, P18_w_E w =
        j q.1 * w ^ 4 + j q.2.1 * w ^ 3 + j q.2.2.1 * w ^ 2 + j q.2.2.2.1 * w + j q.2.2.2.2 := by
      have h := hP18w_deg4.eq_deg4; rw [← hq_E] at h; exact h
    have hPz_eq_Pw (z : Qz.SplittingField) : P18_w_E (-(j (polyC k5Params.ca_h) * z + j (pairC k5Params.c0W)) /
        j (polyC k5Params.cb_h)) = P18_z_E z := by
      dsimp only [P18_w_E, P18_z_E]
      congr 1
      · have hW_E : j W_C ≠ 0 := (map_ne_zero_iff j j.injective).mpr W_C_ne_zero
        field_simp [hW_E, hcaE, hcbE]; ring
      · ring
    -- Apply `remDeg4_comb_roots` to both `z` and `w`!
    have hd1z_map : j (pairC k5Params.d1_z) = remDeg3_d1 (j (pairC k5Params.d2_2))
        (j (pairC k5Params.d2_1)) (j (pairC k5Params.d2_0))
        (j (pairC k5Params.d3_3)) (j (pairC k5Params.d3_2)) (j (pairC k5Params.d3_1)) := by
      simp [CoverParams.d1_z, remDeg3_d1, pairC_sub, pairC_pmul]
    have hd0z_map : j (pairC k5Params.d0_z) = remDeg3_d0 (j (pairC k5Params.d2_2))
        (j (pairC k5Params.d2_1)) (j (pairC k5Params.d2_0))
        (j (pairC k5Params.d3_3)) (j (pairC k5Params.d3_2)) (j (pairC k5Params.d3_0)) := by
      simp [CoverParams.d0_z, remDeg3_d0, pairC_sub, pairC_pmul]
    have hcz := remDeg4_comb_roots (j (pairC k5Params.d2_2))
      (j (pairC k5Params.d3_3)) (j (pairC k5Params.d3_2)) (j (pairC k5Params.d3_1)) (j (pairC k5Params.d3_0))
      (j p.1) (j p.2.1) (j p.2.2.1) (j p.2.2.2.1) (j p.2.2.2.2) z1 z2
    have hcw := remDeg4_comb_roots (j (pairC k5Params.e2_2))
      (j (pairC k5Params.e3_3)) (j (pairC k5Params.e3_2)) (j (pairC k5Params.e3_1)) (j (pairC k5Params.e3_0))
      (j q.1) (j q.2.1) (j q.2.2.1) (j q.2.2.2.1) (j q.2.2.2.2) w1 w2
    dsimp only at hcz hcw
    rw [← hq1_eq, ← hq0_eq, ← hd1z_map, ← hd0z_map, ← hPz_eval z1, ← hPz_eval z2] at hcz
    rw [← he21_eq, ← he20_eq, ← hPw_eval w1, ← hPw_eval w2] at hcw
    have hP1z_map : remDeg4_P1 (j (pairC k5Params.d2_2)) (j (pairC k5Params.d2_1))
        (j (pairC k5Params.d2_0)) (j p.1) (j p.2.1) (j p.2.2.1) (j p.2.2.2.1) = j P1z := by
      simp [P1z, remDeg4_P1]
    have hP0z_map : remDeg4_P0 (j (pairC k5Params.d2_2)) (j (pairC k5Params.d2_1))
        (j (pairC k5Params.d2_0)) (j p.1) (j p.2.1) (j p.2.2.1) (j p.2.2.2.2) = j P0z := by
      simp [P0z, remDeg4_P0]
    have hP1w_map : remDeg4_P1 (j (pairC k5Params.e2_2)) (j (pairC k5Params.e2_1))
        (j (pairC k5Params.e2_0)) (j q.1) (j q.2.1) (j q.2.2.1) (j q.2.2.2.1) = j P1w := by
      simp [P1w, remDeg4_P1]
    have hP0w_map : remDeg4_P0 (j (pairC k5Params.e2_2)) (j (pairC k5Params.e2_1))
        (j (pairC k5Params.e2_0)) (j q.1) (j q.2.1) (j q.2.2.1) (j q.2.2.2.2) = j P0w := by
      simp [P0w, remDeg4_P0]
    have hd1w_map : remDeg3_d1 (j (pairC k5Params.e2_2)) (j (pairC k5Params.e2_1))
        (j (pairC k5Params.e2_0)) (j (pairC k5Params.e3_3)) (j (pairC k5Params.e3_2))
        (j (pairC k5Params.e3_1)) = j d1w := by
      simp [d1w, remDeg3_d1]
    have hd0w_map : remDeg3_d0 (j (pairC k5Params.e2_2)) (j (pairC k5Params.e2_1))
        (j (pairC k5Params.e2_0)) (j (pairC k5Params.e3_3)) (j (pairC k5Params.e3_2))
        (j (pairC k5Params.e3_0)) = j d0w := by
      simp [d0w, remDeg3_d0]
    rw [hP1z_map, hP0z_map] at hcz
    rw [hP1w_map, hP0w_map, hd1w_map, hd0w_map, hw12, hPz_eq_Pw z1, hPz_eq_Pw z2] at hcw
    have hE3_1 := hE3_rel z1; have hE3_2 := hE3_rel z2
    dsimp only at hE3_1 hE3_2
    change j (polyC k5Params.cb_h) ^ 3 * (j (pairC k5Params.e3_3) * w1 ^ 3 +
      j (pairC k5Params.e3_2) * w1 ^ 2 + j (pairC k5Params.e3_1) * w1 + j (pairC k5Params.e3_0)) = _ at hE3_1
    change j (polyC k5Params.cb_h) ^ 3 * (j (pairC k5Params.e3_3) * w2 ^ 3 +
      j (pairC k5Params.e3_2) * w2 ^ 2 + j (pairC k5Params.e3_1) * w2 + j (pairC k5Params.e3_0)) = _ at hE3_2
    have hmul : j (polyC k5Params.cb_h) ^ 3 *
        ((j P1w * j d0w - j P0w * j d1w) * (-(j (polyC k5Params.ca_h) / j (polyC k5Params.cb_h)) * (z1 - z2))) =
        j (polyC k5Params.ca_h) ^ 3 * ((j P1z * j (pairC k5Params.d0_z) - j P0z * j (pairC k5Params.d1_z)) * (z1 - z2)) := by
      rw [hcw, hcz]
      have he22 : j (pairC k5Params.e2_2) = j (pairC k5Params.d2_2) := rfl
      rw [he22]
      linear_combination j (pairC k5Params.d2_2) ^ 5 * P18_z_E z1 * hE3_2 -
        j (pairC k5Params.d2_2) ^ 5 * P18_z_E z2 * hE3_1
    have hfac_ne : j (polyC k5Params.ca_h) * (z1 - z2) ≠ 0 := mul_ne_zero hcaE hz12_ne
    simp only [map_neg, map_mul, map_sub, map_pow]
    apply mul_right_cancel₀ hfac_ne
    have hcb3 : j (polyC k5Params.cb_h) ^ 3 * (-(j (polyC k5Params.ca_h) / j (polyC k5Params.cb_h))) =
        -j (polyC k5Params.cb_h) ^ 2 * j (polyC k5Params.ca_h) := by
      have hc : j (polyC k5Params.cb_h) * (j (polyC k5Params.ca_h) / j (polyC k5Params.cb_h)) =
          j (polyC k5Params.ca_h) := mul_div_cancel₀ _ hcbE
      linear_combination -j (polyC k5Params.cb_h) ^ 2 * hc
    linear_combination hmul - (j P1w * j d0w - j P0w * j d1w) * (z1 - z2) * hcb3
  -- Step 3: Combine `hcomb_symm` and `hres_symm`!
  have hden_ne : (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q5_z ^ 3 : A_C) ≠ 0 := by
    have h2W : 2 * W_C + polyC k5Params.bW ≠ 0 := by
      intro h0
      have hsq : (2 * W_C + polyC k5Params.bW) ^ 2 = polyC k5Params.disc_E0 := by
        simp only [polyC, CoverParams.disc_E0, map_sub, map_pow, map_mul, map_ofNat]
        linear_combination 4 * W_C_relation
      rw [h0, zero_pow (by omega)] at hsq
      have hdisc_ne : k5Params.disc_E0 ≠ 0 := by
        intro hd0
        have hcop := isCoprime_P34_disc_E0
        rw [hd0, isCoprime_zero_right] at hcop
        have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hcop
        rw [P34_K5_natDegree] at hdeg; omega
      exact polyC_ne_zero hdisc_ne hsq.symm
    have h81 : (81 : A_C) ≠ 0 := by exact_mod_cast (by decide : (81 : ℕ) ≠ 0)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h81
      ((map_ne_zero_iff ιC_K5 ιC_K5.injective).mpr Av0_K5_ne_zero)) h2W) (pow_ne_zero 3 hQ5)
  rw [div_eq_div_iff (mul_ne_zero hden_ne hres_z) (mul_ne_zero hden_ne hres_w)]
  apply mul_left_cancel₀ (pow_ne_zero 2 hca)
  linear_combination
    U_C ^ 3 * W_C * (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q5_z ^ 3) * polyC k5Params.cb_h ^ 4 * pairC k5Params.res_w * hcomb_symm -
    U_C ^ 3 * W_C * (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q5_z ^ 3) * (P1w * d0w - P0w * d1w) * hres_symm

-- Regularity algebra in `A_C` relative to a point `r : L`.
end RegIdProof

private theorem cover_reg_identities_proof : CoverRegIdentitiesSpec :=
  ⟨fun mi S Q T U V a1 a0 b1 b0 => numM_isPolyDeg3 mi S Q T U V a1 a0 b1 b0,
   fun S Q T x y U V a1 a0 b1 b0 => P18_of_isPolyDeg4 S Q T x y U V a1 a0 b1 b0,
   fun φ a b U W hU hW => E1_of_cover φ a b U W hU hW,
   fun φ z U W hU hW0 hcb hW => E2_z_of_cover φ z U W hU hW0 hcb hW,
   fun φ z U W hU hW0 hcb hW => E3_z_of_cover φ z U W hU hW0 hcb hW,
   nine_U_G_AC_eq,
   pnm_P_G_eval_one,
   P18_z_AC_eq_regX,
   P18_z_AC_eq_regY,
   eta_AC_eq_a_elim⟩

end SymmetricSexticResidual.CoverResidue

theorem solution : SymmetricSexticResidual.CoverResidue.CoverRegIdentitiesSpec :=
  SymmetricSexticResidual.CoverResidue.cover_reg_identities_proof
