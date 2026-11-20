-- Prove2me | solution 1 for LL_Decomp587l.r0j16_short
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T10:02:34.635479+00:00
-- url     : https://prove2.me/submissions/92d698de-98d4-4042-b5a2-80018857c474

import Mathlib
import Definitions.Def_LL_Decomp587l_IsBuchstab
import Definitions.Def_LL_Decomp587l_ZeroBelowOne
import Definitions.Def_LL_Decomp587l_buchstabIntegral
import Definitions.Def_LL_Decomp587l_r0j16_lo
import Definitions.Def_LL_Decomp587l_r0j16_hi

open Real Set MeasureTheory LL_Decomp587l

namespace SolBuchstabR0J16

/-! ### Part 1: Pure-`Nat` 4D `Cell4` Simplex-Tree Verifier (`r0j16_short`) -/

def S_scale : Nat := 1000000000000
def D_grid : Nat := 3622912
def A_num : Nat := 1249280
def B_num : Nat := 1484800
def TargetNat : Nat := 74908000
def PaTail : Nat := 7870281
def W_ub_nat : Nat := 97322707

inductive Cell4 where
  | c4    (a b : Nat)
  | c31   (a0 b0 a1 b1 : Nat)
  | c13   (a0 b0 a1 b1 : Nat)
  | c22   (a0 b0 a1 b1 : Nat)
  | c211  (a0 b0 a1 b1 a2 b2 : Nat)
  | c121  (a0 b0 a1 b1 a2 b2 : Nat)
  | c112  (a0 b0 a1 b1 a2 b2 : Nat)
  | c1111 (a0 b0 a1 b1 a2 b2 a3 b3 : Nat)

inductive CTree where
  | Z
  | I
  | T
  | B
  | S2 (idx : Nat) (c0 c1 : CTree)
  | S3 (idx : Nat) (c0 c1 c2 : CTree)
  | S4 (idx : Nat) (c0 c1 c2 c3 : CTree)
  | S5 (idx : Nat) (c0 c1 c2 c3 c4 : CTree)

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b
def min2 (a b : Nat) : Nat := match Nat.ble a b with | true => a | false => b
def max2 (a b : Nat) : Nat := match Nat.ble a b with | true => b | false => a

theorem le_mul_ceilDiv {a b : Nat} (hb : 0 < b) : a ≤ b * ceilDiv a b := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  omega

theorem min2_le_left (a b : Nat) : min2 a b ≤ a := by
  unfold min2
  cases h : Nat.ble a b with
  | true => exact le_refl a
  | false =>
    dsimp only
    have : ¬ a ≤ b := by intro hle; rw [Nat.ble_eq.mpr hle] at h; exact Bool.noConfusion h
    omega

theorem min2_le_right (a b : Nat) : min2 a b ≤ b := by
  unfold min2
  cases h : Nat.ble a b with
  | true => exact Nat.ble_eq.mp h
  | false => exact le_refl b

theorem left_le_max2 (a b : Nat) : a ≤ max2 a b := by
  unfold max2
  cases h : Nat.ble a b with
  | true => exact Nat.ble_eq.mp h
  | false => exact le_refl a

theorem right_le_max2 (a b : Nat) : b ≤ max2 a b := by
  unfold max2
  cases h : Nat.ble a b with
  | true => exact le_refl b
  | false =>
    dsimp only
    have : ¬ a ≤ b := by intro hle; rw [Nat.ble_eq.mpr hle] at h; exact Bool.noConfusion h
    omega

def posPow4 (a b : Nat) : Nat :=
  match Nat.ble b a with
  | true => let d := a - b; let d2 := d * d; d2 * d2
  | false => 0

def box4Hs48 (h0 h1 h2 h3 R : Nat) : Nat :=
  let h22 := h2 + h2
  match Nat.ble (h0 + h1 + h22 + h3) R with
  | true => 48 * h0 * h1 * h2 * h3
  | false =>
    let p0 := posPow4 R 0
    let p1 := posPow4 R (h0 + h1)
    let p2 := posPow4 R (h0 + h22)
    let p3 := posPow4 R (h0 + h3)
    let p4 := posPow4 R (h1 + h22)
    let p5 := posPow4 R (h1 + h3)
    let p6 := posPow4 R (h22 + h3)
    let p7 := posPow4 R (h0 + h1 + h22 + h3)
    let n0 := posPow4 R h0
    let n1 := posPow4 R h1
    let n2 := posPow4 R h22
    let n3 := posPow4 R h3
    let n4 := posPow4 R (h0 + h1 + h22)
    let n5 := posPow4 R (h0 + h1 + h3)
    let n6 := posPow4 R (h0 + h22 + h3)
    let n7 := posPow4 R (h1 + h22 + h3)
    (p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7) - (n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7)

def evalVertInt (pa num fprod x0 x1 x2 x3 : Nat) : Nat :=
  ceilDiv num (fprod * x0 * x1 * x2 * x3 * (pa - x0 - x1 - x2 - x3))

def evalVertW (num dfprod x0 x1 x2 x3 : Nat) : Nat :=
  ceilDiv num (dfprod * x0 * x1 * x2 * x2 * x3)

def evalIntCell (pa : Nat) : Cell4 → Nat
  | .c4 a b =>
    let h := b - a; let h2 := h * h; let num := S_scale * D_grid * h2 * h2
    evalVertInt pa num 120 a a a a + evalVertInt pa num 120 a a a b +
    evalVertInt pa num 120 a a b b + evalVertInt pa num 120 a b b b +
    evalVertInt pa num 120 b b b b
  | .c31 a0 b0 a1 b1 =>
    let h0 := b0 - a0; let num := S_scale * D_grid * h0 * h0 * h0 * (b1 - a1)
    let s (y : Nat) :=
      evalVertInt pa num 48 a0 a0 a0 y + evalVertInt pa num 48 a0 a0 b0 y +
      evalVertInt pa num 48 a0 b0 b0 y + evalVertInt pa num 48 b0 b0 b0 y
    s a1 + s b1
  | .c13 a0 b0 a1 b1 =>
    let h1 := b1 - a1; let num := S_scale * D_grid * (b0 - a0) * h1 * h1 * h1
    let s (x : Nat) :=
      evalVertInt pa num 48 x a1 a1 a1 + evalVertInt pa num 48 x a1 a1 b1 +
      evalVertInt pa num 48 x a1 b1 b1 + evalVertInt pa num 48 x b1 b1 b1
    s a0 + s b0
  | .c22 a0 b0 a1 b1 =>
    let h0 := b0 - a0; let h1 := b1 - a1; let num := S_scale * D_grid * h0 * h0 * h1 * h1
    let s (x0 x1 : Nat) :=
      evalVertInt pa num 36 x0 x1 a1 a1 + evalVertInt pa num 36 x0 x1 a1 b1 +
      evalVertInt pa num 36 x0 x1 b1 b1
    s a0 a0 + s a0 b0 + s b0 b0
  | .c211 a0 b0 a1 b1 a2 b2 =>
    let h0 := b0 - a0; let num := S_scale * D_grid * h0 * h0 * (b1 - a1) * (b2 - a2)
    let s (x0 x1 : Nat) :=
      evalVertInt pa num 24 x0 x1 a1 a2 + evalVertInt pa num 24 x0 x1 a1 b2 +
      evalVertInt pa num 24 x0 x1 b1 a2 + evalVertInt pa num 24 x0 x1 b1 b2
    s a0 a0 + s a0 b0 + s b0 b0
  | .c121 a0 b0 a1 b1 a2 b2 =>
    let h1 := b1 - a1; let num := S_scale * D_grid * (b0 - a0) * h1 * h1 * (b2 - a2)
    let s (x1 x2 : Nat) :=
      evalVertInt pa num 24 a0 x1 x2 a2 + evalVertInt pa num 24 a0 x1 x2 b2 +
      evalVertInt pa num 24 b0 x1 x2 a2 + evalVertInt pa num 24 b0 x1 x2 b2
    s a1 a1 + s a1 b1 + s b1 b1
  | .c112 a0 b0 a1 b1 a2 b2 =>
    let h2 := b2 - a2; let num := S_scale * D_grid * (b0 - a0) * (b1 - a1) * h2 * h2
    let s (x2 x3 : Nat) :=
      evalVertInt pa num 24 a0 a1 x2 x3 + evalVertInt pa num 24 a0 b1 x2 x3 +
      evalVertInt pa num 24 b0 a1 x2 x3 + evalVertInt pa num 24 b0 b1 x2 x3
    s a2 a2 + s a2 b2 + s b2 b2
  | .c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
    let num := S_scale * D_grid * (b0 - a0) * (b1 - a1) * (b2 - a2) * (b3 - a3)
    let s (x0 x1 : Nat) :=
      evalVertInt pa num 16 x0 x1 a2 a3 + evalVertInt pa num 16 x0 x1 a2 b3 +
      evalVertInt pa num 16 x0 x1 b2 a3 + evalVertInt pa num 16 x0 x1 b2 b3
    s a0 a1 + s a0 b1 + s b0 a1 + s b0 b1

def evalWCell (nm dm : Nat) : Cell4 → Nat
  | .c4 a b =>
    let h := b - a; let h2 := h * h; let num := nm * S_scale * D_grid * h2 * h2; let df := dm * 120
    evalVertW num df a a a a + evalVertW num df a a a b +
    evalVertW num df a a b b + evalVertW num df a b b b +
    evalVertW num df b b b b
  | .c31 a0 b0 a1 b1 =>
    let h0 := b0 - a0; let num := nm * S_scale * D_grid * h0 * h0 * h0 * (b1 - a1); let df := dm * 48
    let s (y : Nat) :=
      evalVertW num df a0 a0 a0 y + evalVertW num df a0 a0 b0 y +
      evalVertW num df a0 b0 b0 y + evalVertW num df b0 b0 b0 y
    s a1 + s b1
  | .c13 a0 b0 a1 b1 =>
    let h1 := b1 - a1; let num := nm * S_scale * D_grid * (b0 - a0) * h1 * h1 * h1; let df := dm * 48
    let s (x : Nat) :=
      evalVertW num df x a1 a1 a1 + evalVertW num df x a1 a1 b1 +
      evalVertW num df x a1 b1 b1 + evalVertW num df x b1 b1 b1
    s a0 + s b0
  | .c22 a0 b0 a1 b1 =>
    let h0 := b0 - a0; let h1 := b1 - a1; let num := nm * S_scale * D_grid * h0 * h0 * h1 * h1; let df := dm * 36
    let s (x0 x1 : Nat) :=
      evalVertW num df x0 x1 a1 a1 + evalVertW num df x0 x1 a1 b1 +
      evalVertW num df x0 x1 b1 b1
    s a0 a0 + s a0 b0 + s b0 b0
  | .c211 a0 b0 a1 b1 a2 b2 =>
    let h0 := b0 - a0; let num := nm * S_scale * D_grid * h0 * h0 * (b1 - a1) * (b2 - a2); let df := dm * 24
    let s (x0 x1 : Nat) :=
      evalVertW num df x0 x1 a1 a2 + evalVertW num df x0 x1 a1 b2 +
      evalVertW num df x0 x1 b1 a2 + evalVertW num df x0 x1 b1 b2
    s a0 a0 + s a0 b0 + s b0 b0
  | .c121 a0 b0 a1 b1 a2 b2 =>
    let h1 := b1 - a1; let num := nm * S_scale * D_grid * (b0 - a0) * h1 * h1 * (b2 - a2); let df := dm * 24
    let s (x1 x2 : Nat) :=
      evalVertW num df a0 x1 x2 a2 + evalVertW num df a0 x1 x2 b2 +
      evalVertW num df b0 x1 x2 a2 + evalVertW num df b0 x1 x2 b2
    s a1 a1 + s a1 b1 + s b1 b1
  | .c112 a0 b0 a1 b1 a2 b2 =>
    let h2 := b2 - a2; let num := nm * S_scale * D_grid * (b0 - a0) * (b1 - a1) * h2 * h2; let df := dm * 24
    let s (x2 x3 : Nat) :=
      evalVertW num df a0 a1 x2 x3 + evalVertW num df a0 b1 x2 x3 +
      evalVertW num df b0 a1 x2 x3 + evalVertW num df b0 b1 x2 x3
    s a2 a2 + s a2 b2 + s b2 b2
  | .c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
    let num := nm * S_scale * D_grid * (b0 - a0) * (b1 - a1) * (b2 - a2) * (b3 - a3); let df := dm * 16
    let s (x0 x1 : Nat) :=
      evalVertW num df x0 x1 a2 a3 + evalVertW num df x0 x1 a2 b3 +
      evalVertW num df x0 x1 b2 a3 + evalVertW num df x0 x1 b2 b3
    s a0 a1 + s a0 b1 + s b0 a1 + s b0 b1

def cellVol48 : Cell4 → Nat
  | .c4 a b => let h := b - a; let h2 := h * h; 2 * h2 * h2
  | .c31 a0 b0 a1 b1 => let h0 := b0 - a0; 8 * h0 * h0 * h0 * (b1 - a1)
  | .c13 a0 b0 a1 b1 => let h1 := b1 - a1; 8 * (b0 - a0) * h1 * h1 * h1
  | .c22 a0 b0 a1 b1 => let h0 := b0 - a0; let h1 := b1 - a1; 12 * h0 * h0 * h1 * h1
  | .c211 a0 b0 a1 b1 a2 b2 => let h0 := b0 - a0; 24 * h0 * h0 * (b1 - a1) * (b2 - a2)
  | .c121 a0 b0 a1 b1 a2 b2 => let h1 := b1 - a1; 24 * (b0 - a0) * h1 * h1 * (b2 - a2)
  | .c112 a0 b0 a1 b1 a2 b2 => let h2 := b2 - a2; 24 * (b0 - a0) * (b1 - a1) * h2 * h2
  | .c1111 a0 b0 a1 b1 a2 b2 a3 b3 => 48 * (b0 - a0) * (b1 - a1) * (b2 - a2) * (b3 - a3)

def cellLoHi : Cell4 → Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat
  | .c4 a b => (a, a, a, a, b, b, b, b)
  | .c31 a0 b0 a1 b1 => (a0, a0, a0, a1, b0, b0, b0, b1)
  | .c13 a0 b0 a1 b1 => (a0, a1, a1, a1, b0, b1, b1, b1)
  | .c22 a0 b0 a1 b1 => (a0, a0, a1, a1, b0, b0, b1, b1)
  | .c211 a0 b0 a1 b1 a2 b2 => (a0, a0, a1, a2, b0, b0, b1, b2)
  | .c121 a0 b0 a1 b1 a2 b2 => (a0, a1, a1, a2, b0, b1, b1, b2)
  | .c112 a0 b0 a1 b1 a2 b2 => (a0, a1, a2, a2, b0, b1, b2, b2)
  | .c1111 a0 b0 a1 b1 a2 b2 a3 b3 => (a0, a1, a2, a3, b0, b1, b2, b3)

def canSplit (a b : Nat) : Bool :=
  match Nat.ble 2 (b - a) with
  | true => Nat.beq ((b - a) % 2) 0
  | false => false

def evalBndCell (pa pb : Nat) (c : Cell4) : Option Nat :=
  let (l0, l1, l2, l3, u0, u1, u2, u3) := cellLoHi c
  let wden := 48 * l0 * l1 * l2 * l2 * l3
  match Nat.ble 1 wden with
  | false => none
  | true =>
    let R := pb - (l0 + l1 + l2 + l2 + l3)
    let v48 := min2 (cellVol48 c) (box4Hs48 (u0 - l0) (u1 - l1) (u2 - l2) (u3 - l3) R)
    match Nat.ble (u0 + u1 + u2 + u2 + u3) pa with
    | true =>
      let diff := pa - (u0 + u1 + u2 + u3)
      let num_om := max2 (7 * diff) (12 * u2)
      let den_om := 12 * diff
      some (ceilDiv (S_scale * D_grid * v48 * num_om) (den_om * wden))
    | false =>
      match Nat.ble (l0 + l1 + l2 + l2 + l3 + 1) pa, Nat.ble pb (l0 + l1 + 3 * l2 + l3) with
      | true, true =>
        let Ra := pa - (l0 + l1 + l2 + l2 + l3)
        some (ceilDiv (S_scale * D_grid * v48 * (l2 + l3)) (wden * (l2 + l3 + Ra)))
      | _, _ =>
        some (ceilDiv (S_scale * D_grid * v48) wden)

def evalMainLeaf (pa pb : Nat) : CTree → Cell4 → Option Nat
  | .Z, c =>
    let (l0, l1, l2, l3, _, _, _, _) := cellLoHi c
    match Nat.ble pb (l0 + l1 + l2 + l2 + l3) with
    | true => some 0
    | false => none
  | .I, c =>
    let (l0, l1, l2, l3, u0, u1, u2, u3) := cellLoHi c
    match Nat.ble 1 l0, Nat.ble (u0 + u1 + u2 + u2 + u3) pa, Nat.ble pb (l0 + l1 + 3 * l2 + l3) with
    | true, true, true => some (evalIntCell pa c)
    | _, _, _ => none
  | .T, c =>
    let (l0, _, _, _, u0, u1, u2, u3) := cellLoHi c
    match Nat.ble 1 l0, Nat.ble (u0 + u1 + 3 * u2 + u3) pa with
    | true, true => some (evalWCell 7 12 c)
    | _, _ => none
  | .B, c => evalBndCell pa pb c
  | _, _ => none

def evalWLeaf : CTree → Cell4 → Option Nat
  | .T, c =>
    let (l0, _, _, _, _, _, _, _) := cellLoHi c
    match Nat.ble 1 l0 with
    | true => some (evalWCell 1 1 c)
    | false => none
  | _, _ => none

def evalGen (leaf : CTree → Cell4 → Option Nat) : CTree → Cell4 → Option Nat
  | .Z, c => leaf .Z c
  | .I, c => leaf .I c
  | .T, c => leaf .T c
  | .B, c => leaf .B c
  | .S5 0 t0 t1 t2 t3 t4, .c4 a b =>
    match canSplit a b with
    | false => none
    | true =>
      let m := (a + b) / 2
      match evalGen leaf t0 (.c4 m b), evalGen leaf t1 (.c13 a m m b),
            evalGen leaf t2 (.c22 a m m b), evalGen leaf t3 (.c31 a m m b),
            evalGen leaf t4 (.c4 a m) with
      | some v0, some v1, some v2, some v3, some v4 => some (v0 + v1 + v2 + v3 + v4)
      | _, _, _, _, _ => none
  | .S4 0 t0 t1 t2 t3, .c31 a0 b0 a1 b1 =>
    match canSplit a0 b0 with
    | false => none
    | true =>
      let m := (a0 + b0) / 2
      match evalGen leaf t0 (.c31 m b0 a1 b1), evalGen leaf t1 (.c121 a0 m m b0 a1 b1),
            evalGen leaf t2 (.c211 a0 m m b0 a1 b1), evalGen leaf t3 (.c31 a0 m a1 b1) with
      | some v0, some v1, some v2, some v3 => some (v0 + v1 + v2 + v3)
      | _, _, _, _ => none
  | .S2 1 t0 t1, .c31 a0 b0 a1 b1 =>
    match canSplit a1 b1 with
    | false => none
    | true =>
      let m := (a1 + b1) / 2
      match evalGen leaf t0 (.c31 a0 b0 m b1), evalGen leaf t1 (.c31 a0 b0 a1 m) with
      | some v0, some v1 => some (v0 + v1)
      | _, _ => none
  | .S2 0 t0 t1, .c13 a0 b0 a1 b1 =>
    match canSplit a0 b0 with
    | false => none
    | true =>
      let m := (a0 + b0) / 2
      match evalGen leaf t0 (.c13 m b0 a1 b1), evalGen leaf t1 (.c13 a0 m a1 b1) with
      | some v0, some v1 => some (v0 + v1)
      | _, _ => none
  | .S4 1 t0 t1 t2 t3, .c13 a0 b0 a1 b1 =>
    match canSplit a1 b1 with
    | false => none
    | true =>
      let m := (a1 + b1) / 2
      match evalGen leaf t0 (.c13 a0 b0 m b1), evalGen leaf t1 (.c112 a0 b0 a1 m m b1),
            evalGen leaf t2 (.c121 a0 b0 a1 m m b1), evalGen leaf t3 (.c13 a0 b0 a1 m) with
      | some v0, some v1, some v2, some v3 => some (v0 + v1 + v2 + v3)
      | _, _, _, _ => none
  | .S3 0 t0 t1 t2, .c22 a0 b0 a1 b1 =>
    match canSplit a0 b0 with
    | false => none
    | true =>
      let m := (a0 + b0) / 2
      match evalGen leaf t0 (.c22 m b0 a1 b1), evalGen leaf t1 (.c112 a0 m m b0 a1 b1),
            evalGen leaf t2 (.c22 a0 m a1 b1) with
      | some v0, some v1, some v2 => some (v0 + v1 + v2)
      | _, _, _ => none
  | .S3 1 t0 t1 t2, .c22 a0 b0 a1 b1 =>
    match canSplit a1 b1 with
    | false => none
    | true =>
      let m := (a1 + b1) / 2
      match evalGen leaf t0 (.c22 a0 b0 m b1), evalGen leaf t1 (.c211 a0 b0 a1 m m b1),
            evalGen leaf t2 (.c22 a0 b0 a1 m) with
      | some v0, some v1, some v2 => some (v0 + v1 + v2)
      | _, _, _ => none
  | .S3 0 t0 t1 t2, .c211 a0 b0 a1 b1 a2 b2 =>
    match canSplit a0 b0 with
    | false => none
    | true =>
      let m := (a0 + b0) / 2
      match evalGen leaf t0 (.c211 m b0 a1 b1 a2 b2), evalGen leaf t1 (.c1111 a0 m m b0 a1 b1 a2 b2),
            evalGen leaf t2 (.c211 a0 m a1 b1 a2 b2) with
      | some v0, some v1, some v2 => some (v0 + v1 + v2)
      | _, _, _ => none
  | .S2 1 t0 t1, .c211 a0 b0 a1 b1 a2 b2 =>
    match canSplit a1 b1 with
    | false => none
    | true =>
      let m := (a1 + b1) / 2
      match evalGen leaf t0 (.c211 a0 b0 m b1 a2 b2), evalGen leaf t1 (.c211 a0 b0 a1 m a2 b2) with
      | some v0, some v1 => some (v0 + v1)
      | _, _ => none
  | .S2 2 t0 t1, .c211 a0 b0 a1 b1 a2 b2 =>
    match canSplit a2 b2 with
    | false => none
    | true =>
      let m := (a2 + b2) / 2
      match evalGen leaf t0 (.c211 a0 b0 a1 b1 m b2), evalGen leaf t1 (.c211 a0 b0 a1 b1 a2 m) with
      | some v0, some v1 => some (v0 + v1)
      | _, _ => none
  | .S2 0 t0 t1, .c121 a0 b0 a1 b1 a2 b2 =>
    match canSplit a0 b0 with
    | false => none
    | true =>
      let m := (a0 + b0) / 2
      match evalGen leaf t0 (.c121 m b0 a1 b1 a2 b2), evalGen leaf t1 (.c121 a0 m a1 b1 a2 b2) with
      | some v0, some v1 => some (v0 + v1)
      | _, _ => none
  | .S3 1 t0 t1 t2, .c121 a0 b0 a1 b1 a2 b2 =>
    match canSplit a1 b1 with
    | false => none
    | true =>
      let m := (a1 + b1) / 2
      match evalGen leaf t0 (.c121 a0 b0 m b1 a2 b2), evalGen leaf t1 (.c1111 a0 b0 a1 m m b1 a2 b2),
            evalGen leaf t2 (.c121 a0 b0 a1 m a2 b2) with
      | some v0, some v1, some v2 => some (v0 + v1 + v2)
      | _, _, _ => none
  | .S2 2 t0 t1, .c121 a0 b0 a1 b1 a2 b2 =>
    match canSplit a2 b2 with
    | false => none
    | true =>
      let m := (a2 + b2) / 2
      match evalGen leaf t0 (.c121 a0 b0 a1 b1 m b2), evalGen leaf t1 (.c121 a0 b0 a1 b1 a2 m) with
      | some v0, some v1 => some (v0 + v1)
      | _, _ => none
  | .S2 0 t0 t1, .c112 a0 b0 a1 b1 a2 b2 =>
    match canSplit a0 b0 with
    | false => none
    | true =>
      let m := (a0 + b0) / 2
      match evalGen leaf t0 (.c112 m b0 a1 b1 a2 b2), evalGen leaf t1 (.c112 a0 m a1 b1 a2 b2) with
      | some v0, some v1 => some (v0 + v1)
      | _, _ => none
  | .S2 1 t0 t1, .c112 a0 b0 a1 b1 a2 b2 =>
    match canSplit a1 b1 with
    | false => none
    | true =>
      let m := (a1 + b1) / 2
      match evalGen leaf t0 (.c112 a0 b0 m b1 a2 b2), evalGen leaf t1 (.c112 a0 b0 a1 m a2 b2) with
      | some v0, some v1 => some (v0 + v1)
      | _, _ => none
  | .S3 2 t0 t1 t2, .c112 a0 b0 a1 b1 a2 b2 =>
    match canSplit a2 b2 with
    | false => none
    | true =>
      let m := (a2 + b2) / 2
      match evalGen leaf t0 (.c112 a0 b0 a1 b1 m b2), evalGen leaf t1 (.c1111 a0 b0 a1 b1 a2 m m b2),
            evalGen leaf t2 (.c112 a0 b0 a1 b1 a2 m) with
      | some v0, some v1, some v2 => some (v0 + v1 + v2)
      | _, _, _ => none
  | .S2 0 t0 t1, .c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
    match canSplit a0 b0 with
    | false => none
    | true =>
      let m := (a0 + b0) / 2
      match evalGen leaf t0 (.c1111 m b0 a1 b1 a2 b2 a3 b3), evalGen leaf t1 (.c1111 a0 m a1 b1 a2 b2 a3 b3) with
      | some v0, some v1 => some (v0 + v1)
      | _, _ => none
  | .S2 1 t0 t1, .c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
    match canSplit a1 b1 with
    | false => none
    | true =>
      let m := (a1 + b1) / 2
      match evalGen leaf t0 (.c1111 a0 b0 m b1 a2 b2 a3 b3), evalGen leaf t1 (.c1111 a0 b0 a1 m a2 b2 a3 b3) with
      | some v0, some v1 => some (v0 + v1)
      | _, _ => none
  | .S2 2 t0 t1, .c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
    match canSplit a2 b2 with
    | false => none
    | true =>
      let m := (a2 + b2) / 2
      match evalGen leaf t0 (.c1111 a0 b0 a1 b1 m b2 a3 b3), evalGen leaf t1 (.c1111 a0 b0 a1 b1 a2 m a3 b3) with
      | some v0, some v1 => some (v0 + v1)
      | _, _ => none
  | .S2 3 t0 t1, .c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
    match canSplit a3 b3 with
    | false => none
    | true =>
      let m := (a3 + b3) / 2
      match evalGen leaf t0 (.c1111 a0 b0 a1 b1 a2 b2 m b3), evalGen leaf t1 (.c1111 a0 b0 a1 b1 a2 b2 a3 m) with
      | some v0, some v1 => some (v0 + v1)
      | _, _ => none
  | _, _ => none


def evalTree (pa pb : Nat) (t : CTree) (c : Cell4) : Option Nat :=
  evalGen (evalMainLeaf pa pb) t c

def evalWTree (t : CTree) (c : Cell4) : Option Nat :=
  evalGen evalWLeaf t c

def initCell : Cell4 := .c4 A_num B_num

def checkInterval (pa pb : Nat) (t : CTree) : Bool :=
  match evalTree pa pb t initCell with
  | some v => Nat.ble v TargetNat
  | none => false


def weight_tree : CTree :=
  (.S5 0 .T (.S2 0 (.S4 1 .T .T .T .T) (.S4 1 .T .T .T .T)) (.S3 0 .T (.S3 2 .T .T .T) (.S3 1 .T .T .T)) (.S4 0 .T .T .T .T) (.S5 0 .T .T .T .T .T))

theorem check_weight_tree :
    (match evalWTree weight_tree initCell with | some v => Nat.ble v W_ub_nat | none => false) = true := by
  decide +kernel

theorem check_tail_1 : W_ub_nat * B_num ≤ TargetNat * (PaTail - 4 * B_num) := by decide +kernel
theorem check_tail_2 : 7 * W_ub_nat ≤ 12 * TargetNat := by decide +kernel
theorem check_tail_pos : 5 * B_num ≤ PaTail := by decide +kernel

def tree_0 : CTree :=
  (.S5 0 (.S5 0 (.S5 0 .Z .B (.S3 0 .B (.S3 2 .Z .B (.S2 0 .B (.S2 1 .B (.S3 2 .Z .B (.S2 0 .B .B))))) (.S3 1 .Z (.S3 0 .B .B (.S2 1 .B (.S2 2 .B (.S3 0 .B .B .B)))) (.S3 0 (.S3 1 .Z .B .B) (.S3 2 .B .B (.S2 0 .B .B)) (.S3 1 .B (.S3 0 .B .B .B) .B)))) (.S4 0 (.S2 1 (.S4 0 .Z .Z .B (.S2 1 .B .B)) (.S4 0 .B .B (.S2 2 .B (.S3 0 .B .B .B)) (.S2 1 .B .B))) (.S2 2 (.S2 0 (.S3 1 .B .B (.S2 2 (.S2 0 .B .B) (.S2 0 .B .B))) (.S3 1 .B .B (.S2 2 (.S2 0 .B .B) (.S2 0 .B .B)))) (.S2 0 (.S3 1 (.S2 2 .B (.S2 0 .B .B)) (.S2 3 .B (.S2 0 .B .B)) (.S2 2 (.S2 0 .B .B) (.S2 0 .B .I))) (.S3 1 (.S2 2 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 2 (.S2 0 .B .I) .I)))) (.S2 2 (.S3 0 (.S2 1 (.S2 2 .B (.S3 0 .B .B .B)) (.S2 2 (.S3 0 .B .B .B) (.S3 0 .B .B .B))) (.S2 2 (.S2 3 .B (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I))) (.S2 1 (.S2 2 (.S3 0 .B .B .B) (.S3 0 .B .B .B)) (.S2 2 (.S3 0 .B .I .I) .I))) (.S3 0 (.S2 1 (.S2 2 (.S3 0 .B .B .B) (.S3 0 .B .B .B)) (.S2 2 (.S3 0 .B .I .I) .I)) (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)) .I) (.S2 1 (.S2 2 (.S3 0 .B .I .I) .I) .I))) (.S2 1 (.S4 0 (.S2 1 .B .I) .I .I .I) .I)) (.S5 0 (.S5 0 .B .B .B .B .I) (.S2 0 (.S4 1 .B (.S2 0 .B .B) .I .I) (.S4 1 .B (.S2 0 .B .I) .I .I)) (.S3 0 (.S3 1 .B .I .I) .I .I) .I .I)) (.S2 0 (.S4 1 (.S2 0 (.S4 1 .Z .Z .B (.S2 0 .B (.S4 1 .Z .Z .B .B))) (.S4 1 .Z .Z (.S2 0 .B (.S3 1 .Z .B (.S2 2 .B (.S2 0 .B .B)))) (.S2 0 (.S4 1 .Z .B (.S2 0 .B .B) .B) (.S4 1 .B .B (.S2 0 .B .B) .B)))) (.S2 0 (.S2 1 (.S3 2 .Z .B (.S2 0 (.S2 1 (.S3 2 .Z .B (.S2 0 .B .B)) (.S3 2 .B .B (.S2 0 .B .B))) (.S2 1 (.S3 2 .B .B (.S2 0 .B .B)) (.S3 2 .B (.S2 0 .B .B) (.S2 0 .B .B))))) (.S3 2 .B (.S2 0 (.S2 1 .B (.S2 2 .B (.S2 3 .B (.S2 0 .B .B)))) (.S2 1 (.S2 2 .B (.S2 3 .B (.S2 0 .B .B))) (.S2 2 .B (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B))))) (.S2 0 (.S2 1 (.S3 2 .B (.S2 0 .B .B) (.S2 0 .B .B)) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I))) (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I)) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I))))) (.S2 1 (.S3 2 .B (.S2 0 (.S2 1 .B (.S2 2 .B (.S2 3 .B (.S2 0 .B .B)))) (.S2 1 (.S2 2 .B (.S2 3 .B (.S2 0 .B .B))) (.S2 2 .B (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B))))) (.S2 0 (.S2 1 (.S3 2 .B (.S2 0 .B .B) (.S2 0 .B .B)) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I))) (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I)) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I)))) (.S3 2 (.S2 0 .B (.S2 1 .B (.S3 2 .Z .B (.S2 0 .B .B)))) (.S2 0 (.S2 1 (.S2 2 .B (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B))) (.S2 2 (.S2 3 .B (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)))) (.S2 1 (.S2 2 (.S2 3 .B (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I))) (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .I) .I)))) (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I) (.S3 2 (.S2 0 .B .B) .I .I)) (.S2 1 (.S3 2 (.S2 0 .B .B) .I .I) (.S3 2 (.S2 0 .B .I) .I .I)))))) (.S2 0 (.S3 1 (.S2 2 (.S2 0 (.S3 1 (.S2 2 .B (.S2 0 .B .B)) (.S2 3 .B (.S2 0 .B .B)) (.S2 2 (.S2 0 .B .B) (.S2 0 .B .I))) (.S3 1 (.S2 2 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 2 (.S2 0 .B .I) .I))) (.S2 0 (.S3 1 (.S2 2 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)) .I) (.S3 1 (.S2 2 (.S2 0 .B .B) (.S2 0 .B .I)) (.S2 3 (.S2 0 .B .I) .I) .I))) (.S2 3 (.S2 0 (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .I) .I)) (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)) .I)) (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)) .I) (.S2 2 (.S2 3 (.S2 0 .B .I) .I) .I))) (.S2 0 (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .I) .I) .I) .I) .I)) .I) (.S3 1 (.S2 2 (.S2 0 (.S3 1 (.S2 2 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)) .I) (.S3 1 (.S2 2 (.S2 0 .B .B) (.S2 0 .B .I)) (.S2 3 (.S2 0 .B .I) .I) .I)) (.S2 0 (.S3 1 (.S2 2 (.S2 0 .B .I) .I) .I .I) .I)) (.S2 3 (.S2 0 (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .I) .I) .I) .I) .I) .I) .I)) (.S2 0 (.S4 1 (.S2 0 (.S4 1 .B .I .I .I) .I) .I .I .I) .I)) (.S4 1 (.S2 0 (.S4 1 .Z .B (.S2 0 (.S3 1 .B .B (.S2 2 (.S2 0 .B .B) (.S2 0 .B .B))) (.S3 1 .B .B (.S2 2 (.S2 0 .B .B) (.S2 0 .B .B)))) (.S2 0 (.S4 1 .B (.S2 0 .B .B) (.S2 0 .B .B) .B) (.S4 1 .B (.S2 0 .B .B) (.S2 0 .B .I) .I))) (.S4 1 .B (.S2 0 .B (.S2 1 .B (.S3 2 .Z .B (.S2 0 .B .B)))) (.S2 0 (.S3 1 (.S2 2 .B (.S2 0 .B .B)) (.S2 3 .B (.S2 0 .B .B)) (.S2 2 (.S2 0 .B .B) (.S2 0 .B .I))) (.S3 1 (.S2 2 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 2 (.S2 0 .B .I) .I))) (.S2 0 (.S4 1 .B (.S2 0 .B .B) .I .I) (.S4 1 .B (.S2 0 .B .I) .I .I)))) (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B (.S2 1 .B (.S3 2 .Z .B (.S2 0 .B .B)))) (.S2 0 (.S2 1 (.S2 2 .B (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B))) (.S2 2 (.S2 3 .B (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)))) (.S2 1 (.S2 2 (.S2 3 .B (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I))) (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .I) .I)))) (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I) (.S3 2 (.S2 0 .B .B) .I .I)) (.S2 1 (.S3 2 (.S2 0 .B .B) .I .I) (.S3 2 (.S2 0 .B .I) .I .I)))) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .Z .B (.S2 0 .B .B)) (.S3 2 .B .B (.S2 0 .B .B))) (.S2 1 (.S3 2 .B .B (.S2 0 .B .B)) (.S3 2 .B (.S2 0 .B .B) (.S2 0 .B .B)))) (.S2 0 (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .I) .I)) (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)) .I)) (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)) .I) (.S2 2 (.S2 3 (.S2 0 .B .I) .I) .I))) (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .I) .I .I) .I) .I))) (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 .Z .B (.S2 0 .B .B)) (.S3 2 .B .B (.S2 0 .B .B))) (.S2 1 (.S3 2 .B .B (.S2 0 .B .B)) (.S3 2 .B (.S2 0 .B .B) (.S2 0 .B .B)))) (.S2 0 (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .I) .I)) (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)) .I)) (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)) .I) (.S2 2 (.S2 3 (.S2 0 .B .I) .I) .I))) (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .I) .I .I) .I) .I)) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B (.S2 0 .B .B) (.S2 0 .B .B)) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I))) (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I)) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I))) (.S2 0 (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .I) .I) .I) .I) .I) .I))) (.S2 0 (.S3 1 (.S2 2 (.S2 0 (.S3 1 (.S2 2 (.S2 0 .B .I) .I) .I .I) .I) .I) .I .I) .I) .I)) (.S3 0 (.S3 1 (.S3 0 (.S3 1 (.S3 0 .B .B (.S3 1 .Z .B .B)) (.S3 0 (.S2 1 (.S2 2 .B (.S3 0 .B .B .B)) (.S2 2 (.S3 0 .B .B .B) (.S3 0 .B .B .B))) (.S2 2 (.S2 3 .B (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I))) (.S2 1 (.S2 2 (.S3 0 .B .B .B) (.S3 0 .B .B .B)) (.S2 2 (.S3 0 .B .I .I) .I))) (.S3 0 (.S3 1 .B (.S3 0 .B .I .I) .I) (.S3 2 (.S2 0 .B .B) .I .I) (.S3 1 .B .I .I))) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .Z .B (.S2 0 .B .B)) (.S3 2 .B .B (.S2 0 .B .B))) (.S2 1 (.S3 2 .B .B (.S2 0 .B .B)) (.S3 2 .B (.S2 0 .B .B) (.S2 0 .B .B)))) (.S2 0 (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .I) .I)) (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)) .I)) (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)) .I) (.S2 2 (.S2 3 (.S2 0 .B .I) .I) .I))) (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .I) .I .I) .I) .I)) (.S3 1 (.S3 0 (.S3 1 .B (.S3 0 .B .B .B) .B) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I)) (.S3 1 .B (.S3 0 .B .I .I) .I)) (.S3 0 (.S2 1 (.S2 2 (.S3 0 .B .I .I) .I) .I) .I .I) .I)) (.S3 0 (.S2 1 (.S2 2 (.S3 0 (.S2 1 (.S2 2 (.S3 0 .B .I .I) .I) .I) .I .I) .I) .I) .I .I) .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B (.S2 0 .B .B) (.S2 0 .B .B)) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I))) (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I)) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I))) (.S2 0 (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .I) .I) .I) .I) .I) .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I) (.S3 2 (.S2 0 .B .B) .I .I)) (.S2 1 (.S3 2 (.S2 0 .B .B) .I .I) (.S3 2 (.S2 0 .B .I) .I .I))) .I .I)) (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I) (.S3 2 (.S2 0 .B .B) .I .I)) (.S2 1 (.S3 2 (.S2 0 .B .B) .I .I) (.S3 2 (.S2 0 .B .I) .I .I))) .I .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .I) .I .I) .I) .I) .I .I))) .I .I) (.S3 1 (.S3 0 (.S3 1 (.S3 0 (.S3 1 .B .I .I) .I .I) .I .I) .I .I) .I .I)) (.S4 0 .I .I .I .I) (.S5 0 .I .I .I .I .I)) (.S2 0 (.S4 1 (.S2 0 (.S4 1 (.S2 0 (.S4 1 (.S2 0 .B (.S4 1 .Z .Z .B .B)) (.S2 0 (.S2 1 (.S3 2 .Z .B (.S2 0 .B .B)) (.S3 2 .B .B (.S2 0 .B .B))) (.S2 1 (.S3 2 .B .B (.S2 0 .B .B)) (.S3 2 .B (.S2 0 .B .B) (.S2 0 .B .B)))) (.S2 0 (.S3 1 (.S2 2 (.S2 0 .B .B) (.S2 0 .B .B)) (.S2 3 (.S2 0 .B .B) (.S2 0 .B .I)) .I) (.S3 1 (.S2 2 (.S2 0 .B .B) (.S2 0 .B .I)) (.S2 3 (.S2 0 .B .I) .I) .I)) (.S2 0 (.S4 1 .B .I .I .I) .I)) (.S4 1 (.S2 0 (.S4 1 .Z .B (.S2 0 .B .B) .B) (.S4 1 .B .B (.S2 0 .B .B) .B)) (.S2 0 (.S2 1 (.S3 2 .B (.S2 0 .B .B) (.S2 0 .B .B)) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I))) (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I)) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I))) (.S2 0 (.S3 1 (.S2 2 (.S2 0 .B .I) .I) .I .I) .I) .I)) (.S2 0 (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B (.S2 0 .B .B) (.S2 0 .B .B)) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I))) (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .B) (.S2 0 .B .I)) (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I))) (.S2 0 (.S2 1 (.S2 2 (.S2 3 (.S2 0 .B .I) .I) .I) .I) .I) .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I) (.S3 2 (.S2 0 .B .B) .I .I)) (.S2 1 (.S3 2 (.S2 0 .B .B) .I .I) (.S3 2 (.S2 0 .B .I) .I .I))) .I .I)) (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I) (.S3 2 (.S2 0 .B .B) .I .I)) (.S2 1 (.S3 2 (.S2 0 .B .B) .I .I) (.S3 2 (.S2 0 .B .I) .I .I))) .I .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .I) .I .I) .I) .I) .I .I))) .I .I) (.S4 1 (.S2 0 (.S4 1 (.S2 0 (.S4 1 .B (.S2 0 .B .B) (.S2 0 .B .B) .B) (.S4 1 .B (.S2 0 .B .B) (.S2 0 .B .I) .I)) (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .B) (.S2 0 .B .I) .I) (.S3 2 (.S2 0 .B .B) .I .I)) (.S2 1 (.S3 2 (.S2 0 .B .B) .I .I) (.S3 2 (.S2 0 .B .I) .I .I))) .I .I) (.S4 1 (.S2 0 (.S4 1 .B (.S2 0 .B .B) .I .I) (.S4 1 .B (.S2 0 .B .I) .I .I)) (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .I) .I .I) .I) .I) .I .I)) (.S2 0 (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .I) .I .I) .I) .I) .I .I) .I) .I) .I .I)) (.S2 0 (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 (.S2 0 .B .I) .I .I) .I) .I) .I .I) .I) .I) .I .I) (.S3 2 .I .I .I)) (.S2 1 (.S3 2 .I .I .I) (.S3 2 .I .I .I))) (.S2 0 (.S3 1 .I (.S2 3 .I .I) .I) (.S3 1 .I (.S2 3 .I .I) .I)) (.S2 0 (.S4 1 .I .I .I .I) (.S4 1 .I .I .I .I))) (.S4 1 (.S2 0 (.S4 1 (.S2 0 (.S4 1 (.S2 0 (.S4 1 .B .I .I .I) .I) .I .I .I) .I) .I .I .I) (.S4 1 .I .I .I .I)) (.S2 0 (.S2 1 (.S3 2 .I .I .I) (.S3 2 .I .I .I)) (.S2 1 (.S3 2 .I .I .I) (.S3 2 .I .I .I))) (.S2 0 (.S3 1 .I (.S2 3 .I .I) .I) (.S3 1 .I (.S2 3 .I .I) .I)) (.S2 0 (.S4 1 .I .I .I .I) (.S4 1 .I .I .I .I)))) (.S3 0 (.S3 1 (.S3 0 (.S3 1 .I .I .I) (.S3 2 .I .I .I) (.S3 1 .I .I .I)) (.S3 0 (.S2 1 .I .I) (.S2 2 (.S2 3 .I .I) (.S2 3 .I .I)) (.S2 1 .I .I)) (.S3 0 (.S3 1 .I .I .I) (.S3 2 .I .I .I) (.S3 1 .I .I .I))) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .I .I .I) (.S3 2 .I .I .I)) (.S2 1 (.S3 2 .I .I .I) (.S3 2 .I .I .I))) (.S2 0 (.S2 1 (.S2 2 (.S2 3 .I .I) (.S2 3 .I .I)) (.S2 2 (.S2 3 .I .I) (.S2 3 .I .I))) (.S2 1 (.S2 2 (.S2 3 .I .I) (.S2 3 .I .I)) (.S2 2 (.S2 3 .I .I) (.S2 3 .I .I)))) (.S2 0 (.S2 1 (.S3 2 .I .I .I) (.S3 2 .I .I .I)) (.S2 1 (.S3 2 .I .I .I) (.S3 2 .I .I .I)))) (.S3 1 (.S3 0 .I (.S3 2 .I .I .I) .I) (.S3 0 (.S2 1 .I .I) (.S2 2 (.S2 3 .I .I) (.S2 3 .I .I)) (.S2 1 .I .I)) (.S3 0 (.S3 1 .I .I .I) (.S3 2 .I .I .I) (.S3 1 .I .I .I)))) (.S4 0 (.S2 1 (.S4 0 .I .I .I .I) (.S4 0 .I .I .I .I)) (.S2 2 (.S2 0 (.S3 1 .I (.S2 3 .I .I) .I) (.S3 1 .I (.S2 3 .I .I) .I)) (.S2 0 (.S3 1 .I (.S2 3 .I .I) .I) (.S3 1 .I (.S2 3 .I .I) .I))) (.S2 2 (.S3 0 (.S2 1 .I .I) (.S2 2 (.S2 3 .I .I) (.S2 3 .I .I)) (.S2 1 .I .I)) (.S3 0 (.S2 1 .I .I) (.S2 2 (.S2 3 .I .I) (.S2 3 .I .I)) (.S2 1 .I .I))) (.S2 1 (.S4 0 .I .I .I .I) (.S4 0 .I .I .I .I))) (.S5 0 (.S5 0 .I .I .I .I .I) (.S2 0 (.S4 1 .I .I .I .I) (.S4 1 .I .I .I .I)) (.S3 0 (.S3 1 .I .I .I) (.S3 2 .I .I .I) (.S3 1 .I .I .I)) (.S4 0 .I .I .I .I) (.S5 0 .I .I .I .I .I)))
def tree_1 : CTree :=
  (.S5 0 (.S5 0 (.S5 0 .Z .B (.S3 0 .B .B (.S3 1 .Z .B (.S3 0 .B (.S3 2 .B .B .B) .B))) (.S4 0 (.S2 1 .B (.S4 0 .B .B .B .B)) (.S2 2 (.S2 0 (.S3 1 .B .B .B) (.S3 1 .B .B .B)) (.S2 0 (.S3 1 .B .B .B) (.S3 1 .B .B .I))) (.S2 2 (.S3 0 (.S2 1 .B .B) (.S2 2 .B .B) (.S2 1 .B .I)) (.S3 0 (.S2 1 .B .I) (.S2 2 .B .I) .I)) .I) (.S5 0 .B (.S2 0 (.S4 1 .B .B .I .I) (.S4 1 .B .I .I .I)) .I .I .I)) (.S2 0 (.S4 1 (.S2 0 .B (.S4 1 .Z .Z .B (.S2 0 (.S4 1 .Z .B .B .B) (.S4 1 .B .B .B .B)))) (.S2 0 (.S2 1 (.S3 2 .Z .B (.S2 0 (.S2 1 .B (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B)))) (.S3 2 .B (.S2 0 (.S2 1 .B .B) (.S2 1 .B (.S2 2 .B .B))) (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .I)) (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I))))) (.S2 1 (.S3 2 .B (.S2 0 (.S2 1 .B .B) (.S2 1 .B (.S2 2 .B .B))) (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .I)) (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I)))) (.S3 2 .B (.S2 0 (.S2 1 (.S2 2 .B .B) (.S2 2 .B .B)) (.S2 1 (.S2 2 .B .B) (.S2 2 .B .I))) (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I))))) (.S2 0 (.S3 1 (.S2 2 (.S2 0 (.S3 1 .B .B .B) (.S3 1 .B .B .I)) (.S2 0 (.S3 1 .B .B .I) (.S3 1 .B .I .I))) (.S2 3 (.S2 0 (.S2 1 (.S2 2 .B .I) (.S2 2 .B .I)) (.S2 1 (.S2 2 .B .I) .I)) .I) .I) (.S3 1 (.S2 2 (.S2 0 (.S3 1 .B .B .I) (.S3 1 .B .I .I)) .I) .I .I)) .I) (.S4 1 (.S2 0 (.S4 1 .Z .B (.S2 0 (.S3 1 .B .B .B) (.S3 1 .B .B .B)) (.S2 0 (.S4 1 .B .B .B .I) (.S4 1 .B .B .I .I))) (.S4 1 .B .B (.S2 0 (.S3 1 .B .B .B) (.S3 1 .B .B .I)) (.S2 0 (.S4 1 .B .B .I .I) (.S4 1 .B .I .I .I)))) (.S2 0 (.S2 1 (.S3 2 .B (.S2 0 (.S2 1 (.S2 2 .B .B) (.S2 2 .B .B)) (.S2 1 (.S2 2 .B .B) (.S2 2 .B .I))) (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I))) (.S3 2 (.S2 0 (.S2 1 .B (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B))) (.S2 0 (.S2 1 (.S2 2 .B .I) (.S2 2 .B .I)) (.S2 1 (.S2 2 .B .I) .I)) .I)) (.S2 1 (.S3 2 (.S2 0 (.S2 1 .B (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B))) (.S2 0 (.S2 1 (.S2 2 .B .I) (.S2 2 .B .I)) (.S2 1 (.S2 2 .B .I) .I)) .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .I)) (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I))) .I .I))) .I .I)) (.S3 0 (.S3 1 (.S3 0 (.S3 1 .B (.S3 0 (.S2 1 .B .B) (.S2 2 .B .B) (.S2 1 .B .I)) (.S3 0 .B (.S3 2 .B .I .I) .I)) (.S3 2 (.S2 0 (.S2 1 .B (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B))) (.S2 0 (.S2 1 (.S2 2 .B .I) (.S2 2 .B .I)) (.S2 1 (.S2 2 .B .I) .I)) .I) (.S3 1 (.S3 0 .B (.S3 2 .B .B .I) .B) .I .I)) .I .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .I)) (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I))) .I .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I)) .I .I)) (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I)) .I .I) .I)) .I .I) .I) (.S4 0 .I .I .I .I) .I) (.S2 0 (.S4 1 (.S2 0 (.S4 1 (.S2 0 (.S4 1 .B (.S2 0 (.S2 1 .B (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B))) (.S2 0 (.S3 1 .B .B .I) (.S3 1 .B .I .I)) .I) (.S4 1 (.S2 0 (.S4 1 .Z .B .B .B) (.S4 1 .B .B .B .B)) (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .I)) (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I))) .I .I)) (.S2 0 (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .I)) (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I))) .I .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I)) .I .I)) (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I)) .I .I) .I)) .I .I) (.S4 1 (.S2 0 (.S4 1 (.S2 0 (.S4 1 .B .B .B .I) (.S4 1 .B .B .I .I)) (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I)) .I .I) (.S4 1 (.S2 0 (.S4 1 .B .B .I .I) (.S4 1 .B .I .I .I)) .I .I .I)) .I .I .I)) (.S2 0 (.S2 1 .I .I) (.S2 1 .I .I)) (.S2 0 (.S3 1 .I .I .I) (.S3 1 .I .I .I)) .I) (.S4 1 (.S2 0 .I .I) (.S2 0 (.S2 1 .I .I) (.S2 1 .I .I)) (.S2 0 (.S3 1 .I .I .I) (.S3 1 .I .I .I)) (.S2 0 .I .I))) (.S3 0 (.S3 1 (.S3 0 .I .I .I) (.S3 0 .I .I .I) (.S3 0 .I .I .I)) (.S3 2 (.S2 0 (.S2 1 .I .I) (.S2 1 .I .I)) (.S2 0 (.S2 1 .I .I) (.S2 1 .I .I)) (.S2 0 (.S2 1 .I .I) (.S2 1 .I .I))) (.S3 1 (.S3 0 .I .I .I) (.S3 0 .I .I .I) (.S3 0 .I .I .I))) (.S4 0 (.S2 1 (.S4 0 .I .I .I .I) (.S4 0 .I .I .I .I)) (.S2 2 (.S2 0 (.S3 1 .I .I .I) (.S3 1 .I .I .I)) (.S2 0 (.S3 1 .I .I .I) (.S3 1 .I .I .I))) (.S2 2 (.S3 0 .I .I .I) (.S3 0 .I .I .I)) (.S2 1 (.S4 0 .I .I .I .I) (.S4 0 .I .I .I .I))) (.S5 0 .I (.S2 0 .I .I) (.S3 0 .I .I .I) (.S4 0 .I .I .I .I) .I))
def tree_2 : CTree :=
  (.S5 0 (.S5 0 (.S5 0 .Z .B (.S3 0 .B (.S3 2 .Z .B (.S2 0 (.S2 1 .B (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B)))) (.S3 1 .B (.S3 0 .B (.S2 2 .B (.S2 3 .B .B)) (.S2 1 .B .B)) (.S3 0 .B (.S3 2 .B .B .B) .B))) (.S4 0 (.S2 1 (.S4 0 .B .B .B .B) (.S4 0 .B .B .B .B)) (.S2 2 (.S2 0 (.S3 1 .B (.S2 3 .B .B) .B) (.S3 1 .B (.S2 3 .B .B) .B)) (.S2 0 (.S3 1 .B (.S2 3 .B .B) .B) (.S3 1 .B .B .I))) (.S2 2 (.S3 0 (.S2 1 .B .B) (.S2 2 (.S2 3 .B .B) .B) (.S2 1 .B .I)) (.S3 0 (.S2 1 .B .I) (.S2 2 .B .I) .I)) .I) (.S5 0 .B (.S2 0 (.S4 1 .B .B .I .I) (.S4 1 .B .I .I .I)) .I .I .I)) (.S2 0 (.S4 1 (.S2 0 (.S4 1 .Z .Z .B (.S2 0 (.S4 1 .Z .B .B .B) (.S4 1 .B .B .B .B))) (.S4 1 .Z .B (.S2 0 (.S3 1 .B .B .B) (.S3 1 .B .B .B)) (.S2 0 (.S4 1 .B .B .B .B) (.S4 1 .B .B .B .B)))) (.S2 0 (.S2 1 (.S3 2 .B (.S2 0 (.S2 1 .B (.S2 2 .B (.S2 3 .B .B))) (.S2 1 (.S2 2 .B (.S2 3 .B .B)) (.S2 2 .B (.S2 3 .B .B)))) (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B)))) (.S3 2 .B (.S2 0 (.S2 1 (.S2 2 .B (.S2 3 .B .B)) (.S2 2 (.S2 3 .B .B) (.S2 3 .B .B))) (.S2 1 (.S2 2 (.S2 3 .B .B) (.S2 3 .B .B)) (.S2 2 (.S2 3 .B .B) .B))) (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .I)) (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I))))) (.S2 1 (.S3 2 .B (.S2 0 (.S2 1 (.S2 2 .B (.S2 3 .B .B)) (.S2 2 (.S2 3 .B .B) (.S2 3 .B .B))) (.S2 1 (.S2 2 (.S2 3 .B .B) (.S2 3 .B .B)) (.S2 2 (.S2 3 .B .B) .B))) (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .I)) (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I)))) (.S3 2 (.S2 0 (.S2 1 .B (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B))) (.S2 0 (.S2 1 (.S2 2 (.S2 3 .B .B) .B) (.S2 2 (.S2 3 .B .B) .B)) (.S2 1 (.S2 2 (.S2 3 .B .B) .B) (.S2 2 .B .I))) (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I))))) (.S2 0 (.S3 1 (.S2 2 (.S2 0 (.S3 1 .B (.S2 3 .B .B) .B) (.S3 1 .B .B .I)) (.S2 0 (.S3 1 .B .B .I) (.S3 1 .B .I .I))) (.S2 3 (.S2 0 (.S2 1 (.S2 2 .B .I) (.S2 2 .B .I)) (.S2 1 (.S2 2 .B .I) .I)) .I) .I) (.S3 1 (.S2 2 (.S2 0 (.S3 1 .B .B .I) (.S3 1 .B .I .I)) .I) .I .I)) .I) (.S4 1 (.S2 0 (.S4 1 .B .B (.S2 0 (.S3 1 .B (.S2 3 .B .B) .B) (.S3 1 .B (.S2 3 .B .B) .B)) (.S2 0 (.S4 1 .B .B .B .I) (.S4 1 .B .B .I .I))) (.S4 1 .B (.S2 0 (.S2 1 .B (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B))) (.S2 0 (.S3 1 .B (.S2 3 .B .B) .B) (.S3 1 .B .B .I)) (.S2 0 (.S4 1 .B .B .I .I) (.S4 1 .B .I .I .I)))) (.S2 0 (.S2 1 (.S3 2 (.S2 0 (.S2 1 .B (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B))) (.S2 0 (.S2 1 (.S2 2 (.S2 3 .B .B) .B) (.S2 2 (.S2 3 .B .B) .B)) (.S2 1 (.S2 2 (.S2 3 .B .B) .B) (.S2 2 .B .I))) (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I))) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B))) (.S2 0 (.S2 1 (.S2 2 .B .I) (.S2 2 .B .I)) (.S2 1 (.S2 2 .B .I) .I)) .I)) (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B))) (.S2 0 (.S2 1 (.S2 2 .B .I) (.S2 2 .B .I)) (.S2 1 (.S2 2 .B .I) .I)) .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .I)) (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I))) .I .I))) .I .I)) (.S3 0 (.S3 1 (.S3 0 (.S3 1 (.S3 0 .B (.S3 2 .B .B .B) .B) (.S3 0 (.S2 1 .B .B) (.S2 2 (.S2 3 .B .B) .B) (.S2 1 .B .I)) (.S3 0 .B (.S3 2 .B .I .I) .I)) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B))) (.S2 0 (.S2 1 (.S2 2 .B .I) (.S2 2 .B .I)) (.S2 1 (.S2 2 .B .I) .I)) .I) (.S3 1 (.S3 0 .B (.S3 2 .B .B .I) .B) .I .I)) .I .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .I)) (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I))) .I .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I)) .I .I)) (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I)) .I .I) .I)) .I .I) .I) (.S4 0 .I .I .I .I) .I) (.S2 0 (.S4 1 (.S2 0 (.S4 1 (.S2 0 (.S4 1 (.S2 0 (.S4 1 .Z .B .B .B) (.S4 1 .B .B .B .B)) (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B)) (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .B))) (.S2 0 (.S3 1 .B .B .I) (.S3 1 .B .I .I)) .I) (.S4 1 (.S2 0 (.S4 1 .B .B .B .B) (.S4 1 .B .B .B .B)) (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .I)) (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I))) .I .I)) (.S2 0 (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .B .B) (.S3 2 .B .B .I)) (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I))) .I .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I)) .I .I)) (.S2 1 (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I)) .I .I) .I)) .I .I) (.S4 1 (.S2 0 (.S4 1 (.S2 0 (.S4 1 .B .B .B .I) (.S4 1 .B .B .I .I)) (.S2 0 (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) .I)) .I .I) (.S4 1 (.S2 0 (.S4 1 .B .B .I .I) (.S4 1 .B .I .I .I)) .I .I .I)) .I .I .I)) (.S2 0 (.S2 1 .I .I) (.S2 1 .I .I)) (.S2 0 (.S3 1 .I .I .I) (.S3 1 .I .I .I)) .I) (.S4 1 (.S2 0 .I .I) (.S2 0 (.S2 1 .I .I) (.S2 1 .I .I)) (.S2 0 (.S3 1 .I .I .I) (.S3 1 .I .I .I)) .I)) (.S3 0 (.S3 1 (.S3 0 .I .I .I) (.S3 0 .I .I .I) (.S3 0 .I .I .I)) (.S3 2 (.S2 0 (.S2 1 .I .I) (.S2 1 .I .I)) (.S2 0 (.S2 1 .I .I) (.S2 1 .I .I)) (.S2 0 (.S2 1 .I .I) (.S2 1 .I .I))) (.S3 1 (.S3 0 .I .I .I) (.S3 0 .I .I .I) (.S3 0 .I .I .I))) (.S4 0 (.S2 1 .I .I) (.S2 2 (.S2 0 (.S3 1 .I .I .I) (.S3 1 .I .I .I)) (.S2 0 (.S3 1 .I .I .I) (.S3 1 .I .I .I))) (.S2 2 (.S3 0 .I .I .I) (.S3 0 .I .I .I)) (.S2 1 (.S4 0 .I .I .I .I) (.S4 0 .I .I .I .I))) (.S5 0 .I (.S2 0 .I .I) (.S3 0 .I .I .I) (.S4 0 .I .I .I .I) .I))
def tree_3 : CTree :=
  (.S5 0 (.S5 0 (.S5 0 .B (.S2 0 .B .B) (.S3 0 .B .B .B) (.S4 0 .B .B .B .I) .B) (.S2 0 (.S4 1 (.S2 0 .B .B) (.S2 0 (.S2 1 .B .B) (.S2 1 .B (.S3 2 .B .B .I))) (.S2 0 (.S3 1 .B .I .I) .I) .I) (.S4 1 (.S2 0 .B .B) (.S2 0 (.S2 1 (.S3 2 .B .B .I) (.S3 2 .B .I .I)) (.S2 1 (.S3 2 .B .I .I) (.S3 2 .B .I .I))) .I .I)) (.S3 0 (.S3 1 (.S3 0 .B (.S3 2 .B .I .I) .B) .I .I) (.S3 2 (.S2 0 (.S2 1 (.S3 2 .B .I .I) .I) .I) .I .I) .I) .I .I) (.S2 0 (.S4 1 (.S2 0 (.S4 1 (.S2 0 .B .B) (.S2 0 (.S2 1 (.S3 2 .B .I .I) .I) .I) .I .I) (.S4 1 (.S2 0 .B .I) .I .I .I)) .I .I .I) .I) (.S3 0 .I (.S3 2 .I .I .I) .I) (.S4 0 .I .I .I (.S2 1 (.S4 0 .I .I .I (.S2 1 .B .B)) (.S4 0 .I .I (.S2 2 .I (.S3 0 .I (.S2 2 .I .B) .B)) (.S2 1 .B .B)))) (.S5 0 .I .I .I (.S4 0 (.S2 1 .I .B) (.S2 2 (.S2 0 (.S3 1 .I .I .B) (.S3 1 .I .I .B)) (.S2 0 (.S3 1 .I .I .B) (.S3 1 .I .B .B))) (.S2 2 (.S3 0 .B (.S2 2 .I .B) .B) (.S3 0 .B (.S2 2 .B .B) .B)) (.S2 1 .B .B)) (.S5 0 .B .B (.S3 0 .B .B .B) .B .B)))
def tree_4 : CTree :=
  (.S5 0 .I .I .I .B .B)

theorem check_intv_0 : checkInterval (7245824) (7247593) tree_0 = true := by decide +kernel
theorem check_intv_1 : checkInterval (7247593) (7251131) tree_1 = true := by decide +kernel
theorem check_intv_2 : checkInterval (7251131) (7265283) tree_2 = true := by decide +kernel
theorem check_intv_3 : checkInterval (7265283) (7718147) tree_3 = true := by decide +kernel
theorem check_intv_4 : checkInterval (7718147) (7870281) tree_4 = true := by decide +kernel

/-! ### Part 2: Elementary Buchstab Bounds -/

noncomputable section

private lemma buchstab_integral_eq {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    b * ω b - a * ω a = ∫ s in (a - 1)..(b - 1), ω s := by
  have hcont_w : ContinuousOn ω (Icc a b) :=
    hω.1.mono (fun x hx => by change 1 ≤ x; linarith [hx.1])
  have hcont_mul : ContinuousOn (fun t => t * ω t) (Icc a b) :=
    continuousOn_id.mul hcont_w
  have hderiv_open : ∀ x ∈ Ioo a b, HasDerivAt (fun t => t * ω t) (ω (x - 1)) x := by
    intro x hx
    exact hω.2.2 x (lt_of_le_of_lt ha hx.1)
  have hcont_shift : ContinuousOn (fun t => ω (t - 1)) (Icc a b) := by
    apply hω.1.comp (continuousOn_id.sub continuousOn_const)
    intro x hx
    change 1 ≤ x - 1
    linarith [hx.1]
  have hint : IntervalIntegrable (fun t => ω (t - 1)) volume a b :=
    hcont_shift.intervalIntegrable_of_Icc hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont_mul hderiv_open hint
  rw [← hftc, intervalIntegral.integral_comp_sub_right]

private lemma buchstab_nonneg_on_Icc {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ∀ n : ℕ, ∀ u : ℝ, 1 ≤ u → u ≤ (n : ℝ) + 2 → 0 ≤ ω u := by
  intro n
  induction n with
  | zero =>
    intro u hu1 hu2
    push_cast at hu2
    rw [hω.2.1 u hu1 (by linarith)]
    positivity
  | succ n ih =>
    intro u hu1 hu2
    by_cases hle : u ≤ (n : ℝ) + 2
    · exact ih u hu1 hle
    · push Not at hle
      set b : ℝ := (n : ℝ) + 2
      have hb2 : 2 ≤ b := by dsimp only [b]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hbu : b ≤ u := le_of_lt hle
      have heq := buchstab_integral_eq hω hb2 hbu
      have hwb : 0 ≤ ω b := ih b (by linarith) (le_refl b)
      have hint_nn : 0 ≤ ∫ s in (b - 1)..(u - 1), ω s := by
        apply intervalIntegral.integral_nonneg (by linarith)
        intro s hs
        exact ih s (by linarith [hs.1]) (by push_cast at hu2; linarith [hs.2])
      have hu_pos : 0 < u := by linarith
      have hmul : 0 ≤ u * ω u := by nlinarith
      exact nonneg_of_mul_nonneg_right hmul hu_pos

private lemma buchstab_nonneg {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    (u : ℝ) : 0 ≤ ω u := by
  by_cases h1 : u < 1
  · rw [hz u h1]
  · push Not at h1
    exact buchstab_nonneg_on_Icc hω (Nat.ceil u) u h1 (by linarith [Nat.le_ceil u])

private lemma integral_inv_le_trapezoid {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ s in a..b, (1 / s : ℝ) ≤ (b - a) / 2 * (1 / a + 1 / b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hcont1 : ContinuousOn (fun s : ℝ => 1 / s) (Icc a b) :=
    continuousOn_const.div continuousOn_id (fun s hs => ne_of_gt (lt_of_lt_of_le ha hs.1))
  have hcont2 : ContinuousOn (fun s : ℝ => (a + b - s) / (a * b)) (Icc a b) :=
    (continuousOn_const.sub continuousOn_id).div_const (a * b)
  have hmono : ∫ s in a..b, (1 / s : ℝ) ≤ ∫ s in a..b, (a + b - s) / (a * b) := by
    apply intervalIntegral.integral_mono_on hab
      (hcont1.intervalIntegrable_of_Icc hab) (hcont2.intervalIntegrable_of_Icc hab)
    intro s hs
    have hs_pos : 0 < s := lt_of_lt_of_le ha hs.1
    rw [div_le_div_iff₀ hs_pos (mul_pos ha hb)]
    nlinarith [hs.1, hs.2]
  have heval : ∫ s in a..b, (a + b - s) / (a * b) = (b - a) / 2 * (1 / a + 1 / b) := by
    have hderiv : ∀ x ∈ uIcc a b,
        HasDerivAt (fun s : ℝ => ((a + b) * s - s ^ 2 / 2) / (a * b)) ((a + b - x) / (a * b)) x := by
      intro x _
      have h1 : HasDerivAt (fun s : ℝ => (a + b) * s) (a + b) x := by
        simpa using (hasDerivAt_id x).const_mul (a + b)
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) x x := by
        simpa [mul_comm] using ((hasDerivAt_pow 2 x).div_const 2)
      exact (h1.sub h2).div_const (a * b)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont2.intervalIntegrable_of_Icc hab)]
    field_simp
    ring
  linarith

private lemma buchstab_max_propagate {ω : ℝ → ℝ} (hω : IsBuchstab ω) {a M : ℝ}
    (ha : 1 ≤ a) (hbase : ∀ u ∈ Icc a (a + 1), ω u ≤ M) :
    ∀ u : ℝ, a ≤ u → ω u ≤ M := by
  have hstep : ∀ n : ℕ, ∀ u ∈ Icc a (a + 1 + n), ω u ≤ M := by
    intro n
    induction n with
    | zero =>
      intro u hu
      exact hbase u (by simpa using hu)
    | succ n ih =>
      intro u hu
      by_cases hle : u ≤ a + 1 + n
      · exact ih u ⟨hu.1, hle⟩
      · push Not at hle
        set b : ℝ := a + 1 + n
        have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hb2 : 2 ≤ b := by dsimp only [b]; linarith
        have hbu : b ≤ u := le_of_lt hle
        have heq := buchstab_integral_eq hω hb2 hbu
        have hwb : ω b ≤ M := ih b ⟨by dsimp only [b]; linarith, le_refl b⟩
        have hcont_sub : ContinuousOn ω (Icc (b - 1) (u - 1)) :=
          hω.1.mono (fun s hs => by change 1 ≤ s; linarith [hs.1])
        have hint_le : ∫ s in (b - 1)..(u - 1), ω s ≤ (u - b) * M := by
          have h1 : ∫ s in (b - 1)..(u - 1), ω s ≤ ∫ _ in (b - 1)..(u - 1), M := by
            apply intervalIntegral.integral_mono_on (by linarith)
              (hcont_sub.intervalIntegrable_of_Icc (by linarith))
              intervalIntegrable_const
            intro s hs
            exact ih s ⟨by dsimp only [b] at hs; linarith [hs.1],
              by dsimp only [b]; push_cast at hu; linarith [hs.2, hu.2]⟩
          rw [intervalIntegral.integral_const, smul_eq_mul] at h1
          linarith
        have hu_pos : 0 < u := by linarith
        have hmul : u * ω u ≤ u * M := by nlinarith
        exact le_of_mul_le_mul_left hmul hu_pos
  intro u hu
  exact hstep (Nat.ceil (u - a)) u ⟨hu, by linarith [Nat.le_ceil (u - a)]⟩

private lemma buchstab_le_seven_twelfths {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : 2 ≤ u) : ω u ≤ 7 / 12 := by
  apply buchstab_max_propagate hω (a := 2) (M := 7 / 12) (by norm_num) _ u hu
  intro t ht
  have ht2 : 2 ≤ t := ht.1
  have ht3 : t ≤ 3 := by linarith [ht.2]
  have heq := buchstab_integral_eq hω (le_refl 2) ht2
  have hw2 : ω 2 = 1 / 2 := hω.2.1 2 (by norm_num) (by norm_num)
  have hint_eq : ∫ s in (2 - 1 : ℝ)..(t - 1), ω s = ∫ s in (1 : ℝ)..(t - 1), (1 / s : ℝ) := by
    have h1 : (2 - 1 : ℝ) = 1 := by norm_num
    rw [h1]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by linarith)] at hs
    exact hω.2.1 s hs.1 (by linarith [hs.2])
  have htrap := integral_inv_le_trapezoid (a := (1 : ℝ)) (b := t - 1) (by norm_num) (by linarith)
  have hsubt : t - 1 - 1 = t - 2 := by ring
  rw [hsubt] at htrap
  have ht_pos : 0 < t := by linarith
  have ht1_pos : 0 < t - 1 := by linarith
  have hle : t * ω t ≤ 1 + (t - 2) / 2 * (1 / 1 + 1 / (t - 1)) := by
    rw [hw2, hint_eq] at heq; linarith
  have hmul : (t - 1) * (t * ω t) ≤ (t - 1) * (t * (7 / 12)) := by
    have h1 : (t - 1) * (1 + (t - 2) / 2 * (1 / 1 + 1 / (t - 1))) = (t * t - 2) / 2 := by
      field_simp; ring
    have h2 : (t - 1) * (t * ω t) ≤ (t * t - 2) / 2 := by
      calc (t - 1) * (t * ω t)
          ≤ (t - 1) * (1 + (t - 2) / 2 * (1 / 1 + 1 / (t - 1))) :=
            mul_le_mul_of_nonneg_left hle (le_of_lt ht1_pos)
        _ = (t * t - 2) / 2 := h1
    have h3 : (t * t - 2) / 2 ≤ (t - 1) * (t * (7 / 12)) := by
      have hsq : 0 ≤ (3 - t) * (4 - t) := mul_nonneg (by linarith) (by linarith)
      linarith
    linarith
  have hmul2 : t * ω t ≤ t * (7 / 12) := le_of_mul_le_mul_left hmul ht1_pos
  exact le_of_mul_le_mul_left hmul2 ht_pos

private lemma buchstab_le_one {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    (u : ℝ) : ω u ≤ 1 := by
  by_cases h1 : u < 1
  · rw [hz u h1]; norm_num
  · push Not at h1
    by_cases h2 : u ≤ 2
    · rw [hω.2.1 u h1 h2]
      exact div_le_one_of_le₀ h1 (by linarith)
    · push Not at h2
      linarith [buchstab_le_seven_twelfths hω (le_of_lt h2)]

private lemma buchstab_le_max_inv {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {umin u : ℝ} (h1 : 1 ≤ umin) (hle : umin ≤ u) :
    ω u ≤ max (7 / 12 : ℝ) (1 / umin) := by
  by_cases h2 : u ≤ 2
  · rw [hω.2.1 u (le_trans h1 hle) h2]
    exact le_trans (one_div_le_one_div_of_le (by linarith) hle) (le_max_right _ _)
  · push Not at h2
    exact le_trans (buchstab_le_seven_twelfths hω (le_of_lt h2)) (le_max_left _ _)

/-! ### Part 3: 4D Geometry, Fubini, Joint Convexity, and Hermite-Hadamard on `Cell4` -/

abbrev R4 := ℝ × ℝ × ℝ × ℝ

private def gval (k : Nat) : ℝ := (k : ℝ) / D_grid

private lemma hDpos : (0 : ℝ) < D_grid := by unfold D_grid; positivity
private lemma hSpos : (0 : ℝ) < S_scale := by unfold S_scale; positivity

private lemma gval_le {a b : Nat} (h : a ≤ b) : gval a ≤ gval b :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) (le_of_lt hDpos)

private lemma gval_lt {a b : Nat} (h : a < b) : gval a < gval b :=
  div_lt_div_of_pos_right (by exact_mod_cast h) hDpos

private lemma gval_pos {a : Nat} (h : 0 < a) : 0 < gval a :=
  div_pos (by exact_mod_cast h) hDpos

private lemma gval_sub {a b : Nat} (h : a ≤ b) : gval b - gval a = ((b - a : Nat) : ℝ) / D_grid := by
  unfold gval
  rw [Nat.cast_sub h, sub_div]

private lemma gval_add (a b : Nat) : gval (a + b) = gval a + gval b := by
  unfold gval; push_cast; rw [add_div]

private lemma gval_2mul (a : Nat) : gval (2 * a) = 2 * gval a := by
  unfold gval; push_cast; ring

private lemma gval_3mul (a : Nat) : gval (3 * a) = 3 * gval a := by
  unfold gval; push_cast; ring

private lemma div_eq_one_add_sub_div {x l : ℝ} (hl : l ≠ 0) : x / l = 1 + (x - l) / l := by
  rw [sub_div, div_self hl]; ring

private lemma inv_u_div_weight {x0 x1 x2 x3 rem : ℝ} (hx2 : x2 ≠ 0) :
    (1 / (rem / x2)) / (x0 * x1 * x2 * x2 * x3) = 1 / (x0 * x1 * x2 * x3 * rem) := by
  rw [one_div_div, div_div, show rem * (x0 * x1 * x2 * x2 * x3) = x2 * (x0 * x1 * x2 * x3 * rem) by ring,
      show x2 / (x2 * (x0 * x1 * x2 * x3 * rem)) = (x2 * 1) / (x2 * (x0 * x1 * x2 * x3 * rem)) by rw [mul_one],
      mul_div_mul_left _ _ hx2]

private lemma weight_mul_vol {D x0 x1 x2 x3 v : ℝ} (hD : D ≠ 0) :
    (1 / ((x0 / D) * (x1 / D) * (x2 / D) * (x2 / D) * (x3 / D))) * (v / (48 * D ^ 4)) =
      (D * v) / (48 * x0 * x1 * x2 * x2 * x3) := by
  have hD4 : D ^ 4 ≠ 0 := pow_ne_zero 4 hD
  have hD5 : D ^ 5 ≠ 0 := pow_ne_zero 5 hD
  rw [show (x0 / D) * (x1 / D) * (x2 / D) * (x2 / D) * (x3 / D) = (x0 * x1 * x2 * x2 * x3) / D ^ 5 by ring,
      one_div_div, div_mul_div_comm,
      show D ^ 5 * v = D ^ 4 * (D * v) by ring,
      show x0 * x1 * x2 * x2 * x3 * (48 * D ^ 4) = D ^ 4 * (48 * x0 * x1 * x2 * x2 * x3) by ring,
      mul_div_mul_left _ _ hD4]

private lemma vertInt_alg {D v f x0 x1 x2 x3 rem : ℝ} (hD : D ≠ 0) :
    (v / D ^ 4) / f * (1 / ((x0 / D) * (x1 / D) * (x2 / D) * (x3 / D) * (rem / D))) =
      (D * v) / (f * x0 * x1 * x2 * x3 * rem) := by
  have hD4 : D ^ 4 ≠ 0 := pow_ne_zero 4 hD
  rw [div_div, show (x0 / D) * (x1 / D) * (x2 / D) * (x3 / D) * (rem / D) = (x0 * x1 * x2 * x3 * rem) / D ^ 5 by ring,
      one_div_div, div_mul_div_comm,
      show v * D ^ 5 = D ^ 4 * (D * v) by ring,
      show D ^ 4 * f * (x0 * x1 * x2 * x3 * rem) = D ^ 4 * (f * x0 * x1 * x2 * x3 * rem) by ring,
      mul_div_mul_left _ _ hD4]

private lemma vertW_alg {D nm dm v f x0 x1 x2 x3 : ℝ} (hD : D ≠ 0) :
    ((nm / dm) * ((v / D ^ 4) / f)) * (1 / ((x0 / D) * (x1 / D) * (x2 / D) * (x2 / D) * (x3 / D))) =
      (nm * D * v) / (dm * f * x0 * x1 * x2 * x2 * x3) := by
  have hD4 : D ^ 4 ≠ 0 := pow_ne_zero 4 hD
  rw [div_div, div_mul_div_comm,
      show (x0 / D) * (x1 / D) * (x2 / D) * (x2 / D) * (x3 / D) = (x0 * x1 * x2 * x2 * x3) / D ^ 5 by ring,
      one_div_div, div_mul_div_comm,
      show nm * v * D ^ 5 = D ^ 4 * (nm * D * v) by ring,
      show dm * (D ^ 4 * f) * (x0 * x1 * x2 * x2 * x3) = D ^ 4 * (dm * f * x0 * x1 * x2 * x2 * x3) by ring,
      mul_div_mul_left _ _ hD4]

private lemma canSplit_mid {a b : Nat} (h : canSplit a b = true) :
    a < (a + b) / 2 ∧ (a + b) / 2 < b := by
  unfold canSplit at h
  cases hb : Nat.ble 2 (b - a) with
  | false => simp [hb] at h
  | true =>
    simp only [hb, Nat.beq_eq] at h
    have h2 : 2 ≤ b - a := Nat.ble_eq.mp hb
    omega

private def Cell4.valid : Cell4 → Prop
  | .c4 a b => 0 < a ∧ a < b
  | .c31 a0 b0 a1 b1 => 0 < a0 ∧ a0 < b0 ∧ b0 ≤ a1 ∧ a1 < b1
  | .c13 a0 b0 a1 b1 => 0 < a0 ∧ a0 < b0 ∧ b0 ≤ a1 ∧ a1 < b1
  | .c22 a0 b0 a1 b1 => 0 < a0 ∧ a0 < b0 ∧ b0 ≤ a1 ∧ a1 < b1
  | .c211 a0 b0 a1 b1 a2 b2 => 0 < a0 ∧ a0 < b0 ∧ b0 ≤ a1 ∧ a1 < b1 ∧ b1 ≤ a2 ∧ a2 < b2
  | .c121 a0 b0 a1 b1 a2 b2 => 0 < a0 ∧ a0 < b0 ∧ b0 ≤ a1 ∧ a1 < b1 ∧ b1 ≤ a2 ∧ a2 < b2
  | .c112 a0 b0 a1 b1 a2 b2 => 0 < a0 ∧ a0 < b0 ∧ b0 ≤ a1 ∧ a1 < b1 ∧ b1 ≤ a2 ∧ a2 < b2
  | .c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
      0 < a0 ∧ a0 < b0 ∧ b0 ≤ a1 ∧ a1 < b1 ∧ b1 ≤ a2 ∧ a2 < b2 ∧ b2 ≤ a3 ∧ a3 < b3

private def Cell4.box : Cell4 → Set R4 := fun c =>
  let (l0, l1, l2, l3, u0, u1, u2, u3) := cellLoHi c
  Icc (gval l0) (gval u0) ×ˢ Icc (gval l1) (gval u1) ×ˢ Icc (gval l2) (gval u2) ×ˢ Icc (gval l3) (gval u3)

private def Cell4.set : Cell4 → Set R4
  | .c4 a b =>
      {x : R4 | gval a ≤ x.1 ∧ x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2.1 ∧ x.2.2.1 ≤ x.2.2.2 ∧ x.2.2.2 ≤ gval b}
  | .c31 a0 b0 a1 b1 =>
      {x : R4 | gval a0 ≤ x.1 ∧ x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2.1 ∧ x.2.2.1 ≤ gval b0 ∧
                gval a1 ≤ x.2.2.2 ∧ x.2.2.2 ≤ gval b1}
  | .c13 a0 b0 a1 b1 =>
      {x : R4 | gval a0 ≤ x.1 ∧ x.1 ≤ gval b0 ∧
                gval a1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2.1 ∧ x.2.2.1 ≤ x.2.2.2 ∧ x.2.2.2 ≤ gval b1}
  | .c22 a0 b0 a1 b1 =>
      {x : R4 | gval a0 ≤ x.1 ∧ x.1 ≤ x.2.1 ∧ x.2.1 ≤ gval b0 ∧
                gval a1 ≤ x.2.2.1 ∧ x.2.2.1 ≤ x.2.2.2 ∧ x.2.2.2 ≤ gval b1}
  | .c211 a0 b0 a1 b1 a2 b2 =>
      {x : R4 | gval a0 ≤ x.1 ∧ x.1 ≤ x.2.1 ∧ x.2.1 ≤ gval b0 ∧
                gval a1 ≤ x.2.2.1 ∧ x.2.2.1 ≤ gval b1 ∧ gval a2 ≤ x.2.2.2 ∧ x.2.2.2 ≤ gval b2}
  | .c121 a0 b0 a1 b1 a2 b2 =>
      {x : R4 | gval a0 ≤ x.1 ∧ x.1 ≤ gval b0 ∧
                gval a1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2.1 ∧ x.2.2.1 ≤ gval b1 ∧
                gval a2 ≤ x.2.2.2 ∧ x.2.2.2 ≤ gval b2}
  | .c112 a0 b0 a1 b1 a2 b2 =>
      {x : R4 | gval a0 ≤ x.1 ∧ x.1 ≤ gval b0 ∧ gval a1 ≤ x.2.1 ∧ x.2.1 ≤ gval b1 ∧
                gval a2 ≤ x.2.2.1 ∧ x.2.2.1 ≤ x.2.2.2 ∧ x.2.2.2 ≤ gval b2}
  | .c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
      {x : R4 | gval a0 ≤ x.1 ∧ x.1 ≤ gval b0 ∧ gval a1 ≤ x.2.1 ∧ x.2.1 ≤ gval b1 ∧
                gval a2 ≤ x.2.2.1 ∧ x.2.2.1 ≤ gval b2 ∧ gval a3 ≤ x.2.2.2 ∧ x.2.2.2 ≤ gval b3}

private lemma Cell4.set_subset_box (c : Cell4) : c.set ⊆ c.box := by
  cases c <;> intro x hx <;>
    simp only [Cell4.set, Cell4.box, cellLoHi, mem_ofPred_eq, mem_prod, mem_Icc] at hx ⊢ <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

private lemma Cell4.isClosed_set (c : Cell4) : IsClosed c.set := by
  have hc0 : Continuous (fun x : R4 => x.1) := continuous_fst
  have hc1 : Continuous (fun x : R4 => x.2.1) := continuous_fst.comp continuous_snd
  have hc2 : Continuous (fun x : R4 => x.2.2.1) := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hc3 : Continuous (fun x : R4 => x.2.2.2) := continuous_snd.comp (continuous_snd.comp continuous_snd)
  cases c <;> unfold Cell4.set <;>
    repeat first
      | apply IsClosed.inter
      | exact isClosed_le continuous_const hc0
      | exact isClosed_le hc0 continuous_const
      | exact isClosed_le continuous_const hc1
      | exact isClosed_le hc1 continuous_const
      | exact isClosed_le continuous_const hc2
      | exact isClosed_le hc2 continuous_const
      | exact isClosed_le continuous_const hc3
      | exact isClosed_le hc3 continuous_const
      | exact isClosed_le hc0 hc1
      | exact isClosed_le hc1 hc2
      | exact isClosed_le hc2 hc3

private lemma Cell4.isCompact_box (c : Cell4) : IsCompact c.box := by
  unfold Cell4.box
  exact isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

private lemma Cell4.isCompact_set (c : Cell4) : IsCompact c.set :=
  c.isCompact_box.of_isClosed_subset c.isClosed_set c.set_subset_box

private lemma Cell4.measurableSet_set (c : Cell4) : MeasurableSet c.set :=
  c.isClosed_set.measurableSet

private lemma Cell4.convex_box (c : Cell4) : Convex ℝ c.box := by
  unfold Cell4.box
  exact (convex_Icc _ _).prod ((convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _)))

private lemma Cell4.valid_bounds {c : Cell4} (hv : c.valid) :
    let (l0, l1, l2, l3, u0, u1, u2, u3) := cellLoHi c
    0 < l0 ∧ l0 < u0 ∧ l0 ≤ l1 ∧ l1 < u1 ∧ l1 ≤ l2 ∧ l2 < u2 ∧ l2 ≤ l3 ∧ l3 < u3 := by
  cases c <;> simp only [Cell4.valid, cellLoHi] at hv ⊢ <;> omega

private lemma setIntegral_union_le_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B : Set α} {f : α → ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hnnB : ∀ x ∈ B, 0 ≤ f x) (hintA : IntegrableOn f A μ) (hintB : IntegrableOn f B μ) :
    ∫ x in A ∪ B, f x ∂μ ≤ (∫ x in A, f x ∂μ) + (∫ x in B, f x ∂μ) := by
  have hAB : A ∪ B = A ∪ (B \ A) := (Set.union_sdiff_self).symm
  rw [hAB, setIntegral_union disjoint_sdiff_self_right (hB.diff hA) hintA
    (hintB.mono_set Set.sdiff_subset)]
  have hle : ∫ x in B \ A, f x ∂μ ≤ ∫ x in B, f x ∂μ :=
    setIntegral_mono_set hintB
      (ae_restrict_of_forall_mem hB hnnB)
      (Filter.Eventually.of_forall Set.sdiff_subset)
  linarith

private lemma setIntegral_le_of_subset_union2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {S A B : Set α} {f : α → ℝ}
    (hsub : S ⊆ A ∪ B) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hnnA : ∀ x ∈ A, 0 ≤ f x) (hnnB : ∀ x ∈ B, 0 ≤ f x)
    (hintA : IntegrableOn f A μ) (hintB : IntegrableOn f B μ) :
    ∫ x in S, f x ∂μ ≤ (∫ x in A, f x ∂μ) + (∫ x in B, f x ∂μ) := by
  have h1 : ∫ x in S, f x ∂μ ≤ ∫ x in A ∪ B, f x ∂μ := by
    apply setIntegral_mono_set (hintA.union hintB)
    · exact ae_restrict_of_forall_mem (hA.union hB) (fun x hx => hx.elim (hnnA x) (hnnB x))
    · exact Filter.Eventually.of_forall hsub
  exact le_trans h1 (setIntegral_union_le_of_nonneg hA hB hnnB hintA hintB)

private lemma setIntegral_le_of_subset_union3 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {S A B C : Set α} {f : α → ℝ}
    (hsub : S ⊆ A ∪ (B ∪ C)) (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hnnA : ∀ x ∈ A, 0 ≤ f x) (hnnB : ∀ x ∈ B, 0 ≤ f x) (hnnC : ∀ x ∈ C, 0 ≤ f x)
    (hintA : IntegrableOn f A μ) (hintB : IntegrableOn f B μ) (hintC : IntegrableOn f C μ) :
    ∫ x in S, f x ∂μ ≤ (∫ x in A, f x ∂μ) + (∫ x in B, f x ∂μ) + (∫ x in C, f x ∂μ) := by
  have hBC : MeasurableSet (B ∪ C) := hB.union hC
  have hnnBC : ∀ x ∈ B ∪ C, 0 ≤ f x := fun x hx => hx.elim (hnnB x) (hnnC x)
  have hintBC : IntegrableOn f (B ∪ C) μ := hintB.union hintC
  have h1 := setIntegral_le_of_subset_union2 hsub hA hBC hnnA hnnBC hintA hintBC
  have h2 := setIntegral_union_le_of_nonneg hB hC hnnC hintB hintC
  linarith

private lemma setIntegral_le_of_subset_union4 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {S A B C D : Set α} {f : α → ℝ}
    (hsub : S ⊆ A ∪ (B ∪ (C ∪ D)))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hnnA : ∀ x ∈ A, 0 ≤ f x) (hnnB : ∀ x ∈ B, 0 ≤ f x) (hnnC : ∀ x ∈ C, 0 ≤ f x) (hnnD : ∀ x ∈ D, 0 ≤ f x)
    (hintA : IntegrableOn f A μ) (hintB : IntegrableOn f B μ) (hintC : IntegrableOn f C μ) (hintD : IntegrableOn f D μ) :
    ∫ x in S, f x ∂μ ≤ (∫ x in A, f x ∂μ) + (∫ x in B, f x ∂μ) + (∫ x in C, f x ∂μ) + (∫ x in D, f x ∂μ) := by
  have hCD : MeasurableSet (C ∪ D) := hC.union hD
  have hnnCD : ∀ x ∈ C ∪ D, 0 ≤ f x := fun x hx => hx.elim (hnnC x) (hnnD x)
  have hintCD : IntegrableOn f (C ∪ D) μ := hintC.union hintD
  have h1 := setIntegral_le_of_subset_union3 hsub hA hB hCD hnnA hnnB hnnCD hintA hintB hintCD
  have h2 := setIntegral_union_le_of_nonneg hC hD hnnD hintC hintD
  linarith

private lemma setIntegral_le_of_subset_union5 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {S A B C D E : Set α} {f : α → ℝ}
    (hsub : S ⊆ A ∪ (B ∪ (C ∪ (D ∪ E))))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hnnA : ∀ x ∈ A, 0 ≤ f x) (hnnB : ∀ x ∈ B, 0 ≤ f x) (hnnC : ∀ x ∈ C, 0 ≤ f x) (hnnD : ∀ x ∈ D, 0 ≤ f x) (hnnE : ∀ x ∈ E, 0 ≤ f x)
    (hintA : IntegrableOn f A μ) (hintB : IntegrableOn f B μ) (hintC : IntegrableOn f C μ) (hintD : IntegrableOn f D μ) (hintE : IntegrableOn f E μ) :
    ∫ x in S, f x ∂μ ≤ (∫ x in A, f x ∂μ) + (∫ x in B, f x ∂μ) + (∫ x in C, f x ∂μ) + (∫ x in D, f x ∂μ) + (∫ x in E, f x ∂μ) := by
  have hDE : MeasurableSet (D ∪ E) := hD.union hE
  have hnnDE : ∀ x ∈ D ∪ E, 0 ≤ f x := fun x hx => hx.elim (hnnD x) (hnnE x)
  have hintDE : IntegrableOn f (D ∪ E) μ := hintD.union hintE
  have h1 := setIntegral_le_of_subset_union4 hsub hA hB hC hDE hnnA hnnB hnnC hnnDE hintA hintB hintC hintDE
  have h2 := setIntegral_union_le_of_nonneg hD hE hnnE hintD hintE
  linarith

/-! #### 1D-peeling Fubini -/

private lemma setIntegral_slice {β : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite ν]
    {a b : ℝ} (hab : a ≤ b) {T : ℝ → Set β} {f : ℝ × β → ℝ}
    (hT : ∀ x, MeasurableSet (T x))
    (hmeas : MeasurableSet {p : ℝ × β | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1})
    (hint : IntegrableOn f {p : ℝ × β | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1} (volume.prod ν)) :
    ∫ p in {p : ℝ × β | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1}, f p ∂(volume.prod ν) =
      ∫ x in a..b, ∫ y in T x, f (x, y) ∂ν := by
  rw [← integral_indicator hmeas]
  rw [MeasureTheory.integral_prod _ (hint.integrable_indicator hmeas)]
  have heq : (fun x => ∫ y, {p : ℝ × β | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1}.indicator f (x, y) ∂ν) =
      (Icc a b).indicator (fun x => ∫ y in T x, f (x, y) ∂ν) := by
    ext x
    by_cases hx : x ∈ Icc a b
    · simp only [indicator_of_mem hx]
      rw [← integral_indicator (hT x)]
      congr 1; ext y
      by_cases hy : y ∈ T x
      · rw [indicator_of_mem (show (x, y) ∈ {p : ℝ × β | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1} from ⟨hx, hy⟩),
            indicator_of_mem hy]
      · rw [indicator_of_notMem (fun h => hy h.2), indicator_of_notMem hy]
    · simp only [indicator_of_notMem hx]
      have h0 : ∀ y, {p : ℝ × β | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1}.indicator f (x, y) = 0 :=
        fun y => indicator_of_notMem (show (x, y) ∉ {p : ℝ × β | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1} from fun h => hx h.1) f
      simp only [h0, integral_zero]
  rw [heq, integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

private def cell4SetGen (l0 u0 l1 u1 l2 u2 l3 u3 : ℝ) (m01 m12 m23 : Bool) : Set R4 :=
  {x : R4 | x.1 ∈ Icc l0 u0 ∧
            x.2.1 ∈ Icc (if m01 then x.1 else l1) u1 ∧
            x.2.2.1 ∈ Icc (if m12 then x.2.1 else l2) u2 ∧
            x.2.2.2 ∈ Icc (if m23 then x.2.2.1 else l3) u3}

private lemma setIntegral_cell4SetGen {l0 u0 l1 u1 l2 u2 l3 u3 : ℝ} {m01 m12 m23 : Bool}
    (h0 : l0 ≤ u0) (h1 : l1 ≤ u1) (h2 : l2 ≤ u2) (h3 : l3 ≤ u3)
    (hm01 : m01 = true → l1 ≤ l0 ∧ u0 ≤ u1)
    (hm12 : m12 = true → l2 ≤ l1 ∧ u1 ≤ u2)
    (hm23 : m23 = true → l3 ≤ l2 ∧ u2 ≤ u3)
    {g : R4 → ℝ} (hg : Continuous g) :
    ∫ x in cell4SetGen l0 u0 l1 u1 l2 u2 l3 u3 m01 m12 m23, g x =
      ∫ x0 in l0..u0, ∫ x1 in (if m01 then x0 else l1)..u1,
        ∫ x2 in (if m12 then x1 else l2)..u2,
          ∫ x3 in (if m23 then x2 else l3)..u3, g (x0, x1, x2, x3) := by
  let S3 : ℝ → ℝ → ℝ → Set ℝ := fun x0 x1 x2 => Icc (if m23 then x2 else l3) u3
  let S2 : ℝ → ℝ → Set (ℝ × ℝ) := fun x0 x1 =>
    {p : ℝ × ℝ | p.1 ∈ Icc (if m12 then x1 else l2) u2 ∧ p.2 ∈ S3 x0 x1 p.1}
  let S1 : ℝ → Set (ℝ × ℝ × ℝ) := fun x0 =>
    {p : ℝ × ℝ × ℝ | p.1 ∈ Icc (if m01 then x0 else l1) u1 ∧ p.2 ∈ S2 x0 p.1}
  let S0 : Set R4 := {p : R4 | p.1 ∈ Icc l0 u0 ∧ p.2 ∈ S1 p.1}
  have hS3m : ∀ x0 x1 x2, MeasurableSet (S3 x0 x1 x2) := fun _ _ _ => measurableSet_Icc
  have hS2c : ∀ x0 x1, IsClosed (S2 x0 x1) := fun x0 x1 => by
    dsimp only [S2, S3]
    refine IsClosed.inter (IsClosed.inter (isClosed_le continuous_const continuous_fst)
      (isClosed_le continuous_fst continuous_const)) ?_
    refine IsClosed.inter ?_ (isClosed_le continuous_snd continuous_const)
    cases m23
    · exact isClosed_le continuous_const continuous_snd
    · exact isClosed_le continuous_fst continuous_snd
  have hS1c : ∀ x0, IsClosed (S1 x0) := fun x0 => by
    dsimp only [S1, S2, S3]
    refine IsClosed.inter (IsClosed.inter (isClosed_le continuous_const continuous_fst)
      (isClosed_le continuous_fst continuous_const)) ?_
    refine IsClosed.inter (IsClosed.inter ?_ (isClosed_le (continuous_fst.comp continuous_snd) continuous_const)) ?_
    · cases m12
      · exact isClosed_le continuous_const (continuous_fst.comp continuous_snd)
      · exact isClosed_le continuous_fst (continuous_fst.comp continuous_snd)
    · refine IsClosed.inter ?_ (isClosed_le (continuous_snd.comp continuous_snd) continuous_const)
      cases m23
      · exact isClosed_le continuous_const (continuous_snd.comp continuous_snd)
      · exact isClosed_le (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)
  have hS0c : IsClosed S0 := by
    dsimp only [S0, S1, S2, S3]
    refine IsClosed.inter (IsClosed.inter (isClosed_le continuous_const continuous_fst)
      (isClosed_le continuous_fst continuous_const)) ?_
    refine IsClosed.inter (IsClosed.inter ?_ (isClosed_le (continuous_fst.comp continuous_snd) continuous_const)) ?_
    · cases m01
      · exact isClosed_le continuous_const (continuous_fst.comp continuous_snd)
      · exact isClosed_le continuous_fst (continuous_fst.comp continuous_snd)
    · refine IsClosed.inter (IsClosed.inter ?_ (isClosed_le (continuous_fst.comp (continuous_snd.comp continuous_snd)) continuous_const)) ?_
      · cases m12
        · exact isClosed_le continuous_const (continuous_fst.comp (continuous_snd.comp continuous_snd))
        · exact isClosed_le (continuous_fst.comp continuous_snd) (continuous_fst.comp (continuous_snd.comp continuous_snd))
      · refine IsClosed.inter ?_ (isClosed_le (continuous_snd.comp (continuous_snd.comp continuous_snd)) continuous_const)
        cases m23
        · exact isClosed_le continuous_const (continuous_snd.comp (continuous_snd.comp continuous_snd))
        · exact isClosed_le (continuous_fst.comp (continuous_snd.comp continuous_snd)) (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hS0_sub : S0 ⊆ Icc l0 u0 ×ˢ Icc l1 u1 ×ˢ Icc l2 u2 ×ˢ Icc l3 u3 := by
    intro x hx
    simp only [S0, S1, S2, S3, mem_ofPred_eq, mem_Icc, mem_prod] at hx ⊢
    rcases hx with ⟨⟨hx0a, hx0b⟩, ⟨hx1a, hx1b⟩, ⟨hx2a, hx2b⟩, ⟨hx3a, hx3b⟩⟩
    have hl1 : l1 ≤ x.2.1 := by cases m01 <;> simp at hx1a; linarith; linarith [(hm01 rfl).1]
    have hl2 : l2 ≤ x.2.2.1 := by cases m12 <;> simp at hx2a; linarith; linarith [(hm12 rfl).1]
    have hl3 : l3 ≤ x.2.2.2 := by cases m23 <;> simp at hx3a; linarith; linarith [(hm23 rfl).1]
    exact ⟨⟨hx0a, hx0b⟩, ⟨hl1, hx1b⟩, ⟨hl2, hx2b⟩, ⟨hl3, hx3b⟩⟩
  have hS0_comp : IsCompact S0 :=
    (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))).of_isClosed_subset hS0c hS0_sub
  have heq0 : cell4SetGen l0 u0 l1 u1 l2 u2 l3 u3 m01 m12 m23 = {p : R4 | p.1 ∈ Icc l0 u0 ∧ p.2 ∈ S1 p.1} := rfl
  rw [heq0]
  rw [show ∫ p in {p : R4 | p.1 ∈ Icc l0 u0 ∧ p.2 ∈ S1 p.1}, g p =
        ∫ x0 in l0..u0, ∫ y in S1 x0, g (x0, y) from
      setIntegral_slice h0 (fun x0 => (hS1c x0).measurableSet) hS0c.measurableSet
        (hg.continuousOn.integrableOn_compact hS0_comp)]
  apply intervalIntegral.integral_congr
  intro x0 hx0
  dsimp only
  rw [uIcc_of_le h0] at hx0
  have h1' : (if m01 then x0 else l1) ≤ u1 := by
    cases m01 with | false => simpa using h1 | true => simpa using le_trans hx0.2 (hm01 rfl).2
  have hS1_sub : S1 x0 ⊆ Icc l1 u1 ×ˢ Icc l2 u2 ×ˢ Icc l3 u3 := by
    intro y hy; exact (hS0_sub (show (x0, y) ∈ S0 from ⟨hx0, hy⟩)).2
  have hS1_comp : IsCompact (S1 x0) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset (hS1c x0) hS1_sub
  have hg1 : Continuous (fun y : ℝ × ℝ × ℝ => g (x0, y)) := hg.comp (continuous_const.prodMk continuous_id)
  rw [show ∫ y in S1 x0, g (x0, y) = ∫ x1 in (if m01 then x0 else l1)..u1, ∫ z in S2 x0 x1, g (x0, x1, z) from
      setIntegral_slice h1' (fun x1 => (hS2c x0 x1).measurableSet) (hS1c x0).measurableSet
        (hg1.continuousOn.integrableOn_compact hS1_comp)]
  apply intervalIntegral.integral_congr
  intro x1 hx1
  dsimp only
  rw [uIcc_of_le h1'] at hx1
  have h2' : (if m12 then x1 else l2) ≤ u2 := by
    cases m12 with | false => simpa using h2 | true => simpa using le_trans hx1.2 (hm12 rfl).2
  have hS2_sub : S2 x0 x1 ⊆ Icc l2 u2 ×ˢ Icc l3 u3 := by
    intro z hz; exact (hS1_sub (show (x1, z) ∈ S1 x0 from ⟨hx1, hz⟩)).2
  have hS2_comp : IsCompact (S2 x0 x1) :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (hS2c x0 x1) hS2_sub
  have hg2 : Continuous (fun z : ℝ × ℝ => g (x0, x1, z)) :=
    hg.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  rw [show ∫ z in S2 x0 x1, g (x0, x1, z) = ∫ x2 in (if m12 then x1 else l2)..u2, ∫ x3 in S3 x0 x1 x2, g (x0, x1, x2, x3) from
      setIntegral_slice h2' (fun x2 => hS3m x0 x1 x2) (hS2c x0 x1).measurableSet
        (hg2.continuousOn.integrableOn_compact hS2_comp)]
  apply intervalIntegral.integral_congr
  intro x2 hx2
  dsimp only
  rw [uIcc_of_le h2'] at hx2
  have h3' : (if m23 then x2 else l3) ≤ u3 := by
    cases m23 with | false => simpa using h3 | true => simpa using le_trans hx2.2 (hm23 rfl).2
  dsimp only [S3]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h3']

/-! #### Elementary Polynomial Integrals for Simplex Weights & Volumes -/

private lemma integral_sub_pow {a b : ℝ} (n : ℕ) :
    ∫ t in a..b, (b - t) ^ n = (b - a) ^ (n + 1) / (n + 1) := by
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun t => -((b - t) ^ (n + 1)) / ((n : ℝ) + 1)) ((b - x) ^ n) x := by
    intro x _
    have h1 : HasDerivAt (fun t => b - t) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub b
    have h2 : HasDerivAt (fun t => -((b - t) ^ (n + 1)) / ((n : ℝ) + 1))
        (-(((n + 1 : ℕ) : ℝ) * (b - x) ^ (n + 1 - 1) * (-1)) / ((n : ℝ) + 1)) x :=
      ((h1.pow (n + 1)).neg).div_const ((n : ℝ) + 1)
    have heq : -(((n + 1 : ℕ) : ℝ) * (b - x) ^ (n + 1 - 1) * (-1)) / ((n : ℝ) + 1) = (b - x) ^ n := by
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      field_simp [hn]
    rwa [heq] at h2
  have hcont : ContinuousOn (fun t : ℝ => (b - t) ^ n) (uIcc a b) :=
    ((continuous_const.sub continuous_id).pow n).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp; ring

private lemma integral_sub_mul_pow {a b : ℝ} (n : ℕ) :
    ∫ t in a..b, (t - a) * (b - t) ^ n = (b - a) ^ (n + 2) / ((n + 1) * (n + 2)) := by
  have heq : ∀ t : ℝ, (t - a) * (b - t) ^ n = (b - a) * (b - t) ^ n - (b - t) ^ (n + 1) := by
    intro t; ring
  simp_rw [heq]
  have hc1 : IntervalIntegrable (fun t => (b - a) * (b - t) ^ n) volume a b :=
    (continuous_const.mul ((continuous_const.sub continuous_id).pow n)).intervalIntegrable a b
  have hc2 : IntervalIntegrable (fun t => (b - t) ^ (n + 1)) volume a b :=
    ((continuous_const.sub continuous_id).pow (n + 1)).intervalIntegrable a b
  rw [intervalIntegral.integral_sub hc1 hc2, intervalIntegral.integral_const_mul,
      integral_sub_pow n, integral_sub_pow (n + 1)]
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  push_cast; field_simp [hn1, hn2]; ring

private lemma iter1_w0 {a b : ℝ} : ∫ x in a..b, (b - x) = (b - a) ^ 2 / 2 := by
  have h := integral_sub_pow (a := a) (b := b) 1
  simp only [pow_one] at h; rw [h]; norm_num

private lemma iter1_w1 {a b : ℝ} : ∫ x in a..b, (x - a) = (b - a) ^ 2 / 2 := by
  have h := integral_sub_mul_pow (a := a) (b := b) 0
  simp only [pow_zero, mul_one] at h; rw [h]; norm_num

private lemma iter1_c {a b : ℝ} : ∫ _ in a..b, (1 : ℝ) = b - a := by simp

private lemma iter2_w0 {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, (b - x1) = (b - a) ^ 3 / 6 := by
  simp_rw [iter1_w0, div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_sub_pow 2]; ring

private lemma iter2_w1 {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, (x1 - x0) = (b - a) ^ 3 / 6 := by
  simp_rw [iter1_w1, div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_sub_pow 2]; ring

private lemma iter2_w2 {a b : ℝ} :
    ∫ x0 in a..b, ∫ _ in x0..b, (x0 - a) = (b - a) ^ 3 / 6 := by
  simp_rw [intervalIntegral.integral_const, smul_eq_mul]
  have heq : (fun x0 : ℝ => (b - x0) * (x0 - a)) = (fun x0 : ℝ => (x0 - a) * (b - x0) ^ 1) := by
    ext; ring
  rw [heq, integral_sub_mul_pow 1]; ring

private lemma iter2_c {a b : ℝ} :
    ∫ x0 in a..b, ∫ _ in x0..b, (1 : ℝ) = (b - a) ^ 2 / 2 := by
  simp_rw [iter1_c]; exact iter1_w0

private lemma iter3_w0 {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ x2 in x1..b, (b - x2) = (b - a) ^ 4 / 24 := by
  simp_rw [iter2_w0, div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_sub_pow 3]; ring

private lemma iter3_w1 {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ x2 in x1..b, (x2 - x1) = (b - a) ^ 4 / 24 := by
  simp_rw [iter2_w1, div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_sub_pow 3]; ring

private lemma iter3_w2 {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ _ in x1..b, (x1 - x0) = (b - a) ^ 4 / 24 := by
  simp_rw [iter2_w2, div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_sub_pow 3]; ring

private lemma iter3_w3 {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ _ in x1..b, (x0 - a) = (b - a) ^ 4 / 24 := by
  have h1 : ∀ x0 : ℝ, ∫ x1 in x0..b, ∫ _ in x1..b, (x0 - a) = (x0 - a) * ((b - x0) ^ 2 / 2) := by
    intro x0
    simp_rw [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_mul_const, iter1_w0]
    ring
  simp_rw [h1]
  have heq : (fun x0 : ℝ => (x0 - a) * ((b - x0) ^ 2 / 2)) =
      (fun x0 => (1 / 2 : ℝ) * ((x0 - a) * (b - x0) ^ 2)) := by ext; ring
  rw [heq, intervalIntegral.integral_const_mul, integral_sub_mul_pow 2]; ring

private lemma iter3_c {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ _ in x1..b, (1 : ℝ) = (b - a) ^ 3 / 6 := by
  simp_rw [iter2_c, div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_sub_pow 2]; ring

private lemma iter4_w0 {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ x2 in x1..b, ∫ x3 in x2..b, (b - x3) = (b - a) ^ 5 / 120 := by
  simp_rw [iter3_w0, div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_sub_pow 4]; ring

private lemma iter4_w1 {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ x2 in x1..b, ∫ x3 in x2..b, (x3 - x2) = (b - a) ^ 5 / 120 := by
  simp_rw [iter3_w1, div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_sub_pow 4]; ring

private lemma iter4_w2 {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ x2 in x1..b, ∫ _ in x2..b, (x2 - x1) = (b - a) ^ 5 / 120 := by
  simp_rw [iter3_w2, div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_sub_pow 4]; ring

private lemma iter4_w3 {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ x2 in x1..b, ∫ _ in x2..b, (x1 - x0) = (b - a) ^ 5 / 120 := by
  simp_rw [iter3_w3, div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_sub_pow 4]; ring

private lemma iter4_w4 {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ x2 in x1..b, ∫ _ in x2..b, (x0 - a) = (b - a) ^ 5 / 120 := by
  have h1 : ∀ x0 : ℝ, ∫ x1 in x0..b, ∫ x2 in x1..b, ∫ _ in x2..b, (x0 - a) = (x0 - a) * ((b - x0) ^ 3 / 6) := by
    intro x0
    have heq : ∀ x2 : ℝ, ∫ _ in x2..b, (x0 - a) = (x0 - a) * (∫ _ in x2..b, (1 : ℝ)) := by
      intro x2; simp; ring
    simp_rw [heq]; simp_rw [intervalIntegral.integral_const_mul]; rw [iter3_c]
  simp_rw [h1]
  have heq : (fun x0 : ℝ => (x0 - a) * ((b - x0) ^ 3 / 6)) =
      (fun x0 => (1 / 6 : ℝ) * ((x0 - a) * (b - x0) ^ 3)) := by ext; ring
  rw [heq, intervalIntegral.integral_const_mul, integral_sub_mul_pow 3]; ring

private lemma iter4_c {a b : ℝ} :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ x2 in x1..b, ∫ _ in x2..b, (1 : ℝ) = (b - a) ^ 4 / 24 := by
  simp_rw [iter3_c, div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_sub_pow 3]; ring

/-! #### Simplex Barycentric Weights & Cell Volumes -/

private def w1 (a b : ℝ) : Bool → ℝ → ℝ
  | false, x => (b - x) / (b - a)
  | true,  x => (x - a) / (b - a)

private def v1 (a b : ℝ) : Bool → ℝ
  | false => a
  | true  => b

private def w2 (a b : ℝ) : Fin 3 → ℝ → ℝ → ℝ
  | ⟨0, _⟩, _, x1 => (b - x1) / (b - a)
  | ⟨1, _⟩, x0, x1 => (x1 - x0) / (b - a)
  | ⟨2, _⟩, x0, _ => (x0 - a) / (b - a)

private def v2 (a b : ℝ) : Fin 3 → ℝ × ℝ
  | ⟨0, _⟩ => (a, a)
  | ⟨1, _⟩ => (a, b)
  | ⟨2, _⟩ => (b, b)

private def w3 (a b : ℝ) : Fin 4 → ℝ → ℝ → ℝ → ℝ
  | ⟨0, _⟩, _, _, x2 => (b - x2) / (b - a)
  | ⟨1, _⟩, _, x1, x2 => (x2 - x1) / (b - a)
  | ⟨2, _⟩, x0, x1, _ => (x1 - x0) / (b - a)
  | ⟨3, _⟩, x0, _, _ => (x0 - a) / (b - a)

private def v3 (a b : ℝ) : Fin 4 → ℝ × ℝ × ℝ
  | ⟨0, _⟩ => (a, a, a)
  | ⟨1, _⟩ => (a, a, b)
  | ⟨2, _⟩ => (a, b, b)
  | ⟨3, _⟩ => (b, b, b)

private def w4 (a b : ℝ) : Fin 5 → ℝ → ℝ → ℝ → ℝ → ℝ
  | ⟨0, _⟩, _, _, _, x3 => (b - x3) / (b - a)
  | ⟨1, _⟩, _, _, x2, x3 => (x3 - x2) / (b - a)
  | ⟨2, _⟩, _, x1, x2, _ => (x2 - x1) / (b - a)
  | ⟨3, _⟩, x0, x1, _, _ => (x1 - x0) / (b - a)
  | ⟨4, _⟩, x0, _, _, _ => (x0 - a) / (b - a)

private def v4 (a b : ℝ) : Fin 5 → R4
  | ⟨0, _⟩ => (a, a, a, a)
  | ⟨1, _⟩ => (a, a, a, b)
  | ⟨2, _⟩ => (a, a, b, b)
  | ⟨3, _⟩ => (a, b, b, b)
  | ⟨4, _⟩ => (b, b, b, b)

private lemma pow_div_const_mul_inv {x c : ℝ} (hx : x ≠ 0) (n : ℕ) :
    x ^ (n + 1) / c * x⁻¹ = x ^ n * c⁻¹ := by
  rw [← div_eq_mul_inv, div_right_comm, pow_succ, mul_div_cancel_right₀ _ hx, div_eq_mul_inv]

private lemma iter_w1 {a b : ℝ} (hab : a < b) (e : Bool) :
    ∫ x in a..b, w1 a b e x = (b - a) / 2 := by
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  cases e <;> simp only [w1, div_eq_mul_inv, intervalIntegral.integral_mul_const]
  · rw [iter1_w0, pow_div_const_mul_inv hba 1, pow_one]
  · rw [iter1_w1, pow_div_const_mul_inv hba 1, pow_one]

private lemma iter_w2 {a b : ℝ} (hab : a < b) (i : Fin 3) :
    ∫ x0 in a..b, ∫ x1 in x0..b, w2 a b i x0 x1 = (b - a) ^ 2 / 6 := by
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  fin_cases i <;> simp only [w2, div_eq_mul_inv, intervalIntegral.integral_mul_const]
  · rw [iter2_w0, pow_div_const_mul_inv hba 2]
  · rw [iter2_w1, pow_div_const_mul_inv hba 2]
  · rw [iter2_w2, pow_div_const_mul_inv hba 2]

private lemma iter_w3 {a b : ℝ} (hab : a < b) (i : Fin 4) :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ x2 in x1..b, w3 a b i x0 x1 x2 = (b - a) ^ 3 / 24 := by
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  fin_cases i <;> simp only [w3, div_eq_mul_inv, intervalIntegral.integral_mul_const]
  · rw [iter3_w0, pow_div_const_mul_inv hba 3]
  · rw [iter3_w1, pow_div_const_mul_inv hba 3]
  · rw [iter3_w2, pow_div_const_mul_inv hba 3]
  · rw [iter3_w3, pow_div_const_mul_inv hba 3]

private lemma iter_w4 {a b : ℝ} (hab : a < b) (i : Fin 5) :
    ∫ x0 in a..b, ∫ x1 in x0..b, ∫ x2 in x1..b, ∫ x3 in x2..b, w4 a b i x0 x1 x2 x3 = (b - a) ^ 4 / 120 := by
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  fin_cases i <;> simp only [w4, div_eq_mul_inv, intervalIntegral.integral_mul_const]
  · rw [iter4_w0, pow_div_const_mul_inv hba 4]
  · rw [iter4_w1, pow_div_const_mul_inv hba 4]
  · rw [iter4_w2, pow_div_const_mul_inv hba 4]
  · rw [iter4_w3, pow_div_const_mul_inv hba 4]
  · rw [iter4_w4, pow_div_const_mul_inv hba 4]

private lemma c4_set_eq (a b : Nat) :
    (Cell4.c4 a b).set = cell4SetGen (gval a) (gval b) (gval a) (gval b) (gval a) (gval b) (gval a) (gval b) true true true := by
  ext x; simp only [Cell4.set, cell4SetGen, mem_ofPred_eq, mem_Icc, ↓reduceIte]
  exact ⟨fun ⟨h0, h01, h12, h23, h3⟩ => ⟨⟨h0, by linarith⟩, ⟨h01, by linarith⟩, ⟨h12, by linarith⟩, ⟨h23, h3⟩⟩,
    fun ⟨⟨h0, _⟩, ⟨h01, _⟩, ⟨h12, _⟩, ⟨h23, h3⟩⟩ => ⟨h0, h01, h12, h23, h3⟩⟩

private lemma c31_set_eq (a0 b0 a1 b1 : Nat) :
    (Cell4.c31 a0 b0 a1 b1).set = cell4SetGen (gval a0) (gval b0) (gval a0) (gval b0) (gval a0) (gval b0) (gval a1) (gval b1) true true false := by
  ext x; simp only [Cell4.set, cell4SetGen, mem_ofPred_eq, mem_Icc, ↓reduceIte, Bool.false_eq_true]
  exact ⟨fun ⟨h0, h01, h12, h2, h3a, h3b⟩ => ⟨⟨h0, by linarith⟩, ⟨h01, by linarith⟩, ⟨h12, h2⟩, ⟨h3a, h3b⟩⟩,
    fun ⟨⟨h0, _⟩, ⟨h01, _⟩, ⟨h12, h2⟩, ⟨h3a, h3b⟩⟩ => ⟨h0, h01, h12, h2, h3a, h3b⟩⟩

private lemma c13_set_eq (a0 b0 a1 b1 : Nat) :
    (Cell4.c13 a0 b0 a1 b1).set = cell4SetGen (gval a0) (gval b0) (gval a1) (gval b1) (gval a1) (gval b1) (gval a1) (gval b1) false true true := by
  ext x; simp only [Cell4.set, cell4SetGen, mem_ofPred_eq, mem_Icc, ↓reduceIte, Bool.false_eq_true]
  exact ⟨fun ⟨h0a, h0b, h1, h12, h23, h3⟩ => ⟨⟨h0a, h0b⟩, ⟨h1, by linarith⟩, ⟨h12, by linarith⟩, ⟨h23, h3⟩⟩,
    fun ⟨⟨h0a, h0b⟩, ⟨h1, _⟩, ⟨h12, _⟩, ⟨h23, h3⟩⟩ => ⟨h0a, h0b, h1, h12, h23, h3⟩⟩

private lemma c22_set_eq (a0 b0 a1 b1 : Nat) :
    (Cell4.c22 a0 b0 a1 b1).set = cell4SetGen (gval a0) (gval b0) (gval a0) (gval b0) (gval a1) (gval b1) (gval a1) (gval b1) true false true := by
  ext x; simp only [Cell4.set, cell4SetGen, mem_ofPred_eq, mem_Icc, ↓reduceIte, Bool.false_eq_true]
  exact ⟨fun ⟨h0, h01, h1, h2, h23, h3⟩ => ⟨⟨h0, by linarith⟩, ⟨h01, h1⟩, ⟨h2, by linarith⟩, ⟨h23, h3⟩⟩,
    fun ⟨⟨h0, _⟩, ⟨h01, h1⟩, ⟨h2, _⟩, ⟨h23, h3⟩⟩ => ⟨h0, h01, h1, h2, h23, h3⟩⟩

private lemma c211_set_eq (a0 b0 a1 b1 a2 b2 : Nat) :
    (Cell4.c211 a0 b0 a1 b1 a2 b2).set = cell4SetGen (gval a0) (gval b0) (gval a0) (gval b0) (gval a1) (gval b1) (gval a2) (gval b2) true false false := by
  ext x; simp only [Cell4.set, cell4SetGen, mem_ofPred_eq, mem_Icc, ↓reduceIte, Bool.false_eq_true]
  exact ⟨fun ⟨h0, h01, h1, h2a, h2b, h3a, h3b⟩ => ⟨⟨h0, by linarith⟩, ⟨h01, h1⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩,
    fun ⟨⟨h0, _⟩, ⟨h01, h1⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ => ⟨h0, h01, h1, h2a, h2b, h3a, h3b⟩⟩

private lemma c121_set_eq (a0 b0 a1 b1 a2 b2 : Nat) :
    (Cell4.c121 a0 b0 a1 b1 a2 b2).set = cell4SetGen (gval a0) (gval b0) (gval a1) (gval b1) (gval a1) (gval b1) (gval a2) (gval b2) false true false := by
  ext x; simp only [Cell4.set, cell4SetGen, mem_ofPred_eq, mem_Icc, ↓reduceIte, Bool.false_eq_true]
  exact ⟨fun ⟨h0a, h0b, h1, h12, h2, h3a, h3b⟩ => ⟨⟨h0a, h0b⟩, ⟨h1, by linarith⟩, ⟨h12, h2⟩, ⟨h3a, h3b⟩⟩,
    fun ⟨⟨h0a, h0b⟩, ⟨h1, _⟩, ⟨h12, h2⟩, ⟨h3a, h3b⟩⟩ => ⟨h0a, h0b, h1, h12, h2, h3a, h3b⟩⟩

private lemma c112_set_eq (a0 b0 a1 b1 a2 b2 : Nat) :
    (Cell4.c112 a0 b0 a1 b1 a2 b2).set = cell4SetGen (gval a0) (gval b0) (gval a1) (gval b1) (gval a2) (gval b2) (gval a2) (gval b2) false false true := by
  ext x; simp only [Cell4.set, cell4SetGen, mem_ofPred_eq, mem_Icc, ↓reduceIte, Bool.false_eq_true]
  exact ⟨fun ⟨h0a, h0b, h1a, h1b, h2, h23, h3⟩ => ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩, ⟨h2, by linarith⟩, ⟨h23, h3⟩⟩,
    fun ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩, ⟨h2, _⟩, ⟨h23, h3⟩⟩ => ⟨h0a, h0b, h1a, h1b, h2, h23, h3⟩⟩

private lemma c1111_set_eq (a0 b0 a1 b1 a2 b2 a3 b3 : Nat) :
    (Cell4.c1111 a0 b0 a1 b1 a2 b2 a3 b3).set = cell4SetGen (gval a0) (gval b0) (gval a1) (gval b1) (gval a2) (gval b2) (gval a3) (gval b3) false false false := by
  ext x; simp only [Cell4.set, cell4SetGen, mem_ofPred_eq, mem_Icc, ↓reduceIte, Bool.false_eq_true]
  exact ⟨fun ⟨h0a, h0b, h1a, h1b, h2a, h2b, h3a, h3b⟩ => ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩,
    fun ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ => ⟨h0a, h0b, h1a, h1b, h2a, h2b, h3a, h3b⟩⟩

private lemma cell4_vol_eq {c : Cell4} (hv : c.valid) :
    ∫ _ in c.set, (1 : ℝ) = ((cellVol48 c : Nat) : ℝ) / (48 * (D_grid : ℝ) ^ 4) := by
  cases c with
  | c4 a b =>
    rcases hv with ⟨_, hab⟩
    rw [c4_set_eq, setIntegral_cell4SetGen (gval_le (le_of_lt hab)) (gval_le (le_of_lt hab))
      (gval_le (le_of_lt hab)) (gval_le (le_of_lt hab)) (fun _ => ⟨le_refl _, le_refl _⟩)
      (fun _ => ⟨le_refl _, le_refl _⟩) (fun _ => ⟨le_refl _, le_refl _⟩) continuous_const]
    simp only [↓reduceIte, iter4_c, cellVol48, gval_sub (le_of_lt hab)]
    push_cast; ring
  | c31 a0 b0 a1 b1 =>
    rcases hv with ⟨_, h0, _, h1⟩
    rw [c31_set_eq, setIntegral_cell4SetGen (gval_le (le_of_lt h0)) (gval_le (le_of_lt h0))
      (gval_le (le_of_lt h0)) (gval_le (le_of_lt h1)) (fun _ => ⟨le_refl _, le_refl _⟩)
      (fun _ => ⟨le_refl _, le_refl _⟩) (by simp) continuous_const]
    simp only [↓reduceIte, Bool.false_eq_true, iter1_c]
    have hmul : ∀ x0 : ℝ, ∫ x1 in x0..gval b0, ∫ _ in x1..gval b0, (gval b1 - gval a1) =
        (gval b1 - gval a1) * ∫ x1 in x0..gval b0, ∫ _ in x1..gval b0, (1 : ℝ) := by
      intro x0
      have h' : ∀ x1 : ℝ, ∫ _ in x1..gval b0, (gval b1 - gval a1) = (gval b1 - gval a1) * ∫ _ in x1..gval b0, (1 : ℝ) := by
        intro x1; simp; ring
      simp_rw [h', intervalIntegral.integral_const_mul]
    simp_rw [hmul, intervalIntegral.integral_const_mul, iter3_c, cellVol48, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1)]
    push_cast; ring
  | c13 a0 b0 a1 b1 =>
    rcases hv with ⟨_, h0, _, h1⟩
    rw [c13_set_eq, setIntegral_cell4SetGen (gval_le (le_of_lt h0)) (gval_le (le_of_lt h1))
      (gval_le (le_of_lt h1)) (gval_le (le_of_lt h1)) (by simp) (fun _ => ⟨le_refl _, le_refl _⟩)
      (fun _ => ⟨le_refl _, le_refl _⟩) continuous_const]
    simp only [↓reduceIte, Bool.false_eq_true, iter3_c]
    simp only [intervalIntegral.integral_const, smul_eq_mul,
      cellVol48, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1)]
    push_cast; ring
  | c22 a0 b0 a1 b1 =>
    rcases hv with ⟨_, h0, _, h1⟩
    rw [c22_set_eq, setIntegral_cell4SetGen (gval_le (le_of_lt h0)) (gval_le (le_of_lt h0))
      (gval_le (le_of_lt h1)) (gval_le (le_of_lt h1)) (fun _ => ⟨le_refl _, le_refl _⟩) (by simp)
      (fun _ => ⟨le_refl _, le_refl _⟩) continuous_const]
    simp only [↓reduceIte, Bool.false_eq_true, iter2_c]
    have hmul : ∀ x0 : ℝ, ∫ _ in x0..gval b0, ((gval b1 - gval a1) ^ 2 / 2) =
        ((gval b1 - gval a1) ^ 2 / 2) * ∫ _ in x0..gval b0, (1 : ℝ) := by
      intro x0; simp; ring
    simp_rw [hmul, intervalIntegral.integral_const_mul, iter2_c, cellVol48, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1)]
    push_cast; ring
  | c211 a0 b0 a1 b1 a2 b2 =>
    rcases hv with ⟨_, h0, _, h1, _, h2⟩
    rw [c211_set_eq, setIntegral_cell4SetGen (gval_le (le_of_lt h0)) (gval_le (le_of_lt h0))
      (gval_le (le_of_lt h1)) (gval_le (le_of_lt h2)) (fun _ => ⟨le_refl _, le_refl _⟩) (by simp)
      (by simp) continuous_const]
    simp only [↓reduceIte, Bool.false_eq_true, intervalIntegral.integral_const, smul_eq_mul]
    simp_rw [intervalIntegral.integral_mul_const, iter1_w0, cellVol48,
      gval_sub (le_of_lt h0), gval_sub (le_of_lt h1), gval_sub (le_of_lt h2)]
    push_cast; ring
  | c121 a0 b0 a1 b1 a2 b2 =>
    rcases hv with ⟨_, h0, _, h1, _, h2⟩
    rw [c121_set_eq, setIntegral_cell4SetGen (gval_le (le_of_lt h0)) (gval_le (le_of_lt h1))
      (gval_le (le_of_lt h1)) (gval_le (le_of_lt h2)) (by simp) (fun _ => ⟨le_refl _, le_refl _⟩)
      (by simp) continuous_const]
    simp only [↓reduceIte, Bool.false_eq_true, intervalIntegral.integral_const, smul_eq_mul]
    simp_rw [intervalIntegral.integral_mul_const, iter1_w0, cellVol48,
      gval_sub (le_of_lt h0), gval_sub (le_of_lt h1), gval_sub (le_of_lt h2)]
    push_cast; ring
  | c112 a0 b0 a1 b1 a2 b2 =>
    rcases hv with ⟨_, h0, _, h1, _, h2⟩
    rw [c112_set_eq, setIntegral_cell4SetGen (gval_le (le_of_lt h0)) (gval_le (le_of_lt h1))
      (gval_le (le_of_lt h2)) (gval_le (le_of_lt h2)) (by simp) (by simp)
      (fun _ => ⟨le_refl _, le_refl _⟩) continuous_const]
    simp only [↓reduceIte, Bool.false_eq_true, iter2_c]
    simp only [intervalIntegral.integral_const, smul_eq_mul,
      cellVol48, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1), gval_sub (le_of_lt h2)]
    push_cast; ring
  | c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
    rcases hv with ⟨_, h0, _, h1, _, h2, _, h3⟩
    rw [c1111_set_eq, setIntegral_cell4SetGen (gval_le (le_of_lt h0)) (gval_le (le_of_lt h1))
      (gval_le (le_of_lt h2)) (gval_le (le_of_lt h3)) (by simp) (by simp) (by simp) continuous_const]
    simp only [↓reduceIte, Bool.false_eq_true, intervalIntegral.integral_const, smul_eq_mul,
      cellVol48, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1), gval_sub (le_of_lt h2), gval_sub (le_of_lt h3)]
    push_cast; ring

/-! #### Joint Convexity of Interior Integrand & Weight Function -/

private lemma convex_bary3 {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {f : E → ℝ} (hf : ConvexOn ℝ S f)
    {x0 x1 x2 : E} (hx0 : x0 ∈ S) (hx1 : x1 ∈ S) (hx2 : x2 ∈ S)
    {c0 c1 c2 : ℝ} (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hsum : c0 + c1 + c2 = 1) :
    f (c0 • x0 + c1 • x1 + c2 • x2) ≤ c0 * f x0 + c1 * f x1 + c2 * f x2 := by
  by_cases hs : c0 + c1 = 0
  · have h0 : c0 = 0 := by linarith
    have h1 : c1 = 0 := by linarith
    have h2 : c2 = 1 := by linarith
    simp [h0, h1, h2]
  · have hs_pos : 0 < c0 + c1 := lt_of_le_of_ne (by linarith) (Ne.symm hs)
    set s := c0 + c1
    have hmem : (c0 / s) • x0 + (c1 / s) • x1 ∈ S :=
      hf.1 hx0 hx1 (div_nonneg hc0 (le_of_lt hs_pos)) (div_nonneg hc1 (le_of_lt hs_pos))
        (by rw [← add_div, div_self (ne_of_gt hs_pos)])
    have heq : c0 • x0 + c1 • x1 + c2 • x2 = s • ((c0 / s) • x0 + (c1 / s) • x1) + c2 • x2 := by
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ (ne_of_gt hs_pos),
          mul_div_cancel₀ _ (ne_of_gt hs_pos)]
    rw [heq]
    have h1 := hf.2 hmem hx2 (le_of_lt hs_pos) hc2 (by dsimp [s]; linarith)
    have h2 := hf.2 hx0 hx1 (div_nonneg hc0 (le_of_lt hs_pos)) (div_nonneg hc1 (le_of_lt hs_pos))
      (by rw [← add_div, div_self (ne_of_gt hs_pos)])
    have h3 : s * f ((c0 / s) • x0 + (c1 / s) • x1) ≤ c0 * f x0 + c1 * f x1 := by
      have hm := mul_le_mul_of_nonneg_left h2 (le_of_lt hs_pos)
      have hr : s * ((c0 / s) * f x0 + (c1 / s) * f x1) = c0 * f x0 + c1 * f x1 := by
        field_simp [ne_of_gt hs_pos]
      simpa [smul_eq_mul, hr] using hm
    simp only [smul_eq_mul] at h1
    linarith

private lemma convex_bary4 {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {f : E → ℝ} (hf : ConvexOn ℝ S f)
    {x0 x1 x2 x3 : E} (hx0 : x0 ∈ S) (hx1 : x1 ∈ S) (hx2 : x2 ∈ S) (hx3 : x3 ∈ S)
    {c0 c1 c2 c3 : ℝ} (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hsum : c0 + c1 + c2 + c3 = 1) :
    f (c0 • x0 + c1 • x1 + c2 • x2 + c3 • x3) ≤
      c0 * f x0 + c1 * f x1 + c2 * f x2 + c3 * f x3 := by
  by_cases hs : c0 + c1 + c2 = 0
  · have h0 : c0 = 0 := by linarith
    have h1 : c1 = 0 := by linarith
    have h2 : c2 = 0 := by linarith
    have h3 : c3 = 1 := by linarith
    simp [h0, h1, h2, h3]
  · have hs_pos : 0 < c0 + c1 + c2 := lt_of_le_of_ne (by linarith) (Ne.symm hs)
    set s := c0 + c1 + c2
    have h12 : c0 / s + c1 / s + c2 / s = 1 := by
      rw [← add_div, ← add_div, div_self (ne_of_gt hs_pos)]
    have hmem : (c0 / s) • x0 + (c1 / s) • x1 + (c2 / s) • x2 ∈ S := by
      by_cases hs01 : c0 + c1 = 0
      · have h0 : c0 = 0 := by linarith
        have h1 : c1 = 0 := by linarith
        have h2 : c2 / s = 1 := by dsimp [s]; rw [h0, h1, zero_add, zero_add, div_self (by linarith)]
        simp [h0, h1, h2, hx2]
      · have hs01_pos : 0 < c0 + c1 := lt_of_le_of_ne (by linarith) (Ne.symm hs01)
        set t := c0 + c1
        have hm01 : (c0 / t) • x0 + (c1 / t) • x1 ∈ S :=
          hf.1 hx0 hx1 (div_nonneg hc0 (le_of_lt hs01_pos)) (div_nonneg hc1 (le_of_lt hs01_pos))
            (by rw [← add_div, div_self (ne_of_gt hs01_pos)])
        have heq0 : (c0 / s) • x0 + (c1 / s) • x1 + (c2 / s) • x2 =
            (t / s) • ((c0 / t) • x0 + (c1 / t) • x1) + (c2 / s) • x2 := by
          rw [smul_add, smul_smul, smul_smul]
          congr 1; congr 1
          · congr 1; field_simp [ne_of_gt hs_pos, ne_of_gt hs01_pos]
          · congr 1; field_simp [ne_of_gt hs_pos, ne_of_gt hs01_pos]
        rw [heq0]
        exact hf.1 hm01 hx2 (div_nonneg (le_of_lt hs01_pos) (le_of_lt hs_pos))
          (div_nonneg hc2 (le_of_lt hs_pos))
          (by rw [← add_div]; dsimp [s, t]; exact div_self (ne_of_gt hs_pos))
    have heq : c0 • x0 + c1 • x1 + c2 • x2 + c3 • x3 =
        s • ((c0 / s) • x0 + (c1 / s) • x1 + (c2 / s) • x2) + c3 • x3 := by
      rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul,
          mul_div_cancel₀ _ (ne_of_gt hs_pos), mul_div_cancel₀ _ (ne_of_gt hs_pos),
          mul_div_cancel₀ _ (ne_of_gt hs_pos)]
    rw [heq]
    have h1 := hf.2 hmem hx3 (le_of_lt hs_pos) hc3 (by dsimp [s]; linarith)
    have h2 := convex_bary3 hf hx0 hx1 hx2 (div_nonneg hc0 (le_of_lt hs_pos))
      (div_nonneg hc1 (le_of_lt hs_pos)) (div_nonneg hc2 (le_of_lt hs_pos)) h12
    have h3 : s * f ((c0 / s) • x0 + (c1 / s) • x1 + (c2 / s) • x2) ≤
        c0 * f x0 + c1 * f x1 + c2 * f x2 := by
      have hm := mul_le_mul_of_nonneg_left h2 (le_of_lt hs_pos)
      have hr : s * ((c0 / s) * f x0 + (c1 / s) * f x1 + (c2 / s) * f x2) =
          c0 * f x0 + c1 * f x1 + c2 * f x2 := by
        field_simp [ne_of_gt hs_pos]
      simpa [smul_eq_mul, hr] using hm
    simp only [smul_eq_mul] at h1
    linarith

private lemma convex_bary5 {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {f : E → ℝ} (hf : ConvexOn ℝ S f)
    {x0 x1 x2 x3 x4 : E} (hx0 : x0 ∈ S) (hx1 : x1 ∈ S) (hx2 : x2 ∈ S) (hx3 : x3 ∈ S) (hx4 : x4 ∈ S)
    {c0 c1 c2 c3 c4 : ℝ} (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4)
    (hsum : c0 + c1 + c2 + c3 + c4 = 1) :
    f (c0 • x0 + c1 • x1 + c2 • x2 + c3 • x3 + c4 • x4) ≤
      c0 * f x0 + c1 * f x1 + c2 * f x2 + c3 * f x3 + c4 * f x4 := by
  by_cases hs : c0 + c1 + c2 + c3 = 0
  · have h0 : c0 = 0 := by linarith
    have h1 : c1 = 0 := by linarith
    have h2 : c2 = 0 := by linarith
    have h3 : c3 = 0 := by linarith
    have h4 : c4 = 1 := by linarith
    simp [h0, h1, h2, h3, h4]
  · have hs_pos : 0 < c0 + c1 + c2 + c3 := lt_of_le_of_ne (by linarith) (Ne.symm hs)
    set s := c0 + c1 + c2 + c3
    have h123 : c0 / s + c1 / s + c2 / s + c3 / s = 1 := by
      rw [← add_div, ← add_div, ← add_div, div_self (ne_of_gt hs_pos)]
    have hmem : (c0 / s) • x0 + (c1 / s) • x1 + (c2 / s) • x2 + (c3 / s) • x3 ∈ S := by
      by_cases h01 : c0 + c1 = 0
      · have h0 : c0 = 0 := by linarith
        have h1 : c1 = 0 := by linarith
        have h23 : c2 / s + c3 / s = 1 := by
          rw [← add_div, show c2 + c3 = s by dsimp [s]; linarith, div_self (ne_of_gt hs_pos)]
        simpa [h0, h1] using hf.1 hx2 hx3 (div_nonneg hc2 (le_of_lt hs_pos))
          (div_nonneg hc3 (le_of_lt hs_pos)) h23
      · by_cases h23 : c2 + c3 = 0
        · have h2 : c2 = 0 := by linarith
          have h3 : c3 = 0 := by linarith
          have h01s : c0 / s + c1 / s = 1 := by
            rw [← add_div, show c0 + c1 = s by dsimp [s]; linarith, div_self (ne_of_gt hs_pos)]
          simpa [h2, h3] using hf.1 hx0 hx1 (div_nonneg hc0 (le_of_lt hs_pos))
            (div_nonneg hc1 (le_of_lt hs_pos)) h01s
        · have hp01 : 0 < c0 + c1 := lt_of_le_of_ne (by linarith) (Ne.symm h01)
          have hp23 : 0 < c2 + c3 := lt_of_le_of_ne (by linarith) (Ne.symm h23)
          set t1 := c0 + c1
          set t2 := c2 + c3
          have hm1 : (c0 / t1) • x0 + (c1 / t1) • x1 ∈ S :=
            hf.1 hx0 hx1 (div_nonneg hc0 (le_of_lt hp01)) (div_nonneg hc1 (le_of_lt hp01))
              (by rw [← add_div, div_self (ne_of_gt hp01)])
          have hm2 : (c2 / t2) • x2 + (c3 / t2) • x3 ∈ S :=
            hf.1 hx2 hx3 (div_nonneg hc2 (le_of_lt hp23)) (div_nonneg hc3 (le_of_lt hp23))
              (by rw [← add_div, div_self (ne_of_gt hp23)])
          have heq0 : (c0 / s) • x0 + (c1 / s) • x1 + (c2 / s) • x2 + (c3 / s) • x3 =
              (t1 / s) • ((c0 / t1) • x0 + (c1 / t1) • x1) +
              (t2 / s) • ((c2 / t2) • x2 + (c3 / t2) • x3) := by
            rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, ← add_assoc]
            have e0 : t1 / s * (c0 / t1) = c0 / s := by field_simp [ne_of_gt hs_pos, ne_of_gt hp01]
            have e1 : t1 / s * (c1 / t1) = c1 / s := by field_simp [ne_of_gt hs_pos, ne_of_gt hp01]
            have e2 : t2 / s * (c2 / t2) = c2 / s := by field_simp [ne_of_gt hs_pos, ne_of_gt hp23]
            have e3 : t2 / s * (c3 / t2) = c3 / s := by field_simp [ne_of_gt hs_pos, ne_of_gt hp23]
            rw [e0, e1, e2, e3]
          rw [heq0]
          exact hf.1 hm1 hm2 (div_nonneg (le_of_lt hp01) (le_of_lt hs_pos))
            (div_nonneg (le_of_lt hp23) (le_of_lt hs_pos))
            (by rw [← add_div, show t1 + t2 = s by dsimp [s, t1, t2]; ring, div_self (ne_of_gt hs_pos)])
    have heq : c0 • x0 + c1 • x1 + c2 • x2 + c3 • x3 + c4 • x4 =
        s • ((c0 / s) • x0 + (c1 / s) • x1 + (c2 / s) • x2 + (c3 / s) • x3) + c4 • x4 := by
      rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
          mul_div_cancel₀ _ (ne_of_gt hs_pos), mul_div_cancel₀ _ (ne_of_gt hs_pos),
          mul_div_cancel₀ _ (ne_of_gt hs_pos), mul_div_cancel₀ _ (ne_of_gt hs_pos)]
    rw [heq]
    have h1 := hf.2 hmem hx4 (le_of_lt hs_pos) hc4 (by dsimp [s]; linarith)
    have h2 := convex_bary4 hf hx0 hx1 hx2 hx3 (div_nonneg hc0 (le_of_lt hs_pos))
      (div_nonneg hc1 (le_of_lt hs_pos)) (div_nonneg hc2 (le_of_lt hs_pos))
      (div_nonneg hc3 (le_of_lt hs_pos)) h123
    have h3 : s * f ((c0 / s) • x0 + (c1 / s) • x1 + (c2 / s) • x2 + (c3 / s) • x3) ≤
        c0 * f x0 + c1 * f x1 + c2 * f x2 + c3 * f x3 := by
      have hm := mul_le_mul_of_nonneg_left h2 (le_of_lt hs_pos)
      have hr : s * ((c0 / s) * f x0 + (c1 / s) * f x1 + (c2 / s) * f x2 + (c3 / s) * f x3) =
          c0 * f x0 + c1 * f x1 + c2 * f x2 + c3 * f x3 := by
        field_simp [ne_of_gt hs_pos]
      simpa [smul_eq_mul, hr] using hm
    simp only [smul_eq_mul] at h1
    linarith

private lemma log_concave_pair {u v a b : ℝ} (hu : 0 < u) (hv : 0 < v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * Real.log u + b * Real.log v ≤ Real.log (a * u + b * v) := by
  have hpos : 0 < a * u + b * v := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      rw [ha0, hb1]; linarith
    · have : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0); nlinarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos hu hpos)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hv hpos)
  rw [Real.log_div (ne_of_gt hu) (ne_of_gt hpos)] at h1
  rw [Real.log_div (ne_of_gt hv) (ne_of_gt hpos)] at h2
  have h1' := mul_le_mul_of_nonneg_left h1 ha
  have h2' := mul_le_mul_of_nonneg_left h2 hb
  have hsum : a * (u / (a * u + b * v) - 1) + b * (v / (a * u + b * v) - 1) = 0 := by
    have hnum : a * (u / (a * u + b * v) - 1) + b * (v / (a * u + b * v) - 1) =
        ((a * u + b * v) - (a + b) * (a * u + b * v)) / (a * u + b * v) := by
      field_simp [ne_of_gt hpos]; ring
    rw [hnum, hab]; ring
  have hlog_sum : a * Real.log (a * u + b * v) + b * Real.log (a * u + b * v) =
      Real.log (a * u + b * v) := by
    rw [← add_mul, hab, one_mul]
  linarith

private lemma log_inv_prod5_convex (p : ℝ) :
    ConvexOn ℝ {x : R4 | 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2 ∧
      0 < p - x.1 - x.2.1 - x.2.2.1 - x.2.2.2}
      (fun x : R4 => 1 / (x.1 * x.2.1 * x.2.2.1 * x.2.2.2 * (p - x.1 - x.2.1 - x.2.2.1 - x.2.2.2))) := by
  have hpos_comb : ∀ {u v a b : ℝ}, 0 < u → 0 < v → 0 ≤ a → 0 ≤ b → a + b = 1 → 0 < a * u + b * v := by
    intro u v a b hu hv ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      rw [ha0, hb1]; linarith
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      nlinarith
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    rcases hx with ⟨hx0, hx1, hx2, hx3, hx4⟩
    rcases hy with ⟨hy0, hy1, hy2, hy3, hy4⟩
    simp only [mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have hp4 : p - (a * x.1 + b * y.1) - (a * x.2.1 + b * y.2.1) - (a * x.2.2.1 + b * y.2.2.1) -
        (a * x.2.2.2 + b * y.2.2.2) =
        a * (p - x.1 - x.2.1 - x.2.2.1 - x.2.2.2) + b * (p - y.1 - y.2.1 - y.2.2.1 - y.2.2.2) := by
      have : p = (a + b) * p := by rw [hab, one_mul]
      linarith
    rw [hp4]
    exact ⟨hpos_comb hx0 hy0 ha hb hab, hpos_comb hx1 hy1 ha hb hab,
           hpos_comb hx2 hy2 ha hb hab, hpos_comb hx3 hy3 ha hb hab,
           hpos_comb hx4 hy4 ha hb hab⟩
  · intro x hx y hy a b ha hb hab
    rcases hx with ⟨hx0, hx1, hx2, hx3, hx4⟩
    rcases hy with ⟨hy0, hy1, hy2, hy3, hy4⟩
    have l0 := log_concave_pair hx0 hy0 ha hb hab
    have l1 := log_concave_pair hx1 hy1 ha hb hab
    have l2 := log_concave_pair hx2 hy2 ha hb hab
    have l3 := log_concave_pair hx3 hy3 ha hb hab
    have l4 := log_concave_pair hx4 hy4 ha hb hab
    simp only [smul_eq_mul] at ⊢
    set z0 := a * x.1 + b * y.1
    set z1 := a * x.2.1 + b * y.2.1
    set z2 := a * x.2.2.1 + b * y.2.2.1
    set z3 := a * x.2.2.2 + b * y.2.2.2
    set z4 := a * (p - x.1 - x.2.1 - x.2.2.1 - x.2.2.2) + b * (p - y.1 - y.2.1 - y.2.2.1 - y.2.2.2)
    have hz0 : 0 < z0 := hpos_comb hx0 hy0 ha hb hab
    have hz1 : 0 < z1 := hpos_comb hx1 hy1 ha hb hab
    have hz2 : 0 < z2 := hpos_comb hx2 hy2 ha hb hab
    have hz3 : 0 < z3 := hpos_comb hx3 hy3 ha hb hab
    have hz4 : 0 < z4 := hpos_comb hx4 hy4 ha hb hab
    have hp4 : p - z0 - z1 - z2 - z3 = z4 := by
      dsimp only [z0, z1, z2, z3, z4]
      have : p = (a + b) * p := by rw [hab, one_mul]
      linarith
    have hsum : -(Real.log z0 + Real.log z1 + Real.log z2 + Real.log z3 + Real.log z4) ≤
        a * (-(Real.log x.1 + Real.log x.2.1 + Real.log x.2.2.1 + Real.log x.2.2.2 +
          Real.log (p - x.1 - x.2.1 - x.2.2.1 - x.2.2.2))) +
        b * (-(Real.log y.1 + Real.log y.2.1 + Real.log y.2.2.1 + Real.log y.2.2.2 +
          Real.log (p - y.1 - y.2.1 - y.2.2.1 - y.2.2.2))) := by linarith
    have hexp1 := Real.exp_le_exp.mpr hsum
    have hexp2 := convexOn_exp.2
      (mem_univ (-(Real.log x.1 + Real.log x.2.1 + Real.log x.2.2.1 + Real.log x.2.2.2 +
        Real.log (p - x.1 - x.2.1 - x.2.2.1 - x.2.2.2))))
      (mem_univ (-(Real.log y.1 + Real.log y.2.1 + Real.log y.2.2.1 + Real.log y.2.2.2 +
        Real.log (p - y.1 - y.2.1 - y.2.2.1 - y.2.2.2)))) ha hb hab
    simp only [smul_eq_mul] at hexp2
    have hrew : ∀ {u0 u1 u2 u3 u4 : ℝ}, 0 < u0 → 0 < u1 → 0 < u2 → 0 < u3 → 0 < u4 →
        Real.exp (-(Real.log u0 + Real.log u1 + Real.log u2 + Real.log u3 + Real.log u4)) =
          1 / (u0 * u1 * u2 * u3 * u4) := by
      intro u0 u1 u2 u3 u4 h0 h1 h2 h3 h4
      rw [Real.exp_neg, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
          Real.exp_log h0, Real.exp_log h1, Real.exp_log h2, Real.exp_log h3, Real.exp_log h4, one_div]
    rw [hrew hz0 hz1 hz2 hz3 hz4] at hexp1
    rw [hrew hx0 hx1 hx2 hx3 hx4, hrew hy0 hy1 hy2 hy3 hy4] at hexp2
    have hfst : (a • x + b • y).1 = z0 := rfl
    have hsnd1 : (a • x + b • y).2.1 = z1 := rfl
    have hsnd2 : (a • x + b • y).2.2.1 = z2 := rfl
    have hsnd3 : (a • x + b • y).2.2.2 = z3 := rfl
    rw [hfst, hsnd1, hsnd2, hsnd3, hp4]
    exact le_trans hexp1 hexp2

private lemma weight4_convex :
    ConvexOn ℝ {x : R4 | 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2}
      (fun x : R4 => 1 / (x.1 * x.2.1 * x.2.2.1 * x.2.2.1 * x.2.2.2)) := by
  have hpos_comb : ∀ {u v a b : ℝ}, 0 < u → 0 < v → 0 ≤ a → 0 ≤ b → a + b = 1 → 0 < a * u + b * v := by
    intro u v a b hu hv ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      rw [ha0, hb1]; linarith
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      nlinarith
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    rcases hx with ⟨hx0, hx1, hx2, hx3⟩
    rcases hy with ⟨hy0, hy1, hy2, hy3⟩
    simp only [mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact ⟨hpos_comb hx0 hy0 ha hb hab, hpos_comb hx1 hy1 ha hb hab,
           hpos_comb hx2 hy2 ha hb hab, hpos_comb hx3 hy3 ha hb hab⟩
  · intro x hx y hy a b ha hb hab
    rcases hx with ⟨hx0, hx1, hx2, hx3⟩
    rcases hy with ⟨hy0, hy1, hy2, hy3⟩
    have l0 := log_concave_pair hx0 hy0 ha hb hab
    have l1 := log_concave_pair hx1 hy1 ha hb hab
    have l2 := log_concave_pair hx2 hy2 ha hb hab
    have l3 := log_concave_pair hx3 hy3 ha hb hab
    simp only [smul_eq_mul] at ⊢
    set z0 := a * x.1 + b * y.1
    set z1 := a * x.2.1 + b * y.2.1
    set z2 := a * x.2.2.1 + b * y.2.2.1
    set z3 := a * x.2.2.2 + b * y.2.2.2
    have hz0 : 0 < z0 := hpos_comb hx0 hy0 ha hb hab
    have hz1 : 0 < z1 := hpos_comb hx1 hy1 ha hb hab
    have hz2 : 0 < z2 := hpos_comb hx2 hy2 ha hb hab
    have hz3 : 0 < z3 := hpos_comb hx3 hy3 ha hb hab
    have hsum : -(Real.log z0 + Real.log z1 + Real.log z2 + Real.log z2 + Real.log z3) ≤
        a * (-(Real.log x.1 + Real.log x.2.1 + Real.log x.2.2.1 + Real.log x.2.2.1 + Real.log x.2.2.2)) +
        b * (-(Real.log y.1 + Real.log y.2.1 + Real.log y.2.2.1 + Real.log y.2.2.1 + Real.log y.2.2.2)) := by
      linarith
    have hexp1 := Real.exp_le_exp.mpr hsum
    have hexp2 := convexOn_exp.2
      (mem_univ (-(Real.log x.1 + Real.log x.2.1 + Real.log x.2.2.1 + Real.log x.2.2.1 + Real.log x.2.2.2)))
      (mem_univ (-(Real.log y.1 + Real.log y.2.1 + Real.log y.2.2.1 + Real.log y.2.2.1 + Real.log y.2.2.2))) ha hb hab
    simp only [smul_eq_mul] at hexp2
    have hrew : ∀ {u0 u1 u2 u3 : ℝ}, 0 < u0 → 0 < u1 → 0 < u2 → 0 < u3 →
        Real.exp (-(Real.log u0 + Real.log u1 + Real.log u2 + Real.log u2 + Real.log u3)) =
          1 / (u0 * u1 * u2 * u2 * u3) := by
      intro u0 u1 u2 u3 h0 h1 h2 h3
      rw [Real.exp_neg, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
          Real.exp_log h0, Real.exp_log h1, Real.exp_log h2, Real.exp_log h3, one_div]
    rw [hrew hz0 hz1 hz2 hz3] at hexp1
    rw [hrew hx0 hx1 hx2 hx3, hrew hy0 hy1 hy2 hy3] at hexp2
    exact le_trans hexp1 hexp2

/-! #### Pointwise Barycentric Bounds on Convex Boxes → Hermite-Hadamard for ALL 8 `Cell4` Shapes -/

private lemma w1_nonneg {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) (e : Bool) : 0 ≤ w1 a b e x := by
  have hba : 0 < b - a := sub_pos.mpr hab
  cases e <;> simp only [w1]
  · exact div_nonneg (sub_nonneg.mpr hx.2) (le_of_lt hba)
  · exact div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hba)

private lemma w2_nonneg {a b x0 x1 : ℝ} (hab : a < b) (h0 : a ≤ x0) (h01 : x0 ≤ x1) (h1 : x1 ≤ b)
    (i : Fin 3) : 0 ≤ w2 a b i x0 x1 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  fin_cases i <;> simp only [w2]
  · exact div_nonneg (sub_nonneg.mpr h1) (le_of_lt hba)
  · exact div_nonneg (sub_nonneg.mpr h01) (le_of_lt hba)
  · exact div_nonneg (sub_nonneg.mpr h0) (le_of_lt hba)

private lemma w3_nonneg {a b x0 x1 x2 : ℝ} (hab : a < b) (h0 : a ≤ x0) (h01 : x0 ≤ x1)
    (h12 : x1 ≤ x2) (h2 : x2 ≤ b) (i : Fin 4) : 0 ≤ w3 a b i x0 x1 x2 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  fin_cases i <;> simp only [w3]
  · exact div_nonneg (sub_nonneg.mpr h2) (le_of_lt hba)
  · exact div_nonneg (sub_nonneg.mpr h12) (le_of_lt hba)
  · exact div_nonneg (sub_nonneg.mpr h01) (le_of_lt hba)
  · exact div_nonneg (sub_nonneg.mpr h0) (le_of_lt hba)

private lemma w4_nonneg {a b x0 x1 x2 x3 : ℝ} (hab : a < b) (h0 : a ≤ x0) (h01 : x0 ≤ x1)
    (h12 : x1 ≤ x2) (h23 : x2 ≤ x3) (h3 : x3 ≤ b) (i : Fin 5) : 0 ≤ w4 a b i x0 x1 x2 x3 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  fin_cases i <;> simp only [w4]
  · exact div_nonneg (sub_nonneg.mpr h3) (le_of_lt hba)
  · exact div_nonneg (sub_nonneg.mpr h23) (le_of_lt hba)
  · exact div_nonneg (sub_nonneg.mpr h12) (le_of_lt hba)
  · exact div_nonneg (sub_nonneg.mpr h01) (le_of_lt hba)
  · exact div_nonneg (sub_nonneg.mpr h0) (le_of_lt hba)

private lemma v1_mem {a b : ℝ} (hab : a ≤ b) (e : Bool) : v1 a b e ∈ Icc a b := by
  cases e <;> simp [v1, hab]

private lemma v2_mem {a b : ℝ} (hab : a ≤ b) (i : Fin 3) :
    (v2 a b i).1 ∈ Icc a b ∧ (v2 a b i).2 ∈ Icc a b := by
  fin_cases i <;> simp [v2, hab]

private lemma v3_mem {a b : ℝ} (hab : a ≤ b) (i : Fin 4) :
    (v3 a b i).1 ∈ Icc a b ∧ (v3 a b i).2.1 ∈ Icc a b ∧ (v3 a b i).2.2 ∈ Icc a b := by
  fin_cases i <;> simp [v3, hab]

private lemma v4_mem {a b : ℝ} (hab : a ≤ b) (i : Fin 5) :
    (v4 a b i).1 ∈ Icc a b ∧ (v4 a b i).2.1 ∈ Icc a b ∧
    (v4 a b i).2.2.1 ∈ Icc a b ∧ (v4 a b i).2.2.2 ∈ Icc a b := by
  fin_cases i <;> simp [v4, hab]

private lemma convex_bary1_coord {S : Set R4} {f : R4 → ℝ} (hf : ConvexOn ℝ S f)
    {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    {q : Bool → R4} (hq : ∀ e, q e ∈ S) {p : R4}
    (heq : w1 a b false t • q false + w1 a b true t • q true = p) :
    f p ≤ ∑ e : Bool, w1 a b e t * f (q e) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hsum : w1 a b false t + w1 a b true t = 1 := by
    simp only [w1]; field_simp [ne_of_gt hba]; ring
  have h := hf.2 (hq false) (hq true) (w1_nonneg hab ht false) (w1_nonneg hab ht true) hsum
  rw [heq] at h
  simp only [Fintype.sum_bool, smul_eq_mul] at h ⊢
  linarith

private lemma convex_bary2_coord {S : Set R4} {f : R4 → ℝ} (hf : ConvexOn ℝ S f)
    {a b x0 x1 : ℝ} (hab : a < b) (h0 : a ≤ x0) (h01 : x0 ≤ x1) (h1 : x1 ≤ b)
    {q : Fin 3 → R4} (hq : ∀ i, q i ∈ S) {p : R4}
    (heq : w2 a b 0 x0 x1 • q 0 + w2 a b 1 x0 x1 • q 1 + w2 a b 2 x0 x1 • q 2 = p) :
    f p ≤ ∑ i : Fin 3, w2 a b i x0 x1 * f (q i) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hsum : w2 a b 0 x0 x1 + w2 a b 1 x0 x1 + w2 a b 2 x0 x1 = 1 := by
    simp only [w2]; field_simp [ne_of_gt hba]; ring
  have h := convex_bary3 hf (hq 0) (hq 1) (hq 2)
    (w2_nonneg hab h0 h01 h1 0) (w2_nonneg hab h0 h01 h1 1) (w2_nonneg hab h0 h01 h1 2) hsum
  rw [heq] at h
  simpa [Fin.sum_univ_three] using h

private lemma convex_bary3_coord {S : Set R4} {f : R4 → ℝ} (hf : ConvexOn ℝ S f)
    {a b x0 x1 x2 : ℝ} (hab : a < b) (h0 : a ≤ x0) (h01 : x0 ≤ x1) (h12 : x1 ≤ x2) (h2 : x2 ≤ b)
    {q : Fin 4 → R4} (hq : ∀ i, q i ∈ S) {p : R4}
    (heq : w3 a b 0 x0 x1 x2 • q 0 + w3 a b 1 x0 x1 x2 • q 1 +
           w3 a b 2 x0 x1 x2 • q 2 + w3 a b 3 x0 x1 x2 • q 3 = p) :
    f p ≤ ∑ i : Fin 4, w3 a b i x0 x1 x2 * f (q i) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hsum : w3 a b 0 x0 x1 x2 + w3 a b 1 x0 x1 x2 + w3 a b 2 x0 x1 x2 + w3 a b 3 x0 x1 x2 = 1 := by
    simp only [w3]; field_simp [ne_of_gt hba]; ring
  have h := convex_bary4 hf (hq 0) (hq 1) (hq 2) (hq 3)
    (w3_nonneg hab h0 h01 h12 h2 0) (w3_nonneg hab h0 h01 h12 h2 1)
    (w3_nonneg hab h0 h01 h12 h2 2) (w3_nonneg hab h0 h01 h12 h2 3) hsum
  rw [heq] at h
  simpa [Fin.sum_univ_four] using h

private lemma convex_bary4_coord {S : Set R4} {f : R4 → ℝ} (hf : ConvexOn ℝ S f)
    {a b x0 x1 x2 x3 : ℝ} (hab : a < b) (h0 : a ≤ x0) (h01 : x0 ≤ x1)
    (h12 : x1 ≤ x2) (h23 : x2 ≤ x3) (h3 : x3 ≤ b)
    {q : Fin 5 → R4} (hq : ∀ i, q i ∈ S) {p : R4}
    (heq : w4 a b 0 x0 x1 x2 x3 • q 0 + w4 a b 1 x0 x1 x2 x3 • q 1 +
           w4 a b 2 x0 x1 x2 x3 • q 2 + w4 a b 3 x0 x1 x2 x3 • q 3 +
           w4 a b 4 x0 x1 x2 x3 • q 4 = p) :
    f p ≤ ∑ i : Fin 5, w4 a b i x0 x1 x2 x3 * f (q i) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hsum : w4 a b 0 x0 x1 x2 x3 + w4 a b 1 x0 x1 x2 x3 + w4 a b 2 x0 x1 x2 x3 +
      w4 a b 3 x0 x1 x2 x3 + w4 a b 4 x0 x1 x2 x3 = 1 := by
    simp only [w4]; field_simp [ne_of_gt hba]; ring
  have h := convex_bary5 hf (hq 0) (hq 1) (hq 2) (hq 3) (hq 4)
    (w4_nonneg hab h0 h01 h12 h23 h3 0) (w4_nonneg hab h0 h01 h12 h23 h3 1)
    (w4_nonneg hab h0 h01 h12 h23 h3 2) (w4_nonneg hab h0 h01 h12 h23 h3 3)
    (w4_nonneg hab h0 h01 h12 h23 h3 4) hsum
  rw [heq] at h
  simpa [Fin.sum_univ_five] using h

private def vertSumReal (f : R4 → ℝ) : Cell4 → ℝ
  | .c4 a b =>
    let a' := gval a; let b' := gval b
    (b' - a') ^ 4 / 120 *
      (f (a', a', a', a') + f (a', a', a', b') + f (a', a', b', b') +
       f (a', b', b', b') + f (b', b', b', b'))
  | .c31 a0 b0 a1 b1 =>
    let a0' := gval a0; let b0' := gval b0; let a1' := gval a1; let b1' := gval b1
    (b0' - a0') ^ 3 * (b1' - a1') / 48 *
      ((f (a0', a0', a0', a1') + f (a0', a0', b0', a1') + f (a0', b0', b0', a1') + f (b0', b0', b0', a1')) +
       (f (a0', a0', a0', b1') + f (a0', a0', b0', b1') + f (a0', b0', b0', b1') + f (b0', b0', b0', b1')))
  | .c13 a0 b0 a1 b1 =>
    let a0' := gval a0; let b0' := gval b0; let a1' := gval a1; let b1' := gval b1
    (b0' - a0') * (b1' - a1') ^ 3 / 48 *
      ((f (a0', a1', a1', a1') + f (a0', a1', a1', b1') + f (a0', a1', b1', b1') + f (a0', b1', b1', b1')) +
       (f (b0', a1', a1', a1') + f (b0', a1', a1', b1') + f (b0', a1', b1', b1') + f (b0', b1', b1', b1')))
  | .c22 a0 b0 a1 b1 =>
    let a0' := gval a0; let b0' := gval b0; let a1' := gval a1; let b1' := gval b1
    (b0' - a0') ^ 2 * (b1' - a1') ^ 2 / 36 *
      ((f (a0', a0', a1', a1') + f (a0', a0', a1', b1') + f (a0', a0', b1', b1')) +
       (f (a0', b0', a1', a1') + f (a0', b0', a1', b1') + f (a0', b0', b1', b1')) +
       (f (b0', b0', a1', a1') + f (b0', b0', a1', b1') + f (b0', b0', b1', b1')))
  | .c211 a0 b0 a1 b1 a2 b2 =>
    let a0' := gval a0; let b0' := gval b0; let a1' := gval a1; let b1' := gval b1; let a2' := gval a2; let b2' := gval b2
    (b0' - a0') ^ 2 * (b1' - a1') * (b2' - a2') / 24 *
      ((f (a0', a0', a1', a2') + f (a0', a0', a1', b2') + f (a0', a0', b1', a2') + f (a0', a0', b1', b2')) +
       (f (a0', b0', a1', a2') + f (a0', b0', a1', b2') + f (a0', b0', b1', a2') + f (a0', b0', b1', b2')) +
       (f (b0', b0', a1', a2') + f (b0', b0', a1', b2') + f (b0', b0', b1', a2') + f (b0', b0', b1', b2')))
  | .c121 a0 b0 a1 b1 a2 b2 =>
    let a0' := gval a0; let b0' := gval b0; let a1' := gval a1; let b1' := gval b1; let a2' := gval a2; let b2' := gval b2
    (b0' - a0') * (b1' - a1') ^ 2 * (b2' - a2') / 24 *
      ((f (a0', a1', a1', a2') + f (a0', a1', a1', b2') + f (b0', a1', a1', a2') + f (b0', a1', a1', b2')) +
       (f (a0', a1', b1', a2') + f (a0', a1', b1', b2') + f (b0', a1', b1', a2') + f (b0', a1', b1', b2')) +
       (f (a0', b1', b1', a2') + f (a0', b1', b1', b2') + f (b0', b1', b1', a2') + f (b0', b1', b1', b2')))
  | .c112 a0 b0 a1 b1 a2 b2 =>
    let a0' := gval a0; let b0' := gval b0; let a1' := gval a1; let b1' := gval b1; let a2' := gval a2; let b2' := gval b2
    (b0' - a0') * (b1' - a1') * (b2' - a2') ^ 2 / 24 *
      ((f (a0', a1', a2', a2') + f (a0', b1', a2', a2') + f (b0', a1', a2', a2') + f (b0', b1', a2', a2')) +
       (f (a0', a1', a2', b2') + f (a0', b1', a2', b2') + f (b0', a1', a2', b2') + f (b0', b1', a2', b2')) +
       (f (a0', a1', b2', b2') + f (a0', b1', b2', b2') + f (b0', a1', b2', b2') + f (b0', b1', b2', b2')))
  | .c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
    let a0' := gval a0; let b0' := gval b0; let a1' := gval a1; let b1' := gval b1
    let a2' := gval a2; let b2' := gval b2; let a3' := gval a3; let b3' := gval b3
    (b0' - a0') * (b1' - a1') * (b2' - a2') * (b3' - a3') / 16 *
      ((f (a0', a1', a2', a3') + f (a0', a1', a2', b3') + f (a0', a1', b2', a3') + f (a0', a1', b2', b3')) +
       (f (a0', b1', a2', a3') + f (a0', b1', a2', b3') + f (a0', b1', b2', a3') + f (a0', b1', b2', b3')) +
       (f (b0', a1', a2', a3') + f (b0', a1', a2', b3') + f (b0', a1', b2', a3') + f (b0', a1', b2', b3')) +
       (f (b0', b1', a2', a3') + f (b0', b1', a2', b3') + f (b0', b1', b2', a3') + f (b0', b1', b2', b3')))

private lemma bary1_sum {a b x : ℝ} (h : b - a ≠ 0) :
    (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
  rw [← add_div, show b - x + (x - a) = b - a by ring, div_self h]

private lemma bary1_id {a b x : ℝ} (h : b - a ≠ 0) :
    (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      show (b - x) * a + (x - a) * b = x * (b - a) by ring, mul_div_cancel_right₀ _ h]

private lemma bary1_const {a b x c : ℝ} (h : b - a ≠ 0) :
    (b - x) / (b - a) * c + (x - a) / (b - a) * c = c := by
  rw [← add_mul, bary1_sum h, one_mul]

private lemma bary2_sum {a b x0 x1 : ℝ} (h : b - a ≠ 0) :
    (b - x1) / (b - a) + (x1 - x0) / (b - a) + (x0 - a) / (b - a) = 1 := by
  rw [← add_div, ← add_div, show b - x1 + (x1 - x0) + (x0 - a) = b - a by ring, div_self h]

private lemma bary2_const {a b x0 x1 c : ℝ} (h : b - a ≠ 0) :
    (b - x1) / (b - a) * c + (x1 - x0) / (b - a) * c + (x0 - a) / (b - a) * c = c := by
  rw [← add_mul, ← add_mul, bary2_sum h, one_mul]

private lemma bary2_id0 {a b x0 x1 : ℝ} (h : b - a ≠ 0) :
    (b - x1) / (b - a) * a + (x1 - x0) / (b - a) * a + (x0 - a) / (b - a) * b = x0 := by
  simp only [div_mul_eq_mul_div]; rw [← add_div, ← add_div,
      show (b - x1) * a + (x1 - x0) * a + (x0 - a) * b = x0 * (b - a) by ring, mul_div_cancel_right₀ _ h]

private lemma bary2_id1 {a b x0 x1 : ℝ} (h : b - a ≠ 0) :
    (b - x1) / (b - a) * a + (x1 - x0) / (b - a) * b + (x0 - a) / (b - a) * b = x1 := by
  simp only [div_mul_eq_mul_div]; rw [← add_div, ← add_div,
      show (b - x1) * a + (x1 - x0) * b + (x0 - a) * b = x1 * (b - a) by ring, mul_div_cancel_right₀ _ h]

private lemma bary3_sum {a b x0 x1 x2 : ℝ} (h : b - a ≠ 0) :
    (b - x2) / (b - a) + (x2 - x1) / (b - a) + (x1 - x0) / (b - a) + (x0 - a) / (b - a) = 1 := by
  rw [← add_div, ← add_div, ← add_div, show b - x2 + (x2 - x1) + (x1 - x0) + (x0 - a) = b - a by ring, div_self h]

private lemma bary3_const {a b x0 x1 x2 c : ℝ} (h : b - a ≠ 0) :
    (b - x2) / (b - a) * c + (x2 - x1) / (b - a) * c + (x1 - x0) / (b - a) * c + (x0 - a) / (b - a) * c = c := by
  rw [← add_mul, ← add_mul, ← add_mul, bary3_sum h, one_mul]

private lemma bary3_id0 {a b x0 x1 x2 : ℝ} (h : b - a ≠ 0) :
    (b - x2) / (b - a) * a + (x2 - x1) / (b - a) * a + (x1 - x0) / (b - a) * a + (x0 - a) / (b - a) * b = x0 := by
  simp only [div_mul_eq_mul_div]; rw [← add_div, ← add_div, ← add_div,
      show (b - x2) * a + (x2 - x1) * a + (x1 - x0) * a + (x0 - a) * b = x0 * (b - a) by ring, mul_div_cancel_right₀ _ h]

private lemma bary3_id1 {a b x0 x1 x2 : ℝ} (h : b - a ≠ 0) :
    (b - x2) / (b - a) * a + (x2 - x1) / (b - a) * a + (x1 - x0) / (b - a) * b + (x0 - a) / (b - a) * b = x1 := by
  simp only [div_mul_eq_mul_div]; rw [← add_div, ← add_div, ← add_div,
      show (b - x2) * a + (x2 - x1) * a + (x1 - x0) * b + (x0 - a) * b = x1 * (b - a) by ring, mul_div_cancel_right₀ _ h]

private lemma bary3_id2 {a b x0 x1 x2 : ℝ} (h : b - a ≠ 0) :
    (b - x2) / (b - a) * a + (x2 - x1) / (b - a) * b + (x1 - x0) / (b - a) * b + (x0 - a) / (b - a) * b = x2 := by
  simp only [div_mul_eq_mul_div]; rw [← add_div, ← add_div, ← add_div,
      show (b - x2) * a + (x2 - x1) * b + (x1 - x0) * b + (x0 - a) * b = x2 * (b - a) by ring, mul_div_cancel_right₀ _ h]

private lemma bary4_id0 {a b x0 x1 x2 x3 : ℝ} (h : b - a ≠ 0) :
    (b - x3) / (b - a) * a + (x3 - x2) / (b - a) * a + (x2 - x1) / (b - a) * a +
    (x1 - x0) / (b - a) * a + (x0 - a) / (b - a) * b = x0 := by
  simp only [div_mul_eq_mul_div]; rw [← add_div, ← add_div, ← add_div, ← add_div,
      show (b - x3) * a + (x3 - x2) * a + (x2 - x1) * a + (x1 - x0) * a + (x0 - a) * b = x0 * (b - a) by ring,
      mul_div_cancel_right₀ _ h]

private lemma bary4_id1 {a b x0 x1 x2 x3 : ℝ} (h : b - a ≠ 0) :
    (b - x3) / (b - a) * a + (x3 - x2) / (b - a) * a + (x2 - x1) / (b - a) * a +
    (x1 - x0) / (b - a) * b + (x0 - a) / (b - a) * b = x1 := by
  simp only [div_mul_eq_mul_div]; rw [← add_div, ← add_div, ← add_div, ← add_div,
      show (b - x3) * a + (x3 - x2) * a + (x2 - x1) * a + (x1 - x0) * b + (x0 - a) * b = x1 * (b - a) by ring,
      mul_div_cancel_right₀ _ h]

private lemma bary4_id2 {a b x0 x1 x2 x3 : ℝ} (h : b - a ≠ 0) :
    (b - x3) / (b - a) * a + (x3 - x2) / (b - a) * a + (x2 - x1) / (b - a) * b +
    (x1 - x0) / (b - a) * b + (x0 - a) / (b - a) * b = x2 := by
  simp only [div_mul_eq_mul_div]; rw [← add_div, ← add_div, ← add_div, ← add_div,
      show (b - x3) * a + (x3 - x2) * a + (x2 - x1) * b + (x1 - x0) * b + (x0 - a) * b = x2 * (b - a) by ring,
      mul_div_cancel_right₀ _ h]

private lemma bary4_id3 {a b x0 x1 x2 x3 : ℝ} (h : b - a ≠ 0) :
    (b - x3) / (b - a) * a + (x3 - x2) / (b - a) * b + (x2 - x1) / (b - a) * b +
    (x1 - x0) / (b - a) * b + (x0 - a) / (b - a) * b = x3 := by
  simp only [div_mul_eq_mul_div]; rw [← add_div, ← add_div, ← add_div, ← add_div,
      show (b - x3) * a + (x3 - x2) * b + (x2 - x1) * b + (x1 - x0) * b + (x0 - a) * b = x3 * (b - a) by ring,
      mul_div_cancel_right₀ _ h]

private lemma w1_cont (a b : ℝ) (e : Bool) : Continuous (fun x => w1 a b e x) := by
  cases e <;> simp only [w1] <;> fun_prop

private lemma w2_cont (a b : ℝ) (i : Fin 3) : Continuous (fun p : ℝ × ℝ => w2 a b i p.1 p.2) := by
  fin_cases i <;> simp only [w2] <;> fun_prop

private lemma w3_cont (a b : ℝ) (i : Fin 4) : Continuous (fun p : ℝ × ℝ × ℝ => w3 a b i p.1 p.2.1 p.2.2) := by
  fin_cases i <;> simp only [w3] <;> fun_prop

private lemma w4_cont (a b : ℝ) (i : Fin 5) : Continuous (fun p : R4 => w4 a b i p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  fin_cases i <;> simp only [w4] <;> fun_prop

private lemma hh_cell4 (c : Cell4) (hv : c.valid) {f : R4 → ℝ}
    (hcont : ContinuousOn f c.box) (hconv : ConvexOn ℝ c.box f) :
    ∫ x in c.set, f x ≤ vertSumReal f c := by
  have hint_f : IntegrableOn f c.set volume :=
    (hcont.mono c.set_subset_box).integrableOn_compact c.isCompact_set
  have hc0 : Continuous (fun x : R4 => x.1) := continuous_fst
  have hc1 : Continuous (fun x : R4 => x.2.1) := continuous_fst.comp continuous_snd
  have hc2 : Continuous (fun x : R4 => x.2.2.1) := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hc3 : Continuous (fun x : R4 => x.2.2.2) := continuous_snd.comp (continuous_snd.comp continuous_snd)
  cases c with
  | c4 a b =>
    rcases hv with ⟨_, hab⟩
    set a' := gval a; set b' := gval b
    have hlt : a' < b' := gval_lt hab
    have hle : a' ≤ b' := le_of_lt hlt
    have hba : b' - a' ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
    have hpt : ∀ x ∈ (Cell4.c4 a b).set,
        f x ≤ ∑ i : Fin 5, w4 a' b' i x.1 x.2.1 x.2.2.1 x.2.2.2 * f (v4 a' b' i) := by
      intro x hx; rcases hx with ⟨h0, h01, h12, h23, h3⟩
      apply convex_bary4_coord hconv hlt h0 h01 h12 h23 h3
      · intro i; exact v4_mem hle i
      · refine Prod.ext (bary4_id0 hba) (Prod.ext (bary4_id1 hba) (Prod.ext (bary4_id2 hba) (bary4_id3 hba)))
    have hcont_w : ∀ i : Fin 5, Continuous (fun x : R4 => w4 a' b' i x.1 x.2.1 x.2.2.1 x.2.2.2 * f (v4 a' b' i)) :=
      fun i => (w4_cont a' b' i).mul continuous_const
    have hmono := setIntegral_mono_on hint_f
      ((continuous_finsetSum _ fun i _ => hcont_w i).continuousOn.integrableOn_compact (Cell4.c4 a b).isCompact_set)
      (Cell4.c4 a b).measurableSet_set hpt
    rw [integral_finsetSum _ (fun i _ => (hcont_w i).continuousOn.integrableOn_compact (Cell4.c4 a b).isCompact_set)] at hmono
    have hterm : ∀ i : Fin 5,
        ∫ x in (Cell4.c4 a b).set, w4 a' b' i x.1 x.2.1 x.2.2.1 x.2.2.2 * f (v4 a' b' i) =
          (b' - a') ^ 4 / 120 * f (v4 a' b' i) := by
      intro i
      rw [integral_mul_const, c4_set_eq, setIntegral_cell4SetGen hle hle hle hle
        (fun _ => ⟨le_refl _, le_refl _⟩) (fun _ => ⟨le_refl _, le_refl _⟩)
        (fun _ => ⟨le_refl _, le_refl _⟩) (w4_cont a' b' i)]
      simp only [↓reduceIte, iter_w4 hlt i]
    simp_rw [hterm] at hmono
    simp only [Fin.sum_univ_five, v4, vertSumReal] at hmono ⊢
    refine le_trans hmono (le_of_eq ?_); ring
  | c31 a0 b0 a1 b1 =>
    rcases hv with ⟨_, h0, _, h1⟩
    set a0' := gval a0; set b0' := gval b0; set a1' := gval a1; set b1' := gval b1
    have hlt0 : a0' < b0' := gval_lt h0; have hlt1 : a1' < b1' := gval_lt h1
    have hle0 : a0' ≤ b0' := le_of_lt hlt0; have hle1 : a1' ≤ b1' := le_of_lt hlt1
    have hba0 : b0' - a0' ≠ 0 := ne_of_gt (sub_pos.mpr hlt0)
    have hba1 : b1' - a1' ≠ 0 := ne_of_gt (sub_pos.mpr hlt1)
    have hpt : ∀ x ∈ (Cell4.c31 a0 b0 a1 b1).set,
        f x ≤ ∑ p : Fin 4 × Bool,
          (w3 a0' b0' p.1 x.1 x.2.1 x.2.2.1 * w1 a1' b1' p.2 x.2.2.2) *
          f ((v3 a0' b0' p.1).1, (v3 a0' b0' p.1).2.1, (v3 a0' b0' p.1).2.2, v1 a1' b1' p.2) := by
      intro x hx; rcases hx with ⟨hx0, hx01, hx12, hx2, hx3a, hx3b⟩
      have s1 : f x ≤ ∑ i : Fin 4, w3 a0' b0' i x.1 x.2.1 x.2.2.1 *
          f ((v3 a0' b0' i).1, (v3 a0' b0' i).2.1, (v3 a0' b0' i).2.2, x.2.2.2) := by
        apply convex_bary3_coord hconv hlt0 hx0 hx01 hx12 hx2
          (q := fun i => ((v3 a0' b0' i).1, (v3 a0' b0' i).2.1, (v3 a0' b0' i).2.2, x.2.2.2))
        · intro i; rcases v3_mem hle0 i with ⟨m0, m1, m2⟩; exact ⟨m0, m1, m2, ⟨hx3a, hx3b⟩⟩
        · refine Prod.ext (bary3_id0 hba0) (Prod.ext (bary3_id1 hba0) (Prod.ext (bary3_id2 hba0) (bary3_const hba0)))
      have s2 : ∀ i : Fin 4, f ((v3 a0' b0' i).1, (v3 a0' b0' i).2.1, (v3 a0' b0' i).2.2, x.2.2.2) ≤
          ∑ e : Bool, w1 a1' b1' e x.2.2.2 *
            f ((v3 a0' b0' i).1, (v3 a0' b0' i).2.1, (v3 a0' b0' i).2.2, v1 a1' b1' e) := by
        intro i; rcases v3_mem hle0 i with ⟨m0, m1, m2⟩
        apply convex_bary1_coord hconv hlt1 ⟨hx3a, hx3b⟩
          (q := fun e => ((v3 a0' b0' i).1, (v3 a0' b0' i).2.1, (v3 a0' b0' i).2.2, v1 a1' b1' e))
        · intro e; exact ⟨m0, m1, m2, v1_mem hle1 e⟩
        · refine Prod.ext (bary1_const hba1) (Prod.ext (bary1_const hba1) (Prod.ext (bary1_const hba1) (bary1_id hba1)))
      calc f x ≤ _ := s1
        _ ≤ ∑ i : Fin 4, w3 a0' b0' i x.1 x.2.1 x.2.2.1 *
              (∑ e : Bool, w1 a1' b1' e x.2.2.2 *
                f ((v3 a0' b0' i).1, (v3 a0' b0' i).2.1, (v3 a0' b0' i).2.2, v1 a1' b1' e)) :=
            Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (s2 i) (w3_nonneg hlt0 hx0 hx01 hx12 hx2 i))
        _ = _ := by
            simp_rw [Finset.mul_sum]; rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ => by ring
    have hcw : ∀ (i : Fin 4) (e : Bool), Continuous (fun x : R4 =>
        w3 a0' b0' i x.1 x.2.1 x.2.2.1 * w1 a1' b1' e x.2.2.2) :=
      fun i e => ((w3_cont a0' b0' i).comp (hc0.prodMk (hc1.prodMk hc2))).mul ((w1_cont a1' b1' e).comp hc3)
    have hcont_w : ∀ p : Fin 4 × Bool, Continuous (fun x : R4 =>
        (w3 a0' b0' p.1 x.1 x.2.1 x.2.2.1 * w1 a1' b1' p.2 x.2.2.2) *
        f ((v3 a0' b0' p.1).1, (v3 a0' b0' p.1).2.1, (v3 a0' b0' p.1).2.2, v1 a1' b1' p.2)) :=
      fun p => (hcw p.1 p.2).mul continuous_const
    have hmono := setIntegral_mono_on hint_f
      ((continuous_finsetSum _ fun p _ => hcont_w p).continuousOn.integrableOn_compact (Cell4.c31 a0 b0 a1 b1).isCompact_set)
      (Cell4.c31 a0 b0 a1 b1).measurableSet_set hpt
    rw [integral_finsetSum _ (fun p _ => (hcont_w p).continuousOn.integrableOn_compact (Cell4.c31 a0 b0 a1 b1).isCompact_set)] at hmono
    have hterm : ∀ p : Fin 4 × Bool,
        ∫ x in (Cell4.c31 a0 b0 a1 b1).set,
          (w3 a0' b0' p.1 x.1 x.2.1 x.2.2.1 * w1 a1' b1' p.2 x.2.2.2) *
          f ((v3 a0' b0' p.1).1, (v3 a0' b0' p.1).2.1, (v3 a0' b0' p.1).2.2, v1 a1' b1' p.2) =
          (b0' - a0') ^ 3 * (b1' - a1') / 48 *
          f ((v3 a0' b0' p.1).1, (v3 a0' b0' p.1).2.1, (v3 a0' b0' p.1).2.2, v1 a1' b1' p.2) := by
      rintro ⟨i, e⟩
      rw [integral_mul_const, c31_set_eq, setIntegral_cell4SetGen hle0 hle0 hle0 hle1
        (fun _ => ⟨le_refl _, le_refl _⟩) (fun _ => ⟨le_refl _, le_refl _⟩) (by simp) (hcw i e)]
      simp only [↓reduceIte, Bool.false_eq_true, intervalIntegral.integral_const_mul, iter_w1 hlt1 e,
        intervalIntegral.integral_mul_const, iter_w3 hlt0 i]
      ring
    simp_rw [hterm] at hmono
    rw [Fintype.sum_prod_type_right] at hmono
    simp only [Fintype.sum_bool, Fin.sum_univ_four, v3, v1, vertSumReal] at hmono ⊢
    refine le_trans hmono (le_of_eq ?_); ring
  | c13 a0 b0 a1 b1 =>
    rcases hv with ⟨_, h0, _, h1⟩
    set a0' := gval a0; set b0' := gval b0; set a1' := gval a1; set b1' := gval b1
    have hlt0 : a0' < b0' := gval_lt h0; have hlt1 : a1' < b1' := gval_lt h1
    have hle0 : a0' ≤ b0' := le_of_lt hlt0; have hle1 : a1' ≤ b1' := le_of_lt hlt1
    have hba0 : b0' - a0' ≠ 0 := ne_of_gt (sub_pos.mpr hlt0)
    have hba1 : b1' - a1' ≠ 0 := ne_of_gt (sub_pos.mpr hlt1)
    have hpt : ∀ x ∈ (Cell4.c13 a0 b0 a1 b1).set,
        f x ≤ ∑ p : Bool × Fin 4,
          (w1 a0' b0' p.1 x.1 * w3 a1' b1' p.2 x.2.1 x.2.2.1 x.2.2.2) *
          f (v1 a0' b0' p.1, (v3 a1' b1' p.2).1, (v3 a1' b1' p.2).2.1, (v3 a1' b1' p.2).2.2) := by
      intro x hx; rcases hx with ⟨hx0a, hx0b, hx1, hx12, hx23, hx3⟩
      have s1 : f x ≤ ∑ e : Bool, w1 a0' b0' e x.1 * f (v1 a0' b0' e, x.2.1, x.2.2.1, x.2.2.2) := by
        apply convex_bary1_coord hconv hlt0 ⟨hx0a, hx0b⟩
          (q := fun e => (v1 a0' b0' e, x.2.1, x.2.2.1, x.2.2.2))
        · intro e; exact ⟨v1_mem hle0 e, ⟨hx1, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, hx3⟩⟩
        · refine Prod.ext (bary1_id hba0) (Prod.ext (bary1_const hba0) (Prod.ext (bary1_const hba0) (bary1_const hba0)))
      have s2 : ∀ e : Bool, f (v1 a0' b0' e, x.2.1, x.2.2.1, x.2.2.2) ≤
          ∑ i : Fin 4, w3 a1' b1' i x.2.1 x.2.2.1 x.2.2.2 *
            f (v1 a0' b0' e, (v3 a1' b1' i).1, (v3 a1' b1' i).2.1, (v3 a1' b1' i).2.2) := by
        intro e
        apply convex_bary3_coord hconv hlt1 hx1 hx12 hx23 hx3
          (q := fun i => (v1 a0' b0' e, (v3 a1' b1' i).1, (v3 a1' b1' i).2.1, (v3 a1' b1' i).2.2))
        · intro i; rcases v3_mem hle1 i with ⟨m0, m1, m2⟩; exact ⟨v1_mem hle0 e, m0, m1, m2⟩
        · refine Prod.ext (bary3_const hba1) (Prod.ext (bary3_id0 hba1) (Prod.ext (bary3_id1 hba1) (bary3_id2 hba1)))
      calc f x ≤ _ := s1
        _ ≤ ∑ e : Bool, w1 a0' b0' e x.1 *
              (∑ i : Fin 4, w3 a1' b1' i x.2.1 x.2.2.1 x.2.2.2 *
                f (v1 a0' b0' e, (v3 a1' b1' i).1, (v3 a1' b1' i).2.1, (v3 a1' b1' i).2.2)) :=
            Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (s2 e) (w1_nonneg hlt0 ⟨hx0a, hx0b⟩ e))
        _ = _ := by
            simp_rw [Finset.mul_sum]; rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => by ring
    have hcw : ∀ (e : Bool) (i : Fin 4), Continuous (fun x : R4 =>
        w1 a0' b0' e x.1 * w3 a1' b1' i x.2.1 x.2.2.1 x.2.2.2) :=
      fun e i => ((w1_cont a0' b0' e).comp hc0).mul ((w3_cont a1' b1' i).comp (hc1.prodMk (hc2.prodMk hc3)))
    have hcont_w : ∀ p : Bool × Fin 4, Continuous (fun x : R4 =>
        (w1 a0' b0' p.1 x.1 * w3 a1' b1' p.2 x.2.1 x.2.2.1 x.2.2.2) *
        f (v1 a0' b0' p.1, (v3 a1' b1' p.2).1, (v3 a1' b1' p.2).2.1, (v3 a1' b1' p.2).2.2)) :=
      fun p => (hcw p.1 p.2).mul continuous_const
    have hmono := setIntegral_mono_on hint_f
      ((continuous_finsetSum _ fun p _ => hcont_w p).continuousOn.integrableOn_compact (Cell4.c13 a0 b0 a1 b1).isCompact_set)
      (Cell4.c13 a0 b0 a1 b1).measurableSet_set hpt
    rw [integral_finsetSum _ (fun p _ => (hcont_w p).continuousOn.integrableOn_compact (Cell4.c13 a0 b0 a1 b1).isCompact_set)] at hmono
    have hterm : ∀ p : Bool × Fin 4,
        ∫ x in (Cell4.c13 a0 b0 a1 b1).set,
          (w1 a0' b0' p.1 x.1 * w3 a1' b1' p.2 x.2.1 x.2.2.1 x.2.2.2) *
          f (v1 a0' b0' p.1, (v3 a1' b1' p.2).1, (v3 a1' b1' p.2).2.1, (v3 a1' b1' p.2).2.2) =
          (b0' - a0') * (b1' - a1') ^ 3 / 48 *
          f (v1 a0' b0' p.1, (v3 a1' b1' p.2).1, (v3 a1' b1' p.2).2.1, (v3 a1' b1' p.2).2.2) := by
      rintro ⟨e, i⟩
      rw [integral_mul_const, c13_set_eq, setIntegral_cell4SetGen hle0 hle1 hle1 hle1
        (by simp) (fun _ => ⟨le_refl _, le_refl _⟩) (fun _ => ⟨le_refl _, le_refl _⟩) (hcw e i)]
      simp only [↓reduceIte, Bool.false_eq_true, intervalIntegral.integral_const_mul, iter_w3 hlt1 i,
        intervalIntegral.integral_mul_const, iter_w1 hlt0 e]
      ring
    simp_rw [hterm] at hmono
    rw [Fintype.sum_prod_type] at hmono
    simp only [Fintype.sum_bool, Fin.sum_univ_four, v3, v1, vertSumReal] at hmono ⊢
    refine le_trans hmono (le_of_eq ?_); ring
  | c22 a0 b0 a1 b1 =>
    rcases hv with ⟨_, h0, _, h1⟩
    set a0' := gval a0; set b0' := gval b0; set a1' := gval a1; set b1' := gval b1
    have hlt0 : a0' < b0' := gval_lt h0; have hlt1 : a1' < b1' := gval_lt h1
    have hle0 : a0' ≤ b0' := le_of_lt hlt0; have hle1 : a1' ≤ b1' := le_of_lt hlt1
    have hba0 : b0' - a0' ≠ 0 := ne_of_gt (sub_pos.mpr hlt0)
    have hba1 : b1' - a1' ≠ 0 := ne_of_gt (sub_pos.mpr hlt1)
    have hpt : ∀ x ∈ (Cell4.c22 a0 b0 a1 b1).set,
        f x ≤ ∑ p : Fin 3 × Fin 3,
          (w2 a0' b0' p.1 x.1 x.2.1 * w2 a1' b1' p.2 x.2.2.1 x.2.2.2) *
          f ((v2 a0' b0' p.1).1, (v2 a0' b0' p.1).2, (v2 a1' b1' p.2).1, (v2 a1' b1' p.2).2) := by
      intro x hx; rcases hx with ⟨hx0, hx01, hx1, hx2, hx23, hx3⟩
      have s1 : f x ≤ ∑ i : Fin 3, w2 a0' b0' i x.1 x.2.1 *
          f ((v2 a0' b0' i).1, (v2 a0' b0' i).2, x.2.2.1, x.2.2.2) := by
        apply convex_bary2_coord hconv hlt0 hx0 hx01 hx1
          (q := fun i => ((v2 a0' b0' i).1, (v2 a0' b0' i).2, x.2.2.1, x.2.2.2))
        · intro i; rcases v2_mem hle0 i with ⟨n0, n1⟩; exact ⟨n0, n1, ⟨hx2, by linarith⟩, ⟨by linarith, hx3⟩⟩
        · refine Prod.ext (bary2_id0 hba0) (Prod.ext (bary2_id1 hba0) (Prod.ext (bary2_const hba0) (bary2_const hba0)))
      have s2 : ∀ i : Fin 3, f ((v2 a0' b0' i).1, (v2 a0' b0' i).2, x.2.2.1, x.2.2.2) ≤
          ∑ j : Fin 3, w2 a1' b1' j x.2.2.1 x.2.2.2 *
            f ((v2 a0' b0' i).1, (v2 a0' b0' i).2, (v2 a1' b1' j).1, (v2 a1' b1' j).2) := by
        intro i; rcases v2_mem hle0 i with ⟨n0, n1⟩
        apply convex_bary2_coord hconv hlt1 hx2 hx23 hx3
          (q := fun j => ((v2 a0' b0' i).1, (v2 a0' b0' i).2, (v2 a1' b1' j).1, (v2 a1' b1' j).2))
        · intro j; rcases v2_mem hle1 j with ⟨m0, m1⟩; exact ⟨n0, n1, m0, m1⟩
        · refine Prod.ext (bary2_const hba1) (Prod.ext (bary2_const hba1) (Prod.ext (bary2_id0 hba1) (bary2_id1 hba1)))
      calc f x ≤ _ := s1
        _ ≤ ∑ i : Fin 3, w2 a0' b0' i x.1 x.2.1 *
              (∑ j : Fin 3, w2 a1' b1' j x.2.2.1 x.2.2.2 *
                f ((v2 a0' b0' i).1, (v2 a0' b0' i).2, (v2 a1' b1' j).1, (v2 a1' b1' j).2)) :=
            Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (s2 i) (w2_nonneg hlt0 hx0 hx01 hx1 i))
        _ = _ := by
            simp_rw [Finset.mul_sum]; rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hcw : ∀ (i j : Fin 3), Continuous (fun x : R4 =>
        w2 a0' b0' i x.1 x.2.1 * w2 a1' b1' j x.2.2.1 x.2.2.2) :=
      fun i j => ((w2_cont a0' b0' i).comp (hc0.prodMk hc1)).mul ((w2_cont a1' b1' j).comp (hc2.prodMk hc3))
    have hcont_w : ∀ p : Fin 3 × Fin 3, Continuous (fun x : R4 =>
        (w2 a0' b0' p.1 x.1 x.2.1 * w2 a1' b1' p.2 x.2.2.1 x.2.2.2) *
        f ((v2 a0' b0' p.1).1, (v2 a0' b0' p.1).2, (v2 a1' b1' p.2).1, (v2 a1' b1' p.2).2)) :=
      fun p => (hcw p.1 p.2).mul continuous_const
    have hmono := setIntegral_mono_on hint_f
      ((continuous_finsetSum _ fun p _ => hcont_w p).continuousOn.integrableOn_compact (Cell4.c22 a0 b0 a1 b1).isCompact_set)
      (Cell4.c22 a0 b0 a1 b1).measurableSet_set hpt
    rw [integral_finsetSum _ (fun p _ => (hcont_w p).continuousOn.integrableOn_compact (Cell4.c22 a0 b0 a1 b1).isCompact_set)] at hmono
    have hterm : ∀ p : Fin 3 × Fin 3,
        ∫ x in (Cell4.c22 a0 b0 a1 b1).set,
          (w2 a0' b0' p.1 x.1 x.2.1 * w2 a1' b1' p.2 x.2.2.1 x.2.2.2) *
          f ((v2 a0' b0' p.1).1, (v2 a0' b0' p.1).2, (v2 a1' b1' p.2).1, (v2 a1' b1' p.2).2) =
          (b0' - a0') ^ 2 * (b1' - a1') ^ 2 / 36 *
          f ((v2 a0' b0' p.1).1, (v2 a0' b0' p.1).2, (v2 a1' b1' p.2).1, (v2 a1' b1' p.2).2) := by
      rintro ⟨i, j⟩
      rw [integral_mul_const, c22_set_eq, setIntegral_cell4SetGen hle0 hle0 hle1 hle1
        (fun _ => ⟨le_refl _, le_refl _⟩) (by simp) (fun _ => ⟨le_refl _, le_refl _⟩) (hcw i j)]
      simp only [↓reduceIte, Bool.false_eq_true, intervalIntegral.integral_const_mul, iter_w2 hlt1 j,
        intervalIntegral.integral_mul_const, iter_w2 hlt0 i]
      ring
    simp_rw [hterm] at hmono
    rw [Fintype.sum_prod_type] at hmono
    simp only [Fin.sum_univ_three, v2, vertSumReal] at hmono ⊢
    refine le_trans hmono (le_of_eq ?_); ring
  | c211 a0 b0 a1 b1 a2 b2 =>
    rcases hv with ⟨_, h0, _, h1, _, h2⟩
    set a0' := gval a0; set b0' := gval b0; set a1' := gval a1; set b1' := gval b1; set a2' := gval a2; set b2' := gval b2
    have hlt0 : a0' < b0' := gval_lt h0; have hlt1 : a1' < b1' := gval_lt h1; have hlt2 : a2' < b2' := gval_lt h2
    have hle0 : a0' ≤ b0' := le_of_lt hlt0; have hle1 : a1' ≤ b1' := le_of_lt hlt1; have hle2 : a2' ≤ b2' := le_of_lt hlt2
    have hba0 : b0' - a0' ≠ 0 := ne_of_gt (sub_pos.mpr hlt0)
    have hba1 : b1' - a1' ≠ 0 := ne_of_gt (sub_pos.mpr hlt1)
    have hba2 : b2' - a2' ≠ 0 := ne_of_gt (sub_pos.mpr hlt2)
    have hpt : ∀ x ∈ (Cell4.c211 a0 b0 a1 b1 a2 b2).set,
        f x ≤ ∑ p : Fin 3 × Bool × Bool,
          (w2 a0' b0' p.1 x.1 x.2.1 * (w1 a1' b1' p.2.1 x.2.2.1 * w1 a2' b2' p.2.2 x.2.2.2)) *
          f ((v2 a0' b0' p.1).1, (v2 a0' b0' p.1).2, v1 a1' b1' p.2.1, v1 a2' b2' p.2.2) := by
      intro x hx; rcases hx with ⟨hx0, hx01, hx1, hx2a, hx2b, hx3a, hx3b⟩
      have s1 : f x ≤ ∑ i : Fin 3, w2 a0' b0' i x.1 x.2.1 *
          f ((v2 a0' b0' i).1, (v2 a0' b0' i).2, x.2.2.1, x.2.2.2) := by
        apply convex_bary2_coord hconv hlt0 hx0 hx01 hx1
          (q := fun i => ((v2 a0' b0' i).1, (v2 a0' b0' i).2, x.2.2.1, x.2.2.2))
        · intro i; rcases v2_mem hle0 i with ⟨n0, n1⟩; exact ⟨n0, n1, ⟨hx2a, hx2b⟩, ⟨hx3a, hx3b⟩⟩
        · refine Prod.ext (bary2_id0 hba0) (Prod.ext (bary2_id1 hba0) (Prod.ext (bary2_const hba0) (bary2_const hba0)))
      have s2 : ∀ i : Fin 3, f ((v2 a0' b0' i).1, (v2 a0' b0' i).2, x.2.2.1, x.2.2.2) ≤
          ∑ e1 : Bool, w1 a1' b1' e1 x.2.2.1 *
            f ((v2 a0' b0' i).1, (v2 a0' b0' i).2, v1 a1' b1' e1, x.2.2.2) := by
        intro i; rcases v2_mem hle0 i with ⟨n0, n1⟩
        apply convex_bary1_coord hconv hlt1 ⟨hx2a, hx2b⟩
          (q := fun e1 => ((v2 a0' b0' i).1, (v2 a0' b0' i).2, v1 a1' b1' e1, x.2.2.2))
        · intro e1; exact ⟨n0, n1, v1_mem hle1 e1, ⟨hx3a, hx3b⟩⟩
        · refine Prod.ext (bary1_const hba1) (Prod.ext (bary1_const hba1) (Prod.ext (bary1_id hba1) (bary1_const hba1)))
      have s3 : ∀ (i : Fin 3) (e1 : Bool), f ((v2 a0' b0' i).1, (v2 a0' b0' i).2, v1 a1' b1' e1, x.2.2.2) ≤
          ∑ e2 : Bool, w1 a2' b2' e2 x.2.2.2 *
            f ((v2 a0' b0' i).1, (v2 a0' b0' i).2, v1 a1' b1' e1, v1 a2' b2' e2) := by
        intro i e1; rcases v2_mem hle0 i with ⟨n0, n1⟩
        apply convex_bary1_coord hconv hlt2 ⟨hx3a, hx3b⟩
          (q := fun e2 => ((v2 a0' b0' i).1, (v2 a0' b0' i).2, v1 a1' b1' e1, v1 a2' b2' e2))
        · intro e2; exact ⟨n0, n1, v1_mem hle1 e1, v1_mem hle2 e2⟩
        · refine Prod.ext (bary1_const hba2) (Prod.ext (bary1_const hba2) (Prod.ext (bary1_const hba2) (bary1_id hba2)))
      calc f x ≤ _ := s1
        _ ≤ ∑ i : Fin 3, w2 a0' b0' i x.1 x.2.1 *
              (∑ e1 : Bool, w1 a1' b1' e1 x.2.2.1 *
                (∑ e2 : Bool, w1 a2' b2' e2 x.2.2.2 *
                  f ((v2 a0' b0' i).1, (v2 a0' b0' i).2, v1 a1' b1' e1, v1 a2' b2' e2))) := by
            refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (w2_nonneg hlt0 hx0 hx01 hx1 i)
            exact le_trans (s2 i) (Finset.sum_le_sum fun e1 _ =>
              mul_le_mul_of_nonneg_left (s3 i e1) (w1_nonneg hlt1 ⟨hx2a, hx2b⟩ e1))
        _ = _ := by
            simp_rw [Finset.mul_sum, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e1 _ =>
              Finset.sum_congr rfl fun e2 _ => by ring
    have hcw : ∀ (i : Fin 3) (e1 e2 : Bool), Continuous (fun x : R4 =>
        w2 a0' b0' i x.1 x.2.1 * (w1 a1' b1' e1 x.2.2.1 * w1 a2' b2' e2 x.2.2.2)) :=
      fun i e1 e2 => ((w2_cont a0' b0' i).comp (hc0.prodMk hc1)).mul
        (((w1_cont a1' b1' e1).comp hc2).mul ((w1_cont a2' b2' e2).comp hc3))
    have hcont_w : ∀ p : Fin 3 × Bool × Bool, Continuous (fun x : R4 =>
        (w2 a0' b0' p.1 x.1 x.2.1 * (w1 a1' b1' p.2.1 x.2.2.1 * w1 a2' b2' p.2.2 x.2.2.2)) *
        f ((v2 a0' b0' p.1).1, (v2 a0' b0' p.1).2, v1 a1' b1' p.2.1, v1 a2' b2' p.2.2)) :=
      fun p => (hcw p.1 p.2.1 p.2.2).mul continuous_const
    have hmono := setIntegral_mono_on hint_f
      ((continuous_finsetSum _ fun p _ => hcont_w p).continuousOn.integrableOn_compact (Cell4.c211 a0 b0 a1 b1 a2 b2).isCompact_set)
      (Cell4.c211 a0 b0 a1 b1 a2 b2).measurableSet_set hpt
    rw [integral_finsetSum _ (fun p _ => (hcont_w p).continuousOn.integrableOn_compact (Cell4.c211 a0 b0 a1 b1 a2 b2).isCompact_set)] at hmono
    have hterm : ∀ p : Fin 3 × Bool × Bool,
        ∫ x in (Cell4.c211 a0 b0 a1 b1 a2 b2).set,
          (w2 a0' b0' p.1 x.1 x.2.1 * (w1 a1' b1' p.2.1 x.2.2.1 * w1 a2' b2' p.2.2 x.2.2.2)) *
          f ((v2 a0' b0' p.1).1, (v2 a0' b0' p.1).2, v1 a1' b1' p.2.1, v1 a2' b2' p.2.2) =
          (b0' - a0') ^ 2 * (b1' - a1') * (b2' - a2') / 24 *
          f ((v2 a0' b0' p.1).1, (v2 a0' b0' p.1).2, v1 a1' b1' p.2.1, v1 a2' b2' p.2.2) := by
      rintro ⟨i, e1, e2⟩
      rw [integral_mul_const, c211_set_eq, setIntegral_cell4SetGen hle0 hle0 hle1 hle2
        (fun _ => ⟨le_refl _, le_refl _⟩) (by simp) (by simp) (hcw i e1 e2)]
      simp only [↓reduceIte, Bool.false_eq_true, intervalIntegral.integral_const_mul, iter_w1 hlt2 e2,
        intervalIntegral.integral_mul_const, iter_w1 hlt1 e1, iter_w2 hlt0 i]
      ring
    simp_rw [hterm] at hmono
    simp_rw [Fintype.sum_prod_type] at hmono
    simp only [Fin.sum_univ_three, Fintype.sum_bool, v2, v1, vertSumReal] at hmono ⊢
    refine le_trans hmono (le_of_eq ?_); ring
  | c121 a0 b0 a1 b1 a2 b2 =>
    rcases hv with ⟨_, h0, _, h1, _, h2⟩
    set a0' := gval a0; set b0' := gval b0; set a1' := gval a1; set b1' := gval b1; set a2' := gval a2; set b2' := gval b2
    have hlt0 : a0' < b0' := gval_lt h0; have hlt1 : a1' < b1' := gval_lt h1; have hlt2 : a2' < b2' := gval_lt h2
    have hle0 : a0' ≤ b0' := le_of_lt hlt0; have hle1 : a1' ≤ b1' := le_of_lt hlt1; have hle2 : a2' ≤ b2' := le_of_lt hlt2
    have hba0 : b0' - a0' ≠ 0 := ne_of_gt (sub_pos.mpr hlt0)
    have hba1 : b1' - a1' ≠ 0 := ne_of_gt (sub_pos.mpr hlt1)
    have hba2 : b2' - a2' ≠ 0 := ne_of_gt (sub_pos.mpr hlt2)
    have hpt : ∀ x ∈ (Cell4.c121 a0 b0 a1 b1 a2 b2).set,
        f x ≤ ∑ p : Bool × Fin 3 × Bool,
          (w1 a0' b0' p.1 x.1 * (w2 a1' b1' p.2.1 x.2.1 x.2.2.1 * w1 a2' b2' p.2.2 x.2.2.2)) *
          f (v1 a0' b0' p.1, (v2 a1' b1' p.2.1).1, (v2 a1' b1' p.2.1).2, v1 a2' b2' p.2.2) := by
      intro x hx; rcases hx with ⟨hx0a, hx0b, hx1, hx12, hx2, hx3a, hx3b⟩
      have s1 : f x ≤ ∑ e0 : Bool, w1 a0' b0' e0 x.1 * f (v1 a0' b0' e0, x.2.1, x.2.2.1, x.2.2.2) := by
        apply convex_bary1_coord hconv hlt0 ⟨hx0a, hx0b⟩
          (q := fun e0 => (v1 a0' b0' e0, x.2.1, x.2.2.1, x.2.2.2))
        · intro e0; exact ⟨v1_mem hle0 e0, ⟨hx1, by linarith⟩, ⟨by linarith, hx2⟩, ⟨hx3a, hx3b⟩⟩
        · refine Prod.ext (bary1_id hba0) (Prod.ext (bary1_const hba0) (Prod.ext (bary1_const hba0) (bary1_const hba0)))
      have s2 : ∀ e0 : Bool, f (v1 a0' b0' e0, x.2.1, x.2.2.1, x.2.2.2) ≤
          ∑ i : Fin 3, w2 a1' b1' i x.2.1 x.2.2.1 *
            f (v1 a0' b0' e0, (v2 a1' b1' i).1, (v2 a1' b1' i).2, x.2.2.2) := by
        intro e0
        apply convex_bary2_coord hconv hlt1 hx1 hx12 hx2
          (q := fun i => (v1 a0' b0' e0, (v2 a1' b1' i).1, (v2 a1' b1' i).2, x.2.2.2))
        · intro i; rcases v2_mem hle1 i with ⟨m0, m1⟩; exact ⟨v1_mem hle0 e0, m0, m1, ⟨hx3a, hx3b⟩⟩
        · refine Prod.ext (bary2_const hba1) (Prod.ext (bary2_id0 hba1) (Prod.ext (bary2_id1 hba1) (bary2_const hba1)))
      have s3 : ∀ (e0 : Bool) (i : Fin 3), f (v1 a0' b0' e0, (v2 a1' b1' i).1, (v2 a1' b1' i).2, x.2.2.2) ≤
          ∑ e2 : Bool, w1 a2' b2' e2 x.2.2.2 *
            f (v1 a0' b0' e0, (v2 a1' b1' i).1, (v2 a1' b1' i).2, v1 a2' b2' e2) := by
        intro e0 i; rcases v2_mem hle1 i with ⟨m0, m1⟩
        apply convex_bary1_coord hconv hlt2 ⟨hx3a, hx3b⟩
          (q := fun e2 => (v1 a0' b0' e0, (v2 a1' b1' i).1, (v2 a1' b1' i).2, v1 a2' b2' e2))
        · intro e2; exact ⟨v1_mem hle0 e0, m0, m1, v1_mem hle2 e2⟩
        · refine Prod.ext (bary1_const hba2) (Prod.ext (bary1_const hba2) (Prod.ext (bary1_const hba2) (bary1_id hba2)))
      calc f x ≤ _ := s1
        _ ≤ ∑ e0 : Bool, w1 a0' b0' e0 x.1 *
              (∑ i : Fin 3, w2 a1' b1' i x.2.1 x.2.2.1 *
                (∑ e2 : Bool, w1 a2' b2' e2 x.2.2.2 *
                  f (v1 a0' b0' e0, (v2 a1' b1' i).1, (v2 a1' b1' i).2, v1 a2' b2' e2))) := by
            refine Finset.sum_le_sum fun e0 _ => mul_le_mul_of_nonneg_left ?_ (w1_nonneg hlt0 ⟨hx0a, hx0b⟩ e0)
            exact le_trans (s2 e0) (Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (s3 e0 i) (w2_nonneg hlt1 hx1 hx12 hx2 i))
        _ = _ := by
            simp_rw [Finset.mul_sum, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun e0 _ => Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun e2 _ => by ring
    have hcw : ∀ (e0 : Bool) (i : Fin 3) (e2 : Bool), Continuous (fun x : R4 =>
        w1 a0' b0' e0 x.1 * (w2 a1' b1' i x.2.1 x.2.2.1 * w1 a2' b2' e2 x.2.2.2)) :=
      fun e0 i e2 => ((w1_cont a0' b0' e0).comp hc0).mul
        (((w2_cont a1' b1' i).comp (hc1.prodMk hc2)).mul ((w1_cont a2' b2' e2).comp hc3))
    have hcont_w : ∀ p : Bool × Fin 3 × Bool, Continuous (fun x : R4 =>
        (w1 a0' b0' p.1 x.1 * (w2 a1' b1' p.2.1 x.2.1 x.2.2.1 * w1 a2' b2' p.2.2 x.2.2.2)) *
        f (v1 a0' b0' p.1, (v2 a1' b1' p.2.1).1, (v2 a1' b1' p.2.1).2, v1 a2' b2' p.2.2)) :=
      fun p => (hcw p.1 p.2.1 p.2.2).mul continuous_const
    have hmono := setIntegral_mono_on hint_f
      ((continuous_finsetSum _ fun p _ => hcont_w p).continuousOn.integrableOn_compact (Cell4.c121 a0 b0 a1 b1 a2 b2).isCompact_set)
      (Cell4.c121 a0 b0 a1 b1 a2 b2).measurableSet_set hpt
    rw [integral_finsetSum _ (fun p _ => (hcont_w p).continuousOn.integrableOn_compact (Cell4.c121 a0 b0 a1 b1 a2 b2).isCompact_set)] at hmono
    have hterm : ∀ p : Bool × Fin 3 × Bool,
        ∫ x in (Cell4.c121 a0 b0 a1 b1 a2 b2).set,
          (w1 a0' b0' p.1 x.1 * (w2 a1' b1' p.2.1 x.2.1 x.2.2.1 * w1 a2' b2' p.2.2 x.2.2.2)) *
          f (v1 a0' b0' p.1, (v2 a1' b1' p.2.1).1, (v2 a1' b1' p.2.1).2, v1 a2' b2' p.2.2) =
          (b0' - a0') * (b1' - a1') ^ 2 * (b2' - a2') / 24 *
          f (v1 a0' b0' p.1, (v2 a1' b1' p.2.1).1, (v2 a1' b1' p.2.1).2, v1 a2' b2' p.2.2) := by
      rintro ⟨e0, i, e2⟩
      rw [integral_mul_const, c121_set_eq, setIntegral_cell4SetGen hle0 hle1 hle1 hle2
        (by simp) (fun _ => ⟨le_refl _, le_refl _⟩) (by simp) (hcw e0 i e2)]
      simp only [↓reduceIte, Bool.false_eq_true, intervalIntegral.integral_const_mul, iter_w1 hlt2 e2,
        intervalIntegral.integral_mul_const, iter_w2 hlt1 i, iter_w1 hlt0 e0]
      ring
    simp_rw [hterm] at hmono
    simp_rw [Fintype.sum_prod_type] at hmono
    simp only [Fin.sum_univ_three, Fintype.sum_bool, v2, v1, vertSumReal] at hmono ⊢
    refine le_trans hmono (le_of_eq ?_); ring
  | c112 a0 b0 a1 b1 a2 b2 =>
    rcases hv with ⟨_, h0, _, h1, _, h2⟩
    set a0' := gval a0; set b0' := gval b0; set a1' := gval a1; set b1' := gval b1; set a2' := gval a2; set b2' := gval b2
    have hlt0 : a0' < b0' := gval_lt h0; have hlt1 : a1' < b1' := gval_lt h1; have hlt2 : a2' < b2' := gval_lt h2
    have hle0 : a0' ≤ b0' := le_of_lt hlt0; have hle1 : a1' ≤ b1' := le_of_lt hlt1; have hle2 : a2' ≤ b2' := le_of_lt hlt2
    have hba0 : b0' - a0' ≠ 0 := ne_of_gt (sub_pos.mpr hlt0)
    have hba1 : b1' - a1' ≠ 0 := ne_of_gt (sub_pos.mpr hlt1)
    have hba2 : b2' - a2' ≠ 0 := ne_of_gt (sub_pos.mpr hlt2)
    have hpt : ∀ x ∈ (Cell4.c112 a0 b0 a1 b1 a2 b2).set,
        f x ≤ ∑ p : Bool × Bool × Fin 3,
          (w1 a0' b0' p.1 x.1 * (w1 a1' b1' p.2.1 x.2.1 * w2 a2' b2' p.2.2 x.2.2.1 x.2.2.2)) *
          f (v1 a0' b0' p.1, v1 a1' b1' p.2.1, (v2 a2' b2' p.2.2).1, (v2 a2' b2' p.2.2).2) := by
      intro x hx; rcases hx with ⟨hx0a, hx0b, hx1a, hx1b, hx2, hx23, hx3⟩
      have s1 : f x ≤ ∑ e0 : Bool, w1 a0' b0' e0 x.1 * f (v1 a0' b0' e0, x.2.1, x.2.2.1, x.2.2.2) := by
        apply convex_bary1_coord hconv hlt0 ⟨hx0a, hx0b⟩
          (q := fun e0 => (v1 a0' b0' e0, x.2.1, x.2.2.1, x.2.2.2))
        · intro e0; exact ⟨v1_mem hle0 e0, ⟨hx1a, hx1b⟩, ⟨hx2, by linarith⟩, ⟨by linarith, hx3⟩⟩
        · refine Prod.ext (bary1_id hba0) (Prod.ext (bary1_const hba0) (Prod.ext (bary1_const hba0) (bary1_const hba0)))
      have s2 : ∀ e0 : Bool, f (v1 a0' b0' e0, x.2.1, x.2.2.1, x.2.2.2) ≤
          ∑ e1 : Bool, w1 a1' b1' e1 x.2.1 * f (v1 a0' b0' e0, v1 a1' b1' e1, x.2.2.1, x.2.2.2) := by
        intro e0
        apply convex_bary1_coord hconv hlt1 ⟨hx1a, hx1b⟩
          (q := fun e1 => (v1 a0' b0' e0, v1 a1' b1' e1, x.2.2.1, x.2.2.2))
        · intro e1; exact ⟨v1_mem hle0 e0, v1_mem hle1 e1, ⟨hx2, by linarith⟩, ⟨by linarith, hx3⟩⟩
        · refine Prod.ext (bary1_const hba1) (Prod.ext (bary1_id hba1) (Prod.ext (bary1_const hba1) (bary1_const hba1)))
      have s3 : ∀ (e0 e1 : Bool), f (v1 a0' b0' e0, v1 a1' b1' e1, x.2.2.1, x.2.2.2) ≤
          ∑ i : Fin 3, w2 a2' b2' i x.2.2.1 x.2.2.2 *
            f (v1 a0' b0' e0, v1 a1' b1' e1, (v2 a2' b2' i).1, (v2 a2' b2' i).2) := by
        intro e0 e1
        apply convex_bary2_coord hconv hlt2 hx2 hx23 hx3
          (q := fun i => (v1 a0' b0' e0, v1 a1' b1' e1, (v2 a2' b2' i).1, (v2 a2' b2' i).2))
        · intro i; rcases v2_mem hle2 i with ⟨m0, m1⟩; exact ⟨v1_mem hle0 e0, v1_mem hle1 e1, m0, m1⟩
        · refine Prod.ext (bary2_const hba2) (Prod.ext (bary2_const hba2) (Prod.ext (bary2_id0 hba2) (bary2_id1 hba2)))
      calc f x ≤ _ := s1
        _ ≤ ∑ e0 : Bool, w1 a0' b0' e0 x.1 *
              (∑ e1 : Bool, w1 a1' b1' e1 x.2.1 *
                (∑ i : Fin 3, w2 a2' b2' i x.2.2.1 x.2.2.2 *
                  f (v1 a0' b0' e0, v1 a1' b1' e1, (v2 a2' b2' i).1, (v2 a2' b2' i).2))) := by
            refine Finset.sum_le_sum fun e0 _ => mul_le_mul_of_nonneg_left ?_ (w1_nonneg hlt0 ⟨hx0a, hx0b⟩ e0)
            exact le_trans (s2 e0) (Finset.sum_le_sum fun e1 _ =>
              mul_le_mul_of_nonneg_left (s3 e0 e1) (w1_nonneg hlt1 ⟨hx1a, hx1b⟩ e1))
        _ = _ := by
            simp_rw [Finset.mul_sum, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun e0 _ => Finset.sum_congr rfl fun e1 _ =>
              Finset.sum_congr rfl fun i _ => by ring
    have hcw : ∀ (e0 e1 : Bool) (i : Fin 3), Continuous (fun x : R4 =>
        w1 a0' b0' e0 x.1 * (w1 a1' b1' e1 x.2.1 * w2 a2' b2' i x.2.2.1 x.2.2.2)) :=
      fun e0 e1 i => ((w1_cont a0' b0' e0).comp hc0).mul
        (((w1_cont a1' b1' e1).comp hc1).mul ((w2_cont a2' b2' i).comp (hc2.prodMk hc3)))
    have hcont_w : ∀ p : Bool × Bool × Fin 3, Continuous (fun x : R4 =>
        (w1 a0' b0' p.1 x.1 * (w1 a1' b1' p.2.1 x.2.1 * w2 a2' b2' p.2.2 x.2.2.1 x.2.2.2)) *
        f (v1 a0' b0' p.1, v1 a1' b1' p.2.1, (v2 a2' b2' p.2.2).1, (v2 a2' b2' p.2.2).2)) :=
      fun p => (hcw p.1 p.2.1 p.2.2).mul continuous_const
    have hmono := setIntegral_mono_on hint_f
      ((continuous_finsetSum _ fun p _ => hcont_w p).continuousOn.integrableOn_compact (Cell4.c112 a0 b0 a1 b1 a2 b2).isCompact_set)
      (Cell4.c112 a0 b0 a1 b1 a2 b2).measurableSet_set hpt
    rw [integral_finsetSum _ (fun p _ => (hcont_w p).continuousOn.integrableOn_compact (Cell4.c112 a0 b0 a1 b1 a2 b2).isCompact_set)] at hmono
    have hterm : ∀ p : Bool × Bool × Fin 3,
        ∫ x in (Cell4.c112 a0 b0 a1 b1 a2 b2).set,
          (w1 a0' b0' p.1 x.1 * (w1 a1' b1' p.2.1 x.2.1 * w2 a2' b2' p.2.2 x.2.2.1 x.2.2.2)) *
          f (v1 a0' b0' p.1, v1 a1' b1' p.2.1, (v2 a2' b2' p.2.2).1, (v2 a2' b2' p.2.2).2) =
          (b0' - a0') * (b1' - a1') * (b2' - a2') ^ 2 / 24 *
          f (v1 a0' b0' p.1, v1 a1' b1' p.2.1, (v2 a2' b2' p.2.2).1, (v2 a2' b2' p.2.2).2) := by
      rintro ⟨e0, e1, i⟩
      rw [integral_mul_const, c112_set_eq, setIntegral_cell4SetGen hle0 hle1 hle2 hle2
        (by simp) (by simp) (fun _ => ⟨le_refl _, le_refl _⟩) (hcw e0 e1 i)]
      simp only [↓reduceIte, Bool.false_eq_true, intervalIntegral.integral_const_mul, iter_w2 hlt2 i,
        intervalIntegral.integral_mul_const, iter_w1 hlt1 e1, iter_w1 hlt0 e0]
      ring
    simp_rw [hterm] at hmono
    simp_rw [Fintype.sum_prod_type] at hmono
    simp only [Fin.sum_univ_three, Fintype.sum_bool, v2, v1, vertSumReal] at hmono ⊢
    refine le_trans hmono (le_of_eq ?_); ring
  | c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
    rcases hv with ⟨_, h0, _, h1, _, h2, _, h3⟩
    set a0' := gval a0; set b0' := gval b0; set a1' := gval a1; set b1' := gval b1
    set a2' := gval a2; set b2' := gval b2; set a3' := gval a3; set b3' := gval b3
    have hlt0 : a0' < b0' := gval_lt h0; have hlt1 : a1' < b1' := gval_lt h1
    have hlt2 : a2' < b2' := gval_lt h2; have hlt3 : a3' < b3' := gval_lt h3
    have hle0 : a0' ≤ b0' := le_of_lt hlt0; have hle1 : a1' ≤ b1' := le_of_lt hlt1
    have hle2 : a2' ≤ b2' := le_of_lt hlt2; have hle3 : a3' ≤ b3' := le_of_lt hlt3
    have hba0 : b0' - a0' ≠ 0 := ne_of_gt (sub_pos.mpr hlt0)
    have hba1 : b1' - a1' ≠ 0 := ne_of_gt (sub_pos.mpr hlt1)
    have hba2 : b2' - a2' ≠ 0 := ne_of_gt (sub_pos.mpr hlt2)
    have hba3 : b3' - a3' ≠ 0 := ne_of_gt (sub_pos.mpr hlt3)
    have hpt : ∀ x ∈ (Cell4.c1111 a0 b0 a1 b1 a2 b2 a3 b3).set,
        f x ≤ ∑ p : Bool × Bool × Bool × Bool,
          (w1 a0' b0' p.1 x.1 * (w1 a1' b1' p.2.1 x.2.1 * (w1 a2' b2' p.2.2.1 x.2.2.1 * w1 a3' b3' p.2.2.2 x.2.2.2))) *
          f (v1 a0' b0' p.1, v1 a1' b1' p.2.1, v1 a2' b2' p.2.2.1, v1 a3' b3' p.2.2.2) := by
      intro x hx; rcases hx with ⟨hx0a, hx0b, hx1a, hx1b, hx2a, hx2b, hx3a, hx3b⟩
      have s1 : f x ≤ ∑ e0 : Bool, w1 a0' b0' e0 x.1 * f (v1 a0' b0' e0, x.2.1, x.2.2.1, x.2.2.2) := by
        apply convex_bary1_coord hconv hlt0 ⟨hx0a, hx0b⟩
          (q := fun e0 => (v1 a0' b0' e0, x.2.1, x.2.2.1, x.2.2.2))
        · intro e0; exact ⟨v1_mem hle0 e0, ⟨hx1a, hx1b⟩, ⟨hx2a, hx2b⟩, ⟨hx3a, hx3b⟩⟩
        · refine Prod.ext (bary1_id hba0) (Prod.ext (bary1_const hba0) (Prod.ext (bary1_const hba0) (bary1_const hba0)))
      have s2 : ∀ e0 : Bool, f (v1 a0' b0' e0, x.2.1, x.2.2.1, x.2.2.2) ≤
          ∑ e1 : Bool, w1 a1' b1' e1 x.2.1 * f (v1 a0' b0' e0, v1 a1' b1' e1, x.2.2.1, x.2.2.2) := by
        intro e0
        apply convex_bary1_coord hconv hlt1 ⟨hx1a, hx1b⟩
          (q := fun e1 => (v1 a0' b0' e0, v1 a1' b1' e1, x.2.2.1, x.2.2.2))
        · intro e1; exact ⟨v1_mem hle0 e0, v1_mem hle1 e1, ⟨hx2a, hx2b⟩, ⟨hx3a, hx3b⟩⟩
        · refine Prod.ext (bary1_const hba1) (Prod.ext (bary1_id hba1) (Prod.ext (bary1_const hba1) (bary1_const hba1)))
      have s3 : ∀ e0 e1 : Bool, f (v1 a0' b0' e0, v1 a1' b1' e1, x.2.2.1, x.2.2.2) ≤
          ∑ e2 : Bool, w1 a2' b2' e2 x.2.2.1 * f (v1 a0' b0' e0, v1 a1' b1' e1, v1 a2' b2' e2, x.2.2.2) := by
        intro e0 e1
        apply convex_bary1_coord hconv hlt2 ⟨hx2a, hx2b⟩
          (q := fun e2 => (v1 a0' b0' e0, v1 a1' b1' e1, v1 a2' b2' e2, x.2.2.2))
        · intro e2; exact ⟨v1_mem hle0 e0, v1_mem hle1 e1, v1_mem hle2 e2, ⟨hx3a, hx3b⟩⟩
        · refine Prod.ext (bary1_const hba2) (Prod.ext (bary1_const hba2) (Prod.ext (bary1_id hba2) (bary1_const hba2)))
      have s4 : ∀ e0 e1 e2 : Bool, f (v1 a0' b0' e0, v1 a1' b1' e1, v1 a2' b2' e2, x.2.2.2) ≤
          ∑ e3 : Bool, w1 a3' b3' e3 x.2.2.2 * f (v1 a0' b0' e0, v1 a1' b1' e1, v1 a2' b2' e2, v1 a3' b3' e3) := by
        intro e0 e1 e2
        apply convex_bary1_coord hconv hlt3 ⟨hx3a, hx3b⟩
          (q := fun e3 => (v1 a0' b0' e0, v1 a1' b1' e1, v1 a2' b2' e2, v1 a3' b3' e3))
        · intro e3; exact ⟨v1_mem hle0 e0, v1_mem hle1 e1, v1_mem hle2 e2, v1_mem hle3 e3⟩
        · refine Prod.ext (bary1_const hba3) (Prod.ext (bary1_const hba3) (Prod.ext (bary1_const hba3) (bary1_id hba3)))
      calc f x ≤ _ := s1
        _ ≤ ∑ e0 : Bool, w1 a0' b0' e0 x.1 *
              (∑ e1 : Bool, w1 a1' b1' e1 x.2.1 *
                (∑ e2 : Bool, w1 a2' b2' e2 x.2.2.1 *
                  (∑ e3 : Bool, w1 a3' b3' e3 x.2.2.2 *
                    f (v1 a0' b0' e0, v1 a1' b1' e1, v1 a2' b2' e2, v1 a3' b3' e3)))) := by
            refine Finset.sum_le_sum fun e0 _ => mul_le_mul_of_nonneg_left ?_ (w1_nonneg hlt0 ⟨hx0a, hx0b⟩ e0)
            refine le_trans (s2 e0) (Finset.sum_le_sum fun e1 _ => mul_le_mul_of_nonneg_left ?_ (w1_nonneg hlt1 ⟨hx1a, hx1b⟩ e1))
            exact le_trans (s3 e0 e1) (Finset.sum_le_sum fun e2 _ =>
              mul_le_mul_of_nonneg_left (s4 e0 e1 e2) (w1_nonneg hlt2 ⟨hx2a, hx2b⟩ e2))
        _ = _ := by
            simp_rw [Finset.mul_sum, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun e0 _ => Finset.sum_congr rfl fun e1 _ =>
              Finset.sum_congr rfl fun e2 _ => Finset.sum_congr rfl fun e3 _ => by ring
    have hcw : ∀ (e0 e1 e2 e3 : Bool), Continuous (fun x : R4 =>
        w1 a0' b0' e0 x.1 * (w1 a1' b1' e1 x.2.1 * (w1 a2' b2' e2 x.2.2.1 * w1 a3' b3' e3 x.2.2.2))) :=
      fun e0 e1 e2 e3 => ((w1_cont a0' b0' e0).comp hc0).mul
        (((w1_cont a1' b1' e1).comp hc1).mul (((w1_cont a2' b2' e2).comp hc2).mul ((w1_cont a3' b3' e3).comp hc3)))
    have hcont_w : ∀ p : Bool × Bool × Bool × Bool, Continuous (fun x : R4 =>
        (w1 a0' b0' p.1 x.1 * (w1 a1' b1' p.2.1 x.2.1 * (w1 a2' b2' p.2.2.1 x.2.2.1 * w1 a3' b3' p.2.2.2 x.2.2.2))) *
        f (v1 a0' b0' p.1, v1 a1' b1' p.2.1, v1 a2' b2' p.2.2.1, v1 a3' b3' p.2.2.2)) :=
      fun p => (hcw p.1 p.2.1 p.2.2.1 p.2.2.2).mul continuous_const
    have hmono := setIntegral_mono_on hint_f
      ((continuous_finsetSum _ fun p _ => hcont_w p).continuousOn.integrableOn_compact (Cell4.c1111 a0 b0 a1 b1 a2 b2 a3 b3).isCompact_set)
      (Cell4.c1111 a0 b0 a1 b1 a2 b2 a3 b3).measurableSet_set hpt
    rw [integral_finsetSum _ (fun p _ => (hcont_w p).continuousOn.integrableOn_compact (Cell4.c1111 a0 b0 a1 b1 a2 b2 a3 b3).isCompact_set)] at hmono
    have hterm : ∀ p : Bool × Bool × Bool × Bool,
        ∫ x in (Cell4.c1111 a0 b0 a1 b1 a2 b2 a3 b3).set,
          (w1 a0' b0' p.1 x.1 * (w1 a1' b1' p.2.1 x.2.1 * (w1 a2' b2' p.2.2.1 x.2.2.1 * w1 a3' b3' p.2.2.2 x.2.2.2))) *
          f (v1 a0' b0' p.1, v1 a1' b1' p.2.1, v1 a2' b2' p.2.2.1, v1 a3' b3' p.2.2.2) =
          (b0' - a0') * (b1' - a1') * (b2' - a2') * (b3' - a3') / 16 *
          f (v1 a0' b0' p.1, v1 a1' b1' p.2.1, v1 a2' b2' p.2.2.1, v1 a3' b3' p.2.2.2) := by
      rintro ⟨e0, e1, e2, e3⟩
      rw [integral_mul_const, c1111_set_eq, setIntegral_cell4SetGen hle0 hle1 hle2 hle3
        (by simp) (by simp) (by simp) (hcw e0 e1 e2 e3)]
      simp only [↓reduceIte, Bool.false_eq_true, intervalIntegral.integral_const_mul, iter_w1 hlt3 e3,
        intervalIntegral.integral_mul_const, iter_w1 hlt2 e2, iter_w1 hlt1 e1, iter_w1 hlt0 e0]
      ring
    simp_rw [hterm] at hmono
    simp_rw [Fintype.sum_prod_type] at hmono
    simp only [Fintype.sum_bool, v1, vertSumReal] at hmono ⊢
    refine le_trans hmono (le_of_eq ?_); ring

/-! ### Part 4: Exact 4D Half-Space Volume, Boundary Boost, and Tree Soundness -/

private lemma integral_ind_le {h r : ℝ} (hh : 0 ≤ h) :
    ∫ y in (0 : ℝ)..h, (if y ≤ r then (1 : ℝ) else 0) = max 0 r - max 0 (r - h) := by
  rw [intervalIntegral.integral_of_le hh]
  have hfn : (fun y : ℝ => if y ≤ r then (1 : ℝ) else 0) = (Iic r).indicator (fun _ => (1 : ℝ)) := by
    ext y; simp [indicator, mem_Iic]
  rw [hfn, setIntegral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul, mul_one]
  have hinter : Ioc (0 : ℝ) h ∩ Iic r = Ioc 0 (min h r) := by
    ext y; simp only [mem_inter_iff, mem_Ioc, mem_Iic, le_min_iff]; tauto
  rw [hinter, Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal']
  rcases le_total r 0 with hr0 | hr0
  · have hm : min h r ≤ 0 := min_le_of_right_le hr0
    rw [max_eq_right hm, max_eq_left hr0, max_eq_left (by linarith : r - h ≤ 0)]; ring
  · rcases le_total r h with hrh | hrh
    · rw [min_eq_right hrh, max_eq_left hr0, max_eq_right hr0, max_eq_left (by linarith : r - h ≤ 0)]; ring
    · rw [min_eq_left hrh, max_eq_left hh, max_eq_right hr0, max_eq_right (by linarith : 0 ≤ r - h)]; ring

private lemma integral_sub_mul_const_pow (n : ℕ) {a b r c : ℝ} (hc : c ≠ 0) :
    ∫ y in a..b, (r - c * y) ^ (n + 1) =
      ((r - c * a) ^ (n + 2) - (r - c * b) ^ (n + 2)) / (c * (n + 2)) := by
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y => -((r - c * y) ^ (n + 2)) / (c * ((n : ℝ) + 2))) ((r - c * x) ^ (n + 1)) x := by
    intro x _
    have h1 : HasDerivAt (fun y => r - c * y) (-c) x := by
      have := ((hasDerivAt_id x).const_mul c).const_sub r
      simpa [mul_one] using this
    have h2 : HasDerivAt (fun y => -((r - c * y) ^ (n + 2)) / (c * ((n : ℝ) + 2)))
        (-(((n + 2 : ℕ) : ℝ) * (r - c * x) ^ (n + 2 - 1) * (-c)) / (c * ((n : ℝ) + 2))) x :=
      ((h1.pow (n + 2)).neg).div_const (c * ((n : ℝ) + 2))
    have heq : -(((n + 2 : ℕ) : ℝ) * (r - c * x) ^ (n + 2 - 1) * (-c)) / (c * ((n : ℝ) + 2)) =
        (r - c * x) ^ (n + 1) := by
      have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
      rw [show n + 2 - 1 = n + 1 by omega, Nat.cast_add, Nat.cast_ofNat]
      field_simp [hc, hn]
    rwa [heq] at h2
  have hcont : ContinuousOn (fun y : ℝ => (r - c * y) ^ (n + 1)) (uIcc a b) :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).pow (n + 1)).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  ring

private lemma integral_posPow_succ (n : ℕ) {h r c : ℝ} (hh : 0 ≤ h) (hc : 0 < c) :
    ∫ y in (0 : ℝ)..h, (max 0 (r - c * y)) ^ (n + 1) =
      ((max 0 r) ^ (n + 2) - (max 0 (r - c * h)) ^ (n + 2)) / (c * (n + 2)) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  by_cases hr0 : r ≤ 0
  · have hzero : ∀ y ∈ uIcc (0 : ℝ) h, (max 0 (r - c * y)) ^ (n + 1) = 0 := by
      intro y hy; rw [uIcc_of_le hh] at hy
      have : r - c * y ≤ 0 := by nlinarith [hy.1]
      rw [max_eq_left this, zero_pow (Nat.succ_ne_zero n)]
    rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero,
        max_eq_left hr0, max_eq_left (by nlinarith : r - c * h ≤ 0),
        zero_pow (by omega), sub_self, zero_div]
  · push Not at hr0
    by_cases hrh : c * h ≤ r
    · have hpos : ∀ y ∈ uIcc (0 : ℝ) h, (max 0 (r - c * y)) ^ (n + 1) = (r - c * y) ^ (n + 1) := by
        intro y hy; rw [uIcc_of_le hh] at hy
        rw [max_eq_right (by nlinarith [hy.2] : 0 ≤ r - c * y)]
      rw [intervalIntegral.integral_congr hpos, integral_sub_mul_const_pow n hcne, mul_zero, sub_zero,
          max_eq_right (le_of_lt hr0), max_eq_right (by linarith : 0 ≤ r - c * h)]
    · push Not at hrh
      set m := r / c
      have hm0 : 0 ≤ m := div_nonneg (le_of_lt hr0) (le_of_lt hc)
      have hmh : m ≤ h := (div_le_iff₀ hc).mpr (by linarith)
      have hcm : c * m = r := mul_div_cancel₀ r hcne
      have hint1 : IntervalIntegrable (fun y => (max 0 (r - c * y)) ^ (n + 1)) volume 0 m :=
        (by fun_prop : Continuous _).intervalIntegrable _ _
      have hint2 : IntervalIntegrable (fun y => (max 0 (r - c * y)) ^ (n + 1)) volume m h :=
        (by fun_prop : Continuous _).intervalIntegrable _ _
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
      have h1 : ∫ y in (0 : ℝ)..m, (max 0 (r - c * y)) ^ (n + 1) = r ^ (n + 2) / (c * (n + 2)) := by
        have hpos : ∀ y ∈ uIcc (0 : ℝ) m, (max 0 (r - c * y)) ^ (n + 1) = (r - c * y) ^ (n + 1) := by
          intro y hy; rw [uIcc_of_le hm0] at hy
          rw [max_eq_right (by nlinarith [hy.2] : 0 ≤ r - c * y)]
        rw [intervalIntegral.integral_congr hpos, integral_sub_mul_const_pow n hcne, mul_zero, sub_zero,
            hcm, sub_self, zero_pow (by omega), sub_zero]
      have h2 : ∫ y in m..h, (max 0 (r - c * y)) ^ (n + 1) = 0 := by
        have hzero : ∀ y ∈ uIcc m h, (max 0 (r - c * y)) ^ (n + 1) = 0 := by
          intro y hy; rw [uIcc_of_le hmh] at hy
          rw [max_eq_left (by nlinarith [hy.1] : r - c * y ≤ 0), zero_pow (Nat.succ_ne_zero n)]
        rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]
      rw [h1, h2, add_zero, max_eq_right (le_of_lt hr0), max_eq_left (by linarith : r - c * h ≤ 0),
          zero_pow (by omega), sub_zero]

private lemma posPow4_cast (R b : Nat) :
    ((posPow4 R b : Nat) : ℝ) / (D_grid : ℝ) ^ 4 = (max 0 (gval R - gval b)) ^ 4 := by
  unfold posPow4 gval
  cases h : Nat.ble b R with
  | true =>
    have hle : b ≤ R := Nat.ble_eq.mp h
    have hge : (0 : ℝ) ≤ (R : ℝ) / D_grid - (b : ℝ) / D_grid := by
      rw [← sub_div]; exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hle)) (le_of_lt hDpos)
    rw [max_eq_right hge, ← sub_div, ← Nat.cast_sub hle]
    push_cast; field_simp [ne_of_gt hDpos]
  | false =>
    have hlt : R < b := by
      have : ¬ b ≤ R := by intro hle; rw [Nat.ble_eq.mpr hle] at h; exact Bool.noConfusion h
      omega
    have hle : (R : ℝ) / D_grid - (b : ℝ) / D_grid ≤ 0 := by
      rw [← sub_div]; exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (by exact_mod_cast le_of_lt hlt)) (le_of_lt hDpos)
    rw [max_eq_left hle]; simp

private lemma volume_singleton_R4 (p : R4) : volume ({p} : Set R4) = 0 := by
  have heq : ({p} : Set R4) = {p.1} ×ˢ {p.2} := by ext x; simp [Prod.ext_iff]
  rw [heq, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

private lemma box4_halfspace_vol {l0 l1 l2 l3 u0 u1 u2 u3 pb : Nat}
    (h0 : l0 ≤ u0) (h1 : l1 ≤ u1) (h2 : l2 ≤ u2) (h3 : l3 ≤ u3) :
    ∫ _ in (Icc (gval l0) (gval u0) ×ˢ Icc (gval l1) (gval u1) ×ˢ
            Icc (gval l2) (gval u2) ×ˢ Icc (gval l3) (gval u3)) ∩
           {x : R4 | x.1 + x.2.1 + 2 * x.2.2.1 + x.2.2.2 ≤ gval pb}, (1 : ℝ) ≤
      ((box4Hs48 (u0 - l0) (u1 - l1) (u2 - l2) (u3 - l3) (pb - (l0 + l1 + l2 + l2 + l3)) : Nat) : ℝ) /
        (48 * (D_grid : ℝ) ^ 4) := by
  set B : Set R4 := Icc (gval l0) (gval u0) ×ˢ Icc (gval l1) (gval u1) ×ˢ
                    Icc (gval l2) (gval u2) ×ˢ Icc (gval l3) (gval u3)
  set H : Set R4 := {x : R4 | x.1 + x.2.1 + 2 * x.2.2.1 + x.2.2.2 ≤ gval pb}
  have hHc : IsClosed H := isClosed_le (by fun_prop) continuous_const
  have hHm : MeasurableSet H := hHc.measurableSet
  have hBc : IsCompact B := isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hBm : MeasurableSet B := hBc.measurableSet
  by_cases hpb_lt : pb ≤ l0 + l1 + l2 + l2 + l3
  · -- Intersection is contained in the single corner {(l0, l1, l2, l3)} of measure 0!
    have hsub : B ∩ H ⊆ {(gval l0, gval l1, gval l2, gval l3)} := by
      intro x ⟨hxB, hxH⟩
      rcases hxB with ⟨⟨hx0a, _⟩, ⟨hx1a, _⟩, ⟨hx2a, _⟩, ⟨hx3a, _⟩⟩
      change x.1 + x.2.1 + 2 * x.2.2.1 + x.2.2.2 ≤ gval pb at hxH
      have hpb_le : gval pb ≤ gval l0 + gval l1 + 2 * gval l2 + gval l3 := by
        have := gval_le hpb_lt; simp only [gval_add] at this; linarith only [this]
      have heq0 : x.1 = gval l0 := by linarith
      have heq1 : x.2.1 = gval l1 := by linarith
      have heq2 : x.2.2.1 = gval l2 := by linarith
      have heq3 : x.2.2.2 = gval l3 := by linarith
      simp only [mem_singleton_iff]
      ext <;> simp [heq0, heq1, heq2, heq3]
    have hm0 : volume (B ∩ H) = 0 :=
      measure_mono_null hsub (volume_singleton_R4 _)
    rw [Measure.restrict_eq_zero.mpr hm0, integral_zero_measure]
    positivity
  · push Not at hpb_lt
    set Rnat := pb - (l0 + l1 + l2 + l2 + l3)
    set dh0 := u0 - l0; set dh1 := u1 - l1; set dh2 := u2 - l2; set dh3 := u3 - l3
    have hvolB : ∫ _ in B, (1 : ℝ) = (gval u0 - gval l0) * (gval u1 - gval l1) *
        (gval u2 - gval l2) * (gval u3 - gval l3) := by
      have hBeq : B = cell4SetGen (gval l0) (gval u0) (gval l1) (gval u1) (gval l2) (gval u2) (gval l3) (gval u3) false false false := by
        ext x; simp only [B, cell4SetGen, mem_prod, mem_ofPred_eq, Bool.false_eq_true, ↓reduceIte]
      rw [hBeq, setIntegral_cell4SetGen (gval_le h0) (gval_le h1) (gval_le h2) (gval_le h3)
        (by simp) (by simp) (by simp) continuous_const]
      simp only [Bool.false_eq_true, ↓reduceIte, intervalIntegral.integral_const, smul_eq_mul]
      ring
    by_cases hfull : dh0 + dh1 + (dh2 + dh2) + dh3 ≤ Rnat
    · have hle : ∫ _ in B ∩ H, (1 : ℝ) ≤ ∫ _ in B, (1 : ℝ) :=
        setIntegral_mono_set (continuousOn_const.integrableOn_compact hBc)
          (ae_restrict_of_forall_mem hBm (fun _ _ => zero_le_one))
          (Filter.Eventually.of_forall inter_subset_left)
      rw [hvolB] at hle
      have hbox : box4Hs48 dh0 dh1 dh2 dh3 Rnat = 48 * dh0 * dh1 * dh2 * dh3 := by
        unfold box4Hs48; dsimp only; rw [Nat.ble_eq.mpr hfull]
      rw [hbox]
      rw [gval_sub h0, gval_sub h1, gval_sub h2, gval_sub h3] at hle
      convert hle using 1
      push_cast; ring
    · -- General inclusion-exclusion case: evaluate exact 4D integral!
      have hble_false : Nat.ble (dh0 + dh1 + (dh2 + dh2) + dh3) Rnat = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; exact hfull
      set hh0 := gval dh0; set hh1 := gval dh1; set hh2 := gval dh2; set hh3 := gval dh3
      set RR := gval Rnat
      have hhh0 : 0 ≤ hh0 := div_nonneg (Nat.cast_nonneg _) (le_of_lt hDpos)
      have hhh1 : 0 ≤ hh1 := div_nonneg (Nat.cast_nonneg _) (le_of_lt hDpos)
      have hhh2 : 0 ≤ hh2 := div_nonneg (Nat.cast_nonneg _) (le_of_lt hDpos)
      have hhh3 : 0 ≤ hh3 := div_nonneg (Nat.cast_nonneg _) (le_of_lt hDpos)
      have hstep_fubini :
          ∫ _ in B ∩ H, (1 : ℝ) =
            ∫ x0 in gval l0..gval u0, ∫ x1 in gval l1..gval u1,
              ∫ x2 in gval l2..gval u2, ∫ x3 in gval l3..gval u3,
                (if x0 + x1 + 2 * x2 + x3 ≤ gval pb then (1 : ℝ) else 0) := by
        rw [← setIntegral_indicator hHm]
        have h1_int : IntegrableOn (H.indicator (fun _ : R4 => (1 : ℝ))) B volume := by
          rw [integrableOn_indicator_iff hHm]
          exact continuousOn_const.integrableOn_compact (hBc.of_isClosed_subset (hHc.inter hBc.isClosed) inter_subset_right)
        let f := H.indicator (fun _ : R4 => (1 : ℝ))
        have hf_eq : ∀ x : R4, f x = if x.1 + x.2.1 + 2 * x.2.2.1 + x.2.2.2 ≤ gval pb then 1 else 0 := by
          intro x; simp [f, H, indicator]
        -- Peel x0, x1, x2 using setIntegral_slice!
        rw [show ∫ x in B, f x = ∫ x0 in gval l0..gval u0,
            ∫ y in Icc (gval l1) (gval u1) ×ˢ Icc (gval l2) (gval u2) ×ˢ Icc (gval l3) (gval u3), f (x0, y) from
          setIntegral_slice (gval_le h0) (fun _ => measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc))
            hBm h1_int]
        apply intervalIntegral.integral_congr; intro x0 _; dsimp only
        have h2_int : IntegrableOn (fun y : ℝ × ℝ × ℝ => f (x0, y))
            (Icc (gval l1) (gval u1) ×ˢ Icc (gval l2) (gval u2) ×ˢ Icc (gval l3) (gval u3)) volume := by
          have hH1 : MeasurableSet {y : ℝ × ℝ × ℝ | (x0, y) ∈ H} := hHm.preimage (by fun_prop)
          have heq : (fun y : ℝ × ℝ × ℝ => f (x0, y)) = {y | (x0, y) ∈ H}.indicator (fun _ => 1) := by
            ext y; simp [f, indicator]
          rw [heq, integrableOn_indicator_iff hH1]
          exact (continuousOn_const.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))).mono_set inter_subset_right
        rw [show ∫ y in Icc (gval l1) (gval u1) ×ˢ Icc (gval l2) (gval u2) ×ˢ Icc (gval l3) (gval u3), f (x0, y) =
            ∫ x1 in gval l1..gval u1, ∫ z in Icc (gval l2) (gval u2) ×ˢ Icc (gval l3) (gval u3), f (x0, x1, z) from
          setIntegral_slice (gval_le h1) (fun _ => measurableSet_Icc.prod measurableSet_Icc)
            (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)) h2_int]
        apply intervalIntegral.integral_congr; intro x1 _; dsimp only
        have h3_int : IntegrableOn (fun z : ℝ × ℝ => f (x0, x1, z))
            (Icc (gval l2) (gval u2) ×ˢ Icc (gval l3) (gval u3)) volume := by
          have hH2 : MeasurableSet {z : ℝ × ℝ | (x0, x1, z) ∈ H} := hHm.preimage (by fun_prop)
          have heq : (fun z : ℝ × ℝ => f (x0, x1, z)) = {z | (x0, x1, z) ∈ H}.indicator (fun _ => 1) := by
            ext z; simp [f, indicator]
          rw [heq, integrableOn_indicator_iff hH2]
          exact (continuousOn_const.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set inter_subset_right
        rw [show ∫ z in Icc (gval l2) (gval u2) ×ˢ Icc (gval l3) (gval u3), f (x0, x1, z) =
            ∫ x2 in gval l2..gval u2, ∫ x3 in Icc (gval l3) (gval u3), f (x0, x1, x2, x3) from
          setIntegral_slice (gval_le h2) (fun _ => measurableSet_Icc)
            (measurableSet_Icc.prod measurableSet_Icc) h3_int]
        apply intervalIntegral.integral_congr; intro x2 _; dsimp only
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (gval_le h3)]
        apply intervalIntegral.integral_congr; intro x3 _; dsimp only
        exact hf_eq (x0, x1, x2, x3)
      -- Shift all 4 variables x_i = y_i + gval l_i
      have hshift :
          (∫ x0 in gval l0..gval u0, ∫ x1 in gval l1..gval u1,
            ∫ x2 in gval l2..gval u2, ∫ x3 in gval l3..gval u3,
              (if x0 + x1 + 2 * x2 + x3 ≤ gval pb then (1 : ℝ) else 0)) =
          ∫ y0 in (0 : ℝ)..hh0, ∫ y1 in (0 : ℝ)..hh1,
            ∫ y2 in (0 : ℝ)..hh2, ∫ y3 in (0 : ℝ)..hh3,
              (if y3 ≤ RR - y0 - y1 - 2 * y2 then (1 : ℝ) else 0) := by
        have hshift1 : ∀ {a h : ℝ} {g : ℝ → ℝ}, ∫ x in a..(h + a), g x = ∫ y in (0 : ℝ)..h, g (y + a) := by
          intro a h g
          have hcomp := intervalIntegral.integral_comp_add_right g a (a := 0) (b := h)
          rw [zero_add] at hcomp; exact hcomp.symm
        have hu0 : gval u0 = hh0 + gval l0 := by have := gval_sub h0; dsimp only [hh0, dh0]; unfold gval at this ⊢; linarith
        have hu1 : gval u1 = hh1 + gval l1 := by have := gval_sub h1; dsimp only [hh1, dh1]; unfold gval at this ⊢; linarith
        have hu2 : gval u2 = hh2 + gval l2 := by have := gval_sub h2; dsimp only [hh2, dh2]; unfold gval at this ⊢; linarith
        have hu3 : gval u3 = hh3 + gval l3 := by have := gval_sub h3; dsimp only [hh3, dh3]; unfold gval at this ⊢; linarith
        have hRR : RR = gval pb - gval l0 - gval l1 - 2 * gval l2 - gval l3 := by
          have := gval_sub (a := l0 + l1 + l2 + l2 + l3) (b := pb) (le_of_lt hpb_lt)
          simp only [gval_add] at this; dsimp only [RR, Rnat]; unfold gval at this ⊢; linarith only [this]
        rw [hu0, hshift1]; apply intervalIntegral.integral_congr; intro y0 _; dsimp only
        rw [hu1, hshift1]; apply intervalIntegral.integral_congr; intro y1 _; dsimp only
        rw [hu2, hshift1]; apply intervalIntegral.integral_congr; intro y2 _; dsimp only
        rw [hu3, hshift1]; apply intervalIntegral.integral_congr; intro y3 _; dsimp only
        have hiff : (y0 + gval l0) + (y1 + gval l1) + 2 * (y2 + gval l2) + (y3 + gval l3) ≤ gval pb ↔
            y3 ≤ RR - y0 - y1 - 2 * y2 := by rw [hRR]; constructor <;> intro h <;> linarith
        simp [hiff]
      -- Evaluate 4 iterated 1D integrals!
      have hstep3 : ∀ y0 y1 y2 : ℝ,
          ∫ y3 in (0 : ℝ)..hh3, (if y3 ≤ RR - y0 - y1 - 2 * y2 then (1 : ℝ) else 0) =
            (max 0 ((RR - y0 - y1) - 2 * y2)) ^ 1 - (max 0 ((RR - hh3 - y0 - y1) - 2 * y2)) ^ 1 := by
        intro y0 y1 y2
        rw [integral_ind_le hhh3]; simp only [pow_one]
        congr 2; ring
      have hstep2 : ∀ y0 y1 : ℝ,
          ∫ y2 in (0 : ℝ)..hh2,
            ((max 0 ((RR - y0 - y1) - 2 * y2)) ^ 1 - (max 0 ((RR - hh3 - y0 - y1) - 2 * y2)) ^ 1) =
          (((max 0 ((RR - y0) - 1 * y1)) ^ 2 - (max 0 ((RR - 2 * hh2 - y0) - 1 * y1)) ^ 2) -
           ((max 0 ((RR - hh3 - y0) - 1 * y1)) ^ 2 - (max 0 ((RR - 2 * hh2 - hh3 - y0) - 1 * y1)) ^ 2)) / 4 := by
        intro y0 y1
        rw [intervalIntegral.integral_sub ((by fun_prop : Continuous _).intervalIntegrable _ _)
            ((by fun_prop : Continuous _).intervalIntegrable _ _),
            integral_posPow_succ 0 hhh2 (by norm_num : (0 : ℝ) < 2),
            integral_posPow_succ 0 hhh2 (by norm_num : (0 : ℝ) < 2)]
        have h22 : (2 : ℝ) * ((0 : ℕ) + 2) = 4 := by norm_num
        rw [h22, ← sub_div]
        congr 1; congr 1
        · congr 1
          · congr 2; ring
          · congr 2; ring
        · congr 1
          · congr 2; ring
          · congr 2; ring
      have hstep1 : ∀ y0 : ℝ,
          ∫ y1 in (0 : ℝ)..hh1,
            ((((max 0 ((RR - y0) - 1 * y1)) ^ 2 - (max 0 ((RR - 2 * hh2 - y0) - 1 * y1)) ^ 2) -
              ((max 0 ((RR - hh3 - y0) - 1 * y1)) ^ 2 - (max 0 ((RR - 2 * hh2 - hh3 - y0) - 1 * y1)) ^ 2)) / 4) =
          ((((max 0 (RR - 1 * y0)) ^ 3 - (max 0 ((RR - hh1) - 1 * y0)) ^ 3) -
            ((max 0 ((RR - 2 * hh2) - 1 * y0)) ^ 3 - (max 0 ((RR - hh1 - 2 * hh2) - 1 * y0)) ^ 3)) -
           (((max 0 ((RR - hh3) - 1 * y0)) ^ 3 - (max 0 ((RR - hh1 - hh3) - 1 * y0)) ^ 3) -
            ((max 0 ((RR - 2 * hh2 - hh3) - 1 * y0)) ^ 3 - (max 0 ((RR - hh1 - 2 * hh2 - hh3) - 1 * y0)) ^ 3))) / 12 := by
        intro y0
        have hi : ∀ r : ℝ, IntervalIntegrable (fun y1 => (max 0 (r - 1 * y1)) ^ 2) volume 0 hh1 :=
          fun _ => (by fun_prop : Continuous _).intervalIntegrable _ _
        rw [intervalIntegral.integral_div,
            intervalIntegral.integral_sub ((hi _).sub (hi _)) ((hi _).sub (hi _)),
            intervalIntegral.integral_sub (hi _) (hi _),
            intervalIntegral.integral_sub (hi _) (hi _),
            integral_posPow_succ 1 hhh1 one_pos, integral_posPow_succ 1 hhh1 one_pos,
            integral_posPow_succ 1 hhh1 one_pos, integral_posPow_succ 1 hhh1 one_pos]
        have h13 : (1 : ℝ) * ((1 : ℕ) + 2) = 3 := by norm_num
        rw [h13]
        have e1 : RR - y0 - 1 * hh1 = RR - hh1 - 1 * y0 := by ring
        have e2 : RR - 2 * hh2 - y0 - 1 * hh1 = RR - hh1 - 2 * hh2 - 1 * y0 := by ring
        have e3 : RR - hh3 - y0 - 1 * hh1 = RR - hh1 - hh3 - 1 * y0 := by ring
        have e4 : RR - 2 * hh2 - hh3 - y0 - 1 * hh1 = RR - hh1 - 2 * hh2 - hh3 - 1 * y0 := by ring
        have f1 : RR - y0 = RR - 1 * y0 := by ring
        have f2 : RR - 2 * hh2 - y0 = RR - 2 * hh2 - 1 * y0 := by ring
        have f3 : RR - hh3 - y0 = RR - hh3 - 1 * y0 := by ring
        have f4 : RR - 2 * hh2 - hh3 - y0 = RR - 2 * hh2 - hh3 - 1 * y0 := by ring
        rw [e1, e2, e3, e4, f1, f2, f3, f4]; ring
      have hstep0 :
          ∫ y0 in (0 : ℝ)..hh0,
            (((((max 0 (RR - 1 * y0)) ^ 3 - (max 0 ((RR - hh1) - 1 * y0)) ^ 3) -
               ((max 0 ((RR - 2 * hh2) - 1 * y0)) ^ 3 - (max 0 ((RR - hh1 - 2 * hh2) - 1 * y0)) ^ 3)) -
              (((max 0 ((RR - hh3) - 1 * y0)) ^ 3 - (max 0 ((RR - hh1 - hh3) - 1 * y0)) ^ 3) -
               ((max 0 ((RR - 2 * hh2 - hh3) - 1 * y0)) ^ 3 - (max 0 ((RR - hh1 - 2 * hh2 - hh3) - 1 * y0)) ^ 3))) / 12) =
          (((max 0 RR) ^ 4 + (max 0 (RR - hh0 - hh1)) ^ 4 + (max 0 (RR - hh0 - 2 * hh2)) ^ 4 +
            (max 0 (RR - hh0 - hh3)) ^ 4 + (max 0 (RR - hh1 - 2 * hh2)) ^ 4 + (max 0 (RR - hh1 - hh3)) ^ 4 +
            (max 0 (RR - 2 * hh2 - hh3)) ^ 4 + (max 0 (RR - hh0 - hh1 - 2 * hh2 - hh3)) ^ 4) -
           ((max 0 (RR - hh0)) ^ 4 + (max 0 (RR - hh1)) ^ 4 + (max 0 (RR - 2 * hh2)) ^ 4 +
            (max 0 (RR - hh3)) ^ 4 + (max 0 (RR - hh0 - hh1 - 2 * hh2)) ^ 4 + (max 0 (RR - hh0 - hh1 - hh3)) ^ 4 +
            (max 0 (RR - hh0 - 2 * hh2 - hh3)) ^ 4 + (max 0 (RR - hh1 - 2 * hh2 - hh3)) ^ 4)) / 48 := by
        have hi : ∀ r : ℝ, IntervalIntegrable (fun y0 => (max 0 (r - 1 * y0)) ^ 3) volume 0 hh0 :=
          fun _ => (by fun_prop : Continuous _).intervalIntegrable _ _
        rw [intervalIntegral.integral_div,
            intervalIntegral.integral_sub (((hi _).sub (hi _)).sub ((hi _).sub (hi _)))
              (((hi _).sub (hi _)).sub ((hi _).sub (hi _))),
            intervalIntegral.integral_sub ((hi _).sub (hi _)) ((hi _).sub (hi _)),
            intervalIntegral.integral_sub ((hi _).sub (hi _)) ((hi _).sub (hi _)),
            intervalIntegral.integral_sub (hi _) (hi _), intervalIntegral.integral_sub (hi _) (hi _),
            intervalIntegral.integral_sub (hi _) (hi _), intervalIntegral.integral_sub (hi _) (hi _),
            integral_posPow_succ 2 hhh0 one_pos, integral_posPow_succ 2 hhh0 one_pos,
            integral_posPow_succ 2 hhh0 one_pos, integral_posPow_succ 2 hhh0 one_pos,
            integral_posPow_succ 2 hhh0 one_pos, integral_posPow_succ 2 hhh0 one_pos,
            integral_posPow_succ 2 hhh0 one_pos, integral_posPow_succ 2 hhh0 one_pos]
        have h14 : (1 : ℝ) * ((2 : ℕ) + 2) = 4 := by norm_num
        rw [h14]
        have r1 : RR - 1 * hh0 = RR - hh0 := by ring
        have r2 : RR - hh1 - 1 * hh0 = RR - hh0 - hh1 := by ring
        have r3 : RR - 2 * hh2 - 1 * hh0 = RR - hh0 - 2 * hh2 := by ring
        have r4 : RR - hh1 - 2 * hh2 - 1 * hh0 = RR - hh0 - hh1 - 2 * hh2 := by ring
        have r5 : RR - hh3 - 1 * hh0 = RR - hh0 - hh3 := by ring
        have r6 : RR - hh1 - hh3 - 1 * hh0 = RR - hh0 - hh1 - hh3 := by ring
        have r7 : RR - 2 * hh2 - hh3 - 1 * hh0 = RR - hh0 - 2 * hh2 - hh3 := by ring
        have r8 : RR - hh1 - 2 * hh2 - hh3 - 1 * hh0 = RR - hh0 - hh1 - 2 * hh2 - hh3 := by ring
        rw [r1, r2, r3, r4, r5, r6, r7, r8]; ring
      have hvol_exact : ∫ _ in B ∩ H, (1 : ℝ) =
          (((max 0 RR) ^ 4 + (max 0 (RR - hh0 - hh1)) ^ 4 + (max 0 (RR - hh0 - 2 * hh2)) ^ 4 +
            (max 0 (RR - hh0 - hh3)) ^ 4 + (max 0 (RR - hh1 - 2 * hh2)) ^ 4 + (max 0 (RR - hh1 - hh3)) ^ 4 +
            (max 0 (RR - 2 * hh2 - hh3)) ^ 4 + (max 0 (RR - hh0 - hh1 - 2 * hh2 - hh3)) ^ 4) -
           ((max 0 (RR - hh0)) ^ 4 + (max 0 (RR - hh1)) ^ 4 + (max 0 (RR - 2 * hh2)) ^ 4 +
            (max 0 (RR - hh3)) ^ 4 + (max 0 (RR - hh0 - hh1 - 2 * hh2)) ^ 4 + (max 0 (RR - hh0 - hh1 - hh3)) ^ 4 +
            (max 0 (RR - hh0 - 2 * hh2 - hh3)) ^ 4 + (max 0 (RR - hh1 - 2 * hh2 - hh3)) ^ 4)) / 48 := by
        rw [hstep_fubini, hshift]
        simp_rw [hstep3, hstep2, hstep1, hstep0]
      -- Match each `max 0 (RR - ...)^4` with `posPow4 Rnat ... / D^4`!
      set h22 := dh2 + dh2
      set posSum := posPow4 Rnat 0 + posPow4 Rnat (dh0 + dh1) + posPow4 Rnat (dh0 + h22) +
        posPow4 Rnat (dh0 + dh3) + posPow4 Rnat (dh1 + h22) + posPow4 Rnat (dh1 + dh3) +
        posPow4 Rnat (h22 + dh3) + posPow4 Rnat (dh0 + dh1 + h22 + dh3)
      set negSum := posPow4 Rnat dh0 + posPow4 Rnat dh1 + posPow4 Rnat h22 +
        posPow4 Rnat dh3 + posPow4 Rnat (dh0 + dh1 + h22) + posPow4 Rnat (dh0 + dh1 + dh3) +
        posPow4 Rnat (dh0 + h22 + dh3) + posPow4 Rnat (dh1 + h22 + dh3)
      have hmatch : ∫ _ in B ∩ H, (1 : ℝ) = ((posSum : ℝ) - (negSum : ℝ)) / (48 * (D_grid : ℝ) ^ 4) := by
        rw [hvol_exact]
        have g_add : ∀ a b : Nat, gval (a + b) = gval a + gval b := fun a b => by
          unfold gval; push_cast; rw [add_div]
        have g0 : gval 0 = 0 := by unfold gval; simp
        have g22 : gval h22 = 2 * hh2 := by dsimp [h22, hh2]; rw [g_add]; ring
        have hD4 : (D_grid : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hDpos)
        have hpos_eq : (posSum : ℝ) / (D_grid : ℝ) ^ 4 =
            (max 0 RR) ^ 4 + (max 0 (RR - hh0 - hh1)) ^ 4 + (max 0 (RR - hh0 - 2 * hh2)) ^ 4 +
            (max 0 (RR - hh0 - hh3)) ^ 4 + (max 0 (RR - hh1 - 2 * hh2)) ^ 4 + (max 0 (RR - hh1 - hh3)) ^ 4 +
            (max 0 (RR - 2 * hh2 - hh3)) ^ 4 + (max 0 (RR - hh0 - hh1 - 2 * hh2 - hh3)) ^ 4 := by
          dsimp only [posSum]
          push_cast
          simp only [add_div, posPow4_cast, g0, sub_zero, g_add, g22, sub_add_eq_sub_sub]
          rfl
        have hneg_eq : (negSum : ℝ) / (D_grid : ℝ) ^ 4 =
            (max 0 (RR - hh0)) ^ 4 + (max 0 (RR - hh1)) ^ 4 + (max 0 (RR - 2 * hh2)) ^ 4 +
            (max 0 (RR - hh3)) ^ 4 + (max 0 (RR - hh0 - hh1 - 2 * hh2)) ^ 4 + (max 0 (RR - hh0 - hh1 - hh3)) ^ 4 +
            (max 0 (RR - hh0 - 2 * hh2 - hh3)) ^ 4 + (max 0 (RR - hh1 - 2 * hh2 - hh3)) ^ 4 := by
          dsimp only [negSum]
          push_cast
          simp only [add_div, posPow4_cast, g_add, g22, sub_add_eq_sub_sub]
          rfl
        rw [← hpos_eq, ← hneg_eq]; field_simp [hD4]
      have hnn : 0 ≤ ∫ _ in B ∩ H, (1 : ℝ) := setIntegral_nonneg (hBm.inter hHm) (fun _ _ => zero_le_one)
      rw [hmatch] at hnn
      have hle_real : (negSum : ℝ) ≤ (posSum : ℝ) := by
        have hden : (0 : ℝ) < 48 * (D_grid : ℝ) ^ 4 := mul_pos (by norm_num) (pow_pos hDpos 4)
        have := (div_nonneg_iff.mp hnn).resolve_right (by intro h; linarith [h.2])
        linarith [this.1]
      have hle_nat : negSum ≤ posSum := by exact_mod_cast hle_real
      have hbox_eq : box4Hs48 dh0 dh1 dh2 dh3 Rnat = posSum - negSum := by
        unfold box4Hs48; dsimp only; rw [hble_false]
      rw [hmatch, hbox_eq, Nat.cast_sub hle_nat]

/-! #### Integrand, Boundary Denominator Boost, and Tree Soundness -/

private def integrand4 (ω : ℝ → ℝ) (φ : ℝ) (x : R4) : ℝ :=
  ω ((φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1) / (x.1 * x.2.1 * x.2.2.1 * x.2.2.1 * x.2.2.2)

private def weight4 (x : R4) : ℝ :=
  1 / (x.1 * x.2.1 * x.2.2.1 * x.2.2.1 * x.2.2.2)

private lemma integrand4_nonneg {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    (φ : ℝ) {c : Cell4} (hv : c.valid) :
    ∀ x ∈ c.set, 0 ≤ integrand4 ω φ x := by
  intro x hx
  have hxb := c.set_subset_box hx
  rcases c.valid_bounds hv with ⟨hl0, _, hl01, _, hl12, _, hl23, _⟩
  rcases hxb with ⟨⟨hx0, _⟩, ⟨hx1, _⟩, ⟨hx2, _⟩, ⟨hx3, _⟩⟩
  have h0 : 0 < x.1 := lt_of_lt_of_le (gval_pos hl0) hx0
  have h1 : 0 < x.2.1 := lt_of_lt_of_le (gval_pos (by omega)) hx1
  have h2 : 0 < x.2.2.1 := lt_of_lt_of_le (gval_pos (by omega)) hx2
  have h3 : 0 < x.2.2.2 := lt_of_lt_of_le (gval_pos (by omega)) hx3
  exact div_nonneg (buchstab_nonneg hω hz _) (by positivity)

private lemma integrand4_integrableOn {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    (φ : ℝ) {c : Cell4} (hv : c.valid) :
    IntegrableOn (integrand4 ω φ) c.set volume := by
  set S : Set R4 := {x : R4 | x.1 + x.2.1 + 2 * x.2.2.1 + x.2.2.2 ≤ φ}
  have hSc : IsClosed S := isClosed_le (by fun_prop) continuous_const
  have hSm : MeasurableSet S := hSc.measurableSet
  have hcomp : IsCompact (c.set ∩ S) :=
    c.isCompact_set.of_isClosed_subset (c.isClosed_set.inter hSc) inter_subset_left
  rcases c.valid_bounds hv with ⟨hl0, _, hl01, _, hl12, _, hl23, _⟩
  have hcont : ContinuousOn (integrand4 ω φ) (c.set ∩ S) := by
    unfold integrand4
    apply ContinuousOn.div
    · apply hω.1.comp
      · apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro x ⟨hx, _⟩
        have hxb := c.set_subset_box hx
        exact ne_of_gt (lt_of_lt_of_le (gval_pos (by omega)) hxb.2.2.1.1)
      · intro x ⟨hx, hxS⟩
        have hxb := c.set_subset_box hx
        have hx2 : 0 < x.2.2.1 := lt_of_lt_of_le (gval_pos (by omega)) hxb.2.2.1.1
        change 1 ≤ (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1
        rw [le_div_iff₀ hx2]; simp only [S, mem_ofPred_eq] at hxS; linarith
    · fun_prop
    · intro x ⟨hx, _⟩
      have hxb := c.set_subset_box hx
      have h0 : 0 < x.1 := lt_of_lt_of_le (gval_pos hl0) hxb.1.1
      have h1 : 0 < x.2.1 := lt_of_lt_of_le (gval_pos (by omega)) hxb.2.1.1
      have h2 : 0 < x.2.2.1 := lt_of_lt_of_le (gval_pos (by omega)) hxb.2.2.1.1
      have h3 : 0 < x.2.2.2 := lt_of_lt_of_le (gval_pos (by omega)) hxb.2.2.2.1
      positivity
  have heq : EqOn (integrand4 ω φ) (S.indicator (integrand4 ω φ)) c.set := by
    intro x hx
    by_cases hxS : x ∈ S
    · simp [hxS]
    · simp only [indicator_of_notMem hxS, integrand4]
      have hxb := c.set_subset_box hx
      have hx2 : 0 < x.2.2.1 := lt_of_lt_of_le (gval_pos (by omega)) hxb.2.2.1.1
      have hu : (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1 < 1 := by
        rw [div_lt_one hx2]; simp only [S, mem_ofPred_eq, not_le] at hxS; linarith
      rw [hz _ hu, zero_div]
  have hint_ind : IntegrableOn (S.indicator (integrand4 ω φ)) c.set volume := by
    rw [integrableOn_indicator_iff hSm, inter_comm]
    exact hcont.integrableOn_compact hcomp
  exact hint_ind.congr_fun heq.symm c.measurableSet_set

private lemma weight4_integrableOn {c : Cell4} (hv : c.valid) :
    IntegrableOn weight4 c.set volume := by
  rcases c.valid_bounds hv with ⟨hl0, _, hl01, _, hl12, _, hl23, _⟩
  apply ContinuousOn.integrableOn_compact c.isCompact_set
  unfold weight4
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro x hx
  have hxb := c.set_subset_box hx
  have h0 : 0 < x.1 := lt_of_lt_of_le (gval_pos hl0) hxb.1.1
  have h1 : 0 < x.2.1 := lt_of_lt_of_le (gval_pos (by omega)) hxb.2.1.1
  have h2 : 0 < x.2.2.1 := lt_of_lt_of_le (gval_pos (by omega)) hxb.2.2.1.1
  have h3 : 0 < x.2.2.2 := lt_of_lt_of_le (gval_pos (by omega)) hxb.2.2.2.1
  positivity

private lemma weight4_nonneg {c : Cell4} (hv : c.valid) : ∀ x ∈ c.set, 0 ≤ weight4 x := by
  intro x hx
  have hxb := c.set_subset_box hx
  rcases c.valid_bounds hv with ⟨hl0, _, hl01, _, hl12, _, hl23, _⟩
  have h0 : 0 < x.1 := lt_of_lt_of_le (gval_pos hl0) hxb.1.1
  have h1 : 0 < x.2.1 := lt_of_lt_of_le (gval_pos (by omega)) hxb.2.1.1
  have h2 : 0 < x.2.2.1 := lt_of_lt_of_le (gval_pos (by omega)) hxb.2.2.1.1
  have h3 : 0 < x.2.2.2 := lt_of_lt_of_le (gval_pos (by omega)) hxb.2.2.2.1
  unfold weight4; positivity

private lemma one_add_sum_le_prod {a0 a1 a2 a3 : ℝ}
    (h0 : 0 ≤ a0) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3) :
    1 + a0 + a1 + 2 * a2 + a3 ≤ (1 + a0) * (1 + a1) * (1 + a2) * (1 + a2) * (1 + a3) := by
  have p1 : 1 + a0 + a1 ≤ (1 + a0) * (1 + a1) := by
    have hm := mul_nonneg h0 h1; linarith only [hm]
  have p2 : 1 + a0 + a1 + a2 ≤ (1 + a0) * (1 + a1) * (1 + a2) := by
    have hm := mul_nonneg (add_nonneg h0 h1) h2
    have hq := mul_le_mul_of_nonneg_right p1 (by linarith only [h2] : 0 ≤ 1 + a2)
    linarith only [hm, hq]
  have p3 : 1 + a0 + a1 + 2 * a2 ≤ (1 + a0) * (1 + a1) * (1 + a2) * (1 + a2) := by
    have hm := mul_nonneg (add_nonneg (add_nonneg h0 h1) h2) h2
    have hq := mul_le_mul_of_nonneg_right p2 (by linarith only [h2] : 0 ≤ 1 + a2)
    linarith only [hm, hq]
  have hm := mul_nonneg (by linarith only [h0, h1, h2] : 0 ≤ a0 + a1 + 2 * a2) h3
  have hq := mul_le_mul_of_nonneg_right p3 (by linarith only [h3] : 0 ≤ 1 + a3)
  linarith only [hm, hq]

private lemma boundary_denom_boost {l0 l1 l2 l3 x0 x1 x2 x3 pa φ : ℝ}
    (hl0 : 0 < l0) (hl01 : l0 ≤ l1) (hl12 : l1 ≤ l2) (hl23 : l2 ≤ l3)
    (hx0 : l0 ≤ x0) (hx1 : l1 ≤ x1) (hx2 : l2 ≤ x2) (hx3 : l3 ≤ x3)
    (hpa : pa ≤ φ) (hRa : 0 < pa - l0 - l1 - 2 * l2 - l3)
    (hu1 : x2 ≤ φ - x0 - x1 - x2 - x3) :
    l0 * l1 * l2 * l2 * l3 * (1 + (pa - l0 - l1 - 2 * l2 - l3) / (l2 + l3)) ≤
      x0 * x1 * x2 * x3 * (φ - x0 - x1 - x2 - x3) := by
  have hl1 : 0 < l1 := lt_of_lt_of_le hl0 hl01
  have hl2 : 0 < l2 := lt_of_lt_of_le hl1 hl12
  have hl3 : 0 < l3 := lt_of_lt_of_le hl2 hl23
  have hx0p : 0 < x0 := lt_of_lt_of_le hl0 hx0
  have hx1p : 0 < x1 := lt_of_lt_of_le hl1 hx1
  have hx2p : 0 < x2 := lt_of_lt_of_le hl2 hx2
  have hx3p : 0 < x3 := lt_of_lt_of_le hl3 hx3
  set y0 := x0 - l0; set y1 := x1 - l1; set y2 := x2 - l2; set y3 := x3 - l3
  set Ra := pa - l0 - l1 - 2 * l2 - l3
  set t := Ra * l3 / (l2 + l3)
  have hy0 : 0 ≤ y0 := sub_nonneg.mpr hx0
  have hy1 : 0 ≤ y1 := sub_nonneg.mpr hx1
  have hy2 : 0 ≤ y2 := sub_nonneg.mpr hx2
  have hy3 : 0 ≤ y3 := sub_nonneg.mpr hx3
  have h23pos : 0 < l2 + l3 := by linarith
  by_cases hcase : y0 + y1 + 2 * y2 + y3 ≤ t
  · have hrem : l2 * (1 + Ra / (l2 + l3)) ≤ φ - x0 - x1 - x2 - x3 := by
      have h1 : l2 * (1 + Ra / (l2 + l3)) = l2 + Ra - t := by
        dsimp only [t]; field_simp [ne_of_gt h23pos]; ring
      rw [h1]
      dsimp only [y0, y1, y2, y3, Ra] at hcase ⊢
      linarith
    have hprod : l0 * l1 * l2 * l3 ≤ x0 * x1 * x2 * x3 := by
      have h01 : l0 * l1 ≤ x0 * x1 := mul_le_mul hx0 hx1 (le_of_lt hl1) (by linarith)
      have h012 : l0 * l1 * l2 ≤ x0 * x1 * x2 := mul_le_mul h01 hx2 (le_of_lt hl2) (by positivity)
      exact mul_le_mul h012 hx3 (le_of_lt hl3) (by positivity)
    have hfin := mul_le_mul hprod hrem (by positivity) (by positivity)
    linarith
  · push Not at hcase
    have hx_eq : x0 * x1 * x2 * x3 * (φ - x0 - x1 - x2 - x3) ≥ x0 * x1 * x2 * x3 * x2 :=
      mul_le_mul_of_nonneg_left hu1 (by positivity)
    have hdiv : 1 + y0 / l0 + y1 / l1 + 2 * (y2 / l2) + y3 / l3 ≤
        (x0 / l0) * (x1 / l1) * (x2 / l2) * (x2 / l2) * (x3 / l3) := by
      have e0 : x0 / l0 = 1 + y0 / l0 := div_eq_one_add_sub_div (ne_of_gt hl0)
      have e1 : x1 / l1 = 1 + y1 / l1 := div_eq_one_add_sub_div (ne_of_gt hl1)
      have e2 : x2 / l2 = 1 + y2 / l2 := div_eq_one_add_sub_div (ne_of_gt hl2)
      have e3 : x3 / l3 = 1 + y3 / l3 := div_eq_one_add_sub_div (ne_of_gt hl3)
      rw [e0, e1, e2, e3]
      set a0 := y0 / l0; set a1 := y1 / l1; set a2 := y2 / l2; set a3 := y3 / l3
      have ha0 : 0 ≤ a0 := div_nonneg hy0 (le_of_lt hl0)
      have ha1 : 0 ≤ a1 := div_nonneg hy1 (le_of_lt hl1)
      have ha2 : 0 ≤ a2 := div_nonneg hy2 (le_of_lt hl2)
      have ha3 : 0 ≤ a3 := div_nonneg hy3 (le_of_lt hl3)
      exact one_add_sum_le_prod ha0 ha1 ha2 ha3
    have hmono : (y0 + y1 + 2 * y2 + y3) / l3 ≤ y0 / l0 + y1 / l1 + 2 * (y2 / l2) + y3 / l3 := by
      have d0 : y0 / l3 ≤ y0 / l0 := div_le_div_of_nonneg_left hy0 hl0 (by linarith)
      have d1 : y1 / l3 ≤ y1 / l1 := div_le_div_of_nonneg_left hy1 hl1 (by linarith)
      have d2 : y2 / l3 ≤ y2 / l2 := div_le_div_of_nonneg_left hy2 hl2 hl23
      rw [add_div, add_div, add_div, mul_div_assoc]; linarith
    have ht_eq : t / l3 = Ra / (l2 + l3) := by
      dsimp only [t]; field_simp [ne_of_gt hl3, ne_of_gt h23pos]
    have hstep : 1 + Ra / (l2 + l3) ≤ (x0 / l0) * (x1 / l1) * (x2 / l2) * (x2 / l2) * (x3 / l3) := by
      have : t / l3 ≤ (y0 + y1 + 2 * y2 + y3) / l3 := div_le_div_of_nonneg_right (le_of_lt hcase) (le_of_lt hl3)
      linarith
    have hmul := mul_le_mul_of_nonneg_left hstep (show 0 ≤ l0 * l1 * l2 * l2 * l3 by positivity)
    have hr : l0 * l1 * l2 * l2 * l3 * ((x0 / l0) * (x1 / l1) * (x2 / l2) * (x2 / l2) * (x3 / l3)) =
        x0 * x1 * x2 * x3 * x2 := by
      have h0 := mul_div_cancel₀ x0 (ne_of_gt hl0)
      have h1 := mul_div_cancel₀ x1 (ne_of_gt hl1)
      have h2 := mul_div_cancel₀ x2 (ne_of_gt hl2)
      have h3 := mul_div_cancel₀ x3 (ne_of_gt hl3)
      calc l0 * l1 * l2 * l2 * l3 * ((x0 / l0) * (x1 / l1) * (x2 / l2) * (x2 / l2) * (x3 / l3))
          = (l0 * (x0 / l0)) * (l1 * (x1 / l1)) * (l2 * (x2 / l2)) * (l3 * (x3 / l3)) * (l2 * (x2 / l2)) := by ring
        _ = x0 * x1 * x2 * x3 * x2 := by rw [h0, h1, h2, h3]
    linarith

private lemma vertInt_ceil_bound {pa vprod fprod x0 x1 x2 x3 : Nat}
    (hx0 : 0 < x0) (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) (hf : 0 < fprod)
    (hpa : x0 + x1 + x2 + x3 < pa) :
    ((vprod : ℝ) / (D_grid : ℝ) ^ 4) / (fprod : ℝ) *
      (1 / (gval x0 * gval x1 * gval x2 * gval x3 * (gval pa - gval x0 - gval x1 - gval x2 - gval x3))) ≤
      (evalVertInt pa (S_scale * D_grid * vprod) fprod x0 x1 x2 x3 : ℝ) / S_scale := by
  have hden_pos : 0 < fprod * x0 * x1 * x2 * x3 * (pa - x0 - x1 - x2 - x3) := by
    have : 0 < pa - x0 - x1 - x2 - x3 := by omega
    positivity
  have hceil := le_mul_ceilDiv (a := S_scale * D_grid * vprod) hden_pos
  have hsub : ((pa - x0 - x1 - x2 - x3 : Nat) : ℝ) = (pa : ℝ) - x0 - x1 - x2 - x3 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  have hceil_r : (S_scale : ℝ) * D_grid * vprod ≤
      (fprod : ℝ) * x0 * x1 * x2 * x3 * ((pa : ℝ) - x0 - x1 - x2 - x3) *
        (evalVertInt pa (S_scale * D_grid * vprod) fprod x0 x1 x2 x3 : ℝ) := by
    have hcast : ((S_scale * D_grid * vprod : Nat) : ℝ) ≤
        ((fprod * x0 * x1 * x2 * x3 * (pa - x0 - x1 - x2 - x3) *
          evalVertInt pa (S_scale * D_grid * vprod) fprod x0 x1 x2 x3 : Nat) : ℝ) := by
      exact_mod_cast hceil
    push_cast at hcast
    rw [hsub] at hcast
    linarith
  have hfr : (0 : ℝ) < fprod := by exact_mod_cast hf
  have hx0r : (0 : ℝ) < x0 := by exact_mod_cast hx0
  have hx1r : (0 : ℝ) < x1 := by exact_mod_cast hx1
  have hx2r : (0 : ℝ) < x2 := by exact_mod_cast hx2
  have hx3r : (0 : ℝ) < x3 := by exact_mod_cast hx3
  have hpar : (0 : ℝ) < (pa : ℝ) - x0 - x1 - x2 - x3 := by
    have : ((x0 + x1 + x2 + x3 : Nat) : ℝ) < pa := by exact_mod_cast hpa
    push_cast at this; linarith
  have hlhs_eq : ((vprod : ℝ) / (D_grid : ℝ) ^ 4) / (fprod : ℝ) *
      (1 / (gval x0 * gval x1 * gval x2 * gval x3 * (gval pa - gval x0 - gval x1 - gval x2 - gval x3))) =
      ((D_grid : ℝ) * vprod) / ((fprod : ℝ) * x0 * x1 * x2 * x3 * ((pa : ℝ) - x0 - x1 - x2 - x3)) := by
    unfold gval
    rw [show (pa : ℝ) / D_grid - x0 / D_grid - x1 / D_grid - x2 / D_grid - x3 / D_grid =
          ((pa : ℝ) - x0 - x1 - x2 - x3) / D_grid by ring]
    exact vertInt_alg (ne_of_gt hDpos)
  rw [hlhs_eq, div_le_div_iff₀ (by positivity) hSpos]
  linarith

private lemma vertW_ceil_bound {nm dm vprod fprod x0 x1 x2 x3 : Nat}
    (hdm : 0 < dm) (hf : 0 < fprod) (hx0 : 0 < x0) (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) :
    (((nm : ℝ) / dm) * (((vprod : ℝ) / (D_grid : ℝ) ^ 4) / (fprod : ℝ))) *
      weight4 (gval x0, gval x1, gval x2, gval x3) ≤
      (evalVertW (nm * S_scale * D_grid * vprod) (dm * fprod) x0 x1 x2 x3 : ℝ) / S_scale := by
  have hden_pos : 0 < (dm * fprod) * x0 * x1 * x2 * x2 * x3 := by positivity
  have hceil := le_mul_ceilDiv (a := nm * S_scale * D_grid * vprod) hden_pos
  have hceil_r : (nm : ℝ) * S_scale * D_grid * vprod ≤
      (dm : ℝ) * fprod * x0 * x1 * x2 * x2 * x3 *
        (evalVertW (nm * S_scale * D_grid * vprod) (dm * fprod) x0 x1 x2 x3 : ℝ) := by
    have hcast : ((nm * S_scale * D_grid * vprod : Nat) : ℝ) ≤
        (((dm * fprod) * x0 * x1 * x2 * x2 * x3 *
          evalVertW (nm * S_scale * D_grid * vprod) (dm * fprod) x0 x1 x2 x3 : Nat) : ℝ) := by
      exact_mod_cast hceil
    push_cast at hcast; linarith
  have hdmr : (0 : ℝ) < dm := by exact_mod_cast hdm
  have hfr : (0 : ℝ) < fprod := by exact_mod_cast hf
  have hx0r : (0 : ℝ) < x0 := by exact_mod_cast hx0
  have hx1r : (0 : ℝ) < x1 := by exact_mod_cast hx1
  have hx2r : (0 : ℝ) < x2 := by exact_mod_cast hx2
  have hx3r : (0 : ℝ) < x3 := by exact_mod_cast hx3
  have hlhs_eq : (((nm : ℝ) / dm) * (((vprod : ℝ) / (D_grid : ℝ) ^ 4) / (fprod : ℝ))) *
      weight4 (gval x0, gval x1, gval x2, gval x3) =
      ((nm : ℝ) * D_grid * vprod) / ((dm : ℝ) * fprod * x0 * x1 * x2 * x2 * x3) := by
    unfold weight4 gval
    exact vertW_alg (ne_of_gt hDpos)
  rw [hlhs_eq, div_le_div_iff₀ (by positivity) hSpos]
  linarith

private lemma sum4_lt {x0 x1 x2 x3 u0 u1 u2 u3 pa : Nat}
    (h0 : x0 ≤ u0) (h1 : x1 ≤ u1) (h2 : x2 ≤ u2) (h3 : x3 ≤ u3)
    (hp : u0 + u1 + u2 + u3 < pa) : x0 + x1 + x2 + x3 < pa :=
  Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h0 h1) h2) h3) hp

private lemma mul_sum2_le {c x1 x2 y1 y2 : ℝ}
    (h1 : c * x1 ≤ y1) (h2 : c * x2 ≤ y2) : c * (x1 + x2) ≤ y1 + y2 := by
  rw [mul_add]; exact add_le_add h1 h2

private lemma mul_sum4_le {c x1 x2 x3 x4 y1 y2 y3 y4 : ℝ}
    (h1 : c * x1 ≤ y1) (h2 : c * x2 ≤ y2) (h3 : c * x3 ≤ y3) (h4 : c * x4 ≤ y4) :
    c * (x1 + x2 + x3 + x4) ≤ y1 + y2 + y3 + y4 :=
  mul_sum2_le (mul_sum2_le (mul_sum2_le h1 h2) h3) h4

private lemma mul_sum5_le {c x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℝ}
    (h1 : c * x1 ≤ y1) (h2 : c * x2 ≤ y2) (h3 : c * x3 ≤ y3) (h4 : c * x4 ≤ y4) (h5 : c * x5 ≤ y5) :
    c * (x1 + x2 + x3 + x4 + x5) ≤ y1 + y2 + y3 + y4 + y5 :=
  mul_sum2_le (mul_sum4_le h1 h2 h3 h4) h5

private lemma mul_sum3_le {c x1 x2 x3 y1 y2 y3 : ℝ}
    (h1 : c * x1 ≤ y1) (h2 : c * x2 ≤ y2) (h3 : c * x3 ≤ y3) :
    c * (x1 + x2 + x3) ≤ y1 + y2 + y3 :=
  mul_sum2_le (mul_sum2_le h1 h2) h3

private lemma evalIntCell_bound {pa : Nat} {c : Cell4} (hv : c.valid)
    (hpa_ge : let (_, _, _, _, u0, u1, u2, u3) := cellLoHi c; u0 + u1 + u2 + u2 + u3 ≤ pa) :
    vertSumReal (fun x : R4 => 1 / (x.1 * x.2.1 * x.2.2.1 * x.2.2.2 *
      (gval pa - x.1 - x.2.1 - x.2.2.1 - x.2.2.2))) c ≤
      (evalIntCell pa c : ℝ) / S_scale := by
  have hDne : (D_grid : ℝ) ≠ 0 := ne_of_gt hDpos
  cases c with
  | c4 a b =>
    rcases hv with ⟨ha, hab⟩
    simp only [cellLoHi] at hpa_ge
    simp only [vertSumReal, evalIntCell, gval_sub (le_of_lt hab)]
    set h := b - a; set vp := h * h * (h * h)
    have hbp : 0 < b := lt_trans ha hab
    have hle : a ≤ b := le_of_lt hab
    have hmax : b + b + b + b < pa := by omega
    have heq_fac : ((h : ℝ) / D_grid) ^ 4 / 120 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (120 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : S_scale * D_grid * (h * h) * (h * h) = S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 q0 q1 q2 q3 =>
      vertInt_ceil_bound (pa := pa) (vprod := vp) (fprod := 120) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)
        p0 p1 p2 p3 (by decide) (sum4_lt q0 q1 q2 q3 hmax)
    exact mul_sum5_le
      (hb a a a a ha ha ha ha hle hle hle hle)
      (hb a a a b ha ha ha hbp hle hle hle le_rfl)
      (hb a a b b ha ha hbp hbp hle hle le_rfl le_rfl)
      (hb a b b b ha hbp hbp hbp hle le_rfl le_rfl le_rfl)
      (hb b b b b hbp hbp hbp hbp le_rfl le_rfl le_rfl le_rfl)
  | c31 a0 b0 a1 b1 =>
    rcases hv with ⟨ha0, h0, h01, h1⟩
    simp only [cellLoHi] at hpa_ge
    simp only [vertSumReal, evalIntCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1)]
    set h0n := b0 - a0; set h1n := b1 - a1; set vp := h0n * h0n * h0n * h1n
    have hb0 : 0 < b0 := lt_trans ha0 h0
    have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01
    have hb1 : 0 < b1 := lt_trans ha1 h1
    have l0 : a0 ≤ b0 := le_of_lt h0; have l1 : a1 ≤ b1 := le_of_lt h1
    have hmax : b0 + b0 + b0 + b1 < pa := by omega
    have heq_fac : ((h0n : ℝ) / D_grid) ^ 3 * ((h1n : ℝ) / D_grid) / 48 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (48 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : S_scale * D_grid * h0n * h0n * h0n * h1n = S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 q0 q1 q2 q3 =>
      vertInt_ceil_bound (pa := pa) (vprod := vp) (fprod := 48) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)
        p0 p1 p2 p3 (by decide) (sum4_lt q0 q1 q2 q3 hmax)
    exact mul_sum2_le
      (mul_sum4_le (hb a0 a0 a0 a1 ha0 ha0 ha0 ha1 l0 l0 l0 l1) (hb a0 a0 b0 a1 ha0 ha0 hb0 ha1 l0 l0 le_rfl l1)
        (hb a0 b0 b0 a1 ha0 hb0 hb0 ha1 l0 le_rfl le_rfl l1) (hb b0 b0 b0 a1 hb0 hb0 hb0 ha1 le_rfl le_rfl le_rfl l1))
      (mul_sum4_le (hb a0 a0 a0 b1 ha0 ha0 ha0 hb1 l0 l0 l0 le_rfl) (hb a0 a0 b0 b1 ha0 ha0 hb0 hb1 l0 l0 le_rfl le_rfl)
        (hb a0 b0 b0 b1 ha0 hb0 hb0 hb1 l0 le_rfl le_rfl le_rfl) (hb b0 b0 b0 b1 hb0 hb0 hb0 hb1 le_rfl le_rfl le_rfl le_rfl))
  | c13 a0 b0 a1 b1 =>
    rcases hv with ⟨ha0, h0, h01, h1⟩
    simp only [cellLoHi] at hpa_ge
    simp only [vertSumReal, evalIntCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1)]
    set h0n := b0 - a0; set h1n := b1 - a1; set vp := h0n * h1n * h1n * h1n
    have hb0 : 0 < b0 := lt_trans ha0 h0
    have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01
    have hb1 : 0 < b1 := lt_trans ha1 h1
    have l0 : a0 ≤ b0 := le_of_lt h0; have l1 : a1 ≤ b1 := le_of_lt h1
    have hmax : b0 + b1 + b1 + b1 < pa := by omega
    have heq_fac : ((h0n : ℝ) / D_grid) * ((h1n : ℝ) / D_grid) ^ 3 / 48 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (48 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : S_scale * D_grid * h0n * h1n * h1n * h1n = S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 q0 q1 q2 q3 =>
      vertInt_ceil_bound (pa := pa) (vprod := vp) (fprod := 48) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)
        p0 p1 p2 p3 (by decide) (sum4_lt q0 q1 q2 q3 hmax)
    exact mul_sum2_le
      (mul_sum4_le (hb a0 a1 a1 a1 ha0 ha1 ha1 ha1 l0 l1 l1 l1) (hb a0 a1 a1 b1 ha0 ha1 ha1 hb1 l0 l1 l1 le_rfl)
        (hb a0 a1 b1 b1 ha0 ha1 hb1 hb1 l0 l1 le_rfl le_rfl) (hb a0 b1 b1 b1 ha0 hb1 hb1 hb1 l0 le_rfl le_rfl le_rfl))
      (mul_sum4_le (hb b0 a1 a1 a1 hb0 ha1 ha1 ha1 le_rfl l1 l1 l1) (hb b0 a1 a1 b1 hb0 ha1 ha1 hb1 le_rfl l1 l1 le_rfl)
        (hb b0 a1 b1 b1 hb0 ha1 hb1 hb1 le_rfl l1 le_rfl le_rfl) (hb b0 b1 b1 b1 hb0 hb1 hb1 hb1 le_rfl le_rfl le_rfl le_rfl))
  | c22 a0 b0 a1 b1 =>
    rcases hv with ⟨ha0, h0, h01, h1⟩
    simp only [cellLoHi] at hpa_ge
    simp only [vertSumReal, evalIntCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1)]
    set h0n := b0 - a0; set h1n := b1 - a1; set vp := h0n * h0n * h1n * h1n
    have hb0 : 0 < b0 := lt_trans ha0 h0
    have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01
    have hb1 : 0 < b1 := lt_trans ha1 h1
    have l0 : a0 ≤ b0 := le_of_lt h0; have l1 : a1 ≤ b1 := le_of_lt h1
    have hmax : b0 + b0 + b1 + b1 < pa := by omega
    have heq_fac : ((h0n : ℝ) / D_grid) ^ 2 * ((h1n : ℝ) / D_grid) ^ 2 / 36 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (36 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : S_scale * D_grid * h0n * h0n * h1n * h1n = S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 q0 q1 q2 q3 =>
      vertInt_ceil_bound (pa := pa) (vprod := vp) (fprod := 36) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)
        p0 p1 p2 p3 (by decide) (sum4_lt q0 q1 q2 q3 hmax)
    exact mul_sum3_le
      (mul_sum3_le (hb a0 a0 a1 a1 ha0 ha0 ha1 ha1 l0 l0 l1 l1) (hb a0 a0 a1 b1 ha0 ha0 ha1 hb1 l0 l0 l1 le_rfl)
        (hb a0 a0 b1 b1 ha0 ha0 hb1 hb1 l0 l0 le_rfl le_rfl))
      (mul_sum3_le (hb a0 b0 a1 a1 ha0 hb0 ha1 ha1 l0 le_rfl l1 l1) (hb a0 b0 a1 b1 ha0 hb0 ha1 hb1 l0 le_rfl l1 le_rfl)
        (hb a0 b0 b1 b1 ha0 hb0 hb1 hb1 l0 le_rfl le_rfl le_rfl))
      (mul_sum3_le (hb b0 b0 a1 a1 hb0 hb0 ha1 ha1 le_rfl le_rfl l1 l1) (hb b0 b0 a1 b1 hb0 hb0 ha1 hb1 le_rfl le_rfl l1 le_rfl)
        (hb b0 b0 b1 b1 hb0 hb0 hb1 hb1 le_rfl le_rfl le_rfl le_rfl))
  | c211 a0 b0 a1 b1 a2 b2 =>
    rcases hv with ⟨ha0, h0, h01, h1, h12, h2⟩
    simp only [cellLoHi] at hpa_ge
    simp only [vertSumReal, evalIntCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1), gval_sub (le_of_lt h2)]
    set h0n := b0 - a0; set h1n := b1 - a1; set h2n := b2 - a2; set vp := h0n * h0n * h1n * h2n
    have hb0 : 0 < b0 := lt_trans ha0 h0; have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01
    have hb1 : 0 < b1 := lt_trans ha1 h1; have ha2 : 0 < a2 := lt_of_lt_of_le hb1 h12
    have hb2 : 0 < b2 := lt_trans ha2 h2
    have l0 : a0 ≤ b0 := le_of_lt h0; have l1 : a1 ≤ b1 := le_of_lt h1; have l2 : a2 ≤ b2 := le_of_lt h2
    have hmax : b0 + b0 + b1 + b2 < pa := by omega
    have heq_fac : ((h0n : ℝ) / D_grid) ^ 2 * ((h1n : ℝ) / D_grid) * ((h2n : ℝ) / D_grid) / 24 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (24 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : S_scale * D_grid * h0n * h0n * h1n * h2n = S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 q0 q1 q2 q3 =>
      vertInt_ceil_bound (pa := pa) (vprod := vp) (fprod := 24) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)
        p0 p1 p2 p3 (by decide) (sum4_lt q0 q1 q2 q3 hmax)
    exact mul_sum3_le
      (mul_sum4_le (hb a0 a0 a1 a2 ha0 ha0 ha1 ha2 l0 l0 l1 l2) (hb a0 a0 a1 b2 ha0 ha0 ha1 hb2 l0 l0 l1 le_rfl)
        (hb a0 a0 b1 a2 ha0 ha0 hb1 ha2 l0 l0 le_rfl l2) (hb a0 a0 b1 b2 ha0 ha0 hb1 hb2 l0 l0 le_rfl le_rfl))
      (mul_sum4_le (hb a0 b0 a1 a2 ha0 hb0 ha1 ha2 l0 le_rfl l1 l2) (hb a0 b0 a1 b2 ha0 hb0 ha1 hb2 l0 le_rfl l1 le_rfl)
        (hb a0 b0 b1 a2 ha0 hb0 hb1 ha2 l0 le_rfl le_rfl l2) (hb a0 b0 b1 b2 ha0 hb0 hb1 hb2 l0 le_rfl le_rfl le_rfl))
      (mul_sum4_le (hb b0 b0 a1 a2 hb0 hb0 ha1 ha2 le_rfl le_rfl l1 l2) (hb b0 b0 a1 b2 hb0 hb0 ha1 hb2 le_rfl le_rfl l1 le_rfl)
        (hb b0 b0 b1 a2 hb0 hb0 hb1 ha2 le_rfl le_rfl le_rfl l2) (hb b0 b0 b1 b2 hb0 hb0 hb1 hb2 le_rfl le_rfl le_rfl le_rfl))
  | c121 a0 b0 a1 b1 a2 b2 =>
    rcases hv with ⟨ha0, h0, h01, h1, h12, h2⟩
    simp only [cellLoHi] at hpa_ge
    simp only [vertSumReal, evalIntCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1), gval_sub (le_of_lt h2)]
    set h0n := b0 - a0; set h1n := b1 - a1; set h2n := b2 - a2; set vp := h0n * h1n * h1n * h2n
    have hb0 : 0 < b0 := lt_trans ha0 h0; have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01
    have hb1 : 0 < b1 := lt_trans ha1 h1; have ha2 : 0 < a2 := lt_of_lt_of_le hb1 h12
    have hb2 : 0 < b2 := lt_trans ha2 h2
    have l0 : a0 ≤ b0 := le_of_lt h0; have l1 : a1 ≤ b1 := le_of_lt h1; have l2 : a2 ≤ b2 := le_of_lt h2
    have hmax : b0 + b1 + b1 + b2 < pa := by omega
    have heq_fac : ((h0n : ℝ) / D_grid) * ((h1n : ℝ) / D_grid) ^ 2 * ((h2n : ℝ) / D_grid) / 24 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (24 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : S_scale * D_grid * h0n * h1n * h1n * h2n = S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 q0 q1 q2 q3 =>
      vertInt_ceil_bound (pa := pa) (vprod := vp) (fprod := 24) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)
        p0 p1 p2 p3 (by decide) (sum4_lt q0 q1 q2 q3 hmax)
    exact mul_sum3_le
      (mul_sum4_le (hb a0 a1 a1 a2 ha0 ha1 ha1 ha2 l0 l1 l1 l2) (hb a0 a1 a1 b2 ha0 ha1 ha1 hb2 l0 l1 l1 le_rfl)
        (hb b0 a1 a1 a2 hb0 ha1 ha1 ha2 le_rfl l1 l1 l2) (hb b0 a1 a1 b2 hb0 ha1 ha1 hb2 le_rfl l1 l1 le_rfl))
      (mul_sum4_le (hb a0 a1 b1 a2 ha0 ha1 hb1 ha2 l0 l1 le_rfl l2) (hb a0 a1 b1 b2 ha0 ha1 hb1 hb2 l0 l1 le_rfl le_rfl)
        (hb b0 a1 b1 a2 hb0 ha1 hb1 ha2 le_rfl l1 le_rfl l2) (hb b0 a1 b1 b2 hb0 ha1 hb1 hb2 le_rfl l1 le_rfl le_rfl))
      (mul_sum4_le (hb a0 b1 b1 a2 ha0 hb1 hb1 ha2 l0 le_rfl le_rfl l2) (hb a0 b1 b1 b2 ha0 hb1 hb1 hb2 l0 le_rfl le_rfl le_rfl)
        (hb b0 b1 b1 a2 hb0 hb1 hb1 ha2 le_rfl le_rfl le_rfl l2) (hb b0 b1 b1 b2 hb0 hb1 hb1 hb2 le_rfl le_rfl le_rfl le_rfl))
  | c112 a0 b0 a1 b1 a2 b2 =>
    rcases hv with ⟨ha0, h0, h01, h1, h12, h2⟩
    simp only [cellLoHi] at hpa_ge
    simp only [vertSumReal, evalIntCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1), gval_sub (le_of_lt h2)]
    set h0n := b0 - a0; set h1n := b1 - a1; set h2n := b2 - a2; set vp := h0n * h1n * h2n * h2n
    have hb0 : 0 < b0 := lt_trans ha0 h0; have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01
    have hb1 : 0 < b1 := lt_trans ha1 h1; have ha2 : 0 < a2 := lt_of_lt_of_le hb1 h12
    have hb2 : 0 < b2 := lt_trans ha2 h2
    have l0 : a0 ≤ b0 := le_of_lt h0; have l1 : a1 ≤ b1 := le_of_lt h1; have l2 : a2 ≤ b2 := le_of_lt h2
    have hmax : b0 + b1 + b2 + b2 < pa := by omega
    have heq_fac : ((h0n : ℝ) / D_grid) * ((h1n : ℝ) / D_grid) * ((h2n : ℝ) / D_grid) ^ 2 / 24 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (24 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : S_scale * D_grid * h0n * h1n * h2n * h2n = S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 q0 q1 q2 q3 =>
      vertInt_ceil_bound (pa := pa) (vprod := vp) (fprod := 24) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)
        p0 p1 p2 p3 (by decide) (sum4_lt q0 q1 q2 q3 hmax)
    exact mul_sum3_le
      (mul_sum4_le (hb a0 a1 a2 a2 ha0 ha1 ha2 ha2 l0 l1 l2 l2) (hb a0 b1 a2 a2 ha0 hb1 ha2 ha2 l0 le_rfl l2 l2)
        (hb b0 a1 a2 a2 hb0 ha1 ha2 ha2 le_rfl l1 l2 l2) (hb b0 b1 a2 a2 hb0 hb1 ha2 ha2 le_rfl le_rfl l2 l2))
      (mul_sum4_le (hb a0 a1 a2 b2 ha0 ha1 ha2 hb2 l0 l1 l2 le_rfl) (hb a0 b1 a2 b2 ha0 hb1 ha2 hb2 l0 le_rfl l2 le_rfl)
        (hb b0 a1 a2 b2 hb0 ha1 ha2 hb2 le_rfl l1 l2 le_rfl) (hb b0 b1 a2 b2 hb0 hb1 ha2 hb2 le_rfl le_rfl l2 le_rfl))
      (mul_sum4_le (hb a0 a1 b2 b2 ha0 ha1 hb2 hb2 l0 l1 le_rfl le_rfl) (hb a0 b1 b2 b2 ha0 hb1 hb2 hb2 l0 le_rfl le_rfl le_rfl)
        (hb b0 a1 b2 b2 hb0 ha1 hb2 hb2 le_rfl l1 le_rfl le_rfl) (hb b0 b1 b2 b2 hb0 hb1 hb2 hb2 le_rfl le_rfl le_rfl le_rfl))
  | c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
    rcases hv with ⟨ha0, h0, h01, h1, h12, h2, h23, h3⟩
    simp only [cellLoHi] at hpa_ge
    simp only [vertSumReal, evalIntCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1),
      gval_sub (le_of_lt h2), gval_sub (le_of_lt h3)]
    set h0n := b0 - a0; set h1n := b1 - a1; set h2n := b2 - a2; set h3n := b3 - a3; set vp := h0n * h1n * h2n * h3n
    have hb0 : 0 < b0 := lt_trans ha0 h0; have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01
    have hb1 : 0 < b1 := lt_trans ha1 h1; have ha2 : 0 < a2 := lt_of_lt_of_le hb1 h12
    have hb2 : 0 < b2 := lt_trans ha2 h2; have ha3 : 0 < a3 := lt_of_lt_of_le hb2 h23
    have hb3 : 0 < b3 := lt_trans ha3 h3
    have l0 : a0 ≤ b0 := le_of_lt h0; have l1 : a1 ≤ b1 := le_of_lt h1
    have l2 : a2 ≤ b2 := le_of_lt h2; have l3 : a3 ≤ b3 := le_of_lt h3
    have hmax : b0 + b1 + b2 + b3 < pa := by omega
    have heq_fac : ((h0n : ℝ) / D_grid) * ((h1n : ℝ) / D_grid) * ((h2n : ℝ) / D_grid) * ((h3n : ℝ) / D_grid) / 16 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (16 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : S_scale * D_grid * h0n * h1n * h2n * h3n = S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 q0 q1 q2 q3 =>
      vertInt_ceil_bound (pa := pa) (vprod := vp) (fprod := 16) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)
        p0 p1 p2 p3 (by decide) (sum4_lt q0 q1 q2 q3 hmax)
    exact mul_sum4_le
      (mul_sum4_le (hb a0 a1 a2 a3 ha0 ha1 ha2 ha3 l0 l1 l2 l3) (hb a0 a1 a2 b3 ha0 ha1 ha2 hb3 l0 l1 l2 le_rfl)
        (hb a0 a1 b2 a3 ha0 ha1 hb2 ha3 l0 l1 le_rfl l3) (hb a0 a1 b2 b3 ha0 ha1 hb2 hb3 l0 l1 le_rfl le_rfl))
      (mul_sum4_le (hb a0 b1 a2 a3 ha0 hb1 ha2 ha3 l0 le_rfl l2 l3) (hb a0 b1 a2 b3 ha0 hb1 ha2 hb3 l0 le_rfl l2 le_rfl)
        (hb a0 b1 b2 a3 ha0 hb1 hb2 ha3 l0 le_rfl le_rfl l3) (hb a0 b1 b2 b3 ha0 hb1 hb2 hb3 l0 le_rfl le_rfl le_rfl))
      (mul_sum4_le (hb b0 a1 a2 a3 hb0 ha1 ha2 ha3 le_rfl l1 l2 l3) (hb b0 a1 a2 b3 hb0 ha1 ha2 hb3 le_rfl l1 l2 le_rfl)
        (hb b0 a1 b2 a3 hb0 ha1 hb2 ha3 le_rfl l1 le_rfl l3) (hb b0 a1 b2 b3 hb0 ha1 hb2 hb3 le_rfl l1 le_rfl le_rfl))
      (mul_sum4_le (hb b0 b1 a2 a3 hb0 hb1 ha2 ha3 le_rfl le_rfl l2 l3) (hb b0 b1 a2 b3 hb0 hb1 ha2 hb3 le_rfl le_rfl l2 le_rfl)
        (hb b0 b1 b2 a3 hb0 hb1 hb2 ha3 le_rfl le_rfl le_rfl l3) (hb b0 b1 b2 b3 hb0 hb1 hb2 hb3 le_rfl le_rfl le_rfl le_rfl))

private lemma evalWCell_bound {nm dm : Nat} (hdm : 0 < dm) {c : Cell4} (hv : c.valid) :
    ((nm : ℝ) / dm) * vertSumReal weight4 c ≤ (evalWCell nm dm c : ℝ) / S_scale := by
  have hDne : (D_grid : ℝ) ≠ 0 := ne_of_gt hDpos
  cases c with
  | c4 a b =>
    rcases hv with ⟨ha, hab⟩
    simp only [vertSumReal, evalWCell, gval_sub (le_of_lt hab)]
    set h := b - a; set vp := h * h * (h * h)
    have hbp : 0 < b := lt_trans ha hab
    have heq_fac : ((h : ℝ) / D_grid) ^ 4 / 120 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (120 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : nm * S_scale * D_grid * (h * h) * (h * h) = nm * S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac, ← mul_assoc]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 =>
      vertW_ceil_bound (nm := nm) (vprod := vp) (fprod := 120) hdm (by decide)
        (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) p0 p1 p2 p3
    exact mul_sum5_le (hb a a a a ha ha ha ha) (hb a a a b ha ha ha hbp) (hb a a b b ha ha hbp hbp)
      (hb a b b b ha hbp hbp hbp) (hb b b b b hbp hbp hbp hbp)
  | c31 a0 b0 a1 b1 =>
    rcases hv with ⟨ha0, h0, h01, h1⟩
    simp only [vertSumReal, evalWCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1)]
    set h0n := b0 - a0; set h1n := b1 - a1; set vp := h0n * h0n * h0n * h1n
    have hb0 : 0 < b0 := lt_trans ha0 h0; have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01; have hb1 : 0 < b1 := lt_trans ha1 h1
    have heq_fac : ((h0n : ℝ) / D_grid) ^ 3 * ((h1n : ℝ) / D_grid) / 48 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (48 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : nm * S_scale * D_grid * h0n * h0n * h0n * h1n = nm * S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac, ← mul_assoc]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 =>
      vertW_ceil_bound (nm := nm) (vprod := vp) (fprod := 48) hdm (by decide)
        (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) p0 p1 p2 p3
    exact mul_sum2_le
      (mul_sum4_le (hb a0 a0 a0 a1 ha0 ha0 ha0 ha1) (hb a0 a0 b0 a1 ha0 ha0 hb0 ha1)
        (hb a0 b0 b0 a1 ha0 hb0 hb0 ha1) (hb b0 b0 b0 a1 hb0 hb0 hb0 ha1))
      (mul_sum4_le (hb a0 a0 a0 b1 ha0 ha0 ha0 hb1) (hb a0 a0 b0 b1 ha0 ha0 hb0 hb1)
        (hb a0 b0 b0 b1 ha0 hb0 hb0 hb1) (hb b0 b0 b0 b1 hb0 hb0 hb0 hb1))
  | c13 a0 b0 a1 b1 =>
    rcases hv with ⟨ha0, h0, h01, h1⟩
    simp only [vertSumReal, evalWCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1)]
    set h0n := b0 - a0; set h1n := b1 - a1; set vp := h0n * h1n * h1n * h1n
    have hb0 : 0 < b0 := lt_trans ha0 h0; have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01; have hb1 : 0 < b1 := lt_trans ha1 h1
    have heq_fac : ((h0n : ℝ) / D_grid) * ((h1n : ℝ) / D_grid) ^ 3 / 48 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (48 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : nm * S_scale * D_grid * h0n * h1n * h1n * h1n = nm * S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac, ← mul_assoc]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 =>
      vertW_ceil_bound (nm := nm) (vprod := vp) (fprod := 48) hdm (by decide)
        (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) p0 p1 p2 p3
    exact mul_sum2_le
      (mul_sum4_le (hb a0 a1 a1 a1 ha0 ha1 ha1 ha1) (hb a0 a1 a1 b1 ha0 ha1 ha1 hb1)
        (hb a0 a1 b1 b1 ha0 ha1 hb1 hb1) (hb a0 b1 b1 b1 ha0 hb1 hb1 hb1))
      (mul_sum4_le (hb b0 a1 a1 a1 hb0 ha1 ha1 ha1) (hb b0 a1 a1 b1 hb0 ha1 ha1 hb1)
        (hb b0 a1 b1 b1 hb0 ha1 hb1 hb1) (hb b0 b1 b1 b1 hb0 hb1 hb1 hb1))
  | c22 a0 b0 a1 b1 =>
    rcases hv with ⟨ha0, h0, h01, h1⟩
    simp only [vertSumReal, evalWCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1)]
    set h0n := b0 - a0; set h1n := b1 - a1; set vp := h0n * h0n * h1n * h1n
    have hb0 : 0 < b0 := lt_trans ha0 h0; have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01; have hb1 : 0 < b1 := lt_trans ha1 h1
    have heq_fac : ((h0n : ℝ) / D_grid) ^ 2 * ((h1n : ℝ) / D_grid) ^ 2 / 36 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (36 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : nm * S_scale * D_grid * h0n * h0n * h1n * h1n = nm * S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac, ← mul_assoc]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 =>
      vertW_ceil_bound (nm := nm) (vprod := vp) (fprod := 36) hdm (by decide)
        (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) p0 p1 p2 p3
    exact mul_sum3_le
      (mul_sum3_le (hb a0 a0 a1 a1 ha0 ha0 ha1 ha1) (hb a0 a0 a1 b1 ha0 ha0 ha1 hb1) (hb a0 a0 b1 b1 ha0 ha0 hb1 hb1))
      (mul_sum3_le (hb a0 b0 a1 a1 ha0 hb0 ha1 ha1) (hb a0 b0 a1 b1 ha0 hb0 ha1 hb1) (hb a0 b0 b1 b1 ha0 hb0 hb1 hb1))
      (mul_sum3_le (hb b0 b0 a1 a1 hb0 hb0 ha1 ha1) (hb b0 b0 a1 b1 hb0 hb0 ha1 hb1) (hb b0 b0 b1 b1 hb0 hb0 hb1 hb1))
  | c211 a0 b0 a1 b1 a2 b2 =>
    rcases hv with ⟨ha0, h0, h01, h1, h12, h2⟩
    simp only [vertSumReal, evalWCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1), gval_sub (le_of_lt h2)]
    set h0n := b0 - a0; set h1n := b1 - a1; set h2n := b2 - a2; set vp := h0n * h0n * h1n * h2n
    have hb0 : 0 < b0 := lt_trans ha0 h0; have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01
    have hb1 : 0 < b1 := lt_trans ha1 h1; have ha2 : 0 < a2 := lt_of_lt_of_le hb1 h12; have hb2 : 0 < b2 := lt_trans ha2 h2
    have heq_fac : ((h0n : ℝ) / D_grid) ^ 2 * ((h1n : ℝ) / D_grid) * ((h2n : ℝ) / D_grid) / 24 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (24 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : nm * S_scale * D_grid * h0n * h0n * h1n * h2n = nm * S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac, ← mul_assoc]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 =>
      vertW_ceil_bound (nm := nm) (vprod := vp) (fprod := 24) hdm (by decide)
        (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) p0 p1 p2 p3
    exact mul_sum3_le
      (mul_sum4_le (hb a0 a0 a1 a2 ha0 ha0 ha1 ha2) (hb a0 a0 a1 b2 ha0 ha0 ha1 hb2)
        (hb a0 a0 b1 a2 ha0 ha0 hb1 ha2) (hb a0 a0 b1 b2 ha0 ha0 hb1 hb2))
      (mul_sum4_le (hb a0 b0 a1 a2 ha0 hb0 ha1 ha2) (hb a0 b0 a1 b2 ha0 hb0 ha1 hb2)
        (hb a0 b0 b1 a2 ha0 hb0 hb1 ha2) (hb a0 b0 b1 b2 ha0 hb0 hb1 hb2))
      (mul_sum4_le (hb b0 b0 a1 a2 hb0 hb0 ha1 ha2) (hb b0 b0 a1 b2 hb0 hb0 ha1 hb2)
        (hb b0 b0 b1 a2 hb0 hb0 hb1 ha2) (hb b0 b0 b1 b2 hb0 hb0 hb1 hb2))
  | c121 a0 b0 a1 b1 a2 b2 =>
    rcases hv with ⟨ha0, h0, h01, h1, h12, h2⟩
    simp only [vertSumReal, evalWCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1), gval_sub (le_of_lt h2)]
    set h0n := b0 - a0; set h1n := b1 - a1; set h2n := b2 - a2; set vp := h0n * h1n * h1n * h2n
    have hb0 : 0 < b0 := lt_trans ha0 h0; have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01
    have hb1 : 0 < b1 := lt_trans ha1 h1; have ha2 : 0 < a2 := lt_of_lt_of_le hb1 h12; have hb2 : 0 < b2 := lt_trans ha2 h2
    have heq_fac : ((h0n : ℝ) / D_grid) * ((h1n : ℝ) / D_grid) ^ 2 * ((h2n : ℝ) / D_grid) / 24 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (24 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : nm * S_scale * D_grid * h0n * h1n * h1n * h2n = nm * S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac, ← mul_assoc]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 =>
      vertW_ceil_bound (nm := nm) (vprod := vp) (fprod := 24) hdm (by decide)
        (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) p0 p1 p2 p3
    exact mul_sum3_le
      (mul_sum4_le (hb a0 a1 a1 a2 ha0 ha1 ha1 ha2) (hb a0 a1 a1 b2 ha0 ha1 ha1 hb2)
        (hb b0 a1 a1 a2 hb0 ha1 ha1 ha2) (hb b0 a1 a1 b2 hb0 ha1 ha1 hb2))
      (mul_sum4_le (hb a0 a1 b1 a2 ha0 ha1 hb1 ha2) (hb a0 a1 b1 b2 ha0 ha1 hb1 hb2)
        (hb b0 a1 b1 a2 hb0 ha1 hb1 ha2) (hb b0 a1 b1 b2 hb0 ha1 hb1 hb2))
      (mul_sum4_le (hb a0 b1 b1 a2 ha0 hb1 hb1 ha2) (hb a0 b1 b1 b2 ha0 hb1 hb1 hb2)
        (hb b0 b1 b1 a2 hb0 hb1 hb1 ha2) (hb b0 b1 b1 b2 hb0 hb1 hb1 hb2))
  | c112 a0 b0 a1 b1 a2 b2 =>
    rcases hv with ⟨ha0, h0, h01, h1, h12, h2⟩
    simp only [vertSumReal, evalWCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1), gval_sub (le_of_lt h2)]
    set h0n := b0 - a0; set h1n := b1 - a1; set h2n := b2 - a2; set vp := h0n * h1n * h2n * h2n
    have hb0 : 0 < b0 := lt_trans ha0 h0; have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01
    have hb1 : 0 < b1 := lt_trans ha1 h1; have ha2 : 0 < a2 := lt_of_lt_of_le hb1 h12; have hb2 : 0 < b2 := lt_trans ha2 h2
    have heq_fac : ((h0n : ℝ) / D_grid) * ((h1n : ℝ) / D_grid) * ((h2n : ℝ) / D_grid) ^ 2 / 24 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (24 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : nm * S_scale * D_grid * h0n * h1n * h2n * h2n = nm * S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac, ← mul_assoc]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 =>
      vertW_ceil_bound (nm := nm) (vprod := vp) (fprod := 24) hdm (by decide)
        (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) p0 p1 p2 p3
    exact mul_sum3_le
      (mul_sum4_le (hb a0 a1 a2 a2 ha0 ha1 ha2 ha2) (hb a0 b1 a2 a2 ha0 hb1 ha2 ha2)
        (hb b0 a1 a2 a2 hb0 ha1 ha2 ha2) (hb b0 b1 a2 a2 hb0 hb1 ha2 ha2))
      (mul_sum4_le (hb a0 a1 a2 b2 ha0 ha1 ha2 hb2) (hb a0 b1 a2 b2 ha0 hb1 ha2 hb2)
        (hb b0 a1 a2 b2 hb0 ha1 ha2 hb2) (hb b0 b1 a2 b2 hb0 hb1 ha2 hb2))
      (mul_sum4_le (hb a0 a1 b2 b2 ha0 ha1 hb2 hb2) (hb a0 b1 b2 b2 ha0 hb1 hb2 hb2)
        (hb b0 a1 b2 b2 hb0 ha1 hb2 hb2) (hb b0 b1 b2 b2 hb0 hb1 hb2 hb2))
  | c1111 a0 b0 a1 b1 a2 b2 a3 b3 =>
    rcases hv with ⟨ha0, h0, h01, h1, h12, h2, h23, h3⟩
    simp only [vertSumReal, evalWCell, gval_sub (le_of_lt h0), gval_sub (le_of_lt h1),
      gval_sub (le_of_lt h2), gval_sub (le_of_lt h3)]
    set h0n := b0 - a0; set h1n := b1 - a1; set h2n := b2 - a2; set h3n := b3 - a3; set vp := h0n * h1n * h2n * h3n
    have hb0 : 0 < b0 := lt_trans ha0 h0; have ha1 : 0 < a1 := lt_of_lt_of_le hb0 h01
    have hb1 : 0 < b1 := lt_trans ha1 h1; have ha2 : 0 < a2 := lt_of_lt_of_le hb1 h12
    have hb2 : 0 < b2 := lt_trans ha2 h2; have ha3 : 0 < a3 := lt_of_lt_of_le hb2 h23; have hb3 : 0 < b3 := lt_trans ha3 h3
    have heq_fac : ((h0n : ℝ) / D_grid) * ((h1n : ℝ) / D_grid) * ((h2n : ℝ) / D_grid) * ((h3n : ℝ) / D_grid) / 16 = ((vp : ℝ) / (D_grid : ℝ) ^ 4) / (16 : Nat) := by
      dsimp only [vp]; push_cast; ring
    have hnum_eq : nm * S_scale * D_grid * h0n * h1n * h2n * h3n = nm * S_scale * D_grid * vp := by dsimp only [vp]; ring
    simp only [hnum_eq, Nat.cast_add, add_div]; rw [heq_fac, ← mul_assoc]
    have hb := fun x0 x1 x2 x3 p0 p1 p2 p3 =>
      vertW_ceil_bound (nm := nm) (vprod := vp) (fprod := 16) hdm (by decide)
        (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) p0 p1 p2 p3
    exact mul_sum4_le
      (mul_sum4_le (hb a0 a1 a2 a3 ha0 ha1 ha2 ha3) (hb a0 a1 a2 b3 ha0 ha1 ha2 hb3)
        (hb a0 a1 b2 a3 ha0 ha1 hb2 ha3) (hb a0 a1 b2 b3 ha0 ha1 hb2 hb3))
      (mul_sum4_le (hb a0 b1 a2 a3 ha0 hb1 ha2 ha3) (hb a0 b1 a2 b3 ha0 hb1 ha2 hb3)
        (hb a0 b1 b2 a3 ha0 hb1 hb2 ha3) (hb a0 b1 b2 b3 ha0 hb1 hb2 hb3))
      (mul_sum4_le (hb b0 a1 a2 a3 hb0 ha1 ha2 ha3) (hb b0 a1 a2 b3 hb0 ha1 ha2 hb3)
        (hb b0 a1 b2 a3 hb0 ha1 hb2 ha3) (hb b0 a1 b2 b3 hb0 ha1 hb2 hb3))
      (mul_sum4_le (hb b0 b1 a2 a3 hb0 hb1 ha2 ha3) (hb b0 b1 a2 b3 hb0 hb1 ha2 hb3)
        (hb b0 b1 b2 a3 hb0 hb1 hb2 ha3) (hb b0 b1 b2 b3 hb0 hb1 hb2 hb3))

private lemma evalBndCell_sound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {pa pb : Nat} {φ : ℝ} (hpa : gval pa ≤ φ) (hpb : φ ≤ gval pb)
    {c : Cell4} (hv : c.valid) {v : Nat} (heval : evalBndCell pa pb c = some v) :
    ∫ x in c.set, integrand4 ω φ x ≤ (v : ℝ) / S_scale := by
  unfold evalBndCell at heval
  set lh := cellLoHi c
  rcases lh_eq : lh with ⟨l0, l1, l2, l3, u0, u1, u2, u3⟩
  have hbd := c.valid_bounds hv
  rw [lh_eq] at heval
  rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hbd
  dsimp only at hbd heval
  rcases hbd with ⟨hl0, hlu0, hl01, hlu1, hl12, hlu2, hl23, hlu3⟩
  have hl1_pos : 0 < l1 := by omega
  have hl2_pos : 0 < l2 := by omega
  have hl3_pos : 0 < l3 := by omega
  set wden := 48 * l0 * l1 * l2 * l2 * l3
  have hwden_pos : 0 < wden := by dsimp [wden]; positivity
  have hwble : Nat.ble 1 wden = true := Nat.ble_eq.mpr hwden_pos
  rw [hwble] at heval
  dsimp only at heval
  set R := pb - (l0 + l1 + l2 + l2 + l3)
  set v48 := min2 (cellVol48 c) (box4Hs48 (u0 - l0) (u1 - l1) (u2 - l2) (u3 - l3) R)
  set H : Set R4 := {x : R4 | x.1 + x.2.1 + 2 * x.2.2.1 + x.2.2.2 ≤ gval pb}
  have hHc : IsClosed H := isClosed_le (by fun_prop) continuous_const
  have hHm : MeasurableSet H := hHc.measurableSet
  -- First restrict integral from c.set to c.set ∩ H (outside H, ω = 0!)
  have hrest : ∫ x in c.set, integrand4 ω φ x = ∫ x in c.set ∩ H, integrand4 ω φ x := by
    rw [← setIntegral_indicator hHm]
    apply setIntegral_congr_fun c.measurableSet_set
    intro x hx
    by_cases hxH : x ∈ H
    · simp [hxH]
    · simp only [indicator_of_notMem hxH, integrand4]
      have hxb := c.set_subset_box hx
      unfold Cell4.box at hxb
      rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hxb
      have hx2 : 0 < x.2.2.1 := lt_of_lt_of_le (gval_pos (by omega)) hxb.2.2.1.1
      have hu : (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1 < 1 := by
        rw [div_lt_one hx2]; simp only [H, mem_ofPred_eq, not_le] at hxH; linarith
      rw [hz _ hu, zero_div]
  -- Volume of c.set ∩ H is ≤ v48 / (48 * D^4)
  have hvol_le : ∫ _ in c.set ∩ H, (1 : ℝ) ≤ (v48 : ℝ) / (48 * (D_grid : ℝ) ^ 4) := by
    have h1 : ∫ _ in c.set ∩ H, (1 : ℝ) ≤ ((cellVol48 c : Nat) : ℝ) / (48 * (D_grid : ℝ) ^ 4) := by
      rw [← cell4_vol_eq hv]
      exact setIntegral_mono_set (continuousOn_const.integrableOn_compact c.isCompact_set)
        (ae_restrict_of_forall_mem c.measurableSet_set (fun _ _ => zero_le_one))
        (Filter.Eventually.of_forall inter_subset_left)
    have h2 : ∫ _ in c.set ∩ H, (1 : ℝ) ≤
        ((box4Hs48 (u0 - l0) (u1 - l1) (u2 - l2) (u3 - l3) R : Nat) : ℝ) / (48 * (D_grid : ℝ) ^ 4) := by
      have hsub : c.set ∩ H ⊆ c.box ∩ H := inter_subset_inter_left H c.set_subset_box
      have hmono : ∫ _ in c.set ∩ H, (1 : ℝ) ≤ ∫ _ in c.box ∩ H, (1 : ℝ) :=
        setIntegral_mono_set
          (continuousOn_const.integrableOn_compact (c.isCompact_box.of_isClosed_subset (c.isCompact_box.isClosed.inter hHc) inter_subset_left))
          (ae_restrict_of_forall_mem (c.isCompact_box.measurableSet.inter hHm) (fun _ _ => zero_le_one))
          (Filter.Eventually.of_forall hsub)
      refine le_trans hmono ?_
      unfold Cell4.box
      rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq]
      exact box4_halfspace_vol (le_of_lt hlu0) (le_of_lt hlu1) (le_of_lt hlu2) (le_of_lt hlu3)
    dsimp only [v48, min2]
    cases hle : Nat.ble (cellVol48 c) (box4Hs48 (u0 - l0) (u1 - l1) (u2 - l2) (u3 - l3) R) with
    | true => exact h1
    | false => exact h2
  have hcomp_cH : IsCompact (c.set ∩ H) :=
    c.isCompact_set.of_isClosed_subset (c.isClosed_set.inter hHc) inter_subset_left
  have hint_cH : IntegrableOn (integrand4 ω φ) (c.set ∩ H) volume :=
    (integrand4_integrableOn hω hz φ hv).mono_set inter_subset_left
  have hM_bound : ∀ {M : ℝ}, 0 ≤ M → (∀ x ∈ c.set ∩ H, integrand4 ω φ x ≤ M) →
      ∫ x in c.set, integrand4 ω φ x ≤ M * ((v48 : ℝ) / (48 * (D_grid : ℝ) ^ 4)) := by
    intro M hM hpt
    rw [hrest]
    have h1 : ∫ x in c.set ∩ H, integrand4 ω φ x ≤ ∫ _ in c.set ∩ H, M :=
      setIntegral_mono_on hint_cH (continuousOn_const.integrableOn_compact hcomp_cH)
        (c.measurableSet_set.inter hHm) hpt
    have h2 : ∫ _ in c.set ∩ H, M = M * ∫ _ in c.set ∩ H, (1 : ℝ) := by
      have : (fun _ : R4 => M) = (fun _ : R4 => M * 1) := by ext; ring
      rw [this, integral_const_mul]
    rw [h2] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left hvol_le hM)
  have hl0r : (0 : ℝ) < l0 := by exact_mod_cast hl0
  have hl1r : (0 : ℝ) < l1 := by exact_mod_cast hl1_pos
  have hl2r : (0 : ℝ) < l2 := by exact_mod_cast hl2_pos
  have hl3r : (0 : ℝ) < l3 := by exact_mod_cast hl3_pos
  have hgl0 : 0 < gval l0 := gval_pos hl0
  have hgl1 : 0 < gval l1 := gval_pos hl1_pos
  have hgl2 : 0 < gval l2 := gval_pos hl2_pos
  have hgl3 : 0 < gval l3 := gval_pos hl3_pos
  have hxb_ge : ∀ x ∈ c.set, gval l0 ≤ x.1 ∧ gval l1 ≤ x.2.1 ∧ gval l2 ≤ x.2.2.1 ∧ gval l3 ≤ x.2.2.2 ∧
      x.1 ≤ gval u0 ∧ x.2.1 ≤ gval u1 ∧ x.2.2.1 ≤ gval u2 ∧ x.2.2.2 ≤ gval u3 := by
    intro x hx
    have hxb := c.set_subset_box hx
    unfold Cell4.box at hxb
    rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hxb
    exact ⟨hxb.1.1, hxb.2.1.1, hxb.2.2.1.1, hxb.2.2.2.1, hxb.1.2, hxb.2.1.2, hxb.2.2.1.2, hxb.2.2.2.2⟩
  have hw_le : ∀ x ∈ c.set, weight4 x ≤ 1 / (gval l0 * gval l1 * gval l2 * gval l2 * gval l3) := by
    intro x hx
    rcases hxb_ge x hx with ⟨g0, g1, g2, g3, _⟩
    have hx0p : 0 < x.1 := lt_of_lt_of_le hgl0 g0
    have hx1p : 0 < x.2.1 := lt_of_lt_of_le hgl1 g1
    have hx2p : 0 < x.2.2.1 := lt_of_lt_of_le hgl2 g2
    unfold weight4
    apply one_div_le_one_div_of_le (by positivity)
    have p1 : gval l0 * gval l1 ≤ x.1 * x.2.1 := mul_le_mul g0 g1 (le_of_lt hgl1) (le_of_lt hx0p)
    have p2 : gval l0 * gval l1 * gval l2 ≤ x.1 * x.2.1 * x.2.2.1 := mul_le_mul p1 g2 (le_of_lt hgl2) (by positivity)
    have p3 : gval l0 * gval l1 * gval l2 * gval l2 ≤ x.1 * x.2.1 * x.2.2.1 * x.2.2.1 := mul_le_mul p2 g2 (le_of_lt hgl2) (by positivity)
    exact mul_le_mul p3 g3 (le_of_lt hgl3) (by positivity)
  cases hcase1 : Nat.ble (u0 + u1 + u2 + u2 + u3) pa with
  | true =>
    rw [hcase1] at heval; simp only [Option.some.injEq] at heval; subst heval
    have hpa_ge : u0 + u1 + u2 + u2 + u3 ≤ pa := Nat.ble_eq.mp hcase1
    set diff := pa - (u0 + u1 + u2 + u3)
    have hdiff_ge : u2 ≤ diff := by omega
    have hdiff_pos : 0 < diff := by omega
    set num_om := max2 (7 * diff) (12 * u2)
    set den_om := 12 * diff
    have hden_pos : 0 < den_om * wden := by dsimp [den_om]; positivity
    have hpt : ∀ x ∈ c.set ∩ H, integrand4 ω φ x ≤
        ((num_om : ℝ) / den_om) * (1 / (gval l0 * gval l1 * gval l2 * gval l2 * gval l3)) := by
      intro x ⟨hx, _⟩
      rcases hxb_ge x hx with ⟨g0, g1, g2, g3, gu0, gu1, gu2, gu3⟩
      have hu2_pos : 0 < gval u2 := gval_pos (by omega)
      have hx2_pos : 0 < x.2.2.1 := lt_of_lt_of_le hgl2 g2
      have humin1 : (1 : ℝ) ≤ (gval diff) / gval u2 := by
        rw [one_le_div hu2_pos]; exact gval_le hdiff_ge
      have humin_le : (gval diff) / gval u2 ≤ (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1 := by
        have hnum : gval diff ≤ φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2) := by
          have hd : gval diff = gval pa - gval u0 - gval u1 - gval u2 - gval u3 := by
            have := gval_sub (a := u0 + u1 + u2 + u3) (b := pa) (by omega)
            simp only [gval_add] at this; dsimp only [diff]; unfold gval at this ⊢; linarith only [this]
          linarith
        calc gval diff / gval u2 ≤ gval diff / x.2.2.1 :=
              div_le_div_of_nonneg_left (le_of_lt (gval_pos hdiff_pos)) hx2_pos gu2
          _ ≤ (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1 :=
              div_le_div_of_nonneg_right hnum (le_of_lt hx2_pos)
      have hom1 := buchstab_le_max_inv hω humin1 humin_le
      have hom2 : max (7 / 12 : ℝ) (1 / (gval diff / gval u2)) ≤ (num_om : ℝ) / den_om := by
        have hdiffr : (0 : ℝ) < diff := by exact_mod_cast hdiff_pos
        apply max_le
        · have h7 : 7 * diff ≤ num_om := left_le_max2 _ _
          have : (7 : ℝ) * diff ≤ num_om := by exact_mod_cast h7
          dsimp [den_om]; push_cast; rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
        · have h12 : 12 * u2 ≤ num_om := right_le_max2 _ _
          have h12r : (12 : ℝ) * u2 ≤ num_om := by exact_mod_cast h12
          have hinv : 1 / (gval diff / gval u2) = (u2 : ℝ) / diff := by
            unfold gval; rw [one_div_div, div_div_div_cancel_right₀ (ne_of_gt hDpos)]
          rw [hinv]; dsimp [den_om]; push_cast; rw [div_le_div_iff₀ hdiffr (by positivity)]
          have hm := mul_le_mul_of_nonneg_right h12r (le_of_lt hdiffr)
          linarith only [hm]
      have hom : ω ((φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1) ≤ (num_om : ℝ) / den_om :=
        le_trans hom1 hom2
      have hw := hw_le x hx
      have hrew : integrand4 ω φ x = ω ((φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1) * weight4 x := by
        unfold integrand4 weight4; ring
      rw [hrew]
      exact mul_le_mul hom hw (weight4_nonneg hv x hx) (by positivity)
    have hbd1 := hM_bound (by positivity) hpt
    have hceil := le_mul_ceilDiv (a := S_scale * D_grid * v48 * num_om) hden_pos
    have hceil_r : (S_scale : ℝ) * D_grid * v48 * num_om ≤
        (den_om : ℝ) * wden * (ceilDiv (S_scale * D_grid * v48 * num_om) (den_om * wden) : ℝ) := by
      exact_mod_cast hceil
    have hdenr : (0 : ℝ) < den_om := by dsimp [den_om]; positivity
    have hwdenr : (0 : ℝ) < wden := by exact_mod_cast hwden_pos
    have hlhs_eq : ((num_om : ℝ) / den_om) * (1 / (gval l0 * gval l1 * gval l2 * gval l2 * gval l3)) *
        ((v48 : ℝ) / (48 * (D_grid : ℝ) ^ 4)) =
        ((D_grid : ℝ) * v48 * num_om) / ((den_om : ℝ) * wden) := by
      dsimp only [wden]; unfold gval; push_cast
      rw [mul_assoc, weight_mul_vol (ne_of_gt hDpos), div_mul_div_comm]; ring
    refine le_trans hbd1 ?_
    rw [hlhs_eq, div_le_div_iff₀ (by positivity) hSpos]
    linarith
  | false =>
    rw [hcase1] at heval; dsimp only at heval
    have hfallback : ∫ x in c.set, integrand4 ω φ x ≤
        (ceilDiv (S_scale * D_grid * v48) wden : ℝ) / S_scale := by
      have hpt : ∀ x ∈ c.set ∩ H, integrand4 ω φ x ≤ 1 / (gval l0 * gval l1 * gval l2 * gval l2 * gval l3) := by
        intro x ⟨hx, _⟩
        have hrew : integrand4 ω φ x = ω ((φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1) * weight4 x := by
          unfold integrand4 weight4; ring
        rw [hrew]
        have := mul_le_mul (buchstab_le_one hω hz ((φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1))
          (hw_le x hx) (weight4_nonneg hv x hx) zero_le_one
        linarith only [this]
      have hbd1 := hM_bound (by positivity) hpt
      have hceil := le_mul_ceilDiv (a := S_scale * D_grid * v48) hwden_pos
      have hceil_r : (S_scale : ℝ) * D_grid * v48 ≤
          (wden : ℝ) * (ceilDiv (S_scale * D_grid * v48) wden : ℝ) := by exact_mod_cast hceil
      have hwdenr : (0 : ℝ) < wden := by exact_mod_cast hwden_pos
      have hlhs_eq : (1 / (gval l0 * gval l1 * gval l2 * gval l2 * gval l3)) *
          ((v48 : ℝ) / (48 * (D_grid : ℝ) ^ 4)) = ((D_grid : ℝ) * v48) / (wden : ℝ) := by
        dsimp only [wden]; unfold gval; push_cast
        exact weight_mul_vol (ne_of_gt hDpos)
      refine le_trans hbd1 ?_
      rw [hlhs_eq, div_le_div_iff₀ hwdenr hSpos]; linarith only [hceil_r]
    cases hcase2a : Nat.ble (l0 + l1 + l2 + l2 + l3 + 1) pa with
    | false =>
      rw [hcase2a] at heval; simp only [Option.some.injEq] at heval; subst heval
      exact hfallback
    | true =>
      rw [hcase2a] at heval
      cases hcase2b : Nat.ble pb (l0 + l1 + 3 * l2 + l3) with
      | false =>
        rw [hcase2b] at heval; simp only [Option.some.injEq] at heval; subst heval
        exact hfallback
      | true =>
        rw [hcase2b] at heval; simp only [Option.some.injEq] at heval; subst heval
        have hpa_gt : l0 + l1 + l2 + l2 + l3 < pa := by have := Nat.ble_eq.mp hcase2a; omega
        have hpb_le : pb ≤ l0 + l1 + 3 * l2 + l3 := Nat.ble_eq.mp hcase2b
        set Ra := pa - (l0 + l1 + l2 + l2 + l3)
        have hRa_pos : 0 < Ra := by omega
        have hden_pos : 0 < wden * (l2 + l3 + Ra) := by positivity
        have hRa_real : gval Ra = gval pa - gval l0 - gval l1 - 2 * gval l2 - gval l3 := by
          have := gval_sub (a := l0 + l1 + l2 + l2 + l3) (b := pa) (by omega)
          simp only [gval_add] at this; dsimp only [Ra]; unfold gval at this ⊢; linarith only [this]
        have hgRa : 0 < gval Ra := gval_pos hRa_pos
        set boost : ℝ := 1 + gval Ra / (gval l2 + gval l3)
        have hboost_pos : 0 < boost := by dsimp [boost]; positivity
        have hpt : ∀ x ∈ c.set ∩ H, integrand4 ω φ x ≤
            1 / (gval l0 * gval l1 * gval l2 * gval l2 * gval l3 * boost) := by
          intro x ⟨hx, _⟩
          rcases hxb_ge x hx with ⟨g0, g1, g2, g3, _⟩
          have hx2_pos : 0 < x.2.2.1 := lt_of_lt_of_le hgl2 g2
          by_cases hu1 : (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1 < 1
          · unfold integrand4; rw [hz _ hu1, zero_div]; positivity
          · push Not at hu1
            have hu2 : (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1 ≤ 2 := by
              rw [div_le_iff₀ hx2_pos]
              have hpbr : gval pb ≤ gval l0 + gval l1 + 3 * gval l2 + gval l3 := by
                have := gval_le hpb_le; simp only [gval_add, gval_3mul] at this; linarith only [this]
              linarith
            have hrew : integrand4 ω φ x = 1 / (x.1 * x.2.1 * x.2.2.1 * x.2.2.2 *
                (φ - x.1 - x.2.1 - x.2.2.1 - x.2.2.2)) := by
              unfold integrand4
              rw [hω.2.1 _ hu1 hu2]
              rw [show φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2) = φ - x.1 - x.2.1 - x.2.2.1 - x.2.2.2 by ring]
              exact inv_u_div_weight (ne_of_gt hx2_pos)
            rw [hrew]
            apply one_div_le_one_div_of_le (by positivity)
            have hboost_ineq := boundary_denom_boost hgl0 (gval_le hl01) (gval_le hl12) (gval_le hl23)
              g0 g1 g2 g3 hpa (by rw [← hRa_real]; exact gval_pos hRa_pos)
              (by have := (one_le_div hx2_pos).mp hu1; linarith)
            simpa [boost, ← hRa_real] using hboost_ineq
        have hbd1 := hM_bound (by positivity) hpt
        have hceil := le_mul_ceilDiv (a := S_scale * D_grid * v48 * (l2 + l3)) hden_pos
        have hceil_r : (S_scale : ℝ) * D_grid * v48 * ((l2 : ℝ) + l3) ≤
            (wden : ℝ) * ((l2 : ℝ) + l3 + Ra) *
              (ceilDiv (S_scale * D_grid * v48 * (l2 + l3)) (wden * (l2 + l3 + Ra)) : ℝ) := by
          have hcast : ((S_scale * D_grid * v48 * (l2 + l3) : Nat) : ℝ) ≤
              ((wden * (l2 + l3 + Ra) *
                ceilDiv (S_scale * D_grid * v48 * (l2 + l3)) (wden * (l2 + l3 + Ra)) : Nat) : ℝ) := by
            exact_mod_cast hceil
          push_cast at hcast; linarith
        have hwdenr : (0 : ℝ) < wden := by exact_mod_cast hwden_pos
        have h23R : (0 : ℝ) < (l2 : ℝ) + l3 + Ra := by positivity
        have hlhs_eq : (1 / (gval l0 * gval l1 * gval l2 * gval l2 * gval l3 * boost)) *
            ((v48 : ℝ) / (48 * (D_grid : ℝ) ^ 4)) =
            ((D_grid : ℝ) * v48 * ((l2 : ℝ) + l3)) / ((wden : ℝ) * ((l2 : ℝ) + l3 + Ra)) := by
          have h23pos : (0 : ℝ) < (l2 : ℝ) + l3 := by linarith only [hl2r, hl3r]
          have hboost_eq : boost = ((l2 : ℝ) + l3 + Ra) / ((l2 : ℝ) + l3) := by
            dsimp only [boost]; unfold gval
            rw [← add_div, div_div_div_cancel_right₀ (ne_of_gt hDpos), one_add_div (ne_of_gt h23pos)]
          rw [show 1 / (gval l0 * gval l1 * gval l2 * gval l2 * gval l3 * boost) =
                (1 / boost) * (1 / (gval l0 * gval l1 * gval l2 * gval l2 * gval l3)) by ring,
              mul_assoc, hboost_eq, one_div_div]
          dsimp only [wden]; unfold gval; push_cast
          rw [weight_mul_vol (ne_of_gt hDpos), div_mul_div_comm]; ring
        refine le_trans hbd1 ?_
        rw [hlhs_eq, div_le_div_iff₀ (by positivity) hSpos]
        linarith

private lemma evalGen_sound {leaf : CTree → Cell4 → Option Nat} {g : R4 → ℝ}
    (hg_nn : ∀ {c : Cell4}, c.valid → ∀ x ∈ c.set, 0 ≤ g x)
    (hg_int : ∀ {c : Cell4}, c.valid → IntegrableOn g c.set volume)
    (hZ : ∀ {c : Cell4} {v : Nat}, c.valid → leaf .Z c = some v → ∫ x in c.set, g x ≤ (v : ℝ) / S_scale)
    (hI : ∀ {c : Cell4} {v : Nat}, c.valid → leaf .I c = some v → ∫ x in c.set, g x ≤ (v : ℝ) / S_scale)
    (hT : ∀ {c : Cell4} {v : Nat}, c.valid → leaf .T c = some v → ∫ x in c.set, g x ≤ (v : ℝ) / S_scale)
    (hB : ∀ {c : Cell4} {v : Nat}, c.valid → leaf .B c = some v → ∫ x in c.set, g x ≤ (v : ℝ) / S_scale)
    (t : CTree) (c : Cell4) (hv : c.valid) {v : Nat}
    (heval : evalGen leaf t c = some v) :
    ∫ x in c.set, g x ≤ (v : ℝ) / S_scale := by
  induction t generalizing c v with
  | Z => exact hZ hv heval
  | I => exact hI hv heval
  | T => exact hT hv heval
  | B => exact hB hv heval
  | S2 idx t0 t1 ih0 ih1 =>
    have hsp2 : ∀ {c0 c1 : Cell4} {v0 v1 : Nat},
        evalGen leaf t0 c0 = some v0 → evalGen leaf t1 c1 = some v1 →
        c0.valid → c1.valid → c.set ⊆ c0.set ∪ c1.set →
        v = v0 + v1 → ∫ x in c.set, g x ≤ (v : ℝ) / S_scale := by
      intro c0 c1 v0 v1 he0 he1 hv0 hv1 hsub hv_eq
      have hle := setIntegral_le_of_subset_union2 hsub c0.measurableSet_set c1.measurableSet_set
        (hg_nn hv0) (hg_nn hv1)
        (hg_int hv0) (hg_int hv1)
      have b0 := ih0 c0 hv0 he0; have b1 := ih1 c1 hv1 he1
      rw [hv_eq, Nat.cast_add, add_div]; linarith
    cases c <;> cases idx <;> try (simp only [evalGen] at heval; cases heval)
    case c31.succ idx' =>
      cases idx' <;> try (simp only [evalGen] at heval; cases heval)
      rename_i a0 b0 a1 b1
      simp only [Nat.zero_add, evalGen] at heval
      cases hs : canSplit a1 b1 with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3⟩
        cases e0 : evalGen leaf t0 (.c31 a0 b0 ((a1 + b1) / 2) b1) <;>
        cases e1 : evalGen leaf t1 (.c31 a0 b0 a1 ((a1 + b1) / 2)) <;>
          simp only [e0, e1] at heval
        any_goals cases heval
        refine hsp2 e0 e1 ⟨h0, h1, by omega, hm2⟩ ⟨h0, h1, h2, hm1⟩ ?_ rfl
        intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
        rcases le_total (gval ((a1 + b1) / 2)) x.2.2.2 with h | h
        · left; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, h, hx.2.2.2.2.2⟩
        · right; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, h⟩
    case c13.zero a0 b0 a1 b1 =>
      simp only [evalGen] at heval
      cases hs : canSplit a0 b0 with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3⟩
        cases e0 : evalGen leaf t0 (.c13 ((a0 + b0) / 2) b0 a1 b1) <;>
        cases e1 : evalGen leaf t1 (.c13 a0 ((a0 + b0) / 2) a1 b1) <;>
          simp only [e0, e1] at heval
        any_goals cases heval
        refine hsp2 e0 e1 ⟨by omega, hm2, h2, h3⟩ ⟨h0, hm1, by omega, h3⟩ ?_ rfl
        intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
        rcases le_total (gval ((a0 + b0) / 2)) x.1 with h | h
        · left; exact ⟨h, hx.2.1, hx.2.2⟩
        · right; exact ⟨hx.1, h, hx.2.2⟩
    case c211.succ a0 b0 a1 b1 a2 b2 idx' =>
      cases idx' with
      | zero =>
        simp only [Nat.zero_add, evalGen] at heval
        cases hs : canSplit a1 b1 with
        | false => rw [hs] at heval; cases heval
        | true =>
          rw [hs] at heval; dsimp only at heval
          have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5⟩
          cases e0 : evalGen leaf t0 (.c211 a0 b0 ((a1 + b1) / 2) b1 a2 b2) <;>
          cases e1 : evalGen leaf t1 (.c211 a0 b0 a1 ((a1 + b1) / 2) a2 b2) <;>
            simp only [e0, e1] at heval
          any_goals cases heval
          refine hsp2 e0 e1 ⟨h0, h1, by omega, hm2, h4, h5⟩ ⟨h0, h1, h2, hm1, by omega, h5⟩ ?_ rfl
          intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
          rcases le_total (gval ((a1 + b1) / 2)) x.2.2.1 with h | h
          · left; exact ⟨hx.1, hx.2.1, hx.2.2.1, h, hx.2.2.2.2.1, hx.2.2.2.2.2⟩
          · right; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, h, hx.2.2.2.2.2⟩
      | succ idx'' =>
        cases idx'' <;> try (simp only [evalGen] at heval; cases heval)
        simp only [Nat.zero_add, Nat.reduceAdd, evalGen] at heval
        cases hs : canSplit a2 b2 with
        | false => rw [hs] at heval; cases heval
        | true =>
          rw [hs] at heval; dsimp only at heval
          have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5⟩
          cases e0 : evalGen leaf t0 (.c211 a0 b0 a1 b1 ((a2 + b2) / 2) b2) <;>
          cases e1 : evalGen leaf t1 (.c211 a0 b0 a1 b1 a2 ((a2 + b2) / 2)) <;>
            simp only [e0, e1] at heval
          any_goals cases heval
          refine hsp2 e0 e1 ⟨h0, h1, h2, h3, by omega, hm2⟩ ⟨h0, h1, h2, h3, h4, hm1⟩ ?_ rfl
          intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
          rcases le_total (gval ((a2 + b2) / 2)) x.2.2.2 with h | h
          · left; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, h, hx.2.2.2.2.2.2⟩
          · right; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, h⟩
    case c121.zero a0 b0 a1 b1 a2 b2 =>
      simp only [evalGen] at heval
      cases hs : canSplit a0 b0 with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5⟩
        cases e0 : evalGen leaf t0 (.c121 ((a0 + b0) / 2) b0 a1 b1 a2 b2) <;>
        cases e1 : evalGen leaf t1 (.c121 a0 ((a0 + b0) / 2) a1 b1 a2 b2) <;>
          simp only [e0, e1] at heval
        any_goals cases heval
        refine hsp2 e0 e1 ⟨by omega, hm2, h2, h3, h4, h5⟩ ⟨h0, hm1, by omega, h3, h4, h5⟩ ?_ rfl
        intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
        rcases le_total (gval ((a0 + b0) / 2)) x.1 with h | h
        · left; exact ⟨h, hx.2.1, hx.2.2⟩
        · right; exact ⟨hx.1, h, hx.2.2⟩
    case c121.succ a0 b0 a1 b1 a2 b2 idx' =>
      cases idx' with
      | zero => simp only [evalGen] at heval; cases heval
      | succ idx'' =>
        cases idx'' <;> try (simp only [evalGen] at heval; cases heval)
        simp only [Nat.zero_add, Nat.reduceAdd, evalGen] at heval
        cases hs : canSplit a2 b2 with
        | false => rw [hs] at heval; cases heval
        | true =>
          rw [hs] at heval; dsimp only at heval
          have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5⟩
          cases e0 : evalGen leaf t0 (.c121 a0 b0 a1 b1 ((a2 + b2) / 2) b2) <;>
          cases e1 : evalGen leaf t1 (.c121 a0 b0 a1 b1 a2 ((a2 + b2) / 2)) <;>
            simp only [e0, e1] at heval
          any_goals cases heval
          refine hsp2 e0 e1 ⟨h0, h1, h2, h3, by omega, hm2⟩ ⟨h0, h1, h2, h3, h4, hm1⟩ ?_ rfl
          intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
          rcases le_total (gval ((a2 + b2) / 2)) x.2.2.2 with h | h
          · left; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, h, hx.2.2.2.2.2.2⟩
          · right; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, h⟩
    case c112.zero a0 b0 a1 b1 a2 b2 =>
      simp only [evalGen] at heval
      cases hs : canSplit a0 b0 with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5⟩
        cases e0 : evalGen leaf t0 (.c112 ((a0 + b0) / 2) b0 a1 b1 a2 b2) <;>
        cases e1 : evalGen leaf t1 (.c112 a0 ((a0 + b0) / 2) a1 b1 a2 b2) <;>
          simp only [e0, e1] at heval
        any_goals cases heval
        refine hsp2 e0 e1 ⟨by omega, hm2, h2, h3, h4, h5⟩ ⟨h0, hm1, by omega, h3, h4, h5⟩ ?_ rfl
        intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
        rcases le_total (gval ((a0 + b0) / 2)) x.1 with h | h
        · left; exact ⟨h, hx.2.1, hx.2.2⟩
        · right; exact ⟨hx.1, h, hx.2.2⟩
    case c112.succ a0 b0 a1 b1 a2 b2 idx' =>
      cases idx' <;> try (simp only [evalGen] at heval; cases heval)
      simp only [Nat.zero_add, evalGen] at heval
      cases hs : canSplit a1 b1 with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5⟩
        cases e0 : evalGen leaf t0 (.c112 a0 b0 ((a1 + b1) / 2) b1 a2 b2) <;>
        cases e1 : evalGen leaf t1 (.c112 a0 b0 a1 ((a1 + b1) / 2) a2 b2) <;>
          simp only [e0, e1] at heval
        any_goals cases heval
        refine hsp2 e0 e1 ⟨h0, h1, by omega, hm2, h4, h5⟩ ⟨h0, h1, h2, hm1, by omega, h5⟩ ?_ rfl
        intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
        rcases le_total (gval ((a1 + b1) / 2)) x.2.1 with h | h
        · left; exact ⟨hx.1, hx.2.1, h, hx.2.2.2.1, hx.2.2.2.2⟩
        · right; exact ⟨hx.1, hx.2.1, hx.2.2.1, h, hx.2.2.2.2⟩
    case c1111.zero a0 b0 a1 b1 a2 b2 a3 b3 =>
      simp only [evalGen] at heval
      cases hs : canSplit a0 b0 with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
        cases e0 : evalGen leaf t0 (.c1111 ((a0 + b0) / 2) b0 a1 b1 a2 b2 a3 b3) <;>
        cases e1 : evalGen leaf t1 (.c1111 a0 ((a0 + b0) / 2) a1 b1 a2 b2 a3 b3) <;>
          simp only [e0, e1] at heval
        any_goals cases heval
        refine hsp2 e0 e1 ⟨by omega, hm2, h2, h3, h4, h5, h6, h7⟩ ⟨h0, hm1, by omega, h3, h4, h5, h6, h7⟩ ?_ rfl
        intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
        rcases le_total (gval ((a0 + b0) / 2)) x.1 with h | h
        · left; exact ⟨h, hx.2.1, hx.2.2⟩
        · right; exact ⟨hx.1, h, hx.2.2⟩
    case c1111.succ a0 b0 a1 b1 a2 b2 a3 b3 idx' =>
      cases idx' with
      | zero =>
        simp only [Nat.zero_add, evalGen] at heval
        cases hs : canSplit a1 b1 with
        | false => rw [hs] at heval; cases heval
        | true =>
          rw [hs] at heval; dsimp only at heval
          have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
          cases e0 : evalGen leaf t0 (.c1111 a0 b0 ((a1 + b1) / 2) b1 a2 b2 a3 b3) <;>
          cases e1 : evalGen leaf t1 (.c1111 a0 b0 a1 ((a1 + b1) / 2) a2 b2 a3 b3) <;>
            simp only [e0, e1] at heval
          any_goals cases heval
          refine hsp2 e0 e1 ⟨h0, h1, by omega, hm2, h4, h5, h6, h7⟩ ⟨h0, h1, h2, hm1, by omega, h5, h6, h7⟩ ?_ rfl
          intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
          rcases le_total (gval ((a1 + b1) / 2)) x.2.1 with h | h
          · left; exact ⟨hx.1, hx.2.1, h, hx.2.2.2.1, hx.2.2.2.2⟩
          · right; exact ⟨hx.1, hx.2.1, hx.2.2.1, h, hx.2.2.2.2⟩
      | succ idx'' =>
        cases idx'' with
        | zero =>
          simp only [Nat.zero_add, Nat.reduceAdd, evalGen] at heval
          cases hs : canSplit a2 b2 with
          | false => rw [hs] at heval; cases heval
          | true =>
            rw [hs] at heval; dsimp only at heval
            have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
            cases e0 : evalGen leaf t0 (.c1111 a0 b0 a1 b1 ((a2 + b2) / 2) b2 a3 b3) <;>
            cases e1 : evalGen leaf t1 (.c1111 a0 b0 a1 b1 a2 ((a2 + b2) / 2) a3 b3) <;>
              simp only [e0, e1] at heval
            any_goals cases heval
            refine hsp2 e0 e1 ⟨h0, h1, h2, h3, by omega, hm2, h6, h7⟩ ⟨h0, h1, h2, h3, h4, hm1, by omega, h7⟩ ?_ rfl
            intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
            rcases le_total (gval ((a2 + b2) / 2)) x.2.2.1 with h | h
            · left; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, h, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2⟩
            · right; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, h, hx.2.2.2.2.2.2⟩
        | succ idx3 =>
          cases idx3 <;> try (simp only [evalGen] at heval; cases heval)
          simp only [Nat.zero_add, Nat.reduceAdd, evalGen] at heval
          cases hs : canSplit a3 b3 with
          | false => rw [hs] at heval; cases heval
          | true =>
            rw [hs] at heval; dsimp only at heval
            have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
            cases e0 : evalGen leaf t0 (.c1111 a0 b0 a1 b1 a2 b2 ((a3 + b3) / 2) b3) <;>
            cases e1 : evalGen leaf t1 (.c1111 a0 b0 a1 b1 a2 b2 a3 ((a3 + b3) / 2)) <;>
              simp only [e0, e1] at heval
            any_goals cases heval
            refine hsp2 e0 e1 ⟨h0, h1, h2, h3, h4, h5, by omega, hm2⟩ ⟨h0, h1, h2, h3, h4, h5, h6, hm1⟩ ?_ rfl
            intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
            rcases le_total (gval ((a3 + b3) / 2)) x.2.2.2 with h | h
            · left; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, h, hx.2.2.2.2.2.2.2⟩
            · right; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1, h⟩
  | S3 idx t0 t1 t2 ih0 ih1 ih2 =>
    have hsp3 : ∀ {c0 c1 c2 : Cell4} {v0 v1 v2 : Nat},
        evalGen leaf t0 c0 = some v0 → evalGen leaf t1 c1 = some v1 → evalGen leaf t2 c2 = some v2 →
        c0.valid → c1.valid → c2.valid → c.set ⊆ c0.set ∪ (c1.set ∪ c2.set) →
        v = v0 + v1 + v2 → ∫ x in c.set, g x ≤ (v : ℝ) / S_scale := by
      intro c0 c1 c2 v0 v1 v2 he0 he1 he2 hv0 hv1 hv2 hsub hv_eq
      have hle := setIntegral_le_of_subset_union3 hsub c0.measurableSet_set c1.measurableSet_set c2.measurableSet_set
        (hg_nn hv0) (hg_nn hv1) (hg_nn hv2)
        (hg_int hv0) (hg_int hv1) (hg_int hv2)
      have b0 := ih0 c0 hv0 he0; have b1 := ih1 c1 hv1 he1; have b2 := ih2 c2 hv2 he2
      rw [hv_eq, Nat.cast_add, Nat.cast_add, add_div, add_div]; linarith
    cases c <;> cases idx <;> try (simp only [evalGen] at heval; cases heval)
    case c22.zero a0 b0 a1 b1 =>
      simp only [evalGen] at heval
      cases hs : canSplit a0 b0 with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3⟩
        cases e0 : evalGen leaf t0 (.c22 ((a0 + b0) / 2) b0 a1 b1) <;>
        cases e1 : evalGen leaf t1 (.c112 a0 ((a0 + b0) / 2) ((a0 + b0) / 2) b0 a1 b1) <;>
        cases e2 : evalGen leaf t2 (.c22 a0 ((a0 + b0) / 2) a1 b1) <;>
          simp only [e0, e1, e2] at heval
        any_goals cases heval
        refine hsp3 e0 e1 e2 ⟨by omega, hm2, h2, h3⟩ ⟨h0, hm1, le_refl _, hm2, h2, h3⟩ ⟨h0, hm1, by omega, h3⟩ ?_ rfl
        intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
        rcases le_total (gval ((a0 + b0) / 2)) x.1 with h | h
        · left; exact ⟨h, hx.2.1, hx.2.2⟩
        · rcases le_total (gval ((a0 + b0) / 2)) x.2.1 with h' | h'
          · right; left; exact ⟨hx.1, h, h', hx.2.2.1, hx.2.2.2⟩
          · right; right; exact ⟨hx.1, hx.2.1, h', hx.2.2.2⟩
    case c22.succ a0 b0 a1 b1 idx' =>
      cases idx' <;> try (simp only [evalGen] at heval; cases heval)
      simp only [Nat.zero_add, evalGen] at heval
      cases hs : canSplit a1 b1 with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3⟩
        cases e0 : evalGen leaf t0 (.c22 a0 b0 ((a1 + b1) / 2) b1) <;>
        cases e1 : evalGen leaf t1 (.c211 a0 b0 a1 ((a1 + b1) / 2) ((a1 + b1) / 2) b1) <;>
        cases e2 : evalGen leaf t2 (.c22 a0 b0 a1 ((a1 + b1) / 2)) <;>
          simp only [e0, e1, e2] at heval
        any_goals cases heval
        refine hsp3 e0 e1 e2 ⟨h0, h1, by omega, hm2⟩ ⟨h0, h1, h2, hm1, le_refl _, hm2⟩ ⟨h0, h1, h2, hm1⟩ ?_ rfl
        intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
        rcases le_total (gval ((a1 + b1) / 2)) x.2.2.1 with h | h
        · left; exact ⟨hx.1, hx.2.1, hx.2.2.1, h, hx.2.2.2.2⟩
        · rcases le_total (gval ((a1 + b1) / 2)) x.2.2.2 with h' | h'
          · right; left; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, h, h', hx.2.2.2.2.2⟩
          · right; right; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, h'⟩
    case c211.zero a0 b0 a1 b1 a2 b2 =>
      simp only [evalGen] at heval
      cases hs : canSplit a0 b0 with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5⟩
        cases e0 : evalGen leaf t0 (.c211 ((a0 + b0) / 2) b0 a1 b1 a2 b2) <;>
        cases e1 : evalGen leaf t1 (.c1111 a0 ((a0 + b0) / 2) ((a0 + b0) / 2) b0 a1 b1 a2 b2) <;>
        cases e2 : evalGen leaf t2 (.c211 a0 ((a0 + b0) / 2) a1 b1 a2 b2) <;>
          simp only [e0, e1, e2] at heval
        any_goals cases heval
        refine hsp3 e0 e1 e2 ⟨by omega, hm2, h2, h3, h4, h5⟩ ⟨h0, hm1, le_refl _, hm2, h2, h3, h4, h5⟩ ⟨h0, hm1, by omega, h3, h4, h5⟩ ?_ rfl
        intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
        rcases le_total (gval ((a0 + b0) / 2)) x.1 with h | h
        · left; exact ⟨h, hx.2.1, hx.2.2⟩
        · rcases le_total (gval ((a0 + b0) / 2)) x.2.1 with h' | h'
          · right; left; exact ⟨hx.1, h, h', hx.2.2.1, hx.2.2.2⟩
          · right; right; exact ⟨hx.1, hx.2.1, h', hx.2.2.2⟩
    case c121.succ a0 b0 a1 b1 a2 b2 idx' =>
      cases idx' <;> try (simp only [evalGen] at heval; cases heval)
      simp only [Nat.zero_add, evalGen] at heval
      cases hs : canSplit a1 b1 with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5⟩
        cases e0 : evalGen leaf t0 (.c121 a0 b0 ((a1 + b1) / 2) b1 a2 b2) <;>
        cases e1 : evalGen leaf t1 (.c1111 a0 b0 a1 ((a1 + b1) / 2) ((a1 + b1) / 2) b1 a2 b2) <;>
        cases e2 : evalGen leaf t2 (.c121 a0 b0 a1 ((a1 + b1) / 2) a2 b2) <;>
          simp only [e0, e1, e2] at heval
        any_goals cases heval
        refine hsp3 e0 e1 e2 ⟨h0, h1, by omega, hm2, h4, h5⟩ ⟨h0, h1, h2, hm1, le_refl _, hm2, h4, h5⟩ ⟨h0, h1, h2, hm1, by omega, h5⟩ ?_ rfl
        intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
        rcases le_total (gval ((a1 + b1) / 2)) x.2.1 with h | h
        · left; exact ⟨hx.1, hx.2.1, h, hx.2.2.2⟩
        · rcases le_total (gval ((a1 + b1) / 2)) x.2.2.1 with h' | h'
          · right; left; exact ⟨hx.1, hx.2.1, hx.2.2.1, h, h', hx.2.2.2.2.1, hx.2.2.2.2.2⟩
          · right; right; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, h', hx.2.2.2.2.2⟩
    case c112.succ a0 b0 a1 b1 a2 b2 idx' =>
      cases idx' with
      | zero => simp only [evalGen] at heval; cases heval
      | succ idx'' =>
        cases idx'' <;> try (simp only [evalGen] at heval; cases heval)
        simp only [Nat.zero_add, Nat.reduceAdd, evalGen] at heval
        cases hs : canSplit a2 b2 with
        | false => rw [hs] at heval; cases heval
        | true =>
          rw [hs] at heval; dsimp only at heval
          have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3, h4, h5⟩
          cases e0 : evalGen leaf t0 (.c112 a0 b0 a1 b1 ((a2 + b2) / 2) b2) <;>
          cases e1 : evalGen leaf t1 (.c1111 a0 b0 a1 b1 a2 ((a2 + b2) / 2) ((a2 + b2) / 2) b2) <;>
          cases e2 : evalGen leaf t2 (.c112 a0 b0 a1 b1 a2 ((a2 + b2) / 2)) <;>
            simp only [e0, e1, e2] at heval
          any_goals cases heval
          refine hsp3 e0 e1 e2 ⟨h0, h1, h2, h3, by omega, hm2⟩ ⟨h0, h1, h2, h3, h4, hm1, le_refl _, hm2⟩ ⟨h0, h1, h2, h3, h4, hm1⟩ ?_ rfl
          intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
          rcases le_total (gval ((a2 + b2) / 2)) x.2.2.1 with h | h
          · left; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, h, hx.2.2.2.2.2⟩
          · rcases le_total (gval ((a2 + b2) / 2)) x.2.2.2 with h' | h'
            · right; left; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, h, h', hx.2.2.2.2.2.2⟩
            · right; right; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, h'⟩
  | S4 idx t0 t1 t2 t3 ih0 ih1 ih2 ih3 =>
    have hsp4 : ∀ {c0 c1 c2 c3 : Cell4} {v0 v1 v2 v3 : Nat},
        evalGen leaf t0 c0 = some v0 → evalGen leaf t1 c1 = some v1 →
        evalGen leaf t2 c2 = some v2 → evalGen leaf t3 c3 = some v3 →
        c0.valid → c1.valid → c2.valid → c3.valid → c.set ⊆ c0.set ∪ (c1.set ∪ (c2.set ∪ c3.set)) →
        v = v0 + v1 + v2 + v3 → ∫ x in c.set, g x ≤ (v : ℝ) / S_scale := by
      intro c0 c1 c2 c3 v0 v1 v2 v3 he0 he1 he2 he3 hv0 hv1 hv2 hv3 hsub hv_eq
      have hle := setIntegral_le_of_subset_union4 hsub
        c0.measurableSet_set c1.measurableSet_set c2.measurableSet_set c3.measurableSet_set
        (hg_nn hv0) (hg_nn hv1)
        (hg_nn hv2) (hg_nn hv3)
        (hg_int hv0) (hg_int hv1)
        (hg_int hv2) (hg_int hv3)
      have b0 := ih0 c0 hv0 he0; have b1 := ih1 c1 hv1 he1; have b2 := ih2 c2 hv2 he2; have b3 := ih3 c3 hv3 he3
      rw [hv_eq, Nat.cast_add, Nat.cast_add, Nat.cast_add, add_div, add_div, add_div]; linarith
    cases c <;> cases idx <;> try (simp only [evalGen] at heval; cases heval)
    case c31.zero a0 b0 a1 b1 =>
      simp only [evalGen] at heval
      cases hs : canSplit a0 b0 with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3⟩
        cases e0 : evalGen leaf t0 (.c31 ((a0 + b0) / 2) b0 a1 b1) <;>
        cases e1 : evalGen leaf t1 (.c121 a0 ((a0 + b0) / 2) ((a0 + b0) / 2) b0 a1 b1) <;>
        cases e2 : evalGen leaf t2 (.c211 a0 ((a0 + b0) / 2) ((a0 + b0) / 2) b0 a1 b1) <;>
        cases e3 : evalGen leaf t3 (.c31 a0 ((a0 + b0) / 2) a1 b1) <;>
          simp only [e0, e1, e2, e3] at heval
        any_goals cases heval
        refine hsp4 e0 e1 e2 e3 ⟨by omega, hm2, h2, h3⟩ ⟨h0, hm1, le_refl _, hm2, h2, h3⟩
          ⟨h0, hm1, le_refl _, hm2, h2, h3⟩ ⟨h0, hm1, by omega, h3⟩ ?_ rfl
        intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
        rcases le_total (gval ((a0 + b0) / 2)) x.1 with h | h
        · left; exact ⟨h, hx.2.1, hx.2.2⟩
        · rcases le_total (gval ((a0 + b0) / 2)) x.2.1 with h' | h'
          · right; left; exact ⟨hx.1, h, h', hx.2.2.1, hx.2.2.2⟩
          · rcases le_total (gval ((a0 + b0) / 2)) x.2.2.1 with h'' | h''
            · right; right; left; exact ⟨hx.1, hx.2.1, h', h'', hx.2.2.2.1, hx.2.2.2.2⟩
            · right; right; right; exact ⟨hx.1, hx.2.1, hx.2.2.1, h'', hx.2.2.2.2⟩
    case c13.succ a0 b0 a1 b1 idx' =>
      cases idx' <;> try (simp only [evalGen] at heval; cases heval)
      simp only [Nat.zero_add, evalGen] at heval
      cases hs : canSplit a1 b1 with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1, h2, h3⟩
        cases e0 : evalGen leaf t0 (.c13 a0 b0 ((a1 + b1) / 2) b1) <;>
        cases e1 : evalGen leaf t1 (.c112 a0 b0 a1 ((a1 + b1) / 2) ((a1 + b1) / 2) b1) <;>
        cases e2 : evalGen leaf t2 (.c121 a0 b0 a1 ((a1 + b1) / 2) ((a1 + b1) / 2) b1) <;>
        cases e3 : evalGen leaf t3 (.c13 a0 b0 a1 ((a1 + b1) / 2)) <;>
          simp only [e0, e1, e2, e3] at heval
        any_goals cases heval
        refine hsp4 e0 e1 e2 e3 ⟨h0, h1, by omega, hm2⟩ ⟨h0, h1, h2, hm1, le_refl _, hm2⟩
          ⟨h0, h1, h2, hm1, le_refl _, hm2⟩ ⟨h0, h1, h2, hm1⟩ ?_ rfl
        intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
        rcases le_total (gval ((a1 + b1) / 2)) x.2.1 with h | h
        · left; exact ⟨hx.1, hx.2.1, h, hx.2.2.2⟩
        · rcases le_total (gval ((a1 + b1) / 2)) x.2.2.1 with h' | h'
          · right; left; exact ⟨hx.1, hx.2.1, hx.2.2.1, h, h', hx.2.2.2.2⟩
          · rcases le_total (gval ((a1 + b1) / 2)) x.2.2.2 with h'' | h''
            · right; right; left; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, h', h'', hx.2.2.2.2.2⟩
            · right; right; right; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, h''⟩
  | S5 idx t0 t1 t2 t3 t4 ih0 ih1 ih2 ih3 ih4 =>
    cases c <;> cases idx <;> try (simp only [evalGen] at heval; cases heval)
    case c4.zero a b =>
      simp only [evalGen] at heval
      cases hs : canSplit a b with
      | false => rw [hs] at heval; cases heval
      | true =>
        rw [hs] at heval; dsimp only at heval
        have ⟨hm1, hm2⟩ := canSplit_mid hs; rcases hv with ⟨h0, h1⟩
        cases e0 : evalGen leaf t0 (.c4 ((a + b) / 2) b) <;>
        cases e1 : evalGen leaf t1 (.c13 a ((a + b) / 2) ((a + b) / 2) b) <;>
        cases e2 : evalGen leaf t2 (.c22 a ((a + b) / 2) ((a + b) / 2) b) <;>
        cases e3 : evalGen leaf t3 (.c31 a ((a + b) / 2) ((a + b) / 2) b) <;>
        cases e4 : evalGen leaf t4 (.c4 a ((a + b) / 2)) <;>
          simp only [e0, e1, e2, e3, e4] at heval
        any_goals cases heval
        have hv0 : (Cell4.c4 ((a + b) / 2) b).valid := ⟨by omega, hm2⟩
        have hv1 : (Cell4.c13 a ((a + b) / 2) ((a + b) / 2) b).valid := ⟨h0, hm1, le_refl _, hm2⟩
        have hv2 : (Cell4.c22 a ((a + b) / 2) ((a + b) / 2) b).valid := ⟨h0, hm1, le_refl _, hm2⟩
        have hv3 : (Cell4.c31 a ((a + b) / 2) ((a + b) / 2) b).valid := ⟨h0, hm1, le_refl _, hm2⟩
        have hv4 : (Cell4.c4 a ((a + b) / 2)).valid := ⟨h0, hm1⟩
        have hsub : (Cell4.c4 a b).set ⊆ (Cell4.c4 ((a + b) / 2) b).set ∪
            ((Cell4.c13 a ((a + b) / 2) ((a + b) / 2) b).set ∪
             ((Cell4.c22 a ((a + b) / 2) ((a + b) / 2) b).set ∪
              ((Cell4.c31 a ((a + b) / 2) ((a + b) / 2) b).set ∪
               (Cell4.c4 a ((a + b) / 2)).set))) := by
          intro x hx; simp only [Cell4.set, mem_ofPred_eq, mem_union] at hx ⊢
          rcases le_total (gval ((a + b) / 2)) x.1 with h | h
          · left; exact ⟨h, hx.2⟩
          · rcases le_total (gval ((a + b) / 2)) x.2.1 with h' | h'
            · right; left; exact ⟨hx.1, h, h', hx.2.2⟩
            · rcases le_total (gval ((a + b) / 2)) x.2.2.1 with h'' | h''
              · right; right; left; exact ⟨hx.1, hx.2.1, h', h'', hx.2.2.2⟩
              · rcases le_total (gval ((a + b) / 2)) x.2.2.2 with h3p | h3p
                · right; right; right; left; exact ⟨hx.1, hx.2.1, hx.2.2.1, h'', h3p, hx.2.2.2.2⟩
                · right; right; right; right; exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, h3p⟩
        have hle := setIntegral_le_of_subset_union5 hsub
          (Cell4.c4 _ _).measurableSet_set (Cell4.c13 _ _ _ _).measurableSet_set
          (Cell4.c22 _ _ _ _).measurableSet_set (Cell4.c31 _ _ _ _).measurableSet_set
          (Cell4.c4 _ _).measurableSet_set
          (hg_nn hv0) (hg_nn hv1)
          (hg_nn hv2) (hg_nn hv3) (hg_nn hv4)
          (hg_int hv0) (hg_int hv1)
          (hg_int hv2) (hg_int hv3) (hg_int hv4)
        have b0 := ih0 _ hv0 e0; have b1 := ih1 _ hv1 e1; have b2 := ih2 _ hv2 e2
        have b3 := ih3 _ hv3 e3; have b4 := ih4 _ hv4 e4
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_add,
            add_div, add_div, add_div, add_div]
        linarith


private lemma evalTree_sound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {pa pb : Nat} {φ : ℝ} (hpa : gval pa ≤ φ) (hpb : φ ≤ gval pb)
    (t : CTree) (c : Cell4) (hv : c.valid) {v : Nat}
    (heval : evalTree pa pb t c = some v) :
    ∫ x in c.set, integrand4 ω φ x ≤ (v : ℝ) / S_scale := by
  refine evalGen_sound (leaf := evalMainLeaf pa pb)
    (fun hv => integrand4_nonneg hω hz φ hv)
    (fun hv => integrand4_integrableOn hω hz φ hv)
    ?_ ?_ ?_ (fun hv he => evalBndCell_sound hω hz hpa hpb hv he) t c hv heval
  · intro c v hv heval
    simp only [evalMainLeaf] at heval
    set lh := cellLoHi c
    rcases lh_eq : lh with ⟨l0, l1, l2, l3, u0, u1, u2, u3⟩
    have hbd := c.valid_bounds hv
    rw [lh_eq] at heval
    rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hbd
    dsimp only at hbd heval
    rcases hbd with ⟨hl0, hlu0, hl01, hlu1, hl12, hlu2, hl23, hlu3⟩
    cases hble : Nat.ble pb (l0 + l1 + l2 + l2 + l3) with
    | false => rw [hble] at heval; cases heval
    | true =>
      rw [hble] at heval; simp only [Option.some.injEq] at heval; subst heval
      have hle : pb ≤ l0 + l1 + l2 + l2 + l3 := Nat.ble_eq.mp hble
      have hae : ∀ᵐ x ∂(volume.restrict c.set), integrand4 ω φ x = 0 := by
        have hsing : volume ({(gval l0, gval l1, gval l2, gval l3)} : Set R4) = 0 := volume_singleton_R4 _
        have hne : ∀ᵐ x ∂(volume.restrict c.set), x ≠ (gval l0, gval l1, gval l2, gval l3) := by
          rw [ae_restrict_iff' c.measurableSet_set]
          have : volume {x : R4 | ¬ (x ∈ c.set → x ≠ (gval l0, gval l1, gval l2, gval l3))} = 0 := by
            apply measure_mono_null _ hsing
            intro x hx; by_contra hne; exact hx (fun _ => hne)
          exact mem_ae_iff.mpr this
        filter_upwards [ae_restrict_mem c.measurableSet_set, hne] with x hx hxne
        have hxb := c.set_subset_box hx
        unfold Cell4.box at hxb
        rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hxb
        rcases hxb with ⟨⟨hx0, _⟩, ⟨hx1, _⟩, ⟨hx2, _⟩, ⟨hx3, _⟩⟩
        have hlt : gval l0 + gval l1 + 2 * gval l2 + gval l3 < x.1 + x.2.1 + 2 * x.2.2.1 + x.2.2.2 := by
          by_contra hnot; push Not at hnot
          apply hxne; ext <;> dsimp <;> linarith
        have hpbr : gval pb ≤ gval l0 + gval l1 + 2 * gval l2 + gval l3 := by
          have := gval_le hle; simp only [gval_add] at this; linarith only [this]
        have hx2_pos : 0 < x.2.2.1 := lt_of_lt_of_le (gval_pos (by omega)) hx2
        have hu : (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1 < 1 := by
          rw [div_lt_one hx2_pos]; linarith
        unfold integrand4; rw [hz _ hu, zero_div]
      rw [integral_eq_zero_of_ae hae]; simp
  · intro c v hv heval
    simp only [evalMainLeaf] at heval
    set lh := cellLoHi c
    rcases lh_eq : lh with ⟨l0, l1, l2, l3, u0, u1, u2, u3⟩
    have hbd := c.valid_bounds hv
    rw [lh_eq] at heval
    rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hbd
    dsimp only at hbd heval
    rcases hbd with ⟨hl0, hlu0, hl01, hlu1, hl12, hlu2, hl23, hlu3⟩
    cases h1 : Nat.ble 1 l0 <;> cases h2 : Nat.ble (u0 + u1 + u2 + u2 + u3) pa <;>
      cases h3 : Nat.ble pb (l0 + l1 + 3 * l2 + l3) <;>
      simp only [h1, h2, h3] at heval
    any_goals cases heval
    have hpa_ge : u0 + u1 + u2 + u2 + u3 ≤ pa := Nat.ble_eq.mp h2
    have hpb_le : pb ≤ l0 + l1 + 3 * l2 + l3 := Nat.ble_eq.mp h3
    let f_pa : R4 → ℝ := fun x => 1 / (x.1 * x.2.1 * x.2.2.1 * x.2.2.2 *
      (gval pa - x.1 - x.2.1 - x.2.2.1 - x.2.2.2))
    have hbox_sub : c.box ⊆ {x : R4 | 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2 ∧
        0 < gval pa - x.1 - x.2.1 - x.2.2.1 - x.2.2.2} := by
      intro x hx
      unfold Cell4.box at hx
      rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hx
      rcases hx with ⟨⟨hx0a, hx0b⟩, ⟨hx1a, hx1b⟩, ⟨hx2a, hx2b⟩, ⟨hx3a, hx3b⟩⟩
      have hpar : gval u0 + gval u1 + 2 * gval u2 + gval u3 ≤ gval pa := by
        have := gval_le hpa_ge; simp only [gval_add] at this; linarith only [this]
      have hu2p : 0 < gval u2 := gval_pos (by omega)
      exact ⟨lt_of_lt_of_le (gval_pos (by omega)) hx0a, lt_of_lt_of_le (gval_pos (by omega)) hx1a,
        lt_of_lt_of_le (gval_pos (by omega)) hx2a, lt_of_lt_of_le (gval_pos (by omega)) hx3a, by linarith⟩
    have hf_cont : ContinuousOn f_pa c.box := by
      unfold f_pa
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; rcases hbox_sub hx with ⟨p0, p1, p2, p3, p4⟩; positivity
    have hf_conv : ConvexOn ℝ c.box f_pa :=
      (log_inv_prod5_convex (gval pa)).subset hbox_sub c.convex_box
    have hpt : ∀ x ∈ c.set, integrand4 ω φ x ≤ f_pa x := by
      intro x hx
      have hxb := c.set_subset_box hx
      rcases hbox_sub hxb with ⟨p0, p1, p2, p3, p4⟩
      unfold Cell4.box at hxb
      rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hxb
      rcases hxb with ⟨⟨hx0a, hx0b⟩, ⟨hx1a, hx1b⟩, ⟨hx2a, hx2b⟩, ⟨hx3a, hx3b⟩⟩
      have hpar : gval u0 + gval u1 + 2 * gval u2 + gval u3 ≤ gval pa := by
        have := gval_le hpa_ge; simp only [gval_add] at this; linarith only [this]
      have hpbr : gval pb ≤ gval l0 + gval l1 + 3 * gval l2 + gval l3 := by
        have := gval_le hpb_le; simp only [gval_add, gval_3mul] at this; linarith only [this]
      have hu1 : 1 ≤ (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1 := by
        rw [one_le_div p2]; linarith
      have hu2 : (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1 ≤ 2 := by
        rw [div_le_iff₀ p2]; linarith
      have hrew : integrand4 ω φ x = 1 / (x.1 * x.2.1 * x.2.2.1 * x.2.2.2 *
          (φ - x.1 - x.2.1 - x.2.2.1 - x.2.2.2)) := by
        unfold integrand4; rw [hω.2.1 _ hu1 hu2]
        rw [show φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2) = φ - x.1 - x.2.1 - x.2.2.1 - x.2.2.2 by ring]
        exact inv_u_div_weight (ne_of_gt p2)
      rw [hrew]
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hmono := setIntegral_mono_on (integrand4_integrableOn hω hz φ hv)
      ((hf_cont.mono c.set_subset_box).integrableOn_compact c.isCompact_set) c.measurableSet_set hpt
    have hhh := hh_cell4 c hv hf_cont hf_conv
    have hnum := evalIntCell_bound (pa := pa) hv (by rw [show cellLoHi c = _ from lh_eq]; exact hpa_ge)
    exact le_trans hmono (le_trans hhh hnum)
  · intro c v hv heval
    simp only [evalMainLeaf] at heval
    set lh := cellLoHi c
    rcases lh_eq : lh with ⟨l0, l1, l2, l3, u0, u1, u2, u3⟩
    have hbd := c.valid_bounds hv
    rw [lh_eq] at heval
    rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hbd
    dsimp only at hbd heval
    rcases hbd with ⟨hl0, hlu0, hl01, hlu1, hl12, hlu2, hl23, hlu3⟩
    cases h1 : Nat.ble 1 l0 <;> cases h2 : Nat.ble (u0 + u1 + 3 * u2 + u3) pa <;>
      simp only [h1, h2] at heval
    any_goals cases heval
    have hpa_ge : u0 + u1 + 3 * u2 + u3 ≤ pa := Nat.ble_eq.mp h2
    have hbox_sub : c.box ⊆ {x : R4 | 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2} := by
      intro x hx
      unfold Cell4.box at hx
      rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hx
      exact ⟨lt_of_lt_of_le (gval_pos (by omega)) hx.1.1, lt_of_lt_of_le (gval_pos (by omega)) hx.2.1.1,
        lt_of_lt_of_le (gval_pos (by omega)) hx.2.2.1.1, lt_of_lt_of_le (gval_pos (by omega)) hx.2.2.2.1⟩
    have hw_cont : ContinuousOn weight4 c.box := by
      unfold weight4
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; rcases hbox_sub hx with ⟨p0, p1, p2, p3⟩; positivity
    have hw_conv : ConvexOn ℝ c.box weight4 := weight4_convex.subset hbox_sub c.convex_box
    have hpt : ∀ x ∈ c.set, integrand4 ω φ x ≤ ((7 : ℝ) / 12) * weight4 x := by
      intro x hx
      have hxb := c.set_subset_box hx
      rcases hbox_sub hxb with ⟨p0, p1, p2, p3⟩
      unfold Cell4.box at hxb
      rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hxb
      rcases hxb with ⟨⟨_, hx0b⟩, ⟨_, hx1b⟩, ⟨_, hx2b⟩, ⟨_, hx3b⟩⟩
      have hpar : gval u0 + gval u1 + 3 * gval u2 + gval u3 ≤ gval pa := by
        have := gval_le hpa_ge; simp only [gval_add, gval_3mul] at this; linarith only [this]
      have hu2 : 2 ≤ (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1 := by
        rw [le_div_iff₀ p2]; linarith
      have hrew : integrand4 ω φ x = ω ((φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1) * weight4 x := by
        unfold integrand4 weight4; ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_right (buchstab_le_seven_twelfths hω hu2) (weight4_nonneg hv x hx)
    have hmono := setIntegral_mono_on (integrand4_integrableOn hω hz φ hv)
      ((weight4_integrableOn hv).const_mul ((7 : ℝ) / 12)) c.measurableSet_set hpt
    rw [integral_const_mul] at hmono
    have hhh := hh_cell4 c hv hw_cont hw_conv
    have hnum := evalWCell_bound (nm := 7) (dm := 12) (by omega) hv
    have hmul := mul_le_mul_of_nonneg_left hhh (by norm_num : (0 : ℝ) ≤ 7 / 12)
    have hcast712 : ((7 : Nat) : ℝ) / (12 : Nat) = (7 : ℝ) / 12 := by norm_num
    rw [hcast712] at hnum
    exact le_trans hmono (le_trans hmul hnum)

private lemma evalWTree_sound (t : CTree) (c : Cell4) (hv : c.valid) {v : Nat}
    (heval : evalWTree t c = some v) :
    ∫ x in c.set, weight4 x ≤ (v : ℝ) / S_scale := by
  refine evalGen_sound (leaf := evalWLeaf)
    (fun hv => weight4_nonneg hv)
    (fun hv => weight4_integrableOn hv)
    (fun _ he => by cases he)
    (fun _ he => by cases he)
    ?_
    (fun _ he => by cases he) t c hv heval
  intro c v hv heval
  simp only [evalWLeaf] at heval
  set lh := cellLoHi c
  rcases lh_eq : lh with ⟨l0, l1, l2, l3, u0, u1, u2, u3⟩
  have hbd := c.valid_bounds hv
  rw [lh_eq] at heval
  rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hbd
  dsimp only at hbd heval
  rcases hbd with ⟨hl0, hlu0, hl01, hlu1, hl12, hlu2, hl23, hlu3⟩
  cases h1 : Nat.ble 1 l0 with
  | false => rw [h1] at heval; cases heval
  | true =>
    rw [h1] at heval; simp only [Option.some.injEq] at heval; subst heval
    have hbox_sub : c.box ⊆ {x : R4 | 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2} := by
      intro x hx; unfold Cell4.box at hx
      rw [show cellLoHi c = (l0, l1, l2, l3, u0, u1, u2, u3) from lh_eq] at hx
      exact ⟨lt_of_lt_of_le (gval_pos (by omega)) hx.1.1, lt_of_lt_of_le (gval_pos (by omega)) hx.2.1.1,
        lt_of_lt_of_le (gval_pos (by omega)) hx.2.2.1.1, lt_of_lt_of_le (gval_pos (by omega)) hx.2.2.2.1⟩
    have hw_cont : ContinuousOn weight4 c.box := by
      unfold weight4
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; rcases hbox_sub hx with ⟨p0, p1, p2, p3⟩; positivity
    have hw_conv : ConvexOn ℝ c.box weight4 := weight4_convex.subset hbox_sub c.convex_box
    have hhh := hh_cell4 c hv hw_cont hw_conv
    have hnum := evalWCell_bound (nm := 1) (dm := 1) one_pos hv
    simpa using le_trans hhh (by simpa using hnum)


/-! ### Part 5: Domain Equivalence, Interval & Tail Assembly -/

private lemma initCell_valid : initCell.valid := by
  unfold initCell Cell4.valid A_num B_num; omega

private lemma buchstabIntegral_eq_setIntegral (ω : ℝ → ℝ) (φ : ℝ) :
    buchstabIntegral ω 2 (fun j => (r0j16_lo j : ℝ)) (fun j => (r0j16_hi j : ℝ)) φ =
      ∫ x in initCell.set, integrand4 ω φ x := by
  let e3 : (Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.finTwoArrow))
  let e4 : (Fin 4 → ℝ) ≃ᵐ R4 :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) e3)
  have hmp3 : MeasurePreserving e3 volume volume := by
    have h1 := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
    have h2 : MeasurePreserving
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.finTwoArrow (α := ℝ)))
        (volume.prod volume) (volume.prod (volume.prod volume)) :=
      (MeasurePreserving.id volume).prod (MeasureTheory.volume_preserving_finTwoArrow ℝ)
    exact h2.comp h1
  have hmp : MeasurePreserving e4 volume volume := by
    have h1 := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
    have h2 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) e3)
        (volume.prod volume) (volume.prod volume) :=
      (MeasurePreserving.id volume).prod hmp3
    exact h2.comp h1
  have he4_apply : ∀ x : Fin 4 → ℝ, e4 x = (x 0, x 1, x 2, x 3) := fun _ => rfl
  have hlo : ∀ j : Fin 4, (r0j16_lo j : ℝ) = gval A_num := fun j => by
    fin_cases j <;> simp [r0j16_lo, gval, A_num, D_grid] <;> norm_num
  have hhi : ∀ j : Fin 4, (r0j16_hi j : ℝ) = gval B_num := fun j => by
    fin_cases j <;> simp [r0j16_hi, gval, B_num, D_grid] <;> norm_num
  have hdom : domain (fun j => (r0j16_lo j : ℝ)) (fun j => (r0j16_hi j : ℝ)) = e4 ⁻¹' initCell.set := by
    ext x
    simp only [domain, initCell, Cell4.set, mem_ofPred_eq, mem_preimage, mem_ofPred_eq, he4_apply, hlo, hhi]
    constructor
    · rintro ⟨hmono, hbox⟩
      exact ⟨(hbox 0).1, hmono (by decide : (0 : Fin 4) ≤ 1), hmono (by decide : (1 : Fin 4) ≤ 2),
        hmono (by decide : (2 : Fin 4) ≤ 3), (hbox 3).2⟩
    · rintro ⟨h0, h01, h12, h23, h3⟩
      refine ⟨?_, ?_⟩
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
      · intro j
        fin_cases j
        · exact ⟨show gval A_num ≤ x 0 by linarith, show x 0 ≤ gval B_num by linarith⟩
        · exact ⟨show gval A_num ≤ x 1 by linarith, show x 1 ≤ gval B_num by linarith⟩
        · exact ⟨show gval A_num ≤ x 2 by linarith, show x 2 ≤ gval B_num by linarith⟩
        · exact ⟨show gval A_num ≤ x 3 by linarith, show x 3 ≤ gval B_num by linarith⟩
  have hfun : (fun x : Fin 4 → ℝ =>
      ω ((φ - ∑ j, x j) / x ⟨2, by omega⟩) / ((∏ j, x j) * x ⟨2, by omega⟩)) =
      (fun x : Fin 4 → ℝ => integrand4 ω φ (e4 x)) := by
    ext x
    simp only [integrand4, he4_apply, Fin.sum_univ_four, Fin.prod_univ_four]
    have hnum : (φ - (x 0 + x 1 + x 2 + x 3)) / x ⟨2, by omega⟩ =
        (φ - (x 0 + x 1 + x 2 + x 3)) / x 2 := rfl
    have hden : (x 0 * x 1 * x 2 * x 3) * x ⟨2, by omega⟩ = x 0 * x 1 * x 2 * x 2 * x 3 := by
      change (x 0 * x 1 * x 2 * x 3) * x 2 = x 0 * x 1 * x 2 * x 2 * x 3; ring
    rw [hnum, hden]
  unfold buchstabIntegral
  rw [hdom, hfun]
  exact hmp.setIntegral_preimage_emb e4.measurableEmbedding (integrand4 ω φ) initCell.set

theorem interval_bound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {pa pb : Nat} {t : CTree} {φ : ℝ}
    (hpa : (pa : ℝ) / D_grid ≤ φ) (hpb : φ ≤ (pb : ℝ) / D_grid)
    (hchk : checkInterval pa pb t = true) :
    buchstabIntegral ω 2 (fun j => (r0j16_lo j : ℝ)) (fun j => (r0j16_hi j : ℝ)) φ ≤
      ((18727 / 250000000) : ℝ) := by
  unfold checkInterval at hchk
  cases heval : evalTree pa pb t initCell with
  | none => rw [heval] at hchk; cases hchk
  | some v =>
    rw [heval] at hchk
    have hvle : v ≤ TargetNat := Nat.ble_eq.mp hchk
    rw [buchstabIntegral_eq_setIntegral]
    have h1 := evalTree_sound hω hz hpa hpb t initCell initCell_valid heval
    have h2 : (v : ℝ) / S_scale ≤ (TargetNat : ℝ) / S_scale :=
      div_le_div_of_nonneg_right (by exact_mod_cast hvle) (le_of_lt hSpos)
    have h3 : (TargetNat : ℝ) / S_scale = (18727 / 250000000 : ℝ) := by
      unfold TargetNat S_scale; norm_num
    linarith

theorem tail_bound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (PaTail : ℝ) / D_grid ≤ φ) :
    buchstabIntegral ω 2 (fun j => (r0j16_lo j : ℝ)) (fun j => (r0j16_hi j : ℝ)) φ ≤
      ((18727 / 250000000) : ℝ) := by
  rw [buchstabIntegral_eq_setIntegral]
  have hwt : ∫ x in initCell.set, weight4 x ≤ (W_ub_nat : ℝ) / S_scale := by
    have hchk := check_weight_tree
    cases heval : evalWTree weight_tree initCell with
    | none => rw [heval] at hchk; cases hchk
    | some v =>
      rw [heval] at hchk
      have hvle : v ≤ W_ub_nat := Nat.ble_eq.mp hchk
      have h1 := evalWTree_sound weight_tree initCell initCell_valid heval
      have h2 : (v : ℝ) / S_scale ≤ (W_ub_nat : ℝ) / S_scale :=
        div_le_div_of_nonneg_right (by exact_mod_cast hvle) (le_of_lt hSpos)
      linarith
  have hBpos : (0 : ℝ) < B_num := by unfold B_num; positivity
  have hdiff_pos : (0 : ℝ) < (PaTail : ℝ) - 4 * B_num := by
    have h5 : (5 : ℝ) * B_num ≤ PaTail := by exact_mod_cast check_tail_pos
    linarith
  set umin : ℝ := ((PaTail : ℝ) - 4 * B_num) / B_num
  have humin1 : 1 ≤ umin := by
    dsimp [umin]; rw [one_le_div hBpos]
    have h5 : (5 : ℝ) * B_num ≤ PaTail := by exact_mod_cast check_tail_pos
    linarith
  have hpt : ∀ x ∈ initCell.set, integrand4 ω φ x ≤ max (7 / 12 : ℝ) (1 / umin) * weight4 x := by
    intro x hx
    have hxb := initCell.set_subset_box hx
    have hbd := initCell.valid_bounds initCell_valid
    unfold Cell4.box initCell cellLoHi at hxb
    rcases hxb with ⟨⟨hx0a, hx0b⟩, ⟨_, hx1b⟩, ⟨hx2a, hx2b⟩, ⟨_, hx3b⟩⟩
    have hx2_pos : 0 < x.2.2.1 := lt_of_lt_of_le (gval_pos hbd.1) hx2a
    have hB_gval : 0 < gval B_num := gval_pos (by unfold B_num; omega)
    have hu_ge : umin ≤ (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1 := by
      have hnum : gval PaTail - 4 * gval B_num ≤ φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2) := by
        unfold gval at *; linarith
      have humin_eq : umin = (gval PaTail - 4 * gval B_num) / gval B_num := by
        dsimp [umin]; unfold gval; field_simp [ne_of_gt hDpos, ne_of_gt hBpos]
      rw [humin_eq]
      calc (gval PaTail - 4 * gval B_num) / gval B_num
          ≤ (gval PaTail - 4 * gval B_num) / x.2.2.1 :=
            div_le_div_of_nonneg_left (by unfold gval; rw [← mul_div_assoc, ← sub_div]; exact div_nonneg (le_of_lt hdiff_pos) (le_of_lt hDpos))
              hx2_pos hx2b
        _ ≤ (φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1 :=
            div_le_div_of_nonneg_right hnum (le_of_lt hx2_pos)
    have hrew : integrand4 ω φ x = ω ((φ - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2)) / x.2.2.1) * weight4 x := by
      unfold integrand4 weight4; ring
    rw [hrew]
    exact mul_le_mul_of_nonneg_right (buchstab_le_max_inv hω humin1 hu_ge) (weight4_nonneg initCell_valid x hx)
  have hmono := setIntegral_mono_on (integrand4_integrableOn hω hz φ initCell_valid)
    ((weight4_integrableOn initCell_valid).const_mul (max (7 / 12 : ℝ) (1 / umin))) initCell.measurableSet_set hpt
  rw [integral_const_mul] at hmono
  have hmax_pos : 0 ≤ max (7 / 12 : ℝ) (1 / umin) := le_trans (by norm_num) (le_max_left _ _)
  have hcomb := le_trans hmono (mul_le_mul_of_nonneg_left hwt hmax_pos)
  have hbound : max (7 / 12 : ℝ) (1 / umin) * ((W_ub_nat : ℝ) / S_scale) ≤ (TargetNat : ℝ) / S_scale := by
    have ht1 : (W_ub_nat : ℝ) * B_num ≤ (TargetNat : ℝ) * ((PaTail : ℝ) - 4 * B_num) := by
      have hcast : ((W_ub_nat * B_num : Nat) : ℝ) ≤ ((TargetNat * (PaTail - 4 * B_num) : Nat) : ℝ) := by
        exact_mod_cast check_tail_1
      have hsub : ((PaTail - 4 * B_num : Nat) : ℝ) = (PaTail : ℝ) - 4 * B_num := by
        have h5 := check_tail_pos
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast at hcast; rw [hsub] at hcast; exact hcast
    have ht2 : (7 : ℝ) * W_ub_nat ≤ 12 * TargetNat := by exact_mod_cast check_tail_2
    rcases max_cases (7 / 12 : ℝ) (1 / umin) with ⟨hmax, _⟩ | ⟨hmax, _⟩
    · rw [hmax, mul_div_assoc', div_le_div_iff_of_pos_right hSpos]; linarith
    · rw [hmax, show 1 / umin = (B_num : ℝ) / ((PaTail : ℝ) - 4 * B_num) by
            dsimp [umin]; field_simp [ne_of_gt hBpos, ne_of_gt hdiff_pos]]
      rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hdiff_pos hSpos) hSpos]
      nlinarith
  have h3 : (TargetNat : ℝ) / S_scale = (18727 / 250000000 : ℝ) := by
    unfold TargetNat S_scale; norm_num
  linarith


end

end SolBuchstabR0J16

theorem solution {ω : ℝ → ℝ} (hω : LL_Decomp587l.IsBuchstab ω) (hz : LL_Decomp587l.ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (_hφtop : φ ≤ (7 / 2 : ℝ)) :
    LL_Decomp587l.buchstabIntegral ω 2 (fun j => (LL_Decomp587l.r0j16_lo j : ℝ)) (fun j => (LL_Decomp587l.r0j16_hi j : ℝ)) φ ≤
      ((18727 / 250000000) : ℝ) := by
  by_cases h0 : φ ≤ (7247593 : ℝ) / SolBuchstabR0J16.D_grid
  · exact SolBuchstabR0J16.interval_bound hω hz (pa := 7245824) (pb := 7247593) (t := SolBuchstabR0J16.tree_0) (by rw [show ((7245824 : Nat) : ℝ) / SolBuchstabR0J16.D_grid = 2 by unfold SolBuchstabR0J16.D_grid; norm_num]; exact hφ) h0 SolBuchstabR0J16.check_intv_0
  · push Not at h0
    by_cases h1 : φ ≤ (7251131 : ℝ) / SolBuchstabR0J16.D_grid
    · exact SolBuchstabR0J16.interval_bound hω hz (pa := 7247593) (pb := 7251131) (t := SolBuchstabR0J16.tree_1) (le_of_lt h0) h1 SolBuchstabR0J16.check_intv_1
    · push Not at h1
      by_cases h2 : φ ≤ (7265283 : ℝ) / SolBuchstabR0J16.D_grid
      · exact SolBuchstabR0J16.interval_bound hω hz (pa := 7251131) (pb := 7265283) (t := SolBuchstabR0J16.tree_2) (le_of_lt h1) h2 SolBuchstabR0J16.check_intv_2
      · push Not at h2
        by_cases h3 : φ ≤ (7718147 : ℝ) / SolBuchstabR0J16.D_grid
        · exact SolBuchstabR0J16.interval_bound hω hz (pa := 7265283) (pb := 7718147) (t := SolBuchstabR0J16.tree_3) (le_of_lt h2) h3 SolBuchstabR0J16.check_intv_3
        · push Not at h3
          by_cases h4 : φ ≤ (7870281 : ℝ) / SolBuchstabR0J16.D_grid
          · exact SolBuchstabR0J16.interval_bound hω hz (pa := 7718147) (pb := 7870281) (t := SolBuchstabR0J16.tree_4) (le_of_lt h3) h4 SolBuchstabR0J16.check_intv_4
          · push Not at h4
            exact SolBuchstabR0J16.tail_bound hω hz (le_of_lt h4)
