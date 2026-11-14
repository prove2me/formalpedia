-- Prove2me | solution 1 for KSATSingleFlip.Connect.wordRAM_log_width
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:00:16.19392+00:00
-- url     : https://prove2.me/submissions/53b46cb1-fb72-46da-b110-3f2e9c2dcf57

import Definitions.Def_KSATSingleFlip_Connect_WordRAM

namespace KSATSingleFlip.Connect

/-- A quadratic-size address bound needs logarithmically many bits. -/
theorem audit_log2_quadratic_bound (A n : ℕ) :
    Nat.log2 (A * (n + 1)^2 + 1) + 1 ≤
      Nat.log2 (A + 1) + 2 * Nat.log2 (n + 1) + 5 := by
  let b := n + 1
  let q := A + 1
  let X := 2 ^ (Nat.log2 q + 1)
  let Y := 2 ^ (Nat.log2 b + 1)
  have hq : q < X := Nat.lt_log2_self
  have hb : b < Y := Nat.lt_log2_self
  have hb2 : b^2 < Y^2 := Nat.pow_lt_pow_left hb (by decide)
  have hbpos : 0 < b^2 := by dsimp [b]; positivity
  have hXpos : 0 < X := by dsimp [X]; positivity
  have hmul1 : q * b^2 < X * b^2 := Nat.mul_lt_mul_of_pos_right hq hbpos
  have hmul2 : X * b^2 < X * Y^2 := Nat.mul_lt_mul_of_pos_left hb2 hXpos
  have hle : A * (n + 1)^2 + 1 ≤ q * b^2 := by
    dsimp [q, b]
    have hs : 0 < (n + 1)^2 := by positivity
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hpow : X * Y^2 = 2 ^ (Nat.log2 q + 1 + 2 * (Nat.log2 b + 1)) := by
    dsimp [X, Y]
    rw [← Nat.pow_mul, ← Nat.pow_add]
    congr 1
    omega
  have hlt : A * (n + 1)^2 + 1 <
      2 ^ (Nat.log2 q + 1 + 2 * (Nat.log2 b + 1)) := by
    rw [← hpow]
    exact lt_of_le_of_lt hle (lt_trans hmul1 hmul2)
  have hlog := (Nat.log2_lt (by omega : A * (n + 1)^2 + 1 ≠ 0)).mpr hlt
  dsimp [q, b] at hlog
  omega

/-- For sparse linear-size input and a quadratic time budget, the chosen
word width is logarithmic in n, with constants depending on k,c,d. -/
theorem audit_wordRAM_log_width (n k m T c d : ℕ)
    (hm : m ≤ c * n) (hT : T ≤ d * (n + 1)^2) :
    wordRAMWidth n k m T ≤
      Nat.log2 (k + c + 2*k*c + d + 13) + 2 * Nat.log2 (n + 1) + 5 ∧
    wordRAMRouteWidth n k m T ≤
      Nat.log2 (k + c + 2*k*c + d + 13) + 2 * Nat.log2 (n + 1) + 5 := by
  let A := k + c + 2*k*c + d + 12
  let b := (n + 1)^2
  have hs : 1 ≤ b := by
    have hb : 0 < b := by dsimp [b]; positivity
    omega
  have hn : n ≤ b := by
    dsimp [b]
    exact (Nat.le_succ n).trans (Nat.le_self_pow (by decide) (n + 1))
  have hkm := Nat.mul_le_mul_left (2*k) hm
  have hc := Nat.mul_le_mul_left c hn
  have hkc := Nat.mul_le_mul_left (2*k*c) hn
  have hk := Nat.mul_le_mul_left k hs
  have h12 := Nat.mul_le_mul_left 12 hs
  have hn3 := Nat.mul_le_mul_left 3 hn
  have hboundFlip : n + k + m + sparseFlipInputWords n k m + T + 2 ≤ A*b + 1 := by
    dsimp [A, b, sparseFlipInputWords] at *
    nlinarith
  have hboundRoute : n + k + m + sparseRouteInputWords n k m + T + 2 ≤ A*b + 1 := by
    dsimp [A, b, sparseRouteInputWords] at *
    nlinarith
  constructor
  · unfold wordRAMWidth
    have hlog : Nat.log2 (n + k + m + sparseFlipInputWords n k m + T + 2) ≤
        Nat.log2 (A * b + 1) := by
      simp only [Nat.log2_eq_log_two]
      exact Nat.log_mono_right hboundFlip
    have hquad := audit_log2_quadratic_bound A n
    have hfinal := (Nat.add_le_add_right hlog 1).trans hquad
    simpa only [A, b, ← Nat.add_assoc, show 12 + 1 = 13 by decide] using hfinal
  · unfold wordRAMRouteWidth
    have hlog : Nat.log2 (n + k + m + sparseRouteInputWords n k m + T + 2) ≤
        Nat.log2 (A * b + 1) := by
      simp only [Nat.log2_eq_log_two]
      exact Nat.log_mono_right hboundRoute
    have hquad := audit_log2_quadratic_bound A n
    have hfinal := (Nat.add_le_add_right hlog 1).trans hquad
    simpa only [A, b, ← Nat.add_assoc, show 12 + 1 = 13 by decide] using hfinal

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

theorem solution (n k m T c d : ℕ)
    (hm : m ≤ c * n) (hT : T ≤ d * (n + 1)^2) :
    wordRAMWidth n k m T ≤
      Nat.log2 (k + c + 2*k*c + d + 13) + 2 * Nat.log2 (n + 1) + 5 ∧
    wordRAMRouteWidth n k m T ≤
      Nat.log2 (k + c + 2*k*c + d + 13) + 2 * Nat.log2 (n + 1) + 5 := by
  exact audit_wordRAM_log_width n k m T c d hm hT

#print axioms solution
