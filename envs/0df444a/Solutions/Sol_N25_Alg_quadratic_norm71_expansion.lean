-- Prove2me | solution 1 for N25.Alg.quadratic_norm71_expansion
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:22:02.17617+00:00
-- url     : https://prove2.me/submissions/196c9d0f-d9ee-4b43-ac17-ac2d8ccb8bb9

import Mathlib

namespace N25.Alg

private theorem quadratic_zero {G : Type*} [AddCommGroup G] (q : G → ℝ)
    (hp : ∀ a b, q (a + b) + q (a - b) = 2 * q a + 2 * q b) : q 0 = 0 := by
  have h := hp 0 0
  simp only [add_zero, sub_zero] at h
  linarith

private theorem quadratic_double {G : Type*} [AddCommGroup G] (q : G → ℝ)
    (hp : ∀ a b, q (a + b) + q (a - b) = 2 * q a + 2 * q b) (a : G) :
    q (a + a) = 4 * q a := by
  have h := hp a a
  rw [sub_self, quadratic_zero q hp] at h
  linarith

private theorem quadratic_triple {G : Type*} [AddCommGroup G] (q : G → ℝ)
    (hp : ∀ a b, q (a + b) + q (a - b) = 2 * q a + 2 * q b) (a b c : G) :
    q (a + b + c) + q a + q b + q c = q (a + b) + q (a + c) + q (b + c) := by
  have h₁ := hp (a + b) c
  have h₂ := hp (a + c) b
  have h₃ := hp (a + b - c) (a + c - b)
  have h₄ := hp b c
  have hs : a + b - c + (a + c - b) = a + a := by abel
  have hd : a + b - c - (a + c - b) = (b - c) + (b - c) := by abel
  have ht : a + c + b = a + b + c := by abel
  rw [hs, hd, quadratic_double q hp a, quadratic_double q hp (b - c)] at h₃
  rw [ht] at h₂
  linarith

/-- The norm identity for the cyclotomic order-five action. -/
private theorem quadratic_norm_identity {G : Type*} [AddCommGroup G] (d : G →+ G)
    (hΦ : ∀ x, x + d x + d (d x) + d (d (d x)) + d (d (d (d x))) = 0)
    (q : G → ℝ) (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y) (hinv : ∀ x, q (d x) = q x) (x : G) :
    3 * q (2 • x + 4 • d x + d (d x)) = 7 * q x + 10 * q (2 • x + d x + d (d (d (d x)))) := by
  let B : G → G → ℝ := fun a b => q (a + b) - q a - q b
  have Bcomm : ∀ a b, B a b = B b a := by
    intro a b
    dsimp [B]
    rw [add_comm a b]
    ring
  have Bleft : ∀ a b c, B (a + b) c = B a c + B b c := by
    intro a b c
    have h := quadratic_triple q hpar a b c
    have hc : b + c = c + b := add_comm _ _
    dsimp [B]
    linarith
  have Bright : ∀ a b c, B a (b + c) = B a b + B a c := by
    intro a b c
    rw [Bcomm, Bleft, Bcomm b a, Bcomm c a]
  have Bzero : ∀ a, B a 0 = 0 := by
    intro a
    simp [B, quadratic_zero q hpar]
  have Bself : ∀ a, B a a = 2 * q a := by
    intro a
    dsimp [B]
    rw [quadratic_double q hpar]
    ring
  have Binv : ∀ a b, B (d a) (d b) = B a b := by
    intro a b
    dsimp [B]
    rw [← map_add, hinv, hinv, hinv]
  have hpow : d (d (d (d (d x)))) = x := by
    have h := congrArg d (hΦ x)
    simp only [map_add, map_zero] at h
    have hbase := hΦ x
    linear_combination (norm := abel_nf) h - hbase
  have Be : B x (d (d (d (d x)))) = B x (d x) := by
    have h := Binv x (d (d (d (d x))))
    rw [hpow, Bcomm (d x) x] at h
    exact h.symm
  have Bbc : B (d x) (d (d x)) = B x (d x) := Binv x (d x)
  have Bbe : B (d x) (d (d (d (d x)))) = B x (d (d x)) := by
    have h := Binv (d x) (d (d (d (d x))))
    rw [hpow, Bcomm (d (d x)) x] at h
    exact h.symm
  have Bz : B x (d (d (d x))) = B x (d (d x)) := by
    have h := Binv x (d (d (d x)))
    rw [Bbe] at h
    exact h.symm
  have hrel := congrArg (B x) (hΦ x)
  rw [Bright, Bright, Bright, Bright, Bself, Be, Bz, Bzero] at hrel
  have qadd : ∀ a b, q (a + b) = q a + q b + B a b := by
    intro a b
    dsimp [B]
    ring
  have htwo : ∀ a : G, 2 • a = a + a := fun a => two_nsmul a
  have hfour : ∀ a : G, 4 • a = (a + a) + (a + a) := by
    intro a
    simp only [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, two_nsmul]
  simp only [htwo, hfour, qadd, Bleft, Bright, Bself, hinv, Be, Bbc, Bbe]
  linarith

/-- Nonnegativity and the cyclotomic norm identity give expansion by seven thirds. -/
theorem _root_.solution {G : Type*} [AddCommGroup G] (d : G →+ G)
    (hΦ : ∀ x, x + d x + d (d x) + d (d (d x)) + d (d (d (d x))) = 0)
    (q : G → ℝ) (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hinv : ∀ x, q (d x) = q x) (hnn : ∀ x, 0 ≤ q x) (x : G) :
    (7 / 3 : ℝ) * q x ≤ q (2 • x + 4 • d x + d (d x)) := by
  have h := quadratic_norm_identity d hΦ q hpar hinv x
  have hn := hnn (2 • x + d x + d (d (d (d x))))
  linarith

end N25.Alg
