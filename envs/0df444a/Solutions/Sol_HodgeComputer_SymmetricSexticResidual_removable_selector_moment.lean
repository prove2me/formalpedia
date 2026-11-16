-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.removable_selector_moment
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T05:49:04.581589+00:00
-- url     : https://prove2.me/submissions/34ff6c71-3e3a-42ec-915b-8b1b8ad30905

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem solution
    (x u l b0 b1 c0 c1 c2 d0 d1 d2 d3 lam s : ℂ) :
    let B := b0 + b1 * x
    let Bx := b1
    let C := c0 + c1 * x + c2 * x ^ 2
    let Cx := c1 + 2 * c2 * x
    let D := d0 + d1 * x + d2 * x ^ 2 + d3 * x ^ 3
    let Dx := d1 + 2 * d2 * x + 3 * d3 * x ^ 2
    let f := l * u ^ 3 + B * u ^ 2 + C * u + D
    let g := 3 * l * u ^ 2 + 2 * B * u + C
    let gu := 6 * l * u + 2 * B
    let fx := Bx * u ^ 2 + Cx * u + Dx
    let gx := 2 * Bx * u + Cx
    let K0 := (-B * C + 4 * x * Bx * C + 9 * l * D - 12 * l * x * Dx) / (12 * l)
    let K1 := (-B ^ 2 + 4 * x * B * Bx + 3 * l * C - 6 * l * x * Cx) / (6 * l)
    let ell := 2 + 2 * lam ^ 6 - (5 / 7 : ℂ) * lam ^ 2 - (10 / 7 : ℂ) * lam ^ 4
    let actualB1 := 30 * lam ^ 4 + (5 / 7 : ℂ) * (1 + 2 * s) +
      (20 / 7 : ℂ) * lam ^ 2 * (1 + 2 * s)
    let actualC2 := 30 * lam ^ 2 - (10 / 7 : ℂ) * (1 + 2 * s) ^ 2
    (l ≠ 0 →
      (g ^ 2 - 2 * x * g * gx + 2 * x * fx * gu - 2 * (g * K1 - gu * (K0 + K1 * u)) =
        3 * (B + 3 * l * u) * f) ∧
      (K0 = (-b0 * c0 + 9 * l * d0) / (12 * l) +
            ((3 * b1 * c0 - b0 * c1 - 3 * l * d1) / (12 * l)) * x +
            ((3 * b1 * c1 - b0 * c2 - 15 * l * d2) / (12 * l)) * x ^ 2 +
            ((3 * b1 * c2 - 27 * l * d3) / (12 * l)) * x ^ 3) ∧
      (K1 = (-b0 ^ 2 + 3 * l * c0) / (6 * l) +
            ((2 * b0 * b1 - 3 * l * c1) / (6 * l)) * x +
            ((b1 ^ 2 - 3 * l * c2) / (2 * l)) * x ^ 2)) ∧
    (lam = 1 → s = 0 →
      ell ≠ 0 ∧ (actualB1 ^ 2 - 3 * ell * actualC2) / (2 * ell) = (47425 / 182 : ℂ)) := by
  intro B Bx C Cx D Dx f g gu fx gx K0 K1 ell actualB1 actualC2
  refine ⟨fun hl => ⟨?_, ?_, ?_⟩, fun hlam hs => ?_⟩
  · dsimp only [B, Bx, C, Cx, D, Dx, f, g, gu, fx, gx, K0, K1]
    field_simp [hl]
    ring
  · dsimp only [B, Bx, C, D, Dx, K0]
    field_simp [hl]
    ring
  · dsimp only [B, Bx, C, Cx, K1]
    field_simp [hl]
    ring
  · subst hlam; subst hs
    dsimp only [ell, actualB1, actualC2]
    constructor <;> norm_num
