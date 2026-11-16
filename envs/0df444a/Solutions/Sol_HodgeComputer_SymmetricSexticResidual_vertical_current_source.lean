-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.vertical_current_source
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T05:49:05.17279+00:00
-- url     : https://prove2.me/submissions/dc3c6661-cfcc-4a70-8090-2462d414fdd8

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem solution
    {K : Type*} [Field K] [CharZero K]
    (T : Derivation ℤ K K) (t u l B C D Bx Cx Dx : K)
    (hTt : T t = 1) (hTl : T l = 0)
    (hTB : T B = 2 * t * Bx) (hTC : T C = 2 * t * Cx)
    (hTu : T u = -(2 * t * (Bx * u ^ 2 + Cx * u + Dx)) / (3 * l * u ^ 2 + 2 * B * u + C))
    (hl : l ≠ 0)
    (hf : l * u ^ 3 + B * u ^ 2 + C * u + D = 0)
    (hg : 3 * l * u ^ 2 + 2 * B * u + C ≠ 0) :
    let x := t ^ 2
    let g := 3 * l * u ^ 2 + 2 * B * u + C
    let gu := 6 * l * u + 2 * B
    let K0 := (-B * C + 4 * x * Bx * C + 9 * l * D - 12 * l * x * Dx) / (12 * l)
    let K1 := (-B ^ 2 + 4 * x * B * Bx + 3 * l * C - 6 * l * x * Cx) / (6 * l)
    T (t / g) = 2 * (g * K1 - gu * (K0 + K1 * u)) / g ^ 3 := by
  intro x g gu K0 K1
  have hT2 : T (2 : K) = 0 := T.map_natCast 2
  have hT3 : T (3 : K) = 0 := T.map_natCast 3
  have hTg : T g = 2 * t * (2 * Bx * u + Cx) + gu * T u := by
    dsimp only [g, gu]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      hT2, hT3, hTl, hTB, hTC]
    ring
  have hcert : g ^ 2 - 2 * x * g * (2 * Bx * u + Cx) +
      2 * x * (Bx * u ^ 2 + Cx * u + Dx) * gu -
      2 * (g * K1 - gu * (K0 + K1 * u)) =
      3 * (B + 3 * l * u) * (l * u ^ 3 + B * u ^ 2 + C * u + D) := by
    dsimp only [x, g, gu, K0, K1]
    field_simp [hl]
    ring
  rw [hf, mul_zero] at hcert
  have hnum : g ^ 2 - 2 * x * g * (2 * Bx * u + Cx) +
      2 * x * (Bx * u ^ 2 + Cx * u + Dx) * gu =
      2 * (g * K1 - gu * (K0 + K1 * u)) := by
    linear_combination hcert
  have hg0 : g ≠ 0 := hg
  rw [Derivation.leibniz_div, hTt, hTg, hTu]
  simp only [smul_eq_mul, mul_one]
  rw [show (3 * l * u ^ 2 + 2 * B * u + C) = g from rfl]
  field_simp [hg0]
  have hx_eq : t ^ 2 = x := rfl
  rw [← hx_eq] at hnum
  linear_combination hnum
