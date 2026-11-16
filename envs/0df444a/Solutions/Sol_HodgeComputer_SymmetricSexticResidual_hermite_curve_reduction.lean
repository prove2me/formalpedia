-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.hermite_curve_reduction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T05:49:06.44293+00:00
-- url     : https://prove2.me/submissions/7006a93f-15a6-4e82-a19f-6706938c50aa

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem solution
    {K : Type*} [Field K] [CharZero K]
    (D : Derivation ℤ K K)
    (x g n gu nu nn Q Qx Qu : K)
    (hx : x ≠ 0) (hg : g ≠ 0) (hn : n ≠ 0)
    (hQ : D Q = Qx - n * Qu / g)
    (hnD : D n = nn - n * nu / g)
    (hgD : D g = nu - n * gu / g) :
    (g * Qu - gu * Q) / g ^ 3 =
      (D (-Q / (n * g)) + (-Q / (n * g)) / (2 * x)) +
        ((2 * x * (Qx * n - Q * nn) + Q * n) / (n ^ 2 * g)) / (2 * x) := by
  have hprod : D (n * g) = (nn - n * nu / g) * g + n * (nu - n * gu / g) := by
    rw [Derivation.leibniz, hnD, hgD]
    ring
  rw [Derivation.leibniz_div]
  simp only [map_neg, hQ, hprod, smul_eq_mul]
  field_simp [hx, hg, hn]
  ring
