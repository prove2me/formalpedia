-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.cubic_chart_source_identities
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T06:54:30.151465+00:00
-- url     : https://prove2.me/submissions/e3fd95d7-ba22-4c46-9dc2-a2342b01b14d

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem solution
    {K : Type*} [Field K] [CharZero K]
    (p pr ps : Fin 4 → K)
    (t alpha beta U V ar as_ br bs hPa Pra Psa Pta : K)
    (hden : t ^ 2 - alpha ^ 2 ≠ 0)
    (hPa_ne : hPa ≠ 0)
    (hbeta : beta ≠ 0)
    (hbr : br = beta * (Pra + Pta * ar) / (3 * hPa))
    (hbs : bs = beta * (Psa + Pta * as_) / (3 * hPa))
    (hsum : p 0 + p 1 * alpha ^ 2 + p 2 * alpha ^ 4 + p 3 * alpha ^ 6 = 0) :
    let P (q : Fin 4 → K) (x : K) := q 0 + q 1 * x ^ 2 + q 2 * x ^ 4 + q 3 * x ^ 6
    let dPt := 2 * p 1 * t + 4 * p 2 * t ^ 3 + 6 * p 3 * t ^ 5
    let Z := U * as_ - V * ar
    let M := U * Psa - V * Pra
    let T := (Pta * Z + M) / hPa
    let dqt_t := -2 * beta ^ 2 * Z * ((t ^ 2 - alpha ^ 2) - 2 * t ^ 2) / (t ^ 2 - alpha ^ 2) ^ 2
    let dqr_a := 2 * beta ^ 2 * V * ((t ^ 2 - alpha ^ 2) + 2 * alpha ^ 2) / (t ^ 2 - alpha ^ 2) ^ 2
    let dqr_b := 4 * beta * alpha * V / (t ^ 2 - alpha ^ 2)
    let dqs_a := -2 * beta ^ 2 * U * ((t ^ 2 - alpha ^ 2) + 2 * alpha ^ 2) / (t ^ 2 - alpha ^ 2) ^ 2
    let dqs_b := -4 * beta * alpha * U / (t ^ 2 - alpha ^ 2)
    let divq := dqt_t + (dqr_a * ar + dqr_b * br) + (dqs_a * as_ + dqs_b * bs)
    let qt := -2 * beta ^ 2 * t * Z / (t ^ 2 - alpha ^ 2)
    let qr := 2 * beta ^ 2 * alpha * V / (t ^ 2 - alpha ^ 2)
    let qs := -2 * beta ^ 2 * alpha * U / (t ^ 2 - alpha ^ 2)
    let N := alpha * P p t * T - alpha * (U * P ps t - V * P pr t) - t * dPt * Z
    let gamma := (p 1 + alpha ^ 2 * p 2 + alpha ^ 4 * p 3) +
      (p 2 + alpha ^ 2 * p 3) * t ^ 2 + p 3 * t ^ 4
    (P p t = (t ^ 2 - alpha ^ 2) * gamma) ∧
    (divq = -4 * beta ^ 2 * alpha * T / (3 * (t ^ 2 - alpha ^ 2))) ∧
    (-(P p t * divq - (2 / 3 : K) * (qt * dPt + qr * P pr t + qs * P ps t)) =
      (4 / 3 : K) * beta ^ 2 * N / (t ^ 2 - alpha ^ 2)) := by
  intro P dPt Z M T dqt_t dqr_a dqr_b dqs_a dqs_b divq qt qr qs N gamma
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [P, gamma]; linear_combination hsum
  · dsimp only [divq, dqt_t, dqr_a, dqr_b, dqs_a, dqs_b, Z, M, T]
    rw [hbr, hbs]
    field_simp [hden, hPa_ne]
    ring
  · have hdiv : divq = -4 * beta ^ 2 * alpha * T / (3 * (t ^ 2 - alpha ^ 2)) := by
      dsimp only [divq, dqt_t, dqr_a, dqr_b, dqs_a, dqs_b, Z, M, T]
      rw [hbr, hbs]
      field_simp [hden, hPa_ne]
      ring
    rw [hdiv]
    dsimp only [P, dPt, Z, M, T, qt, qr, qs, N]
    field_simp [hden, hPa_ne, hbeta]
    ring
