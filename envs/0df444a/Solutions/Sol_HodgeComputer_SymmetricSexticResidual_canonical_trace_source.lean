-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.canonical_trace_source
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:48:36.600219+00:00
-- url     : https://prove2.me/submissions/cb722fbb-bc3d-4572-94b6-3a0c7c42e905

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exact coefficient and canonical source identities for the symmetric sextic chart.
This algebraic packet does not assert existence of a rational primitive.
The reflection chart and conditional trace endpoint are due to the contributors
credited in fqlx's PR #222 at d0919c2 and benediamond's PR #223.  This exact
coefficient calculation was prepared for kmehltretter82 with OpenAI Codex
assistance. -/
theorem solution
    (lam b c d u : ℂ) :
    let L := 1 + 2*b
    let R := c^2 + 2*c*d
    let ell := 2 + 2*lam^6 - (5/7 : ℂ)*lam^2 - (10/7 : ℂ)*lam^4
    let B := 30 + 30*lam^4*c^2 + (5/7 : ℂ)*(R + 2*lam^2*L) +
      (10/7 : ℂ)*(lam^4*L + 2*lam^2*R)
    let C := 30 + 30*lam^2*c^4 + (5/7 : ℂ)*(-lam^2*L^2 - 2*L*R) +
      (10/7 : ℂ)*(-2*lam^2*L*R - R^2)
    let D := 2 + b^6 + 2*c^6 + d^6 + (5/7 : ℂ)*L^2*R + (10/7 : ℂ)*L*R^2
    let P := b*d*(1-u)*(c^2-lam^2*u)
    let Pu := b*d*(-c^2-lam^2+2*lam^2*u)
    let g := 3*ell*u^2 + 2*B*u + C
    let gu := 6*ell*u + 2*B
    let T0 := b*d*c^2 - b*d*lam^2*C/(3*ell)
    let T1 := -b*d*(c^2+lam^2) - 2*b*d*lam^2*B/(3*ell)
    ell ≠ 0 →
      (2 + b^6 + 2*c^6 + d^6 + 30*u + 30*u^2 + 2*u^3 +
        30*lam^2*c^4*u + 30*lam^4*c^2*u^2 + 2*lam^6*u^3 +
        (5/7 : ℂ)*(L-u)^2*(R-lam^2*u) +
        (10/7 : ℂ)*(L-u)*(R-lam^2*u)^2 = ell*u^3+B*u^2+C*u+D) ∧
      (P - (b*d*lam^2/(3*ell))*g = T0+T1*u) ∧
      (Pu - (b*d*lam^2/(3*ell))*gu = T1) ∧
      (g*Pu-gu*P = g*T1-gu*(T0+T1*u)) := by
  intro L R ell B C D P Pu g gu T0 T1 hell
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [ell, B, C, D]
    ring
  all_goals dsimp only [P, Pu, g, gu, T0, T1]
  all_goals field_simp [hell]
  all_goals ring

#print axioms solution
