-- Prove2me | solution 1 for NonconvexDRS.ADMM.step_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:29:43.568994+00:00
-- url     : https://prove2.me/submissions/d0a11d4b-f327-458c-ba6c-d0dd16143220

import Mathlib
set_option autoImplicit false

open scoped InnerProductSpace

theorem solution {m n p : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (b : EuclideanSpace ℝ (Fin p))
    (β lam : ℝ) (hβ : 0 < β)
    (x xp : EuclideanSpace ℝ (Fin m)) (y yh yp : EuclideanSpace ℝ (Fin p))
    (z : EuclideanSpace ℝ (Fin n))
    (hyh : yh = y - (β * (1 - lam)) • (A x + B z - b))
    (hyp : yp = yh + β • (A xp + B z - b)) :
    A xp - (1 / β) • yp = (A x - (1 / β) • y) + lam • ((b - B z) - A x) := by
  subst hyp hyh
  have hb : β ≠ 0 := hβ.ne'
  match_scalars <;> field_simp <;> ring
