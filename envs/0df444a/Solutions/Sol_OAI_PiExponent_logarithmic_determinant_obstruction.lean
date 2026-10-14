-- Prove2me | solution 1 for OAI.PiExponent.logarithmic_determinant_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T08:31:47.177123+00:00
-- url     : https://prove2.me/submissions/c12502e6-26ab-4087-8875-48a74cc6868b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PiExponent_DeterminantSetup
import Theorems.Thm_OAI_PiExponent_denominator_clearing_determinant_dichotomy

theorem solution
    (nu : ℝ) (hnu : 2 < nu) (B : OAI.PiExponent.DeterminantBudget nu)
    (p : Fin B.m → ℤ) (q w : Fin B.m → ℕ)
    (hq : ∀ i, 2 ≤ q i) (hp : ∀ i, p i ≠ 0)
    (hw : ∀ i, w i = Nat.ceil (Real.log (q i : ℝ)))
    (hmin : ∀ i, B.wmin ≤ w i)
    (happrox : ∀ i,
      |Real.pi - (p i : ℝ) / (q i : ℝ)| ≤ (q i : ℝ) ^ (-nu))
    (hrank : ∀ c : Fin B.K → Fin B.m → ℂ,
      (∀ i : Fin B.m, Function.Injective (fun j : Fin B.K => c j i)) →
      OAI.PiExponent.eventualLogJetSurjective
        B.m B.K B.w0 B.v0 B.theta w c) : False := by
  rcases OAI.PiExponent.denominator_clearing_determinant_dichotomy
      nu hnu B p q w hq hp hw hmin happrox hrank with h | h
  · exact (not_lt_of_ge h) B.error_gap
  · exact (not_lt_of_ge h) B.collision_gap