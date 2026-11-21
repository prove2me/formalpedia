-- Prove2me | solution 1 for Helfgott.actual_primitive_finite_grh_profile
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T23:56:12.720852+00:00
-- url     : https://prove2.me/submissions/e064054d-7d36-486a-8bf4-65e530df56c7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive
import Mathlib.NumberTheory.LSeries.Nonvanishing
open scoped Classical

theorem solution :
  ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),ψ.IsPrimitive →
      (if Odd q then 2*q else q : ℕ)≤300000 → ∀ ρ : ℂ,
      0<ρ.re → ρ.re<1 → ψ.LFunction ρ=0 →
      |ρ.im| < max (200+75000000/((if Odd q then 2*q else q : ℕ) : ℝ))
        ((10 : ℝ)^8/(q : ℝ)) → ρ.re=1/2 :=
  fun q _ ψ hψ _ ρ h0 h1 hz _ => AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive q ψ hψ ρ h0 h1 hz
