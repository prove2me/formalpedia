-- Prove2me | solution 1 for N25.siegelFun_neg_first_index
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:50.601226+00:00
-- url     : https://prove2.me/submissions/d8725806-b34b-4c73-a62f-5a29734ee79b

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option autoImplicit false

open scoped BigOperators

namespace N25

/-- Simultaneous inversion of the exponential factor in the literal product
makes the zero-second-index Siegel function odd in its first index. -/
theorem _root_.solution (N : ℕ) (r : ℤ) (z : ℂ) :
    ModularCurve.siegelFun N (-r) 0 z = -ModularCurve.siegelFun N r 0 z := by
  let B (t : ℤ) : ℂ := Real.pi * Complex.I *
    (((t : ℂ)/(N : ℂ))^2 - (t : ℂ)/(N : ℂ) + 1/6) * z
  let X (t : ℤ) : ℂ := 2 * Real.pi * Complex.I * ((t : ℂ)*z) / (N : ℂ)
  let q : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)
  let P (t : ℤ) : ℂ := ∏' n : ℕ,
    ((1 - q^(n+1) * Complex.exp (X t)) *
      (1 - q^(n+1) * (Complex.exp (X t))⁻¹))
  have hformula (t : ℤ) : ModularCurve.siegelFun N t 0 z =
      -Complex.exp (B t) * (1 - Complex.exp (X t)) * P t := by
    unfold ModularCurve.siegelFun
    dsimp only [B, X, q, P]
    simp only [Int.cast_zero, mul_zero, zero_mul, zero_div, Complex.exp_zero,
      neg_one_mul, add_zero]
  have hX : X (-r) = -X r := by
    dsimp only [X]
    push_cast
    ring
  have hB : B (-r) = B r + X r := by
    dsimp only [B, X]
    push_cast
    ring
  have hP : P (-r) = P r := by
    dsimp only [P]
    apply tprod_congr
    intro n
    rw [hX, Complex.exp_neg, inv_inv]
    ring
  rw [hformula (-r), hformula r, hB, hX, hP, Complex.exp_add, Complex.exp_neg]
  have he := Complex.exp_ne_zero (X r)
  field_simp [he]
  ring

end N25
