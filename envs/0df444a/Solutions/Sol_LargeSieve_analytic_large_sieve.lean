-- Prove2me | solution 1 for LargeSieve.analytic_large_sieve
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T04:15:11.478976+00:00
-- url     : https://prove2.me/submissions/9b91156e-3060-4bb8-8717-63d6337b3f15

import Mathlib

set_option maxHeartbeats 1000000
set_option linter.all false

-- ==== upstream: Salt/LS/Defs.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Large sieve track, node L0.1: the frozen carriers `e` and `expSum`

Blueprint: `docs/blueprints/largesieve.md` (Rung 5 opener). This file freezes
the two carriers the whole track is built on:

* `e x = exp (2πi x)`, the additive character on `ℝ`;
* `expSum N a α = ∑ n < N, a n · e (n α)`, the exponential (trig) polynomial.

Together with the elementary trivia the analytic large sieve needs: `‖e x‖ = 1`,
1-periodicity, additivity, `e 0 = 1`, the conjugate identity
`conj (e x) = e (−x)`, and continuity of both `e` and `expSum` (the derivative
identities are deferred to W2). Continuity is registered with `@[fun_prop]` so
downstream integrability side goals discharge automatically — per the blueprint
docstring note, `expSum` is a finite sum of smooth terms and needs no
measurability nodes.
-/

namespace Salt.LS

open scoped BigOperators

/-- **L0.1 carrier.** The additive character `e(x) = exp(2πi·x)` on `ℝ`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- **L0.1 carrier.** The exponential polynomial `∑_{n<N} a n · e(nα)`. -/
noncomputable def expSum (N : ℕ) (a : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * e (n * α)

/-- `e` has unit modulus: `‖e x‖ = 1`. -/
@[simp] lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  have : e x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold e; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- `e 0 = 1`. -/
@[simp] lemma e_zero : e 0 = 1 := by
  unfold e; simp

/-- Additivity of `e`: `e (x + y) = e x * e y`. -/
lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

/-- `e 1 = 1`. -/
@[simp] lemma e_one : e 1 = 1 := by
  have : e 1 = Complex.exp (2 * (Real.pi : ℂ) * Complex.I) := by
    unfold e; congr 1; push_cast; ring
  rw [this, Complex.exp_two_pi_mul_I]

/-- `e` is 1-periodic: `e (x + 1) = e x`. -/
lemma e_add_one (x : ℝ) : e (x + 1) = e x := by
  rw [e_add, e_one, mul_one]

/-- The conjugate identity `conj (e x) = e (−x)`. -/
lemma conj_e (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- `e` is continuous. Registered with `@[fun_prop]`/`@[continuity]` so
integrability side goals in the track discharge by `fun_prop`. -/
@[continuity, fun_prop]
lemma continuous_e : Continuous e := by
  unfold e; fun_prop

/-- `expSum N a` is continuous (finite sum of smooth terms). -/
@[continuity, fun_prop]
lemma continuous_expSum (N : ℕ) (a : ℕ → ℂ) : Continuous (expSum N a) := by
  unfold expSum
  apply continuous_finsetSum
  intro n _
  fun_prop

end Salt.LS

-- ==== upstream: Salt/LS/Parseval.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Large sieve track, nodes L1.1 + L1.2: orthogonality and finite Parseval

Blueprint: `docs/blueprints/largesieve.md`.

* **L1.1** (`integral_e_int`): orthogonality of the characters,
  `∫₀¹ e(kα) dα = [k = 0]` for `k : ℤ`, with the `(n,m)`-form corollary
  `integral_e_mul_conj` used by Parseval.
* **L1.2** (`parseval`): the frozen finite Parseval identity
  `∫₀¹ ‖expSum N a α‖² dα = ∑_{n<N} ‖a n‖²`.

Integrability throughout is `Continuous.intervalIntegrable` on the smooth
carriers (`continuous_e`, `continuous_expSum`); no measurability nodes.
-/

namespace Salt.LS

open scoped BigOperators
open intervalIntegral MeasureTheory

/-- **L1.1 — orthogonality.** `∫₀¹ e(kα) dα = 1` if `k = 0`, else `0`
(exponent cast from `ℤ`). -/
theorem integral_e_int (k : ℤ) :
    (∫ α in (0:ℝ)..1, e ((k : ℝ) * α)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk]
    have h1 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h2 : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h1) Complex.I_ne_zero) h2
    have hrw : (∫ α in (0:ℝ)..1, e ((k : ℝ) * α))
        = ∫ α in (0:ℝ)..1, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) * α) := by
      apply intervalIntegral.integral_congr
      intro α _
      unfold e
      exact congrArg Complex.exp (by push_cast; ring)
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) = 1 := by
      rw [show (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))
            = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [hrw, integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, hexp,
      sub_self, zero_div]

/-- **L1.1 corollary — the `(n,m)` form.** For `n m : ℕ`,
`∫₀¹ e(nα) · conj (e(mα)) dα = [n = m]`. This is the shape Parseval consumes. -/
theorem integral_e_mul_conj (n m : ℕ) :
    (∫ α in (0:ℝ)..1, e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α)))
      = if n = m then 1 else 0 := by
  have step : ∀ α : ℝ,
      e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α))
        = e ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * α) := by
    intro α
    rw [conj_e, ← e_add]
    congr 1
    push_cast; ring
  have hcongr : (∫ α in (0:ℝ)..1, e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α)))
      = ∫ α in (0:ℝ)..1, e ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * α) :=
    intervalIntegral.integral_congr (fun α _ => step α)
  rw [hcongr, integral_e_int]
  by_cases hnm : n = m
  · subst hnm; simp
  · have hne : ((n : ℤ) - (m : ℤ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
    rw [if_neg hne, if_neg hnm]

/-- **L1.2 — finite Parseval (FROZEN).**
`∫₀¹ ‖expSum N a α‖² dα = ∑_{n<N} ‖a n‖²`. -/
theorem parseval (N : ℕ) (a : ℕ → ℂ) :
    (∫ α in (0:ℝ)..1, ‖expSum N a α‖ ^ 2) = ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  -- Pointwise: ‖z‖² (as a complex) is `z * conj z`.
  have pt : ∀ α : ℝ, ((‖expSum N a α‖ ^ 2 : ℝ) : ℂ)
      = expSum N a α * (starRingEnd ℂ) (expSum N a α) := by
    intro α
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- Pointwise: expand the square of the sum into the double sum.
  have expand : ∀ α : ℝ, expSum N a α * (starRingEnd ℂ) (expSum N a α)
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (a n * (starRingEnd ℂ) (a m))
            * (e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α))) := by
    intro α
    unfold expSum
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro n _
    apply Finset.sum_congr rfl; intro m _
    rw [map_mul]; ring
  -- Continuity of the individual and inner-summed terms (for integrability).
  have cont2 : ∀ n ∈ Finset.range N, ∀ m ∈ Finset.range N,
      Continuous (fun α : ℝ => (a n * (starRingEnd ℂ) (a m))
        * (e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α)))) := by
    intro n _ m _; fun_prop
  have cont1 : ∀ n ∈ Finset.range N,
      Continuous (fun α : ℝ => ∑ m ∈ Finset.range N,
        (a n * (starRingEnd ℂ) (a m))
          * (e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α)))) := by
    intro n hn
    apply continuous_finsetSum
    intro m hm
    exact cont2 n hn m hm
  -- Prove the ℂ-cast identity, then descend to ℝ.
  have key : ((∫ α in (0:ℝ)..1, ‖expSum N a α‖ ^ 2 : ℝ) : ℂ)
      = ((∑ n ∈ Finset.range N, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    calc (∫ α in (0:ℝ)..1, ((‖expSum N a α‖ ^ 2 : ℝ) : ℂ))
        = ∫ α in (0:ℝ)..1, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
            (a n * (starRingEnd ℂ) (a m))
              * (e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α))) := by
          simp_rw [pt, expand]
      _ = ∑ n ∈ Finset.range N, ∫ α in (0:ℝ)..1, ∑ m ∈ Finset.range N,
            (a n * (starRingEnd ℂ) (a m))
              * (e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α))) := by
          rw [intervalIntegral.integral_finsetSum]
          intro n hn; exact (cont1 n hn).intervalIntegrable 0 1
      _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∫ α in (0:ℝ)..1,
            (a n * (starRingEnd ℂ) (a m))
              * (e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α))) := by
          apply Finset.sum_congr rfl; intro n _
          rw [intervalIntegral.integral_finsetSum]
          intro m hm; exact (cont2 n (by assumption) m hm).intervalIntegrable 0 1
      _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
            (a n * (starRingEnd ℂ) (a m)) * (if n = m then 1 else 0) := by
          apply Finset.sum_congr rfl; intro n _
          apply Finset.sum_congr rfl; intro m _
          rw [intervalIntegral.integral_const_mul, integral_e_mul_conj]
      _ = ∑ n ∈ Finset.range N, a n * (starRingEnd ℂ) (a n) := by
          apply Finset.sum_congr rfl; intro n hn
          rw [Finset.sum_eq_single n]
          · rw [if_pos rfl, mul_one]
          · intro m _ hmn; rw [if_neg (fun h => hmn h.symm), mul_zero]
          · intro hn'; exact absurd hn hn'
      _ = ((∑ n ∈ Finset.range N, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
          apply Finset.sum_congr rfl; intro n _
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast key

end Salt.LS

-- ==== upstream: Salt/LS/Deriv.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Large sieve track, nodes L2.1 + L2.2: the derivative of `expSum` and its Parseval bound

Blueprint: `docs/blueprints/largesieve.md`.

* **L2.1** — the derivative of the exponential polynomial is again an exponential
  polynomial, with the frequency `n` folded into the coefficient:
  `deriv (expSum N a) α = expSum N (fun n => 2πi·n · a n) α`
  (`deriv_expSum`), packaged as a global `HasDerivAt` (`hasDerivAt_expSum`) and a
  global `ContDiff ℝ 1` statement (`contDiff_expSum`) for feeding
  `gallagher_pointwise`.
* **L2.2** — the derivative Parseval + crude `n ≤ N` bound:
  `∫₀¹ ‖deriv (expSum N a)‖² ≤ (2πN)² · Σ ‖aₙ‖²` (`integral_norm_deriv_sq_le`).

The derivative identity is obtained termwise: each summand
`a n · e(nα) = a n · exp((2πi·n)·α)` has derivative `2πi·n · a n · e(nα)` by the
chain rule (`HasDerivAt.cexp`); `HasDerivAt.sum` assembles the finite sum. The
L2.2 bound then rewrites the derivative back into `expSum` form, applies the
landed `parseval`, and estimates `‖2πi·n·aₙ‖² = 4π²n²‖aₙ‖² ≤ 4π²N²‖aₙ‖²`.
-/

namespace Salt.LS

open scoped BigOperators
open Complex MeasureTheory

/-- The frequency-twisted coefficient sequence `n ↦ 2πi·n · a n`; `deriv (expSum N a)`
is `expSum N` of this sequence (L2.1). -/
noncomputable def twist (a : ℕ → ℂ) (n : ℕ) : ℂ := 2 * Real.pi * Complex.I * (n : ℂ) * a n

/-- Termwise derivative: `d/dα [a n · e(nα)] = (2πi·n · a n) · e(nα)`. -/
lemma hasDerivAt_expSum_term (a : ℕ → ℂ) (n : ℕ) (α : ℝ) :
    HasDerivAt (fun α : ℝ => a n * e ((n : ℝ) * α)) (twist a n * e ((n : ℝ) * α)) α := by
  set C : ℂ := 2 * Real.pi * Complex.I * (n : ℂ) with hCdef
  have hval : e ((n : ℝ) * α) = Complex.exp (C * (α : ℂ)) := by
    unfold e; rw [hCdef]; push_cast; ring_nf
  have hfun : (fun α : ℝ => e ((n : ℝ) * α)) = fun α : ℝ => Complex.exp (C * (α : ℂ)) := by
    funext β; unfold e; rw [hCdef]; push_cast; ring_nf
  have h1 : HasDerivAt (fun α : ℝ => ((α : ℂ))) 1 α := by
    simpa using (hasDerivAt_id α).ofReal_comp
  have h2 : HasDerivAt (fun α : ℝ => C * (α : ℂ)) (C * 1) α := h1.const_mul _
  have h3 : HasDerivAt (fun α : ℝ => Complex.exp (C * (α : ℂ)))
      (Complex.exp (C * (α : ℂ)) * (C * 1)) α := h2.cexp
  have he : HasDerivAt (fun α : ℝ => e ((n : ℝ) * α)) (C * e ((n : ℝ) * α)) α := by
    rw [hfun, hval]; convert h3 using 1; ring
  have hmul := he.const_mul (a n)
  have hval2 : a n * (C * e ((n : ℝ) * α)) = twist a n * e ((n : ℝ) * α) := by
    rw [hCdef, twist]; ring
  rw [hval2] at hmul
  exact hmul

/-- **L2.1 (HasDerivAt form).** `expSum N a` is differentiable with derivative the
frequency-twisted exponential polynomial `expSum N (twist a)`. -/
theorem hasDerivAt_expSum (N : ℕ) (a : ℕ → ℂ) (α : ℝ) :
    HasDerivAt (expSum N a) (expSum N (twist a) α) α := by
  have h := HasDerivAt.sum (u := Finset.range N)
    (A := fun n => fun α : ℝ => a n * e ((n : ℝ) * α))
    (A' := fun n => twist a n * e ((n : ℝ) * α))
    (fun n _ => hasDerivAt_expSum_term a n α)
  have hfun : expSum N a = ∑ n ∈ Finset.range N, fun α : ℝ => a n * e ((n : ℝ) * α) := by
    funext α; rw [Finset.sum_apply]; rfl
  rw [hfun]
  exact h

/-- **L2.1 (deriv form).** The pointwise derivative identity. -/
theorem deriv_expSum (N : ℕ) (a : ℕ → ℂ) (α : ℝ) :
    deriv (expSum N a) α = expSum N (twist a) α :=
  (hasDerivAt_expSum N a α).deriv

/-- Each summand `a n · e(nα)` is `C¹` (indeed smooth). -/
lemma contDiff_expSum_term (a : ℕ → ℂ) (n : ℕ) :
    ContDiff ℝ 1 (fun α : ℝ => a n * e ((n : ℝ) * α)) := by
  have hfun : (fun α : ℝ => a n * e ((n : ℝ) * α))
      = fun α : ℝ => a n * Complex.exp ((2 * Real.pi * Complex.I * (n : ℂ)) * (α : ℂ)) := by
    funext β; unfold e; push_cast; ring_nf
  rw [hfun]
  have hof : ContDiff ℝ 1 (fun α : ℝ => (α : ℂ)) := Complex.ofRealCLM.contDiff
  exact contDiff_const.mul ((Complex.contDiff_exp).comp (contDiff_const.mul hof))

/-- **L2.1 (ContDiff form).** `expSum N a` is globally `C¹` — the hypothesis
`gallagher_pointwise` consumes. -/
theorem contDiff_expSum (N : ℕ) (a : ℕ → ℂ) : ContDiff ℝ 1 (expSum N a) := by
  unfold expSum
  exact ContDiff.sum (fun n _ => contDiff_expSum_term a n)

/-- `deriv (expSum N a)` is continuous (it is again an `expSum`). -/
lemma continuous_deriv_expSum (N : ℕ) (a : ℕ → ℂ) :
    Continuous (deriv (expSum N a)) := by
  have : deriv (expSum N a) = expSum N (twist a) := by
    funext α; exact deriv_expSum N a α
  rw [this]; exact continuous_expSum N (twist a)

/-- `‖twist a n‖² = 4π²·n²·‖a n‖²`. -/
lemma norm_twist_sq (a : ℕ → ℂ) (n : ℕ) :
    ‖twist a n‖ ^ 2 = 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 * ‖a n‖ ^ 2 := by
  unfold twist
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  rw [show ‖(2 : ℂ)‖ = 2 from by norm_num, Complex.norm_real, Complex.norm_I,
    Complex.norm_natCast, Real.norm_of_nonneg Real.pi_pos.le]
  ring

/-- **L2.2 — derivative Parseval + crude `n ≤ N` bound (FROZEN shape).**
`∫₀¹ ‖deriv (expSum N a)‖² ≤ (2πN)² · Σ ‖aₙ‖²`. -/
theorem integral_norm_deriv_sq_le (N : ℕ) (a : ℕ → ℂ) :
    (∫ α in (0:ℝ)..1, ‖deriv (expSum N a) α‖ ^ 2)
      ≤ (2 * Real.pi * N) ^ 2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  have hrw : (∫ α in (0:ℝ)..1, ‖deriv (expSum N a) α‖ ^ 2)
      = ∑ n ∈ Finset.range N, ‖twist a n‖ ^ 2 := by
    rw [show (fun α => ‖deriv (expSum N a) α‖ ^ 2)
          = (fun α => ‖expSum N (twist a) α‖ ^ 2) from by
        funext α; rw [deriv_expSum]]
    exact parseval N (twist a)
  rw [hrw]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_twist_sq]
  have hnN : (n : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Finset.mem_range.mp hn).le
  have hsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    nlinarith [hnN, Nat.cast_nonneg (α := ℝ) n]
  have hcoef : 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 ≤ (2 * Real.pi * N) ^ 2 := by
    have hexp : (2 * Real.pi * N) ^ 2 = 4 * Real.pi ^ 2 * (N : ℝ) ^ 2 := by ring
    rw [hexp]
    nlinarith [hsq, Real.pi_pos, sq_nonneg Real.pi]
  calc 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 * ‖a n‖ ^ 2
      ≤ (2 * Real.pi * N) ^ 2 * ‖a n‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right hcoef (by positivity)

end Salt.LS

-- ==== upstream: Salt/LS/Dist.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# L0.2 — the mod-1 circle distance `dist₁`

Design: `docs/blueprints/largesieve.md`, "Carrier choices" and node `L0.2`.

`dist₁ x y` is the distance from `x - y` to the nearest integer, i.e. the
distance between `x` and `y` on the circle `ℝ / ℤ`. We implement it via
mathlib's `round` function rather than the `AddCircle` norm: `AddCircle`
carries its own quotient-type coercions (`UnitAddCircle.norm_eq` unfolds to
exactly `|x - round x|`, but only after passing through `(· : UnitAddCircle)`),
whereas the spec lemmas below all consume `x y : ℝ` directly, so the bare
`round`-based definition avoids coercion overhead. The key mathlib facts
driving every lemma here are `abs_sub_round` (`|t - round t| ≤ 1/2`) and
`round_le` (`round` minimizes `|t - m|` over `m : ℤ`, i.e.
`|t - round t| ≤ |t - m|` for every integer `m`).
-/

namespace Salt.LS

/-- The mod-1 circle distance: the distance from `x - y` to the nearest
integer. -/
noncomputable def dist₁ (x y : ℝ) : ℝ := |x - y - round (x - y)|

@[simp]
theorem dist₁_self (x : ℝ) : dist₁ x x = 0 := by simp [dist₁]

theorem dist₁_nonneg (x y : ℝ) : 0 ≤ dist₁ x y := abs_nonneg _

theorem dist₁_le_half (x y : ℝ) : dist₁ x y ≤ 1 / 2 := abs_sub_round (x - y)

theorem dist₁_le_abs (x y : ℝ) : dist₁ x y ≤ |x - y| := by
  unfold dist₁
  simpa using round_le (x - y) 0

theorem dist₁_comm (x y : ℝ) : dist₁ x y = dist₁ y x := by
  have h1 : dist₁ x y ≤ dist₁ y x := by
    have := round_le (x - y) (-round (y - x))
    have he : x - y - ((-round (y - x) : ℤ) : ℝ) = -(y - x - round (y - x)) := by
      push_cast; ring
    rw [he, abs_neg] at this
    exact this
  have h2 : dist₁ y x ≤ dist₁ x y := by
    have := round_le (y - x) (-round (x - y))
    have he : y - x - ((-round (x - y) : ℤ) : ℝ) = -(x - y - round (x - y)) := by
      push_cast; ring
    rw [he, abs_neg] at this
    exact this
  exact le_antisymm h1 h2

theorem dist₁_add_int_left (x y : ℝ) (n : ℤ) : dist₁ (x + n) y = dist₁ x y := by
  unfold dist₁
  have hxy : x + (n : ℝ) - y = (x - y) + (n : ℝ) := by ring
  rw [hxy, round_add_intCast]
  congr 1
  push_cast
  ring

theorem dist₁_add_int_right (x y : ℝ) (n : ℤ) : dist₁ x (y + n) = dist₁ x y := by
  rw [dist₁_comm x (y + n), dist₁_add_int_left y x n, dist₁_comm]

theorem dist₁_triangle (x y z : ℝ) : dist₁ x z ≤ dist₁ x y + dist₁ y z := by
  unfold dist₁
  have h1 : |x - z - round (x - z)|
      ≤ |x - z - ((round (x - y) + round (y - z) : ℤ) : ℝ)| :=
    round_le (x - z) (round (x - y) + round (y - z))
  have h2 : x - z - ((round (x - y) + round (y - z) : ℤ) : ℝ)
      = (x - y - round (x - y)) + (y - z - round (y - z)) := by push_cast; ring
  calc |x - z - round (x - z)|
      ≤ |x - z - ((round (x - y) + round (y - z) : ℤ) : ℝ)| := h1
    _ = |(x - y - round (x - y)) + (y - z - round (y - z))| := by rw [h2]
    _ ≤ |x - y - round (x - y)| + |y - z - round (y - z)| := abs_add_le _ _

theorem dist₁_eq_zero_iff (x y : ℝ) : dist₁ x y = 0 ↔ ∃ n : ℤ, x - y = n := by
  unfold dist₁
  rw [abs_eq_zero, sub_eq_zero]
  constructor
  · intro h
    exact ⟨round (x - y), h⟩
  · rintro ⟨n, hn⟩
    rw [hn, round_intCast]

end Salt.LS

-- ==== upstream: Salt/LS/Spacing.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Large sieve track, nodes L5.1 + L5.2 (fused): periodic unfolding of δ-spaced windows

Blueprint: `docs/blueprints/largesieve.md`.

* `Spaced δ α` — the frozen carrier: the points `α : Fin R → ℝ` are `δ`-separated
  on the circle `ℝ/ℤ` (`∀ r s, r ≠ s → δ ≤ dist₁ (α r) (α s)`).
* **L5.1 + L5.2** (`sum_integral_le_period`): for a nonnegative, continuous,
  1-periodic `g : ℝ → ℝ` and a `δ`-spaced system with `0 < δ ≤ 1/2`,
  `∑ r, ∫_{α r − δ/2}^{α r + δ/2} g ≤ ∫₀¹ g`.

Route (no sorting): reduce each center to `β r = Int.fract (α r) ∈ [0,1)` (the
integral is unchanged by the integer shift, since `g` is 1-periodic). The reduced
half-open intervals `Ioc (β r − δ/2) (β r + δ/2)` are **pairwise disjoint** (an
overlap forces `|β r − β s| < δ` hence `dist₁ (β r) (β s) < δ`, contradicting
spacing) and all sit inside the length-1 window `Ioc a (a+1)` where
`a = (min_r β r) − δ/2` (the left ends dominate `a`; the right ends are bounded by
`a+1` via the wraparound gap `dist₁ ≤ |β r − β_min − 1|`). A disjoint-union
integral plus monotonicity (`g ≥ 0`) and one periodic window shift finish it.
-/

namespace Salt.LS

open scoped BigOperators
open MeasureTheory intervalIntegral Set

/-- **Carrier (Fable-frozen).** `α : Fin R → ℝ` is `δ`-spaced on the circle. -/
def Spaced {R : ℕ} (δ : ℝ) (α : Fin R → ℝ) : Prop :=
  ∀ r s, r ≠ s → δ ≤ dist₁ (α r) (α s)

/-- `g (t + n) = g t` for integer `n`, from 1-periodicity. -/
theorem periodic_add_int {g : ℝ → ℝ} (hper : ∀ x, g (x + 1) = g x) (n : ℤ) (t : ℝ) :
    g (t + (n : ℝ)) = g t := by
  refine Int.induction_on n ?_ ?_ ?_
  · simp
  · intro k ih
    push_cast at ih ⊢
    rw [show t + ((k : ℝ) + 1) = (t + (k : ℝ)) + 1 by ring, hper]
    exact ih
  · intro k ih
    push_cast at ih ⊢
    have hh := hper (t + (-(k : ℝ)) - 1)
    rw [show t + (-(k : ℝ)) - 1 + 1 = t + (-(k : ℝ)) by ring] at hh
    rw [show t + (-(k : ℝ) - 1) = t + (-(k : ℝ)) - 1 by ring, ← hh]
    exact ih

/-- Interval integral of a 1-periodic function is invariant under an integer shift
of both endpoints. -/
theorem intervalIntegral_add_intCast {g : ℝ → ℝ} (hper : ∀ x, g (x + 1) = g x)
    (n : ℤ) (x y : ℝ) :
    (∫ t in (x + (n : ℝ))..(y + (n : ℝ)), g t) = ∫ t in x..y, g t := by
  rw [← intervalIntegral.integral_comp_add_right g (n : ℝ)]
  exact intervalIntegral.integral_congr (fun t _ => periodic_add_int hper n t)

/-- `dist₁` is invariant under reducing both arguments mod 1 via `Int.fract`. -/
theorem dist₁_fract (x y : ℝ) : dist₁ (Int.fract x) (Int.fract y) = dist₁ x y := by
  have hx : Int.fract x = x + ((-⌊x⌋ : ℤ) : ℝ) := by
    have h := Int.fract_add_floor x; push_cast; linarith
  have hy : Int.fract y = y + ((-⌊y⌋ : ℤ) : ℝ) := by
    have h := Int.fract_add_floor y; push_cast; linarith
  rw [hx, hy, dist₁_add_int_left, dist₁_add_int_right]

/-- `dist₁ x y` underestimates the distance from `x − y` to any integer. -/
theorem dist₁_le_sub_int (x y : ℝ) (k : ℤ) : dist₁ x y ≤ |x - y - (k : ℝ)| := by
  unfold dist₁
  exact round_le (x - y) k

/-- **L5.1 + L5.2 (fused) — periodic unfolding (CONSUMER-FROZEN).** -/
theorem sum_integral_le_period {R : ℕ} {δ : ℝ} {α : Fin R → ℝ} (g : ℝ → ℝ)
    (hper : ∀ x, g (x + 1) = g x) (hg : ∀ x, 0 ≤ g x) (hcont : Continuous g)
    (hsp : Spaced δ α) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), g t ≤ ∫ t in (0:ℝ)..1, g t := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => hg t)
  -- The reduced centers.
  set β : Fin R → ℝ := fun r => Int.fract (α r) with hβ
  have hβr : ∀ r, β r = Int.fract (α r) := fun r => rfl
  have hβ_nonneg : ∀ r, 0 ≤ β r := fun r => by rw [hβr]; exact Int.fract_nonneg _
  have hβ_lt : ∀ r, β r < 1 := fun r => by rw [hβr]; exact Int.fract_lt_one _
  -- The window base point `a = (min β) − δ/2`.
  have hne : (Finset.univ : Finset (Fin R)).Nonempty := ⟨⟨0, hR⟩, Finset.mem_univ _⟩
  obtain ⟨r₀, -, hm0⟩ := Finset.exists_mem_eq_inf' hne β
  set m : ℝ := Finset.univ.inf' hne β with hm
  set a : ℝ := m - δ / 2 with ha
  have hm_le : ∀ r, m ≤ β r := fun r => Finset.inf'_le β (Finset.mem_univ r)
  have hm_nonneg : 0 ≤ m := by rw [hm0]; exact hβ_nonneg r₀
  -- Step 1: reduce each interval to the β-window.
  have hstep1 : ∀ r, (∫ t in (α r - δ / 2)..(α r + δ / 2), g t)
      = ∫ t in (β r - δ / 2)..(β r + δ / 2), g t := by
    intro r
    have hfr := Int.fract_add_floor (α r)
    have e1 : α r - δ / 2 = (β r - δ / 2) + ((⌊α r⌋ : ℤ) : ℝ) := by rw [hβr]; linarith
    have e2 : α r + δ / 2 = (β r + δ / 2) + ((⌊α r⌋ : ℤ) : ℝ) := by rw [hβr]; linarith
    rw [e1, e2, intervalIntegral_add_intCast hper ⌊α r⌋]
  -- Step 2: interval integral = set integral over Ioc.
  have hle_int : ∀ r, β r - δ / 2 ≤ β r + δ / 2 := fun r => by linarith
  have hstep2 : ∀ r, (∫ t in (β r - δ / 2)..(β r + δ / 2), g t)
      = ∫ t in Ioc (β r - δ / 2) (β r + δ / 2), g t := fun r =>
    intervalIntegral.integral_of_le (hle_int r)
  -- Disjointness of the reduced intervals.
  have hdisj : Pairwise (Function.onFun Disjoint (fun r => Ioc (β r - δ / 2) (β r + δ / 2))) := by
    intro r s hrs
    rw [Function.onFun, Set.disjoint_left]
    intro x hxr hxs
    have habs : |β r - β s| < δ := by
      rw [abs_lt]
      exact ⟨by have := hxs.1; have := hxr.2; linarith,
             by have := hxr.1; have := hxs.2; linarith⟩
    have hd1 : dist₁ (β r) (β s) < δ := lt_of_le_of_lt (dist₁_le_abs _ _) habs
    have heq : dist₁ (β r) (β s) = dist₁ (α r) (α s) := by rw [hβr, hβr]; exact dist₁_fract _ _
    have := hsp r s hrs
    linarith [heq ▸ hd1]
  -- Containment: each reduced interval sits inside `Ioc a (a+1)`.
  have hsub : ∀ r, Ioc (β r - δ / 2) (β r + δ / 2) ⊆ Ioc a (a + 1) := by
    intro r
    have hbr : β r ≤ m + 1 - δ := by
      by_cases hr : r = r₀
      · subst hr; rw [← hm0]; linarith
      · have hβr0 : β r₀ = m := hm0.symm
        have hd : δ ≤ dist₁ (β r) (β r₀) := by
          rw [hβr, hβr, dist₁_fract]; exact hsp r r₀ hr
        have hle : dist₁ (β r) (β r₀) ≤ |β r - β r₀ - 1| := by
          simpa using dist₁_le_sub_int (β r) (β r₀) 1
        have hneg : β r - β r₀ - 1 ≤ 0 := by
          rw [hβr0]; have := hβ_lt r; linarith [hm_nonneg]
        rw [abs_of_nonpos hneg] at hle
        have hcomb : δ ≤ -(β r - β r₀ - 1) := le_trans hd hle
        rw [hβr0] at hcomb
        linarith
    apply Ioc_subset_Ioc
    · rw [ha]; linarith [hm_le r]
    · rw [ha]; linarith
  -- Integrability of `g` on the window and its subunion.
  have hint_win : IntegrableOn g (Ioc a (a + 1)) := hcont.integrableOn_Ioc
  have hint_union : IntegrableOn g (⋃ r, Ioc (β r - δ / 2) (β r + δ / 2)) :=
    hint_win.mono_set (iUnion_subset hsub)
  -- Assemble.
  calc ∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), g t
      = ∑ r, ∫ t in Ioc (β r - δ / 2) (β r + δ / 2), g t := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [hstep1 r, hstep2 r]
    _ = ∫ t in ⋃ r, Ioc (β r - δ / 2) (β r + δ / 2), g t := by
        rw [MeasureTheory.integral_iUnion (fun r => measurableSet_Ioc) hdisj hint_union,
          tsum_fintype]
    _ ≤ ∫ t in Ioc a (a + 1), g t := by
        refine setIntegral_mono_set hint_win ?_ (iUnion_subset hsub).eventuallyLE
        exact Filter.Eventually.of_forall (fun t => hg t)
    _ = ∫ t in a..(a + 1), g t := (intervalIntegral.integral_of_le (by linarith)).symm
    _ = ∫ t in (0:ℝ)..1, g t := by
        have hp : Function.Periodic g 1 := hper
        simpa using hp.intervalIntegral_add_eq a 0

end Salt.LS

-- ==== upstream: Salt/LS/Gallagher.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Large sieve track, node L4.1: the Sobolev/Gallagher pointwise lemma

Blueprint: `docs/blueprints/largesieve.md`.

**L4.1** (`gallagher_pointwise`): for `f : ℝ → ℂ` with a continuous derivative
and `0 < δ`, the pointwise Sobolev bound
`‖f t₀‖² ≤ δ⁻¹ · ∫_I ‖f‖² + 2 · ∫_I ‖f‖·‖f'‖`,
where `I = [t₀ − δ/2, t₀ + δ/2]`. The constant `2` is frozen (doctrine: a
constant-factor bound is all the large sieve consumes).

Hypothesis-form choice (per blueprint latitude): `ContDiff ℝ 1 f` **globally**,
rather than the interval-local `HasDerivAt` hypotheses. Doctrine ratifies this
because the W2 consumer (`expSum`) is entire, so a global `C¹` hypothesis costs
nothing downstream and keeps this proof free of `…WithinAt` bookkeeping.

Proof: with `g s = ‖f s‖²`, `HasDerivAt.norm_sq` gives `g' s = 2⟪f s, f' s⟫`
and Cauchy–Schwarz gives `|g' s| ≤ 2‖f s‖‖f' s‖`. FTC-2 turns `g t₀ − g u` into
`∫_u^{t₀} g'`, which is `≤ ∫_I 2‖f‖‖f'‖` for every `u ∈ I` (bound the interval
integral by the norm integral over `Ι u t₀ ⊆ I`). Integrating
`g t₀ ≤ g u + ∫_I 2‖f‖‖f'‖` over `u ∈ I` (length `δ`) and dividing by `δ` closes it.
-/

namespace Salt.LS

open MeasureTheory intervalIntegral Set

/-- **L4.1 — Gallagher pointwise lemma (FROZEN).** For a globally `C¹` function
`f : ℝ → ℂ` and `0 < δ`, writing `I = [t₀ − δ/2, t₀ + δ/2]`,
`‖f t₀‖² ≤ δ⁻¹ · ∫_I ‖f‖² + 2 · ∫_I ‖f‖·‖f'‖`. -/
theorem gallagher_pointwise {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) {δ : ℝ} (hδ : 0 < δ)
    (t₀ : ℝ) :
    ‖f t₀‖ ^ 2
      ≤ δ⁻¹ * (∫ t in (t₀ - δ / 2)..(t₀ + δ / 2), ‖f t‖ ^ 2)
        + 2 * ∫ t in (t₀ - δ / 2)..(t₀ + δ / 2), ‖f t‖ * ‖deriv f t‖ := by
  set c := t₀ - δ / 2 with hc_def
  set d := t₀ + δ / 2 with hd_def
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hcd : c ≤ d := by rw [hc_def, hd_def]; linarith
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hcont_f : Continuous f := hf.continuous
  have hcont_df : Continuous (deriv f) := hf.continuous_deriv_one
  -- derivative of `‖f ·‖²` and continuity of the two integrands
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun t => ‖f t‖ ^ 2) (2 * inner ℝ (f s) (deriv f s)) s :=
    fun s => (hdiff s).hasDerivAt.norm_sq
  have hcont_g : Continuous (fun s : ℝ => 2 * inner ℝ (f s) (deriv f s)) := by fun_prop
  have hcont_k : Continuous (fun s : ℝ => 2 * (‖f s‖ * ‖deriv f s‖)) := by fun_prop
  -- Cauchy–Schwarz: `‖g' s‖ ≤ 2‖f s‖‖f' s‖`.
  have hCS : ∀ s : ℝ, ‖2 * inner ℝ (f s) (deriv f s)‖ ≤ 2 * (‖f s‖ * ‖deriv f s‖) := by
    intro s
    rw [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    have := abs_real_inner_le_norm (f s) (deriv f s)
    linarith
  set K := ∫ s in c..d, 2 * (‖f s‖ * ‖deriv f s‖) with hK_def
  -- The core one-sided bound for each `u ∈ I`.
  have core : ∀ u ∈ Icc c d, ‖f t₀‖ ^ 2 - ‖f u‖ ^ 2 ≤ K := by
    intro u hu
    have ht₀ : t₀ ∈ Icc c d := ⟨by rw [hc_def]; linarith, by rw [hd_def]; linarith⟩
    have hFTC : (∫ s in u..t₀, 2 * inner ℝ (f s) (deriv f s)) = ‖f t₀‖ ^ 2 - ‖f u‖ ^ 2 :=
      integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) (hcont_g.intervalIntegrable u t₀)
    have hsub : Set.uIoc u t₀ ⊆ Icc c d :=
      Set.Ioc_subset_Icc_self.trans
        (Set.Icc_subset_Icc (le_inf hu.1 ht₀.1) (sup_le hu.2 ht₀.2))
    rw [← hFTC]
    calc (∫ s in u..t₀, 2 * inner ℝ (f s) (deriv f s))
        ≤ ‖∫ s in u..t₀, 2 * inner ℝ (f s) (deriv f s)‖ := Real.le_norm_self _
      _ ≤ ∫ s in Set.uIoc u t₀, ‖2 * inner ℝ (f s) (deriv f s)‖ :=
          norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ s in Set.uIoc u t₀, 2 * (‖f s‖ * ‖deriv f s‖) :=
          setIntegral_mono_on hcont_g.norm.integrableOn_uIoc hcont_k.integrableOn_uIoc
            measurableSet_uIoc (fun s _ => hCS s)
      _ ≤ ∫ s in Icc c d, 2 * (‖f s‖ * ‖deriv f s‖) :=
          setIntegral_mono_set hcont_k.integrableOn_Icc
            (Filter.Eventually.of_forall (fun s => by positivity)) hsub.eventuallyLE
      _ = K := by
          rw [hK_def, MeasureTheory.integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le hcd]
  -- Integrate `‖f t₀‖² ≤ ‖f u‖² + K` over `u ∈ I` (length `δ`).
  have hintegrated : δ * ‖f t₀‖ ^ 2 ≤ (∫ u in c..d, ‖f u‖ ^ 2) + δ * K := by
    have hii : IntervalIntegrable (fun u => ‖f u‖ ^ 2) volume c d :=
      (hcont_f.norm.pow 2).intervalIntegrable c d
    have hle : (∫ _u in c..d, ‖f t₀‖ ^ 2) ≤ ∫ u in c..d, (‖f u‖ ^ 2 + K) :=
      intervalIntegral.integral_mono_on hcd intervalIntegrable_const
        (hii.add intervalIntegrable_const)
        (fun u hu => by have := core u hu; linarith)
    rw [intervalIntegral.integral_add hii intervalIntegrable_const] at hle
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hle
    rw [show d - c = δ from by rw [hc_def, hd_def]; ring] at hle
    exact hle
  -- `K = 2 · ∫_I ‖f‖·‖f'‖`, then divide the integrated bound by `δ`.
  have hK : K = 2 * ∫ t in c..d, ‖f t‖ * ‖deriv f t‖ := by
    rw [hK_def, intervalIntegral.integral_const_mul]
  rw [hK] at hintegrated
  have hinv : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ
  have key2 : ‖f t₀‖ ^ 2 ≤ δ⁻¹ * (δ * ‖f t₀‖ ^ 2) := by
    rw [← mul_assoc, inv_mul_cancel₀ hδ0, one_mul]
  refine key2.trans ?_
  calc δ⁻¹ * (δ * ‖f t₀‖ ^ 2)
      ≤ δ⁻¹ * ((∫ u in c..d, ‖f u‖ ^ 2) + δ * (2 * ∫ t in c..d, ‖f t‖ * ‖deriv f t‖)) :=
        mul_le_mul_of_nonneg_left hintegrated (le_of_lt hinv)
    _ = δ⁻¹ * (∫ t in c..d, ‖f t‖ ^ 2) + 2 * ∫ t in c..d, ‖f t‖ * ‖deriv f t‖ := by
        rw [mul_add]
        congr 1
        rw [← mul_assoc, inv_mul_cancel₀ hδ0, one_mul]

end Salt.LS

-- ==== upstream: Salt/LS/AnalyticLS.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/



/-!
# Large sieve track, node L3.1: the analytic large sieve

Blueprint: `docs/blueprints/largesieve.md`.

**L3.1** (`analytic_LS`, FROZEN): for a `δ`-spaced system `α : Fin R → ℝ` with
`0 < δ ≤ 1/2`,
`∑ r, ‖expSum N a (α r)‖² ≤ (δ⁻¹ + 13·N) · ∑_{n<N} ‖aₙ‖²`.

Assembly (all inputs are landed W1/W2 nodes):
* `gallagher_pointwise` (L4.1) at `f := expSum N a` for each `r`, using
  `contDiff_expSum` (L2.1);
* sum over `r` and push the two integral families through
  `sum_integral_le_period` (L5) — both `‖expSum·‖²` and `‖expSum·‖·‖deriv·‖`
  are 1-periodic (from `expSum_add_one`), nonnegative, continuous;
* `parseval` (L1.2) evaluates `∫₀¹ ‖expSum‖² = P`;
* the cross term is closed with an **elementary Young inequality**
  `2xy ≤ 5N·x² + y²/(5N)` (integrated form `10N·∫xy ≤ 25N²·∫x² + ∫y²`), the
  derivative Parseval bound `∫₀¹ ‖deriv‖² ≤ (2πN)²P` (L2.2), and `π² ≤ 10`
  (`Real.pi_lt_d2`), giving `2·∫₀¹ ‖expSum‖·‖deriv‖ ≤ 13N·P` (`25 + 4π² ≤ 65`).
No Cauchy–Schwarz/`rpow` needed; the frozen constant `13 ≥ 4π` absorbs the slack.
-/

namespace Salt.LS

open scoped BigOperators
open MeasureTheory intervalIntegral Complex

/-- `e(n) = 1` for a natural number `n`. -/
lemma e_natCast (n : ℕ) : e (n : ℝ) = 1 := by
  have h : e ((n : ℝ)) = Complex.exp (((n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    unfold e; push_cast; ring_nf
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- `expSum N a` is 1-periodic. -/
lemma expSum_add_one (N : ℕ) (a : ℕ → ℂ) (α : ℝ) :
    expSum N a (α + 1) = expSum N a α := by
  unfold expSum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [show (n : ℝ) * (α + 1) = (n : ℝ) * α + (n : ℝ) from by ring, e_add, e_natCast, mul_one]

/-- `deriv (expSum N a)` is 1-periodic. -/
lemma deriv_expSum_add_one (N : ℕ) (a : ℕ → ℂ) (α : ℝ) :
    deriv (expSum N a) (α + 1) = deriv (expSum N a) α := by
  rw [deriv_expSum, deriv_expSum]
  exact expSum_add_one N (twist a) α

/-- **L3.1 — analytic large sieve (FROZEN).** -/
theorem analytic_LS {R N : ℕ} {δ : ℝ} {α : Fin R → ℝ} (a : ℕ → ℂ)
    (hsp : Spaced δ α) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∑ r, ‖expSum N a (α r)‖ ^ 2 ≤ (δ⁻¹ + 13 * N) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [expSum]
  -- N ≥ 1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set P : ℝ := ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 with hP
  have hP_nonneg : 0 ≤ P := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  set S : ℝ → ℂ := expSum N a with hS
  have hcontS : Continuous S := continuous_expSum N a
  have hcontDS : Continuous (deriv S) := continuous_deriv_expSum N a
  have hC1 : ContDiff ℝ 1 S := contDiff_expSum N a
  -- periodicity / nonnegativity / continuity of the two integrand families
  have hg1_per : ∀ x, ‖S (x + 1)‖ ^ 2 = ‖S x‖ ^ 2 := by
    intro x; simp only [hS, expSum_add_one]
  have hg1_nonneg : ∀ x, 0 ≤ ‖S x‖ ^ 2 := fun x => sq_nonneg _
  have hg1_cont : Continuous (fun t => ‖S t‖ ^ 2) := hcontS.norm.pow 2
  have hg2_per : ∀ x, ‖S (x + 1)‖ * ‖deriv S (x + 1)‖ = ‖S x‖ * ‖deriv S x‖ := by
    intro x; simp only [hS]; rw [expSum_add_one, deriv_expSum_add_one]
  have hg2_nonneg : ∀ x, 0 ≤ ‖S x‖ * ‖deriv S x‖ := fun x => by positivity
  have hg2_cont : Continuous (fun t => ‖S t‖ * ‖deriv S t‖) := hcontS.norm.mul hcontDS.norm
  -- Gallagher, summed
  have hgall : ∀ r, ‖S (α r)‖ ^ 2 ≤
      δ⁻¹ * (∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2)
        + 2 * ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖deriv S t‖ :=
    fun r => gallagher_pointwise hC1 hδ (α r)
  -- periodic unfolding (L5), twice
  have hper1 : (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2)
      ≤ ∫ t in (0:ℝ)..1, ‖S t‖ ^ 2 :=
    sum_integral_le_period (fun t => ‖S t‖ ^ 2) hg1_per hg1_nonneg hg1_cont hsp hδ hδ2
  set G : ℝ := ∫ t in (0:ℝ)..1, ‖S t‖ * ‖deriv S t‖ with hG
  have hper2 : (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖deriv S t‖) ≤ G :=
    sum_integral_le_period (fun t => ‖S t‖ * ‖deriv S t‖) hg2_per hg2_nonneg hg2_cont hsp hδ hδ2
  -- Parseval and derivative Parseval
  have hparse : (∫ t in (0:ℝ)..1, ‖S t‖ ^ 2) = P := by rw [hS, hP]; exact parseval N a
  have hL22 : (∫ t in (0:ℝ)..1, ‖deriv S t‖ ^ 2) ≤ (2 * Real.pi * N) ^ 2 * P := by
    rw [hS, hP]; exact integral_norm_deriv_sq_le N a
  -- Young inequality, integrated
  have hcont_x2 : Continuous (fun t => ‖S t‖ ^ 2) := hg1_cont
  have hcont_y2 : Continuous (fun t => ‖deriv S t‖ ^ 2) := hcontDS.norm.pow 2
  have hint_lhs : IntervalIntegrable (fun t => 10 * (N : ℝ) * (‖S t‖ * ‖deriv S t‖)) volume 0 1 :=
    (continuous_const.mul hg2_cont).intervalIntegrable 0 1
  have hint_x2 : IntervalIntegrable (fun t => 25 * (N : ℝ) ^ 2 * ‖S t‖ ^ 2) volume 0 1 :=
    (continuous_const.mul hcont_x2).intervalIntegrable 0 1
  have hint_y2 : IntervalIntegrable (fun t => ‖deriv S t‖ ^ 2) volume 0 1 :=
    hcont_y2.intervalIntegrable 0 1
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
      10 * (N : ℝ) * (‖S t‖ * ‖deriv S t‖) ≤ 25 * (N : ℝ) ^ 2 * ‖S t‖ ^ 2 + ‖deriv S t‖ ^ 2 := by
    intro t _
    nlinarith [sq_nonneg (5 * (N : ℝ) * ‖S t‖ - ‖deriv S t‖), norm_nonneg (S t),
      norm_nonneg (deriv S t), hNpos.le]
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hint_lhs
    (hint_x2.add hint_y2) hpt
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hint_x2 hint_y2,
    intervalIntegral.integral_const_mul, ← hG] at hmono
  -- hmono : 10*N*G ≤ 25*N²*(∫‖S‖²) + ∫‖deriv S‖²
  have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hyoung : 10 * (N : ℝ) * G ≤ 65 * (N : ℝ) ^ 2 * P := by
    have hNP : (0 : ℝ) ≤ (N : ℝ) ^ 2 * P := mul_nonneg (sq_nonneg _) hP_nonneg
    have hkey : (0 : ℝ) ≤ ((N : ℝ) ^ 2 * P) * (10 - Real.pi ^ 2) :=
      mul_nonneg hNP (by linarith [hpi])
    have hb : 25 * (N : ℝ) ^ 2 * (∫ t in (0:ℝ)..1, ‖S t‖ ^ 2)
        + (∫ t in (0:ℝ)..1, ‖deriv S t‖ ^ 2) ≤ 65 * (N : ℝ) ^ 2 * P := by
      rw [hparse]
      nlinarith [hL22, hkey]
    linarith [hmono, hb]
  have h5N : (0 : ℝ) < 5 * (N : ℝ) := by linarith
  have hfin : 2 * G ≤ 13 * (N : ℝ) * P := by nlinarith [hyoung, h5N]
  -- combine
  have hδinv : (0 : ℝ) ≤ δ⁻¹ := by positivity
  have hA : δ⁻¹ * (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2) ≤ δ⁻¹ * P := by
    apply mul_le_mul_of_nonneg_left _ hδinv
    calc (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2)
        ≤ ∫ t in (0:ℝ)..1, ‖S t‖ ^ 2 := hper1
      _ = P := hparse
  have hB : 2 * (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖deriv S t‖)
      ≤ 13 * (N : ℝ) * P := by
    have : 2 * (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖deriv S t‖) ≤ 2 * G :=
      mul_le_mul_of_nonneg_left hper2 (by norm_num)
    linarith [this, hfin]
  calc ∑ r, ‖S (α r)‖ ^ 2
      ≤ δ⁻¹ * (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2)
          + 2 * (∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖deriv S t‖) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum (fun r _ => hgall r)
    _ ≤ δ⁻¹ * P + 13 * (N : ℝ) * P := by linarith [hA, hB]
    _ = (δ⁻¹ + 13 * N) * P := by ring

end Salt.LS

-- ==== upstream: Salt/LS/GaussSum.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Large sieve track, nodes L7.1 + L7.2: the Gauss-sum machinery

Blueprint: `docs/blueprints/largesieve.md` (W4, character form).

Work over a primitive Dirichlet character `χ : DirichletCharacter ℂ q` (`q ≥ 1`,
composite allowed) and the standard primitive additive character
`ψ = ZMod.stdAddChar : AddChar (ZMod q) ℂ`, `ψ j = exp (2πi j / q)`.

* **L7.2** (`gaussSum_normSq_of_primitive`, specialised as `gaussSum_normSq`):
  `‖gaussSum χ ψ‖² = q` for **all** `q` (not just prime). mathlib's
  `gaussSum_mul_gaussSum_eq_card` is `[Field R]`-only, so we take the
  Parseval-over-residues route that works at composite moduli. Compute
  `T := ∑_{n : ZMod q} ‖gaussSum χ (ψ.mulShift n)‖²` two ways:
  - via `gaussSum_mulShift_of_isPrimitive`, `gaussSum χ (ψ.mulShift n) = χ⁻¹ n · τ`,
    so `T = (∑_a ‖χ a‖²) · ‖τ‖²`;
  - expanding the square and using additive-character orthogonality
    (`AddChar.sum_mulShift`), `∑_n ψ(n·(a−b)) = q·δ_{a,b}`, so `T = q · ∑_a ‖χ a‖²`.
  Equate and cancel the positive factor `∑_a ‖χ a‖²` (its `a = 1` term is `1`).
  The argument never computes `φ(q)` and holds for any primitive additive
  character.

* **L7.1** (`dirichlet_inversion`, `dirichlet_inversion'`): the Gauss-sum
  inversion `∑_a χ⁻¹ a · ψ(n·a) = χ n · gaussSum χ⁻¹ ψ`, i.e.
  `gaussSum_mulShift_of_isPrimitive` at the primitive character `χ⁻¹`
  (`conductor_inv` gives primitivity of the inverse). Solving for `χ n` uses
  `gaussSum χ⁻¹ ψ ≠ 0` (`gaussSum_ne_zero`, itself from L7.2 and `q ≥ 1`).

* **The `e`-bridge** (`stdAddChar_eq_e`): `ψ a = e (a.val / q)`, connecting
  mathlib's `stdAddChar`/`toCircle` plumbing to the track carrier
  `e x = exp (2πi x)`. This lets L7.3 rewrite `∑_a χ⁻¹ a · ψ(n·a)` as an
  `expSum`-style evaluation at the Farey point `n/q`.
-/

namespace Salt.LS

open scoped BigOperators
open AddChar DirichletCharacter ComplexConjugate

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-! ### L7.2 — `‖gaussSum χ ψ‖² = q` for primitive `χ`, all `q` -/

/-- **L7.2 (general additive character).** For a primitive Dirichlet character `χ`
and *any* primitive additive character `ψ` on `ZMod q`, `‖gaussSum χ ψ‖² = q`
(with `q` arbitrary — composite included). -/
theorem gaussSum_normSq_of_primitive (hχ : χ.IsPrimitive)
    {ψ : AddChar (ZMod q) ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (q : ℝ) := by
  -- `conj (ψ x) = ψ (-x)`, from primitivity/roots-of-unity.
  have hR : 0 < ringChar (ZMod q) := by
    rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne q)
  have hψconj : ∀ x : ZMod q, conj (ψ x) = ψ (-x) := fun x => by
    rw [AddChar.starComp_apply hR, AddChar.inv_apply]
  -- `conj (χ n) = χ⁻¹ n` and the norm-symmetry `χ⁻¹ n · conj (χ⁻¹ n) = χ n · conj (χ n)`.
  have hconj : ∀ n : ZMod q, conj (χ n) = χ⁻¹ n := fun n => by
    rw [starRingEnd_apply, MulChar.star_apply']
  have hnn : ∀ n : ZMod q, χ⁻¹ n * conj (χ⁻¹ n) = χ n * conj (χ n) := fun n => by
    rw [← hconj n, Complex.conj_conj]; ring
  -- shift relation `gaussSum χ (ψ.mulShift n) = χ⁻¹ n · gaussSum χ ψ`.
  have hG : ∀ n : ZMod q, gaussSum χ (ψ.mulShift n) = χ⁻¹ n * gaussSum χ ψ :=
    fun n => gaussSum_mulShift_of_isPrimitive ψ hχ n
  -- `gaussSum χ (ψ.mulShift n)` expands definitionally.
  have hexp : ∀ n : ZMod q,
      gaussSum χ (ψ.mulShift n) = ∑ a : ZMod q, χ a * ψ (n * a) := fun _ => rfl
  -- expansion of `‖gaussSum χ (ψ.mulShift n)‖²` as a double sum.
  have Gn_conj : ∀ n : ZMod q,
      gaussSum χ (ψ.mulShift n) * conj (gaussSum χ (ψ.mulShift n))
        = ∑ a : ZMod q, ∑ b : ZMod q, χ a * conj (χ b) * ψ (n * (a - b)) := by
    intro n
    rw [hexp n, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul (starRingEnd ℂ), hψconj (n * b)]
    have hcomb : ψ (n * a) * ψ (-(n * b)) = ψ (n * (a - b)) := by
      rw [← AddChar.map_add_eq_mul, show n * a + -(n * b) = n * (a - b) from by ring]
    calc χ a * ψ (n * a) * (conj (χ b) * ψ (-(n * b)))
        = χ a * conj (χ b) * (ψ (n * a) * ψ (-(n * b))) := by ring
      _ = χ a * conj (χ b) * ψ (n * (a - b)) := by rw [hcomb]
  -- Way 2: `T = q · ∑_a χ a · conj (χ a)` (additive orthogonality).
  have hI : ∑ n : ZMod q, gaussSum χ (ψ.mulShift n) * conj (gaussSum χ (ψ.mulShift n))
      = (q : ℂ) * ∑ a : ZMod q, χ a * conj (χ a) := by
    simp_rw [Gn_conj]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    -- collapse the inner `∑_n` via additive orthogonality
    have hstep : ∀ b : ZMod q,
        ∑ n : ZMod q, χ a * conj (χ b) * ψ (n * (a - b))
          = χ a * conj (χ b) * (if a = b then (q : ℂ) else 0) := fun b => by
      rw [← Finset.mul_sum, AddChar.sum_mulShift (a - b) hψ, ZMod.card]
      congr 1
      simp only [Nat.cast_ite, Nat.cast_zero, sub_eq_zero]
    simp_rw [hstep, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ a (fun b => χ a * conj (χ b) * (q : ℂ))]
    rw [if_pos (Finset.mem_univ a)]
    ring
  -- Way 1: `T = (∑_a χ a · conj (χ a)) · (gaussSum χ ψ · conj (gaussSum χ ψ))`.
  have hII : ∑ n : ZMod q, gaussSum χ (ψ.mulShift n) * conj (gaussSum χ (ψ.mulShift n))
      = (∑ a : ZMod q, χ a * conj (χ a)) * (gaussSum χ ψ * conj (gaussSum χ ψ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hG n, map_mul, ← hnn n]
    ring
  -- Equate the two computations.
  have key : (∑ a : ZMod q, χ a * conj (χ a)) * (gaussSum χ ψ * conj (gaussSum χ ψ))
      = (q : ℂ) * ∑ a : ZMod q, χ a * conj (χ a) := by rw [← hII, hI]
  -- Descend to `ℝ`: both `∑_a χ a conj (χ a)` and `τ conj τ` are real casts.
  have hSumCast : (∑ a : ZMod q, χ a * conj (χ a))
      = ((∑ a : ZMod q, ‖χ a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_conj']; norm_cast
  have hτ : gaussSum χ ψ * conj (gaussSum χ ψ) = ((‖gaussSum χ ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; norm_cast
  rw [hSumCast, hτ] at key
  have keyR : (∑ a : ZMod q, ‖χ a‖ ^ 2) * ‖gaussSum χ ψ‖ ^ 2
      = (q : ℝ) * ∑ a : ZMod q, ‖χ a‖ ^ 2 := by exact_mod_cast key
  -- `∑_a ‖χ a‖² > 0` (the `a = 1` term is `1`), so we may cancel it.
  have hS : (∑ a : ZMod q, ‖χ a‖ ^ 2) ≠ 0 := by
    have hpos : 0 < ∑ a : ZMod q, ‖χ a‖ ^ 2 := by
      apply Finset.sum_pos'
      · intro a _; positivity
      · refine ⟨1, Finset.mem_univ 1, ?_⟩
        rw [MulChar.map_one, norm_one]; norm_num
    exact ne_of_gt hpos
  have hcancel : (∑ a : ZMod q, ‖χ a‖ ^ 2) * ‖gaussSum χ ψ‖ ^ 2
      = (∑ a : ZMod q, ‖χ a‖ ^ 2) * (q : ℝ) := by rw [keyR]; ring
  exact mul_left_cancel₀ hS hcancel

/-- **L7.2.** For a primitive Dirichlet character `χ` mod `q` and the standard
additive character, `‖gaussSum χ ψ‖² = q`, for all `q ≥ 1` (composite included). -/
theorem gaussSum_normSq (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)‖ ^ 2 = (q : ℝ) :=
  gaussSum_normSq_of_primitive χ hχ (ZMod.isPrimitive_stdAddChar q)

/-- For primitive `χ`, the Gauss sum with the standard additive character is
nonzero (immediate from L7.2 and `q ≥ 1`). -/
theorem gaussSum_ne_zero (hχ : χ.IsPrimitive) :
    gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) ≠ 0 := by
  have hnorm := gaussSum_normSq χ hχ
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  intro h
  rw [h, norm_zero] at hnorm
  have hq0 : (q : ℝ) = 0 := by rw [← hnorm]; norm_num
  linarith

/-! ### L7.1 — Gauss-sum inversion for primitive `χ` -/

omit [NeZero q] in
/-- `χ⁻¹` is primitive when `χ` is (`conductor_inv`). -/
theorem isPrimitive_inv (hχ : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  have h : χ⁻¹.conductor = q := by rw [DirichletCharacter.conductor_inv]; exact hχ
  exact h

/-- **L7.1 (inversion, sum form).** For primitive `χ` and every `n : ZMod q`
(units and non-units alike),
`∑ a, χ⁻¹ a · ψ (n·a) = χ n · gaussSum χ⁻¹ ψ`. -/
theorem dirichlet_inversion (hχ : χ.IsPrimitive) (n : ZMod q) :
    ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (n * a)
      = χ n * gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
  have hχ' : χ⁻¹.IsPrimitive := isPrimitive_inv χ hχ
  calc ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (n * a)
      = gaussSum χ⁻¹ ((ZMod.stdAddChar : AddChar (ZMod q) ℂ).mulShift n) := by
        simp only [gaussSum, AddChar.mulShift_apply]
    _ = χ n * gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
        rw [gaussSum_mulShift_of_isPrimitive _ hχ', inv_inv]

/-- **L7.1 (inversion, solved for `χ`).** For primitive `χ`,
`χ n = (gaussSum χ⁻¹ ψ)⁻¹ · ∑ a, χ⁻¹ a · ψ (n·a)`. This is the character
LS-expansion form consumed by L7.3. -/
theorem dirichlet_inversion' (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ n = (gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ))⁻¹
        * ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (n * a) := by
  have hχ' : χ⁻¹.IsPrimitive := isPrimitive_inv χ hχ
  rw [dirichlet_inversion χ hχ n, mul_comm (χ n),
    ← mul_assoc, inv_mul_cancel₀ (gaussSum_ne_zero χ⁻¹ hχ'), one_mul]

/-! ### The `e`-bridge -/

/-- **The `e`-bridge (deliverable 3).** mathlib's standard additive character
`ZMod.stdAddChar` on `ZMod q` is the track carrier `e` at the Farey point:
`ψ a = e (a.val / q)`. -/
theorem stdAddChar_eq_e (a : ZMod q) :
    (ZMod.stdAddChar a : ℂ) = e ((a.val : ℝ) / q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp]
  unfold e
  congr 1
  push_cast
  ring

end Salt.LS

-- ==== upstream: Salt/LS/Farey.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/


/-!
# L6.1 — Farey spacing

Design: `docs/blueprints/largesieve.md`, "Carrier choices" and node `L6.1`.
Two distinct Farey-type fractions `a/q ≠ a'/q'` with denominators `q, q' ≤ Q`
are `dist₁`-separated by at least `1/Q²`. Coprimality of `a` with `q` (and
`a'` with `q'`) is NOT needed; the argument only uses `0 ≤ a < q`,
`0 ≤ a' < q'`, and `a/q ≠ a'/q'`.

The denominator-sharp core estimate `1/(q q') ≤ dist₁ (a/q) (a'/q')` is
proved first (`farey_spacing_core`); the `Q`-uniform corollary
(`farey_spacing`) follows from `q, q' ≤ Q ⇒ q q' ≤ Q²`.

Proof idea for the core estimate: writing `x = a/q`, `y = a'/q'`, for every
integer `n` the difference `x - y - n` equals `(k : ℝ) / (q q')` where
`k = a q' - a' q - n q q' : ℤ`. If `k = 0` then `x - y = n`; but
`x, y ∈ [0, 1)` forces `x - y ∈ (-1, 1)`, so `n = 0` and `x = y`,
contradicting `x ≠ y`. Hence `k ≠ 0`, so `|k| ≥ 1` (`Int.one_le_abs`) and
`|x - y - n| ≥ 1/(q q')` for every integer `n`; take `n = round (x - y)`,
which is exactly `dist₁ x y`.
-/

namespace Salt.LS

/-- **L6.1 core.** Denominator-sharp Farey spacing: two distinct fractions
`a/q ≠ a'/q'` with `a < q`, `a' < q'` are `dist₁`-separated by at least
`1/(q q')`. Coprimality is not required. -/
theorem farey_spacing_core {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (ha : a < q) (ha' : a' < q') (hne : (a : ℝ) / q ≠ (a' : ℝ) / q') :
    1 / ((q : ℝ) * q') ≤ dist₁ ((a : ℝ) / q) ((a' : ℝ) / q') := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  set x : ℝ := (a : ℝ) / q with hxdef
  set y : ℝ := (a' : ℝ) / q' with hydef
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg a) hqR.le
  have hx1 : x < 1 := by
    rw [hxdef, div_lt_one hqR]
    exact_mod_cast ha
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg a') hq'R.le
  have hy1 : y < 1 := by
    rw [hydef, div_lt_one hq'R]
    exact_mod_cast ha'
  -- For every integer `n`, `|x - y - n| ≥ 1/(q q')`.
  have key : ∀ n : ℤ, 1 / ((q : ℝ) * q') ≤ |x - y - (n : ℝ)| := by
    intro n
    set k : ℤ := (a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ) - n * (q : ℤ) * (q' : ℤ)
      with hkdef
    have hxy : x - y - (n : ℝ) = (k : ℝ) / ((q : ℝ) * q') := by
      rw [hxdef, hydef, hkdef]
      push_cast
      field_simp
    have hk0 : k ≠ 0 := by
      intro h0
      apply hne
      have hz : (k : ℝ) = 0 := by exact_mod_cast h0
      have hxyn : x - y - (n : ℝ) = 0 := by rw [hxy, hz, zero_div]
      have hnlt : (n : ℝ) < 1 := by linarith
      have hngt : (-1 : ℝ) < (n : ℝ) := by linarith
      have hn0 : n = 0 := by
        have h1 : n < 1 := by exact_mod_cast hnlt
        have h2 : -1 < n := by exact_mod_cast hngt
        omega
      have hn0R : (n : ℝ) = 0 := by exact_mod_cast hn0
      linarith
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have hZ : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      exact_mod_cast hZ
    rw [hxy, abs_div, abs_of_pos (mul_pos hqR hq'R)]
    gcongr
  have := key (round (x - y))
  unfold dist₁
  exact this

/-- **L6.1.** Farey spacing, `Q`-uniform form: two distinct fractions
`a/q ≠ a'/q'` with denominators bounded by a common `Q` are `dist₁`-separated
by at least `1/Q²`. Coprimality is not required. -/
theorem farey_spacing {q q' Q a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hqQ : q ≤ Q) (hq'Q : q' ≤ Q) (ha : a < q) (ha' : a' < q')
    (hne : (a : ℝ) / q ≠ (a' : ℝ) / q') :
    1 / (Q : ℝ) ^ 2 ≤ dist₁ ((a : ℝ) / q) ((a' : ℝ) / q') := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hq'QR : (q' : ℝ) ≤ Q := by exact_mod_cast hq'Q
  have hcore := farey_spacing_core hq hq' ha ha' hne
  have hQR : (0 : ℝ) ≤ (Q : ℝ) := hqR.le.trans hqQR
  have hQQ : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    have hmul : (q : ℝ) * q' ≤ (Q : ℝ) * Q := mul_le_mul hqQR hq'QR hq'R.le hQR
    nlinarith [hmul]
  have hstep : 1 / (Q : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * q') :=
    one_div_le_one_div_of_le (mul_pos hqR hq'R) hQQ
  exact hstep.trans hcore

end Salt.LS

-- ==== upstream: Salt/LS/ArithmeticLS.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/


/-!
# Large sieve track, nodes L6.1b + L6.2: the arithmetic large sieve

Blueprint: `docs/blueprints/largesieve.md`.

* **L6.1b** — Farey system assembly. We enumerate the reduced Farey system
  `{(q, a) : 1 ≤ q ≤ Q, a < q, gcd q a = 1}` as a `Finset` of dependent pairs
  (`fareyPairs`), map each pair to its fraction `a/q` (`fareyFrac`), and package
  the pairwise Farey spacing (L6.1) into the `Spaced (1/Q²)` hypothesis that
  `analytic_LS` (L3.1) consumes.  The generic engine is
  `sum_expSum_sq_le_of_spaced`: given any finite index set carrying pairwise
  `dist₁`-separation, the analytic large-sieve bound holds for the corresponding
  `expSum` sum.  The `Fin R` reindexing that `analytic_LS` needs is done once,
  here, via `Fintype.equivFin` on the coe-sort of the finset.

  **Why reducedness matters (but did not in L6.1).**  L6.1 (`farey_spacing`)
  is coprimality-free, but it needs the two fractions to be *distinct* reals.
  Distinctness of the *pairs* only forces distinctness of the *fractions* when
  the fractions are in lowest terms: `a/q = a'/q'` with `gcd q a = gcd q' a' = 1`
  and `a < q, a' < q'` forces `(q,a) = (q',a')`.  This is exactly
  `fareyFrac`-injectivity, proved by cross-multiplication + `Nat.Coprime`
  divisibility (`Nat.Coprime.dvd_of_dvd_mul_left`).

* **L6.2** — the arithmetic large sieve (FROZEN), for `2 ≤ Q`.  Route:
  `sum_expSum_sq_le_of_spaced` at `δ = 1/Q²`, whose gate `δ ≤ 1/2` uses
  `Q² ≥ 4`, and whose `δ⁻¹` reads off as `Q²`.  The `Q = 1` degenerate case
  (`δ = 1` violates the `δ ≤ 1/2` gate) is the separate one-line Cauchy–Schwarz
  corollary `arithmetic_LS_one`.

**Filter-direction convention.**  The blueprint freezes the reduced-residue
filter as `(Finset.range q).filter (Nat.Coprime q)`, i.e. `fun a => Nat.Coprime q a`
(modulus first).  `Salt/Maynard` uses `fun n => Nat.Coprime n B` (residue first);
`Nat.Coprime` is symmetric so the two filters are equal as sets, but we match the
*frozen* statement here (modulus-first).  Downstream L7.3/L8 consumers follow this.
-/

namespace Salt.LS

open scoped BigOperators

/-- **L6.1b.** The reduced Farey system of order `Q`: dependent pairs `(q, a)`
with `1 ≤ q ≤ Q`, `a < q`, and `gcd q a = 1`. -/
def fareyPairs (Q : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 Q).sigma (fun q => (Finset.range q).filter (Nat.Coprime q))

/-- **L6.1b.** The fraction attached to a Farey pair: `(q, a) ↦ a / q`. -/
noncomputable def fareyFrac (x : Σ _ : ℕ, ℕ) : ℝ := (x.2 : ℝ) / (x.1 : ℝ)

@[simp] lemma fareyFrac_mk (q a : ℕ) : fareyFrac ⟨q, a⟩ = (a : ℝ) / q := rfl

/-- **L6.1b (assembly engine).** The analytic large sieve, packaged for an
arbitrary finite index set `S` whose points, mapped by `φ` into `ℝ`, are
pairwise `δ`-separated (mod 1). The `Fin R` reindexing `analytic_LS` requires is
performed here once via `Fintype.equivFin`. -/
theorem sum_expSum_sq_le_of_spaced {ι : Type*} {N : ℕ} {δ : ℝ}
    (S : Finset ι) (φ : ι → ℝ) (c : ℕ → ℂ)
    (hSp : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist₁ (φ x) (φ y))
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∑ x ∈ S, ‖expSum N c (φ x)‖ ^ 2 ≤ (δ⁻¹ + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  classical
  set R := Fintype.card {x // x ∈ S} with hRdef
  set σ : {x // x ∈ S} ≃ Fin R := Fintype.equivFin _ with hσdef
  set α : Fin R → ℝ := fun r => φ ((σ.symm r : {x // x ∈ S}) : ι) with hαdef
  -- The reduced system is `δ`-spaced: distinct `Fin R` indices point to distinct
  -- members of `S`, whose `φ`-images are `δ`-separated by hypothesis.
  have hspaced : Spaced δ α := by
    intro r s hrs
    have hne : σ.symm r ≠ σ.symm s := fun h => hrs (σ.symm.injective h)
    have hval : ((σ.symm r : {x // x ∈ S}) : ι) ≠ ((σ.symm s : {x // x ∈ S}) : ι) :=
      fun h => hne (Subtype.ext h)
    simpa only [hαdef] using hSp _ (σ.symm r).2 _ (σ.symm s).2 hval
  -- Reindex `∑ x ∈ S` through the enumeration `σ`.
  have hreindex : ∑ x ∈ S, ‖expSum N c (φ x)‖ ^ 2 = ∑ r : Fin R, ‖expSum N c (α r)‖ ^ 2 := by
    rw [← Finset.sum_coe_sort S (fun x => ‖expSum N c (φ x)‖ ^ 2)]
    refine Fintype.sum_equiv σ _ _ (fun i => ?_)
    simp only [hαdef, Equiv.symm_apply_apply]
  rw [hreindex]
  exact analytic_LS c hspaced hδ hδ2

/-- **L6.2 — arithmetic large sieve (FROZEN).** For `2 ≤ Q`, the exponential-sum
energy over the reduced Farey fractions of order `Q` is bounded by
`(Q² + 13N)·∑‖cₙ‖²`. -/
theorem arithmetic_LS {N Q : ℕ} (hQ : 2 ≤ Q) (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
        ‖expSum N c ((a : ℝ) / q)‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  -- `δ = 1/Q²` clears the analytic gate `0 < δ ≤ 1/2` because `Q² ≥ 4`.
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith
  have hQsq : (0 : ℝ) < (Q : ℝ) ^ 2 := by positivity
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := one_div_pos.mpr hQsq
  have hδ2 : 1 / (Q : ℝ) ^ 2 ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [hQR]
  -- Pairwise spacing of the Farey system: distinct reduced pairs ⇒ distinct
  -- fractions (reducedness ⇒ injectivity) ⇒ `1/Q²`-separated by `farey_spacing`.
  have hSp : ∀ x ∈ fareyPairs Q, ∀ y ∈ fareyPairs Q, x ≠ y →
      1 / (Q : ℝ) ^ 2 ≤ dist₁ (fareyFrac x) (fareyFrac y) := by
    rintro ⟨q, a⟩ hx ⟨q', a'⟩ hy hxy
    simp only [fareyPairs, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_range] at hx hy
    obtain ⟨⟨hq1, hqQ⟩, ha_lt, hcop⟩ := hx
    obtain ⟨⟨hq'1, hq'Q⟩, ha'_lt, hcop'⟩ := hy
    have hqpos : 0 < q := hq1
    have hq'pos : 0 < q' := hq'1
    have hfrac_ne : (a : ℝ) / q ≠ (a' : ℝ) / q' := by
      intro heq
      apply hxy
      have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
      have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'pos
      rw [div_eq_div_iff hqR.ne' hq'R.ne'] at heq
      have heqN : a * q' = a' * q := by exact_mod_cast heq
      -- coprimality turns the cross-relation into `q = q'` and `a = a'`
      have hdvd1 : q ∣ q' := hcop.dvd_of_dvd_mul_left ⟨a', by rw [heqN]; ring⟩
      have hdvd2 : q' ∣ q := hcop'.dvd_of_dvd_mul_left ⟨a, by rw [← heqN]; ring⟩
      have hq_eq : q = q' := Nat.dvd_antisymm hdvd1 hdvd2
      have ha_eq : a = a' := by
        have hh := heqN
        rw [hq_eq] at hh
        exact Nat.eq_of_mul_eq_mul_right hq'pos hh
      rw [hq_eq, ha_eq]
    simp only [fareyFrac_mk]
    exact farey_spacing hqpos hq'pos hqQ hq'Q ha_lt ha'_lt hfrac_ne
  -- Assemble: the engine at `δ = 1/Q²`, then read off `δ⁻¹ = Q²`.
  have hkey := sum_expSum_sq_le_of_spaced (N := N) (fareyPairs Q) fareyFrac c hSp hδ hδ2
  have hcoef : (1 / (Q : ℝ) ^ 2)⁻¹ = (Q : ℝ) ^ 2 := by rw [one_div, inv_inv]
  rw [hcoef] at hkey
  have hrewrite : ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
        ‖expSum N c ((a : ℝ) / q)‖ ^ 2 = ∑ x ∈ fareyPairs Q, ‖expSum N c (fareyFrac x)‖ ^ 2 := by
    rw [fareyPairs, Finset.sum_sigma']
    simp only [fareyFrac]
  rw [hrewrite]
  exact hkey

/-- **L6.2 corollary — the `Q = 1` case.** Here `δ = 1/Q² = 1` violates the
`δ ≤ 1/2` gate of `analytic_LS`, so this degenerate case is proved directly by
Cauchy–Schwarz: the single Farey point is `0/1 = 0`, and
`‖∑ cₙ‖² ≤ N·∑‖cₙ‖² ≤ (1 + 13N)·∑‖cₙ‖²`. -/
theorem arithmetic_LS_one {N : ℕ} (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 1, ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
        ‖expSum N c ((a : ℝ) / q)‖ ^ 2 ≤ (1 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  -- The `q = 1` system is the single point `0/1 = 0`.
  have hfilter : (Finset.range 1).filter (Nat.Coprime 1) = {0} := by
    ext a
    simp
  have hexp0 : expSum N c 0 = ∑ n ∈ Finset.range N, c n := by
    unfold expSum
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [mul_zero, e_zero, mul_one]
  rw [Finset.Icc_self, Finset.sum_singleton, hfilter, Finset.sum_singleton]
  simp only [Nat.cast_zero, Nat.cast_one, zero_div]
  rw [hexp0]
  -- Cauchy–Schwarz: `‖∑ cₙ‖² ≤ (∑‖cₙ‖)² ≤ N·∑‖cₙ‖² ≤ (1 + 13N)·∑‖cₙ‖²`.
  have hnorm_sum : ‖∑ n ∈ Finset.range N, c n‖ ≤ ∑ n ∈ Finset.range N, ‖c n‖ :=
    norm_sum_le _ _
  have hcs : (∑ n ∈ Finset.range N, ‖c n‖) ^ 2 ≤ (N : ℝ) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := fun n => ‖c n‖)
    simpa [Finset.card_range] using h
  have hsq : ‖∑ n ∈ Finset.range N, c n‖ ^ 2 ≤ (∑ n ∈ Finset.range N, ‖c n‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm_sum 2
  have hS2 : (0 : ℝ) ≤ ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hNle : (N : ℝ) ≤ 1 + 13 * (N : ℝ) := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  calc ‖∑ n ∈ Finset.range N, c n‖ ^ 2
      ≤ (∑ n ∈ Finset.range N, ‖c n‖) ^ 2 := hsq
    _ ≤ (N : ℝ) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := hcs
    _ ≤ (1 + 13 * (N : ℝ)) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hNle hS2

end Salt.LS

-- ==== upstream: Salt/LS/CharLS.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/


/-!
# Large sieve track, node L7.3: the character-form large sieve

Blueprint: `docs/blueprints/largesieve.md` (W4, character form).

For `2 ≤ Q` and any coefficient sequence `c : ℕ → ℂ`,
```
∑ q ∈ Icc 1 Q, (q / φ q) * ∑ χ primitive mod q, ‖∑ n < N, c n · χ n‖²
  ≤ (Q² + 13 N) · ∑ n < N, ‖c n‖².
```

The proof reduces the character form to the arithmetic large sieve `arithmetic_LS`
(L6.2) one modulus at a time (`char_LS_perQ`), via Gauss-sum inversion.

## The per-`q` argument

Fix `q ≥ 1` and write `ψ = ZMod.stdAddChar`. For `a : ZMod q` set
`S a = ∑ n < N, c n · ψ (n·a)`, and for a Dirichlet character `χ` set
`T χ = ∑ a, χ⁻¹ a · S a` (effectively a sum over units, since `χ⁻¹` vanishes off
units).

* **Per-`χ` identity (primitive `χ`).** Swapping the `a`- and `n`-sums and applying
  the Gauss-sum inversion `dirichlet_inversion` (L7.1) gives
  `T χ = (∑ n, c n · χ n) · gaussSum χ⁻¹ ψ`, whence
  `‖T χ‖² = ‖∑ n, c n · χ n‖² · q` using `‖gaussSum χ⁻¹ ψ‖² = q` (L7.2, `gaussSum_normSq`
  on `χ⁻¹` via `isPrimitive_inv`).

* **Plancherel over *all* `χ` (the budget).** Expanding `∑_χ ‖T χ‖²` and collapsing
  the character sum by the second orthogonality relation
  `DirichletCharacter.sum_characters_eq` yields
  `∑_χ ‖T χ‖² = φ(q) · ∑_{a unit} ‖S a‖²`. Restricting the left sum to primitive `χ`
  (each term `≥ 0`) and inserting the per-`χ` identity gives
  `q · ∑_{χ prim} ‖∑ c χ‖² ≤ φ(q) · ∑_{a unit} ‖S a‖²`, i.e.
  `(q/φ q) · ∑_{χ prim} ‖∑ c χ‖² ≤ ∑_{a unit} ‖S a‖²`. Summing the per-`χ` inequality
  *directly* would over-count the `a`-sum once per `χ`; going through all `χ` and
  orthogonality is what keeps the budget honest.

* **The bridge to Farey points.** `stdAddChar_eq_e` and `e`-power identities give
  `S a = expSum N c (a.val / q)`, and the unit-`a` sum reindexes (`a ↦ a.val`,
  `ZMod.isUnit_iff_coprime`) to `∑ a ∈ (range q).filter (Nat.Coprime q)`. The arithmetic
  large sieve `arithmetic_LS` (L6.2) then closes the `q`-sum.

Only `[propext, Classical.choice, Quot.sound]` are used. `Classical` is opened so the
primitive-character sum can be written as a `Finset.univ.filter` over the (noncomputable)
`Fintype (DirichletCharacter ℂ q)` instance.
-/

namespace Salt.LS

open scoped BigOperators
open ComplexConjugate

/-- `e (n·x) = (e x)^n` for a natural power. -/
lemma e_natCast_mul (n : ℕ) (x : ℝ) : e ((n : ℝ) * x) = e x ^ n := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

open Classical in
/-- **L7.3, per modulus.** For `q ≥ 1` and primitive characters mod `q`,
`(q/φ q) · ∑_{χ prim} ‖∑ n, c n · χ n‖² ≤ ∑ a ∈ (range q).filter (Coprime q),
‖expSum N c (a/q)‖²`. This is the heart of the character large sieve; summing it over
`q ∈ Icc 1 Q` and applying `arithmetic_LS` gives `char_LS`. -/
theorem char_LS_perQ {N : ℕ} (q : ℕ) [NeZero q] (c : ℕ → ℂ) :
    ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2
      ≤ ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), ‖expSum N c ((a : ℝ) / q)‖ ^ 2 := by
  classical
  -- The additive-character "twist" `S a = ∑ n, c n · ψ (n·a)` and its dual pairing
  -- `T χ = ∑ a, χ⁻¹ a · S a`.
  set S : ZMod q → ℂ :=
    fun a => ∑ n ∈ Finset.range N, c n * ZMod.stdAddChar ((n : ZMod q) * a) with hS_def
  set T : DirichletCharacter ℂ q → ℂ := fun χ => ∑ a : ZMod q, χ⁻¹ a * S a with hT_def
  have hSval : ∀ a, S a = ∑ n ∈ Finset.range N, c n * ZMod.stdAddChar ((n : ZMod q) * a) :=
    fun a => by rw [hS_def]
  have hTval : ∀ χ, T χ = ∑ a : ZMod q, χ⁻¹ a * S a := fun χ => by rw [hT_def]
  -- `conj (χ⁻¹ b) = χ b`.
  have hconjInv : ∀ (χ : DirichletCharacter ℂ q) (b : ZMod q),
      (starRingEnd ℂ) (χ⁻¹ b) = χ b := by
    intro χ b
    rw [starRingEnd_apply, MulChar.star_apply', inv_inv]
  -- Second orthogonality: `∑_χ χ⁻¹ a · χ b = φ(q)·δ_{a,b}` for `a` a unit.
  have horth : ∀ (a b : ZMod q), IsUnit a →
      (∑ χ : DirichletCharacter ℂ q, χ⁻¹ a * χ b) = if a = b then (q.totient : ℂ) else 0 := by
    intro a b ha
    have hterm : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ a * χ b = χ (Ring.inverse a * b) := by
      intro χ; rw [MulChar.inv_apply, ← map_mul]
    simp_rw [hterm]
    rw [DirichletCharacter.sum_characters_eq]
    have hiff : (Ring.inverse a * b = 1) ↔ (a = b) := by
      constructor
      · intro h
        have h2 : a * (Ring.inverse a * b) = a * 1 := by rw [h]
        rwa [← mul_assoc, Ring.mul_inverse_cancel a ha, one_mul, mul_one, eq_comm] at h2
      · rintro rfl
        exact Ring.inverse_mul_cancel a ha
    exact if_congr hiff rfl rfl
  -- Expand `‖T χ‖²` (as `T χ · conj (T χ)`) into a double sum over `ZMod q`.
  have expand : ∀ χ : DirichletCharacter ℂ q,
      T χ * (starRingEnd ℂ) (T χ)
        = ∑ a : ZMod q, ∑ b : ZMod q, (χ⁻¹ a * χ b) * (S a * (starRingEnd ℂ) (S b)) := by
    intro χ
    have hTc : (starRingEnd ℂ) (T χ) = ∑ b : ZMod q, χ b * (starRingEnd ℂ) (S b) := by
      rw [hTval χ, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, hconjInv χ b]
    rw [hTval χ, hTc, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  -- Collapse the character sum against the twist products, one `a` at a time.
  have hcollapse : ∀ a : ZMod q,
      (∑ χ : DirichletCharacter ℂ q, ∑ b : ZMod q,
          (χ⁻¹ a * χ b) * (S a * (starRingEnd ℂ) (S b)))
        = (if IsUnit a then (q.totient : ℂ) * (S a * (starRingEnd ℂ) (S a)) else 0) := by
    intro a
    rw [Finset.sum_comm]
    by_cases ha : IsUnit a
    · rw [if_pos ha]
      have step : ∀ b : ZMod q,
          (∑ χ : DirichletCharacter ℂ q, (χ⁻¹ a * χ b) * (S a * (starRingEnd ℂ) (S b)))
            = (if a = b then (q.totient : ℂ) else 0) * (S a * (starRingEnd ℂ) (S b)) := by
        intro b
        rw [← Finset.sum_mul, horth a b ha]
      rw [Finset.sum_congr rfl fun b _ => step b]
      simp_rw [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq Finset.univ a fun b => (q.totient : ℂ) * (S a * (starRingEnd ℂ) (S b))]
      rw [if_pos (Finset.mem_univ a)]
    · rw [if_neg ha]
      refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun χ _ => ?_
      rw [MulChar.map_nonunit χ⁻¹ ha, zero_mul, zero_mul]
  -- Plancherel over ALL characters (complex form).
  have hplancherel : (∑ χ : DirichletCharacter ℂ q, T χ * (starRingEnd ℂ) (T χ))
      = (q.totient : ℂ) * ∑ a : ZMod q, (if IsUnit a then S a * (starRingEnd ℂ) (S a) else 0) := by
    calc (∑ χ : DirichletCharacter ℂ q, T χ * (starRingEnd ℂ) (T χ))
        = ∑ χ : DirichletCharacter ℂ q, ∑ a : ZMod q, ∑ b : ZMod q,
            (χ⁻¹ a * χ b) * (S a * (starRingEnd ℂ) (S b)) :=
          Finset.sum_congr rfl fun χ _ => expand χ
      _ = ∑ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, ∑ b : ZMod q,
            (χ⁻¹ a * χ b) * (S a * (starRingEnd ℂ) (S b)) := Finset.sum_comm
      _ = ∑ a : ZMod q, (if IsUnit a then (q.totient : ℂ) * (S a * (starRingEnd ℂ) (S a)) else 0) :=
          Finset.sum_congr rfl fun a _ => hcollapse a
      _ = (q.totient : ℂ) *
            ∑ a : ZMod q, (if IsUnit a then S a * (starRingEnd ℂ) (S a) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          split_ifs <;> ring
  -- Descend the two sides to `ℝ`.
  have descend_lhs : (∑ χ : DirichletCharacter ℂ q, T χ * (starRingEnd ℂ) (T χ))
      = ((∑ χ : DirichletCharacter ℂ q, ‖T χ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.mul_conj']; norm_cast
  have descend_rhs : (∑ a : ZMod q, (if IsUnit a then S a * (starRingEnd ℂ) (S a) else 0))
      = ((∑ a : ZMod q, (if IsUnit a then ‖S a‖ ^ 2 else 0) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with ha
    · rw [Complex.mul_conj']; norm_cast
    · norm_num
  have hplancherelR : (∑ χ : DirichletCharacter ℂ q, ‖T χ‖ ^ 2)
      = (q.totient : ℝ) * ∑ a : ZMod q, (if IsUnit a then ‖S a‖ ^ 2 else 0) := by
    have h := hplancherel
    rw [descend_lhs, descend_rhs] at h
    have hcast : (↑(∑ χ : DirichletCharacter ℂ q, ‖T χ‖ ^ 2) : ℂ)
        = ↑((q.totient : ℝ) * ∑ a : ZMod q, (if IsUnit a then ‖S a‖ ^ 2 else 0)) := by
      rw [h]; push_cast; ring
    exact_mod_cast hcast
  -- Per-`χ` identity for primitive `χ`.
  have hP1 : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ‖T χ‖ ^ 2 = ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2 * (q : ℝ) := by
    intro χ hχ
    have hTeq : T χ = (∑ n ∈ Finset.range N, c n * χ (n : ZMod q)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
      rw [hTval χ]
      calc ∑ a : ZMod q, χ⁻¹ a * S a
          = ∑ a : ZMod q, χ⁻¹ a *
              ∑ n ∈ Finset.range N, c n * ZMod.stdAddChar ((n : ZMod q) * a) := by
            refine Finset.sum_congr rfl fun a _ => by rw [hSval a]
        _ = ∑ a : ZMod q, ∑ n ∈ Finset.range N,
              χ⁻¹ a * (c n * ZMod.stdAddChar ((n : ZMod q) * a)) :=
            Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
        _ = ∑ n ∈ Finset.range N, ∑ a : ZMod q,
              χ⁻¹ a * (c n * ZMod.stdAddChar ((n : ZMod q) * a)) := Finset.sum_comm
        _ = ∑ n ∈ Finset.range N, c n *
              ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar ((n : ZMod q) * a) := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => by ring
        _ = ∑ n ∈ Finset.range N, c n *
              (χ (n : ZMod q) * gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)) := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [dirichlet_inversion χ hχ (n : ZMod q)]
        _ = (∑ n ∈ Finset.range N, c n * χ (n : ZMod q)) *
              gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun n _ => by ring
    rw [hTeq, norm_mul, mul_pow, gaussSum_normSq χ⁻¹ (isPrimitive_inv χ hχ)]
  -- The twist `S a` is the exponential sum at the Farey point `a.val / q`.
  have hSbridge : ∀ a : ZMod q, S a = expSum N c ((a.val : ℝ) / q) := by
    intro a
    rw [hSval a]
    unfold expSum
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    rw [show ((n : ZMod q) * a) = n • a from by rw [nsmul_eq_mul]]
    rw [AddChar.map_nsmul_eq_pow, stdAddChar_eq_e, e_natCast_mul]
  -- Reindex the unit-`a` sum to the reduced-residue Farey filter.
  have hBunit : (∑ a : ZMod q, (if IsUnit a then ‖S a‖ ^ 2 else 0))
      = ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), ‖expSum N c ((a : ℝ) / q)‖ ^ 2 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun a : ZMod q => a.val) (fun m : ℕ => (m : ZMod q)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at ha ⊢
      refine ⟨ZMod.val_lt a, ?_⟩
      have h := ZMod.val_coe_unit_coprime ha.unit
      rw [IsUnit.unit_spec] at h
      exact h.symm
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hm ⊢
      exact (ZMod.isUnit_iff_coprime m q).mpr hm.2.symm
    · intro a _
      exact ZMod.natCast_zmod_val a
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      exact ZMod.val_natCast_of_lt hm.1
    · intro a _
      rw [hSbridge a]
  -- Assemble: `q · (charSum) ≤ φ(q) · (fareySum)`, then divide.
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hrestrict :
      (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive), ‖T χ‖ ^ 2)
        ≤ ∑ χ : DirichletCharacter ℂ q, ‖T χ‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro χ _ _
    positivity
  have hkey :
      (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2) * (q : ℝ)
        ≤ (q.totient : ℝ) *
            ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), ‖expSum N c ((a : ℝ) / q)‖ ^ 2 := by
    calc (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2) * (q : ℝ)
        = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖T χ‖ ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun χ hχ => (hP1 χ (Finset.mem_filter.mp hχ).2).symm
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖T χ‖ ^ 2 := hrestrict
      _ = (q.totient : ℝ) * ∑ a : ZMod q, (if IsUnit a then ‖S a‖ ^ 2 else 0) := hplancherelR
      _ = (q.totient : ℝ) *
            ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), ‖expSum N c ((a : ℝ) / q)‖ ^ 2 := by
          rw [hBunit]
  rw [div_mul_eq_mul_div, div_le_iff₀ hφpos]
  nlinarith [hkey]

open Classical in
/-- **L7.3 — the character-form large sieve (FROZEN).** For `2 ≤ Q` and any coefficient
sequence `c : ℕ → ℂ`,
```
∑ q ∈ Icc 1 Q, (q / φ q) · ∑ χ primitive mod q, ‖∑ n < N, c n · χ n‖²
  ≤ (Q² + 13 N) · ∑ n < N, ‖c n‖².
```
The primitive-character sum is indexed by `Finset.univ.filter (·.IsPrimitive)` over the
`Fintype (DirichletCharacter ℂ q)` instance (with `Classical` decidability), and `χ n`
means `χ (n : ZMod q)`. Proof: `char_LS_perQ` for each modulus, then `arithmetic_LS`. -/
theorem char_LS {N Q : ℕ} (hQ : 2 ≤ Q) (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  classical
  calc ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
              ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2
      ≤ ∑ q ∈ Finset.Icc 1 Q,
          ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), ‖expSum N c ((a : ℝ) / q)‖ ^ 2 := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        haveI : NeZero q := ⟨Nat.one_le_iff_ne_zero.mp hq1⟩
        exact char_LS_perQ q c
    _ ≤ ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := arithmetic_LS hQ c

end Salt.LS

-- ==== upstream: Salt/Certs/LargeSieve.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/


/-!
# COMPREHENSIBILITY CERTIFICATE — the large sieve, analytic and character forms

**Anchor (row 8 of `docs/CERT-ANCHORS-0811.md`), Nature draft
`${SEAT_DIR}/briefs/2026-08-11-nature-draft-v0.md`** — named by path per M0, and pinned by
PHRASE because line numbers into that file have rotted once already:

* `:201` — *"no public artifact in any proof assistant proves … **the large sieve
  inequality** …"*
* `:205` — the adversary sentence: *"the two live external Bombieri–Vinogradov
  formalization projects **take Siegel–Walfisz and the large sieve as axioms**"*

**Landed declarations certified:** `Salt.LS.analytic_LS` (`Salt/LS/AnalyticLS.lean:58`)
and `Salt.LS.char_LS` (`Salt/LS/CharLS.lean:277`).

## What the second anchor makes this certificate about

The first anchor is an absence claim about the literature; **no Lean theorem can support
or refute it, and none here tries.** The second is different and it is the one that gives
this file its job: the adversaries *take the large sieve as an axiom*. **So the fact worth
certifying is not that a large-sieve-shaped statement exists here, but that it is PROVED,
with the constants written down.**

🔑 ***BOTH CERTIFICATES THEREFORE CARRY THEIR CONSTANTS IN THE STATEMENT — `δ⁻¹ + 13N`
and `Q² + 13N`, explicit numerals, no `O(·)` and no named constant.*** *An axiom can be
stated with any constant one likes; a proof cannot. The `13` is where the difference
between assuming and proving becomes visible to a reader.*

## Direction and scope

**Direction: SAME PROPOSITION** — `analytic_LS`'s `expSum` and `Spaced` are unfolded to
the exponential sum and the circle-separation condition they abbreviate, so nothing but
mathlib primitives remains; `char_LS` is already primitive and is restated verbatim.
Nothing is strengthened.

⚠️ **NOT CLAIMED.** These are the *inequalities*. Bombieri–Vinogradov itself is a
separate landed rung and is not certified here; nor is any statement about what other
projects do or do not assume — that is the anchor's sentence, not a theorem.

## Axioms

MEASURED at the landing (`#print axioms` below), not asserted.
-/

open Salt.LS

namespace Salt.Certs

/-- ⭐ **THE ANALYTIC LARGE SIEVE, FULLY UNFOLDED.** For points `α` that are `δ`-separated
on the circle `ℝ/ℤ` (with `0 < δ ≤ 1/2`), the squared exponential sums at those points
total at most `(δ⁻¹ + 13N)` times the coefficients' energy.

**Both opaque names are gone**: `expSum N a α` is written as `∑_{n<N} aₙ e(nα)`, and
`Spaced δ α` as the separation condition `δ ≤ dist₁ (α r) (α s)` for `r ≠ s`. -/
theorem cert_analytic_large_sieve {R N : ℕ} {δ : ℝ} {α : Fin R → ℝ} (a : ℕ → ℂ)
    (hsp : ∀ r s, r ≠ s → δ ≤ dist₁ (α r) (α s)) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∑ r, ‖∑ n ∈ Finset.range N, a n * e (n * α r)‖ ^ 2
      ≤ (δ⁻¹ + 13 * N) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 :=
  analytic_LS a hsp hδ hδ2

/-- ⛔ **RULE 6 — WITNESS KIND: NON-DEGENERACY** (declared per the council amendment of
2026-08-12; `saltworks/docs/cert-layer-design-0811.md`, rule 6).

**What this witness proves:** not merely that the spacing hypothesis is inhabited, but that
it is inhabited by a point where the hypothesis has CONTENT. *This is the amendment's exact
case, and the degenerate point is real rather than hypothetical: at `R = 1` the condition
`∀ r s, r ≠ s → …` holds vacuously — there is no pair to test — so a satisfiability witness
could discharge rule 6 while certifying nothing.* **The witness therefore uses `R = 2`: two
genuinely separated points `{0, 1/2}` at the extreme admissible `δ = 1/2`.**

*Recorded because the amendment postdates this file: the non-degeneracy reasoning was
already here, but the KIND was not declared, and "every cert must say what its witness
proves" is a claim about the docstring, not about the witness.* -/
theorem cert_analytic_large_sieve_witness :
    ∃ (δ : ℝ) (α : Fin 2 → ℝ), (0 < δ) ∧ (δ ≤ 1/2) ∧
    (∀ r s, r ≠ s → δ ≤ dist₁ (α r) (α s)) := by
  refine ⟨1/2, ![0, 1/2], by norm_num, le_refl _, ?_⟩
  intro r s hrs
  fin_cases r <;> fin_cases s <;> simp_all [dist₁, round_eq] <;> norm_num

open Classical in
/-- ⭐ **THE CHARACTER LARGE SIEVE.** Summing over moduli `q ≤ Q` and primitive characters
mod `q`, weighted by `q/φ(q)`, the squared character sums total at most `(Q² + 13N)` times
the coefficients' energy.

*Already primitive — restated verbatim so the constant `Q² + 13N` sits beside the analytic
form's `δ⁻¹ + 13N` where a reader can compare them.* -/
theorem cert_char_large_sieve {N Q : ℕ} (hQ : 2 ≤ Q) (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 :=
  char_LS hQ c

/-- **RULE 6 — WITNESS KIND: SATISFIABILITY** (declared per the 2026-08-12 amendment).

**What this witness proves:** that the single hypothesis `2 ≤ Q` is inhabited, at `Q = 2`.
*That is all it proves, and the amendment's point is to say so rather than let a reader
assume more.* Recorded even though it is trivial: **"obviously satisfiable" is the
judgement the rule exists to replace.**

📏 **THE NON-DEGENERACY QUESTION, NOW MEASURED — it was never a judgement.** An earlier
version of this docstring flagged it as a sufficiency call and left it for a fresh head.
*That was the wrong classification: "how many primitive characters exist for `q ≤ 2`" is a
MEASUREMENT, and the two `example`s below settle it in the kernel.*

**Result: at `Q = 2` exactly ONE modulus contributes.** Level 1's trivial character *is*
primitive, and **no character mod 2 is primitive** — every `χ : DirichletCharacter ℂ 2` is
the trivial one (the unit group `(ZMod 2)ˣ` is trivial), whose conductor is `1 ≠ 2`.
*So the `q = 2` inner sum runs over an EMPTY filter and the `Q = 2` instance is the THIN
END of the range.*

⚖️ **The witness is kept at `Q = 2` and the thinness is RECORDED rather than hidden** —
the same disposition the fleet settled on for `cert_vaughan`: **forced is not
non-degenerate**, and a reader who reaches for the smallest admissible point should find
out here why it is thin instead of rediscovering it. *A reader wanting the inequality's
full shape should take a larger `Q`; **whether specific larger `q` contribute is NOT
measured here** and is not asserted.*

📌 **THAT REMAINING GAP IS ATTEMPTED AND PRICED, not merely flagged.** *After `Q = 2` turned
out to be a two-`decide` MEASUREMENT rather than the judgement I had filed it as, I tried the
same on the other side and it is genuinely harder: exhibiting a primitive character at some
`q ≥ 3` needs a concrete nontrivial character (mathlib supplies `ZMod.χ₄`, `χ₈` as
`MulChar _ ℤ`) transported into `ℂ`, plus a conductor computation — for `q = 4`, `conductor ∣
4` with `≠ 1` (else the character is trivial) and `≠ 2` (else it factors through the trivial
`(ZMod 2)ˣ`). **Class B at least, not a two-liner.** Recorded with its route so the next
reader inherits a price rather than an open question.*

**None of this is a soundness question —
`cert_char_large_sieve` holds for every `Q ≥ 2` either way.** -/
theorem cert_char_large_sieve_witness : (2 : ℕ) ≤ 2 := le_refl 2

/-- **THE `Q = 2` MEASUREMENT, part 1 — level 1 DOES contribute.** Its trivial character is
primitive, so `q = 1` is a live index of the outer sum. -/
theorem cert_char_large_sieve_level_one_primitive :
    DirichletCharacter.IsPrimitive (1 : DirichletCharacter ℂ 1) :=
  DirichletCharacter.isPrimitive_one_level_one

/-- **THE `Q = 2` MEASUREMENT, part 2 — level 2 does NOT.** Every character mod 2 is the
trivial one, since `(ZMod 2)ˣ` is trivial, and the trivial character's conductor is `1`;
primitivity at level 2 would need conductor `2`. *Hence the `q = 2` inner sum runs over an
empty filter, and `Q = 2` leaves exactly one contributing modulus.* -/
theorem cert_char_large_sieve_level_two_not_primitive (χ : DirichletCharacter ℂ 2) :
    ¬ DirichletCharacter.IsPrimitive χ := by
  intro h
  rw [DirichletCharacter.isPrimitive_def] at h
  have h1 : χ = 1 := by
    ext a
    have ha : a = 1 := Subsingleton.elim a 1
    subst ha
    simp
  rw [h1, DirichletCharacter.conductor_one] at h
  exact absurd h (by norm_num)

#print axioms cert_analytic_large_sieve
#print axioms cert_char_large_sieve
#print axioms cert_analytic_large_sieve_witness
#print axioms cert_char_large_sieve_witness
#print axioms cert_char_large_sieve_level_one_primitive
#print axioms cert_char_large_sieve_level_two_not_primitive

end Salt.Certs




set_option maxHeartbeats 2000000 in
/-- The analytic large sieve, with Salt's `e` and `dist₁` unfolded to their Mathlib forms.
The bridge is done by rewriting the definitions rather than left to `isDefEq`, which times out. -/
theorem solution {R N : ℕ} {δ : ℝ} {α : Fin R → ℝ} (a : ℕ → ℂ)
    (hsp : ∀ r s, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∑ r, ‖∑ n ∈ Finset.range N,
        a n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℝ) * α r))‖ ^ 2
      ≤ (δ⁻¹ + 13 * N) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  have hsp' : ∀ r s, r ≠ s → δ ≤ Salt.LS.dist₁ (α r) (α s) := by
    intro r s h
    simpa [Salt.LS.dist₁] using hsp r s h
  simpa [Salt.LS.e] using Salt.Certs.cert_analytic_large_sieve a hsp' hδ hδ2
