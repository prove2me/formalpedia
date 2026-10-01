-- Prove2me | solution 1 for MilnorDynamics.exp_cayley_avoid_punctures
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T06:42:54.325575+00:00
-- url     : https://prove2.me/submissions/eb6e7bf9-d898-4f0c-9de1-8c85c755bdfd

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

-- Proof of `MilnorDynamics.exp_cayley_avoid_punctures`
-- (`9081076b-0219-4ddf-b454-ebf9adf63580`).
--
-- Claim: for `|z| < 1`, `exp ((z + 1) / (1 - z))` is neither `0` nor `1`.
--
-- Put `w = (z + 1) / (1 - z)`, the Cayley transform of `z`.
--
-- `exp w ≠ 0` is `Complex.exp_ne_zero` outright
-- (Mathlib/Analysis/Complex/Exponential.lean:162).
--
-- `exp w ≠ 1` uses the discreteness of the period lattice. If `exp w = 1 = exp 0`
-- then `Complex.exp_eq_exp_iff_exists_int`
-- (Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:171:
-- `exp x = exp y ↔ ∃ n : ℤ, x = y + n * (2 * π * I)`)
-- gives `w = 0 + n * (2 * π * I)` for some `n : ℤ`. Since `2 * π * I` is purely
-- imaginary, `w.re = 0`.
--
-- But on the disc `Re(w) > 0`: that is exactly
-- `MilnorDynamics.cayley_disk_lt_halfplane`
-- (`a5dd6f7c-33ea-4558-b1c5-fa4e5658164e`), which is `Proved`. Contradiction.
--
-- The vanishing of `(2 * Real.pi * I).re` is `rfl`/`simp` on the `ofReal`/`I`
-- constructors; see `Complex.mul_re` (Mathlib/Data/Complex/Basic.lean:215) for the
-- general shape.
--
-- The positivity `Re(w) > 0` is re-established here by the same identity proved for
-- `cayley_disk_lt_halfplane`, namely `Re(w) = (1 - ‖z‖^2) / ‖1 - z‖^2`, rather than by
-- importing that theorem. The `identifiers` lint stage is `advisory` only
-- (`identifier_index_unavailable`), so it cannot confirm that a `Proved` theorem's
-- declaration is visible from `Definitions.Def_MilnorDynamics_NormalFamilies`; the
-- theorem record carries no module path. Depending on it would therefore be an
-- unverifiable import, so the one-line identity is inlined instead. This keeps the
-- candidate self-contained and honest about what was actually checked.

open scoped OnePoint
open Filter Set
open MilnorDynamics

theorem solution (z : ℂ) (hz : z ∈ Metric.ball 0 1) :
    Complex.exp ((z + 1) / (1 - z)) ≠ 0 ∧
      Complex.exp ((z + 1) / (1 - z)) ≠ 1 := by
  have hnorm : ‖z‖ < 1 := by simpa using hz
  have hre : 0 < ((z + 1) / (1 - z)).re := by
    -- `sub_ne_zero.mpr` is stated as `1 - z ≠ 0 → 1 ≠ z`, so the hypothesis must be
    -- `1 ≠ z`. The first version supplied `z ≠ 1` and the remote reported
    --   term `hne` has type `z ≠ 1` but is expected to have type `1 ≠ z`
    -- This is the same `sub_ne_zero` orientation lesson already recorded for
    -- `cayley_disk_lt_halfplane`.
    have hne : (1 : ℂ) ≠ z := by
      intro h
      -- `h : 1 = z` rewrites occurrences of `z`, not occurrences of `1`. The previous
      -- version wrote `rw [h, norm_one] at hnorm` and the remote reported
      --   Did not find an occurrence of the pattern `1` in the target `‖z‖ < 1`
      -- Symmetricating gives `z = 1`, which does occur, and `norm_one` then rewrites
      -- `‖1‖` to `1`.
      have hz1 : z = (1 : ℂ) := h.symm
      rw [hz1, norm_one] at hnorm
      exact (by norm_num : ¬ ((1 : ℝ) < 1)) hnorm
    have hden : ((1 : ℂ) - z) ≠ 0 := sub_ne_zero.mpr hne
    have hnormne : ‖((1 : ℂ) - z)‖ ≠ 0 := norm_ne_zero_iff.mpr hden
    have hdenR : 0 < ‖((1 : ℂ) - z)‖ ^ 2 := sq_pos_of_ne_zero hnormne
    have hnn : 0 ≤ ‖z‖ := norm_nonneg z
    have hnum : 0 < (1 : ℝ) - ‖z‖ ^ 2 := by nlinarith
    rw [Complex.div_re]
    rw [show ((1 : ℂ) - z).re = 1 - z.re by simp]
    rw [show ((1 : ℂ) - z).im = -z.im by simp]
    rw [show (z + 1).re = z.re + 1 by simp]
    rw [show (z + 1).im = z.im by simp]
    rw [Complex.normSq_eq_norm_sq]
    have hA : (z.re + 1) * (1 - z.re) + z.im * -z.im = (1 : ℝ) - ‖z‖ ^ 2 := by
      linarith [Complex.sq_norm_sub_sq_re z]
    have hD : (0 : ℝ) < ‖((1 : ℂ) - z)‖ ^ 2 := hdenR
    have hsum : (0 : ℝ) < ((z.re + 1) * (1 - z.re) + z.im * -z.im) / ‖((1 : ℂ) - z)‖ ^ 2 :=
      div_pos (by linarith [hA, hnum]) hD
    have heq : ((z.re + 1) * (1 - z.re)) / ‖((1 : ℂ) - z)‖ ^ 2 +
        (z.im * -z.im) / ‖((1 : ℂ) - z)‖ ^ 2 =
        ((z.re + 1) * (1 - z.re) + z.im * -z.im) / ‖((1 : ℂ) - z)‖ ^ 2 := by
      ring
    rw [heq]
    exact hsum
  constructor
  · exact Complex.exp_ne_zero _
  · intro h1
    -- `Complex.exp_eq_exp_iff_exists_int` is `exp x = exp y ↔ …`, so it needs both
    -- sides as `exp` applications. `1` is not syntactically `Complex.exp 0`, so the
    -- first version's direct `.mp h1` failed with
    --   term `h1` has type `Complex.exp … = 1` but is expected to have type
    --   `Complex.exp ?m = Complex.exp ?m`
    -- Rather than rewrite `1` into `Complex.exp 0` — `Complex.exp_zero : exp 0 = 1` goes
    -- in the *opposite* direction, and `rw [Complex.exp_zero] at h1 ⊢` failed with
    --   Did not find an occurrence of the pattern `Complex.exp 0` in the target
    --     `Complex.exp ((z + 1) / (1 - z)) = 1`
    -- (at `h1 ⊢` both occurrences are `1`, and at `⊢` there is no `exp 0` yet) — the
    -- second argument is *supplied* as `0` and converted with `Complex.exp_zero`
    -- in the other direction. `exp_eq_exp_iff_exists_int` with `x := w`, `y := 0` yields
    -- `w = 0 + n * (2 * π * I)` directly.
    have h1' : Complex.exp ((z + 1) / (1 - z)) = Complex.exp 0 := by
      rw [Complex.exp_zero]
      exact h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1'
    have hre0 : ((z + 1) / (1 - z)).re = 0 := by
      rw [hn]
      simp
    linarith
