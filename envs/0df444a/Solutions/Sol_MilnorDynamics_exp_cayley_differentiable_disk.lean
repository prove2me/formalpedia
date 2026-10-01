-- Prove2me | solution 1 for MilnorDynamics.exp_cayley_differentiable_disk
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T03:20:32.237572+00:00
-- url     : https://prove2.me/submissions/87cf84eb-4629-43ce-9861-2d9f8cf4697f

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

-- Proof of `MilnorDynamics.exp_cayley_differentiable_disk`
-- (`8bb64d78-351c-4e64-a93c-9ae05a2150d1`).
--
-- Claim: `z ↦ Complex.exp ((z + 1) / (1 - z))` is complex differentiable on the open
-- unit disc.
--
-- This is a pure composition argument, with no modular theory:
--
--   * `z ↦ z + 1` and `z ↦ 1 - z` are differentiable everywhere
--     (`DifferentiableAt.add_const`, `DifferentiableAt.const_sub`);
--   * the quotient is differentiable wherever `1 - z ≠ 0`
--     (`DifferentiableAt.div`), and `1 - z = 0` forces `z = 1`, whose norm is `1`,
--     so it cannot happen on the disc;
--   * `Complex.exp` is differentiable everywhere.
--
-- The quotient and the exponential are built with the explicit `DifferentiableAt`
-- lemmas rather than `fun_prop`, because `fun_prop` proves differentiability of a
-- quotient only from a `Fact` about the denominator, and the nonzero fact here is
-- derived inside the proof rather than available to the tactic.

open scoped OnePoint
open Filter Set
open MilnorDynamics

theorem solution :
    DifferentiableOn ℂ (fun z : ℂ => Complex.exp ((z + 1) / (1 - z))) (Metric.ball 0 1) := by
  intro z hz
  have hnorm : ‖z‖ < 1 := by simpa using hz
  -- `1 - z ≠ 0`, since that would force `z = 1`, whose norm is `1`.
  have hden : ((1 : ℂ) - z) ≠ 0 := by
    intro hc
    have hz1 : z = (1 : ℂ) := (sub_eq_zero.mp hc).symm
    rw [hz1, norm_one] at hnorm
    exact (by norm_num : ¬ ((1 : ℝ) < 1)) hnorm
  have hquot : DifferentiableAt ℂ (fun w : ℂ => (w + 1) / (1 - w)) z := by
    exact ((differentiableAt_id (𝕜 := ℂ)).add_const (1 : ℂ)).div
      ((differentiableAt_id (𝕜 := ℂ)).const_sub (1 : ℂ)) hden
  -- `.cexp`, not `.exp`: the latter is `Real.exp`'s lemma
  -- (Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:366), while the complex one is
  -- `DifferentiableAt.cexp` (same file, line 175).
  -- The goal is `DifferentiableWithinAt ℂ … (Metric.ball 0 1) z`, because
  -- `DifferentiableOn f s` is *defined* as `∀ x ∈ s, DifferentiableWithinAt 𝕜 f s x`
  -- (Mathlib/Analysis/Calculus/FDeriv/Defs.lean:163). A bare `DifferentiableAt` does not
  -- fit; the first version failed with
  --   term `DifferentiableAt.cexp hquot` has type
  --     `DifferentiableAt ℂ (fun x => Complex.exp ((x + 1) / (1 - x))) z`
  --   but is expected to have type
  --     `DifferentiableWithinAt ℂ … (Metric.ball 0 1) z`
  -- so `.differentiableWithinAt` supplies the missing restriction to the set.
  exact hquot.cexp.differentiableWithinAt
