-- Prove2me | solution 1 for NarrowDNF.ConditionalExpectation.squaredError_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:19:38.491492+00:00
-- url     : https://prove2.me/submissions/d8f1ee79-aeec-4ea2-919f-a990936ffc36

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Theorems.Thm_NarrowDNF_ConditionalExpectation_residual_orthogonal

namespace NarrowDNF.ConditionalExpectation
end NarrowDNF.ConditionalExpectation


noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ConditionalExpectation
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
/-- Exact weighted Pythagorean identity for finite conditional expectation. -/
theorem solution (φ : α → β) (w F : α → ℝ)
    (hw : ∀ a, 0 < w a) (G : β → ℝ) :
    squaredError w F (fun a => G (φ a)) =
      squaredError w F (conditional φ w F) +
        squaredError w (conditional φ w F) (fun a => G (φ a)) := by
  have horth := residual_orthogonal φ w F hw (fun b => mean φ w F b - G b)
  have hpoint (a : α) :
      w a * (F a - G (φ a))^2 =
        w a * (F a - conditional φ w F a)^2 +
          w a * (conditional φ w F a - G (φ a))^2 +
            2 * (w a * (F a - conditional φ w F a) *
              (mean φ w F (φ a) - G (φ a))) := by
    unfold conditional
    ring
  unfold squaredError
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [horth, mul_zero, add_zero]
