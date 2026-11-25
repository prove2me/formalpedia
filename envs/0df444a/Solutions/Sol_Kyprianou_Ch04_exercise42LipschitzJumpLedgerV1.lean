-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzJumpLedgerV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:34:25.09588+00:00
-- url     : https://prove2.me/submissions/3cbb3e08-43d0-4bf1-9371-4f5382a46b6c

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpInsertMaxJumpLedgerV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (U : ℝ → ℝ) (f : ℝ × ℝ → ℝ)
    (S : Finset I) (k : I) (hk : ∀ s ∈ S, s < k) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    let Q : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s < u then j s else 0
    (∑ s ∈ insert k S, (f (U (τ s), P (insert k S) (τ s)) -
        f (U (τ s), Q (insert k S) (τ s)))) =
      f (U (τ k), P (insert k S) (τ k)) -
        f (U (τ k), P S (τ k)) +
      ∑ s ∈ S, (f (U (τ s), P S (τ s)) -
        f (U (τ s), Q S (τ s))) := by
  let F : ℝ × ℝ → ℝ := fun z => f (U z.1, z.2)
  have h := Kyprianou.Ch04.bvFiniteJumpInsertMaxJumpLedgerV1
    τ hτ j a d F S k hk
  simpa only [F] using h