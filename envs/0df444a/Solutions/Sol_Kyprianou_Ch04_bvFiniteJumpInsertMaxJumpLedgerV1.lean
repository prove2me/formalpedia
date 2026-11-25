-- Prove2me | solution 1 for Kyprianou.Ch04.bvFiniteJumpInsertMaxJumpLedgerV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:26:32.611248+00:00
-- url     : https://prove2.me/submissions/be65631f-91ad-42f2-a9c2-bba493b950d1

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (f : ℝ × ℝ → ℝ)
    (S : Finset I) (k : I) (hk : ∀ s ∈ S, s < k) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    let Q : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s < u then j s else 0
    (∑ s ∈ insert k S, (f (τ s, P (insert k S) (τ s)) -
        f (τ s, Q (insert k S) (τ s)))) =
      f (τ k, P (insert k S) (τ k)) - f (τ k, P S (τ k)) +
      ∑ s ∈ S, (f (τ s, P S (τ s)) - f (τ s, Q S (τ s))) := by
  classical
  let P : Finset I → ℝ → ℝ :=
    fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
  let Q : Finset I → ℝ → ℝ :=
    fun S u => a + d * u + ∑ s ∈ S, if τ s < u then j s else 0
  change (∑ s ∈ insert k S, (f (τ s, P (insert k S) (τ s)) -
      f (τ s, Q (insert k S) (τ s)))) =
    f (τ k, P (insert k S) (τ k)) - f (τ k, P S (τ k)) +
    ∑ s ∈ S, (f (τ s, P S (τ s)) - f (τ s, Q S (τ s)))
  have hkn : k ∉ S := fun hs => (lt_irrefl k) (hk k hs)
  have hpre : Q (insert k S) (τ k) = P S (τ k) := by
    simp only [Q, P, Finset.sum_insert hkn, lt_irrefl, if_false, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    have hh := hτ (hk s hs)
    simp [hh, hh.le]
  rw [Finset.sum_insert hkn, hpre]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hh := hτ (hk s hs)
  simp [P, Q, Finset.sum_insert hkn, not_le_of_gt hh, not_lt_of_ge hh.le]
