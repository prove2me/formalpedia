-- Prove2me | solution 1 for Kyprianou.Ch04.bvFiniteJumpDerivativeIntervalIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:16:05.793312+00:00
-- url     : https://prove2.me/submissions/f849d53c-0da7-4987-9cd7-877910fe0b56

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvAffineDerivativeIntervalIntegrableV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ)) (v : ℝ × ℝ) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ S, 0 < τ s) → (∀ s ∈ S, τ s ≤ T) →
      IntervalIntegrable (fun u => fderiv ℝ f (u, P S u) v) volume 0 T := by
  classical
  let P : Finset I → ℝ → ℝ :=
    fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
  change ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
    (∀ s ∈ S, 0 < τ s) → (∀ s ∈ S, τ s ≤ T) →
    IntervalIntegrable (fun u => fderiv ℝ f (u, P S u) v) volume 0 T
  intro S
  induction S using Finset.induction_on_max with
  | empty =>
    intro T hT _ _
    simpa [P] using Kyprianou.Ch04.bvAffineDerivativeIntervalIntegrableV1 f hf a d 0 T le_rfl hT v
  | insert k S hk ih =>
    intro T hT hpos htop
    have hkn : k ∉ S := fun hm => (lt_irrefl k) (hk k hm)
    have hk0 := hpos k (Finset.mem_insert_self k S)
    have hkT := htop k (Finset.mem_insert_self k S)
    have hi := ih (τ k) hk0.le
      (fun s hs => hpos s (Finset.mem_insert_of_mem hs))
      (fun s hs => (hτ (hk s hs)).le)
    have hleft : IntervalIntegrable
        (fun u => fderiv ℝ f (u, P (insert k S) u) v) volume 0 (τ k) := by
      apply hi.congr_uIoo
      rw [uIoo_of_le hk0.le]
      intro u hu
      simp [P, Finset.sum_insert hkn, not_le_of_gt hu.2]
    let b := a + ∑ s ∈ insert k S, j s
    have hj := Kyprianou.Ch04.bvAffineDerivativeIntervalIntegrableV1 f hf b d (τ k) T hk0.le hkT v
    have hright : IntervalIntegrable
        (fun u => fderiv ℝ f (u, P (insert k S) u) v) volume (τ k) T := by
      apply hj.congr_uIoo
      rw [uIoo_of_le hkT]
      intro u hu
      have hsum : (∑ s ∈ insert k S, if τ s ≤ u then j s else 0) =
          ∑ s ∈ insert k S, j s := by
        apply Finset.sum_congr rfl
        intro s hs
        have hsk : τ s ≤ τ k := by
          rcases Finset.mem_insert.mp hs with rfl | hs'
          · exact le_rfl
          · exact (hτ (hk s hs')).le
        simp [hsk.trans hu.1.le]
      have hp : P (insert k S) u = b + d * u := by
        simp only [P, b, hsum]
        ring
      change fderiv ℝ f (u, b + d * u) v = fderiv ℝ f (u, P (insert k S) u) v
      rw [hp]
    exact hleft.trans hright
