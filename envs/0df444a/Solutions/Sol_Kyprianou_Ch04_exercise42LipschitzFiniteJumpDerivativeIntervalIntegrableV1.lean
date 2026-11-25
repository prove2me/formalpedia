-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzFiniteJumpDerivativeIntervalIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:49:25.905968+00:00
-- url     : https://prove2.me/submissions/05a90bba-a884-458f-a8e2-93af74ad0a46

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineDerivativeIntervalIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpAfterMaxAffineV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A Lipschitz-coordinate chain-rule derivative with finitely many jumps
is interval integrable on each compact interval. -/
theorem solution
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (U : ℝ → ℝ) (K : ℝ≥0) (hULip : LipschitzWith K U)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ)) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ S, 0 < τ s) → (∀ s ∈ S, τ s ≤ T) →
      (∀ s ∈ Icc (0 : ℝ) T, 0 ≤ U s) →
      (∀ s ∈ Ioc (0 : ℝ) T, 0 < U s) →
      IntervalIntegrable (fun u =>
        fderiv ℝ f (U u, P S u) (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, P S u) (0, 1)) volume 0 T := by
  classical
  let P : Finset I → ℝ → ℝ :=
    fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
  change ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ S, 0 < τ s) → (∀ s ∈ S, τ s ≤ T) →
      (∀ s ∈ Icc (0 : ℝ) T, 0 ≤ U s) →
      (∀ s ∈ Ioc (0 : ℝ) T, 0 < U s) →
      IntervalIntegrable (fun u =>
        fderiv ℝ f (U u, P S u) (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, P S u) (0, 1)) volume 0 T
  intro S
  induction S using Finset.induction_on_max with
  | empty =>
    intro T hT _ _ hN hPos
    simpa [P] using
      Kyprianou.Ch04.exercise42LipschitzAffineDerivativeIntervalIntegrableV1
        f hf U K hULip a d 0 T hT hN hPos
  | insert k S hk ih =>
    intro T hT hp ht hN hPos
    have hkn : k ∉ S := fun hs => (lt_irrefl k) (hk k hs)
    have hk0 := hp k (Finset.mem_insert_self k S)
    have hkT := ht k (Finset.mem_insert_self k S)
    have hNsmall : ∀ s ∈ Icc (0 : ℝ) (τ k), 0 ≤ U s :=
      fun s hs => hN s ⟨hs.1, hs.2.trans hkT⟩
    have hPsmall : ∀ s ∈ Ioc (0 : ℝ) (τ k), 0 < U s :=
      fun s hs => hPos s ⟨hs.1, hs.2.trans hkT⟩
    have hi := ih (τ k) hk0.le
      (fun s hs => hp s (Finset.mem_insert_of_mem hs))
      (fun s hs => (hτ (hk s hs)).le) hNsmall hPsmall
    have hleft : IntervalIntegrable
        (fun u => fderiv ℝ f (U u, P (insert k S) u) (1, 0) * deriv U u +
          d * fderiv ℝ f (U u, P (insert k S) u) (0, 1))
        volume 0 (τ k) := by
      apply hi.congr_uIoo
      rw [uIoo_of_le hk0.le]
      intro u hu
      simp [P, Finset.sum_insert hkn, not_le_of_gt hu.2]
    let b := a + ∑ s ∈ insert k S, j s
    have hNright : ∀ s ∈ Icc (τ k) T, 0 ≤ U s :=
      fun s hs => hN s ⟨hk0.le.trans hs.1, hs.2⟩
    have hPright : ∀ s ∈ Ioc (τ k) T, 0 < U s :=
      fun s hs => hPos s ⟨lt_of_le_of_lt hk0.le hs.1, hs.2⟩
    have hj := Kyprianou.Ch04.exercise42LipschitzAffineDerivativeIntervalIntegrableV1
      f hf U K hULip b d (τ k) T hkT hNright hPright
    have hright : IntervalIntegrable
        (fun u => fderiv ℝ f (U u, P (insert k S) u) (1, 0) * deriv U u +
          d * fderiv ℝ f (U u, P (insert k S) u) (0, 1))
        volume (τ k) T := by
      apply hj.congr_uIoo
      rw [uIoo_of_le hkT]
      intro u hu
      have hpu : P (insert k S) u = b + d * u :=
        Kyprianou.Ch04.bvFiniteJumpAfterMaxAffineV1
          τ hτ j a d S k hk u hu.1.le
      simp only [hpu]
    exact hleft.trans hright
