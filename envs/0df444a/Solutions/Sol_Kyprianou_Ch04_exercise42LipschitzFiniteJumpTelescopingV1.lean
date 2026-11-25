-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzFiniteJumpTelescopingV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:45:57.151222+00:00
-- url     : https://prove2.me/submissions/445efc96-84f6-4a65-8dd5-5d84e1a1b803

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineSegmentChainV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzJumpLedgerV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpMaxIntegralLedgerV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Induction on the final jump yields the finite-jump formula for the
original, fixed Lipschitz first coordinate. -/
theorem solution
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (U : ℝ → ℝ) (K : ℝ≥0) (hULip : LipschitzWith K U)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ)) :
    let P : Finset I → ℝ → ℝ :=
      fun R u => a + d * u + ∑ s ∈ R, if τ s ≤ u then j s else 0
    let Q : Finset I → ℝ → ℝ :=
      fun R u => a + d * u + ∑ s ∈ R, if τ s < u then j s else 0
    let D : Finset I → ℝ → ℝ :=
      fun R u => fderiv ℝ f (U u, P R u) (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, P R u) (0, 1)
    (∀ (R : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ Icc (0 : ℝ) T, 0 ≤ U s) →
      (∀ s ∈ Ioc (0 : ℝ) T, 0 < U s) →
      IntervalIntegrable (D R) volume 0 T) →
    (∀ (b l r : ℝ), 0 ≤ l → l ≤ r →
      (∀ s ∈ Icc l r, 0 ≤ U s) →
      (∀ s ∈ Ioc l r, 0 < U s) →
      IntervalIntegrable (fun u =>
        fderiv ℝ f (U u, b + d * u) (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, b + d * u) (0, 1)) volume l r) →
    ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ S, 0 < τ s) →
      (∀ s ∈ S, τ s ≤ T) →
      (∀ s ∈ Icc (0 : ℝ) T, 0 ≤ U s) →
      (∀ s ∈ Ioc (0 : ℝ) T, 0 < U s) →
      f (U T, P S T) = f (U 0, a) +
        (∫ u in 0..T, D S u) +
        ∑ s ∈ S, (f (U (τ s), P S (τ s)) -
          f (U (τ s), Q S (τ s))) := by
  classical
  let P : Finset I → ℝ → ℝ :=
    fun R u => a + d * u + ∑ s ∈ R, if τ s ≤ u then j s else 0
  let Q : Finset I → ℝ → ℝ :=
    fun R u => a + d * u + ∑ s ∈ R, if τ s < u then j s else 0
  let D : Finset I → ℝ → ℝ :=
    fun R u => fderiv ℝ f (U u, P R u) (1, 0) * deriv U u +
      d * fderiv ℝ f (U u, P R u) (0, 1)
  change (∀ (R : Finset I) (T : ℝ), 0 ≤ T →
    (∀ s ∈ Icc (0 : ℝ) T, 0 ≤ U s) →
    (∀ s ∈ Ioc (0 : ℝ) T, 0 < U s) →
    IntervalIntegrable (D R) volume 0 T) →
    (∀ (b l r : ℝ), 0 ≤ l → l ≤ r →
      (∀ s ∈ Icc l r, 0 ≤ U s) →
      (∀ s ∈ Ioc l r, 0 < U s) →
      IntervalIntegrable (fun u =>
        fderiv ℝ f (U u, b + d * u) (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, b + d * u) (0, 1)) volume l r) →
    ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ S, 0 < τ s) → (∀ s ∈ S, τ s ≤ T) →
      (∀ s ∈ Icc (0 : ℝ) T, 0 ≤ U s) →
      (∀ s ∈ Ioc (0 : ℝ) T, 0 < U s) →
      f (U T, P S T) = f (U 0, a) +
        (∫ u in 0..T, D S u) +
        ∑ s ∈ S, (f (U (τ s), P S (τ s)) -
          f (U (τ s), Q S (τ s)))
  intro hIntAll hIntAffine S
  induction S using Finset.induction_on_max with
  | empty =>
    intro T hT _ _ hN hPos
    have hSeg := Kyprianou.Ch04.exercise42LipschitzAffineSegmentChainV1
      f hf U K hULip a d 0 T hT hN hPos
    simp [P, Q, D] at hSeg ⊢
    linarith
  | insert k S hk ih =>
    intro T hT hp ht hN hPos
    have hk0 := hp k (Finset.mem_insert_self k S)
    have hkT := ht k (Finset.mem_insert_self k S)
    have hs : ∀ s ∈ S, 0 < τ s := fun s hs => hp s (Finset.mem_insert_of_mem hs)
    have hst : ∀ s ∈ S, τ s ≤ τ k := fun s hs => (hτ (hk s hs)).le
    have hNsmall : ∀ s ∈ Icc (0 : ℝ) (τ k), 0 ≤ U s :=
      fun s hs' => hN s ⟨hs'.1, hs'.2.trans hkT⟩
    have hPsmall : ∀ s ∈ Ioc (0 : ℝ) (τ k), 0 < U s :=
      fun s hs' => hPos s ⟨hs'.1, hs'.2.trans hkT⟩
    have hNright : ∀ s ∈ Icc (τ k) T, 0 ≤ U s :=
      fun s hs' => hN s ⟨hk0.le.trans hs'.1, hs'.2⟩
    have hPright : ∀ s ∈ Ioc (τ k) T, 0 < U s :=
      fun s hs' => hPos s ⟨lt_of_le_of_lt hk0.le hs'.1, hs'.2⟩
    have hold := ih (τ k) hk0.le hs hst hNsmall hPsmall
    let b := a + ∑ s ∈ insert k S, j s
    have hInt := Kyprianou.Ch04.exercise42LipschitzFiniteJumpMaxIntegralLedgerV1
      τ hτ j a d U K hULip f hf S k hk T hk0 hkT hN hPos
      (hIntAll S (τ k) hk0.le hNsmall hPsmall)
      (hIntAffine b (τ k) T hk0.le hkT hNright hPright)
    have hJump := Kyprianou.Ch04.exercise42LipschitzJumpLedgerV1 τ hτ j a d U f S k hk
    change (∫ u in 0..T, D (insert k S) u) =
      (∫ u in 0..τ k, D S u) +
      (f (U T, P (insert k S) T) -
        f (U (τ k), P (insert k S) (τ k))) at hInt
    change (∑ s ∈ insert k S,
        (f (U (τ s), P (insert k S) (τ s)) -
          f (U (τ s), Q (insert k S) (τ s)))) =
      f (U (τ k), P (insert k S) (τ k)) -
        f (U (τ k), P S (τ k)) +
      ∑ s ∈ S, (f (U (τ s), P S (τ s)) -
        f (U (τ s), Q S (τ s))) at hJump
    rw [hInt, hJump]; linarith
