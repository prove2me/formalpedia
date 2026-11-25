-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzFiniteJumpMaxIntegralLedgerV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:37:00.584982+00:00
-- url     : https://prove2.me/submissions/cac605bd-5760-41e3-8833-512a5f804f9e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpAfterMaxAffineV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineSegmentChainV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Insert the final jump: the Lipschitz-coordinate continuous integral
splits into the old left integral and the affine right segment. -/
theorem solution
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (U : ℝ → ℝ) (K : ℝ≥0) (hULip : LipschitzWith K U)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (S : Finset I) (k : I) (hk : ∀ s ∈ S, s < k)
    (T : ℝ) (hk0 : 0 < τ k) (hkT : τ k ≤ T)
    (hNonneg : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ U s)
    (hPositive : ∀ s ∈ Ioc (0 : ℝ) T, 0 < U s) :
    let P : Finset I → ℝ → ℝ :=
      fun R u => a + d * u + ∑ s ∈ R, if τ s ≤ u then j s else 0
    let D : Finset I → ℝ → ℝ :=
      fun R u => fderiv ℝ f (U u, P R u) (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, P R u) (0, 1)
    IntervalIntegrable (D S) volume 0 (τ k) →
    IntervalIntegrable (fun u =>
      fderiv ℝ f (U u, (a + ∑ s ∈ insert k S, j s) + d * u)
        (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, (a + ∑ s ∈ insert k S, j s) + d * u)
          (0, 1)) volume (τ k) T →
    (∫ u in 0..T, D (insert k S) u) =
      (∫ u in 0..τ k, D S u) +
      (f (U T, P (insert k S) T) -
        f (U (τ k), P (insert k S) (τ k))) := by
  classical
  let P : Finset I → ℝ → ℝ :=
    fun R u => a + d * u + ∑ s ∈ R, if τ s ≤ u then j s else 0
  let D : Finset I → ℝ → ℝ :=
    fun R u => fderiv ℝ f (U u, P R u) (1, 0) * deriv U u +
      d * fderiv ℝ f (U u, P R u) (0, 1)
  let b : ℝ := a + ∑ s ∈ insert k S, j s
  change IntervalIntegrable (D S) volume 0 (τ k) →
    IntervalIntegrable (fun u =>
      fderiv ℝ f (U u, b + d * u) (1, 0) * deriv U u +
      d * fderiv ℝ f (U u, b + d * u) (0, 1)) volume (τ k) T →
    (∫ u in 0..T, D (insert k S) u) =
      (∫ u in 0..τ k, D S u) +
      (f (U T, P (insert k S) T) -
        f (U (τ k), P (insert k S) (τ k)))
  intro hi hpost
  have hkn : k ∉ S := fun hs => (lt_irrefl k) (hk k hs)
  have hleft : EqOn (D S) (D (insert k S)) (Ioo 0 (τ k)) := by
    intro u hu
    simp [D, P, Finset.sum_insert hkn, not_le_of_gt hu.2]
  have hP (u : ℝ) (hu : τ k ≤ u) : P (insert k S) u = b + d * u :=
    Kyprianou.Ch04.bvFiniteJumpAfterMaxAffineV1 τ hτ j a d S k hk u hu
  have hright :
      EqOn (fun u =>
        fderiv ℝ f (U u, b + d * u) (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, b + d * u) (0, 1))
        (D (insert k S)) (Ioo (τ k) T) := by
    intro u hu
    simp only [D, hP u hu.1.le]
  have hNonnegRight : ∀ s ∈ Icc (τ k) T, 0 ≤ U s := by
    intro s hs
    exact hNonneg s ⟨hk0.le.trans hs.1, hs.2⟩
  have hPositiveRight : ∀ s ∈ Ioc (τ k) T, 0 < U s := by
    intro s hs
    exact hPositive s ⟨lt_of_le_of_lt hk0.le hs.1, hs.2⟩
  have hSeg := Kyprianou.Ch04.exercise42LipschitzAffineSegmentChainV1
    f hf U K hULip b d (τ k) T hkT hNonnegRight hPositiveRight
  have h1 := hi.congr_uIoo (by rwa [uIoo_of_le hk0.le])
  have h2 := hpost.congr_uIoo (by rwa [uIoo_of_le hkT])
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    ← intervalIntegral.integral_congr_Ioo_of_le hk0.le hleft,
    ← intervalIntegral.integral_congr_Ioo_of_le hkT hright,
    ← hSeg, hP T hkT, hP (τ k) le_rfl]
