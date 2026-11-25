-- Prove2me | solution 1 for Kyprianou.Ch04.bvFiniteJumpInsertMaxIntegralLedgerV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:16:07.82632+00:00
-- url     : https://prove2.me/submissions/69fe1507-dfcd-42e7-90b1-de3a5a149545

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpDerivativeIntervalIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_bvAffineDerivativeIntervalIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_bvAffineSegmentChainRuleV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpAfterMaxAffineV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (S : Finset I) (k : I) (hk : ∀ s ∈ S, s < k)
    (T : ℝ) (hk0 : 0 < τ k) (hkT : τ k ≤ T) (hpos : ∀ s ∈ S, 0 < τ s) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    (∫ u in 0..T, fderiv ℝ f (u, P (insert k S) u) (1,d)) =
      (∫ u in 0..τ k, fderiv ℝ f (u, P S u) (1,d)) +
      (f (T, P (insert k S) T) - f (τ k, P (insert k S) (τ k))) := by
  classical
  let P : Finset I → ℝ → ℝ :=
    fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
  let D (R : Finset I) (u : ℝ) := fderiv ℝ f (u, P R u) (1,d)
  change (∫ u in 0..T, D (insert k S) u) =
    (∫ u in 0..τ k, D S u) +
    (f (T, P (insert k S) T) - f (τ k, P (insert k S) (τ k)))
  have hkn : k ∉ S := fun hs => (lt_irrefl k) (hk k hs)
  have hi : IntervalIntegrable (D S) volume 0 (τ k) :=
    Kyprianou.Ch04.bvFiniteJumpDerivativeIntervalIntegrableV1
      τ hτ j a d f hf (1,d) S (τ k) hk0.le hpos
      (fun s hs => (hτ (hk s hs)).le)
  have hleft : Set.EqOn (D S) (D (insert k S)) (Ioo 0 (τ k)) := by
    intro u hu
    simp [D, P, Finset.sum_insert hkn, not_le_of_gt hu.2]
  let b := a + ∑ s ∈ insert k S, j s
  have hP (u : ℝ) (hu : τ k ≤ u) : P (insert k S) u = b + d * u :=
    Kyprianou.Ch04.bvFiniteJumpAfterMaxAffineV1 τ hτ j a d S k hk u hu
  have hright : Set.EqOn (fun u => fderiv ℝ f (u,b+d*u) (1,d))
      (D (insert k S)) (Ioo (τ k) T) := by
    intro u hu
    simp only [D, hP u hu.1.le]
  have h1 := hi.congr_uIoo (by rwa [uIoo_of_le hk0.le])
  have h2 := (Kyprianou.Ch04.bvAffineDerivativeIntervalIntegrableV1
      f hf b d (τ k) T hk0.le hkT (1,d)).congr_uIoo
        (by rwa [uIoo_of_le hkT])
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    ← intervalIntegral.integral_congr_Ioo_of_le hk0.le hleft,
    ← intervalIntegral.integral_congr_Ioo_of_le hkT hright,
    ← Kyprianou.Ch04.bvAffineSegmentChainRuleV1 f hf b d (τ k) T hk0.le hkT,
    hP T hkT, hP (τ k) le_rfl]
