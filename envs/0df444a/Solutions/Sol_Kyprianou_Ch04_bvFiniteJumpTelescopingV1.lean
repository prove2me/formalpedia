-- Prove2me | solution 1 for Kyprianou.Ch04.bvFiniteJumpTelescopingV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:16:06.869901+00:00
-- url     : https://prove2.me/submissions/21da5818-a205-45f4-a950-dd8c048f5d47

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvAffineSegmentChainRuleV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpInsertMaxIntegralLedgerV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpInsertMaxJumpLedgerV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ)) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    let Q : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s < u then j s else 0
    ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ S, 0 < τ s) → (∀ s ∈ S, τ s ≤ T) →
      f (T,P S T) = f (0,a) +
        (∫ u in 0..T, fderiv ℝ f (u,P S u) (1,d)) +
        ∑ s ∈ S, (f (τ s,P S (τ s)) - f (τ s,Q S (τ s))) := by
  classical
  let P : Finset I → ℝ → ℝ :=
    fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
  let Q : Finset I → ℝ → ℝ :=
    fun S u => a + d * u + ∑ s ∈ S, if τ s < u then j s else 0
  change ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
    (∀ s ∈ S, 0 < τ s) → (∀ s ∈ S, τ s ≤ T) →
    f (T,P S T) = f (0,a) +
      (∫ u in 0..T, fderiv ℝ f (u,P S u) (1,d)) +
      ∑ s ∈ S, (f (τ s,P S (τ s)) - f (τ s,Q S (τ s)))
  intro S
  induction S using Finset.induction_on_max with
  | empty =>
    intro T hT _ _
    have h := Kyprianou.Ch04.bvAffineSegmentChainRuleV1 f hf a d 0 T le_rfl hT
    simp [P, Q] at h ⊢
    linarith
  | insert k S hk ih =>
    intro T hT hp ht
    have hk0 := hp k (Finset.mem_insert_self k S)
    have hkT := ht k (Finset.mem_insert_self k S)
    have hs : ∀ s ∈ S, 0 < τ s := fun s hs => hp s (Finset.mem_insert_of_mem hs)
    have hold := ih (τ k) hk0.le hs (fun s hs' => (hτ (hk s hs')).le)
    have hI := Kyprianou.Ch04.bvFiniteJumpInsertMaxIntegralLedgerV1
      τ hτ j a d f hf S k hk T hk0 hkT hs
    have hJ := Kyprianou.Ch04.bvFiniteJumpInsertMaxJumpLedgerV1 τ hτ j a d f S k hk
    change (∫ u in 0..T, fderiv ℝ f (u,P (insert k S) u) (1,d)) =
      (∫ u in 0..τ k, fderiv ℝ f (u,P S u) (1,d)) +
      (f (T,P (insert k S) T) - f (τ k,P (insert k S) (τ k))) at hI
    change (∑ s ∈ insert k S, (f (τ s,P (insert k S) (τ s)) -
        f (τ s,Q (insert k S) (τ s)))) =
      f (τ k,P (insert k S) (τ k)) - f (τ k,P S (τ k)) +
      ∑ s ∈ S, (f (τ s,P S (τ s)) - f (τ s,Q S (τ s))) at hJ
    rw [hI,hJ]
    linarith
