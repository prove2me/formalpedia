-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KmCover.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:42:13.86197+00:00
-- url     : https://prove2.me/submissions/c7018740-fc46-44a8-a565-e5ddbac82f53

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SolveUnitriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KmCover
open Matrix
namespace GlobalTheory.CompanionTheory.KmCover
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] {ϖ : R} (hϖ : Irreducible ϖ) (k : ℕ) :
    ∃ S : Finset R, S.card ≤ Nat.card (IsLocalRing.ResidueField R) ^ k ∧
      ∀ x : R, ∃ t ∈ S, x - t ∈ Ideal.span {ϖ ^ k} := by
  classical
  obtain ⟨S₁, hS₁, hS₁'⟩ : ∃ S : Finset R, S.card ≤ Nat.card (IsLocalRing.ResidueField R) ∧
      ∀ x : R, ∃ t ∈ S, x - t ∈ Ideal.span {ϖ} := by
    letI := Fintype.ofFinite (IsLocalRing.ResidueField R)
    obtain ⟨sec, hsec⟩ := (IsLocalRing.residue_surjective (R := R)).hasRightInverse
    refine ⟨Finset.univ.image sec, ?_, ?_⟩
    · rw [Nat.card_eq_fintype_card]
      exact Finset.card_image_le.trans (by simp)
    · intro x
      refine ⟨sec (IsLocalRing.residue R x), by simp, ?_⟩
      rw [← hϖ.maximalIdeal_eq, ← IsLocalRing.residue_eq_zero_iff, map_sub, hsec, sub_self]
  induction k with
  | zero =>
    refine ⟨{0}, by simp, fun x => ⟨0, by simp, by simp⟩⟩
  | succ k ih =>
    obtain ⟨S, hS, hS'⟩ := ih
    refine ⟨Finset.image₂ (fun t s => t + ϖ ^ k * s) S S₁, ?_, ?_⟩
    · refine Finset.card_image₂_le _ _ _ |>.trans ?_
      rw [pow_succ]
      exact Nat.mul_le_mul hS hS₁
    · intro x
      obtain ⟨t, ht, hx⟩ := hS' x
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
      obtain ⟨s, hs, hy'⟩ := hS₁' y
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hy'
      refine ⟨t + ϖ ^ k * s, Finset.mem_image₂_of_mem ht hs, ?_⟩
      rw [Ideal.mem_span_singleton]
      refine ⟨z, ?_⟩
      linear_combination hy + ϖ ^ k * hz
end GlobalTheory.CompanionTheory.KmCover
