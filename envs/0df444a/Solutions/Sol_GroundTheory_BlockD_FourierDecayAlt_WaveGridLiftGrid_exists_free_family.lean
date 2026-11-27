-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.exists_free_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:43.278461+00:00
-- url     : https://prove2.me/submissions/45eea7ac-a190-4ed9-831a-4d769ca697ff

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_FreeFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.BlockD GroundTheory.BlockD.FourierDecayAlt GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
open Finset
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
theorem _root_.solution (Y : Finset ℝ) (w : List (Bool × ℝ)) (K D : ℕ)
    (hw : ∀ l ∈ w, ∃ y ∈ Y, l = (true, y) ∨ l = (false, y + 1))
    (hcard : w.length + K * D ≤ Y.card) :
    ∃ g : Fin K → Fin D → ℝ, (∀ a i, g a i ∈ Y) ∧
      (∀ a i a' i', g a i = g a' i' → a = a' ∧ i = i') ∧
      ∀ a i, ∀ l ∈ w, ∃ y ∈ Y, y ≠ g a i ∧ (l = (true, y) ∨ l = (false, y + 1)) := by
  classical
  choose! f hfY hf using hw
  set S : Finset ℝ := (w.map f).toFinset with hS
  have hSc : S.card ≤ w.length := by
    calc S.card ≤ (w.map f).length := List.toFinset_card_le _
      _ = w.length := List.length_map _
  have hT : K * D ≤ (Y \ S).card := by
    have h1 := Finset.le_card_sdiff S Y
    generalize K * D = m at hcard ⊢
    omega
  obtain ⟨emb⟩ : Nonempty (Fin (K * D) ↪ ↥(Y \ S)) := by
    rw [Function.Embedding.nonempty_iff_card_le]
    simpa using hT
  let φ : Fin K × Fin D ≃ Fin (K * D) := finProdFinEquiv
  refine ⟨fun a i => (emb (φ (a, i)) : ℝ), ?_, ?_, ?_⟩
  · intro a i
    exact (Finset.mem_sdiff.mp (emb (φ (a, i))).2).1
  · intro a i a' i' h
    have h1 := emb.injective (Subtype.ext h)
    have h2 := φ.injective h1
    simp only [Prod.mk.injEq] at h2
    exact h2
  · intro a i l hl
    refine ⟨f l, hfY l hl, ?_, hf l hl⟩
    intro heq
    have heq' : f l = (emb (φ (a, i)) : ℝ) := heq
    have hmem := (Finset.mem_sdiff.mp (emb (φ (a, i))).2).2
    apply hmem
    rw [← heq', hS, List.mem_toFinset, List.mem_map]
    exact ⟨l, hl, rfl⟩
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
