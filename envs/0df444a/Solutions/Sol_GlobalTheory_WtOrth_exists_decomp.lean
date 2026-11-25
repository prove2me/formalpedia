-- Prove2me | solution 1 for GlobalTheory.WtOrth.exists_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:36.969719+00:00
-- url     : https://prove2.me/submissions/60da0005-6355-45e1-abe9-1ab008024f1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearOrthDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.WtOrth
namespace GlobalTheory.WtOrth
theorem _root_.solution {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M) (hw : w ∈ WtNear E Λ t) :
    ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t) ∧
      (∀ ω, IsWeight E ω (x ω)) ∧ (∀ ω, ω ∉ T → x ω = 0) ∧ w = ∑ ω ∈ T, x ω := by
  classical
  unfold WtNear at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ω, h1, h2⟩ := hy
    refine ⟨{ω}, fun ω' => if ω' = ω then y else 0, ?_, ?_, ?_, ?_⟩
    · intro ω' h
      rw [Finset.mem_singleton.mp h]; exact h1
    · intro ω'
      by_cases h : ω' = ω
      · simp only [h, if_true]; exact h2
      · intro a; simp [h]
    · intro ω' h
      have : ω' ≠ ω := fun e => h (Finset.mem_singleton.mpr e)
      simp [this]
    · simp
  | zero => exact ⟨∅, fun _ => 0, by simp, fun ω a => by simp, by simp, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨T, x, h1, h2, h3, h4⟩ := hy
    obtain ⟨T', x', h1', h2', h3', h4'⟩ := hz
    refine ⟨T ∪ T', fun ω => x ω + x' ω, ?_, ?_, ?_, ?_⟩
    · intro ω h
      rcases Finset.mem_union.mp h with h | h
      · exact h1 ω h
      · exact h1' ω h
    · intro ω a
      simp only [map_add, h2 ω a, h2' ω a, smul_add]
    · intro ω h
      rw [Finset.mem_union, not_or] at h
      simp [h3 ω h.1, h3' ω h.2]
    · rw [Finset.sum_add_distrib, h4, h4']
      congr 1
      · exact Finset.sum_subset Finset.subset_union_left fun ω _ h => h3 ω h
      · exact Finset.sum_subset Finset.subset_union_right fun ω _ h => h3' ω h
  | smul c y _ hy =>
    obtain ⟨T, x, h1, h2, h3, h4⟩ := hy
    refine ⟨T, fun ω => c • x ω, h1, ?_, ?_, ?_⟩
    · intro ω a
      simp only [map_smul, h2 ω a]
      exact smul_comm _ _ _
    · intro ω h
      simp [h3 ω h]
    · rw [h4, Finset.smul_sum]
end GlobalTheory.WtOrth
