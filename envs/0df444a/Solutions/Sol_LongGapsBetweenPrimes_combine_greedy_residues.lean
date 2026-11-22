-- Prove2me | solution 1 for LongGapsBetweenPrimes.combine_greedy_residues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:18.652921+00:00
-- url     : https://prove2.me/submissions/80b31341-c89b-4db3-8e2c-5ff87f758ff7

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_greedy_residue_classes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (S ps₀ ps₁ ps : Finset ℕ)
    (h₀ : ps₀ ⊆ ps) (h₁ : ps₁ ⊆ ps) (hdisj : Disjoint ps₀ ps₁)
    (hpos : ∀ p ∈ ps, 0 < p) :
    ∃ a : ℕ → ℕ, (∀ p ∈ ps, a p < p) ∧
      ((survivors S ps a).card : ℝ) ≤
        ((survivors S ps₀ (fun _ => 0)).card : ℝ) * ∏ p ∈ ps₁, (1 - 1 / (p : ℝ)) := by
  classical
  obtain ⟨b, hb, hcard⟩ := greedy_residue_classes
    (survivors S ps₀ (fun _ => 0)) ps₁ (fun p hp => hpos p (h₁ hp))
  let a : ℕ → ℕ := fun p => if p ∈ ps₁ then b p else 0
  refine ⟨a, ?_, ?_⟩
  · intro p hp
    by_cases hp₁ : p ∈ ps₁
    · simpa [a, hp₁] using hb p hp₁
    · simpa [a, hp₁] using hpos p hp
  · have hsubset : survivors S ps a ⊆
        survivors (survivors S ps₀ (fun _ => 0)) ps₁ b := by
      intro n hn
      obtain ⟨hnS, hn⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnS, ?_⟩, ?_⟩
      · intro p hp
        have hp₁ : p ∉ ps₁ := Finset.disjoint_left.mp hdisj hp
        simpa [a, hp₁] using hn p (h₀ hp)
      · intro p hp
        simpa [a, hp] using hn p (h₁ hp)
    exact (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans hcard
end LongGapsBetweenPrimes
