-- Prove2me | solution 1 for HGASUndecidable.Main.theorem_2_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:33:47.193331+00:00
-- url     : https://prove2.me/submissions/436931f3-5e88-424e-9279-717a1a680cb2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HGASUndecidable_Main_theorem_2_1_code_reduction
import Theorems.Thm_HGASUndecidable_Main_proposition_4_4

open Filter Topology MeasureTheory
open scoped BigOperators
open HGASUndecidable.Main

theorem solution (n₀ k₀ : ℕ) (hn₀ : 1 ≤ n₀) (hk₀ : 1 ≤ k₀) :
    ∀ n d : ℕ, Nat.choose (n₀+k₀-1) k₀ ≤ n → 3 ≤ d → Odd d →
      (ManyOneComplete (HGAS n₀ (2*k₀+1)) → ManyOneComplete (HGAS n d)) ∧
      (¬ComputablePred (HGAS n₀ (2*k₀+1)) → ¬ComputablePred (HGAS n d)) ∧
      (ManyOneHard (HLS n₀ (2*k₀+1)) → ManyOneHard (HLS n d)) ∧
      (¬ComputablePred (HLS n₀ (2*k₀+1)) → ¬ComputablePred (HLS n d)) := by
  intro n d hn hd hodd
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, d = 3 + 2*j := by
    obtain ⟨k, hk⟩ := hodd
    use k - 1
    omega
  obtain ⟨r, hr, hGAS, hHLS⟩ :=
    theorem_2_1_code_reduction n₀ k₀ n j hn₀ hk₀ hn
  let redGAS : ManyOneReducible (HGAS n₀ (2*k₀+1)) (HGAS n (3+2*j)) :=
    ⟨r, hr, hGAS⟩
  let redHLS : ManyOneReducible (HLS n₀ (2*k₀+1)) (HLS n (3+2*j)) :=
    ⟨r, hr, hHLS⟩
  have hard_transfer {S T : ℕ → Prop} (red : ManyOneReducible S T)
      (hS : ManyOneHard S) : ManyOneHard T := by
    intro A hA
    exact (hS A hA).trans red
  have noncomputable_transfer {S T : ℕ → Prop} (red : ManyOneReducible S T)
      (hS : ¬ ComputablePred S) : ¬ ComputablePred T := by
    intro hT
    apply hS
    obtain ⟨f, hf, hred⟩ := red
    obtain ⟨inst, hinst⟩ := hT
    have hpull : ComputablePred (fun e => T (f e)) :=
      ⟨fun e => inst (f e), hinst.comp hf⟩
    exact hpull.of_eq (fun e => (hred e).symm)
  exact ⟨fun h => ⟨proposition_4_4.2.1 n (3+2*j), hard_transfer redGAS h.2⟩,
    noncomputable_transfer redGAS, hard_transfer redHLS,
    noncomputable_transfer redHLS⟩
