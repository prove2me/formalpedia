-- Prove2me | solution 1 for GlobalTheory.SplitFlip.flipPath_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:34:06.083525+00:00
-- url     : https://prove2.me/submissions/7967b5b5-8d89-4978-a27b-0f7e2483961a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlipGridPathAtSquareSplit
import Theorems.Thm_GlobalTheory_SplitFlip_PathSplit_nodup_of_isPath

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitFlip.PathSplit
namespace GlobalTheory.SplitFlip
theorem _root_.solution : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    ∃ l₁ l₂ : List Edge, γ = l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂ ∧
      flipPath i j γ = l₁ ++ [Edge.ex i (j + 1), Edge.theta (i + 1) j] ++ l₂ := by
  intro γ i j hγ hp
  obtain ⟨l₁, l₂, rfl⟩ := hp
  have hnd := nodup_of_isPath hγ
  refine ⟨l₁, l₂, rfl, ?_⟩
  have hfix : ∀ l : List Edge, Edge.theta i j ∉ l → Edge.ex i j ∉ l →
      l.map (fun e => if e = .theta i j then .ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e) = l :=
    fun l h1 h2 => by
      refine (List.map_congr_left fun e he => ?_).trans (List.map_id l)
      have e1 : e ≠ .theta i j := fun h => h1 (h ▸ he)
      have e2 : e ≠ .ex i j := fun h => h2 (h ▸ he)
      simp [e1, e2]
  rw [List.nodup_append, List.nodup_append] at hnd
  obtain ⟨⟨_, _, hd1⟩, _, hd2⟩ := hnd
  have a1 : Edge.theta i j ∉ l₁ := fun h => hd1 _ h _ (by simp) rfl
  have a2 : Edge.ex i j ∉ l₁ := fun h => hd1 _ h _ (by simp) rfl
  have b1 : Edge.theta i j ∉ l₂ := fun h => hd2 _ (by simp) _ h rfl
  have b2 : Edge.ex i j ∉ l₂ := fun h => hd2 _ (by simp) _ h rfl
  simp only [flipPath, List.map_append, hfix l₁ a1 a2, hfix l₂ b1 b2]
  simp
end GlobalTheory.SplitFlip
