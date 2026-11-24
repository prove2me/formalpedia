-- Prove2me | solution 1 for GlobalTheory.SplitFlip.mem_innerVertices_flipPath
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:33:58.861898+00:00
-- url     : https://prove2.me/submissions/0623fe90-dfeb-426b-af02-a63af6bcaf7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemGridPathInnerVerticesFlipGridPathAtSquare
import Theorems.Thm_GlobalTheory_SplitFlip_IsPath_eq_of_src_eq_of_mem
import Theorems.Thm_GlobalTheory_SplitFlip_src_flipEdge_pathInner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SplitFlip
namespace GlobalTheory.SplitFlip
theorem _root_.solution {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (hp : PassesThrough i j γ) :
    ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by
  intro X hX
  rw [innerVertices, flipPath, ← List.map_tail, List.map_map, List.mem_map] at hX
  obtain ⟨e, he, rfl⟩ := hX
  rw [Function.comp_apply, src_flipEdge_pathInner]
  have hex : Edge.ex i j ∈ γ := hp.subset (by simp)
  have heγ : e ∈ γ := List.mem_of_mem_tail he
  by_cases h : e = .ex i j
  · simp only [h, if_true]
    refine ⟨fun H => ?_, fun H => absurd rfl H⟩
    simp at H
  · simp only [h, if_false]
    refine ⟨fun H => h (hγ.eq_of_src_eq_of_mem heγ hex (by simpa using H)), fun _ => List.mem_map.2 ⟨e, he, rfl⟩⟩
end GlobalTheory.SplitFlip
