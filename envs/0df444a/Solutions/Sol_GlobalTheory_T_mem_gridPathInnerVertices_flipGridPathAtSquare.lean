-- Prove2me | solution 1 for GlobalTheory.T.mem_gridPathInnerVertices_flipGridPathAtSquare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:12.506361+00:00
-- url     : https://prove2.me/submissions/af9ec276-ac6f-47fa-baab-dddecc47a074

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemGridPathInnerVerticesFlipGridPathAtSquare
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemGridPathInnerVerticesFlipGridPathAtSquareStatement
import Theorems.Thm_GlobalTheory_SplitFlip_mem_innerVertices_flipPath


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by
  first | exact @GlobalTheory.SplitFlip.mem_innerVertices_flipPath | exact GlobalTheory.SplitFlip.mem_innerVertices_flipPath | (intros; apply GlobalTheory.SplitFlip.mem_innerVertices_flipPath <;> assumption)
end _root_.GlobalTheory.T
