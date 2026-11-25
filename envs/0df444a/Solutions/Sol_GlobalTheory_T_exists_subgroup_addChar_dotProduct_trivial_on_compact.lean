-- Prove2me | solution 1 for GlobalTheory.T.exists_subgroup_addChar_dotProduct_trivial_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:01.304722+00:00
-- url     : https://prove2.me/submissions/f1f17b11-f8d4-434b-81f5-1595d6f393e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSubgroupAddCharDotProductTrivialOnCompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSubgroupAddCharDotProductTrivialOnCompactStatement
import Theorems.Thm_GlobalTheory_CharDotKill_charDot_kill


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K] (χ : AddChar K ℂ), Continuous χ → ∀ (κ : Type) [Fintype κ] (C : Set (κ → K)), IsCompact C → ∃ H : OpenAddSubgroup (κ → K), ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by
  first | exact @GlobalTheory.CharDotKill.charDot_kill | exact GlobalTheory.CharDotKill.charDot_kill | (intros; apply GlobalTheory.CharDotKill.charDot_kill <;> assumption)
end _root_.GlobalTheory.T
