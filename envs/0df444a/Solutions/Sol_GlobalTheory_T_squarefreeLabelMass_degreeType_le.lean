-- Prove2me | solution 1 for GlobalTheory.T.squarefreeLabelMass_degreeType_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:56.749795+00:00
-- url     : https://prove2.me/submissions/625b86c7-1ce5-4dc3-b6f6-8e0b83652ad6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelMassDegreeTypeLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelMassDegreeTypeLeStatement
import Theorems.Thm_GlobalTheory_BadShare_mass_degType_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (μ : Multiset ℕ), (mass g N fun f => degType g f = μ) ≤ (∏ d ∈ μ.toFinset, ((d : ℝ) ^ μ.count d * (μ.count d).factorial))⁻¹ := by
  first | exact @GlobalTheory.BadShare.mass_degType_le | exact GlobalTheory.BadShare.mass_degType_le | (intros; apply GlobalTheory.BadShare.mass_degType_le <;> assumption)
end _root_.GlobalTheory.T
