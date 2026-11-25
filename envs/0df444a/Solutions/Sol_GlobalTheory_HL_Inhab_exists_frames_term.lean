-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.exists_frames_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:29:12.919722+00:00
-- url     : https://prove2.me/submissions/6d0fe7cd-ffd0-4180-951a-7f2db40db44e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_GlobalTheory_HL_Inhab_exampleFrame_G
import Theorems.Thm_GlobalTheory_HL_Inhab_exampleFrame_a
import Theorems.Thm_GlobalTheory_HL_Inhab_exampleFrame_isSelfDual
import Theorems.Thm_GlobalTheory_HL_Inhab_exampleFrame_exists_isTerm
import Theorems.Thm_GlobalTheory_HL_Inhab_splitExampleFrame_G
import Theorems.Thm_GlobalTheory_HL_Inhab_splitExampleFrame_a
import Theorems.Thm_GlobalTheory_HL_Inhab_splitExampleFrame_isSelfDual
import Theorems.Thm_GlobalTheory_HL_Inhab_splitExampleFrame_exists_isTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Inhab
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    (∃ S : Frames L 1 (m + 1), S.ϖ = ϖ ∧ S.w.blocks = [(1, 2)] ∧ S.T = 1 ∧ S.T' = 1 ∧ S.gg = false ∧
      S.G = 1 ∧ S.a = 0 ∧ ∃ d Λ, S.IsTerm d Λ ∧ IsSD L S.Hm Λ) ∧
    (¬ IsField E → ∃ S : Frames L 1 (m + 3), S.ϖ = ϖ ∧ S.gg = true ∧
      S.G = algebraMap F E ((ϖ : F) ^ 6) ∧ S.a = 2 ∧ ∃ d Λ, S.IsTerm d Λ ∧ IsSD L S.Hm Λ) := by
  refine ⟨⟨toyExample L ϖ hϖ m, rfl, rfl, rfl, rfl, rfl, exampleFrame_G L ϖ hϖ m, exampleFrame_a L ϖ hϖ m, ?_⟩, fun hE =>
    ⟨toyG L hE ϖ hϖ m, rfl, rfl, splitExampleFrame_G L hE ϖ hϖ m, splitExampleFrame_a L hE ϖ hϖ m, ?_⟩⟩
  · obtain ⟨d, hd⟩ := exampleFrame_exists_isTerm L ϖ hϖ m
    exact ⟨d, _, hd, exampleFrame_isSelfDual L ϖ hϖ m⟩
  · obtain ⟨d, hd⟩ := splitExampleFrame_exists_isTerm L hE ϖ hϖ m
    exact ⟨d, _, hd, splitExampleFrame_isSelfDual L hE ϖ hϖ m⟩
end GlobalTheory.HL.Inhab
