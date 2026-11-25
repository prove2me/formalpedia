-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.exists_frames_term_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:40.759656+00:00
-- url     : https://prove2.me/submissions/d12c85c9-90fe-4f90-9dac-725cfed5d0d8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_GlobalTheory_HL_Inhab_exists_frames_term
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Model_nonempty_split
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Inhab
theorem _root_.solution [IsNonarchimedeanLocalField F] (m : ℕ) :
    ∃ L : LocE F (F × F),
      (∃ S : Frames L 1 (m + 1), S.gg = false ∧ ∃ d Λ, S.IsTerm d Λ) ∧
      ∃ S : Frames L 1 (m + 3), S.gg = true ∧ ∃ d Λ, S.IsTerm d Λ := by
  obtain ⟨L, -, -⟩ := nonempty_split (F := F)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hE : ¬ IsField (F × F) := by
    intro h
    obtain ⟨b, hb⟩ := h.mul_inv_cancel (a := ((0 : F), (1 : F))) (by simp)
    have h0 := congrArg Prod.fst hb
    simp at h0
  obtain ⟨⟨S, -, -, -, -, hg, -, -, d, Λ, hd, -⟩, h2⟩ := exists_frames_term L ϖ hϖ m
  obtain ⟨S', -, hg', -, -, d', Λ', hd', -⟩ := h2 hE
  exact ⟨L, ⟨S, hg, d, Λ, hd⟩, S', hg', d', Λ', hd'⟩
end GlobalTheory.HL.Inhab
