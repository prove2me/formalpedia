-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.exampleFrame_exists_isTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:18:50.974017+00:00
-- url     : https://prove2.me/submissions/9a5402bb-fc82-4c7d-9557-05d425e2cd1b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_GlobalTheory_HL_Inhab_isTermW_of_isSD
import Theorems.Thm_GlobalTheory_HL_Inhab_extZ_mem
import Theorems.Thm_GlobalTheory_HL_Inhab_exampleFrame_isSelfDual
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    ∃ d, (toyExample L ϖ hϖ m).IsTerm d (stdLat L _) := by
  have hF : ∀ a, (toyExample L ϖ hϖ m).f a ∈ stdLat L _ := by
    intro a
    fin_cases a <;> exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hF' : ∀ a, (toyExample L ϖ hϖ m).f' a ∈ stdLat L _ := by
    intro a
    fin_cases a <;> exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hS : ∀ j, (toyExample L ϖ hϖ m).es j ∈ stdLat L _ := by
    intro j
    fin_cases j
    exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hS' : ∀ j, (toyExample L ϖ hϖ m).es' j ∈ stdLat L _ := by
    intro j
    fin_cases j
    exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hth : ∀ b, (toyExample L ϖ hϖ m).InTh (stdLat L _) ((toyExample L ϖ hϖ m).f' b - (toyExample L ϖ hϖ m).f b) := by
    intro b
    refine ⟨_, Submodule.sub_mem _ (hF' b) (hF b), ?_⟩
    simp [Frames.th, toyExample]
  exact ⟨_, (1, 1), isTermW_of_isSD _ _ (exampleFrame_isSelfDual L ϖ hϖ m) hF hF' hS hS' (by simp [toyExample])
    (by simp [toyExample]) hth⟩
end GlobalTheory.HL.Inhab
