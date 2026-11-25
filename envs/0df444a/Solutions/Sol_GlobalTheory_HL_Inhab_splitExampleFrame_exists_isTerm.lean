-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.splitExampleFrame_exists_isTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:18:54.50597+00:00
-- url     : https://prove2.me/submissions/521b0b85-684e-469e-9472-f83bf9553920

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_GlobalTheory_HL_Inhab_isTermW_of_isSD
import Theorems.Thm_GlobalTheory_HL_Inhab_extZ_mem
import Theorems.Thm_GlobalTheory_HL_Inhab_extZ_sub_eq
import Theorems.Thm_GlobalTheory_HL_Inhab_splitExampleFrame_isSelfDual
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Model_algebraMap_mem_iff
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
theorem _root_.solution (L : LocE F E) (hE : ¬ IsField E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    ∃ d, (toyG L hE ϖ hϖ m).IsTerm d (stdLat L _) := by
  have ha : algebraMap F E (ϖ : F) ∈ L.O := (algebraMap_mem_iff L _).2 ϖ.2
  have hF : ∀ a, (toyG L hE ϖ hϖ m).f a ∈ stdLat L _ := by
    intro a
    fin_cases a <;> exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hF' : ∀ a, (toyG L hE ϖ hϖ m).f' a ∈ stdLat L _ := by
    intro a
    fin_cases a <;> exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp [ha, pow_mem])
  have hS : ∀ j, (toyG L hE ϖ hϖ m).es j ∈ stdLat L _ := by
    intro j
    fin_cases j
    exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hS' : ∀ j, (toyG L hE ϖ hϖ m).es' j ∈ stdLat L _ := by
    intro j
    fin_cases j
    exact extZ_mem _ L _ (by intro i; fin_cases i <;> simp)
  have hth' : (toyG L hE ϖ hϖ m).th = (ϖ : F) := by simp [Frames.th, toyG]
  have hth : ∀ b, (toyG L hE ϖ hϖ m).InTh (stdLat L _)
      ((toyG L hE ϖ hϖ m).f' b - (toyG L hE ϖ hϖ m).f b) := by
    intro b
    unfold Frames.InTh
    rw [hth']
    fin_cases b
    · refine ⟨extZ (e6 m) ![0, -algebraMap F E ϖ, 1, 1, 0, 0], extZ_mem _ L _ ?_,
        extZ_sub_eq _ _ _ _ _ ?_⟩
      · intro i
        fin_cases i <;> simp [ha]
      · funext i
        fin_cases i <;> simp <;> ring
    · refine ⟨extZ (e6 m) ![0, 0, 0, 0, 0, 1], extZ_mem _ L _ ?_, extZ_sub_eq _ _ _ _ _ ?_⟩
      · intro i
        fin_cases i <;> simp
      · funext i
        fin_cases i <;> simp
  have hT' : (((toyG L hE ϖ hϖ m).T'⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
    show (((Units.map (𝒪[F]).subtype.toMonoidHom (isUnit_one_sub_sq ϖ hϖ).unit)⁻¹ : Fˣ) : F) ∈ 𝒪[F]
    rw [← map_inv]
    exact (((isUnit_one_sub_sq ϖ hϖ).unit⁻¹ : 𝒪[F]ˣ) : 𝒪[F]).2
  exact ⟨_, (1, 1), isTermW_of_isSD _ _ (splitExampleFrame_isSelfDual L hE ϖ hϖ m) hF hF' hS hS' (by simp [toyG]) hT' hth⟩
end GlobalTheory.HL.Inhab
