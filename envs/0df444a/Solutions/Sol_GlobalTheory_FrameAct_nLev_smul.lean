-- Prove2me | solution 1 for GlobalTheory.FrameAct.nLev_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:11.309082+00:00
-- url     : https://prove2.me/submissions/6e910d58-efd4-46ed-87d0-e23fa761f47c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Theorems.Thm_GlobalTheory_FrameAct_mem_smul_iff
import Theorems.Thm_GlobalTheory_FrameAct_sat_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameAct
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FrameAct
theorem _root_.solution (h : S.GLV) (hh : h ∈ S.St) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hM : S.M d (h • Λ) = h • S.M d Λ) (hL : ∀ y, S.levC d (h • Λ) (h y) = S.levC d Λ y) (J : ℕ) :
    S.nLev d (h • Λ) J = S.nLev d Λ J := by
  unfold Frames.nLev
  have hC : ∀ y : S.V, {x | x - h y ∈ S.M d (h • Λ)} = (h : S.V → S.V) '' {x | x - y ∈ S.M d Λ} := by
    intro y
    ext x
    rw [hM]
    constructor
    · intro hx
      have hx' : x - h y ∈ h • S.M d Λ := hx
      have e : x - h y = h (h⁻¹ x - y) := by
        rw [map_sub, show h (h⁻¹ x) = x from h.apply_symm_apply x]
      rw [e] at hx'
      exact ⟨h⁻¹ x, (mem_smul_iff S h _ _).1 hx', h.apply_symm_apply x⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z - y ∈ S.M d Λ := hz
      show h z - h y ∈ h • S.M d Λ
      rw [← map_sub]
      exact (mem_smul_iff S h _ _).2 hz'
  have hT : {C : Set S.V | ∃ y ∈ S.sat (h • Λ), S.levC d (h • Λ) y = J ∧
        C = {x | x - y ∈ S.M d (h • Λ)}} =
      (fun C => (h : S.V → S.V) '' C) ''
        {C | ∃ y ∈ S.sat Λ, S.levC d Λ y = J ∧ C = {x | x - y ∈ S.M d Λ}} := by
    ext C
    constructor
    · rintro ⟨y, hy, hl, rfl⟩
      rw [sat_smul S h hh] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      refine ⟨{x | x - z ∈ S.M d Λ}, ⟨z, hz, ?_, rfl⟩, ?_⟩
      · rw [← hL z]
        exact hl
      · exact (hC z).symm
    · rintro ⟨C0, ⟨z, hz, hl, rfl⟩, rfl⟩
      refine ⟨h z, ?_, ?_, (hC z).symm⟩
      · rw [sat_smul S h hh]
        exact (mem_smul_iff S h _ _).2 hz
      · rw [hL]
        exact hl
  rw [hT, Set.ncard_image_of_injective _ (Set.image_injective.mpr h.injective)]
end GlobalTheory.FrameAct
