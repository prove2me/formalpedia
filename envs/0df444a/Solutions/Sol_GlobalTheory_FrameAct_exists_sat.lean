-- Prove2me | solution 1 for GlobalTheory.FrameAct.exists_sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:12.044906+00:00
-- url     : https://prove2.me/submissions/bfbcb514-37c6-4146-b7de-8a09d51255ed

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
theorem _root_.solution (h : S.GLV) (hh : h ∈ S.St) (Λ : Submodule L.O S.V) (P : S.V → Prop) :
    (∃ y ∈ S.sat (h • Λ), P y) ↔ ∃ y ∈ S.sat Λ, P (h y) := by
  rw [sat_smul S h hh]
  constructor
  · rintro ⟨y, hy, hP⟩
    have e : h (h⁻¹ y) = y := h.apply_symm_apply y
    rw [← e] at hy hP
    exact ⟨_, (mem_smul_iff S h _ _).1 hy, hP⟩
  · rintro ⟨y, hy, hP⟩
    exact ⟨h y, (mem_smul_iff S h _ y).2 hy, hP⟩
end GlobalTheory.FrameAct
