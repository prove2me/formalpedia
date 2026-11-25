-- Prove2me | solution 1 for GlobalTheory.FrameAct.perp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:10:06.058322+00:00
-- url     : https://prove2.me/submissions/81c65417-41cb-43a5-a3b5-2964567a74d7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Theorems.Thm_GlobalTheory_FrameAct_isom

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
theorem _root_.solution (h : S.GLV) (hh : h ∈ S.St) (A : Submodule E S.V) (hA : ∀ v, h v ∈ A ↔ v ∈ A)
    (v : S.V) : h v ∈ perp L S.Hm A ↔ v ∈ perp L S.Hm A := by
  show (∀ y ∈ A, hf L S.Hm (h v) y = 0) ↔ ∀ y ∈ A, hf L S.Hm v y = 0
  constructor
  · intro H y hy
    rw [← isom S h hh v y]
    exact H (h y) ((hA y).2 hy)
  · intro H y hy
    have e : h (h⁻¹ y) = y := h.apply_symm_apply y
    have hy' : h⁻¹ y ∈ A := (hA (h⁻¹ y)).1 (by rw [e]; exact hy)
    rw [← e, isom S h hh]
    exact H _ hy'
end GlobalTheory.FrameAct
