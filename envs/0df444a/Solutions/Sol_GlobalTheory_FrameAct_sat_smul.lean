-- Prove2me | solution 1 for GlobalTheory.FrameAct.sat_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:08.909587+00:00
-- url     : https://prove2.me/submissions/5835b712-9466-4e64-9809-7c0608e7d349

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Theorems.Thm_GlobalTheory_FrameAct_mem_smul_iff
import Theorems.Thm_GlobalTheory_FrameAct_sup_iff

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
theorem _root_.solution (h : S.GLV) (hh : h ∈ S.St) (Λ : Submodule L.O S.V) :
    S.sat (h • Λ) = h • S.sat Λ := by
  ext y
  have e : h (h⁻¹ y) = y := h.apply_symm_apply y
  rw [← e, mem_smul_iff]
  unfold Frames.sat Frames.ME
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_smul_iff, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, sup_iff S h hh]
end GlobalTheory.FrameAct
