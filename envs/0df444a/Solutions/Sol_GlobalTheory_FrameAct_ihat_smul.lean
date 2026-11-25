-- Prove2me | solution 1 for GlobalTheory.FrameAct.ihat_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:47.840535+00:00
-- url     : https://prove2.me/submissions/b3fea600-b113-4162-b44d-10da9795d4d5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Theorems.Thm_GlobalTheory_FrameAct_smul_span
import Theorems.Thm_GlobalTheory_FrameAct_tauRel_map

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
    (hM : S.M d (h • Λ) = h • S.M d Λ) : S.Ihat d (h • Λ) = h • S.Ihat d Λ := by
  have hM' : S.M d (h⁻¹ • h • Λ) = h⁻¹ • S.M d (h • Λ) := by
    rw [inv_smul_smul, hM, inv_smul_smul]
  unfold Frames.Ihat
  rw [Submodule.smul_sup', hM, smul_span]
  congr 2
  ext y
  constructor
  · rintro ⟨w, hw, hT⟩
    have hw0 : w ∈ S.W0 := hw.1
    have hinv := tauRel_map S h⁻¹ (S.St.inv_mem hh) d (h • Λ) hM' w hw0 y hT
    rw [inv_smul_smul] at hinv
    exact ⟨h⁻¹ y, ⟨w, hw, hinv⟩, h.apply_symm_apply y⟩
  · rintro ⟨x, ⟨w, hw, hT⟩, rfl⟩
    have hw0 : w ∈ S.W0 := hw.1
    exact ⟨w, hw, tauRel_map S h hh d Λ hM w hw0 x hT⟩
end GlobalTheory.FrameAct
