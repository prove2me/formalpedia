-- Prove2me | solution 1 for GlobalTheory.FrameAct.frameCls_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:32:18.253937+00:00
-- url     : https://prove2.me/submissions/50293847-48ca-4b65-9f09-ee2d81755e64

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameAct
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FrameAct
theorem _root_.solution (h : S.GLV) (g g' : Fin (r + 1) → S.V) :
    S.frameCls (fun b => h (g b)) (fun b => h (g' b)) = h • S.frameCls g g' := by
  have key : ∀ (y : S.V) (c : Fin (r + 1) → E) (g0 : Fin (r + 1) → S.V),
      (h⁻¹ • y = ∑ i, c i • g0 i) ↔ y = ∑ i, c i • h (g0 i) := by
    intro y c g0
    have hs : ∑ i, c i • h (g0 i) = h (∑ i, c i • g0 i) := by
      simp only [map_sum, LinearEquiv.map_smul]
    rw [hs]
    constructor
    · intro e
      rw [← e]
      exact (h.apply_symm_apply y).symm
    · intro e
      rw [e]
      exact h.symm_apply_apply _
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  unfold Frames.frameCls
  simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, key]
end GlobalTheory.FrameAct
