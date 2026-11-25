-- Prove2me | solution 1 for GlobalTheory.HL.FrameClose.pair_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:47.220816+00:00
-- url     : https://prove2.me/submissions/a5ff922c-a15d-4c33-8b5e-cb1e7eadcee6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitriangularCloseToOneInverseCloseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingConjInverseAdjointCloseToOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemMaximalCompactOfIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalPairingMatrixInvMulSelfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFramesJointGramInvMulSelfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsCommonDenominatorForHermitianLatticeDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CloseOnCompletedLatticeOfCloseOnFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntCastIsUnitCompletionAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMatrixCloseGivesLatticeCloseIntegral
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameStab_hf_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameClose
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.FrameClose
theorem _root_.solution (L : LocE F E) {r n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (u u' : Fin (r + 1) → Fin n → E)
    (h : (Fin n → E) ≃ₗ[E] (Fin n → E)) (hi : ∀ x y, hf L Hm (h x) (h y) = hf L Hm x y)
    (M M' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hM : ∀ j, h (u j) = ∑ i, M i j • u i)
    (hM' : ∀ j, h (u' j) = ∑ i, M' i j • u' i) :
    cT L M * Matrix.of (fun i j => hf L Hm (u' j) (u i)) * M' = Matrix.of (fun i j => hf L Hm (u' j) (u i)) := by
  ext a b
  rw [Matrix.of_apply, ← hi, hM', hM, GlobalTheory.HL.FrameStab.hf_sum]
  simp only [Matrix.mul_apply, Finset.sum_mul, cT, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.HL.FrameClose
