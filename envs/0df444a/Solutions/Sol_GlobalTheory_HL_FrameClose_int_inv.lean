-- Prove2me | solution 1 for GlobalTheory.HL.FrameClose.int_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:58:10.681837+00:00
-- url     : https://prove2.me/submissions/c4ef7f66-1eea-47de-971c-3ada9a2f5179

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
import Theorems.Thm_GlobalTheory_T_unitriangular_close_to_one_inverse_close


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameClose
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.FrameClose
theorem _root_.solution (L : LocE F E) {n : ℕ} (s : Matrix (Fin n) (Fin n) E) (hlow : ∀ i j, j < i → s i j = 0)
    (hdiag : ∀ i, s i i = 1) (hO : ∀ i j, s i j ∈ L.O) :
    ∃ si : Matrix (Fin n) (Fin n) E, s * si = 1 ∧ ∀ i j, si i j ∈ L.O := by
  have h1O : ∀ i j, (1 : Matrix (Fin n) (Fin n) E) i j ∈ L.O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact L.O.one_mem
    · exact L.O.zero_mem
  obtain ⟨si, -, h2, h3⟩ := GlobalTheory.T.unitriangular_close_to_one_inverse_close L n s 1 L.O.one_mem hlow hdiag
    (fun i j => ⟨(s - 1) i j, L.O.sub_mem (hO i j) (h1O i j), (one_mul _).symm⟩)
  refine ⟨si, h2, fun i j => ?_⟩
  obtain ⟨o, ho, he⟩ := h3 i j
  have : si i j = o + (1 : Matrix (Fin n) (Fin n) E) i j := by
    rw [one_mul, Matrix.sub_apply] at he
    rw [← he]; ring
  rw [this]
  exact L.O.add_mem ho (h1O i j)
end GlobalTheory.HL.FrameClose
