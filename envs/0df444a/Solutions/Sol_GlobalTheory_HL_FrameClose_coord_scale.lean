-- Prove2me | solution 1 for GlobalTheory.HL.FrameClose.coord_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:50:58.895488+00:00
-- url     : https://prove2.me/submissions/2765b5a5-5a9e-4b18-a436-9427d6aa3b8d

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
theorem _root_.solution {n r : ℕ} (g : Fin (r + 1) → Fin n → E) (hg : LinearIndependent E g)
    (h : (Fin n → E) ≃ₗ[E] (Fin n → E)) (la : Fin (r + 1) → E) (s M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : ∀ j, h (g j) = ∑ i, s i j • g i) (hM : ∀ j, h (la j • g j) = ∑ i, M i j • (la i • g i)) :
    ∀ i j, M i j * la i = la j * s i j := by
  intro i j
  have h1 : ∑ i, (M i j * la i - la j * s i j) • g i = 0 := by
    have e1 : ∑ i, M i j • (la i • g i) = ∑ i, (M i j * la i) • g i :=
      Finset.sum_congr rfl fun i _ => (smul_smul _ _ _)
    have e2 : h (la j • g j) = ∑ i, (la j * s i j) • g i := by
      rw [map_smul, hs j, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (smul_smul _ _ _)
    have := hM j
    rw [e1, e2] at this
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [this, sub_self]
  have := Fintype.linearIndependent_iff.1 hg _ h1 i
  exact sub_eq_zero.1 this
end GlobalTheory.HL.FrameClose
