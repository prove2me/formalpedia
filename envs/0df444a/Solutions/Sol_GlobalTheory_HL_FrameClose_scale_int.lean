-- Prove2me | solution 1 for GlobalTheory.HL.FrameClose.scale_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:36.811585+00:00
-- url     : https://prove2.me/submissions/06417ae7-52a2-4ae1-813e-dfbe189127e6

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
import Theorems.Thm_GlobalTheory_HL_FrameClose_algebraMap_mem
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
theorem _root_.solution (L : LocE F E) {r : ℕ} (c a q : F) (hc : c ≠ 0) (ha : a ∈ 𝒪[F]) (hac : a * c ∈ 𝒪[F])
    (hq : q ∈ 𝒪[F]) (i j : Fin (r + 1)) (hij : i < j) (x y : E)
    (hx : ∃ o ∈ L.O, x = algebraMap F E (q * a ^ r) * o)
    (hrel : x * algebraMap F E (c ^ (r - (i : ℕ))) = algebraMap F E (c ^ (r - (j : ℕ))) * y) : y ∈ L.O := by
  obtain ⟨o, ho, rfl⟩ := hx
  have hij' : (i : ℕ) < j := hij
  have hj : (j : ℕ) ≤ r := Nat.lt_succ_iff.1 j.2
  have hr : r - (i : ℕ) = (r - (j : ℕ)) + ((j : ℕ) - i) := by omega
  have hr2 : r = (r - ((j : ℕ) - i)) + ((j : ℕ) - i) := by omega
  have hu : IsUnit (algebraMap F E (c ^ (r - (j : ℕ)))) := (IsUnit.mk0 _ (pow_ne_zero _ hc)).map (algebraMap F E)
  have hy : y = algebraMap F E (q * (a ^ (r - ((j : ℕ) - i)) * (a * c) ^ ((j : ℕ) - i))) * o := by
    have p1 : c ^ (r - (i : ℕ)) = c ^ (r - (j : ℕ)) * c ^ ((j : ℕ) - i) := by rw [← pow_add, ← hr]
    have p2 : a ^ r = a ^ (r - ((j : ℕ) - i)) * a ^ ((j : ℕ) - i) := by rw [← pow_add, ← hr2]
    apply hu.mul_right_injective
    dsimp only
    rw [← hrel, p1, p2]
    simp only [map_mul, map_pow, mul_pow]
    ring
  rw [hy]
  exact L.O.mul_mem (algebraMap_mem L (mul_mem hq (mul_mem (pow_mem ha _) (pow_mem hac _)))) ho
end GlobalTheory.HL.FrameClose
