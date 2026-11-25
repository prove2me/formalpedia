-- Prove2me | solution 1 for GlobalTheory.HL.MoveTotal.mv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:33.0861+00:00
-- url     : https://prove2.me/submissions/38942ab0-2794-44de-927c-6e77db65090d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMoveCharacterNeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubiniStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexIntegrableShareTopLevelVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMoveScalarFibreMeasureOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovesTotalMeasureEstimates
import Theorems.Thm_GlobalTheory_HL_MoveTotal_mem_refB
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
import Theorems.Thm_GlobalTheory_HL_FibU_hf_cj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveTotal
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveTotal
theorem _root_.solution [CharZero F] (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V) (b : S.V × S.V) (u : S.V) (t : E) :
    S.Mv J d Λ (b, u, t) ↔ (b ∈ S.refB J Λ ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = J) ∧
      u ∈ S.refU J Λ ∧
      ((∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧
        t + L.cj t = 0) := by
  have hs : algebraMap F E 2⁻¹ * S.h u u + L.cj (algebraMap F E 2⁻¹ * S.h u u) = S.h u u := by
    rw [map_mul, AlgEquiv.commutes, Frames.h, hf_cj L S.herm.1, ← add_mul, ← map_add]
    norm_num
  have e : (S.sOf (b, u, t) + L.cj (S.sOf (b, u, t)) = S.h u u) ↔ t + L.cj t = 0 := by
    simp only [Frames.sOf]
    rw [map_add]
    constructor <;> intro h
    · linear_combination h - hs
    · linear_combination h + hs
  have hU : u ∈ S.refU J Λ ↔ u ∈ Λ ∧ u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) := Iff.rfl
  rw [mem_refB, hU, ← e]
  simp only [Frames.Mv, Frames.IsMove, and_assoc]
  rfl
end GlobalTheory.HL.MoveTotal
