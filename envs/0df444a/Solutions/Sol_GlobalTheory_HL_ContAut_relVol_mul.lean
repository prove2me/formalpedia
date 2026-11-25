-- Prove2me | solution 1 for GlobalTheory.HL.ContAut.relVol_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:51.639161+00:00
-- url     : https://prove2.me/submissions/ddd468c9-b945-4017-992f-4d43ae3833fa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_ContModel_relVol_of_le
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContAut
namespace GlobalTheory.HL.ContAut
theorem _root_.solution {W : Type} [AddCommGroup W] {X Y B : AddSubgroup W}
    (hYX : Y.relIndex X ≠ 0) (hBY : B.relIndex Y ≠ 0) :
    relVol X B = relVol X Y * relVol Y B := by
  have hCY : (B ⊓ Y).relIndex Y ≠ 0 := by rwa [AddSubgroup.inf_relIndex_right]
  have hCX : (B ⊓ Y).relIndex X ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hCY hYX
  have e1 := ContModel.relVol_of_le (W0 := X) (inf_le_left : B ⊓ Y ≤ B) hCX
  have e2 := ContModel.relVol_of_le (W0 := X) (inf_le_right : B ⊓ Y ≤ Y) hCX
  have e3 := ContModel.relVol_of_le (W0 := Y) (inf_le_left : B ⊓ Y ≤ B) hCY
  have e4 : relVol Y (B ⊓ Y) = 1 / ((B ⊓ Y).relIndex Y : ℝ) := by
    unfold relVol
    rw [AddSubgroup.relIndex_eq_one.2 (inf_le_right : B ⊓ Y ≤ Y)]
    simp
  have c : ((B ⊓ Y).relIndex Y : ℝ) ≠ 0 := by exact_mod_cast hCY
  rw [e1, e2, e3, e4]
  field_simp
end GlobalTheory.HL.ContAut
