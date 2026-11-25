-- Prove2me | solution 1 for GlobalTheory.HL.QReflGen.unit_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:51:26.355634+00:00
-- url     : https://prove2.me/submissions/30287628-6313-4bc5-bda5-f863e857c55d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometriesFixingSubspaceLeQuasiReflectionClosure
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QReflGen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.QReflGen
theorem _root_.solution (L : LocE F E) {z : E} (hz : L.cj z = z) (h0 : z ≠ 0) : IsUnit z := by
  obtain ⟨a, rfl⟩ := (L.cj_fix z).1 hz
  have : a ≠ 0 := by rintro rfl; simp at h0
  exact (IsUnit.mk0 a this).map _
end GlobalTheory.HL.QReflGen
