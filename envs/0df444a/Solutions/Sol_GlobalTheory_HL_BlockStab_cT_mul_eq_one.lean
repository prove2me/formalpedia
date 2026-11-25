-- Prove2me | solution 1 for GlobalTheory.HL.BlockStab.cT_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:30:32.350019+00:00
-- url     : https://prove2.me/submissions/965879ef-8ce1-4afc-aadd-e869110358b4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.BlockStab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {n : ℕ}
namespace GlobalTheory.HL.BlockStab
theorem _root_.solution (L : LocE F E) (A B : Matrix (Fin n) (Fin n) E) (h : A * B = 1) :
    cT L B * cT L A = 1 := by
  ext i j
  have h1 := congrArg L.cj (congrFun (congrFun h j) i)
  simp only [Matrix.mul_apply, map_sum, map_mul] at h1
  simp only [Matrix.mul_apply, cT]
  rw [Finset.sum_congr rfl fun k _ => mul_comm _ _, h1]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply, hij, Ne.symm hij]
end GlobalTheory.HL.BlockStab
