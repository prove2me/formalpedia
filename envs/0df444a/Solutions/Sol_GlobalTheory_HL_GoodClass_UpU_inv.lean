-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.UpU.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:36:41.189173+00:00
-- url     : https://prove2.me/submissions/7111f48c-a3ec-4994-ab5a-6c278815997e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
import Theorems.Thm_GlobalTheory_HL_GoodClass_UpU_det
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
variable {E : Type} [CommRing E] {n : ℕ}
namespace GlobalTheory.HL.GoodClass
namespace UpU
theorem _root_.solution {s : Matrix (Fin n) (Fin n) E} (hs : UpU s) :
    ∃ t : Matrix (Fin n) (Fin n) E, UpU t ∧ t * s = 1 := by
  have hd : IsUnit s.det := by rw [hs.det]; exact isUnit_one
  letI := Matrix.invertibleOfIsUnitDet s hd
  have hb : s.BlockTriangular id := fun i j h => hs.1 i j h
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hb
  have h1 : s⁻¹ * s = 1 := Matrix.nonsing_inv_mul s hd
  refine ⟨s⁻¹, ⟨fun i j h => hi h, fun i => ?_⟩, h1⟩
  have h2 := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hs.2, mul_one, Matrix.one_apply_eq] at h2
  · exact h2
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with h1 | h1
    · rw [hi (show id c < id i from h1), zero_mul]
    · rw [hs.1 c i h1, mul_zero]
  · simp
end UpU
end GlobalTheory.HL.GoodClass
