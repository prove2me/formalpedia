-- Prove2me | solution 1 for GlobalTheory.FrameBasic.cramer_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:28:26.521009+00:00
-- url     : https://prove2.me/submissions/35a5d265-dd23-4ac6-a33b-65678130f4c2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
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
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]
namespace GlobalTheory.FrameBasic
theorem _root_.solution {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (β : Fin (r + 1) → E) (c : E)
    (h : Z.mulVec β = Pi.single (Fin.last r) c) :
    Z.det * β (Fin.last r) = (Z.submatrix Fin.castSucc Fin.castSucc).det * c := by
  have h1 := congrArg (fun v => Z.adjugate.mulVec v (Fin.last r)) h
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single] at h1
  rw [h1]
  simp [Matrix.adjugate_fin_succ_eq_det_submatrix, ← two_mul]
end GlobalTheory.FrameBasic
