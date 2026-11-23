-- Prove2me | solution 1 for GlobalTheory.FrameBasic.det_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:45.146977+00:00
-- url     : https://prove2.me/submissions/6df83af9-63ef-4e33-a1dd-867b8c202e16

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (σ : Fin n → Fin n)
    (h0 : ∀ a b, b ≠ σ a → A a b = 0) :
    A.det = (∏ a, A a (σ a)) * ((1 : Matrix (Fin n) (Fin n) E).submatrix σ id).det := by
  rw [← Matrix.det_diagonal, ← Matrix.det_mul]
  congr 1
  ext a b
  rw [Matrix.diagonal_mul]
  by_cases h : b = σ a
  · rw [Matrix.submatrix_apply, id, ← h, Matrix.one_apply_eq, mul_one]
  · simp [h0 a b h, Ne.symm h]
end GlobalTheory.FrameBasic
