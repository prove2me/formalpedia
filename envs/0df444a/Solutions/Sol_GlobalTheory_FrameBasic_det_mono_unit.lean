-- Prove2me | solution 1 for GlobalTheory.FrameBasic.det_mono_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:28:27.417667+00:00
-- url     : https://prove2.me/submissions/32d93ffc-cbbf-4c14-907f-0977d7efd76c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Theorems.Thm_GlobalTheory_FrameBasic_det_mono
import Theorems.Thm_GlobalTheory_FrameBasic_det_perm_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]
namespace GlobalTheory.FrameBasic
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (σ : Fin n → Fin n)
    (h0 : ∀ a b, b ≠ σ a → A a b = 0) (hu : ∀ a, A a (σ a) ≠ 0 → IsUnit (A a (σ a)))
    (hd : A.det ≠ 0) : IsUnit A.det := by
  rw [det_mono A σ h0] at hd ⊢
  refine IsUnit.mul ?_ (det_perm_unit σ ?_)
  · rw [IsUnit.prod_univ_iff]
    intro a
    refine hu a fun h => hd ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ a) h, zero_mul]
  · intro a b hab
    by_contra hne
    apply hd
    rw [Matrix.det_zero_of_row_eq hne (by funext c; rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hab]), mul_zero]
end GlobalTheory.FrameBasic
