-- Prove2me | solution 1 for GlobalTheory.FrameBasic.solve_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:04.887176+00:00
-- url     : https://prove2.me/submissions/09c7b0c7-4bd5-4d33-82db-633141b81ec0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Theorems.Thm_GlobalTheory_FrameBasic_cramer_last
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
theorem _root_.solution {r : ℕ} (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hZ : IsUnit Z.det) (hZ' : IsUnit Z'.det)
    (hG : IsUnit (Z.det * Z'.det - T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det *
      (Z'.submatrix Fin.castSucc Fin.castSucc).det)))
    (α β : Fin (r + 1) → E) (h1 : Z.mulVec β = Pi.single (Fin.last r) (T * α (Fin.last r)))
    (h2 : Z'.mulVec α = Pi.single (Fin.last r) (T' * β (Fin.last r))) : α = 0 ∧ β = 0 := by
  have e1 := cramer_last _ _ _ h1
  have e2 := cramer_last _ _ _ h2
  have ha : α (Fin.last r) = 0 := by
    apply hG.mul_right_eq_zero.1
    linear_combination Z.det * e2 + T' * (Z'.submatrix Fin.castSucc Fin.castSucc).det * e1
  have hb : β = 0 := by
    rw [ha, mul_zero, Pi.single_zero] at h1
    exact (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hZ)) (by simpa using h1)
  refine ⟨?_, hb⟩
  rw [hb, Pi.zero_apply, mul_zero, Pi.single_zero] at h2
  exact (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hZ')) (by simpa using h2)
end GlobalTheory.FrameBasic
