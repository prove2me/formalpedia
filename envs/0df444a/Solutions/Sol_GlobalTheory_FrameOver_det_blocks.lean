-- Prove2me | solution 1 for GlobalTheory.FrameOver.det_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:55.71344+00:00
-- url     : https://prove2.me/submissions/b73919d8-76f5-4dff-9555-fc53db8f1fcf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFrames
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
open GlobalTheory GlobalTheory.FrameOver
namespace GlobalTheory.FrameOver
theorem _root_.solution {E : Type} [CommRing E] {r : ℕ} (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hZ : IsUnit Z.det) (T T' : E) :
    (Matrix.fromBlocks Z (Matrix.single (Fin.last r) (Fin.last r) T)
      (Matrix.single (Fin.last r) (Fin.last r) T') Z').det =
    Z.det * Z'.det - T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det *
      (Z'.submatrix Fin.castSucc Fin.castSucc).det) := by
  let := Z.invertibleOfIsUnitDet hZ
  have hadj : ∀ A : Matrix (Fin (r + 1)) (Fin (r + 1)) E, A.adjugate (Fin.last r) (Fin.last r) =
      (A.submatrix Fin.castSucc Fin.castSucc).det := fun A => by
    simp [Matrix.adjugate_fin_succ_eq_det_submatrix, ← two_mul]
  have hupd : ∀ c : E, (Z' - Matrix.single (Fin.last r) (Fin.last r) c).det =
      Z'.det - c * (Z'.submatrix Fin.castSucc Fin.castSucc).det := fun c => by
    have : Z' - Matrix.single (Fin.last r) (Fin.last r) c =
        Z'.updateRow (Fin.last r) (Z' (Fin.last r) + (-c) • Pi.single (Fin.last r) 1) := by
      ext i j
      by_cases hi : i = Fin.last r
      · subst hi
        by_cases hj : j = Fin.last r
        · subst hj; simp [sub_eq_add_neg]
        · simp [hj, Matrix.single_apply, Ne.symm hj]
      · simp [hi, Matrix.single_apply, Ne.symm hi]
    rw [this, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
      ← Matrix.adjugate_apply, hadj]
    ring
  rw [Matrix.det_fromBlocks₁₁, Matrix.single_mul_mul_single, hupd, Matrix.invOf_eq_nonsing_inv,
    Matrix.inv_def, Matrix.smul_apply, hadj, smul_eq_mul]
  have := Ring.mul_inverse_cancel _ hZ
  linear_combination (-(T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det *
      (Z'.submatrix Fin.castSucc Fin.castSucc).det))) * this
end GlobalTheory.FrameOver
