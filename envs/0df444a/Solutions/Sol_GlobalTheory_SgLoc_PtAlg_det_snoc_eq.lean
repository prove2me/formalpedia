-- Prove2me | solution 1 for GlobalTheory.SgLoc.PtAlg.det_snoc_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:30.481994+00:00
-- url     : https://prove2.me/submissions/30b08140-77a0-4b8c-ad3d-39b7ca2906c4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Theorems.Thm_GlobalTheory_SgLoc_PtAlg_mat_snoc
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
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.PtAlg
variable {E : Type} [CommRing E]
namespace GlobalTheory.SgLoc.PtAlg
theorem _root_.solution {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det =
      h.mat.det * (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) *
        (t : E) ^ (s : ℕ)) := by
  have key : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (h.snoc t s).mat =
      Matrix.fromBlocks h.mat 0 0
        ((t : E) • (Fin.revPerm : Equiv.Perm (Fin s)).permMatrix E) := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, mat_snoc,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] <;>
      have hi := i.isLt <;> have hj := j.isLt
    · rw [dif_pos ⟨hi, hj⟩]
    · rw [dif_neg (by omega), if_neg (by omega)]
    · rw [dif_neg (by omega), if_neg (by omega)]
    · rw [dif_neg (by omega)]
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
      by_cases hij : Fin.rev i = j
      · rw [if_pos (by rw [← hij, Fin.val_rev]; omega), if_pos hij, mul_one]
      · rw [if_neg (fun hc => hij (Fin.ext (by rw [Fin.val_rev]; omega))), if_neg hij, mul_zero]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul,
    Matrix.det_permutation, Fintype.card_fin] at hdet
  rw [hdet]
  ring
end GlobalTheory.SgLoc.PtAlg
