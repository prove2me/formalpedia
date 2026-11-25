-- Prove2me | solution 1 for GlobalTheory.SignedBlockCount.minor_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:23:31.139168+00:00
-- url     : https://prove2.me/submissions/2beb32d9-ee0f-4478-a6be-6d9a295a80f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SignedBlockAntidiagWithLeadingMinorsEncardLe
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.SignedBlockCount
open Formalism.MainNotions.S.Loc
variable {K : Type} [Field K]
namespace GlobalTheory.SignedBlockCount
theorem _root_.solution (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) (l : ℕ) :
    minor ((t, s) :: bs) (s + l) =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) *
        (t : K) ^ (s : ℕ)) * minor bs l := by
  have key : (Matrix.of fun a b : Fin (s + l) => ptEntryL ((t, s) :: bs) a b).submatrix
      finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks ((Matrix.diagonal (fun _ : Fin s => (t : K))).submatrix id
          (Fin.revPerm : Equiv.Perm (Fin s))) 0 0
        (Matrix.of fun a b : Fin l => ptEntryL bs a b) := by
    ext (a | a) (b | b)
    · have ha := a.2
      have hb := b.2
      simp only [Matrix.submatrix_apply, Matrix.of_apply, ptEntryL, finSumFinEquiv_apply_left,
        Fin.val_castAdd, Matrix.fromBlocks_apply₁₁, id, Matrix.diagonal_apply, Fin.revPerm_apply,
        Fin.ext_iff, Fin.val_rev]
      split_ifs <;> first | rfl | omega
    · simp [ptEntryL]
    · simp [ptEntryL]
    · simp [ptEntryL]
  rw [minor, ← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_permute', Matrix.det_diagonal]
  simp [minor]
end GlobalTheory.SignedBlockCount
