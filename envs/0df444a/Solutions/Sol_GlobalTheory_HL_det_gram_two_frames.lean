-- Prove2me | solution 1 for GlobalTheory.HL.det_gram_two_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:12:28.688752+00:00
-- url     : https://prove2.me/submissions/269016aa-2cff-41f3-bcdf-2bd1aef2bda1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
import Theorems.Thm_GlobalTheory_HL_det_fromBlocks_swapCols
import Theorems.Thm_GlobalTheory_HL_det_updateRow_last_single
import Theorems.Thm_GlobalTheory_HL_det_fromBlocks_rowBlocks
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {R : Type} [CommRing R] (r : ℕ)
    (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (T T' : R) :
    (Matrix.fromBlocks (Matrix.single (Fin.last r) (Fin.last r) (-T)) Z Z'
      (Matrix.single (Fin.last r) (Fin.last r) (-T'))).det =
      (-1) ^ (r + 1) * (Z.det * Z'.det - T * T' *
        ((Z.submatrix Fin.castSucc Fin.castSucc).det *
          (Z'.submatrix Fin.castSucc Fin.castSucc).det)) := by
  have hs : ∀ t : R, Matrix.single (Fin.last r) (Fin.last r) t =
      (0 : Matrix (Fin (r + 1)) (Fin (r + 1)) R).updateRow (Fin.last r)
        (Pi.single (Fin.last r) t) := by
    intro t
    ext i j
    simp only [Matrix.updateRow_apply, Matrix.single_apply, Pi.single_apply, Matrix.zero_apply]
    by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;>
      simp [hi, hj, eq_comm]
  rw [det_fromBlocks_swapCols, hs, hs, det_fromBlocks_rowBlocks, det_updateRow_last_single,
    det_updateRow_last_single, Fintype.card_fin]
  ring
end GlobalTheory.HL
