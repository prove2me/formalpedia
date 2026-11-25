-- Prove2me | solution 1 for GlobalTheory.HL.det_updateRow_last_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:15:42.847648+00:00
-- url     : https://prove2.me/submissions/b5eff8d9-da0c-418e-8750-42b9d16d0490

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
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
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (t : R) :
    (Z.updateRow (Fin.last r) (Pi.single (Fin.last r) t)).det =
      t * (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · have : (Z.updateRow (Fin.last r) (Pi.single (Fin.last r) t)).submatrix
        (Fin.last r).succAbove (Fin.last r).succAbove =
        Z.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp [Matrix.updateRow_apply, Fin.succAbove_last, Fin.castSucc_ne_last]
    rw [this]
    simp [← two_mul, pow_mul]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp
end GlobalTheory.HL
