-- Prove2me | solution 1 for GlobalTheory.HL.det_fromBlocks_swapCols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:00:39.118196+00:00
-- url     : https://prove2.me/submissions/64777c0a-5202-4e3a-8ede-3677685d4c20

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
theorem _root_.solution {R n : Type} [CommRing R] [Fintype n] [DecidableEq n]
    (A B C D : Matrix n n R) :
    (Matrix.fromBlocks A B C D).det = (-1) ^ Fintype.card n * (Matrix.fromBlocks B A D C).det := by
  have h : Matrix.fromBlocks A B C D =
      Matrix.fromBlocks B A D C * (Matrix.fromBlocks (1 : Matrix n n R) 1 0 1 *
        Matrix.fromBlocks (1 : Matrix n n R) 0 (-1) 1 * Matrix.fromBlocks (1 : Matrix n n R) 1 0 1 *
        Matrix.fromBlocks (-1 : Matrix n n R) 0 0 1) := by
    simp [Matrix.fromBlocks_multiply]
  rw [h]
  simp only [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, Matrix.det_neg, mul_one, one_mul]
  ring
end GlobalTheory.HL
