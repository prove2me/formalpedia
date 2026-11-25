-- Prove2me | solution 1 for GlobalTheory.HL.fromBlocks_updateRow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:15:48.402073+00:00
-- url     : https://prove2.me/submissions/7a4ede4f-978a-4794-86f3-a08e5ed242c7

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
    (Z Z' : Matrix n n R) (l : n) (a b c d : n → R) :
    ((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) (Sum.elim a b)).updateRow (Sum.inr l)
        (Sum.elim c d) =
      Matrix.fromBlocks (Z.updateRow l a) ((0 : Matrix n n R).updateRow l b)
        ((0 : Matrix n n R).updateRow l c) (Z'.updateRow l d) := by
  ext (i | i) (j | j) <;> by_cases h : i = l <;> simp [Matrix.updateRow_apply, h]
end GlobalTheory.HL
