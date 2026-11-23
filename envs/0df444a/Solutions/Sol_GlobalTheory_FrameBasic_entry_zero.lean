-- Prove2me | solution 1 for GlobalTheory.FrameBasic.entry_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:26.407841+00:00
-- url     : https://prove2.me/submissions/9a49f769-5a34-400f-a264-cd0e79f141ad

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Theorems.Thm_GlobalTheory_FrameBasic_sig_cons
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
theorem _root_.solution : ∀ (bs : List (Eˣ × ℕ+)) (a b : ℕ), b ≠ sig bs a → ptEntryL bs a b = 0
  | [], a, b, _ => rfl
  | (t, s) :: bs, a, b, hb => by
    simp only [sig_cons] at hb
    simp only [ptEntryL]
    split_ifs with h1 h2 h3
    · rw [if_pos h1.1] at hb; omega
    · rfl
    · rw [if_neg (by omega)] at hb
      exact solution bs _ _ (by omega)
    · rfl
end GlobalTheory.FrameBasic
