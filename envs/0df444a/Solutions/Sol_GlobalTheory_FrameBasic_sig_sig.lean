-- Prove2me | solution 1 for GlobalTheory.FrameBasic.sig_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:28:08.590579+00:00
-- url     : https://prove2.me/submissions/33200ab7-a8cd-4fc0-935e-de0e629a9914

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
theorem _root_.solution : ∀ (bs : List (Eˣ × ℕ+)) (a : ℕ), sig bs (sig bs a) = a
  | [], a => rfl
  | (t, s) :: bs, a => by
    by_cases h : a < s
    · have h2 : (s : ℕ) - 1 - a < s := by omega
      simp only [sig_cons, h, h2, if_true]; omega
    · have h2 : ¬ ((s : ℕ) + sig bs (a - s) < s) := by omega
      simp only [sig_cons, h, h2, if_false, Nat.add_sub_cancel_left, solution bs]; omega
end GlobalTheory.FrameBasic
