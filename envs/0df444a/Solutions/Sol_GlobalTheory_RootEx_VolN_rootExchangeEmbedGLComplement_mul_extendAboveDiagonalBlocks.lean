-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.rootExchangeEmbedGLComplement_mul_extendAboveDiagonalBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:03:21.172901+00:00
-- url     : https://prove2.me/submissions/b1f49664-e91c-4ff9-a91f-9b1f280b6718

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_VolN_mul_matrixExtendSelectedEntriesByZero_apply
import Theorems.Thm_GlobalTheory_RootEx_VolN_val_embX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution (p : ℕ) (x : GL n k) (e : Ix n c p → k) :
    (embX c x).val * ext0 (Up n c p) e = ext0 (Up n c p) ((lm (Up n c p) (embX c x).val).mulVec e) := by
  ext r s
  by_cases h : lev p r < lev p s
  · rw [mul_matrixExtendSelectedEntriesByZero_apply (Up n c p) _ e ⟨(r, s), h⟩]
    simp [ext0, h]
  · have h0 : ∀ t, lev p t = lev p r → ∀ e : Ix n c p → k, ext0 (Up n c p) e t s = 0 := by
      intro t ht e
      simp only [ext0, Matrix.of_apply]
      rw [dif_neg]
      simpa [ht] using h
    rw [h0 r rfl, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    rcases r with r | r <;> rcases t with t | t
    · rw [h0 (Sum.inl t) rfl, mul_zero]
    · simp [val_embX]
    · simp [val_embX]
    · by_cases hrt : r = t
      · rw [h0 _ (by rw [hrt]), mul_zero]
      · simp [val_embX, hrt]
end GlobalTheory.RootEx.VolN
