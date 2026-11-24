-- Prove2me | solution 1 for GlobalTheory.ConjSize.Sz.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:43:32.884987+00:00
-- url     : https://prove2.me/submissions/61fb9247-bb26-4ee1-af39-5a4d71f8bf8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open GlobalTheory GlobalTheory.ConjSize
variable {K : Type} [Field K] (ι τ : K →+* ℂ)
variable {ι τ}
namespace GlobalTheory.ConjSize
namespace Sz
theorem _root_.solution {z z' : ℂ} {B B' : ℝ} (h : Sz ι τ z B) (h' : Sz ι τ z' B') : Sz ι τ (z + z') (B + B') := by
  obtain ⟨y, e, hy⟩ := h
  obtain ⟨y', e', hy'⟩ := h'
  exact ⟨y + y', by rw [map_add, e, e'], by rw [map_add]; exact (norm_add_le _ _).trans (add_le_add hy hy')⟩
end Sz
end GlobalTheory.ConjSize
