-- Prove2me | solution 1 for GlobalTheory.ConjSize.Un.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:45.868394+00:00
-- url     : https://prove2.me/submissions/bc18b3f3-eb0c-48af-b646-6010abd30430

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz

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
namespace Un
theorem _root_.solution {z z' : ℂ} (h : Un ι τ z) (h' : Un ι τ z') : Un ι τ (z * z') := by
  obtain ⟨y, e, hy⟩ := h
  obtain ⟨y', e', hy'⟩ := h'
  exact ⟨y * y', by rw [map_mul, e, e'], by rw [map_mul, norm_mul, hy, hy', one_mul]⟩
end Un
end GlobalTheory.ConjSize
