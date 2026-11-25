-- Prove2me | solution 1 for GlobalTheory.ConjSize.Un.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:36:19.9248+00:00
-- url     : https://prove2.me/submissions/eb1e2468-7c65-4220-9556-f49a98be6445

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
theorem _root_.solution {z : ℂ} (h : Un ι τ z) : Un ι τ z⁻¹ := by
  obtain ⟨y, e, hy⟩ := h
  exact ⟨y⁻¹, by rw [map_inv₀, e], by rw [map_inv₀, norm_inv, hy, inv_one]⟩
end Un
end GlobalTheory.ConjSize
