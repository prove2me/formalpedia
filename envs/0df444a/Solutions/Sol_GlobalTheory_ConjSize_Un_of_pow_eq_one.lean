-- Prove2me | solution 1 for GlobalTheory.ConjSize.Un.of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:36:29.667307+00:00
-- url     : https://prove2.me/submissions/5b27cbce-e620-4c8b-a74e-b7a55a403cfb

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
theorem _root_.solution {z : ℂ} (hz : z ∈ Set.range ι) {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) : Un ι τ z := by
  obtain ⟨y, rfl⟩ := hz
  have h1 : y ^ n = 1 := ι.injective (by rw [map_pow, h, map_one])
  have h2 : ‖τ y‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact ⟨y, rfl, (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2⟩
end Un
end GlobalTheory.ConjSize
