-- Prove2me | solution 1 for GlobalTheory.ConjSize.Sz.rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:43:35.458816+00:00
-- url     : https://prove2.me/submissions/94859ea5-b20e-4d40-827f-5c30bdf1c1eb

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
namespace Sz
theorem _root_.solution (q : ℚ) : Sz ι τ (q : ℂ) |(q : ℝ)| := by
  haveI : CharZero K := ι.charZero
  refine ⟨(q : K), map_ratCast _ _, ?_⟩
  rw [map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
end Sz
end GlobalTheory.ConjSize
