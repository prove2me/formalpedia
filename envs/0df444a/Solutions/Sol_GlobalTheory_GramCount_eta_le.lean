-- Prove2me | solution 1 for GlobalTheory.GramCount.eta_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:06:24.681932+00:00
-- url     : https://prove2.me/submissions/91a883f3-4c8f-46c9-b3f7-ad9ff0292cdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTupleExtensionsLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesWithGramMatrixResidueRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
variable {B : Type} [CommRing B]
namespace GlobalTheory.GramCount
theorem _root_.solution {m n : ℕ} (h : 2 * m + 3 ≤ n) : (2 : ℝ) ^ (2 * m + 1) / 2 ^ n ≤ 1 / 4 := by
  rw [div_le_iff₀ (by positivity)]
  have : (2 : ℝ) ^ (2 * m + 3) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
  have h2 : (2 : ℝ) ^ (2 * m + 3) = 4 * 2 ^ (2 * m + 1) := by ring
  linarith
end GlobalTheory.GramCount
