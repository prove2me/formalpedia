-- Prove2me | solution 1 for GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:07:43.934025+00:00
-- url     : https://prove2.me/submissions/b040f5e9-c4ed-4615-b918-e7df823d7239

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormMapRingOfIntegersLeOne
import Theorems.Thm_GlobalTheory_RingOfIntegersNormBound_norm_le_one_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RingOfIntegersNormBound
namespace GlobalTheory.RingOfIntegersNormBound
theorem _root_.solution {K : Type} [Field K] [NumberField K] {p : ℕ}
    [Fact (Nat.Prime p)] (f : K →+* ℂ_[p]) (c : NumberField.RingOfIntegers K) :
    ‖(f : K → ℂ_[p]) (↑c : K)‖ ≤ (1 : ℝ) :=
  norm_le_one_of_isIntegral (map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe c))
end GlobalTheory.RingOfIntegersNormBound
