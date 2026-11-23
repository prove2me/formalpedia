-- Prove2me | solution 1 for GlobalTheory.NormPowSubOne.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:02.554646+00:00
-- url     : https://prove2.me/submissions/73e55885-f5eb-4850-83c4-69ec5dc9c846

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormPowSubOneLe
import Theorems.Thm_GlobalTheory_NormPowSubOne_norm_pow_sub_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.NormPowSubOne
namespace GlobalTheory.NormPowSubOne
theorem _root_.solution : ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] {ζ : K},
    ‖ζ‖ = (1 : ℝ) → ∀ (a : ℕ), ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ :=
  fun hζ a => norm_pow_sub_one_le hζ a
end GlobalTheory.NormPowSubOne
