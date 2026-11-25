-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_sub_one_eq_of_isPrimitiveRoot_of_isUltrametricDist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:34.621159+00:00
-- url     : https://prove2.me/submissions/bd91386e-ead0-4959-855a-07257128cec7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Theorems.Thm_GroundTheory_PAdicHodge_norm_le_one_of_pow_eq_one
import Theorems.Thm_GroundTheory_PAdicHodge_norm_one_sub_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open WittVector
open GroundTheory GroundTheory.PAdicHodge
variable {F : Type*} [NormedField F] [IsUltrametricDist F]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ζ μ : F} {k : ℕ} [NeZero k]
    (hζ : IsPrimitiveRoot ζ k) (hμ : IsPrimitiveRoot μ k) : ‖μ - 1‖ = ‖ζ - 1‖ := by
  have hk : k ≠ 0 := NeZero.ne k
  have h1 : ‖ζ‖ ≤ 1 := norm_le_one_of_pow_eq_one hk hζ.pow_eq_one
  have h2 : ‖μ‖ ≤ 1 := norm_le_one_of_pow_eq_one hk hμ.pow_eq_one
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
  obtain ⟨j, -, hj⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
  rw [norm_sub_rev, norm_sub_rev ζ]
  refine le_antisymm ?_ ?_
  · rw [← hi]; exact norm_one_sub_pow_le h1 i
  · rw [← hj]; exact norm_one_sub_pow_le h2 j
end GroundTheory.PAdicHodge
