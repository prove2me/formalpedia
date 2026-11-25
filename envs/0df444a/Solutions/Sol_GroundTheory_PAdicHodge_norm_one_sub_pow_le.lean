-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_one_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:58.558642+00:00
-- url     : https://prove2.me/submissions/c345cc09-c15c-45e8-a650-36e70ce8da58

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi

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
theorem _root_.solution {x : F} (hx : ‖x‖ ≤ 1) (m : ℕ) : ‖1 - x ^ m‖ ≤ ‖1 - x‖ := by
  rw [← mul_neg_geom_sum, norm_mul]
  have : ‖∑ i ∈ Finset.range m, x ^ i‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  calc ‖1 - x‖ * ‖∑ i ∈ Finset.range m, x ^ i‖ ≤ ‖1 - x‖ * 1 := by gcongr
    _ = ‖1 - x‖ := mul_one _
end GroundTheory.PAdicHodge
