-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_le_one_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:08.248801+00:00
-- url     : https://prove2.me/submissions/8537cc8e-4dfd-41a4-a253-fc3851f8093f

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
omit [IsUltrametricDist F]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ζ : F} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : ‖ζ‖ ≤ 1 := by
  by_contra hlt
  have := one_lt_pow₀ (lt_of_not_ge hlt) hn
  rw [← norm_pow, h, norm_one] at this
  exact lt_irrefl _ this
end GroundTheory.PAdicHodge
