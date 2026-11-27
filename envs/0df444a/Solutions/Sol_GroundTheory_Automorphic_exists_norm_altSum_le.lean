-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_norm_altSum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:11.789593+00:00
-- url     : https://prove2.me/submissions/f3772353-bf60-4d40-b5e6-81f3a7cb0544

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_AltSum
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_MixedDifference
import Theorems.Thm_GroundTheory_Automorphic_norm_altSum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
namespace GroundTheory.Automorphic
theorem _root_.solution {ρ : E → F} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hc : HasCompactSupport ρ) (k : ℕ) :
    ∃ B : ℝ, ∀ (v : Fin k → E) (z : E), ‖altSum k ρ v z‖ ≤ B * ∏ i, ‖v i‖ := by
  have hcont : Continuous fun x => iteratedFDeriv ℝ k ρ x :=
    hρ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support (hc.iteratedFDeriv k)
  exact ⟨B, norm_altSum_le k (hρ.of_le (by exact_mod_cast le_top)) hB⟩
end GroundTheory.Automorphic
