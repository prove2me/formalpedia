-- Prove2me | solution 1 for GroundTheory.Automorphic.norm_altSum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:43.333485+00:00
-- url     : https://prove2.me/submissions/389b1a09-3361-41a7-b6c0-4c1769e48cd3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_AltSum
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_MixedDifference
import Theorems.Thm_GroundTheory_Automorphic_norm_iteratedFDeriv_sub_translate_le
import Theorems.Thm_GroundTheory_Automorphic_altSum_succ
import Theorems.Thm_GroundTheory_Automorphic_altSum_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.altSum_zero



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
namespace GroundTheory.Automorphic
theorem _root_.solution : ∀ (k : ℕ) {ρ : E → F}, ContDiff ℝ k ρ → ∀ {B : ℝ},
    (∀ w, ‖iteratedFDeriv ℝ k ρ w‖ ≤ B) → ∀ (v : Fin k → E) (z : E),
      ‖altSum k ρ v z‖ ≤ B * ∏ i, ‖v i‖
  | 0, ρ, _, B, hB, v, z => by
    simpa [norm_iteratedFDeriv_zero] using hB z
  | k + 1, ρ, hρ, B, hB, v, z => by
    rw [altSum_succ, Fin.prod_univ_succ, ← mul_assoc]
    have hg : ContDiff ℝ k (fun t => ρ (t + v 0) - ρ t) :=
      ((hρ.of_le (by exact_mod_cast Nat.le_succ k)).comp (contDiff_id.add contDiff_const)).sub
        (hρ.of_le (by exact_mod_cast Nat.le_succ k))
    exact solution k hg (fun w => norm_iteratedFDeriv_sub_translate_le hρ hB (v 0) w)
      (Fin.tail v) z
end GroundTheory.Automorphic
