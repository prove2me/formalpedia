-- Prove2me | solution 1 for GroundTheory.Automorphic.norm_iteratedFDeriv_sub_translate_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:20.308801+00:00
-- url     : https://prove2.me/submissions/5bbb6fc0-ea61-4629-9d17-165c632eeb56

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_AltSum
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_MixedDifference
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
theorem _root_.solution {k : ℕ} {ρ : E → F} (hρ : ContDiff ℝ (k + 1) ρ)
    {B : ℝ} (hB : ∀ w, ‖iteratedFDeriv ℝ (k + 1) ρ w‖ ≤ B) (y w : E) :
    ‖iteratedFDeriv ℝ k (fun t => ρ (t + y) - ρ t) w‖ ≤ B * ‖y‖ := by
  have h1 : ContDiff ℝ k ρ := hρ.of_le (by exact_mod_cast Nat.le_succ k)
  have h2 : ContDiff ℝ k (fun t => ρ (t + y)) := h1.comp (contDiff_id.add contDiff_const)
  have hsub : iteratedFDeriv ℝ k (fun t => ρ (t + y) - ρ t) w =
      iteratedFDeriv ℝ k ρ (w + y) - iteratedFDeriv ℝ k ρ w := by
    have := iteratedFDeriv_sub_apply (x := w) (i := k) h2.contDiffAt h1.contDiffAt
    rw [show (fun t => ρ (t + y) - ρ t) = (fun t => ρ (t + y)) - ρ from rfl, this,
      iteratedFDeriv_comp_add_right]
  rw [hsub]
  have hdiff : Differentiable ℝ (fun x => iteratedFDeriv ℝ k ρ x) :=
    hρ.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (f := fun x => iteratedFDeriv ℝ k ρ x) (x := w) (y := w + y) (C := B)
    (fun x _ => hdiff x) (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hB x)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa using this
end GroundTheory.Automorphic
