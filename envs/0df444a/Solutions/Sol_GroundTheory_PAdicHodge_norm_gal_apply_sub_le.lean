-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_gal_apply_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:06.237706+00:00
-- url     : https://prove2.me/submissions/c1bea00d-13fd-4ffa-b810-aeaa85c8d7be

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (x b : PadicAlgCl p) {ρ : ℝ}
    (hρ : ∀ σ : Gal(PadicAlgCl p/K), ‖σ x - x‖ ≤ ρ) (σ : Gal(PadicAlgCl p/K)) :
    ‖σ b - b‖ ≤ max ‖x - b‖ ρ := by
  have h1 : σ b - b = (σ (b - x) + (σ x - x)) + (x - b) := by rw [map_sub]; ring
  have h2 : ‖σ (b - x)‖ = ‖x - b‖ := by rw [norm_gal_apply, norm_sub_rev]
  rw [h1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (le_max_left _ _))
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [h2]; exact le_max_left _ _
  · exact (hρ σ).trans (le_max_right _ _)
end GroundTheory.PAdicHodge
