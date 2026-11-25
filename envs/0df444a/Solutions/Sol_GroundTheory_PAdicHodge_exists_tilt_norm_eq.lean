-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_tilt_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:00:13.268578+00:00
-- url     : https://prove2.me/submissions/d714ce6c-6296-4466-aea8-2d2c186d5760

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_TiltCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_untilt_eq_norm

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
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology NNReal
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "♮" x:max => ((PreTilt.untilt x : normInteger K) : K)
namespace GroundTheory.PAdicHodge
theorem _root_.solution {y : K} (hy : y ≠ 0) : ∃ x : K♭, ‖x‖ = ‖y‖ := by
  rcases le_or_gt ‖y‖ 1 with h | h
  · obtain ⟨a, ha⟩ := exists_norm_untilt_eq_norm (p := p) hy h
    exact ⟨algebraMap 𝒪♭ K♭ a, by rw [norm_algebraMap_preTilt, preTilt_norm_def, ha]⟩
  · obtain ⟨a, ha⟩ := exists_norm_untilt_eq_norm (p := p) (inv_ne_zero hy)
      (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h.le)
    refine ⟨(algebraMap 𝒪♭ K♭ a)⁻¹, ?_⟩
    rw [norm_inv, norm_algebraMap_preTilt, preTilt_norm_def, ha, norm_inv, inv_inv]
end GroundTheory.PAdicHodge
