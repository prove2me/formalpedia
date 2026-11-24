-- Prove2me | solution 1 for GroundTheory.PAdicHodge.tiltSharp_mem_untiltField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:41.693994+00:00
-- url     : https://prove2.me/submissions/70f7a1ad-f3a9-4e6f-9b81-ce6225990dff

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Theorems.Thm_GroundTheory_PAdicHodge_untilt_mem_untiltInteger
import Theorems.Thm_GroundTheory_PAdicHodge_coe_mem_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {N : IntermediateField K♭ C♭} {z : C♭} (hz : z ∈ N) : tiltSharp C p z ∈ untiltField K C p N := by
  have key : ∀ y : C♭, y ∈ N → ‖y‖ ≤ 1 → tiltSharp C p y ∈ untiltField K C p N := by
    intro y hy hy1
    obtain ⟨a, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hy1
    rw [tiltSharp_algebraMap]
    exact coe_mem_untiltField (untilt_mem_untiltInteger ((mem_integerTilt N).2 hy))
  rcases le_or_gt ‖z‖ 1 with h | h
  · exact key z hz h
  · have h0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at h; linarith
    have := key z⁻¹ (inv_mem hz) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h.le)
    rw [map_inv₀] at this
    simpa using inv_mem this
end GroundTheory.PAdicHodge
