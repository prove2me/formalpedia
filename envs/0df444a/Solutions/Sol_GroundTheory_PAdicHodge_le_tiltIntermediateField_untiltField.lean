-- Prove2me | solution 1 for GroundTheory.PAdicHodge.le_tiltIntermediateField_untiltField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:19.506977+00:00
-- url     : https://prove2.me/submissions/4a11941e-5e8f-429d-bdef-56c1d260bff1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltDegree
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Theorems.Thm_GroundTheory_PAdicHodge_iterate_frobeniusEquiv_symm_mem_integerTilt
import Theorems.Thm_GroundTheory_PAdicHodge_algebraMap_mem_tiltIntermediateField
import Theorems.Thm_GroundTheory_PAdicHodge_coe_mem_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_untilt_mem_untiltInteger
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
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (N : IntermediateField K♭ C♭)
    [FiniteDimensional K♭ N] : N ≤ tiltIntermediateField p (untiltField K C p N) := by
  have key : ∀ z ∈ N, ‖z‖ ≤ 1 → z ∈ tiltIntermediateField p (untiltField K C p N) := by
    intro z hz hz1
    obtain ⟨a, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hz1
    have ha : a ∈ integerTilt K C p N := (mem_integerTilt N).2 hz
    exact algebraMap_mem_tiltIntermediateField _ fun n =>
      coe_mem_untiltField (untilt_mem_untiltInteger (iterate_frobeniusEquiv_symm_mem_integerTilt ha n))
  intro z hz
  rcases le_or_gt ‖z‖ 1 with h | h
  · exact key z hz h
  · have h0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at h; linarith
    have := key z⁻¹ (inv_mem hz) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h.le)
    simpa using inv_mem this
end GroundTheory.PAdicHodge
