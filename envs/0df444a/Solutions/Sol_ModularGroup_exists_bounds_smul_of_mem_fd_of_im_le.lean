-- Prove2me | solution 1 for ModularGroup.exists_bounds_smul_of_mem_fd_of_im_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/2987757a-cf5b-5c9e-8806-be0706ee1313

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le

open scoped UpperHalfPlane MatrixGroups

theorem solution (S : Finset SL(2, ℤ)) (Y : ℝ) :
    ∃ B y₀ Y₁ : ℝ, 0 < y₀ ∧ ∀ σ ∈ S, ∀ z ∈ ModularGroup.fd, z.im ≤ Y →
      |(σ • z).re| ≤ B ∧ y₀ ≤ (σ • z).im ∧ (σ • z).im ≤ Y₁ := by
  set K : Set ℍ := ⋃ σ ∈ S, (fun z : ℍ => σ • z) '' ModularGroup.truncatedFundamentalDomain Y
  have hK : IsCompact K := S.isCompact_biUnion fun σ _ =>
    (ModularGroup.isCompact_truncatedFundamentalDomain Y).image (by
      change Continuous fun z : ℍ => ((σ : SL(2, ℝ)) • z)
      exact continuous_const_smul _)
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (continuous_abs.comp UpperHalfPlane.continuous_re).continuousOn
  obtain ⟨Y₁, hY₁⟩ := hK.bddAbove_image UpperHalfPlane.continuous_im.continuousOn
  obtain ⟨y₀, hy₀, hlow⟩ : ∃ y₀ : ℝ, 0 < y₀ ∧ ∀ w ∈ K, y₀ ≤ w.im := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, by simp [hKe]⟩
    · obtain ⟨x, -, hmin⟩ := hK.exists_isMinOn hKne UpperHalfPlane.continuous_im.continuousOn
      exact ⟨x.im, x.im_pos, fun w hw => hmin hw⟩
  refine ⟨B, y₀, Y₁, hy₀, fun σ hσ z hz hzY => ?_⟩
  have hw : σ • z ∈ K := Set.mem_iUnion₂.mpr ⟨σ, hσ, z, ⟨hz, hzY⟩, rfl⟩
  exact ⟨hB ⟨_, hw, rfl⟩, hlow _ hw, hY₁ ⟨_, hw, rfl⟩⟩

end S_ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le
end P2MW
export P2MW.S_ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le (solution)
