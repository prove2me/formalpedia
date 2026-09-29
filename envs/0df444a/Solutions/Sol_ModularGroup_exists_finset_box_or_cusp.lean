-- Prove2me | solution 1 for ModularGroup.exists_finset_box_or_cusp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0a562199-7025-5729-aea8-3e989fdb9403

import Mathlib
import Theorems.Thm_ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularGroup_exists_finset_box_or_cusp

open scoped UpperHalfPlane MatrixGroups

theorem solution (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (Y : ℝ) :
    ∃ (S : Finset SL(2, ℤ)) (B y₀ Y₁ : ℝ), 0 < y₀ ∧ ∀ τ : ℍ, ∃ γ ∈ Γ,
      (|(γ • τ).re| ≤ B ∧ y₀ ≤ (γ • τ).im ∧ (γ • τ).im ≤ Y₁) ∨
      (∃ σ ∈ S, ∃ z ∈ ModularGroup.fd, Y < z.im ∧ γ • τ = σ • z) := by
  classical

  obtain ⟨S, hS⟩ : ∃ S : Finset SL(2, ℤ), ∀ τ : ℍ, ∃ γ ∈ Γ, ∃ σ ∈ S,
      ∃ z ∈ ModularGroup.fd, γ • τ = σ • z := by
    haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
    refine ⟨Finset.univ.image fun q : SL(2, ℤ) ⧸ Γ => (Quotient.out q)⁻¹, fun τ => ?_⟩
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ g
    refine ⟨(h : SL(2, ℤ))⁻¹, Γ.inv_mem h.2, (Quotient.out (g : SL(2, ℤ) ⧸ Γ))⁻¹,
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, g • τ, hg, ?_⟩
    rw [hh, mul_inv_rev, mul_smul, inv_smul_smul]

  obtain ⟨B, y₀, Y₁, hy₀, hbox⟩ := ModularGroup.exists_bounds_smul_of_mem_fd_of_im_le S Y
  refine ⟨S, B, y₀, Y₁, hy₀, fun τ => ?_⟩
  obtain ⟨γ, hγ, σ, hσ, z, hz, he⟩ := hS τ
  refine ⟨γ, hγ, ?_⟩
  rcases le_or_gt z.im Y with hzY | hzY
  · left; rw [he]; exact hbox σ hσ z hz hzY
  · right; exact ⟨σ, hσ, z, hz, hzY, he⟩

end S_ModularGroup_exists_finset_box_or_cusp
end P2MW
export P2MW.S_ModularGroup_exists_finset_box_or_cusp (solution)
