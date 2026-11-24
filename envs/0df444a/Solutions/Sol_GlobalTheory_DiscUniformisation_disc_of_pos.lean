-- Prove2me | solution 1 for GlobalTheory.DiscUniformisation.disc_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:08:06.988952+00:00
-- url     : https://prove2.me/submissions/31cdcc71-259e-4a80-84b0-f5d47cc0d4ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero
import Theorems.Thm_GlobalTheory_DiscUniformisation_E_cube_ne
import Theorems.Thm_GlobalTheory_DiscUniformisation_g_eq
import Theorems.Thm_P2M_GlobalTheory_DiscUniformisation____ne_zero_6e8e510ab80d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries Filter Topology
open GlobalTheory GlobalTheory.DiscUniformisation
namespace GlobalTheory.DiscUniformisation
theorem _root_.solution (L : PeriodPair) (h : 0 < (L.ω₁ / L.ω₂).im) : L.g₂ ^ 3 ≠ 27 * L.g₃ ^ 2 := by
  intro hc
  have hω := ω₂_ne_zero L
  set z : ℍ := UpperHalfPlane.mk (L.ω₁ / L.ω₂) h with hzdef
  have hz : L.ω₁ = L.ω₂ * z := by
    rw [hzdef, UpperHalfPlane.coe_mk]
    field_simp
  obtain ⟨e2, e3⟩ := g_eq L z hz
  rw [e2, e3] at hc
  apply E_cube_ne z
  have hπ : ((Real.pi : ℂ) * L.ω₂⁻¹) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (inv_ne_zero hω)
  have h0 : ((Real.pi : ℂ) * L.ω₂⁻¹) ^ 12 * (64 / 27) * (E₄ z ^ 3 - E₆ z ^ 2) = 0 := by
    linear_combination hc
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exfalso
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact pow_ne_zero _ hπ h2
    · norm_num at h2
  · exact sub_eq_zero.1 h1
end GlobalTheory.DiscUniformisation
