-- Prove2me | solution 1 for GlobalTheory.DiscUniformisation.disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:11.157873+00:00
-- url     : https://prove2.me/submissions/ddfa3e33-4288-4c31-92c5-952fca83b99a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero
import Theorems.Thm_P2M_GlobalTheory_DiscUniformisation____ne_zero_6e8e510ab80d
import Theorems.Thm_GlobalTheory_DiscUniformisation_im_ne_zero
import Theorems.Thm_GlobalTheory_DiscUniformisation_swap_G
import Theorems.Thm_GlobalTheory_DiscUniformisation_disc_of_pos

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
theorem _root_.solution (L : PeriodPair) : L.g₂ ^ 3 ≠ 27 * L.g₃ ^ 2 := by
  rcases lt_or_gt_of_ne (im_ne_zero L) with h | h
  · have hω₁ : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
    have h' : 0 < ((swap L).ω₁ / (swap L).ω₂).im := by
      show 0 < (L.ω₂ / L.ω₁).im
      rw [← inv_div, Complex.inv_im]
      exact div_pos (neg_pos.2 h) (Complex.normSq_pos.2 (div_ne_zero hω₁ (ω₂_ne_zero L)))
    have h2 := disc_of_pos (swap L) h'
    have e2 : (swap L).g₂ = L.g₂ := by simp only [PeriodPair.g₂, swap_G]
    have e3 : (swap L).g₃ = L.g₃ := by simp only [PeriodPair.g₃, swap_G]
    rwa [e2, e3] at h2
  · exact disc_of_pos L h
end GlobalTheory.DiscUniformisation
