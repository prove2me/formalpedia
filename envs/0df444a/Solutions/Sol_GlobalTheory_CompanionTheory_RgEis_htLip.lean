-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.htLip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:03:28.919649+00:00
-- url     : https://prove2.me/submissions/6bc8d7d9-8fea-433d-9500-9f51c58e05dd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeightLipschitzHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution : PositivityTheory.RgEis.HtLip := by
  intro G _ _ _ Γ K P η hK hI hη C hC
  obtain ⟨M, hM⟩ := (hK.mul hC).exists_bound_of_continuousOn hη.cont.continuousOn
  refine ⟨M, fun g u hu => ?_⟩
  obtain ⟨p, hp, k, hk, rfl⟩ := hI g
  have h1 : η (p * k * u) = η p + η (k * u) := by
    rw [mul_assoc]; exact hη.left p hp _
  have h2 : η (p * k) = η p + η k := hη.left p hp k
  have h3 : η (1 : G) = 0 := by
    have := hη.left 1 P.one_mem 1
    simp only [mul_one] at this
    linarith
  have h4 : η k = 0 := by
    have := hη.right 1 k hk
    rw [one_mul] at this
    rw [this, h3]
  have h5 := hM (k * u) (Set.mul_mem_mul hk hu)
  rw [Real.norm_eq_abs] at h5
  rw [h1, h2, h4]
  simpa using h5
end GlobalTheory.CompanionTheory.RgEis
