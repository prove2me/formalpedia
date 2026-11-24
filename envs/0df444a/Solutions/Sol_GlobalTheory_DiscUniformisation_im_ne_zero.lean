-- Prove2me | solution 1 for GlobalTheory.DiscUniformisation.im_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:23:28.952906+00:00
-- url     : https://prove2.me/submissions/21f9751c-0f86-4226-a947-5c24b46b1d7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero
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
theorem _root_.solution (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  intro h
  have hω := ω₂_ne_zero L
  set r := (L.ω₁ / L.ω₂).re with hr
  have hz : L.ω₁ / L.ω₂ = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [h])
  have h1 : L.ω₁ = (r : ℂ) * L.ω₂ := by rw [← hz]; field_simp
  have h2 := (LinearIndependent.pair_iff.1 L.indep) 1 (-r) (by
    rw [one_smul, Complex.real_smul, h1]
    push_cast
    ring)
  exact one_ne_zero h2.1
end GlobalTheory.DiscUniformisation
