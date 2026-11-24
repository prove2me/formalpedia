-- Prove2me | solution 1 for GlobalTheory.DiscUniformisation.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:19.218324+00:00
-- url     : https://prove2.me/submissions/a3e90c97-ce5c-4069-a254-d0e228d7ef4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero
import Theorems.Thm_GlobalTheory_DiscUniformisation_disc
import Theorems.Thm_GlobalTheory_DiscUniformisation_uniformisation

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
theorem _root_.solution (σ : ℂ ≃+* ℂ) (L : PeriodPair) :
    ∃ L' : PeriodPair, L'.g₂ = σ L.g₂ ∧ L'.g₃ = σ L.g₃ := by
  apply uniformisation
  intro h
  apply disc L
  apply σ.injective
  simp only [map_pow, map_mul, map_ofNat]
  exact h
end GlobalTheory.DiscUniformisation
