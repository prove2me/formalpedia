-- Prove2me | solution 1 for GlobalTheory.DiscUniformisation.swap_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:26:31.794307+00:00
-- url     : https://prove2.me/submissions/9f36f692-471d-4c47-a8ca-ef3ea77227af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero

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
theorem _root_.solution (L : PeriodPair) (k : ℕ) : (swap L).G k = L.G k := by
  unfold PeriodPair.G PeriodPair.lattice
  show ∑' (l : ↥(Submodule.span ℤ {L.ω₂, L.ω₁})), ((l : ℂ) ^ k)⁻¹ = _
  rw [Set.pair_comm L.ω₂ L.ω₁]
end GlobalTheory.DiscUniformisation
