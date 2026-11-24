-- Prove2me | solution 1 for GlobalTheory.BK.away_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:00:10.138331+00:00
-- url     : https://prove2.me/submissions/f609a34c-58e7-4a9e-99d1-e43d06e56d7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}
omit [IsUltrametricDist K] [IsUnitBall O K]
namespace GlobalTheory.BK
theorem _root_.solution {B B' : Subalgebra O K⟦X⟧} (h : B ≤ B') {s : B} {s' : B'}
    (hs : (s : K⟦X⟧) = s') : away B s ≤ away B' s' := fun _ ⟨n, hn⟩ => ⟨n, hs ▸ h hn⟩
end GlobalTheory.BK
