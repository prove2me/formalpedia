-- Prove2me | solution 1 for GlobalTheory.BK.mem_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:25:38.275829+00:00
-- url     : https://prove2.me/submissions/61ad6107-d0c5-4bfc-8fe6-cdfe3cd5e140

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
namespace GlobalTheory.BK
theorem _root_.solution {f : K⟦X⟧} : f ∈ A O K ↔ ∀ n, ‖coeff n f‖ ≤ 1 := Iff.rfl
end GlobalTheory.BK
