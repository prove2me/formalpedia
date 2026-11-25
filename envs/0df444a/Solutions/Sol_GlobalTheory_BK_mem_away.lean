-- Prove2me | solution 1 for GlobalTheory.BK.mem_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:25:48.034641+00:00
-- url     : https://prove2.me/submissions/71a92064-babf-44c9-8fed-1f542c89ba27

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
theorem _root_.solution {B : Subalgebra O K⟦X⟧} {s : B} {f : K⟦X⟧} :
    f ∈ away B s ↔ ∃ n : ℕ, (s : K⟦X⟧) ^ n * f ∈ B := Iff.rfl
end GlobalTheory.BK
