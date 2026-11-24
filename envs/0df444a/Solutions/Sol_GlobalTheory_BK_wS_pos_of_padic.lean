-- Prove2me | solution 1 for GlobalTheory.BK.wS_pos_of_padic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:40:43.581982+00:00
-- url     : https://prove2.me/submissions/c59ef5df-d9ee-4e4f-9649-1a73f04b1dc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BK PowerSeries Filter Topology
open GlobalTheory GlobalTheory.BK
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
omit [IsUltrametricDist K]
include l
namespace GlobalTheory.BK
theorem _root_.solution (m : ℕ) : 0 < wS K e m :=
  norm_pos_iff.2 (natCast_ne_zero' l (Nat.factorial_ne_zero _))
end GlobalTheory.BK
