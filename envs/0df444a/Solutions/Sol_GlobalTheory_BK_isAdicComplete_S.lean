-- Prove2me | solution 1 for GlobalTheory.BK.isAdicComplete_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:55.099301+00:00
-- url     : https://prove2.me/submissions/e9804d6f-c0c0-4963-95b5-6b491678ab5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
import Theorems.Thm_GlobalTheory_BK_isHausdorff_S
import Theorems.Thm_GlobalTheory_BK_isPrecomplete_S

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
namespace GlobalTheory.BK
theorem _root_.solution (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : IsAdicComplete (Ideal.span {(l : S O K e)}) (S O K e) :=
  { toIsHausdorff := isHausdorff_S l e, toIsPrecomplete := isPrecomplete_S l e }
end GlobalTheory.BK
