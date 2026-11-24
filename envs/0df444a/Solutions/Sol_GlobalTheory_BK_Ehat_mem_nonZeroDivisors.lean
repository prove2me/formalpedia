-- Prove2me | solution 1 for GlobalTheory.BK.Ehat_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:57.619828+00:00
-- url     : https://prove2.me/submissions/42a378a6-ecdd-4a80-969e-b3eebd44e394

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Theorems.Thm_GlobalTheory_BK_algebraMap_mem_nonZeroDivisors_adicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
namespace GlobalTheory.BK
theorem _root_.solution (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : Ehat O K l e ∈ nonZeroDivisors (Ahat O K l e) :=
  algebraMap_mem_nonZeroDivisors_adicCompletion (mem_nonZeroDivisors_of_ne_zero fun h =>
    (isUnit_E (K := K) l e).ne_zero (congrArg Subtype.val h))
end GlobalTheory.BK
