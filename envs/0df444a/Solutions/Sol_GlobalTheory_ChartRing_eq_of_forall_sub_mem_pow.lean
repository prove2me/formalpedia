-- Prove2me | solution 1 for GlobalTheory.ChartRing.eq_of_forall_sub_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:49.206714+00:00
-- url     : https://prove2.me/submissions/a3d735a3-eca6-4d9e-9b23-164ebfc7956b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable (J : Ideal S) [IsAdicComplete J S] {s : S} (hs : s ∈ J)
namespace GlobalTheory.ChartRing
theorem _root_.solution {x y : S} (h : ∀ n, x - y ∈ J ^ n) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero]
  simpa using h n
end GlobalTheory.ChartRing
