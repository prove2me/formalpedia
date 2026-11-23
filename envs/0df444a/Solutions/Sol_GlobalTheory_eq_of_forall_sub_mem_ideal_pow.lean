-- Prove2me | solution 1 for GlobalTheory.eq_of_forall_sub_mem_ideal_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:04.504921+00:00
-- url     : https://prove2.me/submissions/53a2e970-a910-47d0-92ff-1864af3e78e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]
namespace GlobalTheory
theorem _root_.solution (J : Ideal S) [IsHausdorff J S] {x y : S}
    (h : ∀ n, x - y ∈ J ^ n) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero]
  simpa using h n
end GlobalTheory
