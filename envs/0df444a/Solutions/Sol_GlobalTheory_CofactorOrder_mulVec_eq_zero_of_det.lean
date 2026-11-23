-- Prove2me | solution 1 for GlobalTheory.CofactorOrder.mulVec_eq_zero_of_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:04.361068+00:00
-- url     : https://prove2.me/submissions/523e3277-2b6d-4cfa-b6e5-78cc8541395f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory
open GlobalTheory.CofactorOrder
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CofactorOrder
theorem _root_.solution {P : Matrix n n K} (hP : P.det = 1) {v : n → K}
    (h : P *ᵥ v = 0) : v = 0 := by
  have hu : IsUnit P := (isUnit_iff_isUnit_det P).mpr (by rw [hP]; exact isUnit_one)
  exact (mulVec_injective_iff_isUnit.mpr hu) (by rw [h, mulVec_zero])
end GlobalTheory.CofactorOrder
