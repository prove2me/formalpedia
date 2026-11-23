-- Prove2me | solution 1 for GlobalTheory.CofactorOrder.ker_eq_bot_of_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:26.36536+00:00
-- url     : https://prove2.me/submissions/62d31b57-feeb-477e-b41f-02e59f192fab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel
import Theorems.Thm_GlobalTheory_CofactorOrder_mulVec_eq_zero_of_det

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
theorem _root_.solution {P : Matrix n n K} (hP : P.det = 1) :
    LinearMap.ker P.mulVecLin = ⊥ := by
  refine LinearMap.ker_eq_bot'.mpr fun v hv => ?_
  rw [mulVecLin_apply] at hv
  exact mulVec_eq_zero_of_det hP hv
end GlobalTheory.CofactorOrder
