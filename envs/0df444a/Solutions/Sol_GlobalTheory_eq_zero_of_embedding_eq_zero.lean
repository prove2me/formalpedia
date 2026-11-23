-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_embedding_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:01.58886+00:00
-- url     : https://prove2.me/submissions/aa1303f1-1929-4413-bfdd-75f74643619f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]
namespace GlobalTheory
theorem _root_.solution {A : Type*} [Ring A] [Nontrivial A] (σ : K →+* A) {x : K}
    (h : σ x = 0) : x = 0 :=
  (map_eq_zero σ).mp h
end GlobalTheory
