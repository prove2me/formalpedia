-- Prove2me | solution 1 for GlobalTheory.T.finrank_ker_map_le_of_first_order_kernel_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:14.618744+00:00
-- url     : https://prove2.me/submissions/45078aa2-ae52-421c-a54f-e39b5ed56393

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankKerMapLeOfFirstOrderKernelExt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankKerMapLeOfFirstOrderKernelExtStatement
import Theorems.Thm_GlobalTheory_finrank_ker_map_le_of_first_order_kernel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (a e : ℕ) (Φ : Matrix (Fin a) (Fin a) k) (U : Type) [AddCommGroup U] [Module k U] [Module.Finite k U] (t u : LinearMap.ker Φ.mulVecLin →ₗ[k] U), (∀ x0 x1 : Fin (e + 1) → LinearMap.ker Φ.mulVecLin, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → Module.finrank K (LinearMap.ker (Φ.map (algebraMap k K)).mulVecLin) ≤ Module.finrank k U + e := by
  first | exact @GlobalTheory.finrank_ker_map_le_of_first_order_kernel | exact GlobalTheory.finrank_ker_map_le_of_first_order_kernel | (intros; apply GlobalTheory.finrank_ker_map_le_of_first_order_kernel <;> assumption)
end _root_.GlobalTheory.T
