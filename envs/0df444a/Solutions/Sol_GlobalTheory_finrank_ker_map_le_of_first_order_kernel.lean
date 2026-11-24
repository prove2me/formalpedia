-- Prove2me | solution 1 for GlobalTheory.finrank_ker_map_le_of_first_order_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:05.753063+00:00
-- url     : https://prove2.me/submissions/19b1dd6a-21e0-47ed-a33a-ea2350d42189

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankKerMapLeOfFirstOrderKernelExt
import Theorems.Thm_GlobalTheory_finrank_le_of_first_order_kernel
import Theorems.Thm_GlobalTheory_rank_le_rank_map_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (a e : ℕ) (Φ : Matrix (Fin a) (Fin a) k) (U : Type) [AddCommGroup U] [Module k U] [Module.Finite k U] (t u : LinearMap.ker Φ.mulVecLin →ₗ[k] U), (∀ x0 x1 : Fin (e + 1) → LinearMap.ker Φ.mulVecLin, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → Module.finrank K (LinearMap.ker (Φ.map (algebraMap k K)).mulVecLin) ≤ Module.finrank k U + e := by
  intro k K _ _ _ a e Φ U _ _ _ t u h
  have h1 := finrank_le_of_first_order_kernel k (LinearMap.ker Φ.mulVecLin) U e t u h
  have h2 := rank_le_rank_map_algebraMap k K a Φ
  have hk := LinearMap.finrank_range_add_finrank_ker Φ.mulVecLin
  have hK := LinearMap.finrank_range_add_finrank_ker (Φ.map (algebraMap k K)).mulVecLin
  rw [Module.finrank_fin_fun] at hk hK
  unfold Matrix.rank at h2
  omega
end GlobalTheory
