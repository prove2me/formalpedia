-- Prove2me | solution 1 for GlobalTheory.norm_iteratedFDeriv_sub_le_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:27:19.380009+00:00
-- url     : https://prove2.me/submissions/c1f047dc-4764-43b6-943b-dec50ae0a6e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : V → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) {C : ℝ}
    (hC : ∀ v, ‖iteratedFDeriv ℝ (n + 1) f v‖ ≤ C) (a b : V) :
    ‖iteratedFDeriv ℝ n f a - iteratedFDeriv ℝ n f b‖ ≤ C * ‖a - b‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (f := iteratedFDeriv ℝ n f) (fun x _ => hd x)
    (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hC x) convex_univ (Set.mem_univ b)
    (Set.mem_univ a)
end GlobalTheory
