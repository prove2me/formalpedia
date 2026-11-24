-- Prove2me | solution 1 for GlobalTheory.SchwartzFstOp.norm_iteratedFDeriv_sliceCLM_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:35:52.355507+00:00
-- url     : https://prove2.me/submissions/efe671ae-867c-4d81-9020-960f44cfcb3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSliceSeminormLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
open GlobalTheory GlobalTheory.SchwartzFstOp
namespace GlobalTheory.SchwartzFstOp
theorem _root_.solution {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖ ≤ ‖iteratedFDeriv ℝ n f (x, x')‖ := by
  have e : (⇑(sliceCLM x' f) : V → ℂ) =
      (fun q => f (q + ((0 : V), x'))) ∘ (ContinuousLinearMap.inl ℝ V V') := by
    funext y; simp
  have hc : ContDiff ℝ n (fun q : V × V' => f (q + ((0 : V), x'))) :=
    ((f.smooth ⊤).comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc _ le_rfl, iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin n, ‖ContinuousLinearMap.inl ℝ V V'‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inl_le_one ℝ V V')
  have h2 : (ContinuousLinearMap.inl ℝ V V') x + ((0 : V), x') = (x, x') := by simp
  rw [h2]
  exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans (le_of_eq (mul_one _))
end GlobalTheory.SchwartzFstOp
