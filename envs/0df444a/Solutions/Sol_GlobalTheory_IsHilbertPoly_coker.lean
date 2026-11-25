-- Prove2me | solution 1 for GlobalTheory.IsHilbertPoly.coker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:58:03.64481+00:00
-- url     : https://prove2.me/submissions/c346ee81-c382-41e3-b89a-8667a845d2cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Theorems.Thm_GlobalTheory_finrank_eq_add_of_exact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter
open GlobalTheory
open DirectSum Module GradedHilbert
variable {k : Type*} [Field k] {M' M M'' : Type*} [AddCommGroup M'] [Module k M']
  [AddCommGroup M] [Module k M] [AddCommGroup M''] [Module k M'']
namespace GlobalTheory
namespace IsHilbertPoly
theorem _root_.solution {ℳ' : ℤ → Submodule k M'} [Decomposition ℳ']
    {ℳ : ℤ → Submodule k M} [Decomposition ℳ] {P' P : ℚ[X]} (hP' : IsHilbertPoly ℳ' P')
    (hP : IsHilbertPoly ℳ P) (f : M' →ₗ[k] M) (g : M →ₗ[k] M'') (d : ℤ)
    (hf : ∀ n, ∀ m ∈ ℳ' n, f m ∈ ℳ (n + d)) (hinj : Function.Injective f)
    (hfg : Function.Exact f g) :
    IsHilbertPoly (fun n => (ℳ n).map g) (P - P'.comp (X - C (d : ℚ))) where
  finite n := by
    have := hP.finite n
    infer_instance
  eventually_eq := by
    filter_upwards [hP.eventually_eq,
      (Filter.tendsto_atTop_add_const_right atTop (-d) Filter.tendsto_id).eventually
        hP'.eventually_eq] with n h1 h2
    simp only [id_eq] at h2
    have := hP.finite
    have h := finrank_eq_add_of_exact ℳ' ℳ f g d hf hinj hfg (n + -d)
    rw [neg_add_cancel_right] at h
    rw [eval_sub, eval_comp, ← h1, h]
    simp only [eval_sub, eval_X, eval_C]
    rw [show (n : ℚ) - d = ((n + -d : ℤ) : ℚ) by push_cast; ring, ← h2]
    push_cast
    ring
end IsHilbertPoly
end GlobalTheory
