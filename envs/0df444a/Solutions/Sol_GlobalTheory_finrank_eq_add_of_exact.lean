-- Prove2me | solution 1 for GlobalTheory.finrank_eq_add_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:50:03.593836+00:00
-- url     : https://prove2.me/submissions/b381638c-2b1d-4d2e-833d-e234d1f66582

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Theorems.Thm_GlobalTheory_GradedHilbert_inf_range_eq_map

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
theorem _root_.solution (ℳ' : ℤ → Submodule k M') [Decomposition ℳ']
    (ℳ : ℤ → Submodule k M) [Decomposition ℳ] (f : M' →ₗ[k] M) (g : M →ₗ[k] M'') (d : ℤ)
    (hf : ∀ n, ∀ m ∈ ℳ' n, f m ∈ ℳ (n + d)) (hinj : Function.Injective f)
    (hfg : Function.Exact f g) (n : ℤ) [Module.Finite k (ℳ (n + d))] :
    finrank k (ℳ (n + d)) = finrank k (ℳ' n) + finrank k ((ℳ (n + d)).map g) := by
  have h := finrank_map_add_finrank_inf_ker g (ℳ (n + d))
  have hker : LinearMap.ker g = LinearMap.range f := by
    ext y
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    exact hfg y
  rw [hker, inf_range_eq_map ℳ' ℳ f d hf n,
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hinj (ℳ' n)).symm] at h
  omega
end GlobalTheory
