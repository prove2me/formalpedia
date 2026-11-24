-- Prove2me | solution 1 for GlobalTheory.GradedHilbert.inf_range_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:36:34.405318+00:00
-- url     : https://prove2.me/submissions/a221e9fb-8ba2-47a1-b47b-cefbf9009478

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule

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
open GlobalTheory.GradedHilbert
open DirectSum
variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
namespace GlobalTheory.GradedHilbert
theorem _root_.solution (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (𝒩 : ℤ → Submodule R N)
    [Decomposition 𝒩] (f : M →ₗ[R] N) (d : ℤ) (hf : ∀ n, ∀ m ∈ ℳ n, f m ∈ 𝒩 (n + d))
    (n : ℤ) : 𝒩 (n + d) ⊓ LinearMap.range f = (ℳ n).map f := by
  ext y
  simp only [Submodule.mem_inf, LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨hy, x, rfl⟩
    refine ⟨proj ℳ n x, proj_mem ℳ n x, ?_⟩
    rw [← proj_map ℳ 𝒩 f d hf n x, proj_of_mem 𝒩 hy]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hf n x hx, x, rfl⟩
end GlobalTheory.GradedHilbert
