-- Prove2me | solution 1 for GlobalTheory.isoTransvection.sub_mem_smul_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:47.051521+00:00
-- url     : https://prove2.me/submissions/ffc9a527-72b1-4728-9f19-b09ad475c9f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvection_apply_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.isoTransvection
variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
variable {h}
variable (h)
variable {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Module R₀ M] [IsScalarTower R₀ R M]
namespace GlobalTheory.isoTransvection
theorem _root_.solution {L : Submodule R₀ M} (hxL : x ∈ L) {I : Ideal R₀} {b : R} {v : M}
    (hb : ∃ c ∈ I, algebraMap R₀ R c = b * h v x) :
    isoTransvection h x hx b v - v ∈ I • L := by
  obtain ⟨c, hc, hcb⟩ := hb
  rw [apply_sub, ← hcb, algebraMap_smul]
  exact Submodule.smul_mem_smul hc hxL
end GlobalTheory.isoTransvection
