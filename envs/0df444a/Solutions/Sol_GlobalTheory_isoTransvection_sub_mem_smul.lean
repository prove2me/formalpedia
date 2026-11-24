-- Prove2me | solution 1 for GlobalTheory.isoTransvection.sub_mem_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:18:58.770806+00:00
-- url     : https://prove2.me/submissions/50d476e1-a886-4a3c-ab40-e92853d22d0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvection_sub_mem_smul_of_mul

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
theorem _root_.solution {L : Submodule R₀ M} (hxL : x ∈ L)
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) {I : Ideal R₀} {b : R₀} (hb : b ∈ I)
    {v : M} (hv : v ∈ L) :
    isoTransvection h x hx (algebraMap R₀ R b) v - v ∈ I • L := by
  obtain ⟨c, hc⟩ := hL v hv
  exact sub_mem_smul_of_mul h x hx hxL ⟨b * c, I.mul_mem_right c hb, by rw [map_mul, hc]⟩
end GlobalTheory.isoTransvection
