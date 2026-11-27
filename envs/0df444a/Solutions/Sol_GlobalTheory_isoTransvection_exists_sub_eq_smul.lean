-- Prove2me | solution 1 for GlobalTheory.isoTransvection.exists_sub_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:41:41.774193+00:00
-- url     : https://prove2.me/submissions/5d3d71aa-38ad-4168-bc07-5f0bcaa76501

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
theorem _root_.solution {L : Submodule R₀ M} (hxL : x ∈ L)
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) (q b : R₀) {v : M} (hv : v ∈ L) :
    ∃ w ∈ L, isoTransvection h x hx (algebraMap R₀ R (q * b)) v - v = q • w := by
  obtain ⟨c, hc⟩ := hL v hv
  refine ⟨(b * c) • x, L.smul_mem _ hxL, ?_⟩
  rw [apply_sub, ← hc, ← map_mul, algebraMap_smul, smul_smul, mul_assoc]
end GlobalTheory.isoTransvection
