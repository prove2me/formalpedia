-- Prove2me | solution 1 for GlobalTheory.isoTransvection.apply_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:42.681963+00:00
-- url     : https://prove2.me/submissions/9b0b5072-8ad0-4fda-87e3-f322b2a12d42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap

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
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) (b : R₀) {v : M} (hv : v ∈ L) :
    isoTransvection h x hx (algebraMap R₀ R b) v ∈ L := by
  obtain ⟨c, hc⟩ := hL v hv
  rw [apply, ← hc, ← map_mul, algebraMap_smul]
  exact L.add_mem hv (L.smul_mem _ hxL)
end GlobalTheory.isoTransvection
