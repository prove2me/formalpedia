-- Prove2me | solution 1 for GlobalTheory.integral_of_finite_base_change_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:01:23.297974+00:00
-- url     : https://prove2.me/submissions/0e3582d9-5c47-4f8e-975a-b67ae58289c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntegralOfFiniteBaseChangeImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C] (φ : U ⊗[T] C →+* L ⊗[F] K), (∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) → ∀ (ω : L ⊗[F] K) (p : Polynomial (U ⊗[T] C)), p.Monic → p.eval₂ φ ω = 0 → IsIntegral U ω := by
  intro T U C F K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ ω p hp h
  letI : Algebra (U ⊗[T] C) (L ⊗[F] K) := φ.toAlgebra
  have hmap : algebraMap (U ⊗[T] C) (L ⊗[F] K) = φ := rfl
  haveI : IsScalarTower U (U ⊗[T] C) (L ⊗[F] K) := by
    refine IsScalarTower.of_algebraMap_eq fun u => ?_
    rw [hmap]
    change algebraMap U (L ⊗[F] K) u = φ (u ⊗ₜ 1)
    rw [hφ, map_one]
    rfl
  have hint : IsIntegral (U ⊗[T] C) ω := ⟨p, hp, h⟩
  haveI : Algebra.IsIntegral U (U ⊗[T] C) := inferInstance
  exact isIntegral_trans ω hint
end GlobalTheory
