-- Prove2me | solution 1 for GroundTheory.Global.coordinateRing_ringHom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:46.226363+00:00
-- url     : https://prove2.me/submissions/dd1856d6-7295-41c8-ae33-2ed44935ce8d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionLift
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Global
noncomputable section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (W : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
namespace GroundTheory.Global
theorem _root_.solution {S : Type*} [CommRing S]
    {f g : W.toAffine.CoordinateRing →+* S}
    (h₁ : ∀ c : 𝒪, f (algebraMap 𝒪 _ c) = g (algebraMap 𝒪 _ c))
    (h₂ : f (CoordinateRing.mk W (C X)) = g (CoordinateRing.mk W (C X)))
    (h₃ : f (CoordinateRing.mk W Y) = g (CoordinateRing.mk W Y)) : f = g := by
  have hc : ∀ c : 𝒪, algebraMap 𝒪 W.toAffine.CoordinateRing c =
      AdjoinRoot.of W.toAffine.polynomial (C c) := fun c => by
    rw [IsScalarTower.algebraMap_apply 𝒪 𝒪[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      simpa only [RingHom.comp_apply, hc] using h₁ c
    · simpa only [RingHom.comp_apply, AdjoinRoot.mk_C] using h₂
  · simpa only [AdjoinRoot.mk_X] using h₃
end GroundTheory.Global
