-- Prove2me | solution 1 for GlobalTheory.FibreFlat.FlatOver.tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:13.408614+00:00
-- url     : https://prove2.me/submissions/e69a6cfc-a0d4-4ba7-8fc2-b25aabde9f77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TensorProduct IsLocalRing
open GlobalTheory
open GlobalTheory.FibreFlat
variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ S} {s : S' ⟶ S}
namespace GlobalTheory.FibreFlat
namespace FlatOver
theorem _root_.solution {T L A B : Type} [CommRing T] [CommRing L] [CommRing A] [CommRing B]
    [Algebra T L] [Algebra T A] [Algebra T B] (φ : A →ₐ[T] B)
    (H : FlatOver (spMap (φ : A →+* B)) (spMap (algebraMap T A)) (spMap (algebraMap T L))) :
    (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B).Flat := by
  have hA := CommRingCat.isPushout_tensorProduct T L A
  have hB := CommRingCat.isPushout_tensorProduct T L B
  have sq : IsPushout (CommRingCat.ofHom (φ : A →+* B))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[T] L ⊗[T] A).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[T] L ⊗[T] B).toRingHom)
      (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B)) := by
    refine IsPushout.of_left ?_ ?_ hA.flip
    · convert hB.flip using 1
      · ext t; simp
      · ext t; simp
    · ext t; simp
  have := H _ _ _ (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[T] A)))
    (isPullback_SpecMap_of_isPushout _ _ _ _ sq)
    (isPullback_SpecMap_of_isPushout _ _ _ _ hA).w.symm
  exact Flat.SpecMap_iff.mp this
end FlatOver
end GlobalTheory.FibreFlat
