-- Prove2me | solution 1 for GlobalTheory.FibreFlat.flat_of_flatOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:26.899444+00:00
-- url     : https://prove2.me/submissions/37a8ffa7-59bb-44eb-aef7-56f603f69081

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Theorems.Thm_GlobalTheory_FibreFlat_ringHom_flat
import Theorems.Thm_GlobalTheory_FibreFlat_FlatOver_target
import Theorems.Thm_GlobalTheory_FibreFlat_FlatOver_source
import Theorems.Thm_GlobalTheory_FibreFlat_FlatOver_tensor

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
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.FibreFlat
theorem _root_.solution (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp T)
    (h1 : Flat (f ≫ g)) (h2 : LocallyOfFiniteType (f ≫ g)) (h3 : LocallyOfFiniteType g)
    (hK : FlatOver f g (spMap (algebraMap T K))) (hκ : FlatOver f g (spMap (residue T))) :
    Flat f := by
  wlog hY : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i)) (Y.affineCover.f i ≫ g)
      (by rw [e]; infer_instance) (by rw [e]; infer_instance) inferInstance
      (hK.target sq) (hκ.target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hY
  wlog hX : ∃ B, X = Spec B generalizing X
  · refine IsZariskiLocalAtSource.of_openCover X.affineCover fun i => ?_
    exact this (X.affineCover.f i ≫ f) (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance) (hK.source _) (hκ.source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h2
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h2 h3
  letI : Algebra T A := g.hom.toAlgebra
  letI : Algebra T B := (g ≫ f).hom.toAlgebra
  haveI : Module.Flat T B := h1
  haveI : Algebra.FiniteType T B := h2
  haveI : Algebra.FiniteType T A := h3
  haveI := Algebra.FiniteType.isNoetherianRing T A
  haveI := Algebra.FiniteType.isNoetherianRing T B
  let φ : A →ₐ[T] B := { f.hom with commutes' := fun _ => rfl }
  exact ringHom_flat K φ (FlatOver.tensor φ hK) (FlatOver.tensor φ hκ)
end GlobalTheory.FibreFlat
