-- Prove2me | solution 1 for GlobalTheory.FiniteFibreFlat.flat_of_flatOver_fields
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:06.845671+00:00
-- url     : https://prove2.me/submissions/a8d2564d-f337-4cda-a58e-059fee44fcc6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
import Theorems.Thm_GlobalTheory_FiniteFibreFlat_flat_of_flat_fibres
import Theorems.Thm_GlobalTheory_FiniteFibreFlat_flatOver_of_comp_base
import Theorems.Thm_GlobalTheory_FibreFlat_FlatOver_source
import Theorems.Thm_GlobalTheory_FibreFlat_FlatOver_target


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.FiniteFibreFlat
open TensorProduct IsLocalRing
open FibreFlat
variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y}
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.FiniteFibreFlat
theorem _root_.solution (f : X ⟶ Y) (g : Y ⟶ S) (hY : IsLocallyNoetherian Y)
    (h1 : Flat (f ≫ g)) (h2 : IsFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    refine this (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      (LocallyOfFiniteType.isLocallyNoetherian (pullback.fst g u))
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1) inferInstance
      (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩
    rw [← pullback.condition]
    exact (H k _).target sq
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i))
      (LocallyOfFiniteType.isLocallyNoetherian (Y.affineCover.f i)) inferInstance
      (Y.affineCover.f i ≫ g) (by rw [e]; infer_instance) (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · haveI hX' : IsAffine X := isAffine_of_isAffineHom f
    rw [← MorphismProperty.cancel_left_of_respectsIso @Flat X.isoSpec.inv]
    exact this (X.isoSpec.inv ≫ f) inferInstance (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [IsFinite.SpecMap_iff] at h2
  rw [isLocallyNoetherian_Spec] at hY
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : Module.Finite A B := h2
  refine flat_of_flat_fibres (R := R) (A := A) (B := B) fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this
end GlobalTheory.FiniteFibreFlat
