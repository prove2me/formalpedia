-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.LineBundle.pullbackSection_bijective
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:21:57.617577+00:00
-- url     : https://prove2.me/submissions/32612395-10c3-4964-8219-48590d88393b

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

set_option Elab.async false
set_option linter.all false

section
namespace OAI

section

namespace MaximalSeshadri.ModuleLocal
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X : Scheme.{0}} {M N : X.Modules}

lemma app_zero_of_restrict (φ : M ⟶ N) (U W : X.Opens) (hW : W ≤ U)
    (h : (Scheme.Modules.restrictFunctor U.ι).map φ = 0) : φ.app W = 0 := by
  have hz := congrArg (fun q : M.restrict U.ι ⟶ N.restrict U.ι =>
    q.app (U.ι ⁻¹ᵁ W)) h
  have he : U.ι ''ᵁ U.ι ⁻¹ᵁ W = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  change φ.app (U.ι ''ᵁ U.ι ⁻¹ᵁ W) = 0 at hz
  suffices hh : ∀ A : X.Opens, A = W → φ.app A = 0 → φ.app W = 0 from hh _ he hz
  intro A hA hφ
  subst A
  exact hφ

lemma eq_zero_of_local (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (Scheme.Modules.restrictFunctor U.ι).map φ = 0) : φ = 0 := by
  ext W m
  change φ.app W m = 0
  let F : (X : TopCat).Sheaf AddCommGrpCat := (SheafOfModules.toSheaf X.ringCatSheaf).obj N
  apply TopCat.Presheaf.section_ext F W (φ.app W m) 0
  intro x hx
  obtain ⟨U,hxU,hU⟩ := h x
  let V : X.Opens := W ⊓ U
  have hv : φ.app V = 0 := app_zero_of_restrict φ U V inf_le_right hU
  change N.presheaf.germ W x hx (φ.app W m) = N.presheaf.germ W x hx 0
  rw [← TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE (show V ≤ W from inf_le_left))
    x (show x ∈ V from ⟨hx,hxU⟩)]
  have hn := CategoryTheory.congr_fun (φ.mapPresheaf.naturality
    (homOfLE (show V ≤ W from inf_le_left)).op) m
  change φ.app V (M.presheaf.map (homOfLE inf_le_left).op m) =
    N.presheaf.map (homOfLE inf_le_left).op (φ.app W m) at hn
  rw [← hn,hv]
  simp

lemma epi_of_local (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Epi ((Scheme.Modules.restrictFunctor U.ι).map φ)) : Epi φ := by
  apply (Preadditive.epi_iff_cancel_zero _).mpr
  intro P g hg
  apply eq_zero_of_local
  intro x
  obtain ⟨U,hx,hU⟩ := h x
  let := hU
  refine ⟨U,hx,?_⟩
  apply (cancel_epi ((Scheme.Modules.restrictFunctor U.ι).map φ)).mp
  rw [← Functor.map_comp,hg,Functor.map_zero,comp_zero]

lemma mono_of_local (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((Scheme.Modules.restrictFunctor U.ι).map φ)) : Mono φ := by
  apply (Preadditive.mono_iff_cancel_zero _).mpr
  intro P g hg
  apply eq_zero_of_local
  intro x
  obtain ⟨U,hx,hU⟩ := h x
  let := hU
  refine ⟨U,hx,?_⟩
  apply (cancel_mono ((Scheme.Modules.restrictFunctor U.ι).map φ)).mp
  rw [← Functor.map_comp,hg,Functor.map_zero,zero_comp]

lemma isIso_of_local (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) : IsIso φ := by
  have : Epi φ := epi_of_local φ (fun x => by
    obtain ⟨U,hx,hU⟩ := h x
    let := hU
    exact ⟨U,hx,inferInstance⟩)
  have : Mono φ := mono_of_local φ (fun x => by
    obtain ⟨U,hx,hU⟩ := h x
    let := hU
    exact ⟨U,hx,inferInstance⟩)
  exact isIso_of_mono_of_epi φ

end
end MaximalSeshadri.ModuleLocal

end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y Z : Scheme.{0}}

def pullbackFrame (f : Y ⟶ X) {M : X.Modules} (e : M ≅ O X) :
    (Scheme.Modules.pullback f).obj M ≅ O Y :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f

lemma pullbackUnit_adjunction (f : Y ⟶ X) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  change (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) = _
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma unit_compatibility (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (iso f U ((Scheme.Modules.pullback f).obj M)).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M) := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction f
  let b := Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι
  let c := Scheme.Modules.restrictAdjunction U.ι
  let d := Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)
  have h := unit_conjugateEquiv_symm (a.comp b) (c.comp d) (rightSquare f U).hom M
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  change (a.unit.app M ≫ (Scheme.Modules.pushforward f).map
    (b.unit.app ((Scheme.Modules.pullback f).obj M))) ≫
      (rightSquare f U).hom.app _ =
    (c.unit.app M ≫ (Scheme.Modules.pushforward U.ι).map
      (d.unit.app (M.restrict U.ι))) ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M)) at h
  have hc := congrArg (fun q => (Scheme.Modules.restrictFunctor U.ι).map q ≫
    c.counit.app ((Scheme.Modules.pushforward (f ∣_ U)).obj
      (((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι))) h
  simp only [Functor.map_comp, Category.assoc] at hc
  change _ = _ at hc
  have hn := c.counit.naturality
    (d.unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [Functor.map_comp, Functor.map_comp] at hn
  rw [Category.assoc] at hn
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [hn] at hc
  simp only [← Category.assoc] at hc
  have ht := c.left_triangle_components M
  change (Scheme.Modules.restrictFunctor U.ι).map (c.unit.app M) ≫
    c.counit.app (M.restrict U.ι) = 𝟙 _ at ht
  rw [ht, Category.id_comp] at hc
  simpa only [a, b, c, d, iso, asIso_hom, hom, Category.assoc] using hc

end
end MaximalSeshadri.OpenBaseChange

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.LineClosedUnit
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def frame (L : LineBundle Y) (U : Y.Opens) (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj L.sheaf)).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (O (f ⁻¹ᵁ U).toScheme) :=
  OpenBaseChange.iso f U _ ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso
      ((OpenBaseChange.leftSquare f U).app L.sheaf).symm ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso (pullbackFrame (f ∣_ U) e)

lemma framed_map (L : LineBundle Y) (U : Y.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
      (frame f L U e).hom = IdealModule.structureMap (f ∣_ U) := by
  dsimp only [map, IdealModule.structureMap]
  have hu := OpenBaseChange.unit_compatibility f U L.sheaf
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit_naturality e.hom
  have hb := pullbackUnit_adjunction (f ∣_ U)
  rw [Adjunction.homEquiv_unit] at hb
  dsimp only [frame, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [← Category.assoc]
  rw [Category.assoc e.inv, hu]
  simp only [Category.assoc]
  have hec : (OpenBaseChange.leftSquare f U).hom.app L.sheaf ≫
      ((OpenBaseChange.leftSquare f U).app L.sheaf).inv = 𝟙 _ :=
    ((OpenBaseChange.leftSquare f U).app L.sheaf).hom_inv_id
  rw [← Functor.map_comp_assoc, hec]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  change e.inv ≫ (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app _ ≫
    (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.pullback (f ∣_ U)).map e.hom ≫ (pullbackUnitIso (f ∣_ U)).hom) = _
  rw [Functor.map_comp]
  have hn' := congrArg (fun t => e.inv ≫ t ≫
    (Scheme.Modules.pushforward (f ∣_ U)).map (pullbackUnitIso (f ∣_ U)).hom) hn
  simp only [Category.assoc, hb] at hn'
  exact hn'.trans (e.inv_hom_id_assoc _)

end
end MaximalSeshadri.LineClosedUnit

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma LineBundle.pullback_unit_isIso [IsIso (IdealModule.structureMap f)]
    (L : LineBundle Y) : IsIso (LineClosedUnit.map f L) := by
  let OY : LineBundle Y := ⟨O Y,fun _ => ⟨⊤,trivial,⟨Scheme.Modules.restrictUnitIso _⟩⟩⟩
  have hu := pullbackUnit_adjunction f
  rw [Adjunction.homEquiv_unit] at hu
  have : IsIso (LineClosedUnit.map f OY ≫
      (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom) := by
    change IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫
      (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom)
    rw [hu]
    exact inferInstanceAs (IsIso (IdealModule.structureMap f))
  have unitIsIso : IsIso (C := Y.Modules) (LineClosedUnit.map f OY) :=
    (isIso_comp_right_iff _ _).mp ‹IsIso (_ ≫ _)›
  have hU (U : Y.Opens) : IsIso (IdealModule.structureMap (f ∣_ U)) := by
    rw [← LineClosedUnit.framed_map f OY U (Scheme.Modules.restrictUnitIso U.ι)]
    exact ((Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
      (Scheme.Modules.restrictFunctor U.ι).mapIso
        (@asIso Y.Modules _ _ _ (LineClosedUnit.map f OY) unitIsIso) ≪≫
      LineClosedUnit.frame f OY U (Scheme.Modules.restrictUnitIso U.ι)).isIso_hom
  apply ModuleLocal.isIso_of_local
  intro y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne y
  refine ⟨U,hy,?_⟩
  have : IsIso (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (LineClosedUnit.map f L) ≫
      (LineClosedUnit.frame f L U e).hom) := by
    exact (LineClosedUnit.framed_map f L U e).symm ▸ hU U
  have : IsIso (C := U.toScheme.Modules) e.inv := e.isIso_inv
  have : IsIso (C := U.toScheme.Modules) (LineClosedUnit.frame f L U e).hom :=
    (LineClosedUnit.frame f L U e).isIso_hom
  have hi := (isIso_comp_left_iff (C := U.toScheme.Modules) e.inv _).mp ‹IsIso (e.inv ≫ _)›
  exact (isIso_comp_right_iff (C := U.toScheme.Modules) _ _).mp hi

lemma pullbackSection_adjunction {M : Y.Modules} (s : O Y ⟶ M) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((pullbackUnitIso f).hom ≫ pullbackSection f s) =
    s ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M := by
  simp only [pullbackSection,Iso.hom_inv_id_assoc]
  rw [Adjunction.homEquiv_unit]
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality s

lemma LineBundle.pullbackSection_bijective [IsIso (IdealModule.structureMap f)]
    (L : LineBundle Y) : Function.Bijective (pullbackSection f (M := L.sheaf)) := by
  let := L.pullback_unit_isIso f
  let η := LineClosedUnit.map f L
  have hi : Function.Injective (fun t : O X ⟶ (Scheme.Modules.pullback f).obj L.sheaf =>
      (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        ((pullbackUnitIso f).hom ≫ t)) :=
    (Equiv.injective _).comp (fun a b h => (cancel_epi (pullbackUnitIso f).hom).mp h)
  constructor
  · intro a b h
    have hh := congrArg (fun t => (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((pullbackUnitIso f).hom ≫ t)) h
    rw [pullbackSection_adjunction,pullbackSection_adjunction] at hh
    exact (cancel_mono η).mp hh
  · intro t
    let a := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((pullbackUnitIso f).hom ≫ t)
    refine ⟨a ≫ inv η,hi ?_⟩
    dsimp only
    rw [pullbackSection_adjunction]
    change (a ≫ inv η) ≫ η = a
    simp

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.LineBundle.pullbackSection_bijective := @OAI.MaximalSeshadri.Geometry.LineBundle.pullbackSection_bijective
