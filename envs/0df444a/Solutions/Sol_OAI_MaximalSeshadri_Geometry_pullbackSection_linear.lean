-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.pullbackSection_linear
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:22:05.01865+00:00
-- url     : https://prove2.me/submissions/e875e4a6-9cf3-4c9d-b30e-f1dc53853608

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

set_option Elab.async false
set_option linter.all false

section
namespace OAI

section
noncomputable section

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

lemma openScalars_restrict (g : X ⟶ Spec (CommRingCat.of K)) {U V : X.Opens}
    (e : U ≤ V) :
    (X.presheaf.map (homOfLE e).op).hom.comp (openScalars g V) = openScalars g U := by
  exact congrArg (fun morphism : Γ(Spec (CommRingCat.of K), ⊤) ⟶ Γ(X, U) =>
    morphism.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    (Scheme.Hom.appLE_map g (show V ≤ g ⁻¹ᵁ ⊤ from by simp) (homOfLE e).op)

end
end MaximalSeshadri.ProjectiveBertini

end
end

end OAI
end

section
namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y Z : Scheme.{u}}

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

lemma endValue_injective : Function.Injective (endValue (X := X)) := by
  intro f g h
  ext U a
  change Γ(X, U) at a
  change f.app U a = g.app U a
  rw [end_apply f U a, end_apply g U a]
  rw [end_naturality f U, end_naturality g U, h]

end
end MaximalSeshadri.Frames

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma coefficient_injective {M : X.Modules} (e : M ≅ O X) :
    Function.Injective (coefficient e) := by
  intro s t h
  apply (cancel_mono e.hom).1
  exact endValue_injective h

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

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
noncomputable section

section

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}}

lemma coefficient_add {M : X.Modules} (e : M ≅ O X) (s t : O X ⟶ M) :
    coefficient e (s + t) = coefficient e s + coefficient e t := by
  simp [coefficient, endValue, Preadditive.add_comp]
  rfl

lemma restrictSection_add (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (s t : O X ⟶ M) : restrictSection φ (s + t) = restrictSection φ s + restrictSection φ t := by
  ext U a
  rfl

lemma coefficient_restrict_scalar_comp (φ : Y ⟶ X) [IsOpenImmersion φ]
    {M : X.Modules} (e : M.restrict φ ≅ O Y) (a : Γ(X, ⊤)) (s : O X ⟶ M) :
    coefficient e (restrictSection φ (scalarEnd a ≫ s)) =
      φ.appTop a * coefficient e (restrictSection φ s) := by
  have h : restrictSection φ (scalarEnd a ≫ s) =
      (restrictSection φ (scalarEnd a) ≫ (Scheme.Modules.restrictUnitIso φ).hom) ≫
        restrictSection φ s := by
    let restriction : X.Modules ⥤ Y.Modules := Scheme.Modules.restrictFunctor φ
    let unitIso : restriction.obj (O X) ≅ O Y := Scheme.Modules.restrictUnitIso φ
    change unitIso.inv ≫ restriction.map (scalarEnd a ≫ s) =
      (unitIso.inv ≫ restriction.map (scalarEnd a) ≫ unitIso.hom) ≫
        unitIso.inv ≫ restriction.map s
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [h]
  calc
    _ = endValue ((restrictSection φ (scalarEnd a) ≫
        (Scheme.Modules.restrictUnitIso φ).hom) ≫ (restrictSection φ s ≫ e.hom)) :=
      congrArg endValue (Category.assoc _ _ _)
    _ = endValue (restrictSection φ (scalarEnd a) ≫
        (Scheme.Modules.restrictUnitIso φ).hom) * coefficient e (restrictSection φ s) :=
      endValue_comp _ _
    _ = _ := by rw [endValue_restrict, endValue_scalarEnd]

end
end MaximalSeshadri.Frames
end

end
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

lemma pullback_endValue (f : Y ⟶ X) (a : O X ⟶ O X) :
    endValue ((pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (pullbackUnitIso f).hom) = f.appTop (endValue a) := by
  let u := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let b := (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (pullbackUnitIso f).hom
  have he : a ≫ u = u ≫ (Scheme.Modules.pushforward f).map b := by
    have hn := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left
      a (pullbackUnitIso f).hom
    have hr := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right
      (pullbackUnitIso f).hom b
    rw [pullbackUnit_adjunction] at hn hr
    have hcomp : (pullbackUnitIso f).hom ≫ b =
        (Scheme.Modules.pullback f).map a ≫ (pullbackUnitIso f).hom := by simp [b]
    rw [hcomp] at hr
    exact hn.symm.trans hr
  have hev := congrArg (fun t : O X ⟶ (Scheme.Modules.pushforward f).obj (O Y) =>
      t.app ⊤ (1 : Γ(X,⊤))) he
  change f.app ⊤ (a.app ⊤ (1 : Γ(X,⊤))) = b.app (f ⁻¹ᵁ ⊤) (f.app ⊤ 1) at hev
  have hfOne : f.app ⊤ (1 : Γ(X,⊤)) = (1 : Γ(Y,f ⁻¹ᵁ ⊤)) := map_one (f.app ⊤).hom
  rw [hfOne] at hev
  exact hev.symm

lemma coefficient_pullback (f : Y ⟶ X) {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M) :
    coefficient (pullbackFrame f e) (pullbackSection f s) =
      f.appTop (coefficient e s) := by
  unfold coefficient pullbackFrame pullbackSection
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc]
  exact pullback_endValue f (s ≫ e.hom)

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

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

def affineMapAlgHom {X Y : Scheme} (f : X ⟶ complexBase) (g : Y ⟶ complexBase)
    (h : X ⟶ Y) (hh : h ≫ g = f) (U : Y.affineOpens) (V : X.affineOpens)
    (hVU : V.1 ≤ h ⁻¹ᵁ U.1) :
    letI := (openScalars f V.1).toAlgebra
    letI := (openScalars g U.1).toAlgebra
    Γ(Y,U.1) →ₐ[ℂ] Γ(X,V.1) := by
  letI := (openScalars f V.1).toAlgebra
  letI := (openScalars g U.1).toAlgebra
  have he : CommRingCat.ofHom (openScalars g U.1) ≫ h.appLE U.1 V.1 hVU =
      CommRingCat.ofHom (openScalars f V.1) := by
    apply Spec.map_injective
    rw [Spec.map_comp,spec_openScalars,spec_openScalars,
      ← Category.assoc,IsAffineOpen.SpecMap_appLE_fromSpec h U.2 V.2 hVU,
      Category.assoc,hh]
  exact { (h.appLE U.1 V.1 hVU).hom with
    commutes' := fun c => CategoryTheory.congr_fun he c }

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped AlgebraicGeometry
variable {X : Scheme}

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {X : Scheme}

lemma trivialModule_restriction_injective [IsIntegral X] (M : X.Modules)
    (e : M ≅ structureSheaf X) {U V : X.Opens} (i : U ⟶ V) [Nonempty U] :
    Function.Injective (M.presheaf.map i.op) := by
  intro s t h
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf X).mapIso e).app (Opposite.op V)).hom).injective
  have hn := e.hom.mapPresheaf.naturality i.op
  have heq := congrArg (fun a => e.hom.app U a) h
  have hh (a : Γ(M, V)) :
      e.hom.app U (M.presheaf.map i.op a) =
        X.presheaf.map i.op (e.hom.app V a) := by
    exact CategoryTheory.congr_fun hn a
  rw [hh, hh] at heq
  exact map_injective_of_isIntegral X i heq

theorem LineBundle.restriction_injective [IsIntegral X] (L : LineBundle X)
    {U V : X.Opens} (i : U ⟶ V) [Nonempty U] :
    Function.Injective (L.sheaf.presheaf.map i.op) := by
  intro s t h
  apply L.sheaf.isSheaf.section_ext
  intro x hx
  obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
  let f := T.ι
  let U' : T.toScheme.Opens := f ⁻¹ᵁ U
  let V' : T.toScheme.Opens := f ⁻¹ᵁ V
  have hU' : Nonempty U' := by
    obtain ⟨y, hyT, hyU⟩ := nonempty_preirreducible_inter T.isOpen U.isOpen
      ⟨x, hxT⟩ (by obtain ⟨u⟩ := ‹Nonempty U›; exact ⟨u.val, u.property⟩)
    exact ⟨⟨⟨y, hyT⟩, hyU⟩⟩
  have : Nonempty U' := hU'
  have : Nonempty T := ⟨⟨x, hxT⟩⟩
  let j : U' ⟶ V' := homOfLE (fun _ h => leOfHom i h)
  let W := f ''ᵁ V'
  have hWV : W ≤ V := f.image_preimage_le V
  refine ⟨W, hWV, ?_, ?_⟩
  · exact ⟨⟨x, hxT⟩, hx, rfl⟩
  · apply trivialModule_restriction_injective (L.sheaf.restrict f) e j
    change L.sheaf.presheaf.map ((f.opensFunctor.map j).op)
        (L.sheaf.presheaf.map (homOfLE hWV).op s) =
      L.sheaf.presheaf.map ((f.opensFunctor.map j).op)
        (L.sheaf.presheaf.map (homOfLE hWV).op t)
    have hh := congrArg
      (fun a => L.sheaf.presheaf.map (homOfLE (f.image_preimage_le U)).op a) h
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hh ⊢
    have eq : i.op ≫ (homOfLE (f.image_preimage_le U)).op =
        (homOfLE hWV).op ≫ (f.opensFunctor.map j).op := Subsingleton.elim _ _
    rw [eq] at hh
    exact hh

theorem LineBundle.section_restriction_injective [IsIntegral X] (L : LineBundle X)
    (U : X.Opens) [Nonempty U] :
    Function.Injective (fun s : GlobalSections X L.sheaf => s.app U (1 : Γ(X, U))) := by
  intro s t h
  have natural (s : GlobalSections X L.sheaf) (V : X.Opens) :
      s.app V (1 : Γ(X, V)) = L.sheaf.presheaf.map
        (homOfLE (show V ≤ ⊤ from le_top)).op (s.app ⊤ (1 : Γ(X, ⊤))) := by
    have hs := CategoryTheory.congr_fun (s.mapPresheaf.naturality
      (homOfLE (show V ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
    change s.app V (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op 1) =
      L.sheaf.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (s.app ⊤ (1 : Γ(X, ⊤))) at hs
    simpa only [map_one, ConcreteCategory.comp_apply] using hs
  have ht : s.app ⊤ (1 : Γ(X, ⊤)) = t.app ⊤ (1 : Γ(X, ⊤)) := by
    apply L.restriction_injective (homOfLE (show U ≤ ⊤ from le_top))
    rw [← natural s U, ← natural t U]
    exact h
  ext V a
  change Γ(X, V) at a
  have hv : s.app V (1 : Γ(X, V)) = t.app V (1 : Γ(X, V)) := by
    rw [natural s, natural t, ht]
  have scalar (s : GlobalSections X L.sheaf) :
      s.app V a = a • s.app V (1 : Γ(X, V)) := by
    have hs := s.app_smul (r := a) (x := (1 : Γ(X, V)))
    change s.app V (a * 1 : Γ(X, V)) = _ at hs
    simpa only [mul_one] using hs
  rw [scalar s, scalar t, hv]

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

end
end
end

end OAI
end

section
namespace OAI

noncomputable section

namespace MaximalSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

lemma endValue_conjugation (b : O Y ≅ O Y) (a : O Y ⟶ O Y) :
    endValue (b.hom ≫ a ≫ b.inv) = endValue a := by
  rw [endValue_comp, endValue_comp]
  have hb : endValue b.hom * endValue b.inv = 1 := by
    rw [← endValue_comp, b.hom_inv_id, endValue_id]
  calc
    endValue b.hom * (endValue a * endValue b.inv) =
      endValue a * (endValue b.hom * endValue b.inv) := by ring
    _ = endValue a := by rw [hb, mul_one]

def pullbackRestrictNatIso (f : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
    (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
  Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
  Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
  (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm ≪≫
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
    (Scheme.Modules.pullback (f ∣_ U))

end MaximalSeshadri.Geometry

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

variable {X Y : Scheme.{0}}

lemma exists_frame_natIso_all (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) :
    ∃ eF : F.obj M ≅ O Y, ∀ s : O X ⟶ M,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  intro s
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b _

theorem exists_restricted_pullback_frame_all (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme, ∀ s : O X ⟶ M,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) := by
  let F := Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let G := Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)
  let uF : F.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
  let uG : G.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.pullback (f ∣_ U)).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso (f ∣_ U)
  obtain ⟨eF,he⟩ := exists_frame_natIso_all F G (pullbackRestrictNatIso f U) uF uG
    (pullbackFrame (f ∣_ U) e)
  refine ⟨eF, ?_⟩
  intro s
  have he' : coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
      coefficient (pullbackFrame (f ∣_ U) e)
        (pullbackSection (f ∣_ U) (restrictSection U.ι s)) := by
    have restrict_pullback : restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s) =
        uF.inv ≫ F.map s := by
      exact (congrArg (fun sectionMap =>
        (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι).inv ≫ sectionMap)
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map_comp
          (pullbackUnitIso f).inv ((Scheme.Modules.pullback f).map s))).trans
        (Category.assoc _ _ _).symm
    have pullback_restrict : pullbackSection (f ∣_ U) (restrictSection U.ι s) =
        uG.inv ≫ G.map s := by
      exact (congrArg (fun sectionMap => (pullbackUnitIso (f ∣_ U)).inv ≫ sectionMap)
        ((Scheme.Modules.pullback (f ∣_ U)).map_comp
          (Scheme.Modules.restrictUnitIso U.ι).inv
          ((Scheme.Modules.restrictFunctor U.ι).map s))).trans
        (Category.assoc _ _ _).symm
    exact (congrArg (coefficient eF) restrict_pullback).trans
      ((he s).trans (congrArg (coefficient (pullbackFrame (f ∣_ U) e))
        pullback_restrict).symm)
  rw [he', coefficient_pullback]

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X Y : Scheme.{0}}

end
end MaximalSeshadri.Projective
end

end
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames
variable {X Y : Scheme}

lemma LineBundle.restrict_sections_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y] :
    Function.Injective (fun s : GlobalSections X L.sheaf =>
      (Scheme.Modules.restrictFunctor f).map s) := by
  intro s t h
  let U : X.Opens := f ''ᵁ ⊤
  have : Nonempty U := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    exact ⟨⟨f y, y, Set.mem_univ y, rfl⟩⟩
  apply L.section_restriction_injective U
  have he := congrArg (fun s : (structureSheaf X).restrict f ⟶ L.sheaf.restrict f =>
    s.app ⊤ (1 : Γ(X, U))) h
  exact he

lemma LineBundle.restricted_coefficient_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    Function.Injective (fun s : GlobalSections X L.sheaf => coefficient e (restrictSection f s)) := by
  intro s t h
  apply L.restrict_sections_injective f
  let u : (structureSheaf X).restrict f ≅ structureSheaf Y :=
    Scheme.Modules.restrictUnitIso f
  apply (cancel_epi u.inv).mp
  exact coefficient_injective e h

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

end
end MaximalSeshadri.Projective
end

section

end

end
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
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X Y : Scheme.{0}}

lemma baseScalars_comp_actual (f : Y ⟶ X) (g : X ⟶ Spec (CommRingCat.of ℂ)) :
    baseScalars (f ≫ g) = f.appTop.hom.comp (baseScalars g) := by
  ext c
  simp only [baseScalars, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

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
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Projective MaximalSeshadri.Frames
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

variable {X Y : Scheme.{0}}

lemma topIso_baseScalars (p : X ⟶ Spec (CommRingCat.of ℂ)) (U : X.Opens) :
    U.topIso.hom.hom.comp (baseScalars (U.ι ≫ p)) = openScalars p U := by
  ext c
  rw [baseScalars_comp_actual]
  change (U.ι.appTop ≫ U.topIso.hom) (baseScalars p c) = _
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  have H := openScalars_restrict p (show U ≤ ⊤ from le_top)
  have hb : openScalars p ⊤ = baseScalars p := by
    unfold openScalars baseScalars
    change ((p.appTop ≫ X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))))).hom.comp _ = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hb] at H
  exact (congrArg (fun restriction : Γ(X,⊤) ⟶ Γ(X,U) => restriction (baseScalars p c))
    (X.presheaf.map_comp (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op
      (eqToHom U.ι_image_top.symm).op)).symm.trans
    (congrArg (fun scalars : ℂ →+* Γ(X,U) => scalars c) H)

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

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X : Scheme.{0}}

lemma frameOnSmaller_coefficient {M : X.Modules} (U V : X.Opens) (h : V ≤ U)
    (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    coefficient (frameOnSmaller e V h) (restrictSection V.ι s) =
      (X.homOfLE h).appTop (coefficient e (restrictSection U.ι s)) := by
  unfold frameOnSmaller
  rw [coefficient_transport]
  change coefficient ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
    restrictFrame (X.homOfLE h) e) (restrictSection V.ι s ≫
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).hom.app M) = _
  rw [restrictSection_congr,coefficient_restrict_comp]

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma pullback_affine_coefficient (f : Y ⟶ X) (V : X.affineOpens)
    {M : X.Modules} (e : M.restrict V.1.ι ≅ O V.1.toScheme) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ V.1).ι ≅
      O (f ⁻¹ᵁ V.1).toScheme,
      ∀ (W : Y.affineOpens) (h : W.1 ≤ f ⁻¹ᵁ V.1) (s : O X ⟶ M),
        affineCoefficient W (frameOnSmaller eF W.1 h) (pullbackSection f s) =
          f.appLE V.1 W.1 h (affineCoefficient V e s) := by
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame_all f V.1 e
  refine ⟨eF,fun W h s => ?_⟩
  unfold affineCoefficient
  rw [frameOnSmaller_coefficient,he s]
  have hmap : (f.resLE V.1 W.1 h).appTop ≫ W.1.topIso.hom =
      V.1.topIso.hom ≫ f.appLE V.1 W.1 h :=
    (arrowResLEAppIso f V.1 W.1 h).hom.w.symm
  exact congrArg (fun restriction : Γ(V.1.toScheme, ⊤) ⟶ Γ(Y, W.1) =>
    restriction (coefficient e (restrictSection V.1.ι s))) hmap

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.ActualInterpolation MaximalSeshadri.LocalComparison

variable {X : Scheme.{0}}

lemma global_smul_eq_scalarEnd {M : X.Modules} (r : Γ(X,⊤)) (s : O X ⟶ M) :
    r • s = scalarEnd r ≫ s := by
  ext U a
  change Γ(X,U) at a
  change (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) • s.app U a =
    s.app U ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) * a)
  exact (s.app_smul _ _).symm

def affineCoefficientLinear (g : X ⟶ Spec (CommRingCat.of ℂ))
    {M : X.Modules} (U : X.affineOpens) (e : M.restrict U.1.ι ≅ O U.1.toScheme) :
    letI := complexSectionModule g M
    letI : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra
    GlobalSections X M →ₗ[ℂ] Γ(X,U.1) := by
  letI := complexSectionModule g M
  letI : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra
  refine { toFun := affineCoefficient U e
           map_add' := ?_
           map_smul' := ?_ }
  · intro s t
    exact (congrArg (fun sectionValue => U.1.topIso.hom (coefficient e sectionValue))
      (restrictSection_add U.1.ι s t)).trans
      ((congrArg U.1.topIso.hom
        (coefficient_add e (restrictSection U.1.ι s) (restrictSection U.1.ι t))).trans
        (map_add U.1.topIso.hom.hom _ _))
  · intro c s
    change affineCoefficient U e (baseScalars g c • s) =
      openScalars g U.1 c * affineCoefficient U e s
    refine (congrArg (affineCoefficient U e)
      (global_smul_eq_scalarEnd (baseScalars g c) s)).trans ?_
    refine (congrArg U.1.topIso.hom
      (coefficient_restrict_scalar_comp U.1.ι e (baseScalars g c) s)).trans ?_
    refine (map_mul U.1.topIso.hom.hom _ _).trans ?_
    apply congrArg (fun value => value * affineCoefficient U e s)
    change (U.1.ι.appTop ≫ U.1.topIso.hom) (baseScalars g c) = openScalars g U.1 c
    have H := congrArg (fun f : ℂ →+* Γ(X,U.1) => f c) (topIso_baseScalars g U.1)
    rw [baseScalars_comp_actual] at H
    exact H

lemma affineCoefficientLinear_injective [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Function.Injective (affineCoefficientLinear g U e) := by
  intro s t h
  apply L.restricted_coefficient_injective U.1.ι e
  exact (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).injective h

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma pullbackSection_linear [IsIntegral Y] (g : X ⟶ complexBase) (h : Y ⟶ complexBase)
    (f : Y ⟶ X) (hf : f ≫ g = h) (L : LineBundle X) :
    letI (M : X.Modules) : Module ℂ (O X ⟶ M) := complexSectionModule g M
    letI (M : Y.Modules) : Module ℂ (O Y ⟶ M) := complexSectionModule h M
    (∀ s t : (O X ⟶ L.sheaf), pullbackSection f (s+t) = pullbackSection f s + pullbackSection f t) ∧
    (∀ (c : ℂ) (s : (O X ⟶ L.sheaf)), pullbackSection f (c • s) = c • (pullbackSection f s : (O Y ⟶ (L.pullback f).sheaf))) := by
  classical
  let (M : X.Modules) : Module ℂ (O X ⟶ M) := complexSectionModule g M
  let (M : Y.Modules) : Module ℂ (O Y ⟶ M) := complexSectionModule h M
  let y : Y := Classical.arbitrary Y
  obtain ⟨V,hyV,⟨eV⟩,-⟩ := common_affine_frames L L (f y)
  obtain ⟨eF,heF⟩ := pullback_affine_coefficient f V eV
  obtain ⟨_,⟨W,hW,rfl⟩,hyW,hWV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ f ⁻¹ᵁ V.1 from hyV) (f ⁻¹ᵁ V.1).isOpen
  let U : Y.affineOpens := ⟨W,hW⟩
  let eU := frameOnSmaller eF U.1 hWV
  let : Nonempty U.1 := ⟨⟨y,hyW⟩⟩
  let : Algebra ℂ Γ(X,V.1) := (openScalars g V.1).toAlgebra
  let : Algebra ℂ Γ(Y,U.1) := (openScalars h U.1).toAlgebra
  let A := affineCoefficientLinear h U eU
  let B := affineCoefficientLinear g V eV
  let F := affineMapAlgHom h g f hf V U hWV
  have hA := affineCoefficientLinear_injective h (L.pullback f) U eU
  have he (s : (O X ⟶ L.sheaf)) : A (pullbackSection f s) = F (B s) := heF U hWV s
  let := complexSectionModule g L.sheaf
  let := complexSectionModule h ((Scheme.Modules.pullback f).obj L.sheaf)
  constructor
  · intro s t
    apply hA
    change A (pullbackSection f (s+t)) = A (pullbackSection f s + pullbackSection f t)
    calc
      A (pullbackSection f (s+t)) = F (B (s+t)) := he _
      _ = F (B s + B t) := congrArg F (B.map_add s t)
      _ = F (B s) + F (B t) := map_add F _ _
      _ = A (pullbackSection f s) + A (pullbackSection f t) :=
        congrArg₂ (· + ·) (he s).symm (he t).symm
      _ = A (pullbackSection f s + pullbackSection f t) := (A.map_add _ _).symm
  · intro c s
    apply hA
    change A (pullbackSection f (c • s)) = A (c • pullbackSection f s)
    calc
      A (pullbackSection f (c • s)) = F (B (c • s)) := he _
      _ = F (c • B s) := congrArg F (B.map_smul c s)
      _ = c • F (B s) := map_smul F c (B s)
      _ = c • A (pullbackSection f s) := congrArg (c • ·) (he s).symm
      _ = A (c • pullbackSection f s) := (A.map_smul c _).symm

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.pullbackSection_linear := @OAI.MaximalSeshadri.Geometry.pullbackSection_linear
