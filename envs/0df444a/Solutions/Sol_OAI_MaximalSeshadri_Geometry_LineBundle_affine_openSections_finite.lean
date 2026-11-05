-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.LineBundle.affine_openSections_finite
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:19:51.934202+00:00
-- url     : https://prove2.me/submissions/cbe5bafd-5116-4bad-9118-18673685255e

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

set_option Elab.async false
set_option linter.all false

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
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y : Scheme}

def frameOfLE (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.restrict V.ι ≅ structureSheaf V.toScheme := by
  let e' := (Scheme.Modules.restrictFunctorComp (Y.homOfLE h) U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (Y.homOfLE h)
  simp only [Y.homOfLE_ι h] at e'
  exact e'

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.TensorLocalization
noncomputable section
open CategoryTheory MonoidalCategory
universe v' u'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

end
end MaximalSeshadri.TensorLocalization

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory BraidedCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

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

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

lemma finite_sections_of_frame {X : Scheme.{0}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) : Module.Finite Γ(X,U) Γ(M,U) := by
  let e' : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) := overFrame e
  let j : Over U := Over.mk (𝟙 U)
  let f : Γ(X,U) →ₗ[Γ(X,U)] Γ(M,U) := (e'.inv.val.app (op j)).hom
  have hf : Function.Surjective f := (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation (X.ringCatSheaf.over U) (op j)).mapIso e').inv).surjective
  exact Module.Finite.of_surjective f hf

set_option backward.isDefEq.respectTransparency.types false in
theorem LineBundle.spec_sections_finite {R : CommRingCat.{0}} (L : LineBundle (Spec R)) :
    Module.Finite R ((modulesSpecToSheaf.obj L.sheaf).obj.obj (op ⊤)) := by
  classical
  let D (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let t : Set R := {r | Nonempty (L.sheaf.restrict (D r).ι ≅
    structureSheaf (D r).toScheme)}
  have ht : Ideal.span t = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    apply top_unique
    intro x hx
    obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne x
    obtain ⟨_,⟨_,⟨r,rfl⟩,rfl⟩,hxr,hrU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr
      ⟨⟨MaximalSeshadri.InvertibleLocal.frameOfLE L.sheaf hrU e⟩,hxr⟩⟩
  let M := ((modulesSpecToSheaf.obj L.sheaf).obj.obj (op ⊤))
  let (r : t) : Module R Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    inferInstanceAs <| Module R
      ((modulesSpecToSheaf.obj L.sheaf).obj.obj (op (PrimeSpectrum.basicOpen r.val)))
  let (r : t) : Module Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    (L.sheaf.val.obj (op (PrimeSpectrum.basicOpen r.val))).isModule
  have (r : t) : IsScalarTower R Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    IsScalarTower.of_compHom R Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val)
  let f (r : t) : M →ₗ[R] Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    ((modulesSpecToSheaf.obj L.sheaf).obj.map (homOfLE le_top).op).hom
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing L.sheaf).mp inferInstance
  have (r : t) : IsLocalizedModule.Away r.val (f r) := hloc r.val
  have hfin (r : t) : Module.Finite Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    finite_sections_of_frame L.sheaf _ r.property.some
  exact Module.Finite.of_localizationSpan' t ht f hfin

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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

def LineBundle.restrict (L : LineBundle Y) (f : X ⟶ Y) [IsOpenImmersion f] : LineBundle X where
  sheaf := L.sheaf.restrict f
  locallyRankOne x := by
    obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne (f x)
    let V := f ⁻¹ᵁ U
    refine ⟨V,hxU,⟨?_⟩⟩
    let e' := (Scheme.Modules.restrictFunctorComp (f ∣_ U) U.ι).app L.sheaf ≪≫
      (Scheme.Modules.restrictFunctor (f ∣_ U)).mapIso e ≪≫
      Scheme.Modules.restrictUnitIso (f ∣_ U)
    have e'' : L.sheaf.restrict (V.ι ≫ f) ≅ structureSheaf V.toScheme := by
      simpa only [V, morphismRestrict_ι, structureSheaf] using e'
    exact ((Scheme.Modules.restrictFunctorComp V.ι f).app L.sheaf).symm ≪≫ e''

theorem LineBundle.affine_sections_finite [IsAffine X] (L : LineBundle X) :
    Module.Finite Γ(X,⊤) Γ(L.sheaf,⊤) := by
  let f := X.isoSpec.inv
  let J := L.restrict f
  let R := Γ(X,⊤)
  let M := (modulesSpecToSheaf.obj J.sheaf).obj.obj (op ⊤)
  let : Module.Finite R M := J.spec_sections_finite
  let σ : R →+* Γ(X,f ''ᵁ ⊤) := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let φ : M →ₛₗ[σ] Γ(L.sheaf,f ''ᵁ ⊤) := {
    toFun := (L.sheaf.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (L.sheaf.restrictAppIso f ⊤).hom).surjective
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have h := Module.Finite.of_surjective φ hφ
  rw [hf] at h
  exact h

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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem quasicoherent_pushforward_iso (e : X ≅ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward e.hom).obj M).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward e.hom).obj M
  let q : (Scheme.Modules.pushforward e.inv).obj N ≅ M :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app M ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app M ≪≫
      (Scheme.Modules.pushforwardId X).app M
  let j : N ≅ M.restrict e.inv :=
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app N).symm ≪≫
      (Scheme.Modules.restrictFunctor e.inv).mapIso q
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso j.symm inferInstance

abbrev affineToSpecModule [IsAffine X] (M : X.Modules) :=
  (Scheme.Modules.pushforward X.toSpecΓ).obj M

instance affineToSpecModule_quasicoherent [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : (affineToSpecModule M).IsQuasicoherent :=
  quasicoherent_pushforward_iso X.isoSpec M

def openTopSections (M : X.Modules) :
    letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
    OpenSections M ⊤ ≃ₗ[Γ(X,⊤)] Γ(M,⊤) := by
  letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,⊤) Γ(M,⊤) _ (restrictScalar X ⊤ r) m =
    @SMul.smul Γ(X,⊤) Γ(M,⊤) _ r m
  congr 1
  change (X.presheaf.map (𝟙 (op ⊤))) r = r
  rw [X.presheaf.map_id]
  rfl

theorem LineBundle.affine_openSections_finite [IsAffine X] (L : LineBundle X) :
    Module.Finite Γ(X,⊤) (OpenSections L.sheaf ⊤) := by
  let : Module Γ(X,⊤) Γ(L.sheaf,⊤) := (L.sheaf.val.obj (op ⊤)).isModule
  have := L.affine_sections_finite
  exact Module.Finite.of_surjective (openTopSections L.sheaf).symm.toLinearMap
    (openTopSections L.sheaf).symm.surjective

end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.LineBundle.affine_openSections_finite := @OAI.MaximalSeshadri.Geometry.LineBundle.affine_openSections_finite
