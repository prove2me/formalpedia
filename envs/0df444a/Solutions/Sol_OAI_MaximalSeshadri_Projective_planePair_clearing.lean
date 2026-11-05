-- Prove2me | solution 1 for OAI.MaximalSeshadri.Projective.planePair_clearing
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:24:05.188009+00:00
-- url     : https://prove2.me/submissions/b0655f6b-27fc-4501-9696-c42ffbaa2597

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

lemma end_isIso_iff (f : O X ⟶ O X) : IsIso f ↔ IsUnit (endValue f) := by
  constructor
  · intro h
    let := h
    refine isUnit_iff_exists_inv.mpr ⟨endValue (inv f), ?_⟩
    rw [← endValue_comp]
    simp
  · rintro ⟨u, hu⟩
    refine ⟨⟨scalarEnd ↑u⁻¹, ?_, ?_⟩⟩
    · apply endValue_injective
      rw [endValue_comp, ← hu, endValue_scalarEnd, endValue_id]
      exact Units.val_inv u
    · apply endValue_injective
      rw [endValue_comp, ← hu, endValue_scalarEnd, endValue_id]
      exact Units.inv_val u

lemma coefficient_isUnit_iff {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) :
    IsUnit (coefficient e s) ↔ IsIso s := by
  change IsUnit (endValue (s ≫ e.hom)) ↔ _
  rw [← end_isIso_iff]
  exact isIso_comp_right_iff s e.hom

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

namespace MaximalSeshadri.LaurentPlane
noncomputable section

lemma T_add {K : Type*} [CommRing K] (a b : ℤ × ℤ) :
    T (K := K) (a+b) = T a * T b := by
  simp [T, AddMonoidAlgebra.single_mul_single]

section Evaluation
variable {K R : Type*} [CommRing K] [CommRing R]

@[simp] lemma eval_T (k : K →+* R) (u v : Rˣ) (z : ℤ × ℤ) :
    eval k u v (T z) = ↑(u ^ z.1 * v ^ z.2) := by
  simp [eval, T, monomials, AddMonoidAlgebra.liftNCRingHom_single]

end Evaluation

variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (Ring K) M] [IsScalarTower K (Ring K) M]

end
end MaximalSeshadri.LaurentPlane

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
namespace MaximalSeshadri.SectionOpens
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N : X.Modules}

end
end MaximalSeshadri.SectionOpens

namespace MaximalSeshadri.SectionOpens
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N P : X.Modules}

end
end MaximalSeshadri.SectionOpens
namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

lemma isUnit_iff_basicOpen_top (c : Γ(X, ⊤)) :
    IsUnit c ↔ X.basicOpen c = ⊤ := by
  refine ⟨X.basicOpen_of_isUnit, fun h => ?_⟩
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ c
  intro x hx
  apply (X.mem_basicOpen c x hx).mp
  rw [h]
  trivial

lemma coefficient_restrict_isUnit {M : X.Modules} (e : M ≅ O X)
    (s : O X ⟶ M) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    IsUnit (φ.appTop (coefficient e s)) ↔
      IsIso ((Scheme.Modules.restrictFunctor φ).map s) := by
  rw [← coefficient_restrict, coefficient_isUnit_iff]
  let unitIso : (Scheme.Modules.restrictFunctor φ).obj (O X) ≅ O Y :=
    Scheme.Modules.restrictUnitIso φ
  exact isIso_comp_left_iff unitIso.inv
    ((Scheme.Modules.restrictFunctor φ).map s)

theorem isoOpen_eq_basicOpen {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) :
    SectionOpens.isoOpen s = X.basicOpen (coefficient e s) := by
  ext x
  constructor
  · intro hx
    obtain ⟨U, hxU, hU⟩ := (SectionOpens.mem_isoOpen_iff s x).mp hx
    have hc := (coefficient_restrict_isUnit e s U.ι).mpr hU
    have hb := U.toScheme.basicOpen_of_isUnit hc
    rw [← Scheme.preimage_basicOpen_top] at hb
    have H : (⟨x, hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ X.basicOpen (coefficient e s) := by
      rw [hb]; trivial
    exact H
  · intro hx
    let U := X.basicOpen (coefficient e s)
    refine (SectionOpens.mem_isoOpen_iff s x).mpr ⟨U, hx, ?_⟩
    apply (coefficient_restrict_isUnit e s U.ι).mp
    apply (isUnit_iff_basicOpen_top _).mpr
    rw [← Scheme.preimage_basicOpen_top]
    ext z
    change z.val ∈ X.basicOpen (coefficient e s) ↔ True
    exact iff_true_intro z.property

theorem preimage_isoOpen {M : X.Modules} (s : O X ⟶ M)
    (φ : Y ⟶ X) [IsOpenImmersion φ] (e : M.restrict φ ≅ O Y) :
    φ ⁻¹ᵁ SectionOpens.isoOpen s =
      Y.basicOpen (coefficient e (restrictSection φ s)) := by
  rw [← isoOpen_restrictSection, isoOpen_eq_basicOpen e]

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

theorem affine_sections_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r
      (((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.map
        (PrimeSpectrum.basicOpen r).leTop.op).hom) :=
  ((isIso_fromTildeΓ_iff_isLocalizing (affineToSpecModule M)).mp inferInstance) r

def affineSpecSections [IsAffine X] (M : X.Modules)
    (U : (Spec Γ(X,⊤)).Opens) :
    ((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.obj (op U)) ≃ₗ[Γ(X,⊤)]
      OpenSections M (X.toSpecΓ ⁻¹ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    let : Module Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) :=
      (M.val.obj (op (X.toSpecΓ ⁻¹ᵁ U))).isModule
    change @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
      ((X.toSpecΓ.app U).hom
        ((Spec Γ(X,⊤)).presheaf.map U.leTop.op ((Scheme.ΓSpecIso Γ(X,⊤)).inv r))) m =
      @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
        (restrictScalar X (X.toSpecΓ ⁻¹ᵁ U) r) m
    congr 1
    have h := congrArg (fun f : Γ(Spec Γ(X,⊤),⊤) ⟶ Γ(X,X.toSpecΓ ⁻¹ᵁ U) =>
      f ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) (X.toSpecΓ.naturality U.leTop.op)
    simp only [CommRingCat.comp_apply, Scheme.toSpecΓ_appTop] at h
    change _ = restrictScalar X (X.toSpecΓ ⁻¹ᵁ U)
      ((Scheme.ΓSpecIso Γ(X,⊤)).hom ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) at h
    rw [(Scheme.ΓSpecIso Γ(X,⊤)).inv_hom_id_apply r] at h
    exact h

def openSectionsCongr (M : X.Modules) {U V : X.Opens} (h : U = V) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections M V := by
  subst V
  exact LinearEquiv.refl _ _

lemma openSectionsCongr_restriction (M : X.Modules) {U V : X.Opens} (h : U = V)
    (m : OpenSections M ⊤) :
    openSectionsCongr M h (openRestriction M (show U ≤ ⊤ from le_top) m) = openRestriction M (show V ≤ ⊤ from le_top) m := by
  subst V
  rfl

theorem affine_openRestriction_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r (openRestriction M (X.basicOpen_le r)) := by
  let F := modulesSpecToSheaf.obj (affineToSpecModule M)
  let f := (F.obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  let e0 : (F.obj.obj (op ⊤)) ≃ₗ[Γ(X,⊤)] OpenSections M ⊤ := affineSpecSections M ⊤
  let e1 := (affineSpecSections M (PrimeSpectrum.basicOpen r)).trans
    (openSectionsCongr M (Scheme.toSpecΓ_preimage_basicOpen X r))
  have hf : IsLocalizedModule.Away r f := affine_sections_localize M r
  have hq : IsLocalizedModule.Away r (e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap) := by
    have := hf
    have := IsLocalizedModule.of_linearEquiv (.powers r) f e1
    exact IsLocalizedModule.of_linearEquiv_right (.powers r) (e1.toLinearMap ∘ₗ f) e0.symm
  have he : e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap =
      openRestriction M (X.basicOpen_le r) := by
    ext m
    exact openSectionsCongr_restriction M (Scheme.toSpecΓ_preimage_basicOpen X r) m
  rwa [he] at hq

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

variable {X Y Z : Scheme.{0}}

theorem openImmersionTop_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] (t : Γ(X,⊤))
    (hf : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    IsLocalizedModule.Away t (openImmersionTop M f) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  have he : X.basicOpen t = f ''ᵁ (⊤ : Y.Opens) :=
    hf.symm.trans (Scheme.Hom.image_top_eq_opensRange f).symm
  let e := (openSectionsCongr M he).trans (restrictedOpenSections M f ⊤).symm
  let g := openRestriction M (X.basicOpen_le t)
  have : IsLocalizedModule.Away t g := affine_openRestriction_localize M t
  have h := IsLocalizedModule.of_linearEquiv (.powers t) g e
  have hp : e.toLinearMap ∘ₗ g = openImmersionTop M f := by
    ext m
    change (restrictedOpenSections M f ⊤).symm
      (openSectionsCongr M he (openRestriction M (X.basicOpen_le t) m)) = _
    rw [openSectionsCongr_restriction]
    rfl
  rwa [hp] at h

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

theorem chartModuleMap_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] {N : Y.Modules} (e : M.restrict f ≅ N)
    (t : Γ(X,⊤)) (ht : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    IsLocalizedModule.Away t (chartModuleMap M f e) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let : IsLocalizedModule.Away t (openImmersionTop M f) :=
    openImmersionTop_localize M f t ht
  exact IsLocalizedModule.of_linearEquiv (.powers t) (openImmersionTop M f)
    (chartModuleEquiv M f e)

namespace BaseSections
variable {K : Type} [CommRing K]

lemma chartMap_smul (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N)
    (r : Γ(X,⊤)) (m : Sections kX M ⊤) :
    chartMap kX kY f hk M e (r • m) = f.appTop r • chartMap kX kY f hk M e m := by
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  exact (chartModuleMap M f e).map_smul r m

end BaseSections
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

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.LaurentPlane

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

theorem chartMap_clearing [IsAffine X]
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) [M.IsQuasicoherent] {N : Y.Modules} (e : M.restrict f ≅ N)
    (a : Γ(X,⊤)) (ha : f.opensRange = X.basicOpen a) (m : Sections kY N ⊤) :
    ∃ d : ℕ, f.appTop a ^ d • m ∈ (chartMap kX kY f hk M e).range := by
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let F := chartModuleMap M f e
  let : IsLocalizedModule.Away a F := chartModuleMap_localize M f e a ha
  obtain ⟨d,n,hn⟩ := (inferInstance : IsLocalizedModule.Away a F).surj _ _ m
  refine ⟨d,n,?_⟩
  change f.appTop (a^d) • (m : OpenSections N ⊤) = F n at hn
  change F n = f.appTop a ^ d • (m : OpenSections N ⊤)
  rw [map_pow] at hn
  exact hn.symm

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {σ : Type} {X : Scheme.{0}} {M : X.Modules}

@[simp] lemma ratioUnitOn_val (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j)) :
    (ratioUnitOn s i j U hi hj : Γ(U.toScheme,⊤)) = ratioOn s i j U hi := by
  have h := coefficient_change (sectionFrameOn (s j) U hj)
    (sectionFrameOn (s i) U hi) (restrictSection U.ι (s j))
  dsimp only [ratioUnitOn, ratioOn]
  simpa only [sectionFrameOn_normalized, mul_one] using h.symm

lemma ratioOn_restrict (s : σ → (O X ⟶ M)) (i j : σ) {U W : X.Opens}
    (hi : U ≤ SectionOpens.isoOpen (s i)) (h : W ≤ U) :
    (X.homOfLE h).appTop (ratioOn s i j U hi) = ratioOn s i j W (h.trans hi) := by
  dsimp only [ratioOn]
  rw [sectionFrameOn_coefficient, sectionFrameOn_coefficient]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_homOfLE]

lemma ratioOn_cocycle (s : σ → (O X ⟶ M)) (i j l : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j)) :
    ratioOn s i l U hi = ratioOn s i j U hi * ratioOn s j l U hj := by
  have h := coefficient_change (sectionFrameOn (s j) U hj)
    (sectionFrameOn (s i) U hi) (restrictSection U.ι (s l))
  rw [← ratioUnitOn_val s i j U hi hj]
  exact h

lemma ratioUnitOn_cocycle (s : σ → (O X ⟶ M)) (i j l : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j))
    (hl : U ≤ SectionOpens.isoOpen (s l)) :
    ratioUnitOn s i l U hi hl = ratioUnitOn s i j U hi hj * ratioUnitOn s j l U hj hl := by
  apply Units.ext
  simp only [Units.val_mul, ratioUnitOn_val]
  exact ratioOn_cocycle s i j l U hi hj

lemma ratioOn_basicOpen (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) :
    U.ι ⁻¹ᵁ SectionOpens.isoOpen (s j) = U.toScheme.basicOpen (ratioOn s i j U hi) :=
  preimage_isoOpen (s j) U.ι (sectionFrameOn (s i) U hi)

end
end MaximalSeshadri.Projective

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.LaurentPlane
variable {K : Type*} [CommRing K]
lemma T_nsmul (n : ℕ) (z : ℤ × ℤ) : T (K := K) (n • z) = (T z)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul,T_add,ih,pow_succ]
end MaximalSeshadri.LaurentPlane

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

lemma ratioUnitOn_self (s : Fin 3 → (O X ⟶ M)) (i : Fin 3) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) : ratioUnitOn s i i U hi hi = 1 := by
  have h := ratioUnitOn_cocycle s i i i U hi hi hi
  exact mul_left_cancel (show ratioUnitOn s i i U hi hi * ratioUnitOn s i i U hi hi =
    ratioUnitOn s i i U hi hi * 1 by rw [← h,mul_one])

lemma plane_weight_unit (s : Fin 3 → (O X ⟶ M)) (i : Fin 3) :
    ratioUnitOn s 0 i (planeTriple s) (planeTriple_le s 0) (planeTriple_le s i) =
      (planeX s) ^ (weight i).1 * (planeY s) ^ (weight i).2 := by
  fin_cases i
  · simpa [weight] using ratioUnitOn_self s 0 (planeTriple s) (planeTriple_le s 0)
  · simp [weight,planeX]
  · simp [weight,planeY]

lemma plane_ratio_weight (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (i j : Fin 3) :
    ratioOn s i j (planeTriple s) (planeTriple_le s i) =
      LaurentPlane.eval ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
        (T (weight j - weight i)) := by
  rw [← ratioUnitOn_val s i j _ (planeTriple_le s i) (planeTriple_le s j),eval_T]
  congr 1
  have h := ratioUnitOn_cocycle s 0 i j (planeTriple s) (planeTriple_le s 0)
    (planeTriple_le s i) (planeTriple_le s j)
  have he : ratioUnitOn s i j (planeTriple s) (planeTriple_le s i) (planeTriple_le s j) =
      (ratioUnitOn s 0 i (planeTriple s) (planeTriple_le s 0) (planeTriple_le s i))⁻¹ *
        ratioUnitOn s 0 j (planeTriple s) (planeTriple_le s 0) (planeTriple_le s j) := by
    rw [h]; simp
  rw [he,plane_weight_unit,plane_weight_unit]
  simp only [Prod.fst_sub,Prod.snd_sub,zpow_sub,mul_inv_rev]
  ac_rfl

lemma plane_ratio_weight_restrict (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M))
    (i j : Fin 3) (U : X.Opens) (hi : U ≤ SectionOpens.isoOpen (s i)) (hW : planeTriple s ≤ U) :
    (X.homOfLE hW).appTop (ratioOn s i j U hi) =
      LaurentPlane.eval ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
        (T (weight j-weight i)) := by
  rw [ratioOn_restrict]
  exact plane_ratio_weight k s i j

end
end MaximalSeshadri.Projective

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

lemma pairRestriction_basic (s : Fin 3 → (O X ⟶ M)) (i j : Fin 3)
    (U W : X.Opens) (hi : U ≤ SectionOpens.isoOpen (s i)) (h : W ≤ U)
    (he : W = U ⊓ SectionOpens.isoOpen (s j)) :
    (X.homOfLE h).opensRange = U.toScheme.basicOpen (ratioOn s i j U hi) := by
  rw [Scheme.opensRange_homOfLE,he,Scheme.Hom.preimage_inf,
    Scheme.Opens.ι_preimage_self,top_inf_eq]
  exact ratioOn_basicOpen s i j U hi

end
end MaximalSeshadri.Projective

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {K : Type} [Field K] {X : Scheme.{0}}

lemma chartRes_comp (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V W : X.Opens}
    (h : W ≤ V) (g : V ≤ U)
    (m : Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤) :
    chartRes k M h (chartRes k M g m) = chartRes k M (h.trans g) m := by
  apply (chartTop k M W).injective
  rw [chartTop_nested,chartTop_nested,chartTop_nested,res_comp]

theorem chartRes_cross_clearing (k : K →+* Γ(X,⊤)) (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) [IsAffine U.toScheme] (hU : W ≤ U) (hV : W ≤ V)
    (a : Γ(U.toScheme,⊤))
    (ha : (X.homOfLE (show U ⊓ V ≤ U from inf_le_left)).opensRange = U.toScheme.basicOpen a)
    (m : Sections (W.ι.appTop.hom.comp k) (M.restrict W.ι) ⊤)
    (hm : m ∈ (chartRes k M hV).range) :
    ∃ n : ℕ, (X.homOfLE hU).appTop a ^ n • m ∈ (chartRes k M hU).range := by
  obtain ⟨v,rfl⟩ := hm
  let P := U ⊓ V
  have hP : W ≤ P := le_inf hU hV
  let f := X.homOfLE (show P ≤ U from inf_le_left)
  let g := X.homOfLE (show P ≤ V from inf_le_right)
  let w := chartRes k M (show P ≤ V from inf_le_right) v
  obtain ⟨n,u,hu⟩ := chartMap_clearing (U.ι.appTop.hom.comp k) (P.ι.appTop.hom.comp k)
    f (nestedBase k inf_le_left) (M.restrict U.ι) (nestedRestriction M inf_le_left) a ha w
  refine ⟨n,u,?_⟩
  have he := congrArg (chartRes k M hP) hu
  rw [chartRes_comp,chartMap_smul,map_pow,chartRes_comp] at he
  have har : (X.homOfLE hP).appTop (f.appTop a) = (X.homOfLE hU).appTop a := by
    rw [← CommRingCat.comp_apply,← Scheme.Hom.comp_appTop]
    rw [show X.homOfLE hP ≫ f = X.homOfLE hU from Scheme.homOfLE_homOfLE X hP inf_le_left]
  simpa only [har] using he

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

lemma planePair_clearing (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (haff : ∀ i, IsAffineOpen (SectionOpens.isoOpen (s i)))
    (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ i j x, x ∈ planePair k s L i j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ planeVertex k s L i := by
  let := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
    (L.sheaf.restrict (planeTriple s).ι)
  intro i j x hx
  let U := SectionOpens.isoOpen (s i)
  let V := U ⊓ SectionOpens.isoOpen (s j)
  let : IsAffine U.toScheme := haff i
  have hbasic : (X.homOfLE (show U ⊓ V ≤ U from inf_le_left)).opensRange =
      U.toScheme.basicOpen (ratioOn s i j U le_rfl) := by
    apply pairRestriction_basic s i j U (U ⊓ V) le_rfl inf_le_left
    simp only [V,← inf_assoc,inf_idem]
  obtain ⟨d,hd⟩ := chartRes_cross_clearing k L.sheaf U V (planeTriple s)
    (planeTriple_le s i) (le_inf (planeTriple_le s i) (planeTriple_le s j))
    (ratioOn s i j U le_rfl) hbasic x hx
  refine ⟨d,?_⟩
  rw [plane_ratio_weight_restrict k s i j U le_rfl (planeTriple_le s i),← map_pow,← T_nsmul] at hd
  exact hd

end
end MaximalSeshadri.Projective

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Projective.planePair_clearing := @OAI.MaximalSeshadri.Projective.planePair_clearing
