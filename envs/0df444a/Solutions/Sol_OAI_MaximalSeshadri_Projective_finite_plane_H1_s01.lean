-- Prove2me | solution 1 for OAI.MaximalSeshadri.Projective.finite_plane_H1_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:21:24.839985+00:00
-- url     : https://prove2.me/submissions/71a5b19d-8fe5-40c2-8171-d5cfb50b6fbd

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_PlaneCech_toric_H1_finite_s01
import Theorems.Thm_OAI_MaximalSeshadri_Projective_planeVertex_finite_generators_s01

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PlaneChartAlgebra
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.LaurentPlane
noncomputable section
variable {K A R : Type*} [CommRing K] [CommRing A] [CommRing R]

lemma map_unit_zpow (f : A →+* R) (a : Aˣ) (n : ℤ) :
    f (a ^ n : Aˣ) = ((Units.map f a) ^ n : Rˣ) := by
  change (((Units.map f.toMonoidHom) (a ^ n) : Rˣ) : R) = _
  exact congrArg Units.val (map_zpow (Units.map f.toMonoidHom) a n)

lemma lift_cone_left (k : K →+* R) (u v : Rˣ) (f : A →+* R)
    (x : Aˣ) (y : A) (hx : Units.map f x = u) (hy : f y = v)
    (z : ℤ × ℤ) (hz : 0 ≤ z.2) :
    f (↑(x ^ z.1) * y ^ z.2.toNat) = eval k u v (T z) := by
  rw [map_mul, map_pow, map_unit_zpow, hx, hy, eval_T, Units.val_mul]
  have he : z.2 = (z.2.toNat : ℤ) := (Int.toNat_of_nonneg hz).symm
  rw [he, zpow_natCast, Units.val_pow_eq_pow_val]
  simp [max_eq_left hz]

lemma lift_cone_right (k : K →+* R) (u v : Rˣ) (f : A →+* R)
    (x : A) (y : Aˣ) (hx : f x = u) (hy : Units.map f y = v)
    (z : ℤ × ℤ) (hz : 0 ≤ z.1) :
    f (x ^ z.1.toNat * ↑(y ^ z.2)) = eval k u v (T z) := by
  rw [map_mul, map_pow, map_unit_zpow, hx, hy, eval_T, Units.val_mul]
  have he : z.1 = (z.1.toNat : ℤ) := (Int.toNat_of_nonneg hz).symm
  rw [he, zpow_natCast, Units.val_pow_eq_pow_val]
  simp [max_eq_left hz]

lemma lift_cone_top (k : K →+* R) (u v : Rˣ) (f : A →+* R)
    (x : Aˣ) (y : A) (hx : Units.map f x = u * v⁻¹) (hy : f y = ↑(v⁻¹))
    (z : ℤ × ℤ) (hz : z.1 + z.2 ≤ 0) :
    f (↑(x ^ z.1) * y ^ (-(z.1 + z.2)).toNat) = eval k u v (T z) := by
  rw [map_mul, map_pow, map_unit_zpow, hx, hy, eval_T]
  have hn : ((-(z.1 + z.2)).toNat : ℤ) = -(z.1 + z.2) :=
    Int.toNat_of_nonneg (by omega)
  rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, hn, ← Units.val_mul]
  congr 1
  rw [mul_zpow, mul_assoc, ← zpow_add]
  have he : z.1 + -(z.1 + z.2) = -z.2 := by omega
  rw [he]
  simp

end
end MaximalSeshadri.LaurentPlane

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_AffineLocalizing
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

instance affineToSpecModule_quasicoherent [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : (affineToSpecModule M).IsQuasicoherent :=
  quasicoherent_pushforward_iso X.isoSpec M

theorem affine_sections_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r
      (((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.map
        (PrimeSpectrum.basicOpen r).leTop.op).hom) :=
  ((isIso_fromTildeΓ_iff_isLocalizing (affineToSpecModule M)).mp inferInstance) r

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
-- module Solutions.Q223_SES.Seshadri_Sheaves_RestrictionLocalization
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
-- module Solutions.Q223_SES.Seshadri_Sheaves_ChartModuleMap
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PlaneModules
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.LaurentPlane

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

theorem laurentTower (k : K →+* Γ(Y,⊤)) (u v : Γ(Y,⊤)ˣ) (N : Y.Modules) :
    letI := laurentModule k u v N
    IsScalarTower K (LaurentPlane.Ring K) (Sections k N ⊤) := by
  let := laurentModule k u v N
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change LaurentPlane.eval k u v (algebraMap K (LaurentPlane.Ring K) r) •
    (m : OpenSections N ⊤) = k r • (m : OpenSections N ⊤)
  rw [LaurentPlane.eval_algebraMap]

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

lemma chartMap_monomial_mem
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N)
    (u v : Γ(Y,⊤)ˣ) (z : ℤ × ℤ)
    (h : ∃ a : Γ(X,⊤), f.appTop a = LaurentPlane.eval kY u v (T z)) :
    letI := laurentModule kY u v N
    ∀ m ∈ (chartMap kX kY f hk M e).range,
      T (K := K) z • m ∈ (chartMap kX kY f hk M e).range := by
  let := laurentModule kY u v N
  rintro m ⟨n,rfl⟩
  obtain ⟨a,ha⟩ := h
  refine ⟨a • n,?_⟩
  change chartMap kX kY f hk M e (a • n) =
    LaurentPlane.eval kY u v (T z) • chartMap kX kY f hk M e n
  rw [chartMap_smul,ha]

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_SectionMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coordinatesMap_preimage (X : Scheme.{u}) (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) (j : σ) :
    coordinatesMap X k a i hi ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j) = X.basicOpen (a j) := by
  rw [coordinatesMap, Scheme.Hom.comp_preimage,
    fromUnitCoordinate_preimage _ (coordinates_X_mem (K := K) i) _
      (by simpa only [eval₂Hom_X'] using hi) (by decide) (coordinates_X_mem (K := K) j),
    eval₂Hom_X', Scheme.toSpecΓ_preimage_basicOpen]

end

end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionsMorphism_preimage {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (j : σ) :
    sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j) =
      SectionOpens.isoOpen (s j) := by
  ext x
  have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let U := SectionOpens.isoOpen (s i)
  have H : U.ι ⁻¹ᵁ (sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j)) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen (s j) := by
    rw [← Scheme.Hom.comp_preimage, sectionsMorphism_local,
      coordinatesMap_preimage, preimage_isoOpen (s j) U.ι (sectionFrame (s i))]
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : U.toScheme)

end
end MaximalSeshadri.Projective

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ClosedEmbedding
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open scoped AlgebraicGeometry
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma evalAway_constants {R : Type u} [CommRing R] (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))).comp
      ((fromZeroRingHom (homogeneousSubmodule σ K) (.powers (X i))).comp
        projectiveConstants) = k := by
  apply RingHom.ext
  intro c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ K)
      (.powers (X i)) (projectiveConstants c)).val = k c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (algebraMap (MvPolynomial σ K) (Localization.Away (X i)) (C c)) = k c
  rw [IsLocalization.Away.lift_eq, eval₂Hom_C]

@[reassoc]
theorem coordinatesMap_over {X : Scheme.{u}} (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) :
    coordinatesMap X k a i hi ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  simp only [coordinatesMap, fromUnitCoordinate, projectiveBase, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (evalAway_constants k a i hi)

@[reassoc]
theorem sectionsMorphism_over {X : Scheme.{u}} {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (MaximalSeshadri.Frames.O X ⟶ M))
    (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    sectionsMorphism k s hcover ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover).hom_ext
  intro i
  change σ at i
  change (SectionOpens.isoOpen (s i)).ι ≫ _ = _
  rw [← Category.assoc, sectionsMorphism_local, coordinatesMap_over]
  change _ = (SectionOpens.isoOpen (s i)).ι ≫ X.toSpecΓ ≫ _
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

instance sectionsMorphism_proper {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (sectionsMorphism k s hcover) := by
  have : IsProper (sectionsMorphism k s hcover ≫ projectiveBase) := by
    rw [sectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PencilCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_C _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_X
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K]

lemma affine_evaluation_finite {R : Type} [CommRing R] {Y : Scheme}
    (f : R →+* Γ(Y,⊤)) [IsFinite (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f))] :
    f.Finite := by
  let g := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hEq : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop = CommRingCat.ofHom f := by
    simp only [g, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have h := g.finite_appTop.comp (RingHom.Finite.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.Finite at h
  simpa only [hEq, CommRingCat.hom_ofHom] using h

lemma normalized_evalAway_polyToChart {R : Type} [CommRing R]
    (k : K →+* R) (a : σ → R) (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : R)))).comp
      (polyToChart i) = eval₂Hom k (fun j : ChartVariables i => a j) := by
  let F := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : R)))
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, polyToChart, eval₂Hom_C]
    change F (chartConstants i r) = k r
    exact RingHom.congr_fun (evalAway_constants k a i hi) r
  · intro j
    simp only [RingHom.comp_apply, polyToChart, eval₂Hom_X']
    change F (chartCoordinate i j.val) = a j.val
    have H := evalAway_mk_clear (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (MvPolynomial.X i)) by simpa only [eval₂Hom_X',hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (X j.val) (by simpa using isHomogeneous_X K j.val)
    simpa only [chartCoordinate, eval₂Hom_X',hi,one_pow,mul_one] using H

theorem finite_sectionsMorphism_chart {X : Scheme} {M : X.Modules}
    (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (i : σ) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧
    (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (fun j : ChartVariables i => coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))).Finite := by
  let V := projectiveCoordinateCover (K := K) (σ := σ)
  let U := SectionOpens.isoOpen (s i)
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme,⊤) := fun j => coefficient (sectionFrame (s i))
    (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let f := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme,⊤))))
  let g := U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  let chart := Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i)
    (isHomogeneous_X K i) (show 0 < 1 by decide)
  have : IsOpenImmersion chart := V.map_prop i
  have H : IsPullback g U.ι chart (sectionsMorphism k s hs) := by
    apply IsOpenImmersion.isPullback
    · exact (sectionsMorphism_local k s hs i).trans (Category.assoc _ _ _).symm
    · have hrange : chart.opensRange =
          Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X i) :=
        Proj.opensRange_awayι _ _ (isHomogeneous_X K i) (show 0 < 1 by decide)
      rw [hrange, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  have hg : IsFinite g := MorphismProperty.of_isPullback H.flip inferInstance
  refine ⟨isAffine_of_isAffineHom g, ?_⟩
  have hf := (@affine_evaluation_finite _ _ U.toScheme f hg).comp (RingHom.Finite.of_surjective
    (polyToChart (R := K) i) (polynomialChartEquiv (R := K) i).symm.surjective)
  rwa [normalized_evalAway_polyToChart k' a i hi] at hf

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PlaneCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {σ : Type} {X : Scheme.{0}} {M : X.Modules}

lemma ratioOn_restrict (s : σ → (O X ⟶ M)) (i j : σ) {U W : X.Opens}
    (hi : U ≤ SectionOpens.isoOpen (s i)) (h : W ≤ U) :
    (X.homOfLE h).appTop (ratioOn s i j U hi) = ratioOn s i j W (h.trans hi) := by
  dsimp only [ratioOn]
  rw [sectionFrameOn_coefficient, sectionFrameOn_coefficient]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_homOfLE]

lemma ratioUnitOn_restrict (s : σ → (O X ⟶ M)) (i j : σ) {U W : X.Opens}
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j))
    (h : W ≤ U) :
    Units.map (X.homOfLE h).appTop.hom (ratioUnitOn s i j U hi hj) =
      ratioUnitOn s i j W (h.trans hi) (h.trans hj) := by
  apply Units.ext
  simp only [Units.coe_map, ratioUnitOn_val]
  exact ratioOn_restrict s i j hi h

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

lemma ratioUnitOn_symm (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j)) :
    ratioUnitOn s j i U hj hi = (ratioUnitOn s i j U hi hj)⁻¹ := by
  change frameChange _ _ = (frameChange _ _)⁻¹
  rfl

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
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlanePairs
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

lemma planeThird_unit (s : Fin 3 → (O X ⟶ M)) :
    ratioUnitOn s 2 1 (planeTriple s) (planeTriple_le s 2) (planeTriple_le s 1) =
      planeX s * (planeY s)⁻¹ := by
  have h := ratioUnitOn_cocycle s 0 2 1 (planeTriple s)
    (planeTriple_le s 0) (planeTriple_le s 2) (planeTriple_le s 1)
  change planeX s = planeY s * _ at h
  calc
    _ = (planeY s)⁻¹ * planeX s := by rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
    _ = _ := mul_comm _ _

end
end MaximalSeshadri.Projective

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

lemma plane_vertex_lift (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (i : Fin 3)
    (z : ℤ × ℤ) (hz : z ∈ vertexCone i) :
    ∃ a : Γ((SectionOpens.isoOpen (s i)).toScheme,⊤),
      (X.homOfLE (planeTriple_le s i)).appTop a =
      LaurentPlane.eval ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s) (T z) := by
  let E := LaurentPlane.eval ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
  have lift (j l : Fin 3) (n m : ℕ) (he : n • (weight j-weight i) + m • (weight l-weight i) = z) :
      ∃ a : Γ((SectionOpens.isoOpen (s i)).toScheme,⊤),
        (X.homOfLE (planeTriple_le s i)).appTop a = E (T z) := by
    refine ⟨ratioOn s i j _ le_rfl ^ n * ratioOn s i l _ le_rfl ^ m,?_⟩
    rw [map_mul,map_pow,map_pow,plane_ratio_weight_restrict k s i j _ le_rfl _,
      plane_ratio_weight_restrict k s i l _ le_rfl _,← map_pow,← map_pow,
      ← T_nsmul,← T_nsmul,← map_mul,← T_add,he]
  fin_cases i
  · apply lift 1 2 z.1.toNat z.2.toNat
    have ha : 0 ≤ z.1 := hz.2
    have hb : 0 ≤ z.2 := hz.1
    ext <;> simp [weight,Int.toNat_of_nonneg ha,Int.toNat_of_nonneg hb]
  · apply lift 0 2 (-(z.1+z.2)).toNat z.2.toNat
    have ha : 0 ≤ -(z.1+z.2) := by have := hz.2; change z.1+z.2 ≤ 0 at this; omega
    have hb : 0 ≤ z.2 := hz.1
    ext <;> simp [weight,Int.toNat_of_nonneg hb]
    omega
  · apply lift 0 1 (-(z.1+z.2)).toNat z.1.toNat
    have ha : 0 ≤ -(z.1+z.2) := by have := hz.2; change z.1+z.2 ≤ 0 at this; omega
    have hb : 0 ≤ z.1 := hz.1
    ext <;> simp [weight,Int.toNat_of_nonneg hb]
    omega

end
end MaximalSeshadri.Projective

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricSpan
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

lemma shift_span_mem {ι : Type*} (S U : Set (ℤ × ℤ)) (g : ι → M)
    (z : ℤ × ℤ) (hz : ∀ w ∈ S, z+w ∈ U) (x : M) (hx : x ∈ monomialSpan (K := K) S g) :
    T (K := K) z • x ∈ monomialSpan (K := K) U g := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,w,hw,rfl⟩ := hx
    rw [← mul_smul,← T_add]
    exact Submodule.subset_span ⟨i,z+w,hz w hw,rfl⟩
  | zero => simp
  | add x y hx hy ih ih' => simpa only [smul_add] using (monomialSpan (K := K) U g).add_mem ih ih'
  | smul a x hx ih =>
    rw [smul_comm]
    exact (monomialSpan (K := K) U g).smul_mem a ih

omit [IsScalarTower K (LaurentPlane.Ring K) M] in
lemma monomialSpan_le {ι : Type*} (S : Set (ℤ × ℤ)) (g : ι → M)
    (V : Submodule K M) (hg : ∀ i, g i ∈ V)
    (h : ∀ z ∈ S, ∀ x ∈ V, T (K := K) z • x ∈ V) : monomialSpan (K := K) S g ≤ V := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,z,hz,rfl⟩
  exact h z hz _ (hg i)

theorem localized_span {ι : Type*} (S U : Set (ℤ × ℤ)) (g : ι → M)
    (A : Submodule K M) (hg : ∀ a, g a ∈ A)
    (stable : ∀ z ∈ U, ∀ x ∈ A, T (K := K) z • x ∈ A)
    (clear : ∀ x ∈ A, ∃ z : ℤ × ℤ,
      T (K := K) z • x ∈ monomialSpan (K := K) S g ∧ ∀ w ∈ S, -z+w ∈ U) :
    A = monomialSpan (K := K) U g := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z,hz,hshift⟩ := clear x hx
    have hm := shift_span_mem S U g (-z) hshift _ hz
    rw [← mul_smul,← T_add,neg_add_cancel,T_zero,one_smul] at hm
    exact hm
  · exact monomialSpan_le U g A hg stable

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_NestedChart
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

lemma chartRes_range_le (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V W : X.Opens}
    (h : W ≤ V) (g : V ≤ U) :
    (chartRes k M (h.trans g)).range ≤ (chartRes k M h).range := by
  rintro _ ⟨m,rfl⟩
  exact ⟨chartRes k M g m,chartRes_comp k M h g m⟩

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
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneVertex
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

lemma planeVertex_stable (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ i z, z ∈ vertexCone i → ∀ x ∈ planeVertex k s L i, T (K := K) z • x ∈ planeVertex k s L i := by
  let := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
    (L.sheaf.restrict (planeTriple s).ι)
  intro i z hz
  apply chartMap_monomial_mem _ _ _ _ _ _ (planeX s) (planeY s) z
  exact plane_vertex_lift k s i z hz

lemma planeVertex_cross_clearing (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (haff : ∀ i, IsAffineOpen (SectionOpens.isoOpen (s i)))
    (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ i j x, x ∈ planeVertex k s L j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ planeVertex k s L i := by
  let := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
    (L.sheaf.restrict (planeTriple s).ι)
  intro i j x hx
  let U := SectionOpens.isoOpen (s i)
  let V := SectionOpens.isoOpen (s j)
  let : IsAffine U.toScheme := haff i
  have hbasic : (X.homOfLE (show U ⊓ V ≤ U from inf_le_left)).opensRange =
      U.toScheme.basicOpen (ratioOn s i j U le_rfl) :=
    pairRestriction_basic s i j U (U ⊓ V) le_rfl inf_le_left rfl
  obtain ⟨d,hd⟩ := chartRes_cross_clearing k L.sheaf U V (planeTriple s)
    (planeTriple_le s i) (planeTriple_le s j) (ratioOn s i j U le_rfl) hbasic x hx
  refine ⟨d,?_⟩
  rw [plane_ratio_weight_restrict k s i j U le_rfl (planeTriple_le s i),← map_pow,← T_nsmul] at hd
  exact hd

end
end MaximalSeshadri.Projective

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlanePairToric
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

lemma planeVertex_le_pair (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) (i j : Fin 3) :
    planeVertex k s L i ≤ planePair k s L i j :=
  chartRes_range_le k L.sheaf (le_inf (planeTriple_le s i) (planeTriple_le s j)) inf_le_left

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

lemma planePair_stable01 (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ z ∈ coneA, ∀ x ∈ planePair k s L 0 1, T (K := K) z • x ∈ planePair k s L 0 1 := by
  let := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
    (L.sheaf.restrict (planeTriple s).ι)
  intro z hz
  apply chartMap_monomial_mem _ _ _ _ _ _ (planeX s) (planeY s) z
  let U := SectionOpens.isoOpen (s 0) ⊓ SectionOpens.isoOpen (s 1)
  let h := le_inf (planeTriple_le s 0) (planeTriple_le s 1)
  let f := X.homOfLE h
  let u := ratioUnitOn s 0 1 U inf_le_left inf_le_right
  let v := ratioOn s 0 2 U inf_le_left
  refine ⟨↑(u ^ z.1) * v ^ z.2.toNat,?_⟩
  apply lift_cone_left _ (planeX s) (planeY s) f.appTop.hom u v _ _ z hz
  · exact ratioUnitOn_restrict s 0 1 inf_le_left inf_le_right h
  · rw [show f.appTop v = ratioOn s 0 2 (planeTriple s) (planeTriple_le s 0) from
      ratioOn_restrict s 0 2 inf_le_left h]
    exact (ratioUnitOn_val s 0 2 _ _ _).symm

lemma planePair_stable02 (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ z ∈ coneB, ∀ x ∈ planePair k s L 0 2, T (K := K) z • x ∈ planePair k s L 0 2 := by
  let := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
    (L.sheaf.restrict (planeTriple s).ι)
  intro z hz
  apply chartMap_monomial_mem _ _ _ _ _ _ (planeX s) (planeY s) z
  let U := SectionOpens.isoOpen (s 0) ⊓ SectionOpens.isoOpen (s 2)
  let h := le_inf (planeTriple_le s 0) (planeTriple_le s 2)
  let f := X.homOfLE h
  let u := ratioOn s 0 1 U inf_le_left
  let v := ratioUnitOn s 0 2 U inf_le_left inf_le_right
  refine ⟨u ^ z.1.toNat * ↑(v ^ z.2),?_⟩
  apply lift_cone_right _ (planeX s) (planeY s) f.appTop.hom u v _ _ z hz
  · rw [show f.appTop u = ratioOn s 0 1 (planeTriple s) (planeTriple_le s 0) from
      ratioOn_restrict s 0 1 inf_le_left h]
    exact (ratioUnitOn_val s 0 1 _ _ _).symm
  · exact ratioUnitOn_restrict s 0 2 inf_le_left inf_le_right h

lemma planePair_stable12 (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ z ∈ coneC 0, ∀ x ∈ planePair k s L 1 2, T (K := K) z • x ∈ planePair k s L 1 2 := by
  let := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
    (L.sheaf.restrict (planeTriple s).ι)
  intro z hz
  apply chartMap_monomial_mem _ _ _ _ _ _ (planeX s) (planeY s) z
  let U := SectionOpens.isoOpen (s 1) ⊓ SectionOpens.isoOpen (s 2)
  let h := le_inf (planeTriple_le s 1) (planeTriple_le s 2)
  let f := X.homOfLE h
  let u := ratioUnitOn s 2 1 U inf_le_right inf_le_left
  let v := ratioOn s 2 0 U inf_le_right
  refine ⟨↑(u ^ z.1) * v ^ (-(z.1 + z.2)).toNat,?_⟩
  apply lift_cone_top _ (planeX s) (planeY s) f.appTop.hom u v _ _ z hz
  · rw [show Units.map f.appTop.hom u = ratioUnitOn s 2 1 (planeTriple s)
      (planeTriple_le s 2) (planeTriple_le s 1) from ratioUnitOn_restrict s 2 1 inf_le_right inf_le_left h]
    exact planeThird_unit s
  · rw [show f.appTop v = ratioOn s 2 0 (planeTriple s) (planeTriple_le s 2) from
      ratioOn_restrict s 2 0 inf_le_right h]
    rw [← ratioUnitOn_val s 2 0 (planeTriple s) (planeTriple_le s 2) (planeTriple_le s 0),ratioUnitOn_symm]
    rfl

end
end MaximalSeshadri.Projective

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneH1Finite
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

theorem finite_plane_H1_s01_oai (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    Module.Finite K ((cycles (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)) ⧸
      vertexBoundaries (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)
        (planeVertex k s L)) := by
  classical
  let W := planeTriple s
  let := laurentModule (W.ι.appTop.hom.comp k) (planeX s) (planeY s) (L.sheaf.restrict W.ι)
  let := laurentTower (W.ι.appTop.hom.comp k) (planeX s) (planeY s) (L.sheaf.restrict W.ι)
  have haff i := (finite_sectionsMorphism_chart k s hs i).1
  choose d g hgen using fun i => planeVertex_finite_generators_s01 k s hs L i
  have genA : planePair k s L 0 1 = monomialSpan (K := K) coneA (g 0) := by
    apply localized_span (vertexCone 0) coneA (g 0) _
      (fun a => planeVertex_le_pair k s L 0 1 ((hgen 0).1 a)) (planePair_stable01 k s L)
    intro x hx
    obtain ⟨n,hn⟩ := planePair_clearing k s haff L 0 1 x hx
    refine ⟨n • (weight 1-weight 0),?_,?_⟩
    · rw [← (hgen 0).2]; exact hn
    · intro w hw
      have hw' : 0 ≤ w.2 := hw.1
      change 0 ≤ (-(n • (weight 1-weight 0))+w).2
      simpa [weight] using hw'
  have genB : planePair k s L 0 2 = monomialSpan (K := K) coneB (g 0) := by
    apply localized_span (vertexCone 0) coneB (g 0) _
      (fun a => planeVertex_le_pair k s L 0 2 ((hgen 0).1 a)) (planePair_stable02 k s L)
    intro x hx
    obtain ⟨n,hn⟩ := planePair_clearing k s haff L 0 2 x hx
    refine ⟨n • (weight 2-weight 0),?_,?_⟩
    · rw [← (hgen 0).2]; exact hn
    · intro w hw
      have hw' : 0 ≤ w.1 := hw.2
      change 0 ≤ (-(n • (weight 2-weight 0))+w).1
      simpa [weight] using hw'
  have genC : planePair k s L 1 2 = monomialSpan (K := K) (coneC 0) (g 1) := by
    apply localized_span (vertexCone 1) (coneC 0) (g 1) _
      (fun a => planeVertex_le_pair k s L 1 2 ((hgen 1).1 a)) (planePair_stable12 k s L)
    intro x hx
    obtain ⟨n,hn⟩ := planePair_clearing k s haff L 1 2 x hx
    refine ⟨n • (weight 2-weight 1),?_,?_⟩
    · rw [← (hgen 1).2]; exact hn
    · intro w hw
      have hw' : w.1+w.2 ≤ 0 := hw.2
      change (-(n • (weight 2-weight 1))+w).1 + (-(n • (weight 2-weight 1))+w).2 ≤ 0
      simp only [Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg,Prod.smul_fst,Prod.smul_snd]
      simp [weight] at ⊢
      omega
  exact toric_H1_finite_s01 (planeVertex k s L) (planeVertex_stable k s L) g (fun i a => (hgen i).1 a)
    (planeVertex_cross_clearing k s haff L) _ _ _ (planePair_stable01 k s L)
    (planePair_stable02 k s L) (planePair_stable12 k s L)
    (planeVertex_le_pair k s L 0 1) (planeVertex_le_pair k s L 0 2) (planeVertex_le_pair k s L 1 2)
    genA genB genC

end
end MaximalSeshadri.Projective

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Projective.finite_plane_H1_s01_oai := @OAI.MaximalSeshadri.Projective.finite_plane_H1_s01_oai
