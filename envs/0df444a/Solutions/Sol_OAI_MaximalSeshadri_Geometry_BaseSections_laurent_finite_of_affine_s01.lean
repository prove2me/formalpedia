-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.BaseSections.laurent_finite_of_affine_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:03.577223+00:00
-- url     : https://prove2.me/submissions/82ad1ea0-982b-467c-80f9-827093a06ba0

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES005

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentPlane
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.LaurentPlane
noncomputable section

theorem finite_of_clearing {P R N M : Type*} [CommRing P] [CommRing R]
    [AddCommGroup N] [AddCommGroup M] [Module P N] [Module R M]
    [Module.Finite P N] (e : P →+* R) (f : N →+ M)
    (hf : ∀ p n, f (p • n) = e p • f n)
    (hclear : ∀ m : M, ∃ r : R, ∃ n : N, m = r • f n) : Module.Finite R M := by
  classical
  obtain ⟨d,s,hs⟩ := Module.Finite.exists_fin (R := P) (M := N)
  let V := Submodule.span R (Set.range (fun i => f (s i)))
  have image (n : N) : f n ∈ V := by
    have hn : n ∈ Submodule.span P (Set.range s) := hs ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem n hn =>
      obtain ⟨i,rfl⟩ := hn
      exact Submodule.subset_span ⟨i,rfl⟩
    | zero => simp
    | add n m hn hm ih ih' => simpa only [map_add] using V.add_mem ih ih'
    | smul p n hn ih => rw [hf]; exact V.smul_mem (e p) ih
  have hV : V = ⊤ := by
    apply top_unique
    intro m hm
    obtain ⟨r,n,rfl⟩ := hclear m
    exact V.smul_mem r (image n)
  exact Module.Finite.of_fg_top (hV ▸ Submodule.fg_span (Set.finite_range _))

end
end MaximalSeshadri.LaurentPlane

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_AffineLineFinite
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
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
  let (r : t) : Algebra R Γ(Spec R, PrimeSpectrum.basicOpen r.val) :=
    inferInstanceAs <| Algebra R
      ((Spec.structureSheaf R).presheaf.obj (op (PrimeSpectrum.basicOpen r.val)))
  have (r : t) : IsLocalization.Away r.val Γ(Spec R, PrimeSpectrum.basicOpen r.val) :=
    inferInstanceAs <| IsLocalization.Away r.val
      ((Spec.structureSheaf R).presheaf.obj (op (PrimeSpectrum.basicOpen r.val)))
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
-- module Solutions.Q223_SES.Seshadri_Geometry_AffineBundleFinite
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
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
-- module Solutions.Q223_SES.Seshadri_Geometry_PlaneChartAlgebra
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.LaurentPlane
noncomputable section
variable {K A R : Type*} [CommRing K] [CommRing A] [CommRing R]

theorem finite_laurent_of_chart {P N M : Type*} [CommRing P]
    [AddCommGroup N] [AddCommGroup M] [Module P N] [Module R M]
    [Module.Finite P N] (k : K →+* R) (u v : Rˣ)
    (e : P →+* Ring K) (F : N →+ M)
    (hF : ∀ p n, F (p • n) = eval k u v (e p) • F n)
    (hclear : ∀ m : M, ∃ d : ℕ, ∃ n : N, (↑u * ↑v : R)^d • m = F n) :
    letI := Module.compHom M (eval k u v)
    Module.Finite (Ring K) M := by
  let := Module.compHom M (eval k u v)
  apply finite_of_clearing e F hF
  intro m
  obtain ⟨d,n,hn⟩ := hclear m
  refine ⟨T (-(d : ℤ),-(d : ℤ)),n,?_⟩
  change m = eval k u v (T (-(d : ℤ),-(d : ℤ))) • F n
  rw [eval_T, ← hn, ← mul_smul]
  have he : ↑(u ^ (-(d : ℤ)) * v ^ (-(d : ℤ))) * (↑u * ↑v : R)^d = 1 := by
    rw [← Units.val_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    suffices u ^ (-(d : ℤ)) * v ^ (-(d : ℤ)) * (u * v)^d = 1 by
      exact congrArg Units.val this
    rw [← mul_zpow, zpow_neg, zpow_natCast]
    exact inv_mul_cancel _
  rw [he, one_smul]

end
end MaximalSeshadri.LaurentPlane

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_AffineLocalizing
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono
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

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_RestrictionLocalization
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono
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
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono
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
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono
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

theorem laurent_finite_of_affine_s01_oai [IsAffine X] {P : Type} [CommRing P]
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (L : LineBundle X) {N : Y.Modules} (d : L.sheaf.restrict f ≅ N)
    (a b : Γ(X,⊤)) (hopen : f.opensRange = X.basicOpen (a*b))
    (u v : Γ(Y,⊤)ˣ) (hu : f.appTop a = u) (hv : f.appTop b = v)
    (p : P →+* Γ(X,⊤)) (hp : p.Finite) (e : P →+* LaurentPlane.Ring K)
    (he : f.appTop.hom.comp p = (LaurentPlane.eval kY u v).comp e) :
    letI := laurentModule kY u v N
    Module.Finite (LaurentPlane.Ring K) (Sections kY N ⊤) := by
  let := laurentModule kY u v N
  let : Algebra P Γ(X,⊤) := p.toAlgebra
  let : Module.Finite P Γ(X,⊤) := hp
  let : Module P (Sections kX L.sheaf ⊤) := Module.compHom _ p
  let : Module.Finite Γ(X,⊤) (Sections kX L.sheaf ⊤) := L.affine_openSections_finite
  let : IsScalarTower P Γ(X,⊤) (Sections kX L.sheaf ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let : Module.Finite P (Sections kX L.sheaf ⊤) := Module.Finite.trans Γ(X,⊤) _
  let F := chartMap kX kY f hk L.sheaf d
  apply LaurentPlane.finite_laurent_of_chart kY u v e F.toAddMonoidHom
  · intro q m
    change F (p q • m) = _
    rw [chartMap_smul]
    exact congrArg (fun c : Γ(Y,⊤) => c • F m) (RingHom.congr_fun he q)
  · intro m
    obtain ⟨n,z,hz⟩ := chartMap_clearing kX kY f hk L.sheaf d (a*b) hopen m
    refine ⟨n,z,?_⟩
    change (↑u * ↑v : Γ(Y,⊤))^n • m = chartMap kX kY f hk L.sheaf d z
    simpa only [map_mul,hu,hv] using hz.symm

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.BaseSections.laurent_finite_of_affine_s01_oai := @OAI.MaximalSeshadri.Geometry.BaseSections.laurent_finite_of_affine_s01_oai
