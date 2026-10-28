-- Prove2me | solution 1 for OAI.PiExponent.CurveNormalizationMorphism.exists_intrinsic_normalization_morphism_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:19:22.309398+00:00
-- url     : https://prove2.me/submissions/6611141e-237c-46ee-9e13-938c6d80f9a2

import Mathlib
import Definitions.Def_OAIQ068A038

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveStalkGluing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveStalkGluing

universe u

variable {X Y S : Scheme.{u}} [IsIntegral X]

theorem isDominant_fromSpecFunctionField :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure X]
  apply closure_mono
  rw [Set.singleton_subset_iff]
  exact ⟨IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)), by simp⟩


theorem overlap_eq (sX : X ⟶ S) (sY : Y ⟶ S) [IsSeparated sY]
    (η : Spec X.functionField ⟶ Y) (U V : X.Opens)
    (hU : genericPoint X ∈ U) (hV : genericPoint X ∈ V)
    (f : U.toScheme ⟶ Y) (g : V.toScheme ⟶ Y)
    (hf : f ≫ sY = U.ι ≫ sX) (hg : g ≫ sY = V.ι ≫ sX)
    (hfη : U.fromSpecStalkOfMem (genericPoint X) hU ≫ f = η)
    (hgη : V.fromSpecStalkOfMem (genericPoint X) hV ≫ g = η) :
    pullback.fst U.ι V.ι ≫ f = pullback.snd U.ι V.ι ≫ g := by
  let a := U.fromSpecStalkOfMem (genericPoint X) hU
  let b := V.fromSpecStalkOfMem (genericPoint X) hV
  have hab : a ≫ U.ι = b ≫ V.ι := by simp [a, b]
  let k : Spec X.functionField ⟶ pullback U.ι V.ι := pullback.lift a b hab
  let q : pullback U.ι V.ι ⟶ X := pullback.fst U.ι V.ι ≫ U.ι
  have hkq : k ≫ q = X.fromSpecStalk (genericPoint X) := by
    dsimp only [k, q]
    rw [← Category.assoc, pullback.lift_fst]
    exact Scheme.Opens.fromSpecStalkOfMem_ι U _ hU
  have : IsReduced (pullback U.ι V.ι) := isReduced_of_isOpenImmersion q
  have : IsDominant (k ≫ q) := by
    rw [hkq]
    exact isDominant_fromSpecFunctionField
  have : IsDominant k := IsDominant.of_comp_of_isOpenImmersion k q
  have hover : (pullback.fst U.ι V.ι ≫ f) ≫ sY =
      (pullback.snd U.ι V.ι ≫ g) ≫ sY := by
    rw [Category.assoc, hf, Category.assoc, hg]
    exact pullback.condition_assoc (f := U.ι) (g := V.ι) sX
  have hgeneric : k ≫ (pullback.fst U.ι V.ι ≫ f) =
      k ≫ (pullback.snd U.ι V.ι ≫ g) := by
    dsimp only [k]
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    exact hfη.trans hgη.symm
  exact ext_of_isDominant_of_isSeparated sY hover k hgeneric


theorem exists_morphism_of_stalk_maps
    (sX : X ⟶ S) (sY : Y ⟶ S) [LocallyOfFiniteType sY] [IsSeparated sY]
    (η : Spec X.functionField ⟶ Y)
    (H : ∀ x : X, ∃ φ : Spec (X.presheaf.stalk x) ⟶ Y,
      φ ≫ sY = X.fromSpecStalk x ≫ sX ∧
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ φ = η) :
    ∃ g : X ⟶ Y, g ≫ sY = sX ∧ X.fromSpecStalk (genericPoint X) ≫ g = η := by
  classical
  choose φ hφover hφη using H
  have hspread (x : X) :=
    spread_out_of_isGermInjective' sX sY (φ x) (hφover x)
  choose U hx f hφ hf using hspread
  have hgen (x : X) : genericPoint X ∈ U x := genericPoint_mem (U x) x (hx x)
  have hfη (x : X) : (U x).fromSpecStalkOfMem (genericPoint X) (hgen x) ≫ f x = η := by
    rw [← specMap_stalkFunctionField_fromSpecStalkOfMem (U x) x (hx x),
      Category.assoc, ← hφ x]
    exact hφη x
  have hcover : IsOpenCover U := by
    change (⨆ x, U x) = ⊤
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  let 𝒰 := X.openCoverOfIsOpenCover U hcover
  have hcompat (x y : X) :
      pullback.fst (U x).ι (U y).ι ≫ f x =
        pullback.snd (U x).ι (U y).ι ≫ f y :=
    overlap_eq sX sY η (U x) (U y) (hgen x) (hgen y)
      (f x) (f y) (hf x) (hf y) (hfη x) (hfη y)
  let g : X ⟶ Y := 𝒰.glueMorphisms f hcompat
  have hg (x : X) : (U x).ι ≫ g = f x := 𝒰.ι_glueMorphisms f hcompat x
  refine ⟨g, ?_, ?_⟩
  · apply 𝒰.hom_ext
    intro x
    change X at x
    change (U x).ι ≫ g ≫ sY = (U x).ι ≫ sX
    rw [← Category.assoc, hg, hf]
  · let x : X := genericPoint X
    rw [← Scheme.Opens.fromSpecStalkOfMem_ι (U x) (genericPoint X) (hgen x),
      Category.assoc, hg]
    exact hfη x

end PiExponent.CurveStalkGluing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_BirationalOpenIso
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BirationalOpenIso
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem exists_open_iso_of_generic_inverse (f : Y ⟶ X)
    [LocallyOfFiniteType f] [IsSeparated f]
    (e : Y.functionField ≃+* X.functionField)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y) ≫ f = X.fromSpecStalk (genericPoint X)) :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (f ∣_ U) := by
  let η : Spec X.functionField ⟶ Y :=
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y)
  have hηf : η ≫ f = X.fromSpecStalk (genericPoint X) ≫ 𝟙 X := by
    simpa only [η, Category.assoc, Category.comp_id] using! he
  obtain ⟨U, hU, g, hη, hg⟩ := spread_out_of_isGermInjective' (𝟙 X) f η hηf
  simp only [Category.comp_id] at hg
  let V : Y.Opens := f ⁻¹ᵁ U
  have hrange : Set.range g ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨g x, ?_⟩, rfl⟩
    change f (g x) ∈ U
    have hpoint := congrArg (fun k : U.toScheme ⟶ X => k x) hg
    change f (g x) = x.1 at hpoint
    rw [hpoint]
    exact x.2
  let s : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι g hrange
  have hs : s ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hsr : s ≫ (f ∣_ U) = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hs, hg, Category.id_comp]
  let : IsDominant (Y.fromSpecStalk (genericPoint Y)) :=
    CurveStalkGluing.isDominant_fromSpecFunctionField
  have hηdom : IsDominant η := by
    let : IsIso (CommRingCat.ofHom e.toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr e.bijective
    dsimp only [η]
    infer_instance
  have : IsDominant (U.fromSpecStalkOfMem (genericPoint X) hU ≫ g) := by
    rw [← hη]
    exact hηdom
  have : IsDominant g := IsDominant.of_comp (U.fromSpecStalkOfMem (genericPoint X) hU) g
  have : IsDominant (s ≫ V.ι) := by rw [hs]; infer_instance
  have : IsDominant s := IsDominant.of_comp_of_isOpenImmersion s V.ι
  have hbase : ((f ∣_ U) ≫ s) ≫ (f ∣_ U) = (𝟙 V.toScheme) ≫ (f ∣_ U) := by
    rw [Category.assoc, hsr, Category.comp_id, Category.id_comp]
  have hdense : s ≫ ((f ∣_ U) ≫ s) = s ≫ 𝟙 V.toScheme := by
    rw [← Category.assoc, hsr, Category.id_comp, Category.comp_id]
  have hrs : (f ∣_ U) ≫ s = 𝟙 V.toScheme :=
    ext_of_isDominant_of_isSeparated (f ∣_ U) hbase s hdense
  exact ⟨U, hU, ⟨⟨s, hrs, hsr⟩⟩⟩

end PiExponent.BirationalOpenIso

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveModelGenericPoint
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.parameterChart_noetherian _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurve_isSeparated _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurve_noetherian _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
open scoped Polynomial
open PiExponent.CurveZeroPole
universe u

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

theorem parameterChartConstantMap_toField :
    (algebraMap (parameterChart f hf) E).comp (parameterChartConstantMap f hf) =
      algebraMap F E := by
  let := parameterPolynomialAlgebra f hf
  apply RingHom.ext
  intro c
  change algebraMap F[X] E (Polynomial.C c) = algebraMap F E c
  rw [parameterPolynomialAlgebra_map]
  simp

variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]

@[reassoc] theorem parameterCurveGenericPoint_over_base :
    parameterCurveGenericPoint f hf ≫ parameterCurveStructureMap f hf =
      Spec.map (CommRingCat.ofHom (algebraMap F E)) := by
  rw [parameterCurveGenericPoint_eq_zeroChart, Category.assoc,
    zeroChart_structureMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact parameterChartConstantMap_toField f hf

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveProperExtension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveProperExtension
open AlgebraicGeometry CategoryTheory

theorem fractionMap_fromSpecStalk
    (X : Scheme.{u}) [IsIntegral X] (x : X) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) := by
  change Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) ≫
    X.fromSpecStalk x = _
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _

theorem exists_stalk_map
    {X Y S : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (η : Spec X.functionField ⟶ Y)
    (hη : η ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX) (x : X) :
    ∃ φ : Spec (X.presheaf.stalk x) ⟶ Y,
      φ ≫ sY = X.fromSpecStalk x ≫ sX ∧
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ φ = η := by
  by_cases hx : x = genericPoint X
  · subst x
    refine ⟨η, hη, ?_⟩
    change Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) ≫ η = η
    simp
  · let := hDVR x hx
    have hval : ValuativeCriterion sY := by
      have h : IsProper sY := inferInstance
      rw [IsProper.eq_valuativeCriterion] at h
      exact h.1.1.1
    let sq : ValuativeCommSq sY :=
      { R := X.presheaf.stalk x
        commRing := inferInstanceAs (CommRing (X.presheaf.stalk x))
        domain := inferInstanceAs (IsDomain (X.presheaf.stalk x))
        valuationRing := inferInstanceAs (ValuationRing (X.presheaf.stalk x))
        K := X.functionField
        field := inferInstanceAs (Field X.functionField)
        algebra := inferInstanceAs (Algebra (X.presheaf.stalk x) X.functionField)
        isFractionRing := inferInstanceAs (IsFractionRing (X.presheaf.stalk x) X.functionField)
        i₁ := η
        i₂ := X.fromSpecStalk x ≫ sX
        commSq := ⟨by
          rw [hη]
          exact (congrArg (fun g => g ≫ sX) (fractionMap_fromSpecStalk X x)).symm.trans
            (Category.assoc _ _ _)⟩ }
    obtain ⟨φ, hφ, hbase⟩ := (hval.existence sq).exists_lift
    exact ⟨φ, hbase, hφ⟩

end PiExponent.CurveProperExtension

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveGlobalMonomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurve_isSeparated _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurve_noetherian _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveGlobalMonomial
open AlgebraicGeometry CategoryTheory
open CurveNormalizationModel CurveProperExtension CurveMonomialMap WeightedCompactification

theorem exists_extension
    {X Y S : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (η : Spec X.functionField ⟶ Y)
    (hη : η ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX) :
    ∃ g : X ⟶ Y, g ≫ sY = sX ∧ X.fromSpecStalk (genericPoint X) ≫ g = η :=
  CurveStalkGluing.exists_morphism_of_stalk_maps sX sY η
    (exists_stalk_map sX sY hDVR η hη)

theorem exists_parameterCurve_extension
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of F)) [IsProper sY]
    (ηE : Spec (CommRingCat.of E) ⟶ Y)
    (hηE : ηE ≫ sY = Spec.map (CommRingCat.ofHom (algebraMap F E))) :
    ∃ g : parameterCurve f hf ⟶ Y,
      g ≫ sY = parameterCurveStructureMap f hf ∧ parameterCurveGenericPoint f hf ≫ g = ηE := by
  let e := parameterCurveFunctionFieldEquiv f hf
  let eSpec : Spec (CommRingCat.of E) ≅ Spec (parameterCurve f hf).functionField :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op
  let η := eSpec.inv ≫ ηE
  have hη : η ≫ sY = (parameterCurve f hf).fromSpecStalk
      (genericPoint (parameterCurve f hf)) ≫ parameterCurveStructureMap f hf := by
    apply (cancel_epi eSpec.hom).mp
    change eSpec.hom ≫ (eSpec.inv ≫ ηE) ≫ sY = _
    rw [← Category.assoc, eSpec.hom_inv_id_assoc, hηE]
    exact (parameterCurveGenericPoint_over_base f hf).symm
  obtain ⟨g, hbase, hgeneric⟩ := exists_extension (parameterCurveStructureMap f hf) sY
    (parameterCurve_stalkDVR f hf) η hη
  refine ⟨g, hbase, ?_⟩
  change (eSpec.hom ≫ (parameterCurve f hf).fromSpecStalk
    (genericPoint (parameterCurve f hf))) ≫ g = ηE
  rw [Category.assoc, hgeneric]
  exact eSpec.hom_inv_id_assoc ηE

end PiExponent.CurveGlobalMonomial

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveMorphismFinite
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveMorphismFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
universe u

attribute [local instance] specializationOrder

theorem finite_closed_avoiding_genericPoint (X : Scheme.{u}) [IsIntegral X]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
    {Z : Set X} (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) : Z.Finite := by
  obtain ⟨S, hS, hclosed, hirr, hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hcover]
  apply hS.sUnion
  intro C hC
  obtain ⟨x, hx⟩ := QuasiSober.sober (hirr C hC) (hclosed C hC)
  have hxne : x ≠ genericPoint X := by
    intro heq
    apply hη
    rw [hcover, ← heq]
    exact mem_sUnion.mpr ⟨C, hC, hx.mem⟩
  have hxc := isClosed_singleton_of_ne_genericPoint X hdim x hxne
  have heq : C = {x} := hx.def.symm.trans hxc.closure_eq
  rw [heq]
  exact finite_singleton x

theorem finite_fibers {X Y : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    [Nontrivial Y] (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim X ≤ 1) (y : Y) : (f ⁻¹' {y}).Finite := by
  by_cases hy : IsClosed ({y} : Set Y)
  · have hZ : IsClosed (f ⁻¹' {y}) := hy.preimage f.continuous
    apply finite_closed_avoiding_genericPoint X hdim hZ
    intro hη
    have hall : (Set.univ : Set X) ⊆ f ⁻¹' {y} :=
      ((genericPoint_spec X).mem_closed_set_iff hZ).mp hη
    obtain ⟨z, hz⟩ := exists_ne y
    obtain ⟨x, hx⟩ := f.surjective z
    apply hz
    have hh := hall (show x ∈ (Set.univ : Set X) from trivial)
    change f x = y at hh
    exact hx.symm.trans hh
  · apply (finite_singleton (genericPoint X)).subset
    intro x hx
    change f x = y at hx
    by_cases hxe : x = genericPoint X
    · exact hxe
    · exfalso
      apply hy
      have hclosed := f.isClosedMap {x} (isClosed_singleton_of_ne_genericPoint X hdim x hxe)
      simpa only [Set.image_singleton, hx] using hclosed

theorem isFinite_of_proper_dominant {X Y : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    [Nontrivial Y] (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim X ≤ 1) : IsFinite f := by
  let : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f (finite_fibers f hdim)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end PiExponent.CurveMorphismFinite

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationMorphism
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurve_isSeparated _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveNormalizationMorphism
open AlgebraicGeometry CategoryTheory
open CurveNormalizationModel

theorem genericPoint_over_structure
    {F : Type u} [Field F] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) :
    letI := structureFieldAlgebra p
    X.fromSpecStalk (genericPoint X) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap F X.functionField)) := by
  let := structureFieldAlgebra p
  exact (Spec.map_preimage _).symm

theorem isDominant_of_generic_identity
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) (e : Y.functionField ≃+* X.functionField)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y) ≫ g = X.fromSpecStalk (genericPoint X)) :
    IsDominant g := by
  have : IsDominant ((Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y)) ≫ g) := by
    rw [Category.assoc, he]
    exact CurveStalkGluing.isDominant_fromSpecFunctionField
  exact IsDominant.of_comp (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Y.fromSpecStalk (genericPoint Y)) g

theorem nontrivial_of_dimension_one (X : Scheme.{u})
    (hdim : topologicalKrullDim X = 1) : Nontrivial X := by
  classical
  by_contra h
  have : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
  have hzero := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at hzero
  norm_num at hzero

theorem exists_model_morphism
    {F : Type u} [Field F] [CharZero F]
    {X : Scheme.{u}} [IsIntegral X] [Algebra F X.functionField]
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (hp : X.fromSpecStalk (genericPoint X) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap F X.functionField)))
    (f : X.functionField) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) X.functionField] :
    ∃ g : parameterCurve f hf ⟶ X,
      g ≫ p = parameterCurveStructureMap f hf ∧
      parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
      IsProper g ∧ IsDominant g := by
  obtain ⟨g, hover, hgeneric⟩ := CurveGlobalMonomial.exists_parameterCurve_extension
    f hf p (X.fromSpecStalk (genericPoint X)) hp
  have : IsProper (g ≫ p) := by
    rw [hover]
    infer_instance
  have : IsProper g := IsProper.of_comp g p
  have : IsDominant g := isDominant_of_generic_identity g
    (parameterCurveFunctionFieldEquiv f hf) (by
      simpa only [parameterCurveGenericPoint, Category.assoc] using hgeneric)
  exact ⟨g, hover, hgeneric, inferInstance, inferInstance⟩

theorem exists_finite_model_morphism
    {F : Type u} [Field F] [CharZero F]
    {X : Scheme.{u}} [IsIntegral X] [Nontrivial X] [Algebra F X.functionField]
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (hp : X.fromSpecStalk (genericPoint X) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap F X.functionField)))
    (f : X.functionField) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) X.functionField] :
    ∃ g : parameterCurve f hf ⟶ X,
      g ≫ p = parameterCurveStructureMap f hf ∧
      parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
      IsFinite g ∧ ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (g ∣_ U) := by
  obtain ⟨g, hover, hgeneric, hproper, hdominant⟩ := exists_model_morphism p hp f hf
  have : IsProper g := hproper
  have : IsDominant g := hdominant
  have hfinite : IsFinite g := CurveMorphismFinite.isFinite_of_proper_dominant g
    (parameterCurve_dimension_le_one f hf)
  obtain ⟨U, hU, hUiso⟩ := BirationalOpenIso.exists_open_iso_of_generic_inverse g
    (parameterCurveFunctionFieldEquiv f hf) (by
      simpa only [parameterCurveGenericPoint, Category.assoc] using hgeneric)
  exact ⟨g, hover, hgeneric, hfinite, U, hU, hUiso⟩

theorem exists_intrinsic_normalization_morphism_q68_oai
    {F : Type u} [Field F] [CharZero F]
    {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (hdim : topologicalKrullDim X = 1) :
    letI := structureFieldAlgebra p
    ∀ (f : X.functionField) (hf : Transcendental F f),
      ∀ [FiniteDimensional (IntermediateField.adjoin F {f}) X.functionField],
      ∃ g : parameterCurve f hf ⟶ X,
        g ≫ p = parameterCurveStructureMap f hf ∧
        parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
        IsFinite g ∧ ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (g ∣_ U) := by
  let := structureFieldAlgebra p
  intro f hf hfinite
  have : Nontrivial X := nontrivial_of_dimension_one X hdim
  exact exists_finite_model_morphism p (genericPoint_over_structure p) f hf

end PiExponent.CurveNormalizationMorphism

end

end OAI
end

theorem solution.{u} : type_of% @OAI.PiExponent.CurveNormalizationMorphism.exists_intrinsic_normalization_morphism_q68_oai.{u} := @OAI.PiExponent.CurveNormalizationMorphism.exists_intrinsic_normalization_morphism_q68_oai.{u}
