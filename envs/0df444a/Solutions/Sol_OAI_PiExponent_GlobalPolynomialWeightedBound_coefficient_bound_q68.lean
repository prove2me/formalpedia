-- Prove2me | solution 1 for OAI.PiExponent.GlobalPolynomialWeightedBound.coefficient_bound_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:36:35.40598+00:00
-- url     : https://prove2.me/submissions/072c53ea-29cd-41fe-bcf6-3e06c3e6fab6

import Mathlib
import Definitions.Def_OAIQ068A044

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CompositePullbackFrame
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_additive _root_.OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_preservesZero _root_.OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor_additive _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CompositePullbackFrame
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

private theorem mapIso_trans_inv_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B T : C} {U : D} (e : A ≅ B) (u : F.obj B ≅ U)
    (s : A ⟶ T) :
    (F.mapIso e ≪≫ u).inv ≫ F.map s = u.inv ≫ F.map (e.inv ≫ s) := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Functor.map_comp, Category.assoc]

private theorem map_comp_iso_inv {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B T : C} {U : D} (u : U ⟶ F.obj A)
    (s : A ⟶ B) (e : B ≅ T) :
    (u ≫ F.map (s ≫ e.hom)) ≫ (F.mapIso e).inv = u ≫ F.map s := by
  simp only [Functor.mapIso_inv, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id, Category.comp_id]

theorem exists_frame (f : X ⟶ Y) (φ : Z ⟶ X) [IsOpenImmersion φ]
    (V : Y.Opens) (g : Z ⟶ V.toScheme) (h : φ ≫ f = g ≫ V.ι)
    {M : Y.Modules} (e : M.restrict V.ι ≅ O V.toScheme) :
    ∃ E : ((Scheme.Modules.pullback f).obj M).restrict φ ≅ O Z,
      ∀ s : O Y ⟶ M,
        coefficient E (restrictSection φ (pullbackSection f s)) =
          g.appTop (coefficient e (restrictSection V.ι s)) := by
  let F := Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor φ
  let G := Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pullback g
  let v : F ≅ G :=
    Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback φ) ≪≫
    Scheme.Modules.pullbackComp φ f ≪≫
    Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp g V.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm
      (Scheme.Modules.pullback g)
  let uF : F.obj (O Y) ≅ O Z :=
    (Scheme.Modules.restrictFunctor φ).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso φ
  let uG : G.obj (O Y) ≅ O Z :=
    (Scheme.Modules.pullback g).mapIso (Scheme.Modules.restrictUnitIso V.ι) ≪≫
      pullbackUnitIso g
  obtain ⟨E, hE⟩ := PullbackFrameCoefficient.exists_frame_natIso_all F G v uF uG
    (pullbackFrame g e)
  refine ⟨E, fun s => ?_⟩
  have hs : coefficient E (restrictSection φ (pullbackSection f s)) =
      coefficient (pullbackFrame g e) (pullbackSection g (restrictSection V.ι s)) := by
    simp only [restrictSection, pullbackSection]
    exact (congrArg (coefficient E)
      (mapIso_trans_inv_comp (Scheme.Modules.restrictFunctor φ)
        (pullbackUnitIso f) (Scheme.Modules.restrictUnitIso φ)
        ((Scheme.Modules.pullback f).map s)).symm).trans
      ((hE s).trans (congrArg (coefficient (pullbackFrame g e))
        (mapIso_trans_inv_comp (Scheme.Modules.pullback g)
          (Scheme.Modules.restrictUnitIso V.ι) (pullbackUnitIso g)
          ((Scheme.Modules.restrictFunctor V.ι).map s))))
  rw [hs, coefficient_pullback]

theorem exists_power_frame (L : LineBundle Y) (f : X ⟶ Y)
    (φ : Z ⟶ X) [IsOpenImmersion φ] (V : Y.Opens)
    (g : Z ⟶ V.toScheme) (h : φ ≫ f = g ≫ V.ι) (n : ℕ)
    (e : (modulePow Y L.sheaf n).restrict V.ι ≅ O V.toScheme) :
    ∃ E : (modulePow X (L.pullback f).sheaf n).restrict φ ≅ O Z,
      ∀ s : O Y ⟶ modulePow Y L.sheaf n,
        coefficient E (restrictSection φ (pullbackPowerSection L f n s)) =
          g.appTop (coefficient e (restrictSection V.ι s)) := by
  obtain ⟨E, hE⟩ := exists_frame f φ V g h e
  refine ⟨(Scheme.Modules.restrictFunctor φ).mapIso
    (PiExponentSeshadri.PullbackTensor.powIso f L n).symm ≪≫ E, fun s => ?_⟩
  erw [coefficient_transport]
  have hs : restrictSection φ (pullbackPowerSection L f n s) ≫
      ((Scheme.Modules.restrictFunctor φ).mapIso (PiExponentSeshadri.PullbackTensor.powIso f L n).symm).hom =
      restrictSection φ (pullbackSection f s) := by
    simp only [restrictSection, pullbackPowerSection, Functor.mapIso_hom, Iso.symm_hom]
    exact map_comp_iso_inv (Scheme.Modules.restrictFunctor φ)
      (Scheme.Modules.restrictUnitIso φ).inv (pullbackSection f s)
      (PiExponentSeshadri.PullbackTensor.powIso f L n)
  exact (congrArg (coefficient E) hs).trans (hE s)

end PiExponent.CompositePullbackFrame
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedSliceDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedSliceDegree

open scoped BigOperators Pointwise

variable {C E ι σ : Type*} [Field C] [Field E] [Algebra C E]

theorem supportBound_C (ρ : σ → ℝ) (c : E) :
    SupportBound ρ 0 (MvPolynomial.C c) := by
  intro d hd
  have he : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp

theorem SupportBound.mul {ρ : σ → ℝ} {M N : ℝ} {p q : MvPolynomial σ E}
    (hp : SupportBound ρ M p) (hq : SupportBound ρ N q) : SupportBound ρ (M + N) (p * q) := by
  classical
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  simpa only [map_add] using add_le_add (hp a ha) (hq b hb)

end PiExponent.WeightedSliceDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedFrameDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.WeightedFrameDegree
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Frames
open PiExponent.WeightedSliceDegree
variable {K ι : Type} [Field K]

theorem supportBound_unit_mul (ρ : ι → ℝ) (B : ℝ)
    (u p : MvPolynomial ι K) (hu : IsUnit u) (hp : SupportBound ρ B p) :
    SupportBound ρ B (u * p) := by
  obtain ⟨c, _, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  simpa only [zero_add] using (supportBound_C ρ c).mul hp

theorem coefficient_supportBound (ρ : ι → ℝ) (B : ℝ)
    {M : (Spec (CommRingCat.of (MvPolynomial ι K))).Modules}
    (E F : M ≅ O (Spec (CommRingCat.of (MvPolynomial ι K))))
    (s : O (Spec (CommRingCat.of (MvPolynomial ι K))) ⟶ M)
    (h : SupportBound ρ B
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom (coefficient E s))) :
    SupportBound ρ B
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom (coefficient F s)) := by
  rw [coefficient_change E F, map_mul]
  apply supportBound_unit_mul ρ B _ _ ?_ h
  exact (frameChange E F).isUnit.map
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom.hom

end PiExponent.WeightedFrameDegree
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetCoefficientFrame
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetCoefficientFrame
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.AffineJetSupport PiExponent.AffineJetQuotient
variable {X : Scheme}

lemma restrictionSectionsIso_restrict_value {M : X.Modules}
    (s : O X ⟶ M) (U : X.Opens) :
    (restrictionSectionsIso M U).inv (s.app U (1 : Γ(X,U))) =
      (restrictSection U.ι s).app ⊤ (1 : Γ(U.toScheme,⊤)) := by
  have h : (restrictionSectionsIso M U).hom
      ((restrictSection U.ι s).app ⊤ (1 : Γ(U.toScheme,⊤))) =
      s.app U (1 : Γ(X,U)) := openSectionEquiv_restrict s U
  rw [← h]
  exact (restrictionSectionsIso M U).hom_inv_id_apply _

lemma restrictionSectionsIso_unit (U : X.Opens)
    (t : Γ((structureSheaf X).restrict U.ι,⊤)) :
    (restrictionSectionsIso (structureSheaf X) U).hom t =
      U.topIso.hom ((Scheme.Modules.restrictUnitIso U.ι).hom.app ⊤ t) := by
  change U.topIso.hom t = U.topIso.hom ((U.ι.appIso ⊤).hom t)
  rw [U.ι_appIso]
  rfl

theorem globalSectionCoefficient_eq (A : LineBundle X) (n : ℕ) (U : X.affineOpens)
    (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) :
    globalSectionCoefficient A n U e s =
      U.1.topIso.hom (coefficient (untwistPowerFrame A U.1 e n)
        (restrictSection U.1.ι s)) := by
  change (restrictionSectionsIso (structureSheaf X) U.1).hom
      (((moduleTwistRestrictFrame A U.1 e n).app (structureSheaf X)).hom.app ⊤
        ((restrictionSectionsIso ((moduleTwistFunctor A n).obj (structureSheaf X)) U.1).inv
          ((s ≫ (moduleTwistUnitIso A n).inv).app U.1 (1 : Γ(X,U.1))))) =
    U.1.topIso.hom ((Scheme.Modules.restrictUnitIso U.1.ι).hom.app ⊤
      (((moduleTwistRestrictFrame A U.1 e n).app (structureSheaf X)).hom.app ⊤
        ((restrictSection U.1.ι (s ≫ (moduleTwistUnitIso A n).inv)).app ⊤
          (1 : Γ(U.1.toScheme,⊤)))))
  exact (congrArg (fun t => (restrictionSectionsIso (structureSheaf X) U.1).hom
      (((moduleTwistRestrictFrame A U.1 e n).app (structureSheaf X)).hom.app ⊤ t))
    (restrictionSectionsIso_restrict_value (s ≫ (moduleTwistUnitIso A n).inv) U.1)).trans
      (restrictionSectionsIso_unit U.1 _)

open PiExponent.ExceptionalAffineChart PiExponent.AffineJetPolynomial
variable {R : Type} [CommRing R]

theorem polynomialCoefficient_eq (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (A : LineBundle X) (n : ℕ)
    (e : A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) :
    polynomialCoefficient j A n e s =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom
        (coefficient (polynomialPowerFrame j A n e) (restrictSection j s)) := by
  have hframe : coefficient (polynomialPowerFrame j A n e) (restrictSection j s) =
      j.isoOpensRange.hom.appTop (coefficient (untwistPowerFrame A (chartOpen j).1 e n)
        (restrictSection (chartOpen j).1.ι s)) := by
    rw [polynomialPowerFrame, coefficient_transport]
    exact (congrArg (coefficient
      ((Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).app
        (modulePow X A.sheaf n) ≪≫
          restrictFrame j.isoOpensRange.hom (untwistPowerFrame A (chartOpen j).1 e n)))
      (restrictSection_congr j.isoOpensRange_hom_ι.symm s)).trans
        (coefficient_restrict_comp j.isoOpensRange.hom j.opensRange.ι _ s)
  unfold polynomialCoefficient
  rw [globalSectionCoefficient_eq]
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      (j.isoOpensRange.hom.appTop ((chartOpen j).1.topIso.inv
        ((chartOpen j).1.topIso.hom _))) = _
  rw [(chartOpen j).1.topIso.hom_inv_id_apply]
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom hframe.symm

end PiExponent.AffineJetCoefficientFrame
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetCoefficientInterface
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetCoefficientInterface
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.ExceptionalAffineChart
variable {X : Scheme} {R : Type} [CommRing R]
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
variable (A : LineBundle X)

theorem coefficient_eq (n : ℕ) (e : Frame j A) (s : Sections A n) :
    coefficient j A n e s = AffineJetPolynomial.polynomialCoefficient j A n e s := rfl

end PiExponent.AffineJetCoefficientInterface
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GlobalPolynomialCoefficientLaw
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.GlobalPolynomialCoefficientLaw
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_power_frame_of_law {X Y : Scheme.{0}} {A B : Type}
    [CommRing A] [CommRing B] (L : LineBundle Y) (f : X ⟶ Y)
    (φ : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion φ]
    (V : Y.Opens) (g : Spec (CommRingCat.of A) ⟶ V.toScheme)
    (hg : φ ≫ f = g ≫ V.ι) (n : ℕ)
    (e : (modulePow Y L.sheaf n).restrict V.ι ≅ structureSheaf V.toScheme)
    (E : Γ(Y,V) ≃+* B) (P : (structureSheaf Y ⟶ modulePow Y L.sheaf n) → B)
    (hP : CoefficientLaw V e E P) (ev : B →+* A)
    (hev : ∀ q, (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (g.appTop (V.topIso.inv (E.symm q))) = ev q) :
    ∃ F : (modulePow X (L.pullback f).sheaf n).restrict φ ≅ O (Spec (CommRingCat.of A)),
      ∀ s, (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        (coefficient F (restrictSection φ (pullbackPowerSection L f n s))) = ev (P s) := by
  obtain ⟨F, hF⟩ := CompositePullbackFrame.exists_power_frame L f φ V g hg n e
  refine ⟨F, fun s => ?_⟩
  erw [hF s]
  have hcoef : V.topIso.inv (E.symm (P s)) = coefficient e (restrictSection V.ι s) := by
    rw [hP s, RingEquiv.symm_apply_apply]
    exact V.topIso.hom_inv_id_apply _
  rw [← hcoef]
  exact hev (P s)

end PiExponent.GlobalPolynomialCoefficientLaw
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GlobalPolynomialWeightedBound
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.GlobalPolynomialWeightedBound
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedSliceDegree PiExponent.AffineJetCoefficientInterface

theorem coefficient_bound_q68_oai {X Y : Scheme.{0}} {K ι B : Type}
    [Field K] [CommRing B] (L : LineBundle Y) (f : X ⟶ Y)
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (V : Y.Opens) (g : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ V.toScheme)
    (hg : φ ≫ f = g ≫ V.ι) (n : ℕ)
    (e : (modulePow Y L.sheaf n).restrict V.ι ≅ structureSheaf V.toScheme)
    (E : Γ(Y,V) ≃+* B) (P : (structureSheaf Y ⟶ modulePow Y L.sheaf n) → B)
    (hP : GlobalPolynomialCoefficientLaw.CoefficientLaw V e E P)
    (ev : B →+* MvPolynomial ι K)
    (hev : ∀ q, (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom
      (g.appTop (V.topIso.inv (E.symm q))) = ev q)
    (ρ : ι → ℝ) (r : ℝ) (eTarget : Frame φ (L.pullback f)) (s : Sections L n)
    (hbound : SupportBound ρ r (ev (P s))) :
    SupportBound ρ r (AffineJetCoefficientInterface.coefficient φ (L.pullback f) n eTarget
      (pullbackPowerSection L f n s)) := by
  obtain ⟨F, hF⟩ := GlobalPolynomialCoefficientLaw.exists_power_frame_of_law
    L f φ V g hg n e E P hP ev hev
  erw [AffineJetCoefficientInterface.coefficient_eq,
    AffineJetCoefficientFrame.polynomialCoefficient_eq]
  apply WeightedFrameDegree.coefficient_supportBound ρ r F
  exact Eq.mpr (congrArg (SupportBound ρ r) (hF s)) hbound

end PiExponent.GlobalPolynomialWeightedBound
end

end OAI
end

theorem solution : type_of% @OAI.PiExponent.GlobalPolynomialWeightedBound.coefficient_bound_q68_oai := @OAI.PiExponent.GlobalPolynomialWeightedBound.coefficient_bound_q68_oai
