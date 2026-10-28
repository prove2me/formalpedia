-- Prove2me | solution 1 for OAI.PiExponent.AffineReesCanonicalRecovery.eventually_comap_bijective_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:43:11.840684+00:00
-- url     : https://prove2.me/submissions/b897a331-408b-404d-b366-98f5ac85260e

import Mathlib
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_ReesSheafCechRecovery_eventually_recovery_and_cohomology_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesPushdown
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ReesFrozenChart.coordinateInv_isIso _root_.OAI.PiExponent.ReesProductPowerSections.chartMorphism_open _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.ReesPushdown

open Polynomial PiExponentSeshadri.ReesGrading

variable {R : Type*} [CommRing R]

theorem ordinaryPowerEquivPiece_apply_coeff (I : Ideal R) (n : ℕ) (a : ↥(I ^ n : Ideal R)) :
    (((ordinaryPowerEquivPiece I n a : piece I n) : reesAlgebra I) : R[X]).coeff n = a.val := by
  simp [ordinaryPowerEquivPiece]

end PiExponent.ReesPushdown

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalRepresentedValue
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}
variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme)

theorem representedSectionsEquiv_apply (n : ℕ)
    (b : freeOpen Y.ringCatSheaf j.opensRange ⟶ (L.pow n).sheaf) :
    (representedSectionsEquiv I f j φ hf L ι hL e n b).val =
      functionsOnOpenEquiv j
        ((idealPowerInclusion L ι n).app j.opensRange
          (freeOpenEquiv Y.ringCatSheaf (L.pow n).sheaf j.opensRange b)) := by
  exact sectionsOnOpenEquiv_apply I f j φ hf L ι hL e n _

end
end PiExponent.ExceptionalAffineChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalChartPullbackValue
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}

theorem functionsOnOpenEquiv_global
    (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j] (s : Γ(Y, ⊤)) :
    functionsOnOpenEquiv j (Y.presheaf.map (homOfLE le_top).op s) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom (j.appTop s) := by
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (j.isoOpensRange.hom.appTop
      (j.opensRange.topIso.inv (Y.presheaf.map (homOfLE le_top).op s))) = _
  have ht : j.opensRange.topIso.inv (Y.presheaf.map (homOfLE le_top).op s) =
      j.opensRange.ι.appTop s := by
    change (Y.presheaf.map (homOfLE le_top).op ≫
      j.opensRange.topIso.inv) s = _
    simp only [Scheme.Opens.topIso_inv]
    erw [← Functor.map_comp, ← op_comp]
    rfl
  rw [ht]
  have hj := congrArg (fun f => f.appTop) j.isoOpensRange_hom_ι
  rw [Scheme.Hom.comp_appTop] at hj
  exact congrArg (fun f => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (f s)) hj

theorem functionsOnOpenEquiv_pullback
    (f : Y ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ)) (r : R) :
    functionsOnOpenEquiv j (Y.presheaf.map (homOfLE le_top).op
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) = φ r := by
  rw [functionsOnOpenEquiv_global]
  have h := congrArg (fun g => g.appTop) hf
  rw [Scheme.Hom.comp_appTop] at h
  have hv := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (g ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) h
  refine hv.trans ?_
  have hn := CategoryTheory.congr_fun
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Spec.map (CommRingCat.ofHom φ)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
    φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) at hn
  exact hn.trans (congrArg φ
    (CategoryTheory.congr_fun (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id r))

end
end PiExponent.ExceptionalAffineChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesSectionInclusion
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.ReesCohomologySetup.instIsNoetherianAffineBlowupOfIsNoetherianRing _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZero _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZeroClass _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesGroup _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSectionInclusion
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

attribute [local instance] OAI.PiExponent.ReesSectionInclusion.chartOpenImmersion
private theorem transported_augmentation (n : ℕ)
    (f : freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n)
    (t : Fin 1 → J) :
    ExceptionalRepresentedTypes.transportSections
      (chartMap I a (tuple_nonempty 0 t)) (exceptionalLineBundle I) n
      (tupleOpen_eq I a 0 t)
      (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
        (exceptionalPower I n) ⊤ (fun _ => le_top) f t) =
    freeOpenMap (affineBlowup I).ringCatSheaf (homOfLE le_top) ≫ f := by
  change (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor (affineBlowup I).ringCatSheaf).map
      (eqToHom (tupleOpen_eq I a 0 t)) ≫
    (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor (affineBlowup I).ringCatSheaf).map
      (homOfLE _) ≫ f = _
  erw [← Category.assoc, ← Functor.map_comp]
  rfl

theorem section_chart_inclusion (n : ℕ)
    (u : freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n)
    (r : R) (hvalue : HasFrozenValues I a n u r) (t : Fin 1 → J) :
    ExceptionalAffineChart.functionsOnOpenEquiv
      (chartMap I a (tuple_nonempty 0 t))
      ((affineBlowup I).presheaf.map (homOfLE le_top).op
        ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
          (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u))) =
      ReesFrozenChart.base I a (tupleSet t) r := by
  have h := hvalue t
  change (ReesFrozenPower.pieceEquiv I a (tuple_mem 0 t 0) n
    (chartHomEquiv I a (tuple_nonempty 0 t) (tuple_mem 0 t 0) n
      (ExceptionalRepresentedTypes.transportSections
        (chartMap I a (tuple_nonempty 0 t)) (exceptionalLineBundle I) n
        (tupleOpen_eq I a 0 t)
        (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
          (exceptionalPower I n) ⊤ (fun _ => le_top)
          (u) t)))).val = _ at h
  rw [chartHomEquiv_pieceEquiv] at h
  erw [ExceptionalRepresentedTypes.representedSectionsTyped_apply,
    ExceptionalAffineChart.representedSectionsEquiv_apply] at h
  erw [transported_augmentation I a n u t] at h
  erw [freeOpenEquiv_naturality] at h
  have hn := CategoryTheory.congr_fun
    ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).mapPresheaf.naturality
      (homOfLE (show (chartMap I a (tuple_nonempty 0 t)).opensRange ≤ ⊤ from le_top)).op)
    (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u)
  change (idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app _
      ((exceptionalPower I n).presheaf.map (homOfLE le_top).op
        (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u)) =
    (affineBlowup I).presheaf.map (homOfLE le_top).op
      ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
        (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u)) at hn
  change ExceptionalAffineChart.functionsOnOpenEquiv _
    ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app _
      ((exceptionalPower I n).presheaf.map (homOfLE le_top).op
        (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u))) = _ at h
  rw [hn] at h
  exact h

theorem section_inclusion
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (u : freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n)
    (r : R) (hvalue : HasFrozenValues I a n u r) :
    (idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
      (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u) =
    (projection I).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
  apply (O (affineBlowup I)).isSheaf.section_ext
  intro x hx
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp ((iSup_opens I a ha).ge (Set.mem_univ x))
  let t : Fin 1 → J := fun _ => j
  have heq : (chartMap I a (tuple_nonempty 0 t)).opensRange = opens I a j := by
    change (ReesFrozenChart.chartOpen I a (tuple_nonempty 0 t)).1 = _
    rw [tupleOpen_eq]
    simp only [CechHigher.intersection, t, iInf_const]
  refine ⟨(chartMap I a (tuple_nonempty 0 t)).opensRange, le_top,
    heq.ge hj, ?_⟩
  apply (ExceptionalAffineChart.functionsOnOpenEquiv
    (chartMap I a (tuple_nonempty 0 t))).injective
  exact (section_chart_inclusion I a n u r hvalue t).trans
    (ExceptionalAffineChart.functionsOnOpenEquiv_pullback (projection I)
      (chartMap I a (tuple_nonempty 0 t))
      (ReesFrozenChart.base I a (tupleSet t))
      (ReesFrozenChart.chart_projection I a (tuple_nonempty 0 t)) r).symm

end
end PiExponent.ReesSectionInclusion

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesProductAugmentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ReesFrozenChart.coordinateInv_isIso _root_.OAI.PiExponent.ReesProductPowerSections.chartMorphism_open _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZero _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZeroClass _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesGroup _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesProductAugmentation
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections PiExponent.ReesProductChart PiExponent.ReesProductPower
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem ordinaryFraction_evaluation (s : Finset J) (n : ℕ) (b : ↥(I ^ n : Ideal R)) :
    pieceEvaluation I a s n (ordinaryFraction I a s n b) =
      algebraMap R (Localization.Away (coefficientProduct I a s)) b.val := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  change localizationEvaluation I a s
    (fraction (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s)
      (ordinaryPowerEquivIntegerPiece I n b).val 0) = _
  rw [localizationEvaluation_fraction, powerDenominator_zero, IsLocalization.mk'_one]
  congr 1
  change evaluation I (ReesPushdown.ordinaryPowerEquivPiece I n b).val = b.val
  rw [evaluation_piece I (ReesPushdown.ordinaryPowerEquivPiece I n b)]
  exact ReesPushdown.ordinaryPowerEquivPiece_apply_coeff I n b

theorem chartPowerMap_ordinaryFraction {s : Finset J} {j : J} (hj : j ∈ s)
    (n : ℕ) (b : ↥(I ^ n : Ideal R)) :
    (chartPowerMap I a hj n (ordinaryFraction I a s n b)).val =
      ReesProductChart.chartBase I a s b.val := by
  apply ReesProductChart.chartMap_injective I a s
  rw [chartPowerMap_evaluation I a hj, ordinaryFraction_evaluation,
    ReesProductChart.chartMap_base]

theorem augmentation_eq_ordinaryFraction (n : ℕ) (b : ↥(I ^ n : Ideal R)) (t : Fin 1 → J) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    augmentation (grading (J := J) (R := R)) (integerPiece I) MvPolynomial.X variable_mem n
      (ordinaryPowerEquivIntegerPiece I n b) t = ordinaryFraction I a (tupleSet t) n b := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply Subtype.ext
  rfl

end
end PiExponent.ReesProductAugmentation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesSheafCechRecovery
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSheafCechRecovery
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase PiExponent.ReesSheafCechNaturality
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance 1001] AddCommGroup.toAddCommMonoid
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem ordinarySectionHom_restriction
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) (t : Fin 1 → J) :
    tupleHomEquiv I a n 0 t
      (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
        (exceptionalPower I n) ⊤ (fun _ => le_top) (ordinarySectionHom I a ha n b) t) =
      ReesProductAugmentation.ordinaryFraction I a (tupleSet t) n b := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  have h := (globalCyclesEquiv I a ha n).apply_symm_apply (ordinaryAugmentation I a n b)
  have hv := congrFun (congrArg Subtype.val h) t
  change _ = GradedCech.augmentation (grading (J := J) (R := R)) (integerPiece I)
    MvPolynomial.X variable_mem n (ordinaryPowerEquivIntegerPiece I n b) t at hv
  exact hv.trans (ReesProductAugmentation.augmentation_eq_ordinaryFraction I a n b t)

theorem ordinarySectionHom_chartValue
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) (t : Fin 1 → J) :
    (ReesProductPower.chartPowerMap I a (tuple_mem 0 t 0) n
      (tupleHomEquiv I a n 0 t
        (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
          (exceptionalPower I n) ⊤ (fun _ => le_top)
          (ordinarySectionHom I a ha n b) t))).val =
      ReesProductChart.chartBase I a (tupleSet t) b.val := by
  rw [ordinarySectionHom_restriction]
  exact ReesProductAugmentation.chartPowerMap_ordinaryFraction I a (tuple_mem 0 t 0) n b

theorem ordinarySectionHom_frozenChartValue
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) (t : Fin 1 → J) :
    (ReesFrozenPower.pieceEquiv I a (tuple_mem 0 t 0) n
      (tupleHomEquiv I a n 0 t
        (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
          (exceptionalPower I n) ⊤ (fun _ => le_top)
          (ordinarySectionHom I a ha n b) t))).val =
      ReesFrozenChart.base I a (tupleSet t) b.val := by
  apply (ReesFrozenChart.coordinateEquiv I a (tupleSet t)).injective
  rw [ReesFrozenPower.coordinate_pieceEquiv, ordinarySectionHom_chartValue]
  exact ((ReesFrozenChart.coordinateEquiv I a (tupleSet t)).apply_symm_apply _).symm

end
end PiExponent.ReesSheafCechRecovery

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesSheafCanonicalValue
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSheafCechRecovery
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem ordinaryGlobalSection_inclusion
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) :
    (idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
      (ordinaryGlobalSection I a ha n b) =
    (projection I).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv b.val) :=
  ReesSectionInclusion.section_inclusion I a ha n
    (ordinarySectionHom I a ha n b) b.val
    (fun t => ordinarySectionHom_frozenChartValue I a ha n b t)

end
end PiExponent.ReesSheafCechRecovery

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealSectionRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.IdealSectionRestriction
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}}

theorem inclusion_injective (I : Y.IdealSheafData) (U : Y.Opens) :
    Function.Injective ((closedInclusion I).app U) := by
  let : Mono (closedInclusion I).val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules Y).map (closedInclusion I)))
  exact PresheafOfModules.injective_of_mono (closedInclusion I).val (op U)

theorem pullback_inclusion (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (s : Γ(closedModule I,U)) :
    (closedInclusion (I.comap f)).app V (pullback f I U V h s) =
      f.appLE U V h ((closedInclusion I).app U s) := by
  have hn := PresheafOfModules.naturality_apply (closedInclusion (I.comap f)).val
    (homOfLE h).op ((GeometrySupport.IdealPullbackMap.comap f I).app U s)
  change (closedInclusion (I.comap f)).app V (pullback f I U V h s) =
    X.presheaf.map (homOfLE h).op
      ((closedInclusion (I.comap f)).app (f ⁻¹ᵁ U)
        ((GeometrySupport.IdealPullbackMap.comap f I).app U s)) at hn
  have he := congrArg (fun g => g.app U s)
    (GeometrySupport.IdealPullbackMap.comap_inclusion f I)
  exact hn.trans (congrArg (X.presheaf.map (homOfLE h).op) he)

theorem pullback_self (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    (U : Y.Opens) :
    pullback f I U (f ⁻¹ᵁ U) le_rfl =
      ((GeometrySupport.IdealPullbackMap.comap f I).app U).hom := by
  ext s
  exact congrArg (fun a => a ((GeometrySupport.IdealPullbackMap.comap f I).app U s))
    ((closedModule (I.comap f)).presheaf.map_id (op (f ⁻¹ᵁ U)))

theorem pullback_bijective_iff_comap (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (he : V = f ⁻¹ᵁ U) :
    Function.Bijective (pullback f I U V h) ↔
      Function.Bijective ((GeometrySupport.IdealPullbackMap.comap f I).app U) := by
  subst V
  rw [pullback_self]
  rfl

end PiExponent.IdealSectionRestriction

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CanonicalAffineRecovery
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CanonicalAffineRecovery
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule PiExponentSeshadri.IdealPullback
open GeometrySupport

private theorem bijective_iff_of_square {A B C D : Type*}
    (p : A → B) (q : C → D) (a : A → C) (b : B → D)
    (ha : Function.Bijective a) (hb : Function.Bijective b)
    (h : ∀ x, b (p x) = q (a x)) : Function.Bijective p ↔ Function.Bijective q := by
  have he : b ∘ p = q ∘ a := funext h
  rw [← hb.of_comp_iff' p, he]
  exact Function.Bijective.of_comp_iff q ha

theorem bijective_iff_comap {R : Type} [CommRing R] {Y : Scheme.{0}}
    (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (L : LineBundle Y) (ι : L.sheaf ⟶ structureSheaf Y)
    (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
    (r : I → Γ(L.sheaf,⊤))
    (hr : ∀ a : I, ι.app ⊤ (r a) =
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a.val)) :
    Function.Bijective r ↔
      Function.Bijective ((IdealPullbackMap.comap f (specIdeal I)).app ⊤) := by
  let t := PresentedIdealIso.toIdealModule (specIdeal I) f L ι hL
  have ht : Function.Bijective (t.app ⊤) := ConcreteCategory.bijective_of_isIso _
  have hdiag (a : I) :
      t.app ⊤ (r a) =
        IdealSectionRestriction.pullback f (specIdeal I) ⊤ ⊤ (by simp)
          ((AffineIdealSections.equiv I).symm a) := by
    apply IdealSectionRestriction.inclusion_injective ((specIdeal I).comap f) ⊤
    have h₁ := congrArg (fun g => g.app ⊤ (r a))
      (PresentedIdealIso.toIdealModule_inclusion (specIdeal I) f L ι hL)
    have h₂ := IdealSectionRestriction.pullback_inclusion f (specIdeal I) ⊤ ⊤
      (by simp) ((AffineIdealSections.equiv I).symm a)
    have htop : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
    rw [htop] at h₂
    have h₃ := AffineIdealSections.equiv_symm_inclusion I a
    exact (h₁.trans (hr a)).trans
      ((congrArg f.appTop h₃).symm.trans h₂.symm)
  exact (bijective_iff_of_square r
    (IdealSectionRestriction.pullback f (specIdeal I) ⊤ ⊤ (by simp))
    (AffineIdealSections.equiv I).symm (t.app ⊤)
    (AffineIdealSections.equiv I).symm.bijective ht hdiag).trans
      (IdealSectionRestriction.pullback_bijective_iff_comap f (specIdeal I) ⊤ ⊤
        (by simp) (by simp))

theorem power_bijective_iff_comap {R : Type} [CommRing R] {Y : Scheme.{0}}
    (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (L : LineBundle Y) (ι : L.sheaf ⟶ structureSheaf Y)
    (hL : PresentsPullbackIdeal (specIdeal I) f L ι) (n : ℕ)
    (r : ↥(I^n : Ideal R) → Γ((L.pow n).sheaf,⊤))
    (hr : ∀ a : ↥(I^n : Ideal R), (idealPowerInclusion L ι n).app ⊤ (r a) =
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a.val)) :
    Function.Bijective r ↔ CanonicalRecoveryProperties.ComapBijective f (specIdeal (I^n)) ⊤ := by
  have hp : PresentsPullbackIdeal (specIdeal (I^n)) f (L.pow n) (idealPowerInclusion L ι n) := by
    rw [specIdeal_pow]
    exact PresentedIdealIso.idealPower_presents (specIdeal I) f L ι hL n
  exact bijective_iff_comap (I^n) f (L.pow n) (idealPowerInclusion L ι n) hp r hr

end PiExponent.CanonicalAffineRecovery

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealFiniteGenerators
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.IdealFiniteGenerators

theorem exists_generators {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : ∃ m : ℕ, ∃ a : Fin m → I,
      Ideal.span (Set.range fun j => (a j).val) = I := by
  obtain ⟨m,b,hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  let a : Fin m → I := fun j => ⟨b j, by
    rw [← hb]
    exact Submodule.subset_span ⟨j,rfl⟩⟩
  exact ⟨m,a,hb⟩

end PiExponent.IdealFiniteGenerators

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AffineReesCanonicalRecovery
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineReesCanonicalRecovery
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.ReesGrading PiExponentSeshadri.IdealPullback
open CanonicalRecoveryProperties
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion
  ReesSheafCechRecovery.ordinaryGlobalSection

theorem eventually_comap_bijective_q68_oai {R : Type} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ComapBijective (projection I) (specIdeal (I^n)) ⊤ := by
  classical
  obtain ⟨m,a,ha⟩ := IdealFiniteGenerators.exists_generators I
  obtain ⟨N,hN⟩ := ReesSheafCechRecovery.eventually_recovery_and_cohomology_q68 I a ha
  refine ⟨N, ?_⟩
  intro n hn
  exact (CanonicalAffineRecovery.power_bijective_iff_comap I (projection I)
    (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I) n
    (ReesSheafCechRecovery.ordinaryGlobalSection I a ha n)
    (ReesSheafCechRecovery.ordinaryGlobalSection_inclusion I a ha n)).mp (hN n hn).1

end PiExponent.AffineReesCanonicalRecovery

end

end OAI
end

theorem solution : type_of% @OAI.PiExponent.AffineReesCanonicalRecovery.eventually_comap_bijective_q68_oai := @OAI.PiExponent.AffineReesCanonicalRecovery.eventually_comap_bijective_q68_oai
