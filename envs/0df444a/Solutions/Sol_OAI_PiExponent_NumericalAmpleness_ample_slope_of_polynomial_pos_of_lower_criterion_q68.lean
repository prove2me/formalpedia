-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.ample_slope_of_polynomial_pos_of_lower_criterion_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:43:12.94371+00:00
-- url     : https://prove2.me/submissions/5a095a62-5cbe-4eb2-b048-dd710cb690d0

import Mathlib
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_curveDegree_pos_of_ample_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_euler_power_dimension_difference_eq_zero_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_exists_power_section_cover_of_euler_growth_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_lineBundle_cohomology_zero_of_dimension_le_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_AmpleCohomologyFinite
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AmpleCohomologyFinite
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{0}}

theorem cohomology_finite_of_ample [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨d, hd, σ, hσ, s, hs, hclosed⟩ := H.ample_projective_sections_noetherian p hH
  let : Fintype σ := hσ
  have : Nonempty σ := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have hx : x ∈ (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
      rw [hs]
      trivial
    obtain ⟨i, -⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  let k : ℂ →+* Γ(X, ⊤) := baseScalars p
  let i : X ⟶ ProjectiveO1.projectiveSpace ℂ σ := sectionsMorphism k s hs
  have : IsClosedImmersion i := hclosed
  have hover : i ≫ polynomialProjectiveProjection ℂ σ = p := by
    rw [← projectiveBase_eq_polynomialProjectiveProjection]
    exact (sectionsMorphism_over k s hs).trans (toSpec_scalarMap p)
  exact ProjectiveFiniteCoordinates.projectiveOver_cohomology_finite p i hover M q

end PiExponent.AmpleCohomologyFinite

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_NumericalMarginRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_additive _root_.OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_preservesZero _root_.OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor_additive _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry

theorem curveDegree_mapClosed {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (i : Y ⟶ X) [IsClosedImmersion i] (C : IntegralCurve Y) :
    curveDegree p L (C.mapClosed i) = curveDegree (i ≫ p) (L.pullback i) C := by
  unfold curveDegree IntegralCurve.mapClosed LineBundle.pullback
  simp only [Category.assoc]
  congr 1
  exact eulerCharacteristic_iso (C.embedding ≫ i ≫ p)
    ((Scheme.Modules.pullbackComp C.embedding i).app L.sheaf).symm 1

theorem uniform_curve_margin_restrict {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L H : LineBundle X) (ε : ℝ)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (i : Y ⟶ X) [IsClosedImmersion i] :
    ∀ C : IntegralCurve Y,
      ε * (curveDegree (i ≫ p) (H.pullback i) C : ℝ) ≤
        (curveDegree (i ≫ p) (L.pullback i) C : ℝ) := by
  intro C
  simpa only [curveDegree_mapClosed] using hmargin (C.mapClosed i)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveDegreeAdditivity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

theorem power_euler [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L : LineBundle X) (n : ℕ) :
    eulerCharacteristic p 1 (L.pow n).sheaf - eulerCharacteristic p 1 (structureSheaf X) =
      (n : ℤ) * (eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X)) := by
  induction n with
  | zero => simp [LineBundle.pow, modulePow, structureSheaf]
  | succ n ih =>
    have he := tensor_euler_add p hd H hH hfinite hH2 L (L.pow n)
    change eulerCharacteristic p 1 (L.pow (n+1)).sheaf -
      eulerCharacteristic p 1 (L.pow n).sheaf = _ at he
    push_cast
    nlinarith

end
end PiExponent.CurveDegree

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem curveDegree_tensor (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L M : LineBundle X) (C : IntegralCurve X)
    (hfinite : CurveDegree.FiniteLineCohomology (C.embedding ≫ p))
    (hH2 : CurveDegree.LineCohomologyTwoZero C.scheme) :
    curveDegree p (L.tensor M) C = curveDegree p L C + curveDegree p M C := by
  have he := CurveDegree.tensor_euler_add (C.embedding ≫ p) C.dimension.le
    (H.pullback C.embedding) (LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding)
    hfinite hH2 (L.pullback C.embedding) (M.pullback C.embedding)
  have hi := eulerCharacteristic_iso (C.embedding ≫ p)
    (PiExponentSeshadri.PullbackTensor.iso C.embedding L M) 1
  unfold curveDegree
  rw [hi]
  change _ - _ = (_ - _) + (_ - _)
  dsimp only [LineBundle.pullback, LineBundle.tensor] at he ⊢
  omega

theorem curveDegree_pow (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (C : IntegralCurve X)
    (hfinite : CurveDegree.FiniteLineCohomology (C.embedding ≫ p))
    (hH2 : CurveDegree.LineCohomologyTwoZero C.scheme) (n : ℕ) :
    curveDegree p (L.pow n) C = (n : ℤ) * curveDegree p L C := by
  have hi := eulerCharacteristic_iso (C.embedding ≫ p)
    (PiExponentSeshadri.PullbackTensor.powIso C.embedding L n) 1
  unfold curveDegree
  rw [hi]
  exact CurveDegree.power_euler (C.embedding ≫ p) C.dimension.le
    (H.pullback C.embedding) (LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding)
    hfinite hH2 (L.pullback C.embedding) n

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleCurveDegreePositive
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveDegree
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem finite_line_cohomology_of_ample [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) : FiniteLineCohomology p := by
  intro M q _
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
  exact AmpleCohomologyFinite.cohomology_finite_of_ample p H hH M.sheaf q

end PiExponent.CurveDegree

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_IntegralCurveExistence
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Order

namespace PiExponent.NumericalAmpleness

noncomputable section

theorem topologicalKrullDim_irreducibleClosed {X : Type*} [TopologicalSpace X]
    (Z : IrreducibleCloseds X) :
    topologicalKrullDim (Z : Set X) = (Order.height Z : WithBot ℕ∞) := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleClosedsBelowEquiv Z),
    ← Order.height_eq_krullDim_Iic]

theorem exists_irreducibleClosed_dimension_one (X : Type*) [TopologicalSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X = d) (hd : 0 < d) :
    ∃ Z : IrreducibleCloseds X, topologicalKrullDim (Z : Set X) = 1 := by
  have hdim' : Order.krullDim (IrreducibleCloseds X) = d := hdim
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp (le_of_eq hdim'.symm)
  have hlast : (p.length : ℕ∞) = Order.height p.last := by
    apply le_antisymm (Order.length_le_height_last (p := p))
    have hh := Order.height_le_krullDim p.last
    rw [hdim', ← hp] at hh
    exact_mod_cast hh
  have hidx : 1 < p.length + 1 := by omega
  refine ⟨p ⟨1, hidx⟩, ?_⟩
  rw [topologicalKrullDim_irreducibleClosed]
  have hh := Order.height_eq_index_of_length_eq_height_last hlast ⟨1, hidx⟩
  simpa using congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hh

theorem nonempty_integralCurve_of_dimension_pos (X : Scheme.{0})
    (d : ℕ) (hdim : topologicalKrullDim X = d) (hd : 0 < d) :
    Nonempty (IntegralCurve X) := by
  obtain ⟨Z, hZ⟩ := exists_irreducibleClosed_dimension_one X d hdim hd
  exact ⟨integralCurveOfIrreducibleClosed Z hZ⟩

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FiniteFromClosedFibers
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.NumericalAmpleness
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
universe u

theorem isFinite_of_proper_finite_closed_fibers {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [JacobsonSpace Y]
    (hfinite : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {y}).Finite) : IsFinite f := by
  have htop : f.quasiFiniteLocus = ⊤ := by
    apply top_unique
    intro x _
    by_contra hx
    have hclosed : IsClosed (f '' ((f.quasiFiniteLocus : Set X)ᶜ)) :=
      f.isClosedMap _ f.quasiFiniteLocus.isOpen.isClosed_compl
    obtain ⟨y, ⟨z, hz, hzy⟩, hy⟩ :=
      nonempty_inter_closedPoints (Z := f '' ((f.quasiFiniteLocus : Set X)ᶜ))
        ⟨f x, x, hx, rfl⟩ hclosed.isLocallyClosed
    have hfin : (f ⁻¹' {f z}).Finite := by rw [hzy]; exact hfinite y hy
    let : Finite (f.fiber (f z)) := (f.fiberHomeo (f z)).finite_iff.mpr hfin
    have hq : f.QuasiFiniteAt z :=
      Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
    exact hz hq
  let : LocallyQuasiFinite f := (Scheme.Hom.quasiFiniteLocus_eq_top_iff f).mp htop
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end PiExponent.NumericalAmpleness

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_FiniteOfNoContractedCurves
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.NumericalAmpleness
open CategoryTheory AlgebraicGeometry TopologicalSpace Set

private theorem positive_dimension_eq_nat {D : WithBot ℕ∞} (d : ℕ)
    (hD : D ≤ d) (hpos : 0 < D) : ∃ n : ℕ, D = n ∧ 0 < n := by
  have hbot : D ≠ ⊥ := by
    intro h
    rw [h] at hpos
    exact not_lt_bot hpos
  obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have he : e ≤ (d : ℕ∞) := by exact_mod_cast hD
  have hetop : e ≠ ⊤ := ne_of_lt (he.trans_lt (by simp))
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hetop
  exact ⟨n, rfl, by exact_mod_cast hpos⟩

theorem finite_closed_fiber_of_no_integralCurve {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsProper f] (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (y : Y) (hno : IsEmpty (IntegralCurve (f.fiber y))) : (f ⁻¹' {y}).Finite := by
  have hbound : topologicalKrullDim (f.fiber y) ≤ d :=
    (f.fiberι y).isEmbedding.topologicalKrullDim_le.trans hdim
  have hzero : topologicalKrullDim (f.fiber y) ≤ 0 := by
    by_contra h
    obtain ⟨n, hn, hpos⟩ := positive_dimension_eq_nat d hbound (lt_of_not_ge h)
    obtain ⟨C⟩ := nonempty_integralCurve_of_dimension_pos (f.fiber y) n hn hpos
    exact hno.false C
  let : IsLocallyNoetherian (f.fiber y) := by
    unfold Scheme.Hom.fiber
    infer_instance
  let : IsLocallyArtinian (f.fiber y) := IsLocallyArtinian.of_topologicalKrullDim_le_zero hzero
  let : Finite (f.fiber y) := finite_of_compact_of_discrete
  exact (f.fiberHomeo y).finite_iff.mp inferInstance

theorem isFinite_of_no_contracted_integralCurves {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsProper f] [JacobsonSpace Y]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (hno : ∀ (C : IntegralCurve X) (y : Y) (_hy : IsClosed ({y} : Set Y))
      (j : C.scheme ⟶ f.fiber y), j ≫ f.fiberι y = C.embedding → False) : IsFinite f := by
  apply isFinite_of_proper_finite_closed_fibers f
  intro y hy
  apply finite_closed_fiber_of_no_integralCurve f d hdim y
  refine ⟨fun C => ?_⟩
  exact hno (integralCurveFromClosedFiber f y hy C) y hy C.embedding rfl

end PiExponent.NumericalAmpleness

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_NakaiAmpleFromSections
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective PiExponentSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{0}}

theorem curveDegree_eq_zero_of_sectionsMorphism_contracted
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (k : ℕ) (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ z, sectionOpen X (s z)) = ⊤)
    (C : IntegralCurve X)
    (y : ProjectiveO1.projectiveSpace ℂ (Fin k))
    (hconstant : ∀ c : C.scheme, sectionsMorphism (baseScalars p) s hs (C.embedding c) = y) :
    curveDegree p L C = 0 := by
  classical
  obtain ⟨c⟩ : Nonempty C.scheme := inferInstance
  have hc : C.embedding c ∈ ⨆ z, sectionOpen X (s z) := by rw [hs]; trivial
  obtain ⟨z,hz⟩ := Opens.mem_iSup.mp hc
  have hpre : sectionsMorphism (baseScalars p) s hs ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin k) ℂ) (MvPolynomial.X z) =
      sectionOpen X (s z) := sectionsMorphism_preimage (baseScalars p) s hs z
  have hy : y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin k) ℂ)
      (MvPolynomial.X z) := by
    rw [← hpre] at hz
    change sectionsMorphism (baseScalars p) s hs (C.embedding c) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin k) ℂ) (MvPolynomial.X z) at hz
    rwa [hconstant c] at hz
  have hrange : Set.range C.embedding ⊆ (sectionOpen X (s z) : Set X) := by
    rintro x ⟨c',rfl⟩
    rw [← hpre]
    change sectionsMorphism (baseScalars p) s hs (C.embedding c') ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin k) ℂ) (MvPolynomial.X z)
    rwa [hconstant c']
  let e := ConstantPullbackDegree.pullbackFrame_of_range_subset L C.embedding
    (sectionOpen X (s z)) hrange (sectionFrame (s z))
  change eulerCharacteristic (C.embedding ≫ p) 1 (L.pullback C.embedding).sheaf -
    eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme) = 0
  rw [eulerCharacteristic_iso (C.embedding ≫ p) e 1]
  exact sub_self _

theorem isAmple_of_section_cover_of_curveDegree_pos [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (k : ℕ) (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ z, sectionOpen X (s z)) = ⊤)
    (hpositive : ∀ C : IntegralCurve X, 0 < curveDegree p L C) : L.IsAmple := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (baseScalars p))) := by
    change IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)))
    rw [toSpec_scalarMap p]
    infer_instance
  let f : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin k) :=
    sectionsMorphism (baseScalars p) s hs
  let : IsProper f := sectionsMorphism_proper (baseScalars p) s hs
  let : JacobsonSpace (ProjectiveO1.projectiveSpace ℂ (Fin k)) :=
    LocallyOfFiniteType.jacobsonSpace (polynomialProjectiveProjection ℂ (Fin k))
  let : IsFinite f := isFinite_of_no_contracted_integralCurves f d hdim (by
    intro C y hy j hj
    have hconstant (c : C.scheme) : f (C.embedding c) = y := by
      have hc : f.fiberι y (j c) ∈ Set.range (f.fiberι y) := ⟨j c,rfl⟩
      rw [f.range_fiberι] at hc
      change f (f.fiberι y (j c)) = y at hc
      have he := congrArg (fun g : C.scheme ⟶ X => g c) hj
      simpa only [Scheme.Hom.comp_apply] using he ▸ hc
    have hz := curveDegree_eq_zero_of_sectionsMorphism_contracted p L k s hs C y hconstant
    have hp := hpositive C
    omega)
  apply L.ample_of_affine_section_cover s hs
  intro z
  change IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s z))
  exact (sectionsMorphism_preimage (baseScalars p) s hs z) ▸
    (standardChart_isAffineOpen (R := ℂ) z).preimage f

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerDifferencePolynomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness

open Filter Finset Function
open scoped Topology BigOperators

theorem forwardDifference_eq_zero_of_le {G : Type*} [AddCommGroup G]
    (f : ℕ → G) (d : ℕ) (hzero : (fwdDiff (1 : ℕ))^[d] f = 0)
    (k : ℕ) (hk : d ≤ k) : (fwdDiff (1 : ℕ))^[k] f = 0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm d r, Function.iterate_add_apply, hzero]
  ext n
  simp [fwdDiff_iter_eq_sum_shift]

theorem newton_sum_of_forwardDifference_eq_zero {G : Type*} [AddCommGroup G]
    (f : ℕ → G) (d : ℕ) (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0) (n : ℕ) :
    f n = ∑ k ∈ Finset.range (d+1), n.choose k • (fwdDiff (1 : ℕ))^[k] f 0 := by
  have hNewton : f n = ∑ k ∈ Finset.range (n+1),
      n.choose k • (fwdDiff (1 : ℕ))^[k] f 0 := by
    simpa using shift_eq_sum_fwdDiff_iter (1 : ℕ) f n 0
  rw [hNewton]
  by_cases hnd : n ≤ d
  · apply Finset.sum_subset (Finset.range_mono (by omega : n+1 ≤ d+1))
    intro k hk hkn
    have hnk : n < k := by simp only [Finset.mem_range] at hkn; omega
    rw [Nat.choose_eq_zero_of_lt hnk, zero_smul]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega : d+1 ≤ n+1))
    intro k hk hkd
    have hdk : d+1 ≤ k := by simp only [Finset.mem_range] at hkd; omega
    rw [forwardDifference_eq_zero_of_le f (d+1) hzero k hdk]
    simp

theorem integer_newton_sum_of_forwardDifference_eq_zero
    (f : ℕ → ℤ) (d : ℕ) (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0) (n : ℕ) :
    f n = ∑ k ∈ Finset.range (d+1),
      (n.choose k : ℤ) * (fwdDiff (1 : ℕ))^[k] f 0 := by
  simpa only [nsmul_eq_mul] using newton_sum_of_forwardDifference_eq_zero f d hzero n

theorem tendsto_choose_div_pow (k d : ℕ) (hkd : k ≤ d) :
    Tendsto (fun n : ℕ => (n.choose k : ℝ) / (n : ℝ)^d) atTop
      (𝓝 (if k = d then 1 / (d.factorial : ℝ) else 0)) := by
  have he := (isEquivalent_choose k).div
    (Asymptotics.IsEquivalent.refl (u := fun n : ℕ => (n : ℝ)^d) (l := atTop))
  apply he.symm.tendsto_nhds
  by_cases h : k = d
  · subst k
    simp only [ite_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    dsimp
    field_simp
  · simp only [h, ite_false]
    have ht := (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (lt_of_le_of_ne hkd h)).comp
      tendsto_natCast_atTop_atTop
    have ht' := ht.div_const (k.factorial : ℝ)
    change Tendsto (fun n : ℕ => (n : ℝ)^k / (k.factorial : ℝ) / (n : ℝ)^d) _ _
    convert ht' using 1
    · funext n
      simp only [Function.comp_apply]
      ring
    · simp

theorem tendsto_normalized_of_forwardDifference_eq_zero
    (f : ℕ → ℤ) (d : ℕ) (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0) :
    Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)^d) atTop
      (𝓝 ((((fwdDiff (1 : ℕ))^[d] f 0 : ℤ) : ℝ) / (d.factorial : ℝ))) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (d+1)) :=
    (tendsto_choose_div_pow k d (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)).mul_const
      (((fwdDiff (1 : ℕ))^[k] f 0 : ℤ) : ℝ)
  have hs := tendsto_finsetSum (Finset.range (d+1)) hterm
  have hreal (n : ℕ) : (f n : ℝ) = ∑ k ∈ Finset.range (d+1),
      (n.choose k : ℝ) * (((fwdDiff (1 : ℕ))^[k] f 0 : ℤ) : ℝ) := by
    exact_mod_cast integer_newton_sum_of_forwardDifference_eq_zero f d hzero n
  convert hs using 1
  · funext n
    rw [hreal, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · congr 1
    rw [Finset.sum_eq_single d]
    · simp only [ite_true]
      ring
    · intro k hk hkd
      simp [hkd]
    · simp

theorem tendsto_atTop_of_forwardDifference_eq_zero
    (f : ℕ → ℤ) (d : ℕ) (hd : 0 < d)
    (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0)
    (hpositive : 0 < (fwdDiff (1 : ℕ))^[d] f 0) :
    Tendsto f atTop atTop := by
  have hlead : (0 : ℝ) <
      (((fwdDiff (1 : ℕ))^[d] f 0 : ℤ) : ℝ) / (d.factorial : ℝ) :=
    div_pos (by exact_mod_cast hpositive) (by exact_mod_cast Nat.factorial_pos d)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ)^d) atTop atTop :=
    (tendsto_pow_atTop (Nat.ne_of_gt hd)).comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_normalized_of_forwardDifference_eq_zero f d hzero).pos_mul_atTop
    hlead hpow
  apply (tendsto_intCast_atTop_iff (R := ℝ)).mp
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ)^d ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hn)
  exact div_mul_cancel₀ _ hn'

end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveDegreeLaws
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem curveLineCohomologyTwoZero_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (C : IntegralCurve X) :
    CurveDegree.LineCohomologyTwoZero C.scheme := by
  intro M
  have hz := lineBundle_cohomology_zero_of_dimension_le_q68 1 (C.embedding ≫ p)
    (H.pullback C.embedding) (hH.pullback_closedImmersion H C.embedding) M
    C.dimension.le 2 (by omega)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem curveDegree_pow_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (C : IntegralCurve X) (n : ℕ) :
    curveDegree p (L.pow n) C = (n : ℤ) * curveDegree p L C :=
  curveDegree_pow p H hH L C
    (CurveDegree.finite_line_cohomology_of_ample (C.embedding ≫ p) (H.pullback C.embedding)
      (hH.pullback_closedImmersion H C.embedding))
    (curveLineCohomologyTwoZero_of_ample p H hH C) n

theorem curveDegree_tensor_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L M : LineBundle X) (C : IntegralCurve X) :
    curveDegree p (L.tensor M) C = curveDegree p L C + curveDegree p M C :=
  curveDegree_tensor p H hH L M C
    (CurveDegree.finite_line_cohomology_of_ample (C.embedding ≫ p) (H.pullback C.embedding)
      (hH.pullback_closedImmersion H C.embedding))
    (curveLineCohomologyTwoZero_of_ample p H hH C)

theorem curveDegree_pos_of_uniform_margin
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (C : IntegralCurve X) : 0 < curveDegree p L C := by
  have hHpos : (0 : ℝ) < (curveDegree p H C : ℝ) := by
    exact_mod_cast curveDegree_pos_of_ample_q68 p H hH C
  have hpos : (0 : ℝ) < (curveDegree p L C : ℝ) := (mul_pos hε hHpos).trans_le (hmargin C)
  exact_mod_cast hpos

theorem uniform_margin_tensor_powers
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (ε : ℝ)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (a b : ℕ) (C : IntegralCurve X) :
    ((b:ℝ)*ε+a) * (curveDegree p H C : ℝ) ≤
      (curveDegree p ((L.pow b).tensor (H.pow a)) C : ℝ) := by
  rw [curveDegree_tensor_of_ample p H hH,
    curveDegree_pow_of_ample p H hH L C b, curveDegree_pow_of_ample p H hH H C a]
  push_cast
  have h := mul_le_mul_of_nonneg_left (hmargin C) (Nat.cast_nonneg b : (0:ℝ) ≤ b)
  nlinarith

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_NakaiInductionStep
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem isAmple_of_lower_ampleness_of_euler_growth [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) atTop atTop)
    (hpositive : ∀ C : IntegralCurve X, 0 < curveDegree p L C) : L.IsAmple := by
  obtain ⟨a,ha,k,s,hs⟩ := exists_power_section_cover_of_euler_growth_q68
    p r i hi H L hH d hdim hlower hgrowth
  apply LineBundle.IsAmple.of_pow L ha
  apply isAmple_of_section_cover_of_curveDegree_pos p (L.pow a) (d+1) (by
    simpa only [Nat.cast_add, Nat.cast_one] using hdim) k s hs
  intro C
  rw [curveDegree_pow_of_ample p H hH L C a]
  exact mul_pos (by exact_mod_cast ha) (hpositive C)

theorem isAmple_of_lower_ampleness_of_topEuler_pos [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (htop : 0 < (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) 0)
    (hpositive : ∀ C : IntegralCurve X, 0 < curveDegree p L C) : L.IsAmple := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  have hzero := euler_power_dimension_difference_eq_zero_q68 p r i hi L (d+1) (by
    simpa only [Nat.cast_add, Nat.cast_one] using hdim)
  have hgrowth := tendsto_atTop_of_forwardDifference_eq_zero
    (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) (d+1) (by omega) hzero htop
  exact isAmple_of_lower_ampleness_of_euler_growth p r i hi H L hH d hdim hlower hgrowth hpositive

theorem isAmple_of_lower_ampleness_of_topEuler_pos_of_margin [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (htop : 0 < (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) 0)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) : L.IsAmple :=
  isAmple_of_lower_ampleness_of_topEuler_pos p r i hi H L hH d hdim hlower htop
    (curveDegree_pos_of_uniform_margin p H L hH ε hε hmargin)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_NumericalSlopeInduction
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem slope_lower_closed_ampleness
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (a b : ℕ) (hb : 0 < b) :
    ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      ((slopeBundle L H a b).pullback I.subschemeι).IsAmple := by
  intro I hI
  have hδ : (0:ℝ) < (b:ℝ)*ε+a :=
    add_pos_of_pos_of_nonneg (mul_pos (by exact_mod_cast hb) hε) (Nat.cast_nonneg a)
  apply hlower I hI ((slopeBundle L H a b).pullback I.subschemeι) ((b:ℝ)*ε+a) hδ
  exact uniform_curve_margin_restrict p (slopeBundle L H a b) H ((b:ℝ)*ε+a)
    (uniform_margin_tensor_powers p H L hH ε hmargin a b) I.subschemeι

theorem ample_slope_of_topEuler_pos_of_lower_criterion [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (a b : ℕ) (hb : 0 < b)
    (htop : 0 < (fwdDiff (1:ℕ))^[d+1]
      (fun n => eulerCharacteristic p (d+1) ((slopeBundle L H a b).pow n).sheaf) 0) :
    (slopeBundle L H a b).IsAmple := by
  have hδ : (0:ℝ) < (b:ℝ)*ε+a :=
    add_pos_of_pos_of_nonneg (mul_pos (by exact_mod_cast hb) hε) (Nat.cast_nonneg a)
  exact isAmple_of_lower_ampleness_of_topEuler_pos_of_margin p r i hi H
    (slopeBundle L H a b) hH d hdim
    (slope_lower_closed_ampleness p H L hH d hlower ε hε hmargin a b hb)
    htop ((b:ℝ)*ε+a) hδ (uniform_margin_tensor_powers p H L hH ε hmargin a b)

theorem ample_slope_of_polynomial_pos_of_lower_criterion_q68_oai [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (P : Polynomial ℝ)
    (hP : ∀ a b : ℕ, 0 < b →
      (((fwdDiff (1:ℕ))^[d+1]
        (fun n => eulerCharacteristic p (d+1) ((slopeBundle L H a b).pow n).sheaf) 0 : ℤ):ℝ) =
        (b:ℝ)^(d+1) * P.eval ((a:ℝ)/b))
    (a b : ℕ) (hb : 0 < b) (hpos : 0 < P.eval ((a:ℝ)/b)) :
    (slopeBundle L H a b).IsAmple := by
  apply ample_slope_of_topEuler_pos_of_lower_criterion p r i hi H L hH d hdim hlower ε hε hmargin a b hb
  have hreal : (0:ℝ) <
      (((fwdDiff (1:ℕ))^[d+1]
        (fun n => eulerCharacteristic p (d+1) ((slopeBundle L H a b).pow n).sheaf) 0 : ℤ):ℝ) := by
    rw [hP a b hb]
    exact mul_pos (pow_pos (by exact_mod_cast hb) _) hpos
  exact_mod_cast hreal

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.ample_slope_of_polynomial_pos_of_lower_criterion_q68_oai := @OAI.PiExponent.NumericalAmpleness.ample_slope_of_polynomial_pos_of_lower_criterion_q68_oai
