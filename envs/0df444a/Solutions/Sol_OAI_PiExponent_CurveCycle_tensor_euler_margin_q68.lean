-- Prove2me | solution 1 for OAI.PiExponent.CurveCycle.tensor_euler_margin_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:27:37.399335+00:00
-- url     : https://prove2.me/submissions/edc55ab5-f3b0-4ac2-bf38-ce9710479c0e

import Mathlib
import Definitions.Def_OAIQ068A040
import Definitions.Def_OAIQ068A041
import Definitions.Def_OAIQ068A042
import Theorems.Thm_OAI_PiExponent_CurveCycle_zero_lengthNat_eq_component_sum_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_exists_regular_twist_pair_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_lineBundle_cohomology_zero_of_dimension_le_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveLocalAssociativity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentJets.W28.LocalIntersection
open scoped nonZeroDivisors

theorem sectionGerm_nonZeroDivisor {X : Scheme.{0}}
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (x : X) (hx : x ∈ U.1) :
    SectionZeroStalk.sectionGerm L s U e x hx ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  let := X.presheaf.algebra_section_stalk (⟨x,hx⟩ : U.1)
  let := U.2.isLocalization_stalk (⟨x,hx⟩ : U.1)
  exact IsLocalization.nonZeroDivisors_le_comap
    ((U.2.primeIdealOf ⟨x,hx⟩).asIdeal.primeCompl) (X.presheaf.stalk x)
    (NumericalAmpleness.section_affine_coefficient_nonZeroDivisor L s U e)

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ReducedComponentStalk
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

theorem reducedComponentι_genericPoint (X : Scheme.{0}) (C : irreducibleComponents X) :
    reducedComponentι X C (genericPoint (reducedComponent X C)) =
      (genericPoints.ofComponent C).val := by
  have hgen : IsGenericPoint
      (reducedComponentι X C (genericPoint (reducedComponent X C))) C.val := by
    change closure {_} = C.val
    rw [← Set.image_singleton, (reducedComponentι X C).isClosedEmbedding.closure_image_eq,
      genericPoint_closure, Set.image_univ, reducedComponentι_range]
  exact hgen.eq (genericPoints.isGenericPoint_ofComponent C)

theorem fromSpecStalk_bot_eq_genericPoint (Y : Scheme.{0}) [IsIntegral Y] (z : Y) :
    Y.fromSpecStalk z (⟨⊥,inferInstance⟩ : Spec (Y.presheaf.stalk z)) = genericPoint Y := by
  have hbot : (⊥ : Ideal (Y.presheaf.stalk z)) ∈ minimalPrimes (Y.presheaf.stalk z) := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    exact Set.mem_singleton _
  have hgen := (generic_embedding_iff (Y.fromSpecStalk z).isEmbedding
    (fromSpecStalk_generizing Y z) (⟨⊥,inferInstance⟩ : Spec (Y.presheaf.stalk z))).mp
      (minimalPrimesGenericEquiv (Y.presheaf.stalk z) ⟨⊥,hbot⟩).property
  rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at hgen

theorem reducedComponentι_stalkMap_ker (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) :
    RingHom.ker ((reducedComponentι X C).stalkMap z).hom =
      (reducedComponentStalkPrime X C z).val := by
  let i := reducedComponentι X C
  let q : Spec (X.presheaf.stalk (i z)) :=
    ⟨RingHom.ker (i.stalkMap z).hom, RingHom.ker_isPrime _⟩
  let P := reducedComponentStalkPrime X C z
  have hq : X.fromSpecStalk (i z) q = (genericPoints.ofComponent C).val := by
    have hnat := congrArg (fun f : Spec ((reducedComponent X C).presheaf.stalk z) ⟶ X =>
      f (⟨⊥,inferInstance⟩ : Spec ((reducedComponent X C).presheaf.stalk z)))
      (Scheme.SpecMap_stalkMap_fromSpecStalk (f := i) (x := z))
    change X.fromSpecStalk (i z) q =
      i ((reducedComponent X C).fromSpecStalk z (⟨⊥,inferInstance⟩ :
        Spec ((reducedComponent X C).presheaf.stalk z))) at hnat
    rw [hnat, fromSpecStalk_bot_eq_genericPoint]
    exact reducedComponentι_genericPoint X C
  have hP : X.fromSpecStalk (i z) (⟨P.val,P.property.1.1⟩ : Spec (X.presheaf.stalk (i z))) =
      (genericPoints.ofComponent C).val := by
    simpa only [P,i,reducedComponentStalkPrime,Equiv.apply_symm_apply] using
      stalkMinimalPrimesEquivComponentsThrough_point X (i z) P
  exact congrArg PrimeSpectrum.asIdeal
    ((X.fromSpecStalk (i z)).isEmbedding.injective (hq.trans hP.symm))

theorem reducedComponentι_stalkMap_ne_zero (X : Scheme.{0})
    (C : irreducibleComponents X) (z : reducedComponent X C)
    (a : X.presheaf.stalk (reducedComponentι X C z)) (ha : a ∈ nonZeroDivisors _) :
    (reducedComponentι X C).stalkMap z a ≠ 0 := by
  intro h
  have hmem : a ∈ (reducedComponentStalkPrime X C z).val := by
    rw [← reducedComponentι_stalkMap_ker]
    exact h
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    hmem (reducedComponentStalkPrime X C z).property ha

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_RegularComponentSection
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroStalk


variable {X Y : Scheme.{0}}

theorem exists_pullback_frame_sectionGerm (f : Y ⟶ X) [IsAffineHom f]
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    ∃ eF : (L.pullback f).sheaf.restrict (f ⁻¹ᵁ U.1).ι ≅ O (f ⁻¹ᵁ U.1).toScheme,
      ∀ (y : Y) (hy : f y ∈ U.1),
        sectionGerm (L.pullback f) (pullbackSection f s)
          ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩ eF y hy =
        f.stalkMap y (sectionGerm L s U e (f y) hy) := by
  obtain ⟨eF, he⟩ := exists_restricted_pullback_frame f U.1 e s
  refine ⟨eF, ?_⟩
  intro y hy
  have hr (a : Γ(U.1.toScheme, ⊤)) :
      (f ⁻¹ᵁ U.1).topIso.hom ((f ∣_ U.1).appTop a) =
        f.app U.1 (U.1.topIso.hom a) := by
    change (f ⁻¹ᵁ U.1).topIso.hom ((f ∣_ U.1).app ⊤ a) = _
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_app_top]
    simp only [Scheme.Hom.appLE_eq_app]
    exact CategoryTheory.congr_fun (f ⁻¹ᵁ U.1).topIso.inv_hom_id _
  unfold sectionGerm
  erw [he, hr, Scheme.Hom.germ_stalkMap_apply]

private theorem sectionGerm_zero (L : LineBundle X) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) (x : X) (hx : x ∈ U.1) :
    sectionGerm L 0 U e x hx = 0 := by
  simp only [sectionGerm]
  erw [restrictSection_zero, coefficient, CategoryTheory.Limits.zero_comp]
  simp only [endValue]
  change X.presheaf.germ U.1 x hx (U.1.topIso.hom 0) = 0
  simp only [map_zero]

theorem regular_component_section_ne_zero (X : Scheme.{0}) (C : irreducibleComponents X)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    pullbackSection (reducedComponentι X C) s ≠ 0 := by
  let f := reducedComponentι X C
  let z : reducedComponent X C := genericPoint (reducedComponent X C)
  obtain ⟨U, hz, ⟨e⟩, _⟩ := common_affine_frames L L (f z)
  obtain ⟨eF, heF⟩ := exists_pullback_frame_sectionGerm f L s U e
  have hne := reducedComponentι_stalkMap_ne_zero X C z
    (sectionGerm L s U e (f z) hz) (sectionGerm_nonZeroDivisor L s U e (f z) hz)
  intro hs
  apply hne
  rw [← heF z hz, hs]
  exact sectionGerm_zero _ _ _ _ _

theorem regular_component_section_mono (X : Scheme.{0}) (C : irreducibleComponents X)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    Mono (pullbackSection (reducedComponentι X C) s) :=
  (L.pullback (reducedComponentι X C)).mono_section _
    (regular_component_section_ne_zero X C L s)

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_AmpleCohomologyFinite
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerZeroDimensional
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem lineBundle_trivial_of_dim_le_zero [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 0) (L : LineBundle X) :
    Nonempty (L.sheaf ≅ structureSheaf X) := by
  let : DiscreteTopology X := discreteTopology_of_dim_le_zero hdim
  exact PiExponentSeshadri.FiniteSupport.lineBundle_trivial L

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_GeneralCartierDegreeLength
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.GeneralCartierDegreeLength


theorem cartier_euler_difference_eq_sum_local_lengths
    {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData) [Finite I.subscheme]
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))})
    (hfiniteM : ∀ n ≤ 1, letI := Module.compHom (cohomology M.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology M.sheaf n))
    (hfiniteN : ∀ n ≤ 1, letI := Module.compHom (cohomology N.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf n))
    [Subsingleton (cohomology M.sheaf 2)] :
    letI : Fintype I.subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 N.sheaf - eulerCharacteristic p 1 M.sheaf =
      ∑ x : I.subscheme,
        ((Module.length (I.subscheme.presheaf.stalk x)
          (I.subscheme.presheaf.stalk x)).toNat : ℤ) := by
  let : Fintype I.subscheme := Fintype.ofFinite _
  obtain ⟨hz, hseq⟩ := PiExponentSeshadri.CartierSequence.exact p M N φ I heq
  have hfiniteZ (n : ℕ) (_hn : n ≤ 1) :=
    PiExponentSeshadri.FiniteSupport.finite_line_pushforward_finiteDimensional
      I.subschemeι p (N.pullback I.subschemeι) n
  have h := eulerCharacteristic_add p hseq 1 hfiniteM hfiniteN hfiniteZ
  have hdiff : eulerCharacteristic p 1 N.sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1
        ((Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) := by
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h)
  exact hdiff.trans
    (PiExponentSeshadri.FiniteSupport.finite_line_euler_eq_sum_stalk_lengths
      I.subschemeι p (N.pullback I.subschemeι) 1)

theorem regular_section_tensor_euler_eq_sum_local_lengths {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (hfiniteM : ∀ n ≤ 1, letI := Module.compHom (cohomology M.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology M.sheaf n))
    (hfiniteLM : ∀ n ≤ 1, letI := Module.compHom (cohomology (L.tensor M).sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.tensor M).sheaf n))
    [Subsingleton (cohomology M.sheaf 2)] :
    letI : Finite (PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme :=
      finite_zeroIdeal_of_mono p hd L s
    letI : Fintype (PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      ∑ x : (PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme,
        ((Module.length
          ((PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk x)
          ((PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk x)).toNat : ℤ) := by
  let I := PiExponent.SectionZeroIdeal.zeroIdeal L s
  let : Finite I.subscheme := finite_zeroIdeal_of_mono p hd L s
  let : Fintype I.subscheme := Fintype.ofFinite _
  let φ := PiExponent.CartierPowerFrames.sectionMultiplyLeft L.sheaf M.sheaf s
  let : Mono (moduleTensorMap s (𝟙 M.sheaf)) := moduleTensorMap_mono s M
  have hmono : Mono φ := mono_comp _ _
  refine @cartier_euler_difference_eq_sum_local_lengths X p inferInstance M (L.tensor M)
    φ hmono I inferInstance ?_ hfiniteM hfiniteLM inferInstance
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
  refine ⟨U,hx,f,PiExponent.CartierPowerFrames.tensorFrame L.sheaf M.sheaf U.1 e f,?_⟩
  exact (PiExponent.SectionZeroIdeal.zeroIdeal_on_frame L s U e).trans
    (PiExponent.CartierPowerFrames.tensor_multiply_ideal L.sheaf M.sheaf s U e f).symm

end PiExponent.GeneralCartierDegreeLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveRegularEuler
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

theorem regular_section_tensor_euler_eq_lengths {X : Scheme.{0}} [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    letI : Finite (SectionZeroIdeal.zeroIdeal L s).subscheme :=
      GeneralCartierDegreeLength.finite_zeroIdeal_of_mono p hd L s
    letI : Fintype (SectionZeroIdeal.zeroIdeal L s).subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      ∑ x : (SectionZeroIdeal.zeroIdeal L s).subscheme,
        ((Module.length
          ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk x)
          ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk x)).toNat : ℤ) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation (L.tensor M)
  let : Subsingleton (cohomology M.sheaf 2) := ⟨fun a b =>
    (NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le_q68 1 p H hH M hd
      2 (by omega) a).trans
    (NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le_q68 1 p H hH M hd
      2 (by omega) b).symm⟩
  exact GeneralCartierDegreeLength.regular_section_tensor_euler_eq_sum_local_lengths
    p hd L M s
    (fun q _ => AmpleCohomologyFinite.cohomology_finite_of_ample p H hH M.sheaf q)
    (fun q _ => AmpleCohomologyFinite.cohomology_finite_of_ample p H hH (L.tensor M).sheaf q)

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveTensorEuler
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

theorem regular_tensor_euler_add {X : Scheme.{0}} [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  have hM := regular_section_tensor_euler_eq_lengths p hd H hH L M s
  have hO := regular_section_tensor_euler_eq_lengths p hd H hH L (L.pow 0) s
  have he := eulerCharacteristic_iso p (moduleTensorRightUnit L.sheaf) 1
  change eulerCharacteristic p 1 (L.tensor (L.pow 0)).sheaf =
    eulerCharacteristic p 1 L.sheaf at he
  rw [he] at hO
  exact hM.trans hO.symm

theorem tensor_euler_add {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  obtain ⟨B,s,t,hs,ht⟩ := NumericalAmpleness.exists_regular_twist_pair_q68 p H L hH
  let : Mono s := hs
  let : Mono t := ht
  have h₁ := regular_tensor_euler_add p hd H hH (L.tensor B) M s
  have h₂ := regular_tensor_euler_add p hd H hH B L t
  have h₃ := regular_tensor_euler_add p hd H hH B (L.tensor M) t
  have hc := eulerCharacteristic_iso p (moduleTensorComm L.sheaf B.sheaf) 1
  change eulerCharacteristic p 1 (L.tensor B).sheaf =
    eulerCharacteristic p 1 (B.tensor L).sheaf at hc
  have ha := eulerCharacteristic_iso p
    (moduleTensorIso (moduleTensorComm L.sheaf B.sheaf) (Iso.refl M.sheaf) ≪≫
      lineTensorAssoc B L M) 1
  change eulerCharacteristic p 1 ((L.tensor B).tensor M).sheaf =
    eulerCharacteristic p 1 (B.tensor (L.tensor M)).sheaf at ha
  omega

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveCycleEuler
attribute [-instance] _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

theorem componentEulerDegree_tensor {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) (C : irreducibleComponents X) :
    componentEulerDegree p (L.tensor M) C =
      componentEulerDegree p L C + componentEulerDegree p M C := by
  let i := reducedComponentι X C
  let : IsLocallyNoetherian (reducedComponent X C) :=
    LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  let : CompactSpace (reducedComponent X C) :=
    QuasiCompact.compactSpace_of_compactSpace (i ≫ p)
  let : IsNoetherian (reducedComponent X C) := {}
  have hdim : topologicalKrullDim (reducedComponent X C) ≤ 1 :=
    i.isEmbedding.isInducing.topologicalKrullDim_le.trans hd
  have h := tensor_euler_add (i ≫ p) hdim (H.pullback i)
    (hH.pullback_closedImmersion H i) (L.pullback i) (M.pullback i)
  have he := eulerCharacteristic_iso (i ≫ p) (PiExponentSeshadri.PullbackTensor.iso i L M) 1
  unfold componentEulerDegree
  change eulerCharacteristic (i ≫ p) 1 ((L.tensor M).pullback i).sheaf =
    eulerCharacteristic (i ≫ p) 1 ((L.pullback i).tensor (M.pullback i)).sheaf at he
  rw [he]
  dsimp only [i] at h he ⊢
  omega

theorem cycleEulerDegree_tensor {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) :
    cycleEulerDegree p (L.tensor M) = cycleEulerDegree p L + cycleEulerDegree p M := by
  classical
  unfold cycleEulerDegree
  simp only [componentEulerDegree_tensor p hd H hH L M,mul_add,Finset.sum_add_distrib]

theorem componentEulerDegree_zero_of_dimension_le_zero {X : Scheme.{0}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (C : irreducibleComponents X)
    (hdim : topologicalKrullDim (reducedComponent X C) ≤ 0) :
    componentEulerDegree p L C = 0 := by
  let : IsLocallyNoetherian (reducedComponent X C) :=
    LocallyOfFiniteType.isLocallyNoetherian (reducedComponentι X C)
  obtain ⟨e⟩ := NumericalAmpleness.lineBundle_trivial_of_dim_le_zero hdim
    (L.pullback (reducedComponentι X C))
  exact sub_eq_zero.mpr (eulerCharacteristic_iso (reducedComponentι X C ≫ p) e 1)

theorem regular_section_tensor_euler_eq_cycle {X : Scheme.{0}}
    [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      cycleEulerDegree p L := by
  classical
  let : Fintype (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  let : Finite (zeroIdeal L s).subscheme :=
    GeneralCartierDegreeLength.finite_zeroIdeal_of_mono p hd L s
  let : Fintype (zeroIdeal L s).subscheme := Fintype.ofFinite _
  let : ∀ C : irreducibleComponents X,
    Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme := fun _ => Fintype.ofFinite _
  have hcomponent (C : irreducibleComponents X) :
      componentEulerDegree p L C =
        ∑ z, ((stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat : ℤ) := by
    let i := reducedComponentι X C
    let LC := L.pullback i
    let sC := pullbackSection i s
    have hsC : Mono sC := regular_component_section_mono X C L s
    have hdim : topologicalKrullDim (reducedComponent X C) ≤ 1 :=
      i.isEmbedding.isInducing.topologicalKrullDim_le.trans hd
    have hc := @regular_section_tensor_euler_eq_lengths _ inferInstance (i ≫ p)
      inferInstance hdim (H.pullback i) (hH.pullback_closedImmersion H i)
      LC (LC.pow 0) sC hsC
    have he := eulerCharacteristic_iso (i ≫ p) (moduleTensorRightUnit LC.sheaf) 1
    change eulerCharacteristic (i ≫ p) 1 (LC.tensor (LC.pow 0)).sheaf =
      eulerCharacteristic (i ≫ p) 1 LC.sheaf at he
    rw [he] at hc
    exact hc
  have hlength := zero_lengthNat_eq_component_sum_q68 hd L s
  have hlengthZ :
      (∑ y : (zeroIdeal L s).subscheme, ((stalkLength (zeroIdeal L s).subscheme y).toNat : ℤ)) =
        ∑ C : irreducibleComponents X, (componentMultiplicity X C : ℤ) *
          ∑ z, ((stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
            (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat : ℤ) := by
    exact_mod_cast hlength
  calc
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
        ∑ y : (zeroIdeal L s).subscheme, ((stalkLength (zeroIdeal L s).subscheme y).toNat : ℤ) :=
      regular_section_tensor_euler_eq_lengths p hd H hH L M s
    _ = ∑ C : irreducibleComponents X, (componentMultiplicity X C : ℤ) *
          ∑ z, ((stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
            (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat : ℤ) := hlengthZ
    _ = cycleEulerDegree p L := by
      unfold cycleEulerDegree
      apply Finset.sum_congr rfl
      intro C _
      exact congrArg (fun n : ℤ => (componentMultiplicity X C : ℤ) * n) (hcomponent C).symm

theorem tensor_euler_eq_cycle {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      cycleEulerDegree p L := by
  obtain ⟨B,s,t,hs,ht⟩ := NumericalAmpleness.exists_regular_twist_pair_q68 p H L hH
  let : Mono s := hs
  let : Mono t := ht
  have h₁ := regular_section_tensor_euler_eq_cycle p hd H hH (L.tensor B) M s
  have h₂ := regular_section_tensor_euler_eq_cycle p hd H hH B (L.tensor M) t
  have hcycle := cycleEulerDegree_tensor p hd H hH L B
  have ha := eulerCharacteristic_iso p
    (moduleTensorIso (moduleTensorComm L.sheaf B.sheaf) (Iso.refl M.sheaf) ≪≫
      lineTensorAssoc B L M) 1
  change eulerCharacteristic p 1 ((L.tensor B).tensor M).sheaf =
    eulerCharacteristic p 1 (B.tensor (L.tensor M)).sheaf at ha
  omega

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveComponentsDimension
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem component_dimension_one_or_zero {X : Scheme.{0}}
    (hd : topologicalKrullDim X ≤ 1) (C : irreducibleComponents X) :
    topologicalKrullDim (reducedComponent X C) = 1 ∨
      topologicalKrullDim (reducedComponent X C) ≤ 0 := by
  have hdim := (reducedComponentι X C).isEmbedding.isInducing.topologicalKrullDim_le.trans hd
  by_cases h : topologicalKrullDim (reducedComponent X C) = 1
  · exact Or.inl h
  · right
    change topologicalKrullDim (reducedComponent X C) ≤ ((0 : ℕ) : WithBot ℕ∞)
    rw [← ENat.WithBot.lt_add_one_iff]
    simpa using lt_of_le_of_ne hdim h

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveCycleNumerical
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

theorem cycleEulerDegree_margin {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (L H : LineBundle X) (ε : ℝ)
    (hmargin : ∀ C : NumericalAmpleness.IntegralCurve X,
      ε * (NumericalAmpleness.curveDegree p H C : ℝ) ≤
        (NumericalAmpleness.curveDegree p L C : ℝ)) :
    ε * (cycleEulerDegree p H : ℝ) ≤ (cycleEulerDegree p L : ℝ) := by
  classical
  have hc (C : irreducibleComponents X) :
      ε * (componentEulerDegree p H C : ℝ) ≤ (componentEulerDegree p L C : ℝ) := by
    rcases component_dimension_one_or_zero hd C with hC | hC
    · exact hmargin (componentIntegralCurve C hC)
    · rw [componentEulerDegree_zero_of_dimension_le_zero p H C hC,
        componentEulerDegree_zero_of_dimension_le_zero p L C hC]
      simp
  unfold cycleEulerDegree
  simp only [Int.cast_sum,Int.cast_mul,Int.cast_natCast]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C _
  calc
    ε * ((componentMultiplicity X C : ℝ) * (componentEulerDegree p H C : ℝ)) =
        (componentMultiplicity X C : ℝ) * (ε * (componentEulerDegree p H C : ℝ)) := by ring
    _ ≤ (componentMultiplicity X C : ℝ) * (componentEulerDegree p L C : ℝ) :=
      mul_le_mul_of_nonneg_left (hc C) (Nat.cast_nonneg _)

theorem tensor_euler_margin_q68_oai {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (A : LineBundle X) (hA : A.IsAmple)
    (L H M N : LineBundle X) (ε : ℝ)
    (hmargin : ∀ C : NumericalAmpleness.IntegralCurve X,
      ε * (NumericalAmpleness.curveDegree p H C : ℝ) ≤
        (NumericalAmpleness.curveDegree p L C : ℝ)) :
    ε * ((eulerCharacteristic p 1 (H.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf : ℤ) : ℝ) ≤
      ((eulerCharacteristic p 1 (L.tensor N).sheaf - eulerCharacteristic p 1 N.sheaf : ℤ) : ℝ) := by
  rw [tensor_euler_eq_cycle p hd A hA H M,tensor_euler_eq_cycle p hd A hA L N]
  exact cycleEulerDegree_margin p hd L H ε hmargin

end
end PiExponent.CurveCycle

end OAI
end

theorem solution : type_of% @OAI.PiExponent.CurveCycle.tensor_euler_margin_q68_oai := @OAI.PiExponent.CurveCycle.tensor_euler_margin_q68_oai
