-- Prove2me | solution 1 for OAI.PiExponent.CurveCycle.zero_lengthNat_eq_component_sum_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:27:40.26883+00:00
-- url     : https://prove2.me/submissions/d82ced49-7c4a-4280-8bd9-b67a2de7b1a1

import Mathlib
import Definitions.Def_OAIQ068A041
import Definitions.Def_OAIQ068A042
import Theorems.Thm_OAI_PiExponentJets_W28_LocalIntersection_regular_ring_onecut_length_q68

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

theorem stalk_krullDimLE_one (X : Scheme.{0})
    (hd : topologicalKrullDim X ≤ 1) (x : X) :
    Ring.KrullDimLE 1 (X.presheaf.stalk x) := by
  apply Ring.krullDimLE_iff.mpr
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (X.fromSpecStalk x).isEmbedding.isInducing.topologicalKrullDim_le.trans hd

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

theorem zero_stalk_length_eq_minimalPrimeCutSum {X : Scheme.{0}}
    [IsLocallyNoetherian X] (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme)
    (hy : (SectionZeroIdeal.zeroIdeal L s).subschemeι y ∈ U.1) :
    Module.length ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y)
      ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y) =
    minimalPrimeCutSum (⊥ : Ideal
      (X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y)))
      (SectionZeroStalk.sectionGerm L s U e _ hy) := by
  let x := (SectionZeroIdeal.zeroIdeal L s).subschemeι y
  let A := X.presheaf.stalk x
  let c : A := SectionZeroStalk.sectionGerm L s U e x hy
  let := stalk_krullDimLE_one X hd x
  have hlen := SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (SectionZeroStalk.zeroStalkQuotientEquiv L s U e y hy)
  have hsc : Module.length A (A ⧸ Ideal.span {c}) =
      Module.length (A ⧸ Ideal.span {c}) (A ⧸ Ideal.span {c}) :=
    Module.length_eq_of_surjective (M := A ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective
  exact hlen.symm.trans (hsc.symm.trans
    (regular_ring_onecut_length_q68 c (sectionGerm_nonZeroDivisor L s U e x hy)))

theorem zero_stalk_length_ne_top {X : Scheme.{0}} [IsLocallyNoetherian X]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme) :
    Module.length ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y)
      ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y) ≠ ⊤ := by
  let x := (SectionZeroIdeal.zeroIdeal L s).subschemeι y
  obtain ⟨V,hxV,⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨W,hW,hxW,hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let U : X.affineOpens := ⟨W,hW⟩
  let e := restrictOpenFrame hWV eV
  let A := X.presheaf.stalk x
  let c : A := SectionZeroStalk.sectionGerm L s U e x hxW
  let := stalk_krullDimLE_one X hd x
  have hfinite : IsFiniteLength A (A ⧸ Ideal.span {c}) :=
    isFiniteLength_quotient_span_singleton A (sectionGerm_nonZeroDivisor L s U e x hxW)
  have hsc : Module.length A (A ⧸ Ideal.span {c}) =
      Module.length (A ⧸ Ideal.span {c}) (A ⧸ Ideal.span {c}) :=
    Module.length_eq_of_surjective (M := A ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective
  have hlen := SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (SectionZeroStalk.zeroStalkQuotientEquiv L s U e y hxW)
  rw [← hlen,← hsc]
  exact Module.length_ne_top_iff.mpr hfinite

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveComponentMultiplicity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

theorem generic_stalk_isArtinian {X : Scheme.{0}} [IsLocallyNoetherian X]
    (x : X) (hx : closure {x} ∈ irreducibleComponents X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  wlog hX : ∃ R : CommRingCat, X = Spec R
  · obtain ⟨i,x,rfl⟩ := X.affineCover.exists_eq x
    let hNoeth : IsLocallyNoetherian (X.affineCover.X i) :=
      LocallyOfFiniteType.isLocallyNoetherian (X.affineCover.f i)
    have hloc := this x (by
      rw [(X.affineCover.f i).isOpenEmbedding.closure_eq_preimage_closure_image,
        Set.image_singleton]
      exact preimage_mem_irreducibleComponents hx (X.affineCover.f i).isOpenEmbedding
        ⟨X.affineCover.f i x, subset_closure rfl, _, rfl⟩) ⟨_,rfl⟩
    let := hloc
    exact (asIso ((X.affineCover.f i).stalkMap x)).commRingCatIsoToRingEquiv.symm.isArtinianRing
  obtain ⟨R,rfl⟩ := hX
  let : IsNoetherianRing ((Spec R).presheaf.stalk x) := inferInstance
  change PrimeSpectrum R at x
  change closure {x} ∈ irreducibleComponents (PrimeSpectrum R) at hx
  have hp : x.asIdeal ∈ minimalPrimes R := by
    rwa [← PrimeSpectrum.vanishingIdeal_singleton,
      PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
  let : Ring.KrullDimLE 0 ((Spec R).presheaf.stalk x) := by
    exact Ring.KrullDimLE.of_isLocalization x.asIdeal hp ((Spec.structureSheaf R).presheaf.stalk x)
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

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

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_RegularComponentSection
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveLocalMultiplicity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem componentMultiplicity_cast {X : Scheme.{0}} [IsLocallyNoetherian X]
    (C : irreducibleComponents X) :
    (componentMultiplicity X C : ℕ∞) =
      Module.length (X.presheaf.stalk (genericPoints.ofComponent C).val)
        (X.presheaf.stalk (genericPoints.ofComponent C).val) := by
  let x := (genericPoints.ofComponent C).val
  let : IsArtinianRing (X.presheaf.stalk x) :=
    generic_stalk_isArtinian x (genericPoints.ofComponent C).property
  exact ENat.natCast_toNat Module.length_ne_top

theorem localMinimalPrime_length_eq_componentMultiplicity
    {X : Scheme.{0}} [IsLocallyNoetherian X] (x : X)
    (P : minimalPrimes (X.presheaf.stalk x)) :
    letI : P.val.IsPrime := P.property.1.1
    Module.length (Localization.AtPrime P.val) (Localization.AtPrime P.val) =
      (componentMultiplicity X (stalkMinimalPrimesEquivComponentsThrough X x P).val : ℕ∞) := by
  let : P.val.IsPrime := P.property.1.1
  rw [componentMultiplicity_cast]
  exact (SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (localMinimalPrimeGenericStalkIso X x P).commRingCatIsoToRingEquiv).symm

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveComponentLocalLengths
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentJets.W28.LocalIntersection
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

theorem minimalPrimeCutSum_eq_component_sum {X : Scheme.{0}} [IsLocallyNoetherian X]
    (x : X) (c : X.presheaf.stalk x) :
    letI : Fintype {C : irreducibleComponents X // x ∈ C.val} := Fintype.ofFinite _
    minimalPrimeCutSum (⊥ : Ideal (X.presheaf.stalk x)) c =
      ∑ C : {C : irreducibleComponents X // x ∈ C.val},
        (componentMultiplicity X C.val : ℕ∞) * componentLocalCutLength X x C c := by
  classical
  let : Fintype {C : irreducibleComponents X // x ∈ C.val} := Fintype.ofFinite _
  let : Fintype (minimalPrimes (X.presheaf.stalk x)) :=
    ((⊥ : Ideal (X.presheaf.stalk x)).finite_minimalPrimes_of_isNoetherianRing _).fintype
  unfold minimalPrimeCutSum
  apply Fintype.sum_equiv (stalkMinimalPrimesEquivComponentsThrough X x)
  intro P
  let : P.val.IsPrime := P.property.1.1
  rw [Ideal.map_bot]
  have hlength := SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (RingEquiv.quotientBot (Localization.AtPrime P.val))
  have hsc : Module.length (Localization.AtPrime P.val)
      (Localization.AtPrime P.val ⧸ (⊥ : Ideal (Localization.AtPrime P.val))) =
      Module.length (Localization.AtPrime P.val ⧸ (⊥ : Ideal (Localization.AtPrime P.val)))
        (Localization.AtPrime P.val ⧸ (⊥ : Ideal (Localization.AtPrime P.val))) :=
    Module.length_eq_of_surjective (M := Localization.AtPrime P.val ⧸
      (⊥ : Ideal (Localization.AtPrime P.val))) Ideal.Quotient.mk_surjective
  rw [hsc,hlength,localMinimalPrime_length_eq_componentMultiplicity x P]
  congr 1
  exact (congrArg (fun Q : minimalPrimes (X.presheaf.stalk x) =>
    Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ (Q.val ⊔ Ideal.span {c})))
    ((stalkMinimalPrimesEquivComponentsThrough X x).symm_apply_apply P)).symm

theorem zero_stalk_length_eq_component_sum {X : Scheme.{0}} [IsLocallyNoetherian X]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme)
    (hy : (SectionZeroIdeal.zeroIdeal L s).subschemeι y ∈ U.1) :
    let x := (SectionZeroIdeal.zeroIdeal L s).subschemeι y
    letI : Fintype {C : irreducibleComponents X // x ∈ C.val} := Fintype.ofFinite _
    Module.length ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y)
      ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y) =
      ∑ C : {C : irreducibleComponents X // x ∈ C.val},
        (componentMultiplicity X C.val : ℕ∞) * componentLocalCutLength X x C
          (SectionZeroStalk.sectionGerm L s U e x hy) := by
  exact (zero_stalk_length_eq_minimalPrimeCutSum hd L s U e y hy).trans
    (minimalPrimeCutSum_eq_component_sum _ _)

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveCutQuotient
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem cut_length_eq_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (a : A) :
    Module.length A (A ⧸ (RingHom.ker f ⊔ Ideal.span {a})) =
      Module.length B (B ⧸ Ideal.span {f a}) := by
  have hA : Module.length A (A ⧸ (RingHom.ker f ⊔ Ideal.span {a})) =
      Module.length (A ⧸ (RingHom.ker f ⊔ Ideal.span {a}))
        (A ⧸ (RingHom.ker f ⊔ Ideal.span {a})) :=
    Module.length_eq_of_surjective
      (M := A ⧸ (RingHom.ker f ⊔ Ideal.span {a})) Ideal.Quotient.mk_surjective
  have hB : Module.length B (B ⧸ Ideal.span {f a}) =
      Module.length (B ⧸ Ideal.span {f a}) (B ⧸ Ideal.span {f a}) :=
    Module.length_eq_of_surjective
      (M := B ⧸ Ideal.span {f a}) Ideal.Quotient.mk_surjective
  exact hA.trans ((SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (cutQuotientEquivOfSurjective f hf a)).trans hB.symm)

theorem reducedComponent_cut_length (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) (a : X.presheaf.stalk (reducedComponentι X C z)) :
    Module.length (X.presheaf.stalk (reducedComponentι X C z))
      ((X.presheaf.stalk (reducedComponentι X C z)) ⧸
        ((reducedComponentStalkPrime X C z).val ⊔ Ideal.span {a})) =
      Module.length ((reducedComponent X C).presheaf.stalk z)
        (((reducedComponent X C).presheaf.stalk z) ⧸
          Ideal.span {(reducedComponentι X C).stalkMap z a}) := by
  rw [← reducedComponentι_stalkMap_ker]
  exact cut_length_eq_of_surjective ((reducedComponentι X C).stalkMap z).hom
    ((reducedComponentι X C).stalkMap_surjective z) a

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveComponentCutLengths
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.SectionZeroStalk

theorem componentLocalCutLength_eq_zero_stalk {X : Scheme.{0}}
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    (z : (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hy : (zeroIdeal L s).subschemeι (componentZeroToGlobal L s C z) ∈ U.1) :
    componentLocalCutLength X ((zeroIdeal L s).subschemeι (componentZeroToGlobal L s C z))
      ⟨C,componentZeroToGlobal_mem L s C z⟩
      (sectionGerm L s U e _ hy) =
    Module.length ((zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk z)
      ((zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk z) := by
  let i := reducedComponentι X C
  let J := zeroIdeal (L.pullback i) (pullbackSection i s)
  let y := J.subschemeι z
  let a := sectionGerm L s U e (i y) hy
  obtain ⟨eF,heF⟩ := exists_pullback_frame_sectionGerm i L s U e
  let V : (reducedComponent X C).affineOpens := ⟨i ⁻¹ᵁ U.1,U.2.preimage i⟩
  let b := sectionGerm (L.pullback i) (pullbackSection i s) V eF y hy
  have hb : b = i.stalkMap y a := heF y hy
  have hcut := reducedComponent_cut_length X C y a
  change componentLocalCutLength X (i y) ⟨C,reducedComponentι_mem X C y⟩ a =
    Module.length (J.subscheme.presheaf.stalk z) (J.subscheme.presheaf.stalk z)
  change Module.length (X.presheaf.stalk (i y))
    ((X.presheaf.stalk (i y)) ⧸ ((reducedComponentStalkPrime X C y).val ⊔ Ideal.span {a})) = _
  rw [hcut,← hb]
  have hsc : Module.length ((reducedComponent X C).presheaf.stalk y)
      (((reducedComponent X C).presheaf.stalk y) ⧸ Ideal.span {b}) =
    Module.length (((reducedComponent X C).presheaf.stalk y) ⧸ Ideal.span {b})
      (((reducedComponent X C).presheaf.stalk y) ⧸ Ideal.span {b}) :=
    Module.length_eq_of_surjective (M := ((reducedComponent X C).presheaf.stalk y) ⧸
      Ideal.span {b}) Ideal.Quotient.mk_surjective
  exact hsc.trans (intrinsic_length_eq_of_ringEquiv
    (zeroStalkQuotientEquiv (L.pullback i) (pullbackSection i s) V eF z hy))

theorem componentLocalCutLength_eq_zero_stalk_at {X : Scheme.{0}}
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    (t : {y : (zeroIdeal L s).subscheme // (zeroIdeal L s).subschemeι y ∈ C.val})
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hy : (zeroIdeal L s).subschemeι t.val ∈ U.1) :
    componentLocalCutLength X ((zeroIdeal L s).subschemeι t.val) ⟨C,t.property⟩
      (sectionGerm L s U e _ hy) =
    Module.length ((zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk
        ((componentZeroPointEquiv L s C).symm t))
      ((zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk
          ((componentZeroPointEquiv L s C).symm t)) := by
  obtain ⟨z,rfl⟩ := (componentZeroPointEquiv L s C).surjective t
  exact (componentLocalCutLength_eq_zero_stalk L s C z U e hy).trans
    (congrArg (fun w : (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme =>
      Module.length ((zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk w)
        ((zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk w))
      ((componentZeroPointEquiv L s C).symm_apply_apply z)).symm

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveComponentIncidence
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem sum_component_zero_incidence {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Fintype (irreducibleComponents X)]
    [Fintype (zeroIdeal L s).subscheme]
    {R : Type*} [AddCommMonoid R]
    (w : ∀ C : irreducibleComponents X,
      (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme → R) :
    letI : ∀ y : (zeroIdeal L s).subscheme,
      Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
        fun _ => Fintype.ofFinite _
    letI : ∀ C : irreducibleComponents X,
      Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme :=
        fun _ => Fintype.ofFinite _
    (∑ y : (zeroIdeal L s).subscheme,
      ∑ C : {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val},
        w C.val ((componentZeroPointEquiv L s C.val).symm ⟨y,C.property⟩)) =
      ∑ C : irreducibleComponents X, ∑ z, w C z := by
  classical
  let : ∀ y : (zeroIdeal L s).subscheme,
    Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
      fun _ => Fintype.ofFinite _
  let : ∀ C : irreducibleComponents X,
    Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme :=
        fun _ => Fintype.ofFinite _
  let a : (Σ y : (zeroIdeal L s).subscheme,
      {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val}) → R :=
    fun p => w p.2.val ((componentZeroPointEquiv L s p.2.val).symm ⟨p.1,p.2.property⟩)
  let b : (Σ C : irreducibleComponents X,
      (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme) → R :=
    fun q => w q.1 q.2
  exact (Fintype.sum_sigma a).symm.trans
    ((Fintype.sum_equiv (sectionZeroIncidenceEquiv L s) a b (fun _ => rfl)).trans
      (Fintype.sum_sigma b))

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveCycleLengths
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal

theorem zero_stalk_lengthNat_eq_component_sum {X : Scheme.{0}} [IsLocallyNoetherian X]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (y : (zeroIdeal L s).subscheme) :
    letI : Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
      Fintype.ofFinite _
    (stalkLength (zeroIdeal L s).subscheme y).toNat =
      ∑ C : {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val},
        componentMultiplicity X C.val *
          (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C.val))
            (pullbackSection (reducedComponentι X C.val) s)).subscheme
              ((componentZeroPointEquiv L s C.val).symm ⟨y,C.property⟩)).toNat := by
  classical
  let : Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
    Fintype.ofFinite _
  let f := fun C : {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} =>
    (componentMultiplicity X C.val : ℕ∞) *
      stalkLength (zeroIdeal (L.pullback (reducedComponentι X C.val))
        (pullbackSection (reducedComponentι X C.val) s)).subscheme
          ((componentZeroPointEquiv L s C.val).symm ⟨y,C.property⟩)
  have hlocal : stalkLength (zeroIdeal L s).subscheme y = ∑ C, f C := by
    obtain ⟨U,hy,⟨e⟩,_⟩ := common_affine_frames L L ((zeroIdeal L s).subschemeι y)
    refine (zero_stalk_length_eq_component_sum hd L s U e y hy).trans ?_
    apply Finset.sum_congr rfl
    intro C _
    exact congrArg (fun n : ℕ∞ => (componentMultiplicity X C.val : ℕ∞) * n)
      (componentLocalCutLength_eq_zero_stalk_at L s C.val ⟨y,C.property⟩ U e hy)
  have hsum : ∑ C, f C ≠ ⊤ := by
    rw [← hlocal]
    exact zero_stalk_length_ne_top hd L s y
  have hn := congrArg ENat.toNat hlocal
  rw [ENat.toNat_sum (ENat.sum_ne_top.mp hsum)] at hn
  simpa only [f,ENat.toNat_mul,ENat.toNat_natCast] using hn

theorem zero_lengthNat_eq_component_sum_q68_oai {X : Scheme.{0}} [IsLocallyNoetherian X]
    [Fintype (irreducibleComponents X)] (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    [Fintype (zeroIdeal L s).subscheme] :
    letI : ∀ C : irreducibleComponents X,
      Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme := fun _ => Fintype.ofFinite _
    (∑ y : (zeroIdeal L s).subscheme, (stalkLength (zeroIdeal L s).subscheme y).toNat) =
      ∑ C : irreducibleComponents X, componentMultiplicity X C *
        ∑ z, (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat := by
  classical
  let : ∀ C : irreducibleComponents X,
    Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme := fun _ => Fintype.ofFinite _
  let : ∀ y : (zeroIdeal L s).subscheme,
    Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
      fun _ => Fintype.ofFinite _
  calc
    (∑ y : (zeroIdeal L s).subscheme, (stalkLength (zeroIdeal L s).subscheme y).toNat) =
        ∑ y : (zeroIdeal L s).subscheme,
          ∑ C : {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val},
            componentMultiplicity X C.val *
              (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C.val))
                (pullbackSection (reducedComponentι X C.val) s)).subscheme
                  ((componentZeroPointEquiv L s C.val).symm ⟨y,C.property⟩)).toNat :=
      Finset.sum_congr rfl (fun y _ => zero_stalk_lengthNat_eq_component_sum hd L s y)
    _ = ∑ C : irreducibleComponents X, ∑ z,
        componentMultiplicity X C *
          (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
            (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat :=
      sum_component_zero_incidence L s (fun C z => componentMultiplicity X C *
        (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat)
    _ = _ := Finset.sum_congr rfl (fun C _ => (Finset.mul_sum _ _ _).symm)

end
end PiExponent.CurveCycle

end OAI
end

theorem solution : type_of% @OAI.PiExponent.CurveCycle.zero_lengthNat_eq_component_sum_q68_oai := @OAI.PiExponent.CurveCycle.zero_lengthNat_eq_component_sum_q68_oai
