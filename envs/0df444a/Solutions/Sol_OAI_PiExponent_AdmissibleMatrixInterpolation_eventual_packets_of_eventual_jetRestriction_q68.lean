-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleMatrixInterpolation.eventual_packets_of_eventual_jetRestriction_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:41:45.665305+00:00
-- url     : https://prove2.me/submissions/2b1c7eb9-4628-46d5-804c-9f7dc6421b9c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_AdmissibleJetPackets_formalPackets_surjective_of_jetRestriction_q68
import Theorems.Thm_OAI_PiExponent_ProjectiveSectionExtension_eventual_projective_pullbackPowerSection_surjective_q68
import Theorems.Thm_OAI_PiExponent_WeightedPullbackDegree_pullback_supportBound_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveMonomialCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveMonomialCech

noncomputable section

open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [AddCommGroup K]

theorem exists_nonnegative_coordinate [Nonempty ι] {d : ℤ}
    (hd : 0 ≤ d) (a : Monomial ι d) : ∃ i, 0 ≤ a.val i := by
  by_contra h
  have hneg : ∀ i, a.val i < 0 := fun i => lt_of_not_ge (fun hi => h ⟨i, hi⟩)
  have htotal : (∑ i, a.val i) < 0 :=
    Finset.sum_neg (fun i _ => hneg i) Finset.univ_nonempty
  rw [a.property] at htotal
  exact (not_lt_of_ge hd) htotal

end
end PiExponent.ProjectiveMonomialCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveLaurentVertex
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.ProjectiveLaurentVertex

section

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech

variable {ι : Type*} [Fintype ι]

variable {R : Type*} [CommRing R]

theorem vertexLaurent_injective (i : ι) (d : ℤ) :
    Function.Injective (vertexLaurent (R := R) i d) :=
  Subtype.val_injective.comp (vertexPolynomialEquiv i d).injective

end

section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

theorem groupAlgebraToLaurent_polynomial (i : ι) (d : ℤ)
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    groupAlgebraToLaurent i d (polynomialToGroupAlgebra i p) = vertexLaurent i d p := by
  induction p using MvPolynomial.induction_on'
  case add a b ha hb =>
    simp only [map_add, ha, hb]
  case monomial b r =>
    rw [vertexLaurent_monomial]
    change groupAlgebraToLaurent i d
      (AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single b r)) = _
    rw [AddMonoidAlgebra.mapDomain_single]
    simp [groupAlgebraToLaurent, fullExponentEquiv]
    rfl

@[simp] theorem overlapLaurent_base (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i})
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    overlapLaurent i d s (algebraMap _ _ p) = vertexLaurent i d p := by
  change groupAlgebraToLaurent i d (overlapToGroupAlgebra i s (algebraMap _ _ p)) = _
  rw [overlapToGroupAlgebra_base, groupAlgebraToLaurent_polynomial]

end

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
end PiExponent.GeometrySupport.ProjectiveLaurentVertex

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_WeightedProjectiveEmbedding
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_diagonal_affine _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_noetherian _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_separated _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.WeightedCompactification.affineChartMap_isOpenImmersion _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective PiExponentSeshadri.Frames

variable {R ι σ : Type} [CommRing R]

theorem coordinateSection_isoOpen (a : σ → ι →₀ ℕ) (i : σ) :
    PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) a i) =
      Proj.basicOpen (imageGrade a) (imageCoordinate a i) := by
  have h := pullback_isoOpen_eq (ProjectiveO1.lineBundle (R := R) (σ := σ))
    (ProjectiveO1.coordinateSection i) (projectiveMonomialMap a)
  rw [ProjectiveO1.coordinateSection_isoOpen] at h
  exact h

end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedCompactificationGeometry
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial AlgebraicGeometry CategoryTheory Topology

universe u
variable {R ι σ : Type u} [CommRing R]

theorem affineChartMap_range (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Set.range (affineChartMap (R := R) a z hz coordinate hcoordinate) =
      (Proj.basicOpen (imageGrade (R := R) a) (imageCoordinate a z) : Set (Proj (imageGrade (R := R) a))) := by
  let e := constantProjectiveChartIso (R := R) a z hz coordinate hcoordinate
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (e.inv y).2
  · intro hx
    refine ⟨e.hom ⟨x, hx⟩, ?_⟩
    change ((e.hom ≫ e.inv) ⟨x, hx⟩).1 = x
    simp only [Iso.hom_inv_id]
    rfl

end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_WeightedAffineFrame
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedAffineFrame
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective PiExponentSeshadri.Frames
open PiExponent.WeightedCompactification

theorem frame_nonempty_of_isoOpen_eq {X : Scheme} (M : X.Modules)
    (s : O X ⟶ M) (U : X.Opens) (h : PiExponentSeshadri.SectionOpens.isoOpen s = U) :
    Nonempty (M.restrict U.ι ≅ O U.toScheme) := by
  subst U
  exact ⟨sectionFrame s⟩

variable {R ι σ : Type} [CommRing R]

attribute [local irreducible] WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap WeightedCompactification.coordinateSection

theorem affineChart_isoOpen (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) a z) =
      (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange := by
  rw [coordinateSection_isoOpen]
  apply TopologicalSpace.Opens.ext
  exact (affineChartMap_range (R := R) a z hz coordinate hcoordinate).symm

theorem affineFrame_nonempty (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Nonempty ((lineBundle (R := R) a).sheaf.restrict
      (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange.ι ≅
        O (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange.toScheme) :=
  frame_nonempty_of_isoOpen_eq (lineBundle (R := R) a).sheaf (coordinateSection (R := R) a z)
    (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange
    (affineChart_isoOpen (R := R) a z hz coordinate hcoordinate)

end
end PiExponent.WeightedAffineFrame

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AdmissibleMatrixFrame
attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleMatrixInterpolation
open AdmissibleBlowupGeometry AlgebraicGeometry CategoryTheory PiExponentSeshadri.Geometry
attribute [local irreducible] WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap
  AffineJetCoefficientInterface.Frame

theorem frame_exists_of_actual {X : Scheme} {R : Type} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j] (A : LineBundle X)
    (h : Nonempty (A.sheaf.restrict j.opensRange.ι ≅
      structureSheaf j.opensRange.toScheme)) :
    Nonempty (AffineJetCoefficientInterface.Frame j A) := by
  unfold AffineJetCoefficientInterface.Frame
  exact h

theorem monomialFrame_exists {R ι σ : Type} [CommRing R]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Nonempty (AffineJetCoefficientInterface.Frame
      (WeightedCompactification.affineChartMap (R := R) a z hz coordinate hcoordinate)
      (WeightedCompactification.lineBundle (R := R) a)) := by
  exact frame_exists_of_actual
    (X := Proj (WeightedCompactification.imageGrade (R := R) a))
    (R := MvPolynomial ι R)
    (WeightedCompactification.affineChartMap (R := R) a z hz coordinate hcoordinate)
    (WeightedCompactification.lineBundle (R := R) a)
    (WeightedAffineFrame.affineFrame_nonempty (R := R) a z hz coordinate hcoordinate)

theorem actualFrame_exists {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D) :
    Nonempty (AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d)) := by
  exact monomialFrame_exists (R := ℂ)
    (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)
end PiExponent.AdmissibleMatrixInterpolation

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AdmissibleMatrixInterpolation
attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleMatrixInterpolation
open Filter
open DeterminantContradiction AdmissibleBlowupGeometry
variable {ν : ℝ} (d : FixedData ν)

theorem packetMap_surjective_of_family {α : Type*} (n : ℕ)
    (P : α → PiExponentApprox.FramePolynomial d.m)
    (hdegree : ∀ a, WeightedSliceDegree.SupportBound
      (fun i => (d.curveDegreeWeights i : ℝ)) ((n : ℝ) * (scale d).radius) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin d.K =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights
        ((n : ℚ) * (scale d).radius) (FormalLogJet.formalJet (d.curveCenters j) (P a)))) :
    Function.Surjective (packetMap d n) := by
  intro y
  obtain ⟨a,ha⟩ := hpacket y
  exact ⟨⟨P a,hdegree a⟩,ha⟩

end PiExponent.AdmissibleMatrixInterpolation

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GradedSerre
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedSerre

noncomputable section
open scoped BigOperators

variable {R M ι σ : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq ι] [SetLike σ M] [AddSubmonoidClass σ M]
  (𝓜 : ι → σ) [DirectSum.Decomposition 𝓜]

section FreeTwistCech
open ProjectiveMonomialCech ProjectiveMonomialCechHigher
variable {J C B : Type*} [Fintype J] [Fintype C] [AddCommGroup B]

theorem compatible_vertices_are_polynomial [Nonempty C] {d : ℤ} (hd : 0 ≤ d)
    (c : C → Laurent C B d) (hc : ∀ j, RegularOn {j} (c j))
    (heq : ∀ i j, c i = c j) :
    ∃ f : Laurent C B d, RegularOn ∅ f ∧ ∀ j, c j = f := by
  classical
  let p : C := Classical.choice inferInstance
  refine ⟨c p, ?_, fun j => heq j p⟩
  intro a ha k hk
  obtain ⟨j, hj⟩ := exists_nonnegative_coordinate hd a
  have hcoeff : c j a ≠ 0 := by rw [heq j p]; exact ha
  have hkj := hc j a hcoeff k hk
  have hkj' : k = j := hkj
  exact False.elim ((not_lt_of_ge hj) (hkj' ▸ hk))

end FreeTwistCech

end
end PiExponent.GradedSerre

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedH0
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedH0
noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

theorem mem_supported_iff_regular (d : ℤ) (p : Laurent ι R d) :
    p ∈ Finsupp.supported R R (NonnegativeMonomialSet d) ↔ RegularOn ∅ p := by
  classical
  rw [Finsupp.mem_supported]
  constructor
  · intro hp a ha j hj
    exact False.elim ((not_lt_of_ge (hp (Finsupp.mem_support_iff.mpr ha) j)) hj)
  · intro hp a ha j
    by_contra hneg
    exact hp a (Finsupp.mem_support_iff.mp ha) j (lt_of_not_ge hneg)

theorem polynomialLaurent_injective (n : ℕ) :
    Function.Injective (polynomialLaurent (ι := ι) (R := R) n) :=
  Subtype.val_injective.comp (homogeneousPolynomialEquiv n).injective

theorem existsUnique_polynomial_of_regular (n : ℕ) (f : Laurent ι R (n : ℤ))
    (hf : RegularOn ∅ f) :
    ∃! p : MvPolynomial.homogeneousSubmodule ι R n, polynomialLaurent n p = f := by
  let a : Finsupp.supported R R (NonnegativeMonomialSet (ι := ι) (n : ℤ)) :=
    ⟨f, (mem_supported_iff_regular _ _).mpr hf⟩
  refine ⟨(homogeneousPolynomialEquiv n).symm a, ?_, ?_⟩
  · change ((homogeneousPolynomialEquiv n) ((homogeneousPolynomialEquiv n).symm a)).val = f
    rw [LinearEquiv.apply_symm_apply]
  · intro p hp
    apply polynomialLaurent_injective n
    rw [hp]
    change f = ((homogeneousPolynomialEquiv n) ((homogeneousPolynomialEquiv n).symm a)).val
    rw [LinearEquiv.apply_symm_apply]

theorem existsUnique_polynomial_of_compatible_vertices [Nonempty ι] (n : ℕ)
    (c : ι → Laurent ι R (n : ℤ)) (hc : ∀ j, RegularOn {j} (c j))
    (heq : ∀ i j, c i = c j) :
    ∃! p : MvPolynomial.homogeneousSubmodule ι R n,
      ∀ j, polynomialLaurent n p = c j := by
  obtain ⟨f, hf, hcf⟩ := GradedSerre.compatible_vertices_are_polynomial
    (Int.natCast_nonneg n) c hc heq
  obtain ⟨p, hp, huniq⟩ := existsUnique_polynomial_of_regular n f hf
  refine ⟨p, fun j => hp.trans (hcf j).symm, ?_⟩
  intro q hq
  exact huniq q ((hq (Classical.choice inferInstance)).trans (hcf _))

theorem zeroth_cocycle_vertices_eq {d : ℤ}
    (c : ProjectiveMonomialCechHigher.Cochain ι (Laurent ι R d) 0)
    (hc : ProjectiveMonomialCechHigher.differential c = 0) (i j : ι) :
    c (fun _ => i) = c (fun _ => j) := by
  have h := congrFun hc (![i, j] : Fin 2 → ι)
  simp only [ProjectiveMonomialCechHigher.differential, Fin.sum_univ_succ,
    Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, Fin.sum_univ_zero,
    add_zero, Nat.zero_add, pow_one, neg_one_zsmul, Pi.zero_apply] at h
  have hi : (![i, j] : Fin 2 → ι) ∘ (0 : Fin 2).succAbove = (fun _ => j) := by
    funext k
    fin_cases k
    rfl
  have hj : (![i, j] : Fin 2 → ι) ∘ (Fin.succ (0 : Fin 1)).succAbove = (fun _ => i) := by
    funext k
    fin_cases k
    rfl
  rw [hi, hj] at h
  exact (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)).symm

theorem zeroth_cocycle_unique_homogeneous_polynomial [Nonempty ι] (n : ℕ)
    (c : ProjectiveMonomialCechHigher.Cochain ι (Laurent ι R (n : ℤ)) 0)
    (hreg : ProjectiveMonomialCechHigher.Regular c)
    (hc : ProjectiveMonomialCechHigher.differential c = 0) :
    ∃! p : MvPolynomial.homogeneousSubmodule ι R n,
      ∀ t, polynomialLaurent n p = c t := by
  have hreg' (j : ι) : RegularOn {j} (c (fun _ => j)) := by
    have h := hreg (fun _ => j)
    simpa only [Set.range_const] using h
  obtain ⟨p, hp, hu⟩ := existsUnique_polynomial_of_compatible_vertices n
    (fun j => c (fun _ => j)) hreg' (zeroth_cocycle_vertices_eq c hc)
  refine ⟨p, ?_, ?_⟩
  · intro t
    have ht : t = fun _ => t 0 := by
      funext i
      exact congrArg t (show i = 0 by omega)
    rw [ht]
    exact hp (t 0)
  · intro q hq
    exact hu q (fun j => hq (fun _ => j))

end
end PiExponent.GradedH0

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveGlobalPolynomialAlgebra
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra
noncomputable section
open scoped BigOperators
open MvPolynomial
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponentSeshadri.Projective


variable {σ K : Type*} [Fintype σ] [CommRing K]

theorem dehomogenize_monomial (i : σ) (b : σ →₀ ℕ) (r : K) :
    dehomogenize i (MvPolynomial.monomial b r) =
      MvPolynomial.monomial (chartExponent i b) r := by
  classical
  rw [dehomogenize, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq]
  congr 1
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp
    apply Finset.prod_congr rfl
    intro j _
    simp [j.property]
  · intro j
    simp
  · intro j
    simp

theorem encode_chartExponent (i : σ) (n : ℕ) (b : σ →₀ ℕ) (hb : b.degree = n) :
    ProjectiveLaurentVertex.encode i (n : ℤ) (chartExponent i b) =
      GradedH0.encode n ⟨b, hb⟩ := by
  classical
  apply Subtype.ext
  funext j
  by_cases hj : j = i
  · subst j
    rw [ProjectiveLaurentVertex.encode_self]
    erw [GradedH0.encode_apply]
    have hs : (b i : ℤ) + ∑ j : ChartVariables i, (b j.val : ℤ) = n := by
      rw [← Fintype.sum_eq_add_sum_subtype_ne (fun j => (b j : ℤ)) i,
        ← Nat.cast_sum, ← Finsupp.degree_eq_sum, hb]
    simpa only [chartExponent_apply] using (eq_sub_iff_add_eq.mpr hs).symm
  · change (ProjectiveLaurentVertex.encode i (n : ℤ) (chartExponent i b)).val
      (⟨j, hj⟩ : ChartVariables i) = _
    exact ProjectiveLaurentVertex.encode_other i (n : ℤ) (chartExponent i b) ⟨j, hj⟩

theorem polynomialLaurent_monomial (n : ℕ) (b : σ →₀ ℕ) (hb : b.degree = n) (r : K) :
    GradedH0.polynomialLaurent n ⟨MvPolynomial.monomial b r,
      MvPolynomial.isHomogeneous_monomial r hb⟩ =
      Finsupp.single (GradedH0.encode n ⟨b, hb⟩) r := by
  classical
  simp [GradedH0.polynomialLaurent, GradedH0.homogeneousPolynomialEquiv,
    MvPolynomial.monomial, GradedH0.exponentEquiv,
    AddMonoidAlgebra.supportedEquivFinsupp]
  have hs : (Finsupp.supportedEquivFinsupp (R := K) {b : σ →₀ ℕ | b.degree = n})
      ⟨Finsupp.single b r, Finsupp.single_mem_supported K r hb⟩ =
      Finsupp.single ⟨b, hb⟩ r := by
    apply (Finsupp.supportedEquivFinsupp (R := K) {b : σ →₀ ℕ | b.degree = n}).symm.injective
    apply Subtype.ext
    simp
  change (Finsupp.domLCongr (GradedH0.exponentEquiv n)
    ((Finsupp.supportedEquivFinsupp (R := K) {b : σ →₀ ℕ | b.degree = n})
      ⟨Finsupp.single b r, Finsupp.single_mem_supported K r hb⟩)).extendDomain = _
  rw [hs]
  change (Finsupp.domLCongr (GradedH0.exponentEquiv n)
    (Finsupp.single (⟨b, hb⟩ : GradedH0.PolynomialExponent (ι := σ) n) r)).extendDomain = _
  erw [Finsupp.domLCongr_single, Finsupp.extendDomain_single]
  rfl

theorem vertexLaurent_dehomogenize (i : σ) (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ K n) :
    vertexLaurent i (n : ℤ) (dehomogenize i p.val) = GradedH0.polynomialLaurent n p := by
  rcases p with ⟨p, hp⟩
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    change vertexLaurent i (n : ℤ) (dehomogenize i 0) = GradedH0.polynomialLaurent n 0
    simp only [map_zero]
  | add p q hp hq ihp ihq =>
    change vertexLaurent i (n : ℤ) (dehomogenize i (p + q)) =
      GradedH0.polynomialLaurent n (⟨p, hp⟩ + ⟨q, hq⟩)
    rw [map_add, map_add, map_add, ihp, ihq]
  | monomial b r hb =>
    have hd : b.degree = n := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hb
    rw [dehomogenize_monomial, vertexLaurent_monomial,
      polynomialLaurent_monomial n b hd r, encode_chartExponent i n b hd]

end
end PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveVertexCompatibility
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveTupleCharts

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)

lemma coordinatePowerOverlap_restrictVertex (n : ℕ) (i : σ)
    (a : Finset (ChartVariables i))
    (b : freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s i)) ⟶ modulePow X M n) :
    coordinatePowerOverlap M s k hc f hf n i a
      (freeOpenMap X.ringCatSheaf (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)) ≫ b) =
      coordinatePowerVertex M k s hc f hf n i b := by
  change overlapLaurent i (n : ℤ) a
    (coordinateFiniteRingEquiv M s k hc f hf i a
      (framedHomCoefficientsEquiv _ (modulePow X M n)
        (restrictOpenFrame inf_le_left (coordinatePowerFrame (s i) n))
        (freeOpenMap X.ringCatSheaf (homOfLE _) ≫ b))) =
    vertexLaurent i (n : ℤ) (coordinateSectionRingEquiv M k s hc f hf i
      (framedHomCoefficientsEquiv _ (modulePow X M n) (coordinatePowerFrame (s i) n) b))
  erw [framedHomCoefficientsEquiv_restrict]
  erw [coordinateFiniteRingEquiv_restrict_apply M s k hc f hf i a]
  exact overlapLaurent_base i (n : ℤ) a _

lemma coordinateTupleCoefficient_restrictVertex (n q : ℕ) (t : Fin (q+1) → σ)
    (b : freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s (t 0))) ⟶ modulePow X M n) :
    coordinateTupleCoefficient M s k hc f hf n q t
      (freeOpenMap X.ringCatSheaf (homOfLE
        (iInf_le (fun j => SectionOpens.isoOpen (s (t j))) 0)) ≫ b) =
      coordinatePowerVertex M k s hc f hf n (t 0) b := by
  change coordinatePowerOverlap M s k hc f hf n (t 0) (tupleVariables t 0)
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)
      (freeOpenMap X.ringCatSheaf (homOfLE _) ≫ b)) = _
  have h : freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)
      (freeOpenMap X.ringCatSheaf (homOfLE
        (iInf_le (fun j => SectionOpens.isoOpen (s (t j))) 0)) ≫ b) =
      freeOpenMap X.ringCatSheaf (homOfLE (show coordinateFiniteOpen M s (t 0)
        (tupleVariables t 0) ≤ SectionOpens.isoOpen (s (t 0)) from inf_le_left)) ≫ b := by
    change freeOpenMap X.ringCatSheaf _ ≫ (freeOpenMap X.ringCatSheaf _ ≫ b) = _
    simp only [freeOpenMap]
    erw [← Functor.map_comp_assoc, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  rw [h]
  exact coordinatePowerOverlap_restrictVertex M s k hc f hf n (t 0) (tupleVariables t 0) b

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveGlobalPolynomials
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_diagonal_affine _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_noetherian _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_separated _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveGlobalPolynomials
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
open GeometrySupport ProjectiveTwistCech ProjectiveMonomialCech

variable {X : Scheme.{0}} {σ R : Type} [CommRing R] [Fintype σ]
variable {U : σ → X.Opens} {M : X.Modules} {n : ℕ}

lemma globalLaurent_closed (P : LaurentCechPresentation (K := R) U M (n : ℤ))
    (b : structureSheaf X ⟶ M) :
    ProjectiveMonomialCechHigher.differential (globalLaurent P b) = 0 := by
  rw [globalLaurent, ← P.toLaurent_differential]
  rw [globalCochain]
  erw [CechHigher.augmentation_closed]
  funext t
  exact map_zero _

theorem existsUnique_polynomial [Nonempty σ] (P : LaurentCechPresentation (K := R) U M (n : ℤ))
    (b : structureSheaf X ⟶ M) :
    ∃! p : MvPolynomial.homogeneousSubmodule σ R n,
      ∀ t, GradedH0.polynomialLaurent n p = globalLaurent P b t := by
  exact GradedH0.zeroth_cocycle_unique_homogeneous_polynomial n (globalLaurent P b)
    (fun t => P.regular 0 t _) (globalLaurent_closed P b)

omit [Fintype σ] in
lemma globalCochain_restrict (U : σ → X.Opens) (N : X.Modules)
    (b : structureSheaf X ⟶ N) (t : Fin 1 → σ) :
    globalCochain U N b t = freeOpenMap X.ringCatSheaf
      (homOfLE (iInf_le (fun j => U (t j)) 0)) ≫ representedRestriction (U (t 0)) N b := by
  change freeOpenMap X.ringCatSheaf _ ≫ _ = freeOpenMap X.ringCatSheaf _ ≫
    (freeOpenMap X.ringCatSheaf _ ≫ _)
  simp only [freeOpenMap]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp, ← Functor.map_comp]
  rfl

open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open GeometrySupport.ProjectiveCoordinateAcyclicity GeometrySupport.ProjectiveTupleCharts
open GeometrySupport.ProjectiveLaurentVertex GeometrySupport.ProjectiveGlobalPolynomialAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra
variable (L : X.Modules) (s : σ → (structureSheaf X ⟶ L)) (k : R →+* Γ(X,⊤))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade R σ)) (hf : sectionsMorphism k s hc = f.hom)

lemma coordinate_globalLaurent_vertex (n : ℕ)
    (b : structureSheaf X ⟶ modulePow X L n) (t : Fin 1 → σ) :
    globalLaurent (coordinateLaurentCechPresentation L s k hc f hf n) b t =
      vertexLaurent (t 0) (n : ℤ) (coordinateChartPolynomial L s k hc f hf n (t 0) b) := by
  change coordinateTupleCoefficient L s k hc f hf n 0 t
    (globalCochain (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) _ b t) = _
  rw [globalCochain_restrict]
  exact coordinateTupleCoefficient_restrictVertex L s k hc f hf n 0 t _

theorem coordinate_existsUnique_polynomial [Nonempty σ] (n : ℕ)
    (b : structureSheaf X ⟶ modulePow X L n) :
    ∃! p : MvPolynomial.homogeneousSubmodule σ R n,
      ∀ i, dehomogenize i p.val = coordinateChartPolynomial L s k hc f hf n i b := by
  obtain ⟨p, hp, hu⟩ := existsUnique_polynomial
    (coordinateLaurentCechPresentation L s k hc f hf n) b
  refine ⟨p, ?_, ?_⟩
  · intro i
    apply vertexLaurent_injective i (n : ℤ)
    rw [vertexLaurent_dehomogenize]
    exact (hp (fun _ => i)).trans (coordinate_globalLaurent_vertex L s k hc f hf n b _)
  · intro q hq
    apply hu q
    intro t
    calc
      GradedH0.polynomialLaurent n q = vertexLaurent (t 0) (n : ℤ)
          (dehomogenize (t 0) q.val) := (vertexLaurent_dehomogenize (t 0) n q).symm
      _ = vertexLaurent (t 0) (n : ℤ)
          (coordinateChartPolynomial L s k hc f hf n (t 0) b) := congrArg _ (hq (t 0))
      _ = _ := (coordinate_globalLaurent_vertex L s k hc f hf n b t).symm


end
end PiExponent.ProjectiveGlobalPolynomials

namespace PiExponent.ProjectiveO1
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveGlobalPolynomials
attribute [local irreducible] lineBundle coordinateSection scalars sectionsMorphism
variable {R σ : Type} [CommRing R] [Fintype σ]

theorem globalSection_homogeneous_polynomial [Nonempty σ] (n : ℕ)
    (b : structureSheaf (projectiveSpace R σ) ⟶
      modulePow (projectiveSpace R σ) (lineBundle (R := R) (σ := σ)).sheaf n) :
    ∃! p : MvPolynomial.homogeneousSubmodule σ R n,
      ∀ i, dehomogenize i p.val = globalSectionChartPolynomial n i b := by
  exact coordinate_existsUnique_polynomial (X := projectiveSpace R σ) (R := R) (σ := σ)
    (lineBundle (R := R) (σ := σ)).sheaf (coordinateSection (R := R) (σ := σ))
    (scalars (R := R) (σ := σ)) (coordinateSection_cover (R := R) (σ := σ))
    (Iso.refl (projectiveSpace R σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) n b

end
end PiExponent.ProjectiveO1

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSectionPullback
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveSectionExtension
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X Y : Scheme.{0}}

theorem eventual_projective_homogeneous_extension
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n →
      ∀ t : GlobalSections X (modulePow X
        ((ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback f).sheaf n),
      ∃ s : GlobalSections (ProjectiveO1.projectiveSpace R σ)
          (modulePow _ (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf n),
        ∃ p : MvPolynomial.homogeneousSubmodule σ R n,
          pullbackPowerSection (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n s = t ∧
          ∀ i, PiExponentSeshadri.Projective.dehomogenize i p.val =
            ProjectiveO1.globalSectionChartPolynomial n i s := by
  obtain ⟨N, hN⟩ := eventual_projective_pullbackPowerSection_surjective_q68 f
  refine ⟨N, fun n hn t => ?_⟩
  obtain ⟨s, hs⟩ := hN n hn t
  obtain ⟨p, hp, _⟩ := ProjectiveO1.globalSection_homogeneous_polynomial n s
  exact ⟨s, p, hs, hp⟩

end PiExponent.ProjectiveSectionExtension
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSectionInterface
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveSectionInterface
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.AffineJetCoefficientInterface

variable {X Y : Scheme.{0}}

theorem sectionHom_injective (L : LineBundle X) (n : ℕ) :
    Function.Injective (sectionHom L n) := fun _ _ h => h

attribute [local irreducible] AffineJetCoefficientInterface.Frame
  AffineJetCoefficientInterface.Sections

theorem eventual_homogeneous_extension
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n →
      ∀ s : Sections ((ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback f) n,
      ∃ t : Sections (ProjectiveO1.lineBundle (R := R) (σ := σ)) n,
      ∃ p : MvPolynomial.homogeneousSubmodule σ R n,
        pullback (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n t = s ∧
        ∀ z, PiExponentSeshadri.Projective.dehomogenize z p.val =
          ProjectiveO1.globalSectionChartPolynomial n z
            (sectionHom (ProjectiveO1.lineBundle (R := R) (σ := σ)) n t) := by
  obtain ⟨N, hN⟩ := ProjectiveSectionExtension.eventual_projective_homogeneous_extension f
  refine ⟨N, fun n hn s => ?_⟩
  obtain ⟨t, p, ht, hp⟩ := hN n hn
    (sectionHom ((ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback f) n s)
  refine ⟨ofSectionHom (ProjectiveO1.lineBundle (R := R) (σ := σ)) n t, p, ?_, ?_⟩
  · apply sectionHom_injective ((ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback f) n
    rw [sectionHom_pullback, sectionHom_ofSectionHom, ht]
  · simpa only [sectionHom_ofSectionHom] using hp

end
end PiExponent.ProjectiveSectionInterface

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_WeightedHomogeneousSubstitution
attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedHomogeneousSubstitution
noncomputable section
open scoped BigOperators
open MvPolynomial
open WeightedSliceDegree
open PiExponentSeshadri.Projective


variable {σ ι K : Type*}

theorem admissible_exponent_budget {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)
    (j : AdmissibleBlowupGeometry.Index d) :
    Finsupp.weight (fun i => (d.curveDegreeWeights i : ℝ))
      (AdmissibleBlowupGeometry.exponents d j) ≤ (AdmissibleBlowupGeometry.scale d).radius := by
  have hq := (AdmissibleBlowupGeometry.scale d).budget d.curveDegreeWeights_pos j
  have hr : (∑ i, (d.curveDegreeWeights i : ℝ) *
      (AdmissibleBlowupGeometry.exponents d j i : ℝ)) ≤
      (AdmissibleBlowupGeometry.scale d).radius := by
    exact_mod_cast hq
  simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hr

end
end PiExponent.WeightedHomogeneousSubstitution

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoefficientBound
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveCoefficientBound
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.AffineJetCoefficientInterface PiExponent.WeightedSliceDegree

variable {X : Scheme.{0}} {K ι σ : Type} [Field K] [Fintype σ] [Nonempty σ]

theorem eventual_of_homogeneous
    (f : X ⟶ ProjectiveO1.projectiveSpace K σ) [IsClosedImmersion f]
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (ρ : ι → ℝ) (B : ℝ) (h : HomogeneousPullbackBound f φ ρ B) :
    EventualBound φ ((ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback f) ρ B := by
  obtain ⟨N, hN⟩ := ProjectiveSectionInterface.eventual_homogeneous_extension f
  refine ⟨N, fun n hn e s => ?_⟩
  obtain ⟨t, p, ht, hp⟩ := hN n hn s
  rw [← ht]
  exact h n e t p hp

end PiExponent.ProjectiveCoefficientBound
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedGlobalSectionBound
attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.WeightedGlobalSectionBound
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.WeightedCompactification PiExponent.WeightedSliceDegree
open PiExponent.AffineJetCoefficientInterface PiExponent.ProjectiveCoefficientBound
variable {K ι σ : Type} [Field K] [Fintype σ]
attribute [local irreducible] Frame Sections AffineJetCoefficientInterface.coefficient
  LineBundle.pullback EventualBound ProjectiveO1.lineBundle
  WeightedCompactification.affineChartMap
  AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane

theorem eventual_supportBound (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (ρ : ι → ℝ) (B : ℝ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B) :
    EventualBound (affineChartMap (R := K) a z hz coordinate hcoordinate)
      (lineBundle (R := K) a) ρ B := by
  let : Nonempty σ := ⟨z⟩
  apply eventual_of_homogeneous (X := Proj (imageGrade (R := K) a))
    (K := K) (ι := ι) (σ := σ) (projectiveMonomialMap (R := K) a)
    (affineChartMap (R := K) a z hz coordinate hcoordinate) ρ B
  intro n e t p hp
  exact WeightedPullbackDegree.pullback_supportBound_q68 (K := K) (ι := ι) (σ := σ)
    a z hz coordinate hcoordinate ρ B ha n e t p (hp z)

theorem eventual_admissible_supportBound {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D) :
    EventualBound (AdmissibleBlowupGeometry.affineChart d) (AdmissibleBlowupGeometry.hyperplane d)
      (fun i => (d.curveDegreeWeights i : ℝ)) (AdmissibleBlowupGeometry.scale d).radius := by
  unfold AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane
  exact eventual_supportBound (K := ℂ) (ι := Fin (d.m+1))
    (σ := AdmissibleBlowupGeometry.Index d) (AdmissibleBlowupGeometry.exponents d)
    (AdmissibleBlowupGeometry.constantIndex d)
    ((AdmissibleBlowupGeometry.scale d).exponents_constant d.curveDegreeWeights_pos)
    (AdmissibleBlowupGeometry.coordinateIndex d)
    ((AdmissibleBlowupGeometry.scale d).exponents_coordinate d.curveDegreeWeights_pos)
    (fun i => (d.curveDegreeWeights i : ℝ)) (AdmissibleBlowupGeometry.scale d).radius
    (WeightedHomogeneousSubstitution.admissible_exponent_budget d)

end PiExponent.WeightedGlobalSectionBound
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AdmissibleMatrixGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleMatrixInterpolation
open AlgebraicGeometry CategoryTheory Filter
open PiExponentSeshadri.Geometry
open DeterminantContradiction AdmissibleBlowupGeometry AdmissibleJetPackets
attribute [local irreducible] WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap
  AffineJetCoefficientInterface.Frame AffineJetCoefficientInterface.Sections
  AffineJetCoefficientInterface.coefficient
variable {ν : ℝ} (d : FixedData ν)

theorem eventual_packets_of_eventual_jetRestriction_q68_oai
    (hjet : ∀ᶠ n : ℕ in atTop, Function.Surjective
      (BlowupJetSurjectivity.jetRestriction (centerIdeal d) (hyperplane d) n)) :
    ∀ᶠ n : ℕ in atTop, Function.Surjective (packetMap d n) := by
  obtain ⟨N,hN⟩ := WeightedGlobalSectionBound.eventual_admissible_supportBound d
  obtain ⟨e⟩ := actualFrame_exists d
  filter_upwards [hjet, eventually_ge_atTop N] with n hn hnN
  apply packetMap_surjective_of_family d n (sectionPolynomial d n e)
  · intro s
    exact hN n hnN e s
  · exact formalPackets_surjective_of_jetRestriction_q68 d n e hn

end PiExponent.AdmissibleMatrixInterpolation

end

end OAI
end

theorem solution : type_of% @OAI.PiExponent.AdmissibleMatrixInterpolation.eventual_packets_of_eventual_jetRestriction_q68_oai := @OAI.PiExponent.AdmissibleMatrixInterpolation.eventual_packets_of_eventual_jetRestriction_q68_oai
