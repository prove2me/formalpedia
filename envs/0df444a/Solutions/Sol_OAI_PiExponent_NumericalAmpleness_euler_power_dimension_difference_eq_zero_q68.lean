-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.euler_power_dimension_difference_eq_zero_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:36:57.859381+00:00
-- url     : https://prove2.me/submissions/a1eaf6ce-cdcb-4da1-8008-534e856c30f6

import Mathlib
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_exists_regular_twist_pair_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_lineBundle_cohomology_zero_of_dimension_le_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPushforwardLinear
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ClosedImmersionSerreTransfer

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

variable [IsClosedImmersion f]

local instance closedPushforwardLinearSourceHasExt_racad72_1 : HasExt.{1} X.Modules := schemeHasExt
attribute [local instance] OAI.PiExponent.ClosedImmersionSerreTransfer.closedPushforwardLinearTargetHasExt
lemma cohomologyDimension_pushforward
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    cohomologyDimension p ((Scheme.Modules.pushforward f).obj M) n =
      cohomologyDimension (f ≫ p) M n := by
  let := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  exact (cohomologyLinearEquiv f p M n).finrank_eq.symm

theorem euler_pushforward (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ) :
    eulerCharacteristic p d ((Scheme.Modules.pushforward f).obj M) =
      eulerCharacteristic (f ≫ p) d M := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [cohomologyDimension_pushforward]

end
end PiExponent.ClosedImmersionSerreTransfer

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CartierEulerDifference
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames


variable {X : Scheme.{0}}

theorem eulerCharacteristic_eq_pred_of_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ)
    (hzero : ∀ z : cohomology M d, z = 0) :
    eulerCharacteristic p d M = eulerCharacteristic p (d-1) M := by
  have : Subsingleton (cohomology M d) :=
    ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  have hdim : cohomologyDimension p M d = 0 := by
    let := Module.compHom (cohomology M d) (baseScalars p)
    exact Module.finrank_zero_of_subsingleton
  cases d with
  | zero => rfl
  | succ d =>
    simp only [Nat.add_sub_cancel, eulerCharacteristic, Finset.sum_range_succ,
      hdim, Nat.cast_zero, mul_zero, add_zero]

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CartierEulerPair
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

theorem tensorSectionComplex_shortExact (p : X ⟶ Spec (CommRingCat.of ℂ))
    (A F : LineBundle X) (s : GlobalSections X A.sheaf) [Mono s] :
    (tensorSectionComplex p A F s).ShortExact :=
  (regular_tensorSection_restriction_shortExact p A F s).choose_spec

namespace CartierEulerPair

theorem left_shortExact (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) [Mono s] (n : ℕ) :
    (leftComplex p L B M s n).ShortExact :=
  tensorSectionComplex_shortExact p (L.tensor B) (source L M n) s

theorem right_shortExact (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (t : GlobalSections X B.sheaf) [Mono t] (n : ℕ) :
    (rightComplex p L B M t n).ShortExact :=
  ShortComplex.shortExact_of_iso (rightComplexIso p L B M t n).symm
    (tensorSectionComplex_shortExact p B (source L M (n+1)) t)

theorem finiteThrough_closedPushforward {Y : Scheme.{0}} (f : Y ⟶ X)
    [IsClosedImmersion f] (p : X ⟶ Spec (CommRingCat.of ℂ)) (N : Y.Modules) (d : ℕ)
    (hfinite : FiniteThrough (f ≫ p) N d) :
    FiniteThrough p ((Scheme.Modules.pushforward f).obj N) d := by
  intro q hq
  let := Module.compHom (cohomology N q) (baseScalars (f ≫ p))
  let := Module.compHom
    (cohomology ((Scheme.Modules.pushforward f).obj N) q) (baseScalars p)
  let := hfinite q hq
  let e := PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearEquiv f p N q
  exact FiniteDimensional.of_surjective e.toLinearMap e.surjective

theorem euler_difference (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) (t : GlobalSections X B.sheaf)
    [Mono s] [Mono t] (n d : ℕ)
    (hfinitePrev : FiniteThrough p (source L M n).sheaf d)
    (hfiniteNext : FiniteThrough p (source L M (n+1)).sheaf d)
    (hfiniteMiddle : FiniteThrough p (middle L B M n).sheaf d)
    (hfiniteD : FiniteThrough ((zeroIdeal (L.tensor B) s).subschemeι ≫ p)
      ((Scheme.Modules.pullback (zeroIdeal (L.tensor B) s).subschemeι).obj
        (middle L B M n).sheaf) d)
    (hfiniteE : FiniteThrough ((zeroIdeal B t).subschemeι ≫ p)
      ((Scheme.Modules.pullback (zeroIdeal B t).subschemeι).obj
        (B.tensor (source L M (n+1))).sheaf) d)
    (hzeroPrev : ∀ z : cohomology (source L M n).sheaf (d+1), z = 0)
    (hzeroNext : ∀ z : cohomology (source L M (n+1)).sheaf (d+1), z = 0) :
    eulerCharacteristic p d (source L M (n+1)).sheaf -
        eulerCharacteristic p d (source L M n).sheaf =
      eulerCharacteristic ((zeroIdeal (L.tensor B) s).subschemeι ≫ p) d
        ((Scheme.Modules.pullback (zeroIdeal (L.tensor B) s).subschemeι).obj
          (middle L B M n).sheaf) -
      eulerCharacteristic ((zeroIdeal B t).subschemeι ≫ p) d
        ((Scheme.Modules.pullback (zeroIdeal B t).subschemeι).obj
          (B.tensor (source L M (n+1))).sheaf) := by
  let D := zeroIdeal (L.tensor B) s
  let E := zeroIdeal B t
  let Q := (Scheme.Modules.pullback D.subschemeι).obj (middle L B M n).sheaf
  let R := (Scheme.Modules.pullback E.subschemeι).obj (B.tensor (source L M (n+1))).sheaf
  let : Subsingleton (cohomology (leftComplex p L B M s n).X₁ (d+1)) :=
    ⟨fun a b => (hzeroPrev a).trans (hzeroPrev b).symm⟩
  let : Subsingleton (cohomology (rightComplex p L B M t n).X₁ (d+1)) :=
    ⟨fun a b => (hzeroNext a).trans (hzeroNext b).symm⟩
  have hleft := eulerCharacteristic_add p (left_shortExact p L B M s n) d
    hfinitePrev hfiniteMiddle (finiteThrough_closedPushforward D.subschemeι p Q d hfiniteD)
  have hright := eulerCharacteristic_add p (right_shortExact p L B M t n) d
    hfiniteNext hfiniteMiddle (finiteThrough_closedPushforward E.subschemeι p R d hfiniteE)
  change eulerCharacteristic p d (middle L B M n).sheaf =
    eulerCharacteristic p d (source L M n).sheaf +
      eulerCharacteristic p d ((Scheme.Modules.pushforward D.subschemeι).obj Q) at hleft
  change eulerCharacteristic p d (middle L B M n).sheaf =
    eulerCharacteristic p d (source L M (n+1)).sheaf +
      eulerCharacteristic p d ((Scheme.Modules.pushforward E.subschemeι).obj R) at hright
  rw [PiExponent.ClosedImmersionSerreTransfer.euler_pushforward] at hleft hright
  change eulerCharacteristic p d (source L M (n+1)).sheaf -
    eulerCharacteristic p d (source L M n).sheaf =
      eulerCharacteristic (D.subschemeι ≫ p) d Q - eulerCharacteristic (E.subschemeι ≫ p) d R
  omega

end CartierEulerPair
end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateFinite
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveCoordinateFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] negativeCoordinateLaurentPresentation
  coordinateFramedTuple negativeCoordinateFrame LineBundle.inverse lineTensorInverseIso
variable {X Y : Scheme.{0}} {K σ : Type} [Field K] [Fintype σ]

theorem coordinateBundle_cohomology_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf X ⟶ L.sheaf))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade ℂ (Fin l)))
    (hf : sectionsMorphism (baseScalars p) s hc = f.hom)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  exact CoherentProjectiveFinite.coherent_cohomology_finite_of_inverse_powers
    p L l hl s hc (coordinateOpen_isAffine L.sheaf s (baseScalars p) hc f hf)
    (inversePower_cohomology_finite L s (baseScalars p) hc f hf) M q

end
end PiExponent.GeometrySupport.ProjectiveCoordinateFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CohomologyFinite
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CohomologyFiniteness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open GeometrySupport.ProjectiveCoordinateFinite
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X Y : Scheme.{0}}

theorem coordinateBundle_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf X ⟶ L.sheaf))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade ℂ (Fin l)))
    (hf : sectionsMorphism (baseScalars p) s hc = f.hom)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) : CohomologyFinite p M q :=
  coordinateBundle_cohomology_finite p L l hl s hc f hf M q

end
end PiExponent.CohomologyFiniteness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerZeroDimensional
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveEmbeddingCohomologyBound
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.ProjectiveO1

theorem projectiveSpace_cohomology_eq_zero (r : ℕ)
    (M : (projectiveSpace ℂ (Fin (r+1))).Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : r+1 ≤ q) (z : cohomology M q) : z = 0 := by
  exact PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover (r+1) (by omega)
    (coordinateOpen (R := ℂ) (σ := Fin (r+1)))
    (fun j => standardChart_isAffineOpen j) standardChart_cover M q hq z

theorem cohomology_eq_zero_of_projective_embedding {X : Scheme.{0}} (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) (hq : r+1 ≤ q)
    (z : cohomology M q) : z = 0 := by
  let N := (Scheme.Modules.pushforward i).obj M
  let : N.IsFinitePresentation := PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation i M
  let : N.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData N).choose.isQuasicoherent
  let e := PiExponent.ClosedImmersionSerreTransfer.closedCohomologyEquiv i M q
  apply e.injective
  exact (projectiveSpace_cohomology_eq_zero r N q hq (e z)).trans e.map_zero.symm

theorem lineBundle_cohomology_eq_zero_of_projective_embedding {X : Scheme.{0}} (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (L : LineBundle X) (q : ℕ) (hq : r+1 ≤ q) (z : cohomology L.sheaf q) : z = 0 := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  exact cohomology_eq_zero_of_projective_embedding r i L.sheaf q hq z

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerCutoff
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.ProjectiveO1
variable {X : Scheme.{0}}

theorem eulerCharacteristic_eq_of_le_of_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d e : ℕ) (hde : d ≤ e)
    (hzero : ∀ q : ℕ, d < q → ∀ z : cohomology M q, z = 0) :
    eulerCharacteristic p e M = eulerCharacteristic p d M := by
  induction e, hde using Nat.le_induction with
  | base => rfl
  | succ e hde ih =>
    calc
      eulerCharacteristic p (e+1) M = eulerCharacteristic p e M := by
        simpa only [Nat.add_sub_cancel] using
          eulerCharacteristic_eq_pred_of_cohomology_zero p M (e+1)
            (hzero (e+1) (by omega))
      _ = eulerCharacteristic p d M := ih

theorem eulerCharacteristic_projective_eq_dimension
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H : LineBundle X) (hH : H.IsAmple) (M : LineBundle X)
    (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    eulerCharacteristic p r M.sheaf = eulerCharacteristic p d M.sheaf := by
  let : IsProper p := by rw [← hi]; infer_instance
  rcases le_total d r with h | h
  · exact eulerCharacteristic_eq_of_le_of_cohomology_zero p M.sheaf d r h
      (lineBundle_cohomology_zero_of_dimension_le_q68 d p H hH M hdim)
  · symm
    apply eulerCharacteristic_eq_of_le_of_cohomology_zero p M.sheaf r d h
    intro q hq z
    exact lineBundle_cohomology_eq_zero_of_projective_embedding r i M q (by omega) z

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerTwistTransport
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem eulerCharacteristic_pullback_cartierMiddle
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (f : Y ⟶ X)
    (A L M : LineBundle X) (n r : ℕ) :
    eulerCharacteristic (f ≫ p) r
      ((Scheme.Modules.pullback f).obj (A.tensor ((L.pow n).tensor M)).sheaf) =
    eulerCharacteristic (f ≫ p) r
      (((L.pullback f).pow n).tensor ((A.pullback f).tensor (M.pullback f))).sheaf :=
  eulerCharacteristic_iso (f ≫ p) (pullbackCartierMiddleIso f A L M n) r

theorem fwdDiff_eulerCharacteristic_left_pow_eq_zero [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L M : LineBundle X) (r : ℕ)
    (hdim : topologicalKrullDim X ≤ 0) :
    fwdDiff (1 : ℕ) (fun n => eulerCharacteristic p r ((L.pow n).tensor M).sheaf) = 0 := by
  have he (n : ℕ) : eulerCharacteristic p r ((L.pow n).tensor M).sheaf =
      eulerCharacteristic p r M.sheaf := by
    obtain ⟨e⟩ := lineBundle_trivial_of_dim_le_zero hdim (L.pow n)
    exact eulerCharacteristic_iso p
      (moduleTensorIso e (Iso.refl M.sheaf) ≪≫ moduleTensorUnit M.sheaf) r
  funext n
  simp only [fwdDiff, he, sub_self, Pi.zero_apply]

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSpaceFinite
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveSpaceFinite
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveO1 CohomologyFiniteness
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] ProjectiveO1.lineBundle ProjectiveO1.coordinateCocycle
  ProjectiveO1.coordinateSection sectionsMorphism CoordinateAtlas.morphism atlasOfFramedSections
  CohomologyFinite
variable {X : Scheme.{0}}

theorem projectiveSpace_cohomology_finite (r : ℕ)
    (M : (projectiveSpace ℂ (Fin (r+1))).Modules) [M.IsFinitePresentation] (q : ℕ) :
    CohomologyFinite (polynomialProjectiveProjection ℂ (Fin (r+1))) M q := by
  have hid : sectionsMorphism
      (X := projectiveSpace ℂ (Fin (r+1))) (K := ℂ) (σ := Fin (r+1))
      (M := (lineBundle (R := ℂ) (σ := Fin (r+1))).sheaf)
      (baseScalars (polynomialProjectiveProjection ℂ (Fin (r+1))))
      (coordinateSection (R := ℂ) (σ := Fin (r+1))) coordinateSection_cover =
      (Iso.refl (projectiveSpace ℂ (Fin (r+1)))).hom := by
    change sectionsMorphism
      (M := (lineBundle (R := ℂ) (σ := Fin (r+1))).sheaf)
      (baseScalars (polynomialProjectiveProjection ℂ (Fin (r+1))))
      (coordinateSection (R := ℂ) (σ := Fin (r+1)))
      (coordinateSection_cover (R := ℂ) (σ := Fin (r+1))) =
        𝟙 (projectiveSpace ℂ (Fin (r+1)))
    exact coordinate_sectionsMorphism_identity (R := ℂ) (σ := Fin (r+1))
  exact coordinateBundle_finite (X := projectiveSpace ℂ (Fin (r+1)))
    (polynomialProjectiveProjection ℂ (Fin (r+1)))
    (lineBundle (R := ℂ) (σ := Fin (r+1))) (r+1) (Nat.succ_pos r)
    (coordinateSection (R := ℂ) (σ := Fin (r+1)))
    (coordinateSection_cover (R := ℂ) (σ := Fin (r+1)))
    (Iso.refl (projectiveSpace ℂ (Fin (r+1)))) hid M q

theorem projectiveEmbedding_cohomology_finite (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q)
      (baseScalars (i ≫ polynomialProjectiveProjection ℂ (Fin (r+1))))
    FiniteDimensional ℂ (cohomology M q) := by
  exact finiteDimensional (i ≫ polynomialProjectiveProjection ℂ (Fin (r+1))) M q
    (closedPushforward_finite i (polynomialProjectiveProjection ℂ (Fin (r+1))) M q
      (projectiveSpace_cohomology_finite r ((Scheme.Modules.pushforward i).obj M) q))

theorem projectiveOver_cohomology_finite (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  subst p
  exact projectiveEmbedding_cohomology_finite r i M q

end
end PiExponent.ProjectiveSpaceFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerPolynomialDegree
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1

lemma iterate_fwdDiff_sub {G : Type*} [AddCommGroup G] (f g : ℕ → G) (k : ℕ) :
    (fwdDiff (1 : ℕ))^[k] (f-g) = (fwdDiff (1 : ℕ))^[k] f - (fwdDiff (1 : ℕ))^[k] g := by
  simpa only [fwdDiff_aux.coe_fwdDiffₗ_pow] using
    map_sub (fwdDiff_aux.fwdDiffₗ ℕ G (1 : ℕ) ^ k) f g

private lemma difference_step {G : Type*} [AddCommGroup G] (f g h : ℕ → G) (k : ℕ)
    (hd : fwdDiff (1 : ℕ) f = g - fun n => h (n+1))
    (hg : (fwdDiff (1 : ℕ))^[k] g=0) (hh : (fwdDiff (1 : ℕ))^[k] h=0) :
    (fwdDiff (1 : ℕ))^[k+1] f=0 := by
  rw [Function.iterate_succ_apply, hd, iterate_fwdDiff_sub, hg]
  have hz : (fwdDiff (1 : ℕ))^[k] (fun n => h (n+1))=0 := by
    funext n
    rw [fwdDiff_iter_comp_add, hh]
    rfl
  rw [hz, sub_self]

theorem projective_line_cohomology_finite {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L : LineBundle X) (q : ℕ) :
    letI := Module.compHom (cohomology L.sheaf q) (baseScalars p)
    FiniteDimensional ℂ (cohomology L.sheaf q) := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  exact PiExponent.ProjectiveSpaceFinite.projectiveOver_cohomology_finite p r i hi L.sheaf q

theorem euler_tensor_power_difference_aux (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
      (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
      (_hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
      (H : LineBundle X), H.IsAmple → ∀ (L M : LineBundle X),
      topologicalKrullDim X ≤ d →
      (fwdDiff (1 : ℕ))^[d+1]
        (fun n => eulerCharacteristic p r ((L.pow n).tensor M).sheaf) = 0 := by
  induction d with
  | zero =>
    intro X _ p r i _ hi H hH L M hdim
    simpa only [Nat.zero_add, Function.iterate_one] using
      fwdDiff_eulerCharacteristic_left_pow_eq_zero p L M r hdim
  | succ d ih =>
    intro X _ p r i _ hi H hH L M hdim
    obtain ⟨B, s, t, hs, ht⟩ := exists_regular_twist_pair_q68 p H L hH
    let : Mono s := hs
    let : Mono t := ht
    let A := L.tensor B
    let D := zeroIdeal A s
    let E := zeroIdeal B t
    let jD := D.subschemeι
    let jE := E.subschemeι
    let : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian jD
    let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace jD
    let : IsNoetherian D.subscheme := {}
    let : IsLocallyNoetherian E.subscheme := LocallyOfFiniteType.isLocallyNoetherian jE
    let : CompactSpace E.subscheme := QuasiCompact.compactSpace_of_compactSpace jE
    let : IsNoetherian E.subscheme := {}
    have hdD : topologicalKrullDim D.subscheme ≤ d :=
      regular_sectionZero_dimension_le A s d (by
        simpa only [Nat.cast_add, Nat.cast_one] using hdim)
    have hdE : topologicalKrullDim E.subscheme ≤ d :=
      regular_sectionZero_dimension_le B t d (by
        simpa only [Nat.cast_add, Nat.cast_one] using hdim)
    have hiD : (jD ≫ i) ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = jD ≫ p := by
      rw [Category.assoc, hi]
    have hiE : (jE ≫ i) ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = jE ≫ p := by
      rw [Category.assoc, hi]
    let f (n : ℕ) := eulerCharacteristic p r ((L.pow n).tensor M).sheaf
    let g (n : ℕ) := eulerCharacteristic (jD ≫ p) r
      (((L.pullback jD).pow n).tensor ((A.pullback jD).tensor (M.pullback jD))).sheaf
    let h (n : ℕ) := eulerCharacteristic (jE ≫ p) r
      (((L.pullback jE).pow n).tensor ((B.pullback jE).tensor (M.pullback jE))).sheaf
    have hg : (fwdDiff (1 : ℕ))^[d+1] g = 0 :=
      ih (jD ≫ p) r (jD ≫ i) hiD (H.pullback jD)
        (LineBundle.IsAmple.pullback_closedImmersion H hH jD)
        (L.pullback jD) ((A.pullback jD).tensor (M.pullback jD)) hdD
    have hh : (fwdDiff (1 : ℕ))^[d+1] h = 0 :=
      ih (jE ≫ p) r (jE ≫ i) hiE (H.pullback jE)
        (LineBundle.IsAmple.pullback_closedImmersion H hH jE)
        (L.pullback jE) ((B.pullback jE).tensor (M.pullback jE)) hdE
    have hd : fwdDiff (1 : ℕ) f = g - fun n => h (n+1) := by
      funext n
      have hv := CartierEulerPair.euler_difference p L B M s t n r
        (fun q _ => projective_line_cohomology_finite p r i hi ((L.pow n).tensor M) q)
        (fun q _ => projective_line_cohomology_finite p r i hi ((L.pow (n+1)).tensor M) q)
        (fun q _ => projective_line_cohomology_finite p r i hi
          (A.tensor ((L.pow n).tensor M)) q)
        (fun q _ => projective_line_cohomology_finite (jD ≫ p) r (jD ≫ i) hiD
          ((A.tensor ((L.pow n).tensor M)).pullback jD) q)
        (fun q _ => projective_line_cohomology_finite (jE ≫ p) r (jE ≫ i) hiE
          ((B.tensor ((L.pow (n+1)).tensor M)).pullback jE) q)
        (lineBundle_cohomology_eq_zero_of_projective_embedding r i
          ((L.pow n).tensor M) (r+1) le_rfl)
        (lineBundle_cohomology_eq_zero_of_projective_embedding r i
          ((L.pow (n+1)).tensor M) (r+1) le_rfl)
      dsimp only [CartierEulerPair.source, CartierEulerPair.middle] at hv
      rw [eulerCharacteristic_pullback_cartierMiddle,
        eulerCharacteristic_pullback_cartierMiddle] at hv
      exact hv
    exact difference_step f g h (d+1) hd hg hh

theorem euler_tensor_power_difference_eq_zero {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L M : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p r ((L.pow n).tensor M).sheaf) = 0 := by
  let H := (PiExponent.ProjectiveO1.lineBundle (R := ℂ) (σ := Fin (r+1))).pullback i
  have hH : H.IsAmple := LineBundle.IsAmple.pullback_closedImmersion _
    PiExponent.ProjectiveO1.lineBundle_ample i
  exact euler_tensor_power_difference_aux d p r i hi H hH L M hdim

theorem euler_tensor_power_dimension_difference_eq_zero
    {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L M : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p d ((L.pow n).tensor M).sheaf) = 0 := by
  let H := (PiExponent.ProjectiveO1.lineBundle (R := ℂ) (σ := Fin (r+1))).pullback i
  have hH : H.IsAmple := LineBundle.IsAmple.pullback_closedImmersion _
    PiExponent.ProjectiveO1.lineBundle_ample i
  have he : (fun n => eulerCharacteristic p r ((L.pow n).tensor M).sheaf) =
      (fun n => eulerCharacteristic p d ((L.pow n).tensor M).sheaf) := by
    funext n
    exact eulerCharacteristic_projective_eq_dimension p r i hi H hH
      ((L.pow n).tensor M) d hdim
  have h := euler_tensor_power_difference_eq_zero p r i hi L M d hdim
  rwa [he] at h

theorem euler_power_dimension_difference_eq_zero_q68_oai
    {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p d (L.pow n).sheaf) = 0 := by
  have h := euler_tensor_power_dimension_difference_eq_zero p r i hi L (L.pow 0) d hdim
  have he : (fun n => eulerCharacteristic p d ((L.pow n).tensor (L.pow 0)).sheaf) =
      (fun n => eulerCharacteristic p d (L.pow n).sheaf) := by
    funext n
    exact eulerCharacteristic_iso p (moduleTensorRightUnit (L.pow n).sheaf) d
  rwa [he] at h

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.euler_power_dimension_difference_eq_zero_q68_oai := @OAI.PiExponent.NumericalAmpleness.euler_power_dimension_difference_eq_zero_q68_oai
