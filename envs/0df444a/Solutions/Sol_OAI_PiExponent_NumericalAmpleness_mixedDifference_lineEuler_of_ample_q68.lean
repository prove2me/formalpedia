-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.mixedDifference_lineEuler_of_ample_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:38:26.57953+00:00
-- url     : https://prove2.me/submissions/69440af2-cf59-430e-9f28-5ddacc358174

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

local instance closedPushforwardLinearSourceHasExt_rcccacd_1 : HasExt.{1} X.Modules := schemeHasExt
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
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_AmpleLineCohomology
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
theorem line_cohomology_finite_of_ample_all
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (q : ℕ) :
    letI := Module.compHom (cohomology L.sheaf q) (baseScalars p)
    FiniteDimensional ℂ (cohomology L.sheaf q) := by
  cases isEmpty_or_nonempty X with
  | inr hX =>
    let := hX
    let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
    exact AmpleCohomologyFinite.cohomology_finite_of_ample p H hH L.sheaf q
  | inl hX =>
    let := hX
    let := Module.compHom (cohomology L.sheaf q) (baseScalars p)
    let M := (Scheme.Modules.pushforward (𝟙 X)).obj L.sheaf
    let := Module.compHom (cohomology M q) (baseScalars p)
    let : FiniteDimensional ℂ (cohomology M q) :=
      PiExponentSeshadri.FiniteSupport.finite_line_pushforward_finiteDimensional (𝟙 X) p L q
    let e := PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearEquiv (𝟙 X) p L.sheaf q
    exact FiniteDimensional.of_surjective e.symm.toLinearMap e.symm.surjective
end
end PiExponent.NumericalAmpleness

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
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerAlgebra
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem tensorDifference_sub (L : LineBundle X) (f g : LineBundle X → ℤ) :
    tensorDifference L (f - g) = tensorDifference L f - tensorDifference L g := by
  funext M
  simp only [tensorDifference, Pi.sub_apply]
  ring

theorem mixedDifference_sub (ls : List (LineBundle X)) (f g : LineBundle X → ℤ) :
    mixedDifference ls (f - g) = mixedDifference ls f - mixedDifference ls g := by
  induction ls with
  | nil => rfl
  | cons L ls ih => rw [mixedDifference_cons, ih, tensorDifference_sub]; rfl

theorem LineIsoInvariant.tensorDifference {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (L : LineBundle X) : LineIsoInvariant (tensorDifference L f) := by
  intro M N e
  change f (L.tensor M) - f M = f (L.tensor N) - f N
  rw [hf (L.tensor M) (L.tensor N) (moduleTensorIso (Iso.refl L.sheaf) e), hf M N e]

theorem LineIsoInvariant.mixedDifference {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (ls : List (LineBundle X)) : LineIsoInvariant (mixedDifference ls f) := by
  induction ls with
  | nil => exact hf
  | cons L ls ih => exact ih.tensorDifference L

theorem LineIsoInvariant.tensorShift {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (B : LineBundle X) : LineIsoInvariant (fun M => f (B.tensor M)) := by
  intro M N e
  exact hf _ _ (moduleTensorIso (Iso.refl B.sheaf) e)

theorem tensorDifference_commute (L B : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) :
    tensorDifference L (tensorDifference B f) = tensorDifference B (tensorDifference L f) := by
  funext M
  simp only [tensorDifference]
  rw [hf _ _ (tensorTwistSwapIso B L M)]
  ring

theorem mixedDifference_cons_commute (L : LineBundle X) (ls : List (LineBundle X))
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference (L :: ls) f = mixedDifference ls (tensorDifference L f) := by
  induction ls with
  | nil => rfl
  | cons B ls ih =>
      change tensorDifference L (tensorDifference B (mixedDifference ls f)) =
        tensorDifference B (mixedDifference ls (tensorDifference L f))
      rw [tensorDifference_commute L B _ (hf.mixedDifference ls)]
      exact congrArg (tensorDifference B) ih

theorem mixedDifference_tensorShift (ls : List (LineBundle X))
    (g : LineBundle X → ℤ) (hg : LineIsoInvariant g) (B M : LineBundle X) :
    mixedDifference ls (fun N => g (B.tensor N)) M = mixedDifference ls g (B.tensor M) := by
  induction ls generalizing M with
  | nil => rfl
  | cons L ls ih =>
      change mixedDifference ls (fun N => g (B.tensor N)) (L.tensor M) -
        mixedDifference ls (fun N => g (B.tensor N)) M =
          mixedDifference ls g (L.tensor (B.tensor M)) - mixedDifference ls g (B.tensor M)
      rw [ih, ih, (hg.mixedDifference ls) _ _ (tensorTwistSwapIso B L M)]

theorem mixedDifference_pullback (ls : List (LineBundle X)) (i : Y ⟶ X)
    (g : LineBundle Y → ℤ) (hg : LineIsoInvariant g) (M : LineBundle X) :
    mixedDifference ls (fun N => g (N.pullback i)) M =
      mixedDifference (ls.map (fun L => L.pullback i)) g (M.pullback i) := by
  induction ls generalizing M with
  | nil => rfl
  | cons L ls ih =>
      change mixedDifference ls (fun N => g (N.pullback i)) (L.tensor M) -
        mixedDifference ls (fun N => g (N.pullback i)) M =
          mixedDifference (ls.map (fun N => N.pullback i)) g
            ((L.pullback i).tensor (M.pullback i)) -
          mixedDifference (ls.map (fun N => N.pullback i)) g (M.pullback i)
      rw [ih, ih, (hg.mixedDifference _) _ _ (PiExponentSeshadri.PullbackTensor.iso i L M)]

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerCartierAmple
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
variable {X : Scheme.{0}}

theorem tensor_euler_difference_cartier_pair_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (r : ℕ)
    (hdim : topologicalKrullDim X ≤ r)
    (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) (t : GlobalSections X B.sheaf)
    [Mono s] [Mono t] :
    eulerCharacteristic p r (L.tensor M).sheaf - eulerCharacteristic p r M.sheaf =
      eulerCharacteristic ((zeroIdeal (L.tensor B) s).subschemeι ≫ p) r
        (((L.tensor B).pullback (zeroIdeal (L.tensor B) s).subschemeι).tensor
          (M.pullback (zeroIdeal (L.tensor B) s).subschemeι)).sheaf -
      eulerCharacteristic ((zeroIdeal B t).subschemeι ≫ p) r
        (((B.tensor L).pullback (zeroIdeal B t).subschemeι).tensor
          (M.pullback (zeroIdeal B t).subschemeι)).sheaf := by
  let D := zeroIdeal (L.tensor B) s
  let E := zeroIdeal B t
  let jD := D.subschemeι
  let jE := E.subschemeι
  have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH jD
  have hHE := LineBundle.IsAmple.pullback_closedImmersion H hH jE
  let e0 : (CartierEulerPair.source L M 0).sheaf ≅ M.sheaf :=
    moduleTensorUnit M.sheaf
  let e1 : (CartierEulerPair.source L M 1).sheaf ≅ (L.tensor M).sheaf :=
    moduleTensorIso (moduleTensorRightUnit L.sheaf) (Iso.refl M.sheaf)
  let em : (CartierEulerPair.middle L B M 0).sheaf ≅
      ((L.tensor B).tensor M).sheaf :=
    moduleTensorIso (Iso.refl _) e0
  let ee : (B.tensor (CartierEulerPair.source L M 1)).sheaf ≅
      ((B.tensor L).tensor M).sheaf :=
    moduleTensorIso (Iso.refl _) e1 ≪≫ (lineTensorAssoc B L M).symm
  have hv := CartierEulerPair.euler_difference p L B M s t 0 r
    (fun q _ => line_cohomology_finite_of_ample_all p H hH (CartierEulerPair.source L M 0) q)
    (fun q _ => line_cohomology_finite_of_ample_all p H hH (CartierEulerPair.source L M 1) q)
    (fun q _ => line_cohomology_finite_of_ample_all p H hH (CartierEulerPair.middle L B M 0) q)
    (fun q _ => line_cohomology_finite_of_ample_all (jD ≫ p) (H.pullback jD) hHD
      ((CartierEulerPair.middle L B M 0).pullback jD) q)
    (fun q _ => line_cohomology_finite_of_ample_all (jE ≫ p) (H.pullback jE) hHE
      ((B.tensor (CartierEulerPair.source L M 1)).pullback jE) q)
    (lineBundle_cohomology_zero_of_dimension_le_q68 r p H hH
      (CartierEulerPair.source L M 0) hdim (r+1) (by omega))
    (lineBundle_cohomology_zero_of_dimension_le_q68 r p H hH
      (CartierEulerPair.source L M 1) hdim (r+1) (by omega))
  rw [eulerCharacteristic_iso p e0 r, eulerCharacteristic_iso p e1 r] at hv
  have hD := eulerCharacteristic_iso (jD ≫ p)
    ((Scheme.Modules.pullback jD).mapIso em ≪≫
      PiExponentSeshadri.PullbackTensor.iso jD (L.tensor B) M) r
  have hE := eulerCharacteristic_iso (jE ≫ p)
    ((Scheme.Modules.pullback jE).mapIso ee ≪≫
      PiExponentSeshadri.PullbackTensor.iso jE (B.tensor L) M) r
  rw [hD, hE] at hv
  exact hv

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerDimension
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

theorem lineEuler_isoInvariant {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ) :
    LineIsoInvariant (lineEuler p r) := by
  intro L M e
  exact eulerCharacteristic_iso p e r

theorem mixedDifference_pullback_tensorShift_zero {X Y : Scheme.{0}}
    (ls : List (LineBundle X)) (i : Y ⟶ X) (g : LineBundle Y → ℤ)
    (hg : LineIsoInvariant g) (B : LineBundle Y)
    (hz : mixedDifference (ls.map (fun L => L.pullback i)) g = 0) :
    mixedDifference ls (fun M => g (B.tensor (M.pullback i))) = 0 := by
  funext M
  rw [mixedDifference_pullback ls i (fun N => g (B.tensor N)) (hg.tensorShift B) M,
    mixedDifference_tensorShift _ g hg B (M.pullback i), hz]
  rfl

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerAmpleDimension
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

theorem mixedDifference_lineEuler_of_ample_aux (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
      (H : LineBundle X), H.IsAmple → ∀ r : ℕ, d ≤ r →
      topologicalKrullDim X ≤ d → ∀ ls : List (LineBundle X), ls.length = d+1 →
      mixedDifference ls (lineEuler p r) = 0 := by
  induction d with
  | zero =>
    intro X _ p _ H hH r hr hdim ls hlen
    cases ls with
    | nil => simp at hlen
    | cons L ls =>
      have hz : ls = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst ls
      funext M
      obtain ⟨e⟩ := lineBundle_trivial_of_dim_le_zero hdim L
      have he := eulerCharacteristic_iso p
        (moduleTensorIso e (Iso.refl M.sheaf) ≪≫ moduleTensorUnit M.sheaf) r
      change eulerCharacteristic p r (L.tensor M).sheaf - eulerCharacteristic p r M.sheaf = 0
      exact sub_eq_zero.mpr he
  | succ d ih =>
    intro X _ p _ H hH r hr hdim ls hlen
    cases ls with
    | nil => simp at hlen
    | cons L ls =>
      have hlen' : ls.length = d+1 := by simpa using hlen
      obtain ⟨B, s, t, hs, ht⟩ := exists_regular_twist_pair_q68 p H L hH
      let := hs
      let := ht
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
      let g := lineEuler (jD ≫ p) r
      let h := lineEuler (jE ≫ p) r
      let g' (M : LineBundle D.subscheme) := g ((A.pullback jD).tensor M)
      let h' (M : LineBundle E.subscheme) := h (((B.tensor L).pullback jE).tensor M)
      have hg := lineEuler_isoInvariant (jD ≫ p) r
      have hh := lineEuler_isoInvariant (jE ≫ p) r
      have hDz : mixedDifference (ls.map (fun L => L.pullback jD)) g = 0 :=
        ih (jD ≫ p) (H.pullback jD)
          (LineBundle.IsAmple.pullback_closedImmersion H hH jD) r (by omega) hdD _
          (by simpa using hlen')
      have hEz : mixedDifference (ls.map (fun L => L.pullback jE)) h = 0 :=
        ih (jE ≫ p) (H.pullback jE)
          (LineBundle.IsAmple.pullback_closedImmersion H hH jE) r (by omega) hdE _
          (by simpa using hlen')
      have heq : tensorDifference L (lineEuler p r) =
          (fun M => g' (M.pullback jD)) - fun M => h' (M.pullback jE) := by
        funext M
        exact tensor_euler_difference_cartier_pair_of_ample p H hH r
          (hdim.trans (by exact_mod_cast hr)) L B M s t
      have hDzero := mixedDifference_pullback_tensorShift_zero ls jD g hg (A.pullback jD) hDz
      have hEzero := mixedDifference_pullback_tensorShift_zero ls jE h hh
        ((B.tensor L).pullback jE) hEz
      rw [mixedDifference_cons_commute L ls _ (lineEuler_isoInvariant p r),
        heq, mixedDifference_sub, hDzero, hEzero, sub_self]

theorem mixedDifference_lineEuler_of_ample_q68_oai {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d)
    (ls : List (LineBundle X)) (hlen : ls.length = d+1) :
    mixedDifference ls (lineEuler p d) = 0 :=
  mixedDifference_lineEuler_of_ample_aux d p H hH d le_rfl hdim ls hlen

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.mixedDifference_lineEuler_of_ample_q68_oai := @OAI.PiExponent.NumericalAmpleness.mixedDifference_lineEuler_of_ample_q68_oai
