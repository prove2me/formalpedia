-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.mixedTop_cartier_restriction_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:38:49.324406+00:00
-- url     : https://prove2.me/submissions/7fa5d500-74c9-4f83-9a89-64d409ef1508

import Mathlib
import Definitions.Def_OAIQ068A043
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_lineBundle_cohomology_zero_of_dimension_le_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_mixedDifference_lineEuler_of_ample_q68

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

local instance closedPushforwardLinearSourceHasExt_r00cf91_1 : HasExt.{1} X.Modules := schemeHasExt
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
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CartierEulerDifference
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem cartier_euler_difference
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e' : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ e'.hom))})
    (d : ℕ)
    (hfiniteM : ∀ q ≤ d, letI := Module.compHom (cohomology M.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology M.sheaf q))
    (hfiniteN : ∀ q ≤ d, letI := Module.compHom (cohomology N.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf q))
    (hfiniteRestricted : ∀ q ≤ d,
      letI := Module.compHom
        (cohomology ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) q)
        (baseScalars (I.subschemeι ≫ p))
      FiniteDimensional ℂ (cohomology ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) q))
    (hzeroM : ∀ z : cohomology M.sheaf (d+1), z = 0)
    (hzeroRestricted : ∀ z : cohomology ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) d,
      z = 0) :
    eulerCharacteristic p d N.sheaf - eulerCharacteristic p d M.sheaf =
      eulerCharacteristic (I.subschemeι ≫ p) (d-1)
        ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) := by
  obtain ⟨hz,hS⟩ := PiExponentSeshadri.CartierSequence.exact p M N φ I heq
  have : Subsingleton (cohomology M.sheaf (d+1)) :=
    ⟨fun a b => (hzeroM a).trans (hzeroM b).symm⟩
  have hfinitePushforward (q : ℕ) (hq : q ≤ d) :
      letI := Module.compHom
        (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) q) (baseScalars p)
      FiniteDimensional ℂ
        (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) q) := by
    let := Module.compHom
      (cohomology ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) q)
      (baseScalars (I.subschemeι ≫ p))
    let := Module.compHom
      (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) q) (baseScalars p)
    have := hfiniteRestricted q hq
    let e := ClosedImmersionSerreTransfer.cohomologyLinearEquiv I.subschemeι p
      ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) q
    exact FiniteDimensional.of_surjective e.toLinearMap e.surjective
  have hEuler := eulerCharacteristic_add p hS d hfiniteM hfiniteN hfinitePushforward
  change eulerCharacteristic p d N.sheaf = eulerCharacteristic p d M.sheaf +
    eulerCharacteristic p d ((Scheme.Modules.pushforward I.subschemeι).obj
      ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) at hEuler
  rw [ClosedImmersionSerreTransfer.euler_pushforward,
    eulerCharacteristic_eq_pred_of_cohomology_zero (I.subschemeι ≫ p)
      ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) d hzeroRestricted] at hEuler
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hEuler)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CartierPowerFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CartierPowerFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem cartierPowerMultiply_ideal (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (n : ℕ) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((modulePowFrame U.1 e n).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map
        (PiExponent.NumericalAmpleness.cartierPowerMultiply L s n) ≫
      (modulePowFrame U.1 e (n+1)).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} :=
  tensor_multiply_ideal L.sheaf (modulePow X L.sheaf n) s U e (modulePowFrame U.1 e n)
end
end PiExponent.CartierPowerFrames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_SectionCartierRegular
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

private lemma mono_iso_inv_comp_p2 {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (f : A ⟶ D) [Mono f] : Mono (e.inv ≫ f) := inferInstance

theorem cartierPowerMultiply_mono_of_mono (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    Mono (cartierPowerMultiply L s n) := by
  have hm : Mono (moduleTensorMap s (𝟙 (modulePow X L.sheaf n))) :=
    moduleTensorMap_mono s (L.pow n)
  exact @mono_iso_inv_comp_p2 X.Modules _ _ _ _
    (moduleTensorUnit (modulePow X L.sheaf n)) _ hm

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CartierMixedEuler
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

private lemma framed_map {C : Type*} [Category C] {A B P Q T O : C}
    (r : A ≅ P) (r' : B ≅ Q) (e : P ≅ T) (e' : Q ≅ T) (u : T ≅ O)
    (m : A ⟶ B) (p : P ⟶ Q) (b : T ⟶ T) (a : O ⟶ O)
    (hn : m ≫ r'.hom = r.hom ≫ p) (ht : p ≫ e'.hom = e.hom ≫ b)
    (hs : b ≫ u.hom = u.hom ≫ a) :
    (r ≪≫ e ≪≫ u).inv ≫ m ≫ (r' ≪≫ e' ≪≫ u).hom = a := by
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [← Category.assoc m r'.hom, hn]
  simp only [Category.assoc]
  rw [← Category.assoc p e'.hom, ht]
  simp only [Category.assoc]
  rw [hs]
  simp

lemma tensorMap_framed (A B M : X.Modules) (φ : A ⟶ B) (U : X.Opens)
    (e : A.restrict U.ι ≅ O U.toScheme)
    (e' : B.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    (_root_.OAI.PiExponent.CartierPowerFrames.tensorFrame A M U e f).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap φ (𝟙 M)) ≫
        (_root_.OAI.PiExponent.CartierPowerFrames.tensorFrame B M U e' f).hom =
      e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map φ ≫ e'.hom := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U A M
  let R' := moduleTensorRestrict U B M
  let E := moduleTensorIso e f
  let E' := moduleTensorIso e' f
  let T := moduleTensorUnit (O U.toScheme)
  let c := e.inv ≫ F.map φ ≫ e'.hom
  let p := moduleTensorMap (F.map φ) (𝟙 (M.restrict U.ι))
  have he : F.map φ ≫ e'.hom = e.hom ≫ c := by
    simp [c]
  have hn : F.map (moduleTensorMap φ (𝟙 M)) ≫ R'.hom = R.hom ≫ p :=
    (moduleTensorRestrict_natural U φ (𝟙 M)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map φ) q) (F.map_id M))
  have h₁ := (moduleTensorMap_comp (F.map φ) e'.hom (𝟙 (M.restrict U.ι)) f.hom).symm.trans
    (congrArg (moduleTensorMap (F.map φ ≫ e'.hom)) (Category.id_comp f.hom))
  have h₂ := (moduleTensorMap_comp e.hom c f.hom (𝟙 (O U.toScheme))).symm.trans
    (congrArg (moduleTensorMap (e.hom ≫ c)) (Category.comp_id f.hom))
  have ht : p ≫ E'.hom = E.hom ≫ moduleTensorMap c (𝟙 (O U.toScheme)) :=
    h₁.trans ((congrArg (fun q : F.obj A ⟶ O U.toScheme => moduleTensorMap q f.hom)
      he).trans h₂.symm)
  have hs : moduleTensorMap c (𝟙 (O U.toScheme)) ≫ T.hom = T.hom ≫ c :=
    (moduleTensorUnit_scalar (X := U.toScheme) c (𝟙 (O U.toScheme))).trans
      (congrArg (fun q => T.hom ≫ q) (Category.comp_id c))
  simpa only [_root_.OAI.PiExponent.CartierPowerFrames.tensorFrame] using!
    framed_map R R' E E' T (F.map (moduleTensorMap φ (𝟙 M))) p _ c hn ht hs

theorem mixedCartierPowerMultiply_mono (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    Mono (mixedCartierPowerMultiply L M s n) := by
  let := cartierPowerMultiply_mono_of_mono L s n
  exact moduleTensorMap_mono (cartierPowerMultiply L s n) M

theorem mixedCartierPower_zeroIdeal_frames (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (n : ℕ) :
    ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : ((L.pow n).tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e' : ((L.pow (n+1)).tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        (zeroIdeal L s).ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map
            (mixedCartierPowerMultiply L M s n) ≫ e'.hom))} := by
  intro x
  obtain ⟨U, hx, ⟨e⟩, ⟨f⟩⟩ := common_affine_frames L M x
  refine ⟨U, hx,
    _root_.OAI.PiExponent.CartierPowerFrames.tensorFrame (L.pow n).sheaf M.sheaf U.1 (modulePowFrame U.1 e n) f,
    _root_.OAI.PiExponent.CartierPowerFrames.tensorFrame (L.pow (n+1)).sheaf M.sheaf U.1 (modulePowFrame U.1 e (n+1)) f, ?_⟩
  simp only [mixedCartierPowerMultiply]
  have hframe := tensorMap_framed (L.pow n).sheaf (L.pow (n+1)).sheaf M.sheaf
    (cartierPowerMultiply L s n) U.1 (modulePowFrame U.1 e n)
    (modulePowFrame U.1 e (n+1)) f
  exact ((zeroIdeal_on_frame L s U e).trans (cartierPowerMultiply_ideal L s n U e).symm).trans
    (congrArg (fun g : O U.1.toScheme ⟶ O U.1.toScheme =>
      Ideal.span {U.1.topIso.hom (endValue g)}) hframe.symm)

theorem regular_mixedCartierPower_euler_difference
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n d : ℕ)
    (hfiniteSource : ∀ q ≤ d,
      letI := Module.compHom (cohomology ((L.pow n).tensor M).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology ((L.pow n).tensor M).sheaf q))
    (hfiniteTarget : ∀ q ≤ d,
      letI := Module.compHom (cohomology ((L.pow (n+1)).tensor M).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology ((L.pow (n+1)).tensor M).sheaf q))
    (hfiniteRestricted : ∀ q ≤ d,
      letI := Module.compHom
        (cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
          ((L.pow (n+1)).tensor M).sheaf) q)
        (baseScalars ((zeroIdeal L s).subschemeι ≫ p))
      FiniteDimensional ℂ
        (cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
          ((L.pow (n+1)).tensor M).sheaf) q))
    (hzeroSource : ∀ z : cohomology ((L.pow n).tensor M).sheaf (d+1), z = 0)
    (hzeroRestricted : ∀ z :
      cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
        ((L.pow (n+1)).tensor M).sheaf) d, z = 0) :
    eulerCharacteristic p d ((L.pow (n+1)).tensor M).sheaf -
        eulerCharacteristic p d ((L.pow n).tensor M).sheaf =
      eulerCharacteristic ((zeroIdeal L s).subschemeι ≫ p) (d-1)
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
          ((L.pow (n+1)).tensor M).sheaf) := by
  let := mixedCartierPowerMultiply_mono L M s n
  exact cartier_euler_difference p ((L.pow n).tensor M) ((L.pow (n+1)).tensor M)
    (mixedCartierPowerMultiply L M s n) (zeroIdeal L s)
    (mixedCartierPower_zeroIdeal_frames L M s n) d hfiniteSource hfiniteTarget
    hfiniteRestricted hzeroSource hzeroRestricted

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_AmpleLineCohomology
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerAlgebra
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerDimension
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerPolarization
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem mixedDifference_tensor_base_of_degree {d : ℕ} {f : LineBundle X → ℤ}
    (hf : MixedDegreeLE d f) (ls : List (LineBundle X)) (hlen : ls.length = d)
    (A M : LineBundle X) :
    mixedDifference ls f (A.tensor M) = mixedDifference ls f M := by
  have hz := congrFun (hf (A :: ls) (by simp [hlen])) M
  exact sub_eq_zero.mp hz

theorem mixedDifference_eq_structure_of_degree {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (ls : List (LineBundle X)) (hlen : ls.length = d) (M : LineBundle X) :
    mixedDifference ls f M = mixedDifference ls f (structureLineBundle X) := by
  have he := (hf.mixedDifference ls) (M.tensor (structureLineBundle X)) M
    (moduleTensorRightUnit M.sheaf)
  exact he.symm.trans
    (mixedDifference_tensor_base_of_degree hdegree ls hlen M (structureLineBundle X))

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerRestriction
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem tensor_euler_difference_regular_section
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A M : LineBundle X) (s : GlobalSections X A.sheaf) [Mono s] :
    lineEuler p (d+1) (A.tensor M) - lineEuler p (d+1) M =
      lineEuler ((zeroIdeal A s).subschemeι ≫ p) d
        ((A.pullback (zeroIdeal A s).subschemeι).tensor
          (M.pullback (zeroIdeal A s).subschemeι)) := by
  let D := zeroIdeal A s
  let j := D.subschemeι
  have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH j
  have hdimD := regular_sectionZero_dimension_le A s d hdim
  let e0 : ((A.pow 0).tensor M).sheaf ≅ M.sheaf := moduleTensorUnit M.sheaf
  let e1 : ((A.pow 1).tensor M).sheaf ≅ (A.tensor M).sheaf :=
    moduleTensorIso (moduleTensorRightUnit A.sheaf) (Iso.refl M.sheaf)
  have he := regular_mixedCartierPower_euler_difference p A M s 0 (d+1)
    (fun q _ => line_cohomology_finite_of_ample_all p H hH ((A.pow 0).tensor M) q)
    (fun q _ => line_cohomology_finite_of_ample_all p H hH ((A.pow 1).tensor M) q)
    (fun q _ => line_cohomology_finite_of_ample_all (j ≫ p) (H.pullback j) hHD
      (((A.pow 1).tensor M).pullback j) q)
    (lineBundle_cohomology_zero_of_dimension_le_q68 (d+1) p H hH ((A.pow 0).tensor M)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hdim) (d+1+1) (by omega))
    (lineBundle_cohomology_zero_of_dimension_le_q68 d (j ≫ p) (H.pullback j) hHD
      (((A.pow 1).tensor M).pullback j) hdimD (d+1) (by omega))
  rw [eulerCharacteristic_iso p e0 (d+1), eulerCharacteristic_iso p e1 (d+1)] at he
  have hR := eulerCharacteristic_iso (j ≫ p)
    ((Scheme.Modules.pullback j).mapIso e1 ≪≫ PiExponentSeshadri.PullbackTensor.iso j A M) d
  simp only [Nat.add_sub_cancel, Nat.zero_add] at he
  exact he.trans hR

theorem mixedDifference_cartier_restriction
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A : LineBundle X) (s : GlobalSections X A.sheaf) [Mono s]
    (ls : List (LineBundle X)) (M : LineBundle X) :
    mixedDifference (A :: ls) (lineEuler p (d+1)) M =
      mixedDifference (ls.map (fun L => L.pullback (zeroIdeal A s).subschemeι))
        (lineEuler ((zeroIdeal A s).subschemeι ≫ p) d)
        ((A.pullback (zeroIdeal A s).subschemeι).tensor
          (M.pullback (zeroIdeal A s).subschemeι)) := by
  let j := (zeroIdeal A s).subschemeι
  let g := lineEuler (j ≫ p) d
  have hg := lineEuler_isoInvariant (j ≫ p) d
  have he : tensorDifference A (lineEuler p (d+1)) =
      fun N => g ((A.pullback j).tensor (N.pullback j)) := by
    funext N
    exact tensor_euler_difference_regular_section p H hH d hdim A N s
  rw [mixedDifference_cons_commute A ls _ (lineEuler_isoInvariant p (d+1)), he,
    mixedDifference_pullback ls j _ (hg.tensorShift (A.pullback j)) M,
    mixedDifference_tensorShift _ g hg (A.pullback j) (M.pullback j)]

theorem mixedTop_cartier_restriction_q68_oai [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A : LineBundle X) (s : GlobalSections X A.sheaf) [Mono s]
    (ls : List (LineBundle X)) (hlen : ls.length = d) :
    mixedTop (lineEuler p (d+1)) (A :: ls) =
      mixedTop (lineEuler ((zeroIdeal A s).subschemeι ≫ p) d)
        (ls.map (fun L => L.pullback (zeroIdeal A s).subschemeι)) := by
  let D := zeroIdeal A s
  let j := D.subschemeι
  let : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian j
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace j
  let : IsNoetherian D.subscheme := {}
  have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH j
  have hdimD := regular_sectionZero_dimension_le A s d hdim
  have hdeg : MixedDegreeLE d (lineEuler (j ≫ p) d) :=
    mixedDifference_lineEuler_of_ample_q68 (j ≫ p) (H.pullback j) hHD d hdimD
  unfold mixedTop
  rw [mixedDifference_cartier_restriction p H hH d hdim A s ls]
  exact mixedDifference_eq_structure_of_degree (lineEuler_isoInvariant (j ≫ p) d)
    hdeg _ (by simpa using hlen) _

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.mixedTop_cartier_restriction_q68_oai := @OAI.PiExponent.NumericalAmpleness.mixedTop_cartier_restriction_q68_oai
