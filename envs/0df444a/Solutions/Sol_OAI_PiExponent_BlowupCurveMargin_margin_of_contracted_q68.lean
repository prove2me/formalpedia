-- Prove2me | solution 1 for OAI.PiExponent.BlowupCurveMargin.margin_of_contracted_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:21:36.525984+00:00
-- url     : https://prove2.me/submissions/d641f288-5c4f-490a-aa7a-e4104cb6797e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A040
import Definitions.Def_OAIQ068A041
import Theorems.Thm_OAI_PiExponent_BlowupCurveMargin_margin_of_nonnegative_degree_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_curveDegree_pos_of_ample_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_lineBundle_cohomology_zero_of_dimension_le_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_AmpleCohomologyFinite
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveDegreeAdditivity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ConstantPullbackDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_additive _root_.OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_preservesZero _root_.OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor_additive _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ConstantPullbackDegree
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

theorem euler_difference_eq_zero (p : X ⟶ Spec (CommRingCat.of ℂ))
    (K : LineBundle Y) (g : X ⟶ Y) (y : Y)
    (hg : Set.range g ⊆ ({y} : Set Y)) (d : ℕ) :
    eulerCharacteristic p d (K.pullback g).sheaf -
      eulerCharacteristic p d (structureSheaf X) = 0 := by
  rw [eulerCharacteristic_iso p (constantPullbackIso K g y hg) d]
  exact sub_self _

theorem curveDegree_eq_zero_of_contracted
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (K : LineBundle Y)
    (g : X ⟶ Y) (C : NumericalAmpleness.IntegralCurve X) (y : Y)
    (hg : Set.range (C.embedding ≫ g) ⊆ ({y} : Set Y)) :
    NumericalAmpleness.curveDegree p (K.pullback g) C = 0 := by
  have he := eulerCharacteristic_iso (C.embedding ≫ p)
    ((Scheme.Modules.pullbackComp C.embedding g).app K.sheaf) 1
  simp only [CategoryTheory.Functor.comp_obj] at he
  unfold NumericalAmpleness.curveDegree
  change eulerCharacteristic (C.embedding ≫ p) 1
      ((Scheme.Modules.pullback C.embedding).obj ((Scheme.Modules.pullback g).obj K.sheaf)) -
    eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme) = 0
  rw [he]
  exact euler_difference_eq_zero (C.embedding ≫ p) K (C.embedding ≫ g) y hg 1

end
end PiExponent.ConstantPullbackDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupCurveMargin
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BlowupCurveMargin
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open NumericalAmpleness
variable {B X : Scheme.{0}}

theorem curve_degree_laws (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle B) (hH : H.IsAmple) (C : IntegralCurve B) :
    (∀ L M : LineBundle B, curveDegree p (L.tensor M) C =
      curveDegree p L C + curveDegree p M C) ∧
    (∀ (L : LineBundle B) (n : ℕ), curveDegree p (L.pow n) C =
      (n : ℤ) * curveDegree p L C) := by
  let HC := H.pullback C.embedding
  have hHC : HC.IsAmple := LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding
  have hfinite := CurveDegree.finite_line_cohomology_of_ample (C.embedding ≫ p) HC hHC
  have hH2 : CurveDegree.LineCohomologyTwoZero C.scheme := by
    intro M
    exact ⟨fun a b =>
      (lineBundle_cohomology_zero_of_dimension_le_q68 1 (C.embedding ≫ p) HC hHC M
        C.dimension.le 2 (by omega) a).trans
      (lineBundle_cohomology_zero_of_dimension_le_q68 1 (C.embedding ≫ p) HC hHC M
        C.dimension.le 2 (by omega) b).symm⟩
  exact ⟨fun L M => curveDegree_tensor p H hH L M C hfinite hH2,
    fun L n => curveDegree_pow p H hH L C hfinite hH2 n⟩

theorem margin_of_contracted_q68_oai
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (π : B ⟶ X)
    (L : LineBundle X) (J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : (((L.pullback π).pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (x : X) (hc : Set.range (C.embedding ≫ π) ⊆ ({x} : Set X)) :
    marginCoefficient a σ * (curveDegree p (((L.pullback π).pow a).tensor J) C : ℝ) ≤
      (curveDegree p ((L.pullback π).tensor J) C : ℝ) := by
  have hA := ConstantPullbackDegree.curveDegree_eq_zero_of_contracted p L π C x hc
  have hpos := curveDegree_pos_of_ample_q68 p (((L.pullback π).pow a).tensor J) hample C
  obtain ⟨ht,hp⟩ := curve_degree_laws p (((L.pullback π).pow a).tensor J) hample C
  rw [ht, hp, hA, mul_zero, zero_add] at hpos
  apply margin_of_nonnegative_degree_q68 p (L.pullback π) J a ha hample σ hσ C
  rw [hA]
  exact add_nonneg (by norm_num) (mul_nonneg (by linarith)
    (by exact_mod_cast hpos.le))


end PiExponent.BlowupCurveMargin

end

end OAI
end

theorem solution : type_of% @OAI.PiExponent.BlowupCurveMargin.margin_of_contracted_q68_oai := @OAI.PiExponent.BlowupCurveMargin.margin_of_contracted_q68_oai
