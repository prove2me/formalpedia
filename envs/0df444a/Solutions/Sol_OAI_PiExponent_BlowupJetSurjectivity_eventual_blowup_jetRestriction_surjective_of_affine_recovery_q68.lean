-- Prove2me | solution 1 for OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_affine_recovery_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:36:34.344246+00:00
-- url     : https://prove2.me/submissions/9506fc77-dce5-483a-9751-7fdb10629ef8

import Mathlib
import Definitions.Def_OAIQ068A044
import Theorems.Thm_OAI_PiExponent_BlowupJetSurjectivity_eventual_blowup_jetRestriction_surjective_of_section_comparison_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_TwistLocalSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X : Scheme.{0}}

theorem moduleTwist_app_bijective (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    {M N : X.Modules} (β : M ⟶ N) (n : ℕ)
    (h : Function.Bijective (β.app U)) :
    Function.Bijective (((moduleTwistFunctor L n).map β).app U) := by
  let E := SheafOfModules.evaluation U.toScheme.ringCatSheaf (op (⊤ : U.toScheme.Opens))
  have he := NatIso.isIso_map_iff
    (Functor.isoWhiskerRight (moduleTwistRestrictFrame L U e n) E) β
  have hright : IsIso (((Scheme.Modules.restrictFunctor U.ι) ⋙ E).map β) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (β.app (U.ι ''ᵁ ⊤))
    exact U.ι_image_top.symm ▸ h
  have hleft := he.mpr hright
  have hb := ConcreteCategory.bijective_of_isIso
    ((((moduleTwistFunctor L n ⋙ Scheme.Modules.restrictFunctor U.ι) ⋙ E).map β))
  change Function.Bijective (((moduleTwistFunctor L n).map β).app (U.ι ''ᵁ ⊤)) at hb
  exact U.ι_image_top ▸ hb

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalRecoveryTwist
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ExceptionalRecoveryMap
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)

theorem twistedMap_app_bijective (A : LineBundle X) (n : ℕ) (U : X.Opens)
    (e : A.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (h : Function.Bijective ((ordinaryMap f I E ι hE n).app U)) :
    Function.Bijective ((twistedMap f I E ι hE A n).app U) := by
  let a := (ProjectionFormula.twistIso f (modulePow Y E.sheaf n) A n).symm ≪≫
    (Scheme.Modules.pushforward f).mapIso
      (moduleTwistPowerIso (A.pullback f) (modulePow Y E.sheaf n) n ≪≫
        (lineTensorPow E (A.pullback f) n).symm)
  let : IsIso ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map a.hom) :=
    ((SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso a).isIso_hom
  have ha := ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map a.hom)
  exact ha.comp (moduleTwist_app_bijective A U e (ordinaryMap f I E ι hE n) n h)

end
end PiExponent.GeometrySupport.ExceptionalRecoveryMap

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_FiniteAffineFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_additive _root_.OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_preservesZero _root_.OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor_additive _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}}

theorem LineBundle.finite_affine_frame_cover [CompactSpace X] (L : LineBundle X) :
    ∃ k : ℕ, ∃ U : Fin k → X.affineOpens,
      (⨆ i, (U i).1) = ⊤ ∧
      ∀ i, Nonempty (L.sheaf.restrict (U i).1.ι ≅ structureSheaf (U i).1.toScheme) := by
  classical
  have hex (x : X) := common_affine_frames L L x
  choose V hx he _ using hex
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((V x).1 : Set X)) (fun x => (V x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let e := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, fun i => V (e i).val, ?_, fun i => he (e i).val⟩
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (show x ∈ Set.univ from trivial))
  obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
  exact Opens.mem_iSup.mpr ⟨e.symm ⟨i, hi⟩, by simpa using hx⟩

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_FiniteReesComparison
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ExceptionalRecoveryMap
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque
open CechHigher
variable {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)

private theorem intersection_one {J : Type} (U : J → X.Opens) (t : Fin 1 → J) :
    intersection U t = U (t 0) := by
  apply le_antisymm (iInf_le _ 0)
  apply le_iInf
  intro i
  exact le_of_eq (congrArg (fun j => U (t j)) (Subsingleton.elim 0 i))

private theorem intersection_two {J : Type} (U : J → X.Opens) (t : Fin 2 → J) :
    intersection U t = U (t 0) ⊓ U (t 1) := by
  apply le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1))
  apply le_iInf
  intro i
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right

theorem eventual_comparison_of_affine_recovery [CompactSpace X] [X.IsSeparated]
    (A : LineBundle X)
    (hrecover : ∀ U : X.affineOpens, ∃ N, ∀ n, N ≤ n →
      Function.Bijective ((ordinaryMap f I E ι hE n).app U.1)) :
    ∃ k : ℕ, ∃ U : Fin k → X.affineOpens, (⨆ i, (U i).1) = ⊤ ∧
      ∃ N, ∀ n, N ≤ n → Nonempty
        (CechH1Transfer.SectionComparison (fun i => (U i).1)
          (fun i => f ⁻¹ᵁ (U i).1)
          ((moduleTwistFunctor A n).obj (closedModule (I^n)))
          ((E.tensor (A.pullback f)).pow n).sheaf) := by
  classical
  obtain ⟨k,U,hcover,hframe⟩ := A.finite_affine_frame_cover
  let V : Fin k → X.Opens := fun i => (U i).1
  have ha1 (t : Fin 1 → Fin k) : IsAffineOpen (intersection V t) :=
    (intersection_one V t).symm ▸ (U (t 0)).2
  have ha2 (t : Fin 2 → Fin k) : IsAffineOpen (intersection V t) :=
    (intersection_two V t).symm ▸ (U (t 0)).2.inf (U (t 1)).2
  choose Nv hv using fun t : Fin 1 → Fin k => hrecover ⟨intersection V t, ha1 t⟩
  choose Np hp using fun t : Fin 2 → Fin k => hrecover ⟨intersection V t, ha2 t⟩
  let Bv := Finset.univ.sup Nv
  let Bp := Finset.univ.sup Np
  refine ⟨k,U,hcover,Bv ⊔ Bp,?_⟩
  intro n hn
  let β := twistedMap f I E ι hE A n
  have hvn (t : Fin 1 → Fin k) : Function.Bijective (β.app (intersection V t)) := by
    exact twistedMap_app_bijective f I E ι hE A n (intersection V t)
      (restrictOpenFrame (iInf_le _ 0) (Classical.choice (hframe (t 0))))
      (hv t n ((Finset.le_sup (Finset.mem_univ t)).trans (le_sup_left.trans hn)))
  have hpn (t : Fin 2 → Fin k) : Function.Injective (β.app (intersection V t)) := by
    exact (twistedMap_app_bijective f I E ι hE A n (intersection V t)
      (restrictOpenFrame (iInf_le _ 0) (Classical.choice (hframe (t 0))))
      (hp t n ((Finset.le_sup (Finset.mem_univ t)).trans (le_sup_right.trans hn)))).injective
  exact ⟨PushforwardOpenSections.comparison f β V hvn hpn⟩

end
end PiExponent.GeometrySupport.ExceptionalRecoveryMap

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupJetReesReduction
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_blowup_jetRestriction_surjective_of_affine_recovery_q68_oai
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A))
    (hrecover : ∀ U : X.affineOpens, ∃ N, ∀ n, N ≤ n → Function.Bijective
      ((ExceptionalRecoveryMap.ordinaryMap (PiExponentSeshadri.BlowupGluing.projection I)
        I (PiExponentSeshadri.BlowupGluing.exceptionalLineBundle I)
        (PiExponentSeshadri.BlowupGluing.exceptionalInclusion I)
        (PiExponentSeshadri.BlowupGluing.exceptional_presents I) n).app U.1)) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : X.IsSeparated := ⟨by
    have h : IsSeparated (p ≫ terminal.from (Spec (CommRingCat.of R))) := inferInstance
    simpa only [terminal.comp_from] using h⟩
  obtain ⟨k,U,hcover,N,hN⟩ :=
    ExceptionalRecoveryMap.eventual_comparison_of_affine_recovery
      (PiExponentSeshadri.BlowupGluing.projection I) I
      (PiExponentSeshadri.BlowupGluing.exceptionalLineBundle I)
      (PiExponentSeshadri.BlowupGluing.exceptionalInclusion I)
      (PiExponentSeshadri.BlowupGluing.exceptional_presents I) A hrecover
  exact eventual_blowup_jetRestriction_surjective_of_section_comparison_q68
    p I A hample (fun i => (U i).1) (fun i => (U i).2) hcover ⟨N,hN⟩

end
end PiExponent.BlowupJetSurjectivity

end OAI
end

theorem solution : type_of% @OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_affine_recovery_q68_oai := @OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_affine_recovery_q68_oai
