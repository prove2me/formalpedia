-- Prove2me | solution 5 for OAI.PiExponent.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:52:17.571156+00:00
-- url     : https://prove2.me/submissions/6c93c071-eb45-4a36-bde9-25b6c71de620

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_AdmissibleJetSurjectivity_blowupBundle_ample_q68
import Theorems.Thm_OAI_PiExponent_AdmissibleMatrixInterpolation_globalInterpolation_of_eventual_jetRestriction_q68
import Theorems.Thm_OAI_PiExponent_AffineReesCanonicalRecovery_eventually_comap_bijective_q68
import Theorems.Thm_OAI_PiExponent_BlowupJetSurjectivity_eventual_blowup_jetRestriction_surjective_of_affine_recovery_q68
import Theorems.Thm_OAI_PiExponent_piEventualLowerBound_of_globalInterpolation_q68

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

theorem sectionsEquiv_inclusion (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) (s : Γ(closedModule I, f ''ᵁ U)) :
    (closedInclusion (I.comap f)).app U (sectionsEquiv I f U s) =
      (f.appIso U).hom ((closedInclusion I).app (f ''ᵁ U) s) := by
  have h := congrArg (fun g => g.app U s) (restrictedToClosed_inclusion I f)
  exact h

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

theorem idealCongr_inclusion {I J : Y.IdealSheafData} (h : I = J) (U : Y.Opens)
    (s : Γ(closedModule I,U)) :
    (closedInclusion J).app U (idealCongr h U s) = (closedInclusion I).app U s := by
  subst J
  rfl

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
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPullbackOpenSquare
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

private theorem bijective_iff_of_square {A B C D : Type*}
    (p : A → B) (q : C → D) (a : A → C) (b : B → D)
    (ha : Function.Bijective a) (hb : Function.Bijective b)
    (h : ∀ x, b (p x) = q (a x)) : Function.Bijective p ↔ Function.Bijective q := by
  have he : b ∘ p = q ∘ a := funext h
  rw [← hb.of_comp_iff' p, he]
  exact Function.Bijective.of_comp_iff q ha

private theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

theorem pullback_open_square {X Y X' Y' : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f]
    (j : X' ⟶ X) [IsOpenImmersion j]
    (k : Y' ⟶ Y) [IsOpenImmersion k]
    (f' : Y' ⟶ X') [QuasiCompact f'] (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) (U : X'.Opens) (V : Y'.Opens)
    (hV : k ''ᵁ V ≤ f ⁻¹ᵁ (j ''ᵁ U)) (hV' : V ≤ f' ⁻¹ᵁ U)
    (s : Γ(closedModule I, j ''ᵁ U)) :
    idealCongr (squareIdeal f j k f' h I) V
      (sectionsEquiv (I.comap f) k V
        (pullback f I (j ''ᵁ U) (k ''ᵁ V) hV s)) =
      pullback f' (I.comap j) U V hV' (sectionsEquiv I j U s) := by
  apply inclusion_injective ((I.comap j).comap f') V
  rw [idealCongr_inclusion]
  have h₁ := sectionsEquiv_inclusion (I.comap f) k V
    (pullback f I (j ''ᵁ U) (k ''ᵁ V) hV s)
  have h₂ := pullback_inclusion f I (j ''ᵁ U) (k ''ᵁ V) hV s
  have h₃ := pullback_inclusion f' (I.comap j) U V hV' (sectionsEquiv I j U s)
  have h₄ := sectionsEquiv_inclusion I j U s
  rw [Scheme.Hom.appIso_hom'] at h₁ h₄
  have hh : f.appLE (j ''ᵁ U) (k ''ᵁ V) hV ≫
      k.appLE (k ''ᵁ V) V (k.preimage_image_eq V).ge =
      j.appLE (j ''ᵁ U) U (j.preimage_image_eq U).ge ≫ f'.appLE U V hV' := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr h _ _ _ _
  exact (h₁.trans (congrArg (k.appLE (k ''ᵁ V) V (k.preimage_image_eq V).ge) h₂)).trans
    ((congrArg (fun a => a ((closedInclusion I).app (j ''ᵁ U) s)) hh).trans
      ((congrArg (f'.appLE U V hV') h₄).symm.trans h₃.symm))

theorem pullback_open_square_bijective_iff {X Y X' Y' : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f]
    (j : X' ⟶ X) [IsOpenImmersion j]
    (k : Y' ⟶ Y) [IsOpenImmersion k]
    (f' : Y' ⟶ X') [QuasiCompact f'] (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) (U : X'.Opens) (V : Y'.Opens)
    (hV : k ''ᵁ V ≤ f ⁻¹ᵁ (j ''ᵁ U)) (hV' : V ≤ f' ⁻¹ᵁ U) :
    Function.Bijective (pullback f I (j ''ᵁ U) (k ''ᵁ V) hV) ↔
      Function.Bijective (pullback f' (I.comap j) U V hV') := by
  exact bijective_iff_of_square
    (pullback f I (j ''ᵁ U) (k ''ᵁ V) hV)
    (pullback f' (I.comap j) U V hV')
    (sectionsEquiv I j U)
    (fun z => idealCongr (squareIdeal f j k f' h I) V
      (sectionsEquiv (I.comap f) k V z))
    (sectionsEquiv I j U).bijective
    ((idealCongr (squareIdeal f j k f' h I) V).bijective.comp
      (sectionsEquiv (I.comap f) k V).bijective)
    (pullback_open_square f j k f' h I U V hV hV')

theorem comap_app_bijective_iff_open_square {X Y X' Y' : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f]
    (j : X' ⟶ X) [IsOpenImmersion j]
    (k : Y' ⟶ Y) [IsOpenImmersion k]
    (f' : Y' ⟶ X') [QuasiCompact f'] (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) (U : X.Opens) (U' : X'.Opens) (V' : Y'.Opens)
    (hj : j ''ᵁ U' = U) (hk : k ''ᵁ V' = f ⁻¹ᵁ U)
    (hv : V' = f' ⁻¹ᵁ U') :
    Function.Bijective ((GeometrySupport.IdealPullbackMap.comap f I).app U) ↔
      Function.Bijective ((GeometrySupport.IdealPullbackMap.comap f' (I.comap j)).app U') := by
  subst U
  exact (pullback_bijective_iff_comap f I (j ''ᵁ U') (k ''ᵁ V') hk.le hk).symm.trans
    ((pullback_open_square_bijective_iff f j k f' h I U' V' hk.le hv.le).trans
      (pullback_bijective_iff_comap f' (I.comap j) U' V' hv.le hv))

end PiExponent.IdealSectionRestriction

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CanonicalRecoveryProperties
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CanonicalRecoveryProperties
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open GeometrySupport

theorem ordinary_iff_comap {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)
    (n : ℕ) (U : X.Opens) :
    OrdinaryBijective f I E ι hE n U ↔ ComapBijective f (I^n) U := by
  have hb := ConcreteCategory.bijective_of_isIso
    ((PresentedIdealIso.powerIso I f E ι hE n).inv.app (f ⁻¹ᵁ U))
  change Function.Bijective
    (((PresentedIdealIso.powerIso I f E ι hE n).inv.app (f ⁻¹ᵁ U)) ∘
      ((IdealPullbackMap.comap f (I^n)).app U)) ↔ _
  exact hb.of_comp_iff' _

theorem comap_open_square {X Y X' Y' : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f]
    (j : X' ⟶ X) [IsOpenImmersion j]
    (k : Y' ⟶ Y) [IsOpenImmersion k]
    (f' : Y' ⟶ X') [QuasiCompact f'] (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) (U : X.Opens) (U' : X'.Opens) (V' : Y'.Opens)
    (hj : j ''ᵁ U' = U) (hk : k ''ᵁ V' = f ⁻¹ᵁ U)
    (hv : V' = f' ⁻¹ᵁ U') :
    ComapBijective f I U ↔ ComapBijective f' (I.comap j) U' :=
  IdealSectionRestriction.comap_app_bijective_iff_open_square f j k f' h I U U' V' hj hk hv

end PiExponent.CanonicalRecoveryProperties

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_GlobalReesRecoveryComparison
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ReesCohomologySetup.instIsNoetherianAffineBlowupOfIsNoetherianRing _root_.OAI.PiExponent.ReesFrozenChart.instIsOpenImmersionChart _root_.OAI.PiExponent.ReesProductPowerSections.chartMorphism_open _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.GlobalReesRecoveryComparison
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
open GeometrySupport CanonicalRecoveryProperties

attribute [local irreducible] PiExponentSeshadri.BlowupGluing.affineRestrictionIso
  PiExponentSeshadri.ReesGrading.affineBlowup PiExponentSeshadri.ReesGrading.projection
  IdealPullbackMap.map IdealPullbackMap.comap

theorem comap_app_bijective_iff_affine_raw {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (U : X.affineOpens) :
    ComapBijective (PiExponentSeshadri.BlowupGluing.projection I) J U.1 ↔
      ComapBijective (PiExponentSeshadri.ReesGrading.projection
        (PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U))
        (J.comap (PiExponentSeshadri.BlowupGluing.baseChart U)) ⊤ :=
  CanonicalRecoveryProperties.comap_open_square
    (PiExponentSeshadri.BlowupGluing.projection I)
    (PiExponentSeshadri.BlowupGluing.baseChart U)
    (PiExponentSeshadri.BlowupGluing.totalChart I U)
    (PiExponentSeshadri.ReesGrading.projection
      (PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U))
    (PiExponentSeshadri.BlowupGluing.totalChart_projection I U) J U.1 ⊤ ⊤
    (by simp only [Scheme.Hom.image_top_eq_opensRange,
      PiExponentSeshadri.BlowupGluing.baseChart_opensRange])
    (by simp only [Scheme.Hom.image_top_eq_opensRange,
      PiExponentSeshadri.BlowupGluing.totalChart_opensRange])
    (by simp)

theorem comap_app_bijective_iff_affine {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.affineOpens) (n : ℕ) :
    ComapBijective (PiExponentSeshadri.BlowupGluing.projection I) (I^n) U.1 ↔
      ComapBijective (PiExponentSeshadri.ReesGrading.projection
        (PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U))
        (PiExponentSeshadri.IdealPullback.specIdeal
          ((PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U)^n)) ⊤ := by
  have hh := comap_app_bijective_iff_affine_raw I (I^n) U
  have he : (I^n).comap (PiExponentSeshadri.BlowupGluing.baseChart U) =
      PiExponentSeshadri.IdealPullback.specIdeal
        ((PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U)^n) := by
    rw [PiExponentSeshadri.IdealPullback.comap_pow,
      PiExponentSeshadri.BlowupGluing.center_comap_baseChart,
      PiExponentSeshadri.IdealPullback.specIdeal_pow]
  exact hh.trans (iff_of_eq (congrArg (fun J => ComapBijective
    (PiExponentSeshadri.ReesGrading.projection
      (PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U)) J ⊤) he))

end PiExponent.GlobalReesRecoveryComparison

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_GlobalReesCanonicalRecovery
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.GlobalReesRecoveryComparison
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.BlowupGluing
open CanonicalRecoveryProperties

theorem eventually_ordinaryMap_app_bijective {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.affineOpens) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      OrdinaryBijective (projection I) I (exceptionalLineBundle I)
        (exceptionalInclusion I) (exceptional_presents I) n U.1 := by
  let : IsAffine U.1.toScheme := U.2
  let : IsNoetherianRing Γ(U.1.toScheme,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩
  obtain ⟨N,hN⟩ := AffineReesCanonicalRecovery.eventually_comap_bijective_q68 (affineCenterIdeal I U)
  exact ⟨N, fun n hn => (ordinary_iff_comap (projection I) I
    (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I) n U.1).mpr
      ((comap_app_bijective_iff_affine I U n).mpr (hN n hn))⟩

end PiExponent.GlobalReesRecoveryComparison

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupJetSurjectivityComplete
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_blowup_jetRestriction_surjective
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A)) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  exact eventual_blowup_jetRestriction_surjective_of_affine_recovery_q68 p I A hample
    (fun U => GlobalReesRecoveryComparison.eventually_ordinaryMap_app_bijective I U)

end
end PiExponent.BlowupJetSurjectivity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AdmissibleJetSurjectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AdmissibleJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.AdmissibleBlowupGeometry PiExponent.BlowupJetSurjectivity
attribute [local irreducible] AdmissibleBlowupGeometry.centerIdeal
  AdmissibleBlowupGeometry.hyperplane
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem eventual_jetRestriction_surjective :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (jetRestriction (centerIdeal d) (hyperplane d) n) := by
  exact eventual_blowup_jetRestriction_surjective
    (compactificationStructureMap d) (centerIdeal d) (hyperplane d) (blowupBundle_ample_q68 d)

theorem eventually_jetRestriction_surjective :
    ∀ᶠ n in Filter.atTop, Function.Surjective
      (jetRestriction (centerIdeal d) (hyperplane d) n) := by
  obtain ⟨N,hN⟩ := eventual_jetRestriction_surjective d
  exact Filter.eventually_atTop.mpr ⟨N,hN⟩

end
end PiExponent.AdmissibleJetSurjectivity

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

theorem globalInterpolation : GlobalInterpolationStatement := by
  apply globalInterpolation_of_eventual_jetRestriction_q68
  intro ν _ d
  exact AdmissibleJetSurjectivity.eventually_jetRestriction_surjective d

end PiExponent.AdmissibleMatrixInterpolation

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_Exponent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

 theorem eventualLowerBound_iff_integer (x : ℝ) :
    EventualLowerBound x ↔ IntegerEventualLowerBound x := by
  unfold EventualLowerBound IntegerEventualLowerBound
  constructor
  · intro h ν hν
    obtain ⟨Q, hQ, hb⟩ := h ν hν
    refine ⟨Q, by exact_mod_cast hQ, ?_⟩
    intro p q hq
    have hq0 : 0 ≤ q := le_trans (by omega) hq
    have hnat : Q ≤ q.toNat := by omega
    have heq : (q.toNat : ℝ) = (q : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hq0)
    simpa only [heq] using hb p q.toNat hnat
  · intro h ν hν
    obtain ⟨Q, hQ, hb⟩ := h ν hν
    have hQ0 : 0 ≤ Q := by omega
    refine ⟨Q.toNat, by omega, ?_⟩
    intro p q hq
    have hqi : Q ≤ (q : ℤ) := by omega
    simpa using hb p q hqi

theorem finite_rat_den_le_abs_sub_lt_one (x : ℝ) (N : ℕ) :
    {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| < 1}.Finite := by
  classical
  let f : ℚ → ℤ × ℕ := fun r => (r.num, r.den)
  have hinj : Function.Injective f := by
    intro a b hab
    have hp := Prod.mk.inj hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hp.1, hp.2]
  let t : Set (ℤ × ℕ) := ⋃ (q : ℕ) (_ : q ∈ Set.Icc 1 N),
    Set.Icc ⌈(x - 1) * q⌉ ⌊(x + 1) * q⌋ ×ˢ {q}
  have ht : t.Finite :=
    Set.Finite.biUnion (Set.finite_Icc _ _) fun q _ =>
      Set.Finite.prod (Set.finite_Icc _ _) (Set.finite_singleton _)
  have hsub : f '' {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| < 1} ⊆ t := by
    rintro _ ⟨r, ⟨hrN, hr⟩, rfl⟩
    have hrden : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
    have hrlow : x - 1 < (r : ℝ) := by linarith [(abs_lt.mp hr).2]
    have hrhigh : (r : ℝ) < x + 1 := by linarith [(abs_lt.mp hr).1]
    have hnlow : (x - 1) * r.den ≤ (r.num : ℝ) := by
      rw [Rat.cast_def] at hrlow
      exact ((lt_div_iff₀ hrden).mp hrlow).le
    have hnhigh : (r.num : ℝ) ≤ (x + 1) * r.den := by
      rw [Rat.cast_def] at hrhigh
      exact ((div_lt_iff₀ hrden).mp hrhigh).le
    simp only [t, Set.mem_iUnion]
    refine ⟨r.den, ⟨r.pos, hrN⟩, ?_⟩
    exact ⟨⟨Int.ceil_le.mpr hnlow, Int.le_floor.mpr hnhigh⟩, rfl⟩
  exact (ht.subset hsub).of_finite_image hinj.injOn

theorem two_mem_approximationExponents {x : ℝ} (hx : Irrational x) :
    (2 : ℝ) ∈ ApproximationExponents x := by
  refine ⟨by norm_num, ?_⟩
  have hi := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  have hf := finite_rat_den_le_abs_sub_lt_one x 1
  apply (hi.sdiff hf).mono
  intro r hr
  have hrden : 1 ≤ (r.den : ℝ) := by exact_mod_cast r.pos
  have hrone : |x - (r : ℝ)| < 1 :=
    hr.1.trans_le (by
      simpa only [div_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
          (by nlinarith : (1 : ℝ) ≤ (r.den : ℝ)^2))
  have hr2 : 2 ≤ r.den := by
    by_contra h
    exact hr.2 ⟨by omega, hrone⟩
  refine ⟨hr2, abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat r)), ?_⟩
  simpa only [Set.mem_ofPred_eq, Real.rpow_neg (Nat.cast_nonneg r.den),
    Real.rpow_two, one_div] using hr.1

theorem finite_goodRationalApproximations_of_eventualLowerBound {x ν : ℝ}
    (hx : EventualLowerBound x) (hν : 2 < ν) :
    (GoodRationalApproximations x ν).Finite := by
  obtain ⟨Q, hQ, hb⟩ := hx ν hν
  apply (finite_rat_den_le_abs_sub_lt_one x Q).subset
  intro r hr
  have hltQ : r.den < Q := by
    by_contra h
    have h := hb r.num r.den (by omega)
    rw [← Rat.cast_def] at h
    exact (not_lt_of_ge h) hr.2.2
  refine ⟨hltQ.le, hr.2.2.trans_le ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast r.pos) (by linarith)

theorem irrationalityExponent_eq_two_of_eventualLowerBound {x : ℝ}
    (hi : Irrational x) (hx : EventualLowerBound x) :
    irrationalityExponent x = 2 := by
  have htwo := two_mem_approximationExponents hi
  have hbound : ∀ ν ∈ ApproximationExponents x, ν ≤ 2 := by
    intro ν hν
    by_contra h
    exact (finite_goodRationalApproximations_of_eventualLowerBound hx (by linarith)).not_infinite hν.2
  apply le_antisymm
  · exact csSup_le ⟨2, htwo⟩ hbound
  · exact le_csSup ⟨2, hbound⟩ htwo

theorem pi_irrationalityExponent_eq_two_of_eventualLowerBound
    (h : PiEventualLowerBound) : irrationalityExponent Real.pi = 2 :=
  irrationalityExponent_eq_two_of_eventualLowerBound irrational_pi h

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

theorem pi_eventual_lower_bound : PiEventualLowerBound :=
  piEventualLowerBound_of_globalInterpolation_q68 AdmissibleMatrixInterpolation.globalInterpolation

theorem pi_integer_eventual_lower_bound : IntegerEventualLowerBound Real.pi :=
  (eventualLowerBound_iff_integer Real.pi).mp pi_eventual_lower_bound

theorem pi_irrationalityExponent_eq_two : irrationalityExponent Real.pi = 2 :=
  pi_irrationalityExponent_eq_two_of_eventualLowerBound pi_eventual_lower_bound

theorem main_oai :
  (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) ∧
  sSup {ν : ℝ | 0 < ν ∧
    Set.Infinite {r : ℚ | 2 ≤ r.den ∧
      0 < |Real.pi - (r : ℝ)| ∧
      |Real.pi - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 := by
  refine ⟨pi_integer_eventual_lower_bound, ?_⟩
  change irrationalityExponent Real.pi = 2
  exact pi_irrationalityExponent_eq_two

end PiExponent

end OAI
end

theorem solution : type_of% @OAI.PiExponent.main_oai := @OAI.PiExponent.main_oai
