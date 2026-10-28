-- Prove2me | solution 1 for OAI.PiExponentSeshadri.Geometry.isAffineOpen_of_fullSupport_preimage_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:26:52.914988+00:00
-- url     : https://prove2.me/submissions/f7edc84b-2ed6-441e-b3a2-9d6dd220a436

import Mathlib
import Definitions.Def_OAIQ068A039
import Definitions.Def_OAIQ068A040
import Definitions.Def_OAIQ068A041

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedImmersionSerreTransfer
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite
open PiExponentSeshadri.FlasqueCohomology

namespace PiExponent.ClosedImmersionSerreTransfer

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

variable [PreservesFiniteColimits (Scheme.Modules.pushforward f)]

local instance instHasExtModules_solutions_r1e6b4b_1 : HasExt.{u+1} X.Modules := HasExt.standard _
attribute [local instance] OAI.PiExponent.ClosedImmersionSerreTransfer.instHasExtModules_solutions_1
theorem ext_zero_iff (M : X.Modules) (n : ℕ) :
    (∀ x : Ext.{u+1} (C := X.Modules) (schemeUnit X) M n, x = 0) ↔
      (∀ x : Ext.{u+1} (C := Y.Modules) (schemeUnit Y)
        ((Scheme.Modules.pushforward f).obj M) n, x = 0) := by
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := (cohomologyEquiv f M n).surjective x
    rw [h y, map_zero]
  · intro h x
    apply (cohomologyEquiv f M n).injective
    rw [map_zero]
    exact h _

end PiExponent.ClosedImmersionSerreTransfer

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AffineThickeningCriterion
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme}

theorem isUnit_of_basicOpen_eq_top (r : Γ(X,⊤)) (hr : X.basicOpen r = ⊤) :
    IsUnit r := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ r
  intro x hx
  exact (X.mem_basicOpen_top r x).mp (by rw [hr]; trivial)

theorem appTop_reflects_isUnit (f : Y ⟶ X) (hf : Function.Surjective f)
    (r : Γ(X,⊤)) (hr : IsUnit (f.appTop r)) : IsUnit r := by
  apply isUnit_of_basicOpen_eq_top r
  apply top_unique
  intro x hx
  obtain ⟨y, rfl⟩ := hf x
  have hy : y ∈ f ⁻¹ᵁ X.basicOpen r := by
    rw [Scheme.preimage_basicOpen_top, Y.basicOpen_of_isUnit hr]
    trivial
  exact hy

theorem isAffineOpen_basicOpen_of_le (r : Γ(X,⊤)) (U : X.Opens)
    (hU : IsAffineOpen U) (hr : X.basicOpen r ≤ U) :
    IsAffineOpen (X.basicOpen r) := by
  have h := hU.basicOpen (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r)
  rwa [Scheme.basicOpen_res, inf_eq_right.mpr hr] at h

theorem isAffine_of_surjective_appTop (f : Y ⟶ X) [IsAffine Y]
    (hf : Function.Surjective f) (hΓ : Function.Surjective f.appTop) : IsAffine X := by
  let S : Set Γ(X,⊤) := {r | IsAffineOpen (X.basicOpen r)}
  have hcover : (⊤ : Y.Opens) ≤ ⨆ a : (f.appTop '' S), Y.basicOpen a.1 := by
    intro y hy
    obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
      (show f y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨a, haU, hya⟩ := (isAffineOpen_top Y).exists_basicOpen_le
      (⟨y, hyU⟩ : f ⁻¹ᵁ U) (by trivial)
    obtain ⟨r, hr⟩ := hΓ a
    have hrU : X.basicOpen r ≤ U := by
      intro x hx
      obtain ⟨z, rfl⟩ := hf x
      apply haU
      have hz : z ∈ f ⁻¹ᵁ X.basicOpen r := hx
      rwa [Scheme.preimage_basicOpen_top, hr] at hz
    have hrS : r ∈ S := isAffineOpen_basicOpen_of_le r U hU hrU
    exact Opens.mem_iSup.mpr ⟨⟨a, r, hrS, hr⟩, hya⟩
  have hmap : Ideal.map f.appTop.hom (Ideal.span S) = ⊤ := by
    rw [Ideal.map_span]
    exact (isAffineOpen_top Y).self_le_iSup_basicOpen_iff.mp hcover
  obtain ⟨r, hrS, hr⟩ := (Ideal.mem_map_iff_of_surjective f.appTop.hom hΓ).mp
    (show (1 : Γ(Y,⊤)) ∈ Ideal.map f.appTop.hom (Ideal.span S) by rw [hmap]; trivial)
  have hunit : IsUnit r := appTop_reflects_isUnit f hf r (hr ▸ isUnit_one)
  exact isAffine_of_isAffineOpen_basicOpen S
    ((Ideal.span S).eq_top_of_isUnit_mem hrS hunit) (fun r hr => hr)

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FullSupportNilpotence
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme}

lemma idealSheaf_le_nilradical_of_fullSupport (I : X.IdealSheafData)
    (hI : I.support = ⊤) : I ≤ X.nilradical := by
  have h : (⊤ : Closeds X) ≤ I.support := by rw [hI]
  simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h

lemma affineIdeal_isNilpotent_of_fullSupport [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) (U : X.affineOpens) :
    IsNilpotent (I.ideal U) := by
  let := IsLocallyNoetherian.component_noetherian U
  apply (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr
  exact idealSheaf_le_nilradical_of_fullSupport I hI U

theorem exists_pos_pow_eq_bot_of_fullSupport [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) :
    ∃ n : ℕ, 0 < n ∧ I ^ n = ⊥ := by
  classical
  have hlocal : ∀ U : X.affineOpens, ∃ n : ℕ, I.ideal U ^ n = ⊥ :=
    fun U => affineIdeal_isNilpotent_of_fullSupport I hI U
  choose n hn using hlocal
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.isOpen)
    (by
      intro x _
      have hx : x ∈ (⨆ U : X.affineOpens, U.1) := by
        rw [iSup_affineOpens_eq_top X]
        trivial
      obtain ⟨U, hU⟩ := Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  refine ⟨S.sup n + 1, Nat.succ_pos _, ?_⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U : S => U.val)
  · apply top_unique
    intro x _
    obtain ⟨U, hU⟩ := Set.mem_iUnion.mp (hS (show x ∈ Set.univ from trivial))
    obtain ⟨hUS, hxU⟩ := Set.mem_iUnion.mp hU
    exact Opens.mem_iSup.mpr ⟨⟨U, hUS⟩, hxU⟩
  · intro U
    change I.ideal U.val ^ (S.sup n + 1) = ⊥
    apply le_bot_iff.mp
    calc
      I.ideal U.val ^ (S.sup n + 1) ≤ I.ideal U.val ^ n U.val :=
        Ideal.pow_le_pow_right ((Finset.le_sup U.property).trans (Nat.le_succ _))
      _ = ⊥ := hn U.val

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedThickeningSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.closedMap_mono _root_.OAI.PiExponentSeshadri.IdealModule.powerMap_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

attribute [local instance] OAI.PiExponentSeshadri.Geometry.instHasExtModules_solutions
theorem globalSections_surjective_of_ext_one_zero (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X) S.X₁ 1, x = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  intro s
  obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS (Ext.mk₀ s)
    rfl (hzero _)
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

theorem closed_appTop_surjective_of_ext_one_zero (i : Y ⟶ X) [IsClosedImmersion i]
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X) (IdealModule.idealModule i) 1, x = 0) :
    Function.Surjective i.appTop := by
  let P := (Scheme.Modules.pushforward i).obj (IdealModule.unit Y)
  let S := ShortComplex.mk (IdealModule.inclusion i) (IdealModule.structureMap i)
    (kernel.condition _)
  have hlift := globalSections_surjective_of_ext_one_zero S
    (IdealModule.closedSequence_exact i) hzero
  intro y
  let t : GlobalSections X P := (moduleSectionEquiv P).symm y
  obtain ⟨s, hs⟩ := hlift t
  refine ⟨s.app ⊤ (1 : Γ(X,⊤)), ?_⟩
  have he := congrArg (fun t : GlobalSections X P => t.app ⊤ (1 : Γ(X,⊤))) hs
  exact he.trans ((moduleSectionEquiv P).apply_symm_apply y)

theorem subscheme_surjective_of_fullSupport (I : X.IdealSheafData)
    (hI : I.support = ⊤) : Function.Surjective I.subschemeι := by
  apply Set.range_eq_univ.mp
  rw [I.range_subschemeι, hI]
  rfl

theorem isAffine_of_fullSupport_of_ideal_ext_one_zero (I : X.IdealSheafData)
    (hI : I.support = ⊤) [IsAffine I.subscheme]
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X) (IdealModule.closedModule I) 1, x = 0) :
    IsAffine X :=
  isAffine_of_surjective_appTop I.subschemeι (subscheme_surjective_of_fullSupport I hI)
    (closed_appTop_surjective_of_ext_one_zero I.subschemeι hzero)

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedSupportedSerre
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
variable {X Y : Scheme.{0}}

local instance localInst_r1e6b4b_1 (Z : Scheme.{0}) : HasExt.{1} Z.Modules := HasExt.standard _
theorem ext_zero_of_moduleIso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (h : ∀ x : Abelian.Ext.{1} (structureSheaf X) N q, x = 0)
    (x : Abelian.Ext.{1} (structureSheaf X) M q) : x = 0 := by
  let E := (extFunctorObj (structureSheaf X) q).mapIso e
  apply (ConcreteCategory.bijective_of_isIso E.hom).injective
  change E.hom x = E.hom 0
  rw [map_zero]
  exact h (E.hom x)

theorem affine_closed_pushforward_ext_zero (i : Y ⟶ X) [IsClosedImmersion i]
    [IsAffine Y] [IsNoetherian Y] (M : X.Modules) (N : Y.Modules)
    [N.IsQuasicoherent] (e : M ≅ (Scheme.Modules.pushforward i).obj N)
    (q : ℕ) (hq : 0 < q) (x : Abelian.Ext.{1} (structureSheaf X) M q) : x = 0 := by
  apply ext_zero_of_moduleIso e q _ x
  apply (PiExponent.ClosedImmersionSerreTransfer.ext_zero_iff i N q).mp
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hq)
  exact AffineSchemeCohomology.affine_ext_zero Y N k

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPowerFiltration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X : Scheme.{0}}

theorem powerSequence_shortExact (I : X.IdealSheafData) (n : ℕ) :
    (powerSequence I n).ShortExact := by
  change (ShortComplex.mk (powerMap I n) (cokernel.π (powerMap I n)) _).ShortExact
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (powerMap I n)) }

theorem closedModule_bot_isZero : IsZero (closedModule (⊥ : X.IdealSheafData)) := by
  have hmono : Mono (structureMap (Scheme.IdealSheafData.subschemeι (⊥ : X.IdealSheafData))) := by
    let F := Scheme.Modules.toPresheafOfModules X
    apply F.mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U
    exact (ConcreteCategory.bijective_of_isIso
      ((⊥ : X.IdealSheafData).subschemeι.app U.unop)).injective
  exact isZero_kernel_of_mono _

theorem powerModule_eventually_isZero [IsNoetherian X] (I : X.IdealSheafData)
    (hI : I.support = ⊤) : ∃ n : ℕ, 0 < n ∧ IsZero (closedModule (I^n)) := by
  obtain ⟨n, hn, he⟩ := Geometry.exists_pos_pow_eq_bot_of_fullSupport I hI
  exact ⟨n,hn,he ▸ closedModule_bot_isZero⟩

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_IdealPowerCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

attribute [local instance] OAI.PiExponentSeshadri.IdealModule.instHasExtModules_solutions
theorem ext_eq_zero_of_isZero (A M : X.Modules) (hM : IsZero M) (q : ℕ)
    (x : Abelian.Ext.{1} A M q) : x = 0 := by
  have hz := (extFunctorObj A q).map_isZero hM
  exact @Subsingleton.elim _ (AddCommGrpCat.subsingleton_of_isZero hz) x 0

theorem powerModule_twist_ext_zero_of_layers (I : X.IdealSheafData) (L : LineBundle X)
    (N n q : ℕ) (hN : IsZero (closedModule (I^N)))
    (hLayer : ∀ k < N, ∀ x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (powerLayer I k)) q, x = 0)
    (k : ℕ) (hk : k ≤ N)
    (x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (closedModule (I^k))) q) : x = 0 := by
  have hzero : ∀ k ≤ N, ∀ x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (closedModule (I^k))) q, x = 0 := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      exact ext_eq_zero_of_isZero _ _ ((moduleTwistFunctor L n).map_isZero hN) q
    | @of_succ k hk ih =>
      intro x
      let S := (powerSequence I k).map (moduleTwistFunctor L n)
      have hS : S.ShortExact := moduleTwistFunctor_shortExact L n _ (powerSequence_shortExact I k)
      obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₂ (structureSheaf X) hS x
        (hLayer k hk _)
      have hiy : y = 0 := ih y
      exact hy.symm.trans
        ((congrArg (fun z : Abelian.Ext.{1} (structureSheaf X) S.X₁ q =>
          z.comp (Ext.mk₀ S.f) (add_zero q)) hiy).trans
            (Ext.zero_comp (structureSheaf X) q (Ext.mk₀ S.f) q (add_zero q)))
  exact hzero k hk x

theorem powerModule_ext_zero_of_layers (I : X.IdealSheafData)
    (N q : ℕ) (hN : IsZero (closedModule (I^N)))
    (hLayer : ∀ k < N, ∀ x : Abelian.Ext.{1} (structureSheaf X) (powerLayer I k) q, x = 0)
    (k : ℕ) (hk : k ≤ N)
    (x : Abelian.Ext.{1} (structureSheaf X) (closedModule (I^k)) q) : x = 0 := by
  let L : LineBundle X := {
    sheaf := structureSheaf X
    locallyRankOne := fun x => ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso _⟩⟩ }
  exact powerModule_twist_ext_zero_of_layers I L N 0 q hN hLayer k hk x

attribute [local irreducible] closedModule moduleTwistFunctor powerLayer

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ModulePullbackCoherent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponent.FiniteGlobalPresentation

theorem pullback_isFinitePresentation {X Y : Scheme.{0}} (f : Y ⟶ X)
    (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_localPresentations
  intro y
  obtain ⟨U, hy, P, hP⟩ := exists_local_finitePresentation M (f y)
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤
      SheafOfModules (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
    Scheme.Modules.pullback (f ∣_ U)
  let : PreservesColimitsOfSize.{0,0} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).leftAdjoint_preservesColimits
  let Q := P.map F (pullbackUnitIso (f ∣_ U)).symm
  let e := (pullbackRestrictNatIso f U).app M
  exact ⟨f ⁻¹ᵁ U, hy, presentationOfIso (f ⁻¹ᵁ U).toScheme e.symm Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPowerDescent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.ClosedAnnihilatedDescent
variable {X : Scheme.{0}}

instance descendedPowerLayer_isFinitePresentation [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (n : ℕ) : (descendedPowerLayer I n).IsFinitePresentation := by
  have := powerLayer_isFinitePresentation I n
  exact pullback_isFinitePresentation I.subschemeι (powerLayer I n)

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_NilpotentIdealVanishing
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.IdealModule
variable {X : Scheme.{0}}
attribute [local irreducible] closedModule powerLayer moduleTwistFunctor

local instance localInst_r1e6b4b_2 : HasExt.{1} X.Modules := HasExt.standard _
theorem fullSupport_ideal_ext_zero_of_isAffine [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) [IsAffine I.subscheme]
    (q : ℕ) (hq : 0 < q) (x : Abelian.Ext.{1} (structureSheaf X) (closedModule I) q) : x = 0 := by
  let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : IsNoetherian I.subscheme := {}
  obtain ⟨N,hNpos,hN⟩ := powerModule_eventually_isZero I hI
  have hLayer (k : ℕ) (_hk : k < N)
      (z : Abelian.Ext.{1} (structureSheaf X) (powerLayer I k) q) : z = 0 := by
    let : (descendedPowerLayer I k).IsQuasicoherent :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
        (descendedPowerLayer I k)).choose.isQuasicoherent
    exact affine_closed_pushforward_ext_zero I.subschemeι (powerLayer I k)
      (descendedPowerLayer I k) (powerLayerPushforwardIso I k).symm q hq z
  have h := powerModule_ext_zero_of_layers I N q hN hLayer 1 hNpos
  have h' : ∀ z : Abelian.Ext.{1} (structureSheaf X) (closedModule I) q, z = 0 :=
    (congrArg (fun J : X.IdealSheafData =>
      ∀ z : Abelian.Ext.{1} (structureSheaf X) (closedModule J) q, z = 0) (pow_one I)).mp h
  exact h' x

theorem isAffine_of_fullSupport [IsNoetherian X] (I : X.IdealSheafData)
    (hI : I.support = ⊤) [IsAffine I.subscheme] : IsAffine X :=
  isAffine_of_fullSupport_of_ideal_ext_one_zero I hI
    (fullSupport_ideal_ext_zero_of_isAffine I hI 1 (by decide))

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_NilpotentAmpleDescent
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem isAffineOpen_of_fullSupport_preimage_q68_oai [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) (U : X.Opens)
    (hU : IsAffineOpen (I.subschemeι ⁻¹ᵁ U)) : IsAffineOpen U := by
  let : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.ι
  let : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : CompactSpace U.toScheme := NoetherianSpace.compactSpace U.toScheme
  let : IsNoetherian U.toScheme := {}
  let J := I.comap U.ι
  have hJ : J.support = ⊤ := by
    dsimp only [J]
    rw [Scheme.IdealSheafData.support_comap, hI]
    rfl
  let e : J.subscheme ≅ (I.subschemeι ⁻¹ᵁ U).toScheme :=
    I.comapIso U.ι ≪≫ pullbackSymmetry _ _ ≪≫ pullbackRestrictIsoRestrict I.subschemeι U
  let : IsAffine (I.subschemeι ⁻¹ᵁ U).toScheme := hU
  let : IsAffine J.subscheme := IsAffine.of_isIso e.hom
  exact isAffine_of_fullSupport J hJ

end
end PiExponentSeshadri.Geometry

end OAI
end

theorem solution : type_of% @OAI.PiExponentSeshadri.Geometry.isAffineOpen_of_fullSupport_preimage_q68_oai := @OAI.PiExponentSeshadri.Geometry.isAffineOpen_of_fullSupport_preimage_q68_oai
