-- Prove2me | solution 1 for OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_section_comparison_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:23:29.511025+00:00
-- url     : https://prove2.me/submissions/3e12b305-d0c4-4482-9dbb-d46f068626c1

import Mathlib
import Definitions.Def_OAIQ068A040
import Definitions.Def_OAIQ068A041
import Definitions.Def_OAIQ068A042
import Theorems.Thm_OAI_PiExponent_GeometrySupport_NoetherianAmpleSerreVanishing_ample_power_cohomology_zero_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechHigher
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechHigher

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open CechOne
open scoped BigOperators

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

theorem map_sub {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ}
    (c e : Cochain R U M q) :
    map R U M g (c - e) = map R U M g c - map R U M g e := by
  funext t
  exact Preadditive.sub_comp _ _ _

theorem shortExact_global_lift (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i)
    (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (hzero : ∀ (t : Fin 1 → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (hprimitive : HasPrimitives R U S.X₁ 0) (f : freeOpen R V ⟶ S.X₃) :
    ∃ g : freeOpen R V ⟶ S.X₂, g ≫ S.g = f := by
  let c := augmentation R U S.X₃ V hUV f
  obtain ⟨b, a, hb, ha, hclosed⟩ := connecting_cocycle R U S hS hzero c
    (augmentation_closed R U S.X₃ V hUV f)
  obtain ⟨e, he⟩ := hprimitive a hclosed
  have hcorrected : differential R U S.X₂ (b - map R U S.X₁ S.f e) = 0 := by
    rw [differential_sub, ← map_differential, he, ha, sub_self]
  obtain ⟨g, hg⟩ := glue_zero_cocycle R U S.X₂ V hUV hcover _ hcorrected
  refine ⟨g, ?_⟩
  apply hom_ext R U V hUV hcover S.X₃
  intro i
  rw [restrictHom_comp, hg i]
  change (restrictHom R _ (b (fun _ => i) - e (fun _ => i) ≫ S.f)) ≫ S.g = _
  erw [restrictHom_sub, Preadditive.sub_comp, ← restrictHom_comp,
    ← restrictHom_comp, Category.assoc, S.zero, comp_zero]
  simp only [restrictHom, comp_zero, sub_zero]
  have hi := congrFun hb (fun _ => i)
  change b (fun _ => i) ≫ S.g = c (fun _ => i) at hi
  rw [hi]
  exact sectionZero_augmentation R U S.X₃ V hUV f i

theorem ext_one_eq_zero (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i)
    (hzero : ∀ (t : Fin 1 → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) M 1), x = 0)
    (hprimitive : HasPrimitives R U M 0)
    (x : Ext.{u+1} (freeOpen R V) M 1) : x = 0 := by
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (freeOpen R V) hS x
    (Ext.eq_zero_of_injective _) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  obtain ⟨g, rfl⟩ := shortExact_global_lift R U V hUV hcover S hS hzero hprimitive f
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass, Ext.comp_zero] at hy
  exact hy.symm

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

end
end PiExponent.GeometrySupport.CechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SerreSectionLifting
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.SerreSectionLifting
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem globalSections_surjective_of_h1_zero
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hzero : ∀ x : cohomology S.X₁ 1, x = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  intro s
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS
    (Ext.mk₀ s) (n₁ := 1) rfl (hzero _)
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

end
end PiExponent.GeometrySupport.SerreSectionLifting

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechOneConverse
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.CechOneConverse
section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

theorem hasPrimitives_of_ext_one_zero (V : Opens X)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (hzero : ∀ x : Ext.{u+1} (freeOpen R V) M 1, x = 0) :
    CechHigher.HasPrimitives R U M 0 := by
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  let : Mono S.f := hS.mono_f
  intro c hc
  have hcI : differential R U S.X₂ (CechHigher.map R U M S.f c) = 0 := by
    rw [← map_differential, hc, CechHigher.map_zero]
  obtain ⟨b, hb⟩ := FreeCechSections.injective_hasPrimitives U R S.X₂ 0
    (CechHigher.map R U M S.f c) hcI
  have hcomp : CechHigher.map R U S.X₂ S.g (CechHigher.map R U M S.f c) = 0 := by
    funext t
    change (c t ≫ S.f) ≫ S.g = 0
    rw [Category.assoc, S.zero, comp_zero]
  have hclosed : differential R U S.X₃ (CechHigher.map R U S.X₂ S.g b) = 0 := by
    rw [← map_differential, hb, hcomp]
  obtain ⟨g, hg⟩ := CechZero.augmentation_exists R U S.X₃ V hUV hcover _ hclosed
  obtain ⟨t, ht⟩ := CechOne.lift_of_ext_one_zero R S hS V hzero g
  have hkernel : CechHigher.map R U S.X₂ S.g
      (b - augmentation R U S.X₂ V hUV t) = 0 := by
    rw [CechHigher.map_sub, ← CechZero.augmentation_comp, ht, hg, sub_self]
  obtain ⟨a, ha⟩ := lift_kernel_cochain R U S hS _ hkernel
  refine ⟨a, ?_⟩
  apply map_injective R U M S.f
  rw [map_differential, ha, differential_sub, augmentation_closed, sub_zero, hb]

end

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
universe u
variable {Y : Scheme.{u}} {J : Type u} (U : J → Y.Opens) (M : Y.Modules)

attribute [local instance] OAI.PiExponent.GeometrySupport.CechOneConverse.instHasExtModules_solutions
theorem hasPrimitives_of_cohomology_one_zero
    (hcover : (⨆ i, U i) = ⊤)
    (hzero : ∀ x : Ext.{u+1} (C := Y.Modules) schemeUnit M 1, x = 0) :
    CechHigher.HasPrimitives Y.ringCatSheaf U M 0 := by
  let e : schemeFreeOpen ⊤ ≅ schemeUnit :=
    PiExponentSeshadri.FreeOpenUnit.freeTopIso Y.ringCatSheaf
  apply hasPrimitives_of_ext_one_zero Y.ringCatSheaf U M ⊤ (fun _ => le_top)
    (by rw [hcover])
  change ∀ x : Ext.{u+1} (C := Y.Modules) (schemeFreeOpen ⊤) M 1, x = 0
  intro x
  have h := congrArg (fun z => (Ext.mk₀ e.hom).comp z (zero_add 1))
    (hzero ((Ext.mk₀ e.inv).comp x (zero_add 1)))
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

end PiExponent.GeometrySupport.CechOneConverse

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechH1Transfer
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechH1Transfer
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher

universe u
variable {X Y : Scheme.{u}} {J : Type u}

attribute [local instance] freeOpenHomAddCommGroup higherCochainAddCommGroup
  PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

namespace SectionComparison
variable {U : J → X.Opens} {V : J → Y.Opens} {M : X.Modules} {N : Y.Modules}
    (P : SectionComparison U V M N)

theorem cochainOne_injective : Function.Injective P.cochainOne := by
  intro a b h
  funext t
  exact P.pair_injective t (congrFun h t)

theorem map_differential_zero (b : CechHigher.Cochain X.ringCatSheaf U M 0) :
    P.cochainOne (differential X.ringCatSheaf U M b) =
      differential Y.ringCatSheaf V N (P.cochainZero b) := by
  funext t
  change P.pair t (∑ k : Fin 2, (-1 : ℤ) ^ k.val •
    restrictHom X.ringCatSheaf (faceLE U t k) (b (t ∘ k.succAbove))) = _
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [map_zsmul, P.pair_restrict]
  rfl

theorem map_differential_one (b : CechHigher.Cochain X.ringCatSheaf U M 1) :
    P.cochainTwo (differential X.ringCatSheaf U M b) =
      differential Y.ringCatSheaf V N (P.cochainOne b) := by
  funext t
  change P.triple t (∑ k : Fin 3, (-1 : ℤ) ^ k.val •
    restrictHom X.ringCatSheaf (faceLE U t k) (b (t ∘ k.succAbove))) = _
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [map_zsmul, P.triple_restrict]
  rfl

include P

theorem hasPrimitives (h : CechHigher.HasPrimitives Y.ringCatSheaf V N 0) :
    CechHigher.HasPrimitives X.ringCatSheaf U M 0 := by
  intro c hc
  have hclosed : differential Y.ringCatSheaf V N (P.cochainOne c) = 0 := by
    rw [← P.map_differential_one, hc]
    exact P.cochainTwo.map_zero
  obtain ⟨b, hb⟩ := h (P.cochainOne c) hclosed
  refine ⟨P.cochainZero.symm b, ?_⟩
  apply P.cochainOne_injective
  rw [P.map_differential_zero, AddEquiv.apply_symm_apply, hb]

theorem cohomology_one_zero [IsNoetherian X] [M.IsQuasicoherent]
    (hU : ∀ i, IsAffineOpen (U i)) (hcoverU : (⨆ i, U i) = ⊤)
    (hcoverV : (⨆ i, V i) = ⊤)
    (hN : ∀ z : Ext.{u+1} (C := Y.Modules) (schemeUnit Y) N 1, z = 0)
    (x : Ext.{u+1} (C := X.Modules) (schemeUnit X) M 1) : x = 0 := by
  have hprimitive := P.hasPrimitives
    (CechOneConverse.hasPrimitives_of_cohomology_one_zero V N hcoverV hN)
  have hz : ∀ z : Ext.{u+1} (C := X.Modules) (schemeFreeOpen X ⊤) M 1, z = 0 := by
    apply CechHigher.ext_one_eq_zero X.ringCatSheaf U M ⊤ (fun _ => le_top)
      (by rw [hcoverU]) _ hprimitive
    intro t z
    have he : intersection U t = U (t 0) := by
      apply le_antisymm (iInf_le _ 0)
      apply le_iInf
      intro i
      exact le_of_eq (congrArg (fun j => U (t j)) (Subsingleton.elim 0 i))
    have ha : IsAffineOpen (intersection U t) := he.symm ▸ hU (t 0)
    exact PiExponentSeshadri.FiniteCoverCohomology.affine_open_ext_zero
      (intersection U t) ha M 0 z
  let e : schemeFreeOpen X ⊤ ≅ schemeUnit X :=
    PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf
  have h := congrArg (fun z => (Ext.mk₀ e.inv).comp z (zero_add 1))
    (hz ((Ext.mk₀ e.hom).comp x (zero_add 1)))
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

end SectionComparison
end
end PiExponent.GeometrySupport.CechH1Transfer

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactJetIdealCoherent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.closedMap_mono _root_.OAI.PiExponentSeshadri.IdealModule.powerMap_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace PiExponent.CompactJetIdeal


theorem closedModule_isFinitePresentation {X : Scheme} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) :
    (PiExponentSeshadri.IdealModule.closedModule I).IsFinitePresentation := by
  let : (PiExponentSeshadri.IdealModule.unit X).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (PiExponentSeshadri.IdealModule.unit I.subscheme).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : ((Scheme.Modules.pushforward I.subschemeι).obj
      (PiExponentSeshadri.IdealModule.unit I.subscheme)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward I.subschemeι).obj
        (PiExponentSeshadri.IdealModule.unit I.subscheme))).choose.isQuasicoherent
  exact FiniteGlobalPresentation.kernel_isFinitePresentation
    (PiExponentSeshadri.IdealModule.structureMap I.subschemeι)

end PiExponent.CompactJetIdeal
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupJetSurjectivity
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.closedMap_mono _root_.OAI.PiExponentSeshadri.IdealModule.powerMap_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

variable {X B : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem jetRestriction_surjective_of_h1_zero
    (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (hzero : ∀ x : cohomology (twistedIdeal I A n) 1, x = 0) :
    Function.Surjective (jetRestriction I A n) := by
  let S := ShortComplex.mk (PiExponentSeshadri.IdealModule.inclusion (I ^ n).subschemeι)
    (PiExponentSeshadri.IdealModule.structureMap (I ^ n).subschemeι) (kernel.condition _)
  have hS : S.ShortExact := PiExponentSeshadri.IdealModule.closedSequence_exact (I ^ n).subschemeι
  have hsurj := SerreSectionLifting.globalSections_surjective_of_h1_zero
    (S.map (moduleTwistFunctor A n)) (moduleTwistFunctor_shortExact A n S hS) hzero
  intro s
  obtain ⟨t, ht⟩ := hsurj s
  refine ⟨t ≫ (moduleTwistUnitIso A n).hom, ?_⟩
  change t ≫ (moduleTwistFunctor A n).map
    (PiExponentSeshadri.IdealModule.structureMap (I ^ n).subschemeι) = s at ht
  change (t ≫ (moduleTwistUnitIso A n).hom) ≫ (moduleTwistUnitIso A n).inv ≫ _ = s
  erw [Category.assoc, Iso.hom_inv_id_assoc]
  exact ht

theorem eventual_jetRestriction_surjective_of_ample_comparison
    [IsNoetherian X]
    (f : B ⟶ X) (p : B ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (F : LineBundle B) (hF : LineBundle.IsAmple B F)
    {J : Type} (U : J → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤)
    (hcomparison : ∃ N, ∀ n, N ≤ n → Nonempty
      (CechH1Transfer.SectionComparison U (fun i => f ⁻¹ᵁ U i)
        (twistedIdeal I A n) (modulePow B F.sheaf n))) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  obtain ⟨N₁, hN₁⟩ := NoetherianAmpleSerreVanishing.ample_power_cohomology_zero_q68 p F hF
  obtain ⟨N₂, hN₂⟩ := hcomparison
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  apply jetRestriction_surjective_of_h1_zero I A n
  let : (PiExponentSeshadri.IdealModule.closedModule (I ^ n)).IsFinitePresentation :=
    CompactJetIdeal.closedModule_isFinitePresentation (I ^ n)
  let : (twistedIdeal I A n).IsFinitePresentation :=
    FiniteGlobalPresentation.moduleTwist_isFinitePresentation A n _
  let : (twistedIdeal I A n).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (twistedIdeal I A n)).choose.isQuasicoherent
  obtain ⟨P⟩ := hN₂ n ((le_max_right _ _).trans hn)
  apply P.cohomology_one_zero hU hcover _ (hN₁ n ((le_max_left _ _).trans hn) 1 (by decide))
  exact f.iSup_preimage_eq_top hcover

end
end PiExponent.BlowupJetSurjectivity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_GlobalBlowupJetSurjectivity
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_blowup_jetRestriction_surjective_of_section_comparison_q68_oai
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A))
    {J : Type} (U : J → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤)
    (hcomparison : ∃ N, ∀ n, N ≤ n → Nonempty
      (CechH1Transfer.SectionComparison U
        (fun i => PiExponentSeshadri.BlowupGluing.projection I ⁻¹ᵁ U i)
        (twistedIdeal I A n)
        (modulePow (PiExponentSeshadri.BlowupGluing.scheme I) (blowupBundle I A).sheaf n))) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  exact eventual_jetRestriction_surjective_of_ample_comparison
    (PiExponentSeshadri.BlowupGluing.projection I)
    (PiExponentSeshadri.BlowupGluing.projection I ≫ p) I A (blowupBundle I A)
    hample U hU hcover hcomparison

end
end PiExponent.BlowupJetSurjectivity

end OAI
end

theorem solution : type_of% @OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_section_comparison_q68_oai := @OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_section_comparison_q68_oai
