-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.exists_nonzero_power_section_of_euler_growth_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:38:25.536722+00:00
-- url     : https://prove2.me/submissions/b1d514da-9fe9-49d2-b7f3-6cd459e86555

import Mathlib
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_GeometrySupport_NoetherianAmpleSerreVanishing_ample_serre_tensor_vanishing_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleAllPowersGeneration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AmpleGlobalGeneration
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem ample_eventual_global_generators [NoetherianSpace X]
    (L : LineBundle X) (hL : L.IsAmple) (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor L n).obj M).GeneratingSections, G.IsFiniteType := by
  classical
  obtain ⟨d, hd, l, s, hcover, haffine, _⟩ := L.ample_common_degree_cover hL
  have hresidue (r : Fin d) : ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor (L.pow d) n).obj
        ((moduleTwistFunctor L r.val).obj M)).GeneratingSections, G.IsFiniteType := by
    let := PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation L r.val M
    exact eventual_global_generators_of_section_cover (L.pow d)
      ((moduleTwistFunctor L r.val).obj M) s hcover haffine
  choose N hN using hresidue
  let B := Finset.univ.sup N
  refine ⟨d * B, fun n hn => ?_⟩
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  have hB : B ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by
    simpa only [Nat.mul_comm] using hn)
  have hr : N r ≤ n / d := (Finset.le_sup (f := N) (Finset.mem_univ r)).trans hB
  obtain ⟨G, hG⟩ := hN r (n / d) hr
  let : G.IsFiniteType := hG
  let e : ((moduleTwistFunctor (L.pow d) (n / d)).obj
      ((moduleTwistFunctor L r.val).obj M)) ≅ (moduleTwistFunctor L n).obj M :=
    moduleTwistPowerMulIso L ((moduleTwistFunctor L r.val).obj M) d (n / d) ≪≫
      eqToIso (by
        change (moduleTwistFunctor L (n % d) ⋙
          moduleTwistFunctor L (d * (n / d))).obj M = _
        rw [← moduleTwistFunctor_add, Nat.mod_add_div])
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e G, ⟨hG.finite⟩⟩

theorem ample_eventual_power_global_generators [NoetherianSpace X]
    (L : LineBundle X) (hL : L.IsAmple) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : (modulePow X L.sheaf n).GeneratingSections, G.IsFiniteType := by
  let : (structureSheaf X).IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  obtain ⟨N, hN⟩ := ample_eventual_global_generators L hL (structureSheaf X)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨G, hG⟩ := hN n hn
  let : G.IsFiniteType := hG
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso (moduleTwistUnitIso L n) G,
    ⟨hG.finite⟩⟩

end
end PiExponent.AmpleGlobalGeneration

end OAI
end

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

local instance instHasExtModules_solutions_r28386d_1 : HasExt.{u+1} X.Modules := HasExt.standard _
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
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_NakaiCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem cohomologyMap_bijective_of_quotient_vanishing
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ) (hprev : ∀ z : cohomology S.X₃ n, z = 0)
    (hnext : ∀ z : cohomology S.X₃ (n+1), z = 0) :
    Function.Bijective (cohomologyMap p S.f (n+1)) := by
  let := Module.compHom (cohomology S.X₁ (n+1)) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ (n+1)) (baseScalars p)
  constructor
  · apply (injective_iff_map_eq_zero (cohomologyMap p S.f (n+1))).mpr
    intro a ha
    obtain ⟨b,hb⟩ := Ext.covariant_sequence_exact₁ (structureSheaf X) hS a ha rfl
    rw [hprev b, Ext.zero_comp] at hb
    exact hb.symm
  · intro b
    exact Ext.covariant_sequence_exact₂ (structureSheaf X) hS b (hnext _)

theorem cohomologyDimension_eq_of_quotient_vanishing
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ) (hprev : ∀ z : cohomology S.X₃ n, z = 0)
    (hnext : ∀ z : cohomology S.X₃ (n+1), z = 0) :
    cohomologyDimension p S.X₁ (n+1) = cohomologyDimension p S.X₂ (n+1) := by
  let := Module.compHom (cohomology S.X₁ (n+1)) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ (n+1)) (baseScalars p)
  exact (LinearEquiv.ofBijective (cohomologyMap p S.f (n+1))
    (cohomologyMap_bijective_of_quotient_vanishing p S hS n hprev hnext)).finrank_eq

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_NakaiEulerGrowth
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Filter
open PiExponentSeshadri.Geometry
open scoped BigOperators

variable {X : Scheme.{0}}

theorem exists_nonzero_globalSection_of_cohomologyDimension_pos
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules)
    (hpos : 0 < cohomologyDimension p M 0) :
    ∃ s : GlobalSections X M, s ≠ 0 := by
  let := Module.compHom (cohomology M 0) (baseScalars p)
  have : Nontrivial (cohomology M 0) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨z,hz⟩ := exists_ne (0 : cohomology M 0)
  refine ⟨Ext.homEquiv₀ z, ?_⟩
  intro hs
  apply hz
  have hzero := congrArg (fun s : GlobalSections X M => Ext.mk₀ s) hs
  simpa only [Ext.mk₀_homEquiv₀_apply, Ext.mk₀_zero] using hzero

theorem eulerCharacteristic_eq_zero_sub_one_add_tail
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ) (hd : 1 ≤ d) :
    eulerCharacteristic p d M =
      (cohomologyDimension p M 0 : ℤ) - (cohomologyDimension p M 1 : ℤ) +
        ∑ i ∈ Finset.range (d - 1),
          (-1 : ℤ) ^ (i + 2) * (cohomologyDimension p M (i + 2) : ℤ) := by
  unfold eulerCharacteristic
  rw [show d + 1 = 2 + (d - 1) by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    pow_zero, one_mul, zero_add, pow_one, neg_one_mul]
  simp only [Nat.add_comm 2, sub_eq_add_neg]

theorem eventually_nonzero_globalSection_of_euler_growth
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F : ℕ → X.Modules)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d (F n)) atTop atTop)
    (hconstant : ∀ i, 2 ≤ i → i ≤ d →
      ∃ c : ℕ, ∀ᶠ n in atTop, cohomologyDimension p (F n) i = c) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X (F n), s ≠ 0 := by
  classical
  have hh (i : Fin (d - 1)) :
      ∃ c : ℕ, ∀ᶠ n in atTop, cohomologyDimension p (F n) (i.val + 2) = c := by
    apply hconstant (i.val + 2) (by omega) (by have := i.isLt; omega)
  choose c hc using hh
  let C : ℤ := ∑ i : Fin (d - 1), (-1 : ℤ) ^ (i.val + 2) * (c i : ℤ)
  have hall : ∀ᶠ n in atTop,
      ∀ i : Fin (d - 1), cohomologyDimension p (F n) (i.val + 2) = c i :=
    Filter.eventually_all.mpr hc
  have hlarge : ∀ᶠ n in atTop, C < eulerCharacteristic p d (F n) :=
    hgrowth.eventually (eventually_gt_atTop C)
  filter_upwards [hall, hlarge] with n hn hχ
  apply exists_nonzero_globalSection_of_cohomologyDimension_pos p (F n)
  have htail : (∑ i ∈ Finset.range (d - 1),
      (-1 : ℤ) ^ (i + 2) * (cohomologyDimension p (F n) (i + 2) : ℤ)) = C := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hn i]
  rw [eulerCharacteristic_eq_zero_sub_one_add_tail p (F n) d hd, htail] at hχ
  have hnonneg : (0 : ℤ) ≤ (cohomologyDimension p (F n) 1 : ℤ) := Int.natCast_nonneg _
  omega

theorem eventually_nonzero_globalSection_of_eventually_stationary
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F : ℕ → X.Modules)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d (F n)) atTop atTop)
    (hstationary : ∀ i, 2 ≤ i → i ≤ d →
      ∃ N, ∀ n, N ≤ n → cohomologyDimension p (F n) i =
        cohomologyDimension p (F N) i) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X (F n), s ≠ 0 := by
  apply eventually_nonzero_globalSection_of_euler_growth p F d hd hgrowth
  intro i hi hid
  obtain ⟨N,hN⟩ := hstationary i hi hid
  refine ⟨cohomologyDimension p (F N) i, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN n hn

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GeneratorsSectionCover
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeneratorsSectionCover
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

private lemma epi_iso_comp {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (f : B ⟶ D) (e : D ≅ E) [Epi f] :
    Epi (i.hom ≫ f ≫ e.hom) := inferInstance

theorem free_sum_projection_inclusion {ι : Type} [Fintype ι] [DecidableEq ι] :
    (∑ i : ι, freeProjection (X := X) i ≫ schemeInclusion i) =
      𝟙 (schemeFree X ι) := by
  apply (SheafOfModules.isColimitFreeCofan ι).hom_ext
  intro j
  change schemeInclusion j.as ≫ _ = schemeInclusion j.as ≫ _
  simp only [Preadditive.comp_sum, ← Category.assoc, free_inclusion_projection]
  simp only [ite_comp, Category.id_comp, zero_comp, Fintype.sum_ite_eq, Category.comp_id]

lemma hom_sum_app {M N : X.Modules} {ι : Type} (S : Finset ι)
    (f : ι → (M ⟶ N)) (V : X.Opens) (z : Γ(M,V)) :
    (∑ i ∈ S, f i).app V z = ∑ i ∈ S, (f i).app V z := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha, Scheme.Modules.Hom.add_app]
    change (f a).app V z + (∑ i ∈ S, f i).app V z = _
    rw [ih]

theorem unit_epimorphism_cover {ι : Type} [Finite ι]
    (f : schemeFree X ι ⟶ O X) [Epi f] :
    (⨆ i : ι, isoOpen (schemeInclusion i ≫ f)) = ⊤ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply top_unique
  intro x _
  let F : X.Modules ⥤ _ := SheafOfModules.toSheaf X.ringCatSheaf
  have : F.PreservesEpimorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).PreservesEpimorphisms
  have hFf : Epi (F.map f) := F.map_epi f
  have hloc : TopCat.Presheaf.IsLocallySurjective (F.map f).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mpr hFf
  obtain ⟨V, hV, ⟨z, hz⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp hloc ⊤ (1 : Γ(X,⊤)) x trivial
  change Scheme.Modules.Hom.app f V z = X.presheaf.map (homOfLE hV).op (1 : Γ(X,⊤)) at hz
  rw [map_one] at hz
  have he : (∑ i : ι, freeProjection (X := X) i ≫ (schemeInclusion i ≫ f)) = f := by
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, free_sum_projection_inclusion, Category.id_comp]
  have hsum : (∑ i : ι, Scheme.Modules.Hom.app (schemeInclusion i ≫ f) V
      (Scheme.Modules.Hom.app (freeProjection (X := X) i) V z)) = (1 : Γ(X,V)) := by
    exact (hom_sum_app Finset.univ
      (fun i => freeProjection (X := X) i ≫ (schemeInclusion i ≫ f)) V z).symm.trans
      ((congrArg (fun q : (schemeFree X ι : X.Modules) ⟶ O X =>
        Scheme.Modules.Hom.app q V z) he).trans hz)
  have hsum' : (∑ i : ι, X.presheaf.germ V x hxV
      (Scheme.Modules.Hom.app (schemeInclusion i ≫ f) V (Scheme.Modules.Hom.app (freeProjection (X := X) i) V z))) = 1 := by
    exact (map_sum (X.presheaf.germ V x hxV).hom _ _).symm.trans
      ((congrArg (X.presheaf.germ V x hxV) hsum).trans (X.presheaf.germ V x hxV).hom.map_one)
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum (hsum' ▸ isUnit_one)
  have hc : IsUnit (X.presheaf.germ ⊤ x trivial
      (endValue (schemeInclusion i ≫ f))) := by
    let si : O X ⟶ O X := schemeInclusion i ≫ f
    let a : Γ(X,V) := Scheme.Modules.Hom.app (freeProjection (X := X) i) V z
    have ht := end_apply si V a
    have hi' : IsUnit (X.presheaf.germ V x hxV
        (a * (show Γ(X,V) from si.app V (1 : Γ(X,V))))) := ht ▸ hi
    have hc' : IsUnit (X.presheaf.germ V x hxV
        (show Γ(X,V) from si.app V (1 : Γ(X,V)))) := by
      rw [map_mul] at hi'
      exact isUnit_of_mul_isUnit_right hi'
    have hcoeff := congrArg (fun z : Γ(X,V) => X.presheaf.germ V x hxV z)
      (end_naturality si V)
    rw [X.presheaf.germ_res_apply] at hcoeff
    exact hcoeff ▸ hc'
  apply Opens.mem_iSup.mpr
  refine ⟨i, ?_⟩
  erw [isoOpen_eq_basicOpen (Iso.refl (O X))]
  change x ∈ X.basicOpen (endValue (schemeInclusion i ≫ f))
  exact (X.mem_basicOpen (endValue (schemeInclusion i ≫ f)) x (show x ∈ (⊤ : X.Opens) from trivial)).mpr hc

theorem generators_sectionOpen_cover (L : LineBundle X)
    (G : L.sheaf.GeneratingSections) [G.IsFiniteType] :
    (⨆ i : G.I, sectionOpen X (generatorSection L G i)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  let F : SheafOfModules X.ringCatSheaf ⥤ SheafOfModules U.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor U.ι
  have : PreservesColimitsOfSize.{0,0} F :=
    inferInstanceAs (PreservesColimitsOfSize.{0,0} (Scheme.Modules.restrictFunctor U.ι))
  let η := (Scheme.Modules.restrictUnitIso U.ι).symm
  let f : schemeFree U.toScheme G.I ⟶ O U.toScheme :=
    (SheafOfModules.mapFreeIso F G.I η).hom ≫ F.map G.π ≫ e.hom
  have hπ : Epi (F.map G.π) := @Functor.map_epi _ _ _ _ F _ _ _ G.π G.epi
  have : Epi f := @epi_iso_comp _ _ _ _ _ _
    (SheafOfModules.mapFreeIso F G.I η) (F.map G.π) e hπ
  let : Finite G.I := (inferInstance : G.IsFiniteType).finite
  have hf := unit_epimorphism_cover f
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show (⟨x,hx⟩ : U.toScheme) ∈ ⨆ i : G.I, isoOpen (schemeInclusion i ≫ f) by
      rw [hf]; trivial)
  have he : schemeInclusion i ≫ f =
      restrictSection U.ι (generatorSection L G i) ≫ e.hom := by
    dsimp only [f, generatorSection, restrictSection]
    erw [← Category.assoc, ← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom]
    erw [F.map_comp]
    exact Category.assoc _ _ _
  erw [he, isoOpen_postcomp, isoOpen_restrictSection] at hi
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

theorem exists_fin_section_cover (L : LineBundle X)
    (G : L.sheaf.GeneratingSections) [G.IsFiniteType] :
    ∃ k : ℕ, ∃ s : Fin k → GlobalSections X L.sheaf,
      (⨆ i, sectionOpen X (s i)) = ⊤ := by
  let : Finite G.I := (inferInstance : G.IsFiniteType).finite
  let : Fintype G.I := Fintype.ofFinite G.I
  let e := (Fintype.equivFin G.I).symm
  exact ⟨Fintype.card G.I, fun i => generatorSection L G (e i),
    (e.iSup_comp (g := fun i => sectionOpen X (generatorSection L G i))).trans
      (generators_sectionOpen_cover L G)⟩

end
end PiExponent.GeneratorsSectionCover

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SerrePowerDescent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.SerrePowerDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry

variable {X : Scheme.{0}}

theorem ext_zero_of_iso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (h : ∀ x : Ext.{1} (structureSheaf X) M q, x = 0) :
    ∀ x : Ext.{1} (structureSheaf X) N q, x = 0 := by
  let E := (extFunctorObj (structureSheaf X) q).mapIso e
  intro x
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso E.hom).surjective x
  exact (congrArg E.hom (h y)).trans E.hom.hom.map_zero

end
end PiExponent.GeometrySupport.SerrePowerDescent

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

end CartierEulerPair
end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_NakaiStationarity
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Filter
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X Y : Scheme.{0}}
attribute [local irreducible] CartierEulerPair.middleIso lineTensorAssoc moduleTensorComm
  pullbackCartierMiddleIso

theorem eventual_closed_cartierMiddle_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (f : Y ⟶ X) [IsClosedImmersion f] (A L M : LineBundle X)
    (hL : (L.pullback f).IsAmple) :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q → ∀ z : cohomology
      ((Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pullback f).obj (A.tensor ((L.pow n).tensor M)).sheaf)) q, z = 0 := by
  let T := (A.pullback f).tensor (M.pullback f)
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation T
  obtain ⟨N,hN⟩ := GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_tensor_vanishing_q68
    (f ≫ p) (L.pullback f) hL T.sheaf
  refine ⟨N,fun n hn q hq => ?_⟩
  apply (ClosedImmersionSerreTransfer.ext_zero_iff f
    ((Scheme.Modules.pullback f).obj (A.tensor ((L.pow n).tensor M)).sheaf) q).mp
  let e := pullbackCartierMiddleIso f A L M n ≪≫
    moduleTensorComm ((L.pullback f).pow n).sheaf T.sheaf
  exact GeometrySupport.SerrePowerDescent.ext_zero_of_iso e.symm q (hN n hn q hq)

theorem eventual_mixedPower_cohomology_stationary
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) (t : GlobalSections X B.sheaf)
    [Mono s] [Mono t]
    (hD : (L.pullback (zeroIdeal (L.tensor B) s).subschemeι).IsAmple)
    (hE : (L.pullback (zeroIdeal B t).subschemeι).IsAmple)
    (q : ℕ) (hq : 0 < q) :
    ∃ N, ∀ n, N ≤ n →
      cohomologyDimension p ((L.pow n).tensor M).sheaf (q+1) =
        cohomologyDimension p ((L.pow N).tensor M).sheaf (q+1) := by
  obtain ⟨D,hDN⟩ := eventual_closed_cartierMiddle_cohomology_zero p
    (zeroIdeal (L.tensor B) s).subschemeι (L.tensor B) L M hD
  obtain ⟨E,hEN⟩ := eventual_closed_cartierMiddle_cohomology_zero p
    (zeroIdeal B t).subschemeι B L M hE
  let N := max D E
  have hstep (n : ℕ) (hn : N ≤ n) :
      cohomologyDimension p ((L.pow n).tensor M).sheaf (q+1) =
        cohomologyDimension p ((L.pow (n+1)).tensor M).sheaf (q+1) := by
    have hnD : D ≤ n := (le_max_left D E).trans hn
    have hnE : E ≤ n+1 := (le_max_right D E).trans (hn.trans (Nat.le_succ n))
    have hleft := cohomologyDimension_eq_of_quotient_vanishing p
      (CartierEulerPair.leftComplex p L B M s n)
      (CartierEulerPair.left_shortExact p L B M s n) q
      (hDN n hnD q hq) (hDN n hnD (q+1) (by omega))
    have hright := cohomologyDimension_eq_of_quotient_vanishing p
      (CartierEulerPair.rightComplex p L B M t n)
      (CartierEulerPair.right_shortExact p L B M t n) q
      (hEN (n+1) hnE q hq) (hEN (n+1) hnE (q+1) (by omega))
    exact hleft.trans hright.symm
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction j with
  | zero => simp
  | succ j ih =>
    exact (hstep (N+j) (by omega)).symm.trans (ih (by omega))

theorem eventually_nonzero_mixedPower_sections_of_growth
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) (t : GlobalSections X B.sheaf)
    [Mono s] [Mono t]
    (hD : (L.pullback (zeroIdeal (L.tensor B) s).subschemeι).IsAmple)
    (hE : (L.pullback (zeroIdeal B t).subschemeι).IsAmple)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d ((L.pow n).tensor M).sheaf) atTop atTop) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X ((L.pow n).tensor M).sheaf, s ≠ 0 := by
  apply eventually_nonzero_globalSection_of_eventually_stationary p
    (fun n => ((L.pow n).tensor M).sheaf) d hd hgrowth
  intro j hj hjd
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact eventual_mixedPower_cohomology_stationary p L B M s t hD hE q (by omega)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_RegularSectionMono
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem affine_scalar_regular_on_open [IsAffine X] (r : Γ(X, ⊤))
    (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) (U : X.Opens) :
    Function.Injective (fun a : Γ(X, U) =>
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a) := by
  intro a b hab
  apply TopCat.Presheaf.section_ext X.sheaf U a b
  intro x hx
  let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  have hreg : X.presheaf.germ ⊤ x trivial r ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    IsLocalization.nonZeroDivisors_le_comap
      (((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl) (X.presheaf.stalk x) hr
  have h := congrArg (fun v : Γ(X, U) => X.presheaf.germ U x hx v) hab
  simp only [map_mul, TopCat.Presheaf.germ_res_apply] at h
  exact (isRegular_iff_mem_nonZeroDivisors.mpr hreg).left h

theorem scalarEnd_mono_of_regular [IsAffine X] (r : Γ(X, ⊤))
    (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) : Mono (scalarEnd r) := by
  have hm : Mono (scalarEnd r).val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    exact affine_scalar_regular_on_open r hr U.unop
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map hm

theorem framed_section_mono_of_regular [IsAffine X] {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M)
    (hr : coefficient e s ∈ nonZeroDivisors Γ(X, ⊤)) : Mono s := by
  have he : s ≫ e.hom = scalarEnd (coefficient e s) := by
    apply endValue_injective
    rw [endValue_scalarEnd]
    rfl
  have hm : Mono (s ≫ e.hom) := by
    rw [he]
    exact scalarEnd_mono_of_regular _ hr
  exact (mono_comp_iff_of_mono s e.hom).mp hm

theorem section_mono_of_regular_affine_frames (L : LineBundle X)
    (s : GlobalSections X L.sheaf)
    (H : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        coefficient e (restrictSection U.1.ι s) ∈
          nonZeroDivisors Γ(U.1.toScheme, ⊤)) : Mono s := by
  apply CoherentTwist.mono_of_local
  intro x
  obtain ⟨U, hx, e, he⟩ := H x
  have : IsAffine U.1.toScheme := U.2
  have hm : Mono (restrictSection U.1.ι s) := framed_section_mono_of_regular e _ he
  refine ⟨U.1, hx, ?_⟩
  let : IsIso (Scheme.Modules.restrictUnitIso U.1.ι).inv :=
    (Scheme.Modules.restrictUnitIso U.1.ι).isIso_inv
  exact (mono_comp_iff_of_isIso (Scheme.Modules.restrictUnitIso U.1.ι).inv _).mp hm

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_AssociatedPrimeAvoidance
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.AssociatedPrimeAvoidance
noncomputable section
open scoped BigOperators

theorem exists_regular_combination
    {K ι J : Type*} [Field K] [Infinite K] [Finite ι] [Fintype J]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra K (R i)]
    [∀ i, IsNoetherianRing (R i)] (a : ∀ i, J → R i)
    (hspan : ∀ i, Ideal.span (Set.range (a i)) = ⊤) :
    ∃ c : J → K, ∀ i, (∑ j, c j • a i j) ∈ nonZeroDivisors (R i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let (i : ι) : Fintype (associatedPrimes (R i) (R i)) :=
    (associatedPrimes.finite (R i) (R i)).fintype
  let B := (i : ι) × associatedPrimes (R i) (R i)
  let L (i : ι) : (J → K) →ₗ[K] R i := Fintype.linearCombination K (a i)
  let bad (b : B) : Submodule K (J → K) :=
    (b.2.val.restrictScalars K).comap (L b.1)
  have hbad : ∀ b : B, bad b ≠ ⊤ := by
    intro b hb
    apply b.2.property.isPrime.ne_top
    apply top_unique
    rw [← hspan b.1]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hm : Pi.single j (1 : K) ∈ bad b := by
      rw [hb]
      trivial
    change Fintype.linearCombination K (a b.1) (Pi.single j 1) ∈ b.2.val at hm
    rw [Fintype.linearCombination_apply_single, one_smul] at hm
    exact hm
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  refine ⟨c, fun i => ?_⟩
  by_contra hn
  have hz : (∑ j, c j • a i j) ∈ (nonZeroDivisors (R i) : Set (R i))ᶜ := hn
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors (R i)] at hz
  obtain ⟨P, hP, hmem⟩ := Set.mem_iUnion₂.mp hz
  apply hc ⟨i, ⟨P, hP⟩⟩
  change (∑ j, c j • a i j) ∈ P
  exact hmem

end
end PiExponent.GeometrySupport.AssociatedPrimeAvoidance

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_RegularSectionChoice
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem finite_affine_frame_cover [CompactSpace X] (L : LineBundle X) :
    ∃ l : ℕ, ∃ U : Fin l → X.affineOpens,
      (⨆ i, (U i).1) = ⊤ ∧
      Nonempty (∀ i, L.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme) := by
  classical
  have h (x : X) : ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) := by
    obtain ⟨U, hx, he, _⟩ := common_affine_frames L L x
    exact ⟨U, hx, he⟩
  choose U hx e using h
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((U x).1 : Set X)) (fun x => (U x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hx x⟩)
  let E := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun j => U (E j).val, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨E.symm ⟨i,hi⟩,?_⟩
    change x ∈ (U (E (E.symm ⟨i,hi⟩)).val).1
    rw [Equiv.apply_symm_apply]
    exact hx
  · exact ⟨fun j => (e (E j).val).some⟩

theorem coefficients_span_top_of_section_cover (L : LineBundle X) {k : ℕ}
    (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ j, sectionOpen X (s j)) = ⊤)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span (Set.range (fun j => coefficient e (restrictSection U.1.ι (s j)))) = ⊤ := by
  have : IsAffine U.1.toScheme := U.2
  have hc : (⨆ j, U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι (s j)))) = ⊤ := by
    exact (iSup_congr fun j => (preimage_isoOpen (s j) U.1.ι e).symm).trans
      (U.1.ι.iSup_preimage_eq_top hs)
  apply (isAffineOpen_top U.1.toScheme).iSup_basicOpen_eq_self_iff.mp
  apply top_unique
  intro x _
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ j,
    U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι (s j))) by rw [hc]; trivial)
  exact Opens.mem_iSup.mpr ⟨⟨_, Set.mem_range_self j⟩, hj⟩

private theorem iso_inv_map_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B : C} {T : D} (e : F.obj A ≅ T) (f : A ⟶ A) (s : A ⟶ B) :
    e.inv ≫ F.map (f ≫ s) = ((e.inv ≫ F.map f) ≫ e.hom) ≫ e.inv ≫ F.map s := by
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

theorem localCoefficient_scalar (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (r : Γ(X, ⊤)) (s : GlobalSections X L.sheaf) :
    coefficient e (restrictSection U.ι (scalarEnd r ≫ s)) =
      U.ι.appTop r * coefficient e (restrictSection U.ι s) := by
  have hscalar : restrictSection U.ι (scalarEnd r) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom = scalarEnd (U.ι.appTop r) := by
    apply endValue_injective
    erw [endValue_restrict U.ι (scalarEnd r), endValue_scalarEnd, endValue_scalarEnd]
  have hrestrict : restrictSection U.ι (scalarEnd r ≫ s) =
      scalarEnd (U.ι.appTop r) ≫ restrictSection U.ι s := by
    rw [← hscalar]
    exact iso_inv_map_comp (Scheme.Modules.restrictFunctor U.ι)
      (Scheme.Modules.restrictUnitIso U.ι) (scalarEnd r) s
  rw [hrestrict]
  change endValue (scalarEnd (U.ι.appTop r) ≫ restrictSection U.ι s ≫ e.hom) = _
  rw [endValue_comp, endValue_scalarEnd]
  rfl

theorem localCoefficient_linearCombination (L : LineBundle X) {k : ℕ}
    (a : ℂ →+* Γ(X, ⊤)) (s : Fin k → GlobalSections X L.sheaf) (c : Fin k → ℂ)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    coefficient e (restrictSection U.ι (sectionLinearCombination L a s c)) =
      ∑ j, U.ι.appTop (a (c j)) * coefficient e (restrictSection U.ι (s j)) := by
  change localCoefficientAddHom L U e (∑ j, scalarEnd (a (c j)) ≫ s j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact localCoefficient_scalar L U e _ _

theorem exists_mono_linearCombination_of_finite_cover [IsNoetherian X]
    (L : LineBundle X) {k : ℕ} (a : ℂ →+* Γ(X, ⊤))
    (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ j, sectionOpen X (s j)) = ⊤) :
    ∃ c : Fin k → ℂ, Mono (sectionLinearCombination L a s c) := by
  classical
  obtain ⟨l, U, hU, ⟨e⟩⟩ := finite_affine_frame_cover L
  let R (i : Fin l) : Type := Γ((U i).1.toScheme, ⊤)
  have hAff (i : Fin l) : IsAffine (U i).1.toScheme := (U i).2
  let alg (i : Fin l) : Algebra ℂ (R i) := ((U i).1.ι.appTop.hom.comp a).toAlgebra
  let (i : Fin l) : Algebra ℂ (R i) := alg i
  have hNoeth (i : Fin l) : IsNoetherianRing (R i) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (U i).1.toScheme⟩
  let b (i : Fin l) (j : Fin k) : R i := coefficient (e i) (restrictSection (U i).1.ι (s j))
  have hb (i : Fin l) : Ideal.span (Set.range (b i)) = ⊤ :=
    coefficients_span_top_of_section_cover L s hs (U i) (e i)
  obtain ⟨c, hc⟩ := GeometrySupport.AssociatedPrimeAvoidance.exists_regular_combination (K := ℂ) (ι := Fin l) (J := Fin k) R b hb
  refine ⟨c, section_mono_of_regular_affine_frames L _ ?_⟩
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, (U i).1 by rw [hU]; trivial)
  refine ⟨U i, hi, e i, ?_⟩
  rw [localCoefficient_linearCombination]
  simpa only [R, b, Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply] using hc i

theorem exists_mono_section_of_finite_cover [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) {k : ℕ}
    (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ j, sectionOpen X (s j)) = ⊤) :
    ∃ t : GlobalSections X L.sheaf, Mono t := by
  obtain ⟨c, hc⟩ := exists_mono_linearCombination_of_finite_cover L (baseScalars p) s hs
  exact ⟨sectionLinearCombination L (baseScalars p) s c, hc⟩

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerRegularTwists
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem exists_common_tensor_generators [IsNoetherian X]
    (H L : LineBundle X) (hH : H.IsAmple) :
    ∃ n : ℕ, ∃ G : (H.pow n).sheaf.GeneratingSections, G.IsFiniteType ∧
      ∃ G' : (L.tensor (H.pow n)).sheaf.GeneratingSections, G'.IsFiniteType := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  obtain ⟨N, hN⟩ := PiExponent.AmpleGlobalGeneration.ample_eventual_power_global_generators H hH
  obtain ⟨N', hN'⟩ := PiExponent.AmpleGlobalGeneration.ample_eventual_global_generators H hH L.sheaf
  let n := max N N'
  obtain ⟨G, hG⟩ := hN n (le_max_left _ _)
  obtain ⟨G', hG'⟩ := hN' n (le_max_right _ _)
  exact ⟨n, G, hG,
    SheafOfModules.GeneratingSections.equivOfIso (moduleTwistPowerIso H L.sheaf n) G',
    ⟨hG'.finite⟩⟩

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_NakaiEffectivity
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Filter
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem exists_nonzero_power_section_of_euler_growth_q68_oai
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) atTop atTop) :
    ∃ a : ℕ, 0 < a ∧ ∃ s : GlobalSections X (L.pow a).sheaf, s ≠ 0 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  obtain ⟨b,G,hG,G',hG'⟩ := exists_common_tensor_generators H L hH
  let := hG
  let := hG'
  let B := H.pow b
  obtain ⟨k,u,hu⟩ := GeneratorsSectionCover.exists_fin_section_cover B G
  obtain ⟨k',v,hv⟩ := GeneratorsSectionCover.exists_fin_section_cover (L.tensor B) G'
  obtain ⟨s,hs⟩ := exists_mono_section_of_finite_cover p (L.tensor B) v hv
  obtain ⟨t,ht⟩ := exists_mono_section_of_finite_cover p B u hu
  let := hs
  let := ht
  have hD := hlower (zeroIdeal (L.tensor B) s)
    (regular_sectionZero_dimension_le (L.tensor B) s d hdim)
  have hE := hlower (zeroIdeal B t) (regular_sectionZero_dimension_le B t d hdim)
  have heuler (n : ℕ) : eulerCharacteristic p (d+1) ((L.pow n).tensor (H.pow 0)).sheaf =
      eulerCharacteristic p (d+1) (L.pow n).sheaf :=
    eulerCharacteristic_iso p (moduleTensorRightUnit (L.pow n).sheaf) (d+1)
  have hgrowth' : Tendsto
      (fun n => eulerCharacteristic p (d+1) ((L.pow n).tensor (H.pow 0)).sheaf) atTop atTop := by
    simpa only [heuler] using hgrowth
  have hsections := eventually_nonzero_mixedPower_sections_of_growth p L B (H.pow 0)
    s t hD hE (d+1) (by omega) hgrowth'
  obtain ⟨N,hN⟩ := eventually_atTop.mp hsections
  obtain ⟨σ,hσ⟩ := hN (N+1) (by omega)
  let e := moduleTensorRightUnit (L.pow (N+1)).sheaf
  refine ⟨N+1,by omega,σ ≫ e.hom,?_⟩
  intro hz
  apply hσ
  apply (cancel_mono e.hom).mp
  exact hz.trans (zero_comp (C := X.Modules) (f := e.hom)).symm

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.exists_nonzero_power_section_of_euler_growth_q68_oai := @OAI.PiExponent.NumericalAmpleness.exists_nonzero_power_section_of_euler_growth_q68_oai
