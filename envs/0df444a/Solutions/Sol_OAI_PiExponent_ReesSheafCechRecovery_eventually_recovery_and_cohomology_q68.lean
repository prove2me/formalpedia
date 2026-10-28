-- Prove2me | solution 1 for OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_cohomology_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:46:52.319696+00:00
-- url     : https://prove2.me/submissions/201ebf2b-f3ff-4f2b-a3f6-490c4d60ead2

import Mathlib
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_GradedSerreStep_exists_syzygy_eventual_step_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesPushdown
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.ReesPushdown

open Polynomial PiExponentSeshadri.ReesGrading

variable {R : Type*} [CommRing R]

theorem eventually_no_power_torsion [IsNoetherianRing R] (I : Ideal R) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ I ^ n,
      (∃ k : ℕ, ∀ a ∈ I ^ k, a * x = 0) → x = 0 := by
  let A : ℕ →o Ideal R :=
    ⟨fun n => (I ^ n).annihilator,
      fun i j hij => Submodule.annihilator_mono (Ideal.pow_le_pow_right hij)⟩
  obtain ⟨e, he⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) A
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul (A e)
  refine ⟨c + e, ?_⟩
  intro n hn x hxn hx
  obtain ⟨k, hk⟩ := hx
  have hxA : x ∈ A k := by
    apply Submodule.mem_annihilator.mpr
    intro a ha
    simpa only [smul_eq_mul, mul_comm] using hk a ha
  have hxAe : x ∈ A e := by
    have hxmax := (A.monotone (Nat.le_max_left k e)) hxA
    rw [he (max k e) (Nat.le_max_right k e)]
    exact hxmax
  have hinter : I ^ n ⊓ A e = I ^ (n - c) * (I ^ c ⊓ A e) := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hc n (by omega)
  have hzero : I ^ n ⊓ A e ≤ ⊥ := by
    rw [hinter]
    calc
      _ ≤ I ^ e * A e := mul_le_mul' (Ideal.pow_le_pow_right (by omega)) inf_le_right
      _ = ⊥ := by
        change I ^ e * (I ^ e).annihilator = ⊥
        rw [mul_comm, Submodule.annihilator_mul]
  exact Ideal.mem_bot.mp (hzero ⟨hxn, hxAe⟩)

end PiExponent.ReesPushdown

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesPolynomialPresentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZero _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZeroClass _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesGroup _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesPolynomialPresentation
noncomputable section
open scoped BigOperators
open Polynomial PiExponentSeshadri.ReesGrading
variable {R J : Type*} [CommRing R] (I : Ideal R) (a : J → I)

theorem finite_presented_module
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    letI := presentationAlgebra I a
    Module.Finite (MvPolynomial J R) (reesAlgebra I) := by
  let := presentationAlgebra I a
  exact Module.Finite.of_surjective
    (Algebra.linearMap (MvPolynomial J R) (reesAlgebra I)) (presentation_surjective I a ha)

end
end PiExponent.ReesPolynomialPresentation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AdditiveKernelTransport
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AdditiveKernelTransport

variable {A A' B B' : Type*}
  [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']

theorem transport_primitives {A₂ B₂ : Type*} [AddCommGroup A₂] [AddCommGroup B₂]
    (e₀ : A ≃+ B) (e₁ : A' ≃+ B') (e₂ : A₂ ≃+ B₂)
    (d₀ : A →+ A') (d₁ : A' →+ A₂) (D₀ : B →+ B') (D₁ : B' →+ B₂)
    (h₀ : ∀ x, e₁ (d₀ x) = D₀ (e₀ x))
    (h₁ : ∀ x, e₂ (d₁ x) = D₁ (e₁ x))
    (hp : ∀ c, D₁ c = 0 → ∃ b, D₀ b = c) :
    ∀ c, d₁ c = 0 → ∃ b, d₀ b = c := by
  intro c hc
  have hclosed : D₁ (e₁ c) = 0 := by rw [← h₁, hc, map_zero]
  obtain ⟨b, hb⟩ := hp (e₁ c) hclosed
  refine ⟨e₀.symm b, e₁.injective ?_⟩
  rw [h₀, e₀.apply_symm_apply, hb]

end PiExponent.AdditiveKernelTransport

end OAI
end

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

theorem primitives_of_shortExact (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) (q : ℕ)
    (hzero : ∀ (t : Fin (q + 2) → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (hkernel : HasPrimitives R U S.X₁ (q + 1))
    (hmiddle : HasPrimitives R U S.X₂ q) : HasPrimitives R U S.X₃ q := by
  intro c hc
  obtain ⟨b, a, hb, ha, hclosed⟩ := connecting_cocycle R U S hS hzero c hc
  obtain ⟨e, he⟩ := hkernel a hclosed
  have hcorrected : differential R U S.X₂ (b - map R U S.X₁ S.f e) = 0 := by
    rw [differential_sub, ← map_differential, he, ha, sub_self]
  obtain ⟨v, hv⟩ := hmiddle _ hcorrected
  refine ⟨map R U S.X₂ S.g v, ?_⟩
  rw [← map_differential, hv, map_sub, hb]
  have hz : map R U S.X₂ S.g (map R U S.X₁ S.f e) = 0 := by
    funext t
    change (e t ≫ S.f) ≫ S.g = 0
    rw [Category.assoc, S.zero, comp_zero]
  rw [hz, sub_zero]

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

theorem ext_succ_eq_zero_of_injective_cech
    (V : Opens X) (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (hinjective : ∀ (I : SheafOfModules.{u} R) [Injective I] (q : ℕ),
      HasPrimitives R U I q)
    (n : ℕ)
    (hlocal : ∀ (q : ℕ) (t : Fin (q + 1) → J) (k : ℕ)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) M (k + 1)), x = 0)
    (hprimitive : HasPrimitives R U M n)
    (x : Ext.{u+1} (freeOpen R V) M (n + 1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
      exact ext_one_eq_zero R U M V hUV hcover (fun t x => hlocal 0 t 0 x) hprimitive x
  | succ n ih =>
      let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
      have hlocal' : ∀ (q : ℕ) (t : Fin (q + 1) → J) (k : ℕ)
          (y : Ext.{u+1} (freeOpen R (intersection U t)) S.X₃ (k + 1)), y = 0 := by
        intro q t k y
        obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃
          (freeOpen R (intersection U t)) hS y (n₁ := k + 2) rfl (hlocal q t (k + 1) _)
        rw [Ext.eq_zero_of_injective z, Ext.zero_comp] at hz
        exact hz.symm
      have hprimitive' : HasPrimitives R U S.X₃ n :=
        primitives_of_shortExact R U S hS n
          (fun t y => hlocal (n + 1) t 0 y) hprimitive (hinjective S.X₂ n)
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (freeOpen R V) hS x
        (Ext.eq_zero_of_injective _) (n₀ := n + 1) rfl
      rw [ih S.X₃ hlocal' hprimitive' y, Ext.zero_comp] at hy
      exact hy.symm

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

theorem affine_ext_succ_eq_zero_of_injective_cech
    (Y : Scheme.{u}) [IsNoetherian Y] (A : Y.Modules) [A.IsQuasicoherent]
    (W : J → Y.Opens) (V : Y.Opens) (hWV : ∀ i, W i ≤ V)
    (hcover : V ≤ ⨆ i, W i)
    (haffine : ∀ (q : ℕ) (t : Fin (q + 1) → J), IsAffineOpen (intersection W t))
    (hinjective : ∀ (I : Y.Modules) [Injective I] (q : ℕ),
      HasPrimitives Y.ringCatSheaf W I q)
    (n : ℕ) (hprimitive : HasPrimitives Y.ringCatSheaf W A n)
    (x : Ext.{u+1} (C := Y.Modules) (schemeFreeOpen Y V) A (n + 1)) : x = 0 := by
  exact ext_succ_eq_zero_of_injective_cech Y.ringCatSheaf W A V hWV hcover
    hinjective n (fun q t k y =>
      PiExponentSeshadri.FiniteCoverCohomology.affine_open_ext_zero
        (intersection W t) (haffine q t) A k y) hprimitive x

end
end PiExponent.GeometrySupport.CechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FreeCechSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.FreeCechSections

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechHigher FreeCechResolution
open scoped Simplicial BigOperators

universe u
variable {X : TopCat.{u}} {J : Type u} (U : J → Opens X)

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (M : SheafOfModules.{u} R)

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

theorem affine_ext_succ_eq_zero
    (Y : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian Y]
    (A : Y.Modules) [A.IsQuasicoherent]
    (W : J → Y.Opens) (V : Y.Opens) (hWV : ∀ i, W i ≤ V)
    (hcover : V ≤ ⨆ i, W i)
    (haffine : ∀ (q : ℕ) (t : Fin (q + 1) → J),
      AlgebraicGeometry.IsAffineOpen (intersection W t))
    (n : ℕ) (hprimitive : HasPrimitives Y.ringCatSheaf W A n)
    (x : CategoryTheory.Abelian.Ext.{u+1} (C := Y.Modules)
      (schemeFreeOpen Y V) A (n + 1)) : x = 0 := by
  exact affine_ext_succ_eq_zero_of_injective_cech Y A W V hWV hcover haffine
    (fun I hI q => @injective_hasPrimitives _ _ W Y.ringCatSheaf I hI q) n hprimitive x

end
end PiExponent.GeometrySupport.FreeCechSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZero _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZeroClass _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesGroup _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedCech
noncomputable section
open scoped BigOperators
open GradedLocalizationExact

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem restriction_refl (a : R) : restriction (M := M) a a dvd_rfl = LinearMap.id := by
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (divisor_powers_isUnit a a dvd_rfl)
  apply LinearMap.ext
  intro m
  exact restriction_mk_one a a dvd_rfl m

theorem restriction_comp (a b c : R) (hab : a ∣ b) (hbc : b ∣ c) :
    (restriction b c hbc).comp (restriction (M := M) a b hab) =
      restriction a c (hab.trans hbc) := by
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (divisor_powers_isUnit a c (hab.trans hbc))
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply, restriction_mk_one]

variable {σR σM : Type*} [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

section Cover
variable {J : Type*} [DecidableEq J] (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)

@[simp] theorem setRestriction_refl (s : Finset J) (d : ℤ)
    (z : IntersectionPiece 𝒜 𝓜 x hx s d) : setRestriction 𝒜 𝓜 x hx (s := s) le_rfl d z = z := by
  apply Subtype.ext
  rw [setRestriction_coe, restriction_refl]
  rfl

theorem setRestriction_comp {s t u : Finset J} (hst : s ⊆ t) (htu : t ⊆ u)
    (d : ℤ) (z : IntersectionPiece 𝒜 𝓜 x hx s d) :
    setRestriction 𝒜 𝓜 x hx htu d (setRestriction 𝒜 𝓜 x hx hst d z) =
      setRestriction 𝒜 𝓜 x hx (hst.trans htu) d z := by
  apply Subtype.ext
  simp only [setRestriction_coe]
  exact DFunLike.congr_fun (restriction_comp (coverProduct x s) (coverProduct x t)
    (coverProduct x u) (coverProduct_dvd 𝒜 x hx hst) (coverProduct_dvd 𝒜 x hx htu)) z.val

end Cover

end
end PiExponent.GradedCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_TupleCechBound
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.TupleCechBound
noncomputable section
open scoped BigOperators
open ProjectiveMonomialCechHigher
universe u
variable {J K A : Type*} [AddCommGroup A]

lemma pullback_differential (f : K → J) {q : ℕ} (c : Cochain J A q) :
    pullback f (differential c) = differential (pullback f c) := rfl

lemma contraction_closed {q : ℕ} (c : Cochain J A (q + 1))
    (hc : differential c = 0) (p : J) :
    differential (fun t : Fin (q + 1) → J => c (Fin.cons p t)) = c := by
  funext t
  have h := differential_cons c p t
  rw [hc, Pi.zero_apply] at h
  exact (sub_eq_zero.mp h.symm).symm

lemma extend_pullback (p : J) {q : ℕ} (c : Cochain {j : J // j ≠ p} A q)
    (t : Fin (q + 1) → {j : J // j ≠ p}) :
    extend p c (Subtype.val ∘ t) = c t := by
  classical
  simp only [extend, Function.comp_apply, dite_eq_left (fun i => (t i).property)]

lemma differential_extend_pullback (p : J) {q : ℕ}
    (c : Cochain {j : J // j ≠ p} A q)
    (t : Fin (q + 2) → {j : J // j ≠ p}) :
    differential (extend p c) (Subtype.val ∘ t) = differential c t := by
  simp only [differential]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun a => (-1 : ℤ) ^ i.val • a) (extend_pullback p c (t ∘ i.succAbove))

lemma extend_missing (p : J) {q : ℕ} (c : Cochain {j : J // j ≠ p} A q)
    (hc : FullSupport c) (t : Fin (q + 1) → J) (j : J) (hjp : j ≠ p)
    (ht : ∀ i, t i ≠ j) : extend p c t = 0 := by
  classical
  unfold extend
  split_ifs with h
  · apply hc _ ⟨j, hjp⟩
    intro i he
    exact ht i (congrArg Subtype.val he)
  · rfl

lemma differential_extend_missing (p : J) {q : ℕ}
    (c : Cochain {j : J // j ≠ p} A q) (hc : FullSupport c)
    (t : Fin (q + 2) → J) (j : J) (hjp : j ≠ p)
    (ht : ∀ i, t i ≠ j) : differential (extend p c) t = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [extend_missing p c hc (t ∘ i.succAbove) j hjp (fun k => ht (i.succAbove k)), smul_zero]

theorem fullSupport_primitives_aux (n : ℕ) :
    ∀ (J : Type u) [Fintype J], Fintype.card J = n →
    ∀ q : ℕ, n ≤ q + 1 → ∀ c : Cochain J A (q + 1),
      differential c = 0 → FullSupport c →
      ∃ b : Cochain J A q, differential b = c ∧ FullSupport b := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J _ hcard q hq c hc hsupport
    cases isEmpty_or_nonempty J with
    | inl hJ =>
      let := hJ
      refine ⟨0, ?_, ?_⟩
      · funext t
        exact isEmptyElim (t 0)
      · intro t
        exact isEmptyElim (t 0)
    | inr hJ =>
      let p : J := Classical.choice hJ
      let b : Cochain J A q := fun t => c (Fin.cons p t)
      have hb : differential b = c := contraction_closed c hc p
      cases q with
      | zero =>
        refine ⟨b, hb, ?_⟩
        let : Subsingleton J := Fintype.card_le_one_iff_subsingleton.mp (hcard ▸ hq)
        intro t j ht
        exact False.elim (ht 0 (Subsingleton.elim _ _))
      | succ q =>
        let K := {j : J // j ≠ p}
        have hKn : Fintype.card K < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := p) (by simp)
        let bK : Cochain K A (q + 1) := pullback Subtype.val b
        have hbK : differential bK = 0 := by
          rw [← pullback_differential, hb]
          funext t
          exact hsupport _ p (fun i => (t i).property)
        have hsK : FullSupport bK := by
          intro t j ht
          apply hsupport _ j.val
          intro i
          cases i using Fin.cases with
          | zero => exact Ne.symm j.property
          | succ i =>
            intro he
            exact ht i (Subtype.ext he)
        obtain ⟨a, ha, hs⟩ := ih (Fintype.card K) hKn K rfl q (by omega) bK hbK hsK
        refine ⟨b - differential (extend p a), ?_, ?_⟩
        · rw [differential_sub, hb, differential_squared, sub_zero]
        · intro t j ht
          change b t - differential (extend p a) t = 0
          by_cases hj : j = p
          · subst j
            let tK : Fin (q + 2) → K := fun i => ⟨t i, ht i⟩
            have hvalue := congrFun ha tK
            have hext := differential_extend_pullback p a tK
            change differential (extend p a) t = differential a tK at hext
            rw [hext, hvalue]
            exact sub_self _
          · have hb0 : b t = 0 := by
              apply hsupport _ j
              intro i
              cases i using Fin.cases with
              | zero => exact Ne.symm hj
              | succ i => exact ht i
            rw [hb0, differential_extend_missing p a hs t j hj ht, sub_self]

theorem fullSupport_primitives [Fintype J] {q : ℕ}
    (hq : Fintype.card J ≤ q + 1) (c : Cochain J A (q + 1))
    (hc : differential c = 0) (hs : FullSupport c) :
    ∃ b : Cochain J A q, differential b = c ∧ FullSupport b :=
  fullSupport_primitives_aux (Fintype.card J) J rfl q hq c hc hs

end
end PiExponent.TupleCechBound

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedCechBound
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZero _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZeroClass _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesGroup _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FiniteTupleCech
noncomputable section
open scoped BigOperators
open GradedCech (tupleSet tupleSet_comp_subset tupleSet_subset)
variable {J : Type*} [DecidableEq J] (D : Finset J → Type*)
  [∀ s, AddCommGroup (D s)]
  (r : ∀ {s t : Finset J}, s ⊆ t → D s →+ D t)
  (rid : ∀ s (z : D s), r (s := s) le_rfl z = z)
  (rcomp : ∀ {s t u : Finset J} (hst : s ⊆ t) (htu : t ⊆ u) (z : D s),
    r htu (r hst z) = r (hst.trans htu) z)

lemma differential_add {q : ℕ} (a b : Cochain D q) :
    differential D r (a + b) = differential D r a + differential D r b := by
  funext t
  simp only [differential, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

lemma differential_sub {q : ℕ} (a b : Cochain D q) :
    differential D r (a - b) = differential D r a - differential D r b := by
  funext t
  simp only [differential, Pi.sub_apply, map_sub, smul_sub, Finset.sum_sub_distrib]

include rcomp in
lemma evaluate_differential (s : Finset J) {q : ℕ} (c : Cochain D q) :
    evaluate D r s (differential D r c) =
      ProjectiveMonomialCechHigher.differential (evaluate D r s c) := by
  funext t
  simp only [evaluate, differential, ProjectiveMonomialCechHigher.differential,
    map_sum, map_zsmul, rcomp]
  rfl

include rid rcomp in
lemma differential_squared {q : ℕ} (c : Cochain D q) :
    differential D r (differential D r c) = 0 := by
  funext t
  have h := congrFun (ProjectiveMonomialCechHigher.differential_squared
    (evaluate D r (tupleSet t) c)) (liftTo (tupleSet t) t le_rfl)
  rw [← evaluate_differential D r rcomp, ← evaluate_differential D r rcomp] at h
  change r le_rfl (differential D r (differential D r c) t) = 0 at h
  simpa only [rid, Pi.zero_apply] using h

lemma tuple_card_lt_of_missing {s : Finset J} {n : ℕ} (t : Fin n → J)
    (ht : tupleSet t ⊆ s) (j : J) (hj : j ∈ s) (hmiss : ∀ i, t i ≠ j) :
    (tupleSet t).card < s.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨ht, ?_⟩
  intro he
  have hmem : j ∈ tupleSet t := he.symm ▸ hj
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  exact hmiss i hi

include rid in
lemma assemble_restrict {q k : ℕ}
    (B : ∀ s : Finset J, s.card = k → ProjectiveMonomialCechHigher.Cochain s (D s) q)
    (hB : ∀ s hs, TupleCechBound.FullSupport (B s hs))
    (s : Finset J) (hs : s.card = k) (t : Fin (q + 1) → J) (ht : tupleSet t ⊆ s) :
    r ht (assemble D B t) = B s hs (liftTo s t ht) := by
  classical
  by_cases he : tupleSet t = s
  · subst s
    simp only [assemble, dite_eq_left hs, rid]
  · have hlt : (tupleSet t).card < k := by
      rw [← hs]
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨ht, he⟩)
    rw [assemble, dite_eq_right (ne_of_lt hlt), map_zero]
    symm
    have hnot : ¬ s ⊆ tupleSet t := fun h => he (Finset.Subset.antisymm ht h)
    obtain ⟨j, hj, hjt⟩ := Finset.not_subset.mp hnot
    apply hB s hs _ ⟨j, hj⟩
    intro i hi
    have heq : t i = j := congrArg Subtype.val hi
    exact hjt (heq ▸ mem_tupleSet t i)

lemma differential_assemble_below {q k : ℕ}
    (B : ∀ s : Finset J, s.card = k → ProjectiveMonomialCechHigher.Cochain s (D s) q)
    (t : Fin (q + 2) → J) (ht : (tupleSet t).card < k) :
    differential D r (assemble D B) t = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hle := Finset.card_le_card (tupleSet_comp_subset t i.succAbove)
  have hne : (tupleSet (t ∘ i.succAbove)).card ≠ k := by omega
  simp only [assemble, dite_eq_right hne, map_zero, smul_zero]

variable [Fintype J]

include rid rcomp in

theorem level_correction {q k : ℕ} (hq : Fintype.card J ≤ q + 1)
    (c : Cochain D (q + 1)) (hc : differential D r c = 0)
    (hv : ∀ t, (tupleSet t).card < k → c t = 0) :
    ∃ b : Cochain D q,
      (∀ t, (tupleSet t).card < k → differential D r b t = 0) ∧
      (∀ t, (tupleSet t).card = k → differential D r b t = c t) := by
  classical
  have hlocal (s : Finset J) (hs : s.card = k) :
      ∃ b : ProjectiveMonomialCechHigher.Cochain s (D s) q,
        ProjectiveMonomialCechHigher.differential b = evaluate D r s c ∧
        TupleCechBound.FullSupport b := by
    apply TupleCechBound.fullSupport_primitives
    · simpa only [Fintype.card_coe] using (Finset.card_le_univ s).trans hq
    · rw [← evaluate_differential D r rcomp, hc]
      funext t
      exact map_zero _
    · intro t j hj
      have hsub := tupleSet_subset s Subtype.val (fun j => j.property) t
      have hlt : (tupleSet (Subtype.val ∘ t)).card < k := by
        rw [← hs]
        apply tuple_card_lt_of_missing (Subtype.val ∘ t) hsub j.val j.property
        intro i he
        exact hj i (Subtype.ext he)
      change r hsub (c (Subtype.val ∘ t)) = 0
      rw [hv _ hlt, map_zero]
  choose B hB hfull using hlocal
  refine ⟨assemble D B, differential_assemble_below D r B, ?_⟩
  intro t ht
  let s := tupleSet t
  calc
    differential D r (assemble D B) t =
        ProjectiveMonomialCechHigher.differential (B s ht) (liftTo s t le_rfl) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z => (-1 : ℤ) ^ i.val • z)
        (assemble_restrict D r rid B hfull s ht (t ∘ i.succAbove)
          (tupleSet_comp_subset t i.succAbove))
    _ = evaluate D r s c (liftTo s t le_rfl) := congrFun (hB s ht) _
    _ = c t := rid s (c t)

include rid rcomp in

theorem primitives {q : ℕ} (hq : Fintype.card J ≤ q + 1)
    (c : Cochain D (q + 1)) (hc : differential D r c = 0) :
    ∃ b : Cochain D q, differential D r b = c := by
  classical
  have hlevels : ∀ k : ℕ, ∃ b : Cochain D q,
      ∀ t, (tupleSet t).card < k → differential D r b t = c t := by
    intro k
    induction k with
    | zero => exact ⟨0, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
    | succ k ih =>
      obtain ⟨b, hb⟩ := ih
      let a := c - differential D r b
      have ha : differential D r a = 0 := by
        rw [differential_sub, hc, differential_squared D r rid rcomp, sub_self]
      have hav : ∀ t, (tupleSet t).card < k → a t = 0 := by
        intro t ht
        change c t - differential D r b t = 0
        rw [hb t ht, sub_self]
      obtain ⟨e, helo, heeq⟩ := level_correction D r rid rcomp hq a ha hav
      refine ⟨b + e, ?_⟩
      intro t ht
      rw [differential_add, Pi.add_apply]
      by_cases hlt : (tupleSet t).card < k
      · rw [hb t hlt, helo t hlt, add_zero]
      · have heq : (tupleSet t).card = k := by omega
        rw [heeq t heq]
        change differential D r b t + (c t - differential D r b t) = c t
        abel
  obtain ⟨b, hb⟩ := hlevels (Fintype.card J + 1)
  refine ⟨b, funext (fun t => hb t ?_)⟩
  exact Nat.lt_succ_of_le (Finset.card_le_univ (tupleSet t))

end
end PiExponent.FiniteTupleCech

namespace PiExponent.GradedCechBound
noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {σR σM : Type*} [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
  {J : Type*} [Fintype J] [DecidableEq J]
  (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1) (d : ℤ)

theorem primitives {q : ℕ} (hq : Fintype.card J ≤ q + 1)
    (c : GradedCech.Cochain 𝒜 𝓜 x hx d (q + 1))
    (hc : GradedCech.differential 𝒜 𝓜 x hx d c = 0) :
    ∃ b : GradedCech.Cochain 𝒜 𝓜 x hx d q,
      GradedCech.differential 𝒜 𝓜 x hx d b = c := by
  exact FiniteTupleCech.primitives
    (fun s => GradedCech.IntersectionPiece 𝒜 𝓜 x hx s d)
    (fun {_ _} h => GradedCech.setRestriction 𝒜 𝓜 x hx h d)
    (fun s z => GradedCech.setRestriction_refl 𝒜 𝓜 x hx s d z)
    (fun {_ _ _} hst htu z => GradedCech.setRestriction_comp 𝒜 𝓜 x hx hst htu d z)
    hq c hc

end
end PiExponent.GradedCechBound

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedSerreVanishing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZero _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZeroClass _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesGroup _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedSerreVanishing
noncomputable section
open PiExponent.GradedCech PiExponent.GradedPolynomialLaurent PiExponent.GradedSerreStep
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {J R : Type u} [Fintype J] [DecidableEq J] [CommRing R] [IsNoetherianRing R]

theorem eventually_hasPrimitive_aux (depth : ℕ) :
    ∀ {M σM : Type u} [AddCommGroup M] [Module (MvPolynomial J R) M]
      [Module.Finite (MvPolynomial J R) M] [SetLike σM M] [AddSubgroupClass σM M]
      (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
      [SetLike.GradedSMul (grading (J := J) (R := R)) 𝓜]
      (q : ℕ), Fintype.card J ≤ q + 1 + depth →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasPrimitive (J := J) (R := R) 𝓜 n q := by
  induction depth with
  | zero =>
      intro M σM _ _ _ _ _ 𝓜 _ _ q hq
      refine ⟨0, ?_⟩
      intro n _ c hc
      exact GradedCechBound.primitives (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem
        n (by omega) c hc
  | succ depth ih =>
      intro M σM _ _ _ _ _ 𝓜 _ _ q hq
      obtain ⟨rank, w, g, hg, hsurj, N, hstep⟩ := exists_syzygy_eventual_step_q68 (J := J) (R := R) 𝓜
      let 𝓕 := ShiftedFreeGrading.piece (grading (J := J) (R := R)) w
      let hK := GradedSerre.kernel_homogeneous 𝓕 𝓜 g hg
      let 𝓚 := HomogeneousSubmoduleGrading.piece 𝓕 g.ker hK
      obtain ⟨N₁, h₁⟩ := ih 𝓚 (q + 1) (by omega)
      refine ⟨max N N₁, ?_⟩
      intro n hn
      exact (hstep n ((le_max_left _ _).trans hn)).2 q
        (h₁ n ((le_max_right _ _).trans hn))

variable {M σM : Type u} [AddCommGroup M] [Module (MvPolynomial J R) M]
  [Module.Finite (MvPolynomial J R) M] [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (grading (J := J) (R := R)) 𝓜]

theorem eventually_hasPrimitive (q : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasPrimitive (J := J) (R := R) 𝓜 n q :=
  eventually_hasPrimitive_aux (Fintype.card J) 𝓜 q (by omega)

theorem eventually_all_positive :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ, HasPrimitive (J := J) (R := R) 𝓜 n q := by
  classical
  have hq (q : Fin (Fintype.card J)) := eventually_hasPrimitive (J := J) (R := R) 𝓜 q.val
  choose N hN using hq
  refine ⟨∑ q, N q, ?_⟩
  intro n hn q c hc
  by_cases hbound : Fintype.card J ≤ q + 1
  · exact GradedCechBound.primitives (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem
      n hbound c hc
  · have hq' : q < Fintype.card J := by omega
    have hNq : N ⟨q, hq'⟩ ≤ ∑ q, N q :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (N i)) (Finset.mem_univ (⟨q, hq'⟩ : Fin (Fintype.card J)))
    exact hN ⟨q, hq'⟩ n (hNq.trans hn) c hc

theorem eventually_augmentation_recovery :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasRecovery (J := J) (R := R) 𝓜 n := by
  obtain ⟨rank, w, g, hg, hsurj, N, hstep⟩ := exists_syzygy_eventual_step_q68 (J := J) (R := R) 𝓜
  let 𝓕 := ShiftedFreeGrading.piece (grading (J := J) (R := R)) w
  let hK := GradedSerre.kernel_homogeneous 𝓕 𝓜 g hg
  let 𝓚 := HomogeneousSubmoduleGrading.piece 𝓕 g.ker hK
  obtain ⟨N₁, h₁⟩ := eventually_hasPrimitive (J := J) (R := R) 𝓚 0
  refine ⟨max N N₁, ?_⟩
  intro n hn
  exact (hstep n ((le_max_left _ _).trans hn)).1 (h₁ n ((le_max_right _ _).trans hn))

end
end PiExponent.GradedSerreVanishing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesCechInjectivity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ReesFrozenChart.coordinateInv_isIso _root_.OAI.PiExponent.ReesProductPowerSections.chartMorphism_open _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZero _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZeroClass _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesGroup _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesCechInjectivity
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [IsNoetherianRing R]

theorem exists_ideal_power_annihilating (I : Ideal R) (a : J → R)
    (ha : Ideal.span (Set.range a) = I) (x : R)
    (hx : ∀ j, ∃ k : ℕ, a j ^ k * x = 0) :
    ∃ k : ℕ, ∀ b ∈ I ^ k, b * x = 0 := by
  let A : Ideal R := (Ideal.span {x}).annihilator
  have hIA : I ≤ A.radical := by
    rw [← ha]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hx j
    apply Ideal.mem_radical_iff.mpr
    refine ⟨k, ?_⟩
    change a j ^ k ∈ (Submodule.span R {x}).annihilator
    simpa only [Submodule.mem_annihilator_span_singleton, smul_eq_mul] using hk
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIA (IsNoetherian.noetherian I)
  refine ⟨k, ?_⟩
  intro b hb
  have h := hk hb
  change b ∈ (Submodule.span R {x}).annihilator at h
  simpa only [Submodule.mem_annihilator_span_singleton, smul_eq_mul] using h

variable [Fintype J] [DecidableEq J] (I : Ideal R) (a : J → I)

theorem eventually_augmentation_injective
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Injective
      (augmentation (grading (J := J) (R := R)) (integerPiece I) MvPolynomial.X variable_mem n) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨N, hN⟩ := ReesPushdown.eventually_no_power_torsion I
  refine ⟨N, ?_⟩
  intro n hn z w hzw
  have hzero : augmentation (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem n (z - w) = 0 := by
    rw [map_sub, hzw, sub_self]
  let m : reesAlgebra I := (z - w).val
  let x : R := ((m : reesAlgebra I) : Polynomial R).coeff n
  have hm : m ∈ piece I n := (z - w).property
  have heval : evaluation I m = x := evaluation_piece I ⟨m, hm⟩
  have hx : x ∈ I ^ n := m.property n
  have hloc (j : J) : ∃ k : ℕ, (a j).val ^ k * x = 0 := by
    have ht := congrArg Subtype.val (congrFun hzero (fun _ : Fin 1 => j))
    change fraction (coverProduct MvPolynomial.X (tupleSet (fun _ : Fin 1 => j))) m 0 = 0 at ht
    have htuple : tupleSet (fun _ : Fin 1 => j) = {j} := by
      ext k
      simp [tupleSet, eq_comm]
    obtain ⟨k, hk⟩ := (fraction_eq_zero
      (coverProduct MvPolynomial.X (tupleSet (fun _ : Fin 1 => j))) m 0).mp ht
    have hprod : coverProduct (MvPolynomial.X : J → MvPolynomial J R)
        (tupleSet (fun _ : Fin 1 => j)) = MvPolynomial.X j := by
      rw [htuple, coverProduct, Finset.prod_singleton]
    rw [hprod] at hk
    refine ⟨k, ?_⟩
    have h := congrArg (evaluation I) hk
    change evaluation I (presentation I a (MvPolynomial.X j ^ k) * m) = evaluation I 0 at h
    simpa only [map_mul, map_pow, presentation_X, evaluation_generator, heval, map_zero] using h
  have hxzero : x = 0 := hN n hn x hx (exists_ideal_power_annihilating I
    (fun j => (a j).val) ha x hloc)
  apply Subtype.ext
  apply sub_eq_zero.mp
  change m = 0
  apply Subtype.ext
  rw [(mem_piece I n m).mp hm]
  change Polynomial.monomial n x = 0
  rw [hxzero, map_zero]

end
end PiExponent.ReesCechInjectivity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesCechRecovery
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ReesFrozenChart.coordinateInv_isIso _root_.OAI.PiExponent.ReesProductPowerSections.chartMorphism_open _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZero _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZeroClass _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesGroup _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesCechRecovery
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {R J : Type u} [CommRing R] [IsNoetherianRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem eventually_ordinary_power_recovery
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ q : ℕ, GradedSerreStep.HasPrimitive (J := J) (R := R) (integerPiece I) n q) ∧
      (∀ c : Cochain (grading (J := J) (R := R)) (integerPiece I)
          MvPolynomial.X variable_mem n 0,
        differential (grading (J := J) (R := R)) (integerPiece I)
          MvPolynomial.X variable_mem n c = 0 →
        ∃! z : ↥(I ^ n : Ideal R),
          augmentation (grading (J := J) (R := R)) (integerPiece I)
            MvPolynomial.X variable_mem n (ordinaryPowerEquivIntegerPiece I n z) = c) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  let : Module.Finite (MvPolynomial J R) (reesAlgebra I) := finite_presented_module I a ha
  obtain ⟨N₁, h₁⟩ := GradedSerreVanishing.eventually_all_positive (J := J) (R := R)
    (integerPiece I)
  obtain ⟨N₂, h₂⟩ := GradedSerreVanishing.eventually_augmentation_recovery (J := J) (R := R)
    (integerPiece I)
  obtain ⟨N₃, h₃⟩ := ReesCechInjectivity.eventually_augmentation_injective I a ha
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₃ : N₃ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  refine ⟨h₁ n hn₁, ?_⟩
  intro c hc
  obtain ⟨m, hm⟩ := h₂ n hn₂ c hc
  refine ⟨(ordinaryPowerEquivIntegerPiece I n).symm m, ?_, ?_⟩
  · simpa only [AddEquiv.apply_symm_apply] using hm
  · intro z hz
    apply (ordinaryPowerEquivIntegerPiece I n).injective
    rw [AddEquiv.apply_symm_apply]
    exact h₃ n hn₃ (hz.trans hm.symm)

end
end PiExponent.ReesCechRecovery

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesCohomologySetup
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.ReesFrozenChart.instIsOpenImmersionChart _root_.OAI.PiExponent.ReesProductPowerSections.chartMorphism_open _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesCohomologySetup
noncomputable section
open AlgebraicGeometry PiExponentSeshadri.ReesGrading
variable {R : Type} [CommRing R] (I : Ideal R)

theorem exceptionalPower_isQuasicoherent (n : ℕ) :
    ((exceptionalLineBundle I).pow n).sheaf.IsQuasicoherent :=
  GeometrySupport.LineBundleCoherent.modulePow_isQuasicoherent (exceptionalLineBundle I) n

end
end PiExponent.ReesCohomologySetup

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesSheafCechBase
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.ReesCohomologySetup.instIsNoetherianAffineBlowupOfIsNoetherianRing _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZero _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZeroClass _root_.OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesGroup _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSheafCechBase
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
attribute [local irreducible] PiExponent.ExceptionalRepresentedTypes.Frame
  PiExponent.ExceptionalRepresentedTypes.Sections PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped
  PiExponent.ReesFrozenPower.pieceEquiv PiExponent.ReesFrozenPower.powerEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

attribute [local irreducible] genericChartHomEquiv

theorem tuple_isAffine (q : ℕ) (t : Fin (q + 1) → J) :
    IsAffineOpen (CechHigher.intersection (opens I a) t) := by
  rw [← tupleOpen_eq I a q t]
  exact (ReesFrozenChart.chartOpen I a (tuple_nonempty q t)).property

end
end PiExponent.ReesSheafCechBase

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesSheafCechRecovery
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSheafCechRecovery
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase PiExponent.ReesSheafCechNaturality
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance 1001] AddCommGroup.toAddCommMonoid
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

variable [IsNoetherianRing R]

attribute [local instance] OAI.PiExponent.ReesSheafCechRecovery.cochainAddCommGroup
theorem eventually_recovery_and_primitives
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Bijective (ordinaryGlobalSection I a ha n) ∧
      ∀ q : ℕ, CechHigher.HasPrimitives (affineBlowup I).ringCatSheaf
        (opens I a) (exceptionalPower I n) q := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨N, hN⟩ := ReesCechRecovery.eventually_ordinary_power_recovery I a ha
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hpositive, hrecovery⟩ := hN n hn
  have hb : Function.Bijective (ordinaryAugmentation I a n) := by
    apply (Function.bijective_iff_existsUnique _).mpr
    intro c
    obtain ⟨b, hb, hu⟩ := hrecovery c.val c.property
    refine ⟨b, Subtype.ext hb, ?_⟩
    intro z hz
    exact hu z (congrArg Subtype.val hz)
  constructor
  · exact (freeOpenSectionsEquiv ⊤ (exceptionalPower I n)).bijective.comp
      ((globalCyclesEquiv I a ha n).symm.bijective.comp hb)
  · intro q
    exact AdditiveKernelTransport.transport_primitives
      (cochainEquiv I a n q) (cochainEquiv I a n (q+1)) (cochainEquiv I a n (q+2))
      (CechZeroAdditive.differentialHom (affineBlowup I).ringCatSheaf
        (opens I a) (exceptionalPower I n) q)
      (CechZeroAdditive.differentialHom (affineBlowup I).ringCatSheaf
        (opens I a) (exceptionalPower I n) (q+1))
      (GradedCech.differentialHom (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem n q)
      (GradedCech.differentialHom (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem n (q+1))
      (fun c => cochainEquiv_differential I a n q c)
      (fun c => cochainEquiv_differential I a n (q+1) c) (hpositive q)

theorem eventually_recovery_and_cohomology_q68_oai
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Bijective (ordinaryGlobalSection I a ha n) ∧
      ∀ (q : ℕ) (x : CategoryTheory.Abelian.Ext.{1} (C := (affineBlowup I).Modules)
        (schemeFreeOpen (affineBlowup I) ⊤) (exceptionalPower I n) (q+1)), x = 0 := by
  obtain ⟨N, hN⟩ := eventually_recovery_and_primitives I a ha
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hb, hp⟩ := hN n hn
  refine ⟨hb, ?_⟩
  intro q x
  let : (exceptionalPower I n).IsQuasicoherent :=
    ReesCohomologySetup.exceptionalPower_isQuasicoherent I n
  exact FreeCechSections.affine_ext_succ_eq_zero (affineBlowup I) (exceptionalPower I n)
    (opens I a) ⊤ (fun _ => le_top) (by rw [iSup_opens I a ha])
    (tuple_isAffine I a) q (hp q) x

end
end PiExponent.ReesSheafCechRecovery

end OAI
end

theorem solution : type_of% @OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_cohomology_q68_oai := @OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_cohomology_q68_oai
