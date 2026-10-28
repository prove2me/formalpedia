-- Prove2me | solution 1 for OAI.PiExponent.PersistentWeightComparison.ordinary_persistent_comparison_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:11:13.247126+00:00
-- url     : https://prove2.me/submissions/dc0ff965-872a-438c-b975-cfc84441c646

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A033
import Theorems.Thm_OAI_PiExponent_PrimeWeightedBezout_weighted_prime_length_bound_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_NormalBasisRigidity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.NormalBasisRigidity

open Set Submodule Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma IsNormalBasis.card_eq {v : ι → V} {A : Finset ι}
    (hA : IsNormalBasis (K := K) v A) : A.card = Module.finrank K V := by
  classical
  have hli : LinearIndependent K (fun i : A => v i) := hA.1
  let b : Basis A K V := Basis.mk hli (by
    have hr : Set.range (fun i : A => v i) = v '' (A : Set ι) := by
      ext x
      simp
    rw [hr, hA.2])
  exact (Module.finrank_eq_card_finset_basis b).symm

end PiExponent.NormalBasisRigidity

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_RectangularVolume
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent

theorem rectangularCutoff_pos {k : ℕ} (hk : 0 < k) (κ : Fin k → ℝ)
    (hκ : ∀ i, 0 < κ i) {T : ℝ} (hT : 0 < T) (i : Fin k) :
    0 < rectangularCutoff κ T i := by
  apply Nat.lt_ceil.mpr
  simpa only [Nat.cast_zero] using
    div_pos hT (mul_pos (by exact_mod_cast hk) (hκ i))

theorem rectangularCutoff_coordinate_weight_lt {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {T : ℝ}
    (β : Fin k → ℕ) (hβ : ∀ i, β i < rectangularCutoff κ T i) (i : Fin k) :
    κ i * (β i : ℝ) < T / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : (β i : ℝ) < T / ((k : ℝ) * κ i) := Nat.lt_ceil.mp (hβ i)
  have h := mul_lt_mul_of_pos_left hb (hκ i)
  have he : κ i * (T / ((k : ℝ) * κ i)) = T / (k : ℝ) := by
    field_simp [(hκ i).ne']
  simpa only [he] using h

theorem rectangularCutoff_weight_lt {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {T : ℝ}
    (β : Fin k → ℕ) (hβ : ∀ i, β i < rectangularCutoff κ T i) :
    (∑ i, κ i * (β i : ℝ)) < T := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : (∑ i, κ i * (β i : ℝ)) < ∑ _i : Fin k, T / (k : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (rectangularCutoff_coordinate_weight_lt hk κ hκ β hβ i).le
    · exact ⟨⟨0, hk⟩, Finset.mem_univ _,
        rectangularCutoff_coordinate_weight_lt hk κ hκ β hβ ⟨0, hk⟩⟩
  have he : (∑ _i : Fin k, T / (k : ℝ)) = T := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hkR.ne']
  simpa only [he] using hsum

theorem rectangularCutoff_product_lower {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {T : ℝ} (hT : 0 < T) :
    T ^ k / ((k : ℝ) ^ k * ∏ i, κ i) ≤
      ∏ i, (rectangularCutoff κ T i : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hp : (∏ i, T / ((k : ℝ) * κ i)) ≤
      ∏ i, (rectangularCutoff κ T i : ℝ) := by
    apply Finset.prod_le_prod
    · intro i hi
      exact (div_pos hT (mul_pos hkR (hκ i))).le
    · intro i hi
      exact Nat.le_ceil _
  simpa only [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using hp

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FilteredLength
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

section Modules

variable {R M P : Type*} [Ring R] [AddCommGroup M] [AddCommGroup P]
  [Module R M] [Module R P]

theorem surjective_of_finite_corrections (f : M →ₗ[R] P)
    (G : ℕ → Submodule R P) (d : ℕ) (hzero : G 0 = ⊤) (hend : G d = ⊥)
    (hstep : ∀ n < d, ∀ y ∈ G n, ∃ x : M, y - f x ∈ G (n + 1)) :
    Function.Surjective f := by
  intro y
  have hlift : ∀ n, n ≤ d → ∃ x : M, y - f x ∈ G n := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨0, by simp [hzero]⟩
    | succ n ih =>
      intro hn
      obtain ⟨x, hx⟩ := ih (Nat.le_trans (Nat.le_succ n) hn)
      obtain ⟨z, hz⟩ := hstep n (Nat.lt_of_succ_le hn) (y - f x) hx
      exact ⟨x + z, by simpa only [map_add, sub_add_eq_sub_sub] using hz⟩
  obtain ⟨x, hx⟩ := hlift d le_rfl
  rw [hend, Submodule.mem_bot] at hx
  exact ⟨x, (sub_eq_zero.mp hx).symm⟩

end Modules

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_GradedGeneration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

section RingHom

variable {A B : Type*} [CommRing A] [CommRing B]

theorem residue_corrections_of_surjective {K : Type*} [CommRing K]
    (f : A →+* B) (ρ : A →+* K) (π : B →+* K)
    (hρ : Function.Surjective ρ) (hcomm : π.comp f = ρ) :
    ∀ y : B, ∃ x : A, y - f x ∈ RingHom.ker π := by
  intro y
  obtain ⟨x, hx⟩ := hρ (π y)
  have hc : π (f x) = ρ x := congrArg (fun g : A →+* K => g x) hcomm
  refine ⟨x, ?_⟩
  rw [RingHom.mem_ker, map_sub, hc, hx, sub_self]

theorem ideal_power_corrections (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hf : I ≤ J.comap f)
    (hres : ∀ y : B, ∃ x : A, y - f x ∈ J)
    (hone : ∀ y ∈ J, ∃ x ∈ I, y - f x ∈ J ^ 2) :
    ∀ n : ℕ, ∀ y ∈ J ^ n, ∃ x ∈ I ^ n, y - f x ∈ J ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro y _
    obtain ⟨x, hx⟩ := hres y
    exact ⟨x, by simp, by simpa using hx⟩
  | succ n ih =>
    intro y hy
    rw [pow_succ'] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨x, hx, hex⟩ := hone a ha
      obtain ⟨z, hz, hez⟩ := ih b hb
      refine ⟨x * z, ?_, ?_⟩
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hx hz
      · have hleft : (a - f x) * b ∈ J ^ (n + 1 + 1) := by
          simpa only [← pow_add, Nat.add_comm 2 n, Nat.add_assoc] using
            (Ideal.mul_mem_mul hex hb)
        have hright : f x * (b - f z) ∈ J ^ (n + 1 + 1) := by
          rw [pow_succ']
          exact Ideal.mul_mem_mul (hf hx) hez
        have heq : a * b - f (x * z) = (a - f x) * b + f x * (b - f z) := by
          rw [map_mul]
          ring
        rw [heq]
        exact (J ^ (n + 1 + 1)).add_mem hleft hright
    · intro a b ha hb
      obtain ⟨x, hx, hex⟩ := ha
      obtain ⟨z, hz, hez⟩ := hb
      refine ⟨x + z, (I ^ (n + 1)).add_mem hx hz, ?_⟩
      have heq : a + b - f (x + z) = (a - f x) + (b - f z) := by
        rw [map_add]
        ring
      rw [heq]
      exact (J ^ (n + 1 + 1)).add_mem hex hez

end RingHom

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CotangentGeneration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

theorem corrections_of_mapCotangent_surjective (I : Ideal A) (J : Ideal B)
    (f : A →ₐ[R] B) (hf : I ≤ J.comap f)
    (hs : Function.Surjective (Ideal.mapCotangent I J f hf)) :
    ∀ y ∈ J, ∃ x ∈ I, y - f x ∈ J ^ 2 := by
  intro y hy
  obtain ⟨z, hz⟩ := hs (J.toCotangent ⟨y, hy⟩)
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective z
  rw [Ideal.mapCotangent_toCotangent] at hz
  have he : f x - y ∈ J ^ 2 := J.toCotangent_eq.mp hz
  exact ⟨x, x.property, by simpa only [neg_sub] using (J ^ 2).neg_mem he⟩

theorem algHom_surjective_of_residue_cotangent
    {K : Type*} [CommRing K] (I : Ideal A) (J : Ideal B)
    (f : A →ₐ[R] B) (hf : I ≤ J.comap f)
    (ρ : A →+* K) (π : B →+* K) (hρ : Function.Surjective ρ)
    (hcomm : π.comp f.toRingHom = ρ) (hJ : J = RingHom.ker π)
    (hs : Function.Surjective (Ideal.mapCotangent I J f hf))
    (d : ℕ) (hd : J ^ d = ⊥) : Function.Surjective f := by
  have hres : ∀ y : B, ∃ x : A, y - f x ∈ J := by
    rw [hJ]
    exact residue_corrections_of_surjective f.toRingHom ρ π hρ hcomm
  have hcor := ideal_power_corrections f.toRingHom I J hf hres
    (corrections_of_mapCotangent_surjective I J f hf hs)
  let : Algebra A B := f.toRingHom.toAlgebra
  apply surjective_of_finite_corrections (Algebra.linearMap A B)
    (fun n => (J ^ n).restrictScalars A) d
  · simp
  · simp [hd]
  · intro n _ y hy
    obtain ⟨x, _, hx⟩ := hcor n y hy
    exact ⟨x, hx⟩

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_JetGeometry
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.JetGeometry

noncomputable section

open MvPowerSeries

variable {σ R : Type*} [CommRing R]

theorem mem_weightedIdeal_iff (w : σ → ℕ) (N : ℕ)
    (f : MvPowerSeries σ R) :
    f ∈ weightedIdeal w N ↔ ∀ d, Finsupp.weight w d < N → coeff d f = 0 := by
  constructor
  · intro hf d hd
    have hd' : (Finsupp.weight w d : ℕ∞) < (N : ℕ∞) := by exact_mod_cast hd
    exact coeff_eq_zero_of_lt_weightedOrder w (hd'.trans_le hf)
  · intro hf
    exact nat_le_weightedOrder w hf

theorem weightedIdeal_mul_le (w : σ → ℕ) (M N : ℕ) :
    (weightedIdeal w M : Ideal (MvPowerSeries σ R)) * weightedIdeal w N ≤
      weightedIdeal w (M + N) := by
  apply Ideal.mul_le.mpr
  intro f hf g hg
  change ((M + N : ℕ) : ℕ∞) ≤ weightedOrder w (f * g)
  rw [Nat.cast_add]
  exact (add_le_add hf hg).trans (le_weightedOrder_mul w)

theorem ideal_pow_le_weightedIdeal (w : σ → ℕ) (I : Ideal (MvPowerSeries σ R))
    (R₀ : ℕ) (hI : I ≤ weightedIdeal w R₀) (n : ℕ) :
    I ^ n ≤ weightedIdeal w (n * R₀) := by
  induction n with
  | zero =>
      intro f hf
      change ((0 * R₀ : ℕ) : ℕ∞) ≤ weightedOrder w f
      simp
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      apply Ideal.mul_le.mpr
      intro f hf g hg
      exact (Ideal.mul_le.mp (weightedIdeal_mul_le w (n * R₀) R₀)) f (ih hf) g (hI hg)

end

end PiExponent.JetGeometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_TransverseMultiplicity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox.TransverseMultiplicity

noncomputable section

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

theorem card_rectIndex (n : σ → ℕ) : Fintype.card (RectIndex n) = ∏ i, n i := by
  rw [Fintype.card_congr (rectIndexEquiv n), Fintype.card_pi]
  simp only [Fintype.card_fin]

theorem finrank_rectangularQuotient (n : σ → ℕ) :
    Module.finrank K (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) = ∏ i, n i := by
  rw [(rectangularQuotientEquiv (K := K) n).finrank_eq,
    Module.finrank_fintype_fun_eq_card, card_rectIndex]

omit [Fintype σ] in
theorem rectangularQuotient_isLocal (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    IsLocalRing (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) := by
  let := (rectangularAugmentation (K := K) n hn).domain_nontrivial
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (rectangularIdeal (K := K) n))
    Ideal.Quotient.mk_surjective

theorem ordinaryIdeal_le_rectangularIdeal (n : σ → ℕ) :
    PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) (1 + ∑ i, n i) ≤
      rectangularIdeal (K := K) n := by
  intro f hf d hd
  apply (PiExponent.JetGeometry.mem_weightedIdeal_iff _ _ f).mp hf d
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum]
  have hsum : (∑ i, d i) ≤ ∑ i, n i :=
    Finset.sum_le_sum fun i _ => Nat.le_of_lt (hd i)
  omega

omit [Fintype σ] [DecidableEq σ] in
theorem ordinaryOneIdeal_eq_constantKernel :
    (PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) 1 :
      Ideal (MvPowerSeries σ K)) = RingHom.ker constantCoeff := by
  ext f
  change (1 : ℕ∞) ≤ f.order ↔ constantCoeff f = 0
  exact one_le_order_iff_constCoeff_eq_zero

omit [Fintype σ] in
theorem rectangularAugmentation_ker_eq_map (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    RingHom.ker (rectangularAugmentation (K := K) n hn) =
      Ideal.map (Ideal.Quotient.mk (rectangularIdeal (K := K) n))
        (PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) 1) := by
  rw [ordinaryOneIdeal_eq_constantKernel]
  let q := Ideal.Quotient.mk (rectangularIdeal (K := K) n)
  have hker : Ideal.comap q (RingHom.ker (rectangularAugmentation (K := K) n hn)) =
      RingHom.ker (constantCoeff : MvPowerSeries σ K →+* K) := by
    ext f
    rfl
  rw [← hker, Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective]

theorem rectangularAugmentation_ker_pow (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    (RingHom.ker (rectangularAugmentation (K := K) n hn)) ^ (1 + ∑ i, n i) = ⊥ := by
  rw [rectangularAugmentation_ker_eq_map, ← Ideal.map_pow]
  apply le_antisymm _ bot_le
  calc
    _ ≤ Ideal.map (Ideal.Quotient.mk (rectangularIdeal (K := K) n))
          (PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) (1 + ∑ i, n i)) := by
      apply Ideal.map_mono
      simpa only [Nat.mul_one] using
        PiExponent.JetGeometry.ideal_pow_le_weightedIdeal (R := K) (fun _ : σ => 1)
          (PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) 1) 1 le_rfl (1 + ∑ i, n i)
    _ ≤ Ideal.map (Ideal.Quotient.mk (rectangularIdeal (K := K) n))
          (rectangularIdeal (K := K) n) :=
      Ideal.map_mono (ordinaryIdeal_le_rectangularIdeal n)
    _ = ⊥ := Ideal.map_quotient_self _

theorem length_rectangularQuotient (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    Module.length (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n)
      (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) = (∏ i, n i : ℕ) := by
  let := (rectangularAugmentation (K := K) n hn).domain_nontrivial
  let := rectangularQuotient_isLocal (K := K) n hn
  rw [PiExponentJets.W24.ring_length_eq_finrank_of_augmentation
    (rectangularAugmentation (K := K) n hn)
    (rectangularAugmentation_algebraMap n hn), finrank_rectangularQuotient]

theorem rectangular_quotient_length_le_of_residue_cotangent
    {A C : Type*} [CommRing A] [CommRing C] [Algebra C A]
    (n : σ → ℕ) (hn : ∀ i, 0 < n i)
    [Algebra C (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n)]
    (P I : Ideal A)
    (f : A →ₐ[C] (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n))
    (rho : A →+* K) (hrho : Function.Surjective rho)
    (hcomm : (rectangularAugmentation (K := K) n hn).comp f.toRingHom = rho)
    (hf : P ≤ (RingHom.ker (rectangularAugmentation (K := K) n hn)).comap f)
    (hCot : Function.Surjective
      (Ideal.mapCotangent P (RingHom.ker (rectangularAugmentation (K := K) n hn)) f hf))
    (hI : I ≤ RingHom.ker f.toRingHom) :
    (∏ i, n i : ℕ) ≤ Module.length A (A ⧸ I) := by
  let B := MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n
  have hs := PiExponentJets.W24.algHom_surjective_of_residue_cotangent
    P (RingHom.ker (rectangularAugmentation (K := K) n hn)) f hf
    rho (rectangularAugmentation (K := K) n hn) hrho hcomm rfl hCot
    (1 + ∑ i, n i) (rectangularAugmentation_ker_pow n hn)
  let g : (A ⧸ I) →+* B := Ideal.Quotient.lift I f.toRingHom hI
  have hg : Function.Surjective g :=
    Ideal.Quotient.lift_surjective_of_surjective I hI hs
  let : Algebra (A ⧸ I) B := g.toAlgebra
  have hg' : Function.Surjective (algebraMap (A ⧸ I) B) := hg
  have hlength : Module.length B B ≤ Module.length (A ⧸ I) (A ⧸ I) := by
    rw [← Module.length_eq_of_surjective (M := B) hg']
    exact Module.length_le_of_surjective (Algebra.linearMap (A ⧸ I) B) hg'
  rw [Module.length_eq_of_surjective (R := A ⧸ I) (M := A ⧸ I)
    (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap A (A ⧸ I)))]
  rw [length_rectangularQuotient n hn] at hlength
  exact hlength

omit [Fintype σ] in
theorem rectangularTaylorAlgHom_augmentation {A : Type*}
    [CommRing A] [Algebra ℚ A] [Algebra ℚ K]
    (n : σ → ℕ) (hn : ∀ i, 0 < n i) (tau : A →+* MvPowerSeries σ K)
    (rho : A →+* K) (hconstant : ∀ a, constantCoeff (tau a) = rho a) :
    (rectangularAugmentation (K := K) n hn).comp
      (rectangularTaylorAlgHom n tau).toRingHom = rho := by
  ext a
  exact hconstant a

theorem rectangularTaylor_length_lower {A : Type*}
    [CommRing A] [Algebra ℚ A] [Algebra ℚ K]
    (n : σ → ℕ) (hn : ∀ i, 0 < n i) (tau : A →+* MvPowerSeries σ K)
    (rho : A →+* K) (hrho : Function.Surjective rho)
    (hconstant : ∀ a, constantCoeff (tau a) = rho a)
    (P I : Ideal A) (hP : P ≤ RingHom.ker rho)
    (hCot : Function.Surjective
      (Ideal.mapCotangent P (RingHom.ker (rectangularAugmentation (K := K) n hn))
        (rectangularTaylorAlgHom n tau)
        (rectangularTaylorAlgHom_maps_residueIdeal n hn tau rho hconstant P hP)))
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0) :
    (∏ i, n i : ℕ) ≤ Module.length A (A ⧸ I) := by
  apply rectangular_quotient_length_le_of_residue_cotangent n hn P I
    (rectangularTaylorAlgHom n tau) rho hrho
    (rectangularTaylorAlgHom_augmentation n hn tau rho hconstant)
    (rectangularTaylorAlgHom_maps_residueIdeal n hn tau rho hconstant P hP) hCot
  intro a ha
  change Ideal.Quotient.mk (rectangularIdeal (K := K) n) (tau a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hvanish a ha)

omit [Fintype σ] [DecidableEq σ] in
theorem linearCoefficient_mul (i : σ) (f g : MvPowerSeries σ K) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g +
      constantCoeff g * coeff (Finsupp.single i 1) f := by
  have h (p : MvPowerSeries σ K) :
      constantCoeff (MvPowerSeries.pderiv _ i p) = coeff (Finsupp.single i 1) p := by
    rw [← coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
    simp
  rw [← h, (MvPowerSeries.pderiv _ i).leibniz]
  simp only [smul_eq_mul, map_add, map_mul, h]

omit [Fintype σ] [DecidableEq σ] in
theorem localizedTaylorMap_linearCoefficient {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a))
    (i : σ) (d : L → K)
    (hd : ∀ x y, d (x * y) = rho x * d y + rho y * d x)
    (ha : ∀ a, coeff (Finsupp.single i 1) (tau a) = d (algebraMap A L a))
    (x : L) :
    coeff (Finsupp.single i 1) (localizedTaylorMap M tau rho hconstant x) = d x := by
  obtain ⟨a, s, hs⟩ := IsLocalization.exists_mk'_eq M x
  have heq : x * algebraMap A L s = algebraMap A L a :=
    (IsLocalization.mk'_eq_iff_eq_mul.mp hs).symm
  have hc0 (y : L) :
      constantCoeff (localizedTaylorMap M tau rho hconstant y) = rho y :=
    RingHom.congr_fun (localizedTaylorMap_constant M tau rho hconstant) y
  have hc := congrArg
    (fun y => coeff (Finsupp.single i 1) (localizedTaylorMap M tau rho hconstant y)) heq
  rw [map_mul, linearCoefficient_mul, hc0, hc0,
    localizedTaylorMap_algebraMap, localizedTaylorMap_algebraMap, ha, ha] at hc
  have hd' := hd x (algebraMap A L s)
  rw [heq] at hd'
  have he : rho (algebraMap A L s) *
      coeff (Finsupp.single i 1) (localizedTaylorMap M tau rho hconstant x) =
        rho (algebraMap A L s) * d x := by
    exact add_left_cancel (hc.trans hd')
  exact mul_left_cancel₀ ((IsLocalization.map_units L s).map rho).ne_zero he

omit [Fintype σ] in
theorem localizedTaylorMap_ideal_le {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a))
    (n : σ → ℕ) (I : Ideal A)
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0) :
    I.map (algebraMap A L) ≤
      (rectangularIdeal (K := K) n).comap (localizedTaylorMap M tau rho hconstant) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change localizedTaylorMap M tau rho hconstant (algebraMap A L a) ∈ rectangularIdeal n
  rw [localizedTaylorMap_algebraMap]
  exact hvanish a ha

end
end PiExponentApprox.TransverseMultiplicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_TransverseWeightedMultiplicity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.TransverseWeightedMultiplicity

open scoped BigOperators

theorem rectangularCutoff_budget {k : ℕ} (hk : 0 < k)
    (kappa : Fin k → ℝ) (hkappa : ∀ i, 0 < kappa i)
    (T : ℝ) (hT : 0 < T) :
    ∑ i, ((rectangularCutoff kappa T i - 1 : ℕ) : ℝ) * kappa i ≤ T := by
  have hpos := rectangularCutoff_pos hk kappa hkappa hT
  have hlt : ∀ i, rectangularCutoff kappa T i - 1 < rectangularCutoff kappa T i := by
    intro i
    exact Nat.sub_lt (hpos i) (by norm_num)
  have h := rectangularCutoff_weight_lt hk kappa hkappa
    (fun i => rectangularCutoff kappa T i - 1) hlt
  simpa only [mul_comm] using h.le

theorem rectangular_weight_product_comparison {k : ℕ} (hk : 0 < k)
    (rho kappa : Fin k → ℝ) (epsilon N L : ℝ)
    (hrho : ∀ i, 0 < rho i) (hkappa : ∀ i, 0 < kappa i)
    (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hlower : (epsilon * N) ^ k / ((k : ℝ) ^ k * ∏ i, kappa i) ≤ L)
    (hupper : L ≤ N ^ k / ∏ i, rho i) :
    (∏ i, rho i) ≤ (k : ℝ) ^ k * (∏ i, kappa i) / epsilon ^ k := by
  have hA : 0 < ∏ i, rho i := Finset.prod_pos (fun i _ => hrho i)
  have hB : 0 < (k : ℝ) ^ k * ∏ i, kappa i :=
    mul_pos (pow_pos (by exact_mod_cast hk) _) (Finset.prod_pos (fun i _ => hkappa i))
  have h := (div_le_div_iff₀ hB hA).mp (hlower.trans hupper)
  rw [mul_pow] at h
  apply (le_div_iff₀ (pow_pos hepsilon k)).mpr
  apply (mul_le_mul_iff_right₀ (pow_pos hN k)).mp
  calc
    N ^ k * ((∏ i, rho i) * epsilon ^ k) =
        epsilon ^ k * N ^ k * ∏ i, rho i := by ring
    _ ≤ N ^ k * ((k : ℝ) ^ k * ∏ i, kappa i) := h

theorem weight_comparison_of_rectangular_count {k : ℕ} (hk : 0 < k)
    (rho kappa : Fin k → ℝ) (epsilon N : ℝ) (L : ℕ)
    (hrho : ∀ i, 0 < rho i) (hkappa : ∀ i, 0 < kappa i)
    (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hlower : (∏ i, rectangularCutoff kappa (epsilon * N) i : ℕ) ≤ L)
    (hupper : (L : ℝ) ≤ N ^ k / ∏ i, rho i) :
    (∏ i, rho i) ≤ (k : ℝ) ^ k * (∏ i, kappa i) / epsilon ^ k := by
  apply rectangular_weight_product_comparison hk rho kappa epsilon N L
    hrho hkappa hepsilon hN _ hupper
  have hv := rectangularCutoff_product_lower hk kappa hkappa (mul_pos hepsilon hN)
  apply hv.trans
  exact_mod_cast hlower

end PiExponent.TransverseWeightedMultiplicity
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_NormalBasisProducts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.NormalBasisProducts

open scoped BigOperators
open NormalBasisRigidity TransverseWeightedMultiplicity

variable {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem enumeration_linearIndependent {v : ι → V} (A B : Finset ι)
    (hcard : A.card = B.card) (hB : IsNormalBasis (K := K) v B) :
    LinearIndependent K (fun i => v (enumeration A B hcard i)) := by
  have hli : LinearIndependent K (fun i : B => v i) := hB.1
  exact hli.comp (fun i => B.equivFin.symm (Fin.cast hcard i))
    (B.equivFin.symm.injective.comp (Fin.cast_injective hcard))

theorem prod_equivFin {M : Type*} [CommMonoid M] (A : Finset ι) (f : ι → M) :
    (∏ i : Fin A.card, f (A.equivFin.symm i)) = ∏ i ∈ A, f i := by
  calc
    _ = ∏ i : A, f i := Fintype.prod_equiv A.equivFin.symm _ _ (fun _ => rfl)
    _ = _ := Finset.prod_coe_sort A f

theorem prod_enumeration {M : Type*} [CommMonoid M]
    (A B : Finset ι) (hcard : A.card = B.card) (f : ι → M) :
    (∏ i : Fin A.card, f (enumeration A B hcard i)) = ∏ i ∈ B, f i := by
  calc
    _ = ∏ i : Fin B.card, f (B.equivFin.symm i) :=
      Fintype.prod_equiv (finCongr hcard) _ _ (fun _ => rfl)
    _ = _ := prod_equivFin B f

theorem rectangular_factor_le_constant (m k : ℕ) (sigma : ℝ)
    (hsigma : 0 < sigma) (hkm : k ≤ m + 2) :
    (k : ℝ) ^ k * (((m : ℝ) + 2) / sigma) ^ k ≤
      2 * ((m : ℝ) + 2) ^ (m + 2) *
        (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2) := by
  have hbase : 0 ≤ ((m : ℝ) + 2) / sigma := by positivity
  have hdim : (k : ℝ) ≤ (m : ℝ) + 2 := by exact_mod_cast hkm
  have hp : (k : ℝ) ^ k ≤ ((m : ℝ) + 2) ^ (m + 2) := by
    calc
      _ ≤ ((m : ℝ) + 2) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg k) hdim k
      _ ≤ _ := pow_le_pow_right₀ (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith) hkm
  have hfactor : (k : ℝ) ^ k ≤ 2 * ((m : ℝ) + 2) ^ (m + 2) := hp.trans (by
    have h : 0 ≤ ((m : ℝ) + 2) ^ (m + 2) := by positivity
    linarith)
  have hpow : (((m : ℝ) + 2) / sigma) ^ k ≤
      (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2) := by
    calc
      _ ≤ (1 + ((m : ℝ) + 2) / sigma) ^ k :=
        pow_le_pow_left₀ hbase (le_add_of_nonneg_left zero_le_one) k
      _ ≤ _ := pow_le_pow_right₀ (le_add_of_nonneg_right hbase) hkm
  exact mul_le_mul hfactor hpow (pow_nonneg hbase _) (by positivity)

theorem rectangular_comparison_le_constant {m k : ℕ}
    (hkm : k ≤ m + 2) (kappa : Fin k → ℝ) (sigma : ℝ)
    (hsigma : 0 < sigma) (hkappa : ∀ i, 0 ≤ kappa i) :
    (k : ℝ) ^ k * (∏ i, kappa i) / (sigma / ((m : ℝ) + 2)) ^ k ≤
      (2 * ((m : ℝ) + 2) ^ (m + 2) *
        (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2)) * ∏ i, kappa i := by
  have h := rectangular_factor_le_constant m k sigma hsigma hkm
  have hp : 0 ≤ ∏ i, kappa i := Finset.prod_nonneg (fun i _ => hkappa i)
  have hh := mul_le_mul_of_nonneg_right h hp
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow, inv_inv]
  ring

end PiExponent.NormalBasisProducts
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedSliceDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedSliceDegree

open scoped BigOperators Pointwise

variable {C E ι σ : Type*} [Field C] [Field E] [Algebra C E]

theorem SupportBound.mono {ρ : σ → ℝ} {M N : ℝ} {p : MvPolynomial σ E}
    (hp : SupportBound ρ M p) (hMN : M ≤ N) : SupportBound ρ N p :=
  fun d hd => (hp d hd).trans hMN

end PiExponent.WeightedSliceDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_OrdinaryDerivativeIdeals
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryDerivatives

open scoped BigOperators
open DerivativeIdeals

theorem supportBound_pderiv {n : ℕ} (W : Fin n → ℝ) (N : ℝ)
    (p : Polynomial n) (hp : WeightedSliceDegree.SupportBound W N p) (i : Fin n) :
    WeightedSliceDegree.SupportBound W (N - W i) (MvPolynomial.pderiv i p) := by
  intro d hd
  have hshift : d + Finsupp.single i 1 ∈ p.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    have hh := MvPolynomial.mem_support_iff.mp hd
    apply hh
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  apply (le_sub_iff_add_le).mpr
  have h := hp _ hshift
  simpa only [map_add, Finsupp.weight_single, one_smul] using h

theorem supportBound_word {n : ℕ} (W : Fin n → ℝ) (N : ℝ)
    (p : Polynomial n) (hp : WeightedSliceDegree.SupportBound W N p)
    (hW : ∀ i, 0 ≤ W i) (l : List (Fin n)) :
    WeightedSliceDegree.SupportBound W N (word n l p) := by
  induction l with
  | nil => exact hp
  | cons i l ih =>
    exact (supportBound_pderiv W N (word n l p) ih i).mono (sub_le_self N (hW i))

theorem span_equations {n : ℕ} (cost : Fin n → ℝ) (bound : ℝ) (p : Polynomial n) :
    Ideal.span (Set.range (equations cost bound p)) = ideal n cost bound p := by
  unfold ideal derivativeIdeal
  congr 1
  ext g
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.1, l.2, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩

theorem equation_supportBound {n : ℕ} (cost W : Fin n → ℝ) (bound N : ℝ)
    (p : Polynomial n) (hp : WeightedSliceDegree.SupportBound W N p)
    (hW : ∀ i, 0 ≤ W i) (l : BoundedWords cost bound) :
    WeightedSliceDegree.SupportBound W N (equations cost bound p l) :=
  supportBound_word W N p hp hW l.1

end PiExponent.OrdinaryDerivatives
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CommutingTaylor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CommutingTaylor

open Finset Nat
variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem coeff_residueTaylorFin {K : Type*} [CommRing K] [Algebra ℚ K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K)
    (α : Fin m →₀ ℕ) (a : R) :
    MvPowerSeries.coeff α (residueTaylorFin m D ρ a) =
      (∏ i, (1 / ((α i).factorial : ℚ))) • ρ (mixedIter m D α a) := by
  simp [residueTaylorFin, coeff_taylorHomFin, map_rat_smul]

end PiExponent.CommutingTaylor

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_TaylorRectangular
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.TaylorRectangular

open scoped BigOperators
open CommutingTaylor
open PiExponentApprox

section General
variable {R K : Type*} [CommRing R] [Algebra ℚ R] [Field K] [Algebra ℚ K]

theorem residueTaylor_mem_rectangular (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (ρ : R →+* K) (n : Fin m → ℕ) (a : R)
    (ha : ∀ α : Fin m →₀ ℕ, (∀ i, α i < n i) → ρ (mixedIter m D α a) = 0) :
    residueTaylorFin m D ρ a ∈ TransverseMultiplicity.rectangularIdeal n := by
  intro α hα
  rw [coeff_residueTaylorFin, ha α hα]
  rw [Algebra.smul_def]
  exact mul_zero _

end General

end PiExponent.TaylorRectangular

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_OrdinaryTaylor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryTaylor

open scoped BigOperators
open CommutingTaylor TaylorRectangular DerivativeIdeals
open PiExponentApprox

section General
variable {R K ι : Type*} [CommRing R] [Algebra ℚ R] [Field K] [Algebra ℚ K]

theorem wordDerivative_append (D : ι → Derivation ℚ R R)
    (u v : List ι) (a : R) :
    wordDerivative D (u ++ v) a = wordDerivative D u (wordDerivative D v a) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append, wordDerivative_cons, ih]

theorem wordDerivative_replicate (D : ι → Derivation ℚ R R)
    (i : ι) (n : ℕ) (a : R) :
    wordDerivative D (List.replicate n i) a = iter (D i) n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, wordDerivative_cons, ih, iter_succ]

theorem mixedIter_eq_wordDerivative (D : ι → Derivation ℚ R R)
    (k : ℕ) (B : Fin k → ι) (α : Fin k →₀ ℕ) (a : R) :
    mixedIter k (fun i => D (B i)) α a = wordDerivative D (derivativeWord k B α) a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [mixedIter, LinearMap.comp_apply, derivativeWord,
      wordDerivative_append, wordDerivative_replicate]
    exact ih (fun i => B i.succ) α.tail _

theorem derivativeWord_wordCost (k : ℕ) (B : Fin k → ι)
    (α : Fin k →₀ ℕ) (cost : ι → ℝ) :
    wordCost cost (derivativeWord k B α) = ∑ i, (α i : ℝ) * cost (B i) := by
  induction k with
  | zero => simp [derivativeWord, wordCost]
  | succ k ih =>
    simp only [derivativeWord, wordCost, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate]
    change wordCost cost (derivativeWord k (fun i => B i.succ) α.tail) +
      (α 0) • cost (B 0) = _
    rw [ih, Fin.sum_univ_succ]
    simp only [Finsupp.tail_apply, nsmul_eq_mul]
    ring

theorem derivativeWord_wordCost_le (k : ℕ) (B : Fin k → ι)
    (α : Fin k →₀ ℕ) (cost : ι → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hα : ∀ i, α i < n i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ) :
    wordCost cost (derivativeWord k B α) ≤ δ := by
  rw [derivativeWord_wordCost]
  apply le_trans _ hn
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right _ (hcost _)
  exact_mod_cast (by have := hα i; omega : α i ≤ n i - 1)

theorem residueTaylor_ideal_le (D : ι → Derivation ℚ R R)
    (k : ℕ) (B : Fin k → ι) (ρ : R →+* K) (I : Ideal R)
    (cost : ι → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hvanish : ∀ a ∈ I, ∀ word : List ι, wordCost cost word ≤ δ →
      ρ (wordDerivative D word a) = 0) :
    I ≤ (TransverseMultiplicity.rectangularIdeal n).comap
      (residueTaylorFin k (fun i => D (B i)) ρ) := by
  intro a ha
  apply residueTaylor_mem_rectangular
  intro α hα
  rw [mixedIter_eq_wordDerivative]
  exact hvanish a ha _ (derivativeWord_wordCost_le k B α cost n δ hcost hα hn)

end General

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem ordinaryTaylor_ideal_le (m k : ℕ) (B : Fin k → Fin m)
    (ρ : OrdinaryDerivatives.Polynomial m →+* K) (I : Ideal (OrdinaryDerivatives.Polynomial m))
    (cost : Fin m → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hvanish : ∀ a ∈ I, ∀ word : List (Fin m), wordCost cost word ≤ δ →
      ρ (OrdinaryDerivatives.word m word a) = 0) :
    I ≤ (TransverseMultiplicity.rectangularIdeal n).comap (ordinaryTaylor m k B ρ) :=
  residueTaylor_ideal_le (OrdinaryDerivatives.partialFrame m) k B ρ I cost n δ hcost hn hvanish

theorem ordinary_residueTaylor_ideal_le (m k : ℕ) (B : Fin k → Fin m)
    (ρ : OrdinaryDerivatives.Polynomial m →+* K) (I : Ideal (OrdinaryDerivatives.Polynomial m))
    (cost : Fin m → ℝ) (box : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i)
    (hbudget : ∑ i, ((box i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hvanish : ∀ a ∈ I, ∀ word : List (Fin m), wordCost cost word ≤ δ →
      ρ (OrdinaryDerivatives.word m word a) = 0) :
    I ≤ (TransverseMultiplicity.rectangularIdeal box).comap
      (residueTaylorFin k (fun i => OrdinaryDerivatives.partialFrame m (B i)) ρ) :=
  ordinaryTaylor_ideal_le m k B ρ I cost box δ hcost hbudget hvanish

end PiExponent.OrdinaryTaylor
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_RectangularCotangent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentApprox.TransverseMultiplicity

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

theorem rectangular_reconstruct (n : σ → ℕ) (f : RectangularRing (K := K) n) :
    f = ∑ d : RectIndex n,
      Ideal.Quotient.mk (rectangularIdeal (K := K) n)
        (monomial d.val (rectangularQuotientCoefficients (K := K) n f d)) := by
  apply (rectangularQuotientCoefficients_bijective (K := K) n).1
  rw [map_sum]
  funext e
  simp only [Finset.sum_apply, rectangularQuotientCoefficients_mk]
  change rectangularQuotientCoefficients (K := K) n f e =
    ∑ d : RectIndex n, coeff e.val
      (monomial d.val (rectangularQuotientCoefficients (K := K) n f d))
  symm
  rw [Finset.sum_eq_single e]
  · simp only [coeff_monomial_same]
  · intro d _ hde
    have hne : e.val ≠ d.val := by
      intro he
      exact hde (Subtype.ext he.symm)
    simp only [coeff_monomial, ite_eq_right hne]
  · intro h
    exact (h (Finset.mem_univ e)).elim

theorem rectangular_monomial_mem_square (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (d : σ →₀ ℕ) (a : K) (hd : d ≠ 0)
    (hunit : ∀ i, d ≠ Finsupp.single i 1) :
    Ideal.Quotient.mk (rectangularIdeal (K := K) n) (monomial d a) ∈
      (rectangularAugmentationIdeal (K := K) n hn) ^ 2 := by
  have hex : ∃ i, d i ≠ 0 := by
    by_contra! hh
    exact hd (by ext i; exact hh i)
  obtain ⟨i, hi⟩ := hex
  let e : σ →₀ ℕ := d - Finsupp.single i 1
  have he : e + Finsupp.single i 1 = d := Finsupp.sub_add_single_one_cancel hi
  have he0 : e ≠ 0 := by
    intro h
    apply hunit i
    simpa [h] using he.symm
  have hleft : Ideal.Quotient.mk (rectangularIdeal (K := K) n) (monomial (Finsupp.single i 1) (1 : K)) ∈
      rectangularAugmentationIdeal (K := K) n hn := by
    change constantCoeff (monomial (Finsupp.single i 1) (1 : K)) = 0
    have hsingle : (0 : σ →₀ ℕ) ≠ Finsupp.single i 1 := by
      intro h
      have hh := congrArg (fun d : σ →₀ ℕ => d i) h
      simp at hh
    simp [← coeff_zero_eq_constantCoeff, coeff_monomial, hsingle]
  have hright : Ideal.Quotient.mk (rectangularIdeal (K := K) n) (monomial e a) ∈
      rectangularAugmentationIdeal (K := K) n hn := by
    change constantCoeff (monomial e a) = 0
    simp [← coeff_zero_eq_constantCoeff, coeff_monomial, Ne.symm he0]
  rw [pow_two]
  have hh := Ideal.mul_mem_mul hleft hright
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [← map_mul, monomial_mul_monomial, one_mul, add_comm, he]

theorem rectangular_mem_square_of_first_zero (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (f : RectangularRing (K := K) n)
    (hf : f ∈ rectangularAugmentationIdeal (K := K) n hn)
    (hfirst : rectangularFirstCoefficients (K := K) n hn f = 0) :
    f ∈ (rectangularAugmentationIdeal (K := K) n hn) ^ 2 := by
  rw [rectangular_reconstruct n f]
  apply Ideal.sum_mem
  intro d hd
  by_cases hd0 : d.val = 0
  · have hc : rectangularQuotientCoefficients (K := K) n f d = 0 := by
      obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
      change coeff d.val F = 0
      rw [hd0]
      exact hf
    simp [hc]
  · by_cases hu : ∃ i, d.val = Finsupp.single i 1
    · obtain ⟨i, hi⟩ := hu
      have hc : rectangularQuotientCoefficients (K := K) n f d = 0 := by
        have hh := congrFun hfirst i
        change rectangularQuotientCoefficients (K := K) n f (unitRectIndex n hn i) = 0 at hh
        have he : d = unitRectIndex n hn i := Subtype.ext hi
        simpa only [he] using hh
      simp [hc]
    · exact rectangular_monomial_mem_square n hn d.val _ hd0 (by simpa using hu)

theorem rectangularCotangentFirstCoefficients_injective
    (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    Function.Injective (rectangularCotangentFirstCoefficients (K := K) n hn) := by
  have hz : ∀ z, rectangularCotangentFirstCoefficients (K := K) n hn z = 0 → z = 0 := by
    intro z hz
    obtain ⟨f, rfl⟩ := (rectangularAugmentationIdeal (K := K) n hn).toCotangent_surjective z
    apply ((rectangularAugmentationIdeal (K := K) n hn).toCotangent_eq_zero f).mpr
    exact rectangular_mem_square_of_first_zero n hn f.val f.property hz
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

end PiExponentApprox.TransverseMultiplicity

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_PrimeNormalCotangent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open KaehlerDifferential
open scoped TensorProduct

variable {C ι : Type*} [Field C] [Fintype ι]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

theorem primeNormalPairing_ker_le_tangent :
    LinearMap.ker (primeNormalPairing Q) ≤ polynomialTangent (primeResidueMap Q) Q := by
  intro v hv
  change primeNormalPairing Q v = 0 at hv
  change polynomialJacobian (primeResidueMap Q) Q v = 0
  ext p
  have h := LinearMap.congr_fun hv (primePolynomialCotangent Q p)
  simpa only [primeNormalPairing_polynomial, LinearMap.zero_apply,
    polynomialJacobian, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, mul_comm] using h

theorem primeNormalPairing_linearIndependent {σ : Type*} [Fintype σ]
    (v : σ → ι → Q.ResidueField)
    (hv : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ (v j))) :
    LinearIndependent Q.ResidueField (fun j => primeNormalPairing Q (v j)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have hp : primeNormalPairing Q (∑ j, a j • v j) = 0 := by
    simpa only [map_sum, map_smul] using ha
  have hm := primeNormalPairing_ker_le_tangent Q hp
  have hq : (polynomialTangent (primeResidueMap Q) Q).mkQ (∑ j, a j • v j) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hm
  have hsum : ∑ j, a j • (polynomialTangent (primeResidueMap Q) Q).mkQ (v j) = 0 := by
    simpa only [map_sum, map_smul] using hq
  exact Fintype.linearIndependent_iff.mp hv a hsum j

theorem prime_cotangent_evaluation_surjective {σ : Type*} [Fintype σ]
    (v : σ → ι → Q.ResidueField)
    (hv : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ (v j))) :
    Function.Surjective
      (fun x : PrimeLocalCotangent Q => fun j => primeNormalPairing Q (v j) x) := by
  classical
  let f := fun j => primeNormalPairing Q (v j)
  have hf : LinearIndependent Q.ResidueField f := primeNormalPairing_linearIndependent Q v hv
  intro a
  obtain ⟨g, hg⟩ := LinearMap.dualMap_surjective_of_injective
    hf.finsuppLinearCombination_injective (Finsupp.linearCombination Q.ResidueField a)
  refine ⟨(Module.evalEquiv Q.ResidueField (PrimeLocalCotangent Q)).symm g, ?_⟩
  funext j
  change f j ((Module.evalEquiv Q.ResidueField (PrimeLocalCotangent Q)).symm g) = a j
  rw [Module.apply_evalEquiv_symm_apply]
  have hj := LinearMap.congr_fun hg (Finsupp.single j (1 : Q.ResidueField))
  simpa only [LinearMap.dualMap_apply, Finsupp.linearCombination_single, one_smul] using hj

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeNormalKernel
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

variable {C ι : Type*} [Field C] [Fintype ι]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

theorem primeLocalDirectional_polynomial (v : ι → Q.ResidueField) (p : MvPolynomial ι C) :
    primeLocalDirectional Q v
      (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) =
      ∑ i, v i * primeResidueMap Q (MvPolynomial.pderiv i p) := by
  calc
    _ = ∑ i, v i * primeLocalPartial Q i
        (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) := by
      change (Derivation.coeFnAddMonoidHom (∑ i, v i • primeLocalPartial Q i)) _ = _
      rw [map_sum, Finset.sum_apply]
      rfl
    _ = _ := by simp only [primeLocalPartial_polynomial]; rfl

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_PrimeTaylorCotangent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open PiExponentApprox.TransverseMultiplicity MvPowerSeries

variable {C ι σ : Type*} [Field C] [CharZero C] [Fintype ι]
variable [Fintype σ] [DecidableEq σ]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

theorem prime_rectangular_mapCotangent_surjective
    (tau : Localization.AtPrime Q →+* MvPowerSeries σ Q.ResidueField)
    (hzero : ∀ x, constantCoeff (tau x) = algebraMap (Localization.AtPrime Q) Q.ResidueField x)
    (v : σ → ι → Q.ResidueField)
    (hv : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ (v j)))
    (hfirst : ∀ j x, coeff (Finsupp.single j 1) (tau x) = primeLocalDirectional Q (v j) x)
    (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    Function.Surjective
      (Ideal.mapCotangent (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (rectangularAugmentationIdeal (K := Q.ResidueField) n hn)
        (rectangularTaylorAlgHom n tau) (primeRectangular_maps_maximal Q tau hzero n hn)) := by
  intro z
  obtain ⟨x, hx⟩ := prime_cotangent_evaluation_surjective Q v hv
    (rectangularCotangentFirstCoefficients n hn z)
  refine ⟨x, ?_⟩
  apply rectangularCotangentFirstCoefficients_injective n hn
  rw [← hx]
  obtain ⟨a, rfl⟩ :=
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent_surjective x
  funext j
  rw [Ideal.mapCotangent_toCotangent, rectangularCotangentFirstCoefficients_toCotangent]
  change rectangularFirstCoefficients n hn
    (Ideal.Quotient.mk (rectangularIdeal (K := Q.ResidueField) n) (tau a.1)) j = _
  rw [rectangularFirstCoefficients_mk, hfirst]
  exact (primeNormalPairing_toCotangent Q (v j) a).symm

omit [CharZero C] [Fintype σ] [DecidableEq σ] in

theorem prime_localizedTaylor_firstCoefficient
    (tau : MvPolynomial ι C →+* MvPowerSeries σ Q.ResidueField)
    (hzero : ∀ p, constantCoeff (tau p) =
      algebraMap (Localization.AtPrime Q) Q.ResidueField
        (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p))
    (v : σ → ι → Q.ResidueField)
    (hfirst : ∀ j p, coeff (Finsupp.single j 1) (tau p) =
      ∑ i, v j i * primeResidueMap Q (MvPolynomial.pderiv i p))
    (j : σ) (x : Localization.AtPrime Q) :
    coeff (Finsupp.single j 1)
      (localizedTaylorMap Q.primeCompl tau
        (algebraMap (Localization.AtPrime Q) Q.ResidueField) hzero x) =
      primeLocalDirectional Q (v j) x := by
  apply localizedTaylorMap_linearCoefficient Q.primeCompl tau
    (algebraMap (Localization.AtPrime Q) Q.ResidueField) hzero j
      (primeLocalDirectional Q (v j))
  · intro a b
    simp only [Derivation.leibniz, Algebra.smul_def]
  · intro p
    rw [hfirst, primeLocalDirectional_polynomial]

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_OrdinaryMultiplicity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryMultiplicity

open scoped BigOperators
open OrdinaryDerivatives DerivativeIdeals CommutingTaylor
open PiExponentApprox.TransverseMultiplicity

theorem localTaylor_firstCoefficient (n k : ℕ) (B : Fin k → Fin n)
    (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime] (j : Fin k) (x : Localization.AtPrime Q) :
    MvPowerSeries.coeff (Finsupp.single j 1) (localTaylor n k B Q x) =
      primeLocalDirectional Q (Pi.basisFun Q.ResidueField _ (B j)) x := by
  apply prime_localizedTaylor_firstCoefficient Q (polynomialTaylor n k B Q)
    (polynomialTaylor_constant n k B Q) (fun j => Pi.basisFun Q.ResidueField _ (B j))
  intro l p
  change MvPowerSeries.coeff (Finsupp.single l 1)
    (residueTaylorFin k (fun j => partialFrame n (B j))
      (algebraMap (OrdinaryDerivatives.Polynomial n) Q.ResidueField) p) = _
  rw [coeff_single_residueTaylorFin]
  simp [Pi.basisFun_apply, Pi.single_apply, partialFrame_apply, primeResidueMap]

theorem prime_rectangular_length_lower (n k : ℕ)
    (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime] (B : Fin k → Fin n)
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ (B j))))
    (I : Ideal (OrdinaryDerivatives.Polynomial n)) (cost : Fin n → ℝ) (box : Fin k → ℕ) (delta : ℝ)
    (hbox : ∀ i, 2 ≤ box i) (hcost : ∀ i, 0 ≤ cost i)
    (hbudget : ∑ i, ((box i - 1 : ℕ) : ℝ) * cost (B i) ≤ delta)
    (hvanish : ∀ p ∈ I, ∀ l : List (Fin n),
      wordCost cost l ≤ delta → OrdinaryDerivatives.word n l p ∈ Q) :
    (∏ i, box i : ℕ) ≤
      Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map
          (algebraMap (OrdinaryDerivatives.Polynomial n) (Localization.AtPrime Q))) := by
  have hCot := prime_rectangular_mapCotangent_surjective Q (localTaylor n k B Q)
    (localTaylor_constant n k B Q) (fun j => Pi.basisFun Q.ResidueField _ (B j)) hB
    (localTaylor_firstCoefficient n k B Q) box hbox
  have hP : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤
      RingHom.ker (algebraMap (Localization.AtPrime Q) Q.ResidueField) := by
    rw [show RingHom.ker (algebraMap (Localization.AtPrime Q) Q.ResidueField) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) from IsLocalRing.ker_residue]
  apply rectangularTaylor_length_lower box (rectangularPositive box hbox)
    (localTaylor n k B Q) (algebraMap (Localization.AtPrime Q) Q.ResidueField)
    IsLocalRing.residue_surjective (localTaylor_constant n k B Q)
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) _ hP hCot
  apply localizedTaylorMap_ideal_le Q.primeCompl (polynomialTaylor n k B Q)
    (algebraMap (Localization.AtPrime Q) Q.ResidueField) (polynomialTaylor_constant n k B Q)
  apply OrdinaryTaylor.ordinary_residueTaylor_ideal_le n k B
    (algebraMap (OrdinaryDerivatives.Polynomial n) Q.ResidueField) I cost box delta hcost hbudget
  intro p hp l hl
  exact Ideal.algebraMap_residueField_eq_zero.mpr (hvanish p hp l hl)

end PiExponent.OrdinaryMultiplicity
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_OrdinarySliceComparison
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.OrdinarySliceComparison

open scoped BigOperators
open NormalBasisRigidity NormalBasisProducts TransverseWeightedMultiplicity
open OrdinaryDerivatives DerivativeIdeals

theorem comparison_of_normal_basis {n : ℕ}
    (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime]
    (A : Finset (Fin n)) (hk : 0 < A.card)
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    (B : Fin A.card → Fin n)
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ (B j))))
    {J : Type*} (f : J → OrdinaryDerivatives.Polynomial n)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
    (hn : ∀ i, 2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
    (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ l : List (Fin n),
      wordCost cost l ≤ epsilon * N → OrdinaryDerivatives.word n l p ∈ Q) :
    (∏ i ∈ A, (rho i : ℝ)) ≤
      (A.card : ℝ) ^ A.card * (∏ i, cost (B i)) / epsilon ^ A.card := by
  obtain ⟨L, hL, hupper⟩ := PrimeWeightedBezout.weighted_prime_length_bound_q68
    Q A hA f hQ rho hrho N hN.le hdegree
  have hlower := OrdinaryMultiplicity.prime_rectangular_length_lower n A.card Q B hB
    (Ideal.span (Set.range f)) cost
    (rectangularCutoff (fun j => cost (B j)) (epsilon * N)) (epsilon * N) hn
    (fun i => (hcost i).le)
    (rectangularCutoff_budget hk (fun j => cost (B j)) (fun j => hcost _)
      (epsilon * N) (mul_pos hepsilon hN)) hvanish
  change (∏ i, rectangularCutoff (fun j => cost (B j)) (epsilon * N) i : ℕ) ≤
    CoordinateSliceComparison.primeLength Q (Ideal.span (Set.range f)) at hlower
  rw [hL] at hlower
  have hrhoR (i : Fin n) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have h := weight_comparison_of_rectangular_count hk
    (fun i => (rho (A.equivFin.symm i) : ℝ)) (fun j => cost (B j)) epsilon N L
    (fun i => hrhoR _) (fun j => hcost _) hepsilon hN (by exact_mod_cast hlower)
    (by simpa only [prod_equivFin A (fun i => (rho i : ℝ))] using hupper)
  simpa only [prod_equivFin A (fun i => (rho i : ℝ))] using h

end PiExponent.OrdinarySliceComparison
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_PersistentWeightComparison
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PersistentWeightComparison

open scoped BigOperators
open PiExponentApprox NormalBasisRigidity NormalBasisProducts

theorem ordinary_normal_comparison {m n : ℕ} (hn : n ≤ m + 2)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles n cost (sigma / ((m : ℝ) + 2)) N)
    (F : OrdinaryDerivatives.Polynomial n)
    (hF : WeightedSliceDegree.SupportBound (fun i => (rho i : ℝ)) N F)
    (bound : ℝ) (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime]
    (hQ : Q ∈ (OrdinaryDerivatives.ideal n cost bound F).minimalPrimes)
    (hvanish : ∀ p ∈ OrdinaryDerivatives.ideal n cost bound F,
      ∀ word : List (Fin n),
        DerivativeIdeals.wordCost cost word ≤ (sigma / ((m : ℝ) + 2)) * N →
          OrdinaryDerivatives.word n word p ∈ Q) :
    OrdinaryComponentRigidity.NormalProductComparison Q
      (fun i => (rho i : ℝ)) cost (comparisonConstant m sigma) := by
  intro A B hA hB
  have hcard : A.card = B.card := hA.card_eq.trans hB.card_eq.symm
  by_cases hk0 : A.card = 0
  · have hA0 : A = ∅ := Finset.card_eq_zero.mp hk0
    have hB0 : B = ∅ := Finset.card_eq_zero.mp (hcard.symm.trans hk0)
    have hc := rectangular_factor_le_constant m 0 sigma hsigma (by omega)
    simpa [hA0, hB0, comparisonConstant] using hc
  have hk : 0 < A.card := Nat.pos_of_ne_zero hk0
  have hka : A.card ≤ n := by simpa using Finset.card_le_univ A
  have hepsilon : 0 < sigma / ((m : ℝ) + 2) := by positivity
  have hrhoR (i : Fin n) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have hdegree : ∀ j, ∀ d ∈ (OrdinaryDerivatives.equations cost bound F j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N := by
    intro j
    have h := OrdinaryDerivatives.equation_supportBound cost (fun i => (rho i : ℝ))
      bound N F hF (fun i => (hrhoR i).le) j
    simpa only [WeightedSliceDegree.SupportBound, Finsupp.weight_apply, Finsupp.sum,
      nsmul_eq_mul] using h
  have hcomp := OrdinarySliceComparison.comparison_of_normal_basis Q A hk hA
    (enumeration A B hcard) (enumeration_linearIndependent A B hcard hB)
    (OrdinaryDerivatives.equations cost bound F)
    (by simpa only [OrdinaryDerivatives.span_equations] using hQ)
    rho hrho cost hcost (sigma / ((m : ℝ) + 2)) N hepsilon hN hdegree
    (hrect A.card hk hka (enumeration A B hcard))
    (by simpa only [OrdinaryDerivatives.span_equations] using hvanish)
  exact hcomp.trans (by
    have hc := rectangular_comparison_le_constant (m := m) (k := A.card)
      (hka.trans hn) (fun i => cost (enumeration A B hcard i)) sigma hsigma
      (fun i => (hcost _).le)
    simpa only [prod_enumeration A B hcard cost, comparisonConstant] using hc)

theorem ordinary_persistent_comparison_q68_oai {m n : ℕ} (hn : n ≤ m + 2)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles n cost (sigma / ((m : ℝ) + 2)) N)
    (F : OrdinaryDerivatives.Polynomial n)
    (hF : WeightedSliceDegree.SupportBound (fun i => (rho i : ℝ)) N F)
    (d : ℕ) (P : Ideal (OrdinaryDerivatives.Polynomial n)) :
    OrdinaryComponentRigidity.PersistentNormalComparison (fun i => (rho i : ℝ)) cost
      (comparisonConstant m sigma) ((sigma / ((m : ℝ) + 2)) * N) F d P := by
  intro r hr Q hQ hQP hQr hQnext hQlo hQhi hvanish
  let := hQ
  exact ordinary_normal_comparison hn rho hrho cost hcost sigma N hsigma hN hrect
    F hF _ Q hQr hvanish

end PiExponent.PersistentWeightComparison
end

end OAI
end

theorem solution : type_of% @OAI.PiExponent.PersistentWeightComparison.ordinary_persistent_comparison_q68_oai := @OAI.PiExponent.PersistentWeightComparison.ordinary_persistent_comparison_q68_oai
