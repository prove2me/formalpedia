-- Prove2me | solution 1 for OAI.PiExponentJets.W22.ActualRegularCutHistory.degree_bound_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:13:34.505416+00:00
-- url     : https://prove2.me/submissions/9a682728-09e4-4a03-a848-1d6bb81cbeb6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A019
import Definitions.Def_OAIQ068A027
import Theorems.Thm_OAI_PiExponentJets_W22_RetainedPrimeCycle_retainedChild_dimension_q68
import Theorems.Thm_OAI_PiExponentJets_W22_actualHP_natDegree_of_prime_dimension_q68
import Theorems.Thm_OAI_PiExponentJets_W22_component_multiplicity_sum_bound_q68
import Theorems.Thm_OAI_PiExponentJets_W22_localized_cyclic_filtration_length_q68
import Theorems.Thm_OAI_PiExponentJets_W22_localized_onecut_parent_recurrence_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_HilbertDifferenceDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W27
open Polynomial

theorem difference_taylor_coefficient (p : Polynomial ℚ) (s : ℕ)
    (hp : p.natDegree = s+1) (a : ℚ) :
    (p - Polynomial.taylor a p).coeff s = -a * (s+1 : ℚ) * p.leadingCoeff := by
  have hd : (Polynomial.hasseDeriv s p).natDegree ≤ 1 := by
    simpa [hp] using Polynomial.natDegree_hasseDeriv_le p s
  have hlin := Polynomial.eq_X_add_C_of_natDegree_le_one hd
  have h0 : (Polynomial.hasseDeriv s p).coeff 0 = p.coeff s := by
    simp [Polynomial.hasseDeriv_coeff]
  have h1 : (Polynomial.hasseDeriv s p).coeff 1 = (s+1 : ℚ) * p.leadingCoeff := by
    rw [Polynomial.hasseDeriv_coeff]
    simp only [Nat.add_comm 1 s, Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one]
    rw [← hp, Polynomial.coeff_natDegree]
  rw [Polynomial.coeff_sub, Polynomial.taylor_coeff, hlin]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [h0, h1]
  ring

theorem difference_taylor_natDegree_le (p : Polynomial ℚ) (s : ℕ)
    (hp : p.natDegree = s+1) (a : ℚ) :
    (p - Polynomial.taylor a p).natDegree ≤ s := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [Polynomial.coeff_sub]
  by_cases he : n = s+1
  · subst n
    rw [← hp, Polynomial.coeff_natDegree, Polynomial.coeff_taylor_natDegree, sub_self]
  · have hlt : p.natDegree < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hlt), sub_self]

theorem backward_difference_degree_and_leading
    (p : Polynomial ℚ) (s : ℕ) (hp : p.natDegree = s+1)
    (d : ℚ) (hd : d ≠ 0) :
    (p - Polynomial.taylor (-d) p).natDegree = s ∧
      (p - Polynomial.taylor (-d) p).leadingCoeff = d * (s+1 : ℚ) * p.leadingCoeff := by
  have hp0 : p ≠ 0 := by
    intro hz
    simp [hz] at hp
  have hs : (s+1 : ℚ) ≠ 0 := by positivity
  have hc : (p - Polynomial.taylor (-d) p).coeff s =
      d * (s+1 : ℚ) * p.leadingCoeff := by
    simpa using difference_taylor_coefficient p s hp (-d)
  have hcn : (p - Polynomial.taylor (-d) p).coeff s ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero hd hs) (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  have hdeg := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (difference_taylor_natDegree_le p s hp (-d)) hcn
  refine ⟨hdeg, ?_⟩
  simpa only [Polynomial.leadingCoeff, hdeg] using hc

theorem backward_difference_multiplicity
    (p : Polynomial ℚ) (s : ℕ) (hp : p.natDegree = s+1)
    (d : ℚ) (hd : d ≠ 0) :
    (p - Polynomial.taylor (-d) p).leadingCoeff *
        ((p - Polynomial.taylor (-d) p).natDegree.factorial : ℚ) =
      d * (p.leadingCoeff * (p.natDegree.factorial : ℚ)) := by
  obtain ⟨hdeg, hl⟩ := backward_difference_degree_and_leading p s hp d hd
  rw [hl, hdeg, hp, Nat.factorial_succ]
  push_cast
  ring

theorem backward_difference_eq_comp (p : Polynomial ℚ) (d : ℚ) :
    p - Polynomial.taylor (-d) p = p - p.comp (Polynomial.X - Polynomial.C d) := by
  simp only [Polynomial.taylor_apply, Polynomial.C_neg, sub_eq_add_neg]

end PiExponentJets.W27

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_QuotientSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem quotientSectionMultiply_injective (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Function.Injective (quotientSectionMultiply I f hf n) := by
  intro x y h
  apply Subtype.ext
  exact hreg (congrArg Subtype.val h)

theorem quotientSectionCokernel_finrank_add (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Module.finrank k
        (quotientSection I (n + d) ⧸
          LinearMap.range (quotientSectionMultiply I f hf n)) +
      Module.finrank k (quotientSection I n) =
      Module.finrank k (quotientSection I (n + d)) := by
  have hi := quotientSectionMultiply_injective I f hf hreg n
  simpa only [LinearMap.finrank_range_of_inj hi] using
    (LinearMap.range (quotientSectionMultiply I f hf n)).finrank_quotient_add_finrank

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularHilbertStep
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem regular_hilbert_step [Finite σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) (n+d)) +
      Module.finrank k (quotientSection I n) =
      Module.finrank k (quotientSection I (n+d)) := by
  have hd := quotientSectionCokernel_finrank_add I f hf hreg n
  rw [← quotientSectionFactor_ker_eq I hI f hf n] at hd
  let e := (quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right (n+d)).quotKerEquivOfSurjective
      (quotientSectionFactor_surjective I (Ideal.span {f} ⊔ I) le_sup_right (n+d))
  rw [e.finrank_eq] at hd
  exact hd

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProperHypersurfaceHilbert
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem prime_quotient_right_regular (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (f : MvPolynomial σ k) (hfP : f ∉ P) :
    IsRightRegular (Ideal.Quotient.mk P f) := by
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by
    intro hz
    exact hfP (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  intro x y hxy
  exact mul_right_cancel₀ hf0 hxy

theorem regular_hypersurface_polynomial_eventually
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f))
    (p : Polynomial ℚ) (N : ℕ)
    (hP : ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ)) :
    ∀ n : ℕ, N+d < n →
      (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) =
        (p-shiftHilbertPolynomial p d).eval (n : ℚ) := by
  intro n hn
  have hdn : d ≤ n := by omega
  have hnP : N < n := by omega
  have hnshift : N < n-d := by omega
  have h := regular_hilbert_step I hI f hf hreg (n-d)
  rw [Nat.sub_add_cancel hdn] at h
  have hc : (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) +
      (Module.finrank k (quotientSection I (n-d)) : ℚ) =
      (Module.finrank k (quotientSection I n) : ℚ) := by
    exact_mod_cast h
  rw [hP n hnP, hP (n-d) hnshift] at hc
  rw [Polynomial.eval_sub, shiftHilbertPolynomial_eval p d n hdn]
  exact eq_sub_of_add_eq hc

theorem prime_hypersurface_actual_hilbert_degree
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hfP : f ∉ P) (hd : 0 < d)
    (p : Polynomial ℚ) (N s : ℕ)
    (hp : ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection P n) : ℚ) = p.eval (n : ℚ))
    (hdegree : p.natDegree = s+1) :
    ∃ q : Polynomial ℚ,
      (∃ M : ℕ, ∀ n : ℕ, M < n →
        (Module.finrank k (quotientSection (Ideal.span {f} ⊔ P) n) : ℚ) = q.eval (n : ℚ)) ∧
      q.natDegree = s ∧
      q.leadingCoeff * (q.natDegree.factorial : ℚ) =
        (d : ℚ) * (p.leadingCoeff * (p.natDegree.factorial : ℚ)) := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  refine ⟨p-Polynomial.taylor (-(d : ℚ)) p, ⟨N+d, ?_⟩,
    (PiExponentJets.W27.backward_difference_degree_and_leading p s hdegree (d : ℚ) hdq).1,
    PiExponentJets.W27.backward_difference_multiplicity p s hdegree (d : ℚ) hdq⟩
  intro n hn
  rw [PiExponentJets.W27.backward_difference_eq_comp]
  exact regular_hypersurface_polynomial_eventually P hP f hf
    (prime_quotient_right_regular P f hfP) p N hp n hn

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousPrimeFactor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

theorem exists_homogeneous_prime_colon
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hproper : I ≠ ⊤) :
    ∃ (d : ℕ) (f : MvPolynomial σ k), f.IsHomogeneous d ∧ f ∉ I ∧
      (I.colon {f}).IsPrime := by
  classical
  let candidates : Ideal (MvPolynomial σ k) → Prop := fun P =>
    ∃ d f, f.IsHomogeneous d ∧ f ∉ I ∧ P = I.colon {f}
  have hnonempty : ∃ P, candidates P := by
    refine ⟨I.colon {(1 : MvPolynomial σ k)}, 0, 1, ?_, ?_, rfl⟩
    · exact MvPolynomial.isHomogeneous_one σ k
    · exact fun h => hproper (Ideal.eq_top_of_isUnit_mem I h isUnit_one)
  obtain ⟨P, hP, hmax⟩ := exists_maximal_of_wellFoundedGT candidates hnonempty
  obtain ⟨d, f, hf, hfI, rfl⟩ := hP
  refine ⟨d, f, hf, hfI, ?_⟩
  apply (homogeneous_colon_singleton I hI hf).isPrime_of_homogeneous_mem_or_mem
  · intro htop
    have h : (1 : MvPolynomial σ k) ∈ I.colon {f} := by
      rw [htop]
      trivial
    exact hfI (by simpa only [Submodule.mem_colon_singleton, one_smul] using h)
  · intro a b ha hb hab
    by_cases hbI : b ∈ I.colon {f}
    · exact Or.inr hbI
    · left
      obtain ⟨e, he⟩ := hb
      have hb' : b.IsHomogeneous e := he
      have hbf : (b * f).IsHomogeneous (e + d) := hb'.mul hf
      have hbfI : b * f ∉ I := by
        simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using hbI
      have hle : I.colon {f} ≤ I.colon {b * f} := by
        intro r hr
        apply Submodule.mem_colon_singleton.mpr
        have hrf : r * f ∈ I := by
          simpa only [smul_eq_mul] using (Submodule.mem_colon_singleton.mp hr)
        simpa only [smul_eq_mul, mul_left_comm r b f] using I.mul_mem_left b hrf
      have hback : I.colon {b * f} ≤ I.colon {f} :=
        hmax ⟨e + d, b * f, hbf, hbfI, rfl⟩ hle
      apply hback
      apply Submodule.mem_colon_singleton.mpr
      simpa only [smul_eq_mul, mul_assoc] using (Submodule.mem_colon_singleton.mp hab)

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HilbertPolynomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem polynomial_eq_of_nat_tail (p q : Polynomial ℚ) (N : ℕ)
    (h : ∀ n : ℕ, N < n → p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q := by
  have hinj : Function.Injective (fun n : ℕ => ((N + 1 + n : ℕ) : ℚ)) := by
    intro a b hab
    change ((N + 1 + a : ℕ) : ℚ) = ((N + 1 + b : ℕ) : ℚ) at hab
    have hab' : N + 1 + a = N + 1 + b := by exact_mod_cast hab
    omega
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hinj).mono
  rintro x ⟨n, rfl⟩
  exact h _ (by omega)

theorem actualHP_eventually (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = (actualHP I hI).eval (n : ℚ) :=
  (exists_homogeneous_hilbert_polynomial σ I hI).choose_spec

theorem actualHP_unique (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ)) :
    actualHP I hI = p := by
  obtain ⟨M, hM⟩ := actualHP_eventually I hI
  apply polynomial_eq_of_nat_tail _ _ (M + N)
  intro n hn
  exact (hM n (by omega)).symm.trans (hp n (by omega))

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousPrimeFiltration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem HomogeneousPrimeStep.homogeneous {I J : Ideal (MvPolynomial σ k)}
    (h : HomogeneousPrimeStep I J) :
    J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  obtain ⟨hI, d, f, hf, _, _, rfl⟩ := h
  apply hI.sup
  apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule σ k)
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact ⟨d, hf⟩

theorem HomogeneousPrimeStep.lt {I J : Ideal (MvPolynomial σ k)}
    (h : HomogeneousPrimeStep I J) : I < J := by
  obtain ⟨_, d, f, _, hfI, _, rfl⟩ := h
  refine lt_of_le_of_ne le_sup_left ?_
  intro heq
  have hm : f ∈ I ⊔ Ideal.span {f} :=
    (show Ideal.span {f} ≤ I ⊔ Ideal.span {f} from le_sup_right)
      (Ideal.subset_span (by simp))
  exact hfI (by simpa only [← heq] using hm)

variable [Finite σ]

theorem exists_homogeneous_prime_filtration
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ s : RelSeries {(A, B) | HomogeneousPrimeStep (k := k) (σ := σ) A B},
      s.head = I ∧ s.last = ⊤ := by
  let r : Set (Ideal (MvPolynomial σ k) × Ideal (MvPolynomial σ k)) :=
    {(A, B) | HomogeneousPrimeStep A B}
  have ht : (⊤ : Ideal (MvPolynomial σ k)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) ∧
      ∃ s : RelSeries r, s.head = I ∧ s.last = ⊤ := by
    refine WellFoundedGT.induction_top
      ⟨I, hI, RelSeries.singleton r I, rfl, rfl⟩ ?_
    rintro J hJtop ⟨hJ, s, hshead, hslast⟩
    obtain ⟨d, f, hf, hfJ, hp⟩ := exists_homogeneous_prime_colon J hJ hJtop
    have hstep : HomogeneousPrimeStep J (J ⊔ Ideal.span {f}) :=
      ⟨hJ, d, f, hf, hfJ, hp, rfl⟩
    refine ⟨J ⊔ Ideal.span {f}, hstep.lt, hstep.homogeneous,
      s.snoc (J ⊔ Ideal.span {f}) (by
        change HomogeneousPrimeStep s.last (J ⊔ Ideal.span {f})
        simpa only [hslast] using hstep), ?_, by simp only [RelSeries.last_snoc]⟩
    simpa using hshead
  exact ht.2

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousComponentLength
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

theorem exists_homogeneous_cyclic_filtration_nat
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ (n : ℕ) (J : ℕ → Ideal (MvPolynomial σ k))
      (f : ℕ → MvPolynomial σ k) (d : ℕ → ℕ),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = I ∧ J n = ⊤ ∧
      ∀ i < n, (J i).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
        (f i).IsHomogeneous (d i) ∧ f i ∉ J i ∧
        ((J i).colon {f i}).IsPrime ∧ J (i + 1) = J i ⊔ Ideal.span {f i} := by
  classical
  obtain ⟨s, hshead, hslast⟩ := exists_homogeneous_prime_filtration I hI
  have hsmono : Monotone s :=
    (Fin.strictMono_iff_lt_succ.mpr fun i => (s.step i).lt).monotone
  let J : ℕ → Ideal (MvPolynomial σ k) := fun i =>
    s ⟨min i s.length, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hd : ∀ i : Fin s.length, ∃ (d : ℕ) (f : MvPolynomial σ k),
      f.IsHomogeneous d ∧ f ∉ s i.castSucc ∧
        ((s i.castSucc).colon {f}).IsPrime ∧
        s i.succ = s i.castSucc ⊔ Ideal.span {f} := fun i => (s.step i).2
  let degrees : Fin s.length → ℕ := fun i => (hd i).choose
  let generators : Fin s.length → MvPolynomial σ k := fun i => (hd i).choose_spec.choose
  let f : ℕ → MvPolynomial σ k := fun i =>
    if hi : i < s.length then generators ⟨i, hi⟩ else 0
  let d : ℕ → ℕ := fun i => if hi : i < s.length then degrees ⟨i, hi⟩ else 0
  refine ⟨s.length, J, f, d, ?_, ?_, ?_, ?_⟩
  · intro i
    apply hsmono
    exact min_le_min_right s.length (Nat.le_succ i)
  · change s.head = I
    exact hshead
  · simpa only [J, min_self, RelSeries.last, Fin.last] using hslast
  · intro i hi
    have hfi := (hd ⟨i, hi⟩).choose_spec.choose_spec
    have hleft : J i = s (Fin.castSucc ⟨i, hi⟩) := by
      apply congrArg s
      apply Fin.ext
      exact min_eq_left (Nat.le_of_lt hi)
    have hright : J (i + 1) = s (Fin.succ ⟨i, hi⟩) := by
      apply congrArg s
      apply Fin.ext
      exact min_eq_left (Nat.succ_le_of_lt hi)
    simpa only [f, d, dite_eq_left hi, degrees, generators, hleft, hright] using
      And.intro (s.step ⟨i, hi⟩).1 hfi

theorem exists_homogeneous_component_length_count
    (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : Q ∈ I.minimalPrimes) :
    ∃ (n : ℕ) (J : ℕ → Ideal (MvPolynomial σ k))
      (f : ℕ → MvPolynomial σ k) (d : ℕ → ℕ),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = I ∧ J n = ⊤ ∧
      (∀ i < n, (J i).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
        (f i).IsHomogeneous (d i) ∧ f i ∉ J i ∧
        ((J i).colon {f i}).IsPrime ∧ J (i + 1) = J i ⊔ Ideal.span {f i}) ∧
      Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map
          (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) =
        ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then 1 else 0 := by
  obtain ⟨n, J, f, d, hmono, hstart, hend, hstep⟩ :=
    exists_homogeneous_cyclic_filtration_nat I hI
  refine ⟨n, J, f, d, hmono, hstart, hend, hstep, ?_⟩
  exact localized_cyclic_filtration_length_q68 I Q hQ J hmono hstart n hend f
    (fun i hi => (hstep i hi).2.2.2.2) (fun i hi => (hstep i hi).2.2.2.1)

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeCutBudget
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ τ : Type*} [Field k] [Fintype σ] [Fintype τ]

theorem actualLocalLength_spec
    (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : Q ∈ I.minimalPrimes) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = actualLocalLength I Q := by
  obtain ⟨n, J, f, d, hmono, hstart, hend, hdata, hlength⟩ :=
    exists_homogeneous_component_length_count I Q hI hQ
  let m : ℕ := ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then 1 else 0
  have hm : Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = m := by
    rw [hlength]
    simp only [m, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [actualLocalLength, hm, ENat.toNat_natCast]

theorem actualHP_prime_cut_degree_multiplicity
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hfP : f ∉ P) (hd : 0 < d) (s : ℕ)
    (hdegree : (actualHP P hP).natDegree = s+1) :
    (actualHP (Ideal.span {f} ⊔ P) (primeCut_isHomogeneous P hP f hf)).natDegree = s ∧
      actualMultiplicity (Ideal.span {f} ⊔ P) (primeCut_isHomogeneous P hP f hf) s =
        (d : ℚ) * actualMultiplicity P hP (s+1) := by
  obtain ⟨N, hN⟩ := actualHP_eventually P hP
  obtain ⟨q, ⟨M, hM⟩, hqdegree, hqmult⟩ :=
    prime_hypersurface_actual_hilbert_degree P hP f hf hfP hd
      (actualHP P hP) N s hN hdegree
  have hq : actualHP (Ideal.span {f} ⊔ P) (primeCut_isHomogeneous P hP f hf) = q :=
    actualHP_unique _ _ q M hM
  refine ⟨by rw [hq]; exact hqdegree, ?_⟩
  unfold actualMultiplicity
  rw [hq]
  simpa only [Polynomial.leadingCoeff, hqdegree, hdegree] using hqmult

theorem prime_cut_component_budget
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hfP : f ∉ P) (hd : 0 < d) (s : ℕ)
    (hdegree : (actualHP P hP).natDegree = s+1)
    (Q : τ → Ideal (MvPolynomial σ k)) [∀ a, (Q a).IsPrime]
    (hQinj : Function.Injective Q)
    (hQhom : ∀ a, (Q a).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : ∀ a, Q a ∈ (Ideal.span {f} ⊔ P).minimalPrimes)
    (v : τ → σ) (hv : ∀ a, MvPolynomial.X (v a) ∉ Q a)
    (hchildDegree : ∀ a, (actualHP (Q a) (hQhom a)).natDegree = s) :
    (∑ a, (actualLocalLength (Ideal.span {f} ⊔ P) (Q a) : ℚ) *
      actualMultiplicity (Q a) (hQhom a) s) ≤
      (d : ℚ) * actualMultiplicity P hP (s+1) := by
  have hI := primeCut_isHomogeneous P hP f hf
  obtain ⟨hIdegree, hImult⟩ := actualHP_prime_cut_degree_multiplicity
    P hP f hf hfP hd s hdegree
  obtain ⟨m, hm, hpositive, hbudget⟩ := component_multiplicity_sum_bound_q68
    (Ideal.span {f} ⊔ P) hI Q hQinj hQhom hQ v hv
      (fun a => (hchildDegree a).trans hIdegree.symm)
  have hmactual : ∀ a, actualLocalLength (Ideal.span {f} ⊔ P) (Q a) = m a := by
    intro a
    unfold actualLocalLength
    rw [hm a, ENat.toNat_natCast]
  simpa only [hIdegree, hmactual, hImult] using hbudget

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RetainedIntersectionCycles
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

namespace ProjectiveComponent

variable {k : Type u} {σ : Type v} [Field k]

theorem coordinate_not_mem (P : ProjectiveComponent k σ) :
    MvPolynomial.X P.coordinate ∉ P.val := P.property.2.2.choose_spec

end ProjectiveComponent

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_NaturalMultiplicityPropagation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

theorem minimal_cut_of_intermediate_parent
    {A : Type*} [CommRing A] (I P Q : Ideal A) (x : A)
    (hQ : Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes) (hIP : I ≤ P) (hPQ : P ≤ Q) :
    Q ∈ (P ⊔ Ideal.span {x}).minimalPrimes := by
  refine ⟨⟨hQ.1.1, sup_le hPQ (le_sup_right.trans hQ.1.2)⟩, ?_⟩
  intro K hK hKQ
  exact hQ.2 ⟨hK.1, (sup_le_sup hIP le_rfl).trans hK.2⟩ hKQ

universe u
variable {k σ : Type u} [Field k] [Fintype σ]

theorem natural_local_onecut_recurrence
    (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (x : MvPolynomial σ k) (hx : x.IsHomogeneous d)
    (hQ : Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes)
    (hdim : ringKrullDim (Localization.AtPrime Q ⧸
      I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = 1)
    (hregular : Function.Injective
      (W28.LocalIntersection.quotientMul
        (I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q)))
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q) x))) :
    actualLocalLength (I ⊔ Ideal.span {x}) Q =
      ∑ P : MinimalParentsBelow I Q, actualLocalLength I P.val *
        actualLocalLength (P.val ⊔ Ideal.span {x}) Q := by
  have hrec := localized_onecut_parent_recurrence_q68 I Q x hdim hregular
  have hsum : globalParentCutSum I Q x =
      ((∑ P : MinimalParentsBelow I Q, actualLocalLength I P.val *
        actualLocalLength (P.val ⊔ Ideal.span {x}) Q : ℕ) : ℕ∞) := by
    unfold globalParentCutSum
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro P _
    have hP := PiExponentSiegel.W17.ConeLocalLength.minimalPrime_isHomogeneous
      I P.val hI P.property.1
    have hQP := minimal_cut_of_intermediate_parent I P.val Q x hQ
      P.property.1.1.2 P.property.2
    rw [actualLocalLength_spec I P.val hI P.property.1,
      actualLocalLength_spec (P.val ⊔ Ideal.span {x}) Q
        (cut_ideal_homogeneous P.val hP x hx) hQP, Nat.cast_mul]
  rw [actualLocalLength_spec (I ⊔ Ideal.span {x}) Q
    (cut_ideal_homogeneous I hI x hx) hQ, hsum] at hrec
  exact_mod_cast hrec

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_MultiplicityCycles
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

theorem actualMultiplicityCycle_cut_expansion
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (x : MvPolynomial σ k) (hx : x.IsHomogeneous d)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (hdim : ∀ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
      ringKrullDim (Localization.AtPrime Q.val ⧸
        I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val))) = 1)
    (hregular : ∀ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
      Function.Injective (W28.LocalIntersection.quotientMul
        (I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val)))
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val) x))) :
    (actualMultiplicityCycle (I ⊔ Ideal.span {x}) (cut_ideal_homogeneous I hI x hx) T v hv).degree =
      ∑ P : RetainedMinimalPrime I T, (actualLocalLength I P.val : ℚ) *
        ∑ Q : {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val},
          (actualLocalLength (P.val ⊔ Ideal.span {x}) Q.val.val : ℚ) *
          (RetainedMinimalPrime.toComponent (cut_ideal_homogeneous I hI x hx) v hv Q.val).hilbertDegree := by
  let D := actualMultiplicityCycle (I ⊔ Ideal.span {x}) (cut_ideal_homogeneous I hI x hx) T v hv
  have hrec (Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T) :=
    natural_local_onecut_recurrence I Q.val hI x hx Q.property.1 (hdim Q) (hregular Q)
  calc
    D.degree = ∑ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
        ∑ P : MinimalParentsBelow I Q.val,
          (actualLocalLength I P.val : ℚ) *
            (actualLocalLength (P.val ⊔ Ideal.span {x}) Q.val : ℚ) *
              (D.component Q).hilbertDegree := by
      unfold RetainedPrimeCycle.degree
      apply Finset.sum_congr rfl
      intro Q _
      let : Q.val.IsPrime := Q.property.1.1.1
      change (actualLocalLength (I ⊔ Ideal.span {x}) Q.val : ℚ) * (D.component Q).hilbertDegree = _
      rw [hrec Q, Nat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro P _
      rw [Nat.cast_mul]
    _ = ∑ z : (Σ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
        MinimalParentsBelow I Q.val),
          (actualLocalLength I z.2.val : ℚ) *
            (actualLocalLength (z.2.val ⊔ Ideal.span {x}) z.1.val : ℚ) *
              (D.component z.1).hilbertDegree := by rw [Fintype.sum_sigma]
    _ = ∑ z : (Σ P : RetainedMinimalPrime I T,
        {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val}),
          (actualLocalLength I z.1.val : ℚ) *
            (actualLocalLength (z.1.val ⊔ Ideal.span {x}) z.2.val.val : ℚ) *
              (D.component z.2.val).hilbertDegree := by
      apply Fintype.sum_equiv (parentChildIncidenceEquiv I T x)
      intro z
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Finset.mul_sum, mul_assoc, D, actualMultiplicityCycle]

theorem actualMultiplicityCycle_parent_budget
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (x : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hx : x.IsHomogeneous d)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (havoid : ∀ P : RetainedMinimalPrime I T, x ∉ P.val)
    (s : ℕ) (hparent : ∀ P : RetainedMinimalPrime I T,
      (actualHP P.val (RetainedMinimalPrime.toComponent hI v hv P).homogeneous).natDegree = s+1)
    (P : RetainedMinimalPrime I T) :
    (∑ Q : {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val},
      (actualLocalLength (P.val ⊔ Ideal.span {x}) Q.val.val : ℚ) *
        (RetainedMinimalPrime.toComponent (cut_ideal_homogeneous I hI x hx) v hv Q.val).hilbertDegree) ≤
      (d : ℚ) * (RetainedMinimalPrime.toComponent hI v hv P).hilbertDegree := by
  let C := actualMultiplicityCycle I hI T v hv
  let Qs := {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val}
  let Q : Qs → Ideal (MvPolynomial σ k) := fun q => q.val.val
  let E : Qs → ProjectiveComponent k σ := fun q =>
    RetainedMinimalPrime.toComponent (cut_ideal_homogeneous I hI x hx) v hv q.val
  have hQmin : ∀ q : Qs, Q q ∈ (Ideal.span {x} ⊔ P.val).minimalPrimes := by
    intro q
    simpa only [sup_comm] using minimal_cut_of_intermediate_parent I P.val q.val.val x
      q.val.property.1 P.property.1.1.2 q.property
  have hQdegree : ∀ q : Qs, (actualHP (Q q) (E q).homogeneous).natDegree = s := by
    intro q
    have hdim := RetainedPrimeCycle.retainedChild_dimension_q68 C x havoid s hparent T P
      ⟨Q q, hQmin q, q.val.property.2⟩
    exact actualHP_natDegree_of_prime_dimension_q68 (Q q) (E q).homogeneous
      (E q).coordinate (E q).coordinate_not_mem s hdim
  have hinj : Function.Injective Q := by
    intro q r h
    exact Subtype.ext (Subtype.ext h)
  have hb := prime_cut_component_budget P.val (C.component P).homogeneous x hx
    (havoid P) hd s (hparent P) Q hinj (fun q => (E q).homogeneous) hQmin
    (fun q => (E q).coordinate) (fun q => (E q).coordinate_not_mem) hQdegree
  change (∑ q : Qs,
    (actualLocalLength (P.val ⊔ Ideal.span {x}) (Q q) : ℚ) *
      actualMultiplicity (Q q) (E q).homogeneous
        (actualHP (Q q) (E q).homogeneous).natDegree) ≤
    (d : ℚ) * actualMultiplicity P.val (C.component P).homogeneous
      (actualHP P.val (C.component P).homogeneous).natDegree
  simp only [hQdegree, hparent]
  simpa only [sup_comm] using hb

theorem actualMultiplicityCycle_cut_degree_le
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (x : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hx : x.IsHomogeneous d)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (havoid : ∀ P : RetainedMinimalPrime I T, x ∉ P.val)
    (s : ℕ) (hparent : ∀ P : RetainedMinimalPrime I T,
      (actualHP P.val (RetainedMinimalPrime.toComponent hI v hv P).homogeneous).natDegree = s+1)
    (hdim : ∀ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
      ringKrullDim (Localization.AtPrime Q.val ⧸
        I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val))) = 1)
    (hregular : ∀ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
      Function.Injective (W28.LocalIntersection.quotientMul
        (I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val)))
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val) x))) :
    (actualMultiplicityCycle (I ⊔ Ideal.span {x}) (cut_ideal_homogeneous I hI x hx) T v hv).degree ≤
      (d : ℚ) * (actualMultiplicityCycle I hI T v hv).degree := by
  rw [actualMultiplicityCycle_cut_expansion I hI x hx T v hv hdim hregular]
  calc
    _ ≤ ∑ P : RetainedMinimalPrime I T, (actualLocalLength I P.val : ℚ) *
        ((d : ℚ) * (RetainedMinimalPrime.toComponent hI v hv P).hilbertDegree) := by
      apply Finset.sum_le_sum
      intro P _
      exact mul_le_mul_of_nonneg_left
        (actualMultiplicityCycle_parent_budget I hI x d hd hx T v hv havoid s hparent P)
        (Nat.cast_nonneg _)
    _ = _ := by
      rw [RetainedPrimeCycle.degree, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _
      dsimp only [actualMultiplicityCycle]
      ring

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularCutHistory
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

namespace RegularPrefixCut

variable {T : Ideal (MvPolynomial σ k)} {v : σ} {hv : MvPolynomial.X v ∉ T}
  {S : HomogeneousPolynomialIdeal k σ}

theorem degree_step (F : RegularPrefixCut T v hv S) :
    (actualMultiplicityCycle F.next.val F.next.property T v hv).degree ≤
      (F.polynomialDegree : ℚ) * (actualMultiplicityCycle S.val S.property T v hv).degree :=
  actualMultiplicityCycle_cut_degree_le S.val S.property F.polynomial F.polynomialDegree
    F.positiveDegree F.homogeneous T v hv F.avoidsParent F.dimensionIndex F.parentDegree
    F.localDimension F.regularAtChild

end RegularPrefixCut

theorem ActualRegularCutHistory.degree_bound_q68_oai
    {T : Ideal (MvPolynomial σ k)} {v : σ} {hv : MvPolynomial.X v ∉ T}
    {S₀ S : HomogeneousPolynomialIdeal k σ} {e : ℕ}
    (h : ActualRegularCutHistory T v hv S₀ S e) :
    (actualMultiplicityCycle S.val S.property T v hv).degree ≤
      (e : ℚ) * (actualMultiplicityCycle S₀.val S₀.property T v hv).degree := by
  induction h with
  | nil => simp
  | @step S e previous F ih =>
    calc
      _ ≤ (F.polynomialDegree : ℚ) *
          (actualMultiplicityCycle S.val S.property T v hv).degree := F.degree_step
      _ ≤ (F.polynomialDegree : ℚ) * ((e : ℚ) *
          (actualMultiplicityCycle S₀.val S₀.property T v hv).degree) :=
        mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg _)
      _ = _ := by rw [Nat.cast_mul]; ring

end PiExponentJets.W22

end OAI
end

theorem solution.{u} : type_of% @OAI.PiExponentJets.W22.ActualRegularCutHistory.degree_bound_q68_oai.{u} := @OAI.PiExponentJets.W22.ActualRegularCutHistory.degree_bound_q68_oai.{u}
