-- Prove2me | solution 1 for OAI.PiExponentJets.W22.component_multiplicity_sum_bound_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:15:31.357286+00:00
-- url     : https://prove2.me/submissions/2802babb-95c5-4134-9f66-cd6294bf8a50

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A011
import Definitions.Def_OAIQ068A027
import Theorems.Thm_OAI_PiExponentJets_W22_localized_cyclic_filtration_length_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeHilbertDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W27

open scoped BigOperators
open Filter Polynomial
open PiExponentJets.W64

variable {k σ : Type*} [Field k] [Fintype σ]

theorem prime_quotientSection_finrank_pos
    (P : Ideal (MvPolynomial σ k)) [hP : P.IsPrime]
    (i : σ) (hi : MvPolynomial.X i ∉ P) (n : ℕ) :
    0 < Module.finrank k (quotientSection P n) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  let x : quotientSection P n :=
    ⟨Ideal.Quotient.mk P (MvPolynomial.X i ^ n),
      Submodule.mem_map.mpr ⟨MvPolynomial.X i ^ n,
        MvPolynomial.isHomogeneous_X_pow i n, rfl⟩⟩
  refine ⟨x, ?_⟩
  intro hx
  have hx' : Ideal.Quotient.mk P (MvPolynomial.X i ^ n) = 0 :=
    congrArg Subtype.val hx
  exact hi (hP.mem_of_pow_mem n (Ideal.Quotient.eq_zero_iff_mem.mp hx'))

theorem polynomial_leadingCoeff_nonneg_of_eventually_nonneg
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → 0 ≤ p.eval (n : ℚ)) :
    0 ≤ p.leadingCoeff := by
  by_cases hd : p.natDegree = 0
  · have he : p = Polynomial.C p.leadingCoeff := by
      simpa [Polynomial.leadingCoeff, hd] using Polynomial.eq_C_of_natDegree_eq_zero hd
    have hconst := hp N le_rfl
    rw [he, Polynomial.eval_C] at hconst
    exact hconst
  · by_contra hneg
    have hneg' : p.leadingCoeff < 0 := lt_of_not_ge hneg
    have hdeg : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
    have ht : Tendsto (fun n : ℕ => p.eval (n : ℚ)) atTop atBot :=
      (p.tendsto_atBot_of_leadingCoeff_nonpos hdeg hneg'.le).comp
        tendsto_natCast_atTop_atTop
    obtain ⟨n, hnN, hn⟩ := ((eventually_ge_atTop N).and
      (ht.eventually_lt_atBot 0)).exists
    exact (not_lt_of_ge (hp n hnN)) hn

theorem polynomial_leadingCoeff_pos_of_eventually_pos
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → 0 < p.eval (n : ℚ)) :
    0 < p.leadingCoeff := by
  have hn := polynomial_leadingCoeff_nonneg_of_eventually_nonneg p N
    (fun n hn => (hp n hn).le)
  have hp0 : p ≠ 0 := by
    intro h
    simpa [h] using hp N le_rfl
  exact lt_of_le_of_ne hn (Polynomial.leadingCoeff_ne_zero.mpr hp0).symm

theorem factorial_leadingCoeff_is_integer
    (p : Polynomial ℚ) (values : ℕ → ℕ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) = (values n : ℚ)) :
    ∃ z : ℤ, (z : ℚ) = p.leadingCoeff * (p.natDegree.factorial : ℚ) := by
  let d := p.natDegree
  let z : ℤ := ∑ j ∈ Finset.range (d + 1),
    ((-1 : ℤ) ^ (d-j) * (d.choose j : ℤ)) * (values (N+j) : ℤ)
  refine ⟨z, ?_⟩
  have hd := congrFun p.fwdDiff_iter_degree_eq_factorial (N : ℚ)
  rw [fwdDiff_iter_eq_sum_shift] at hd
  have he (j : ℕ) : p.eval ((N : ℚ) + j • (1 : ℚ)) = (values (N+j) : ℚ) := by
    simpa using hp (N+j) (Nat.le_add_right N j)
  simp only [he] at hd
  simpa [z, d, Int.cast_sum, Int.cast_mul, Int.cast_pow, zsmul_eq_mul,
    Pi.smul_apply, smul_eq_mul] using hd

theorem eventual_hilbert_degree_ge_one
    (p : Polynomial ℚ) (values : ℕ → ℕ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) = (values n : ℚ))
    (hv : ∀ n : ℕ, N ≤ n → 0 < values n) :
    1 ≤ p.leadingCoeff * (p.natDegree.factorial : ℚ) := by
  have hl := polynomial_leadingCoeff_pos_of_eventually_pos p N (by
    intro n hn
    rw [hp n hn]
    exact_mod_cast hv n hn)
  have hpos : 0 < p.leadingCoeff * (p.natDegree.factorial : ℚ) :=
    mul_pos hl (by exact_mod_cast Nat.factorial_pos p.natDegree)
  obtain ⟨z, hz⟩ := factorial_leadingCoeff_is_integer p values N hp
  have hzpos : 0 < z := by exact_mod_cast (hz.symm ▸ hpos)
  have hzge : (1 : ℤ) ≤ z := by omega
  rw [← hz]
  exact_mod_cast hzge

theorem prime_eventual_hilbert_degree_ge_one
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (i : σ) (hi : MvPolynomial.X i ∉ P)
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection P n) : ℚ)) :
    1 ≤ p.leadingCoeff * (p.natDegree.factorial : ℚ) :=
  eventual_hilbert_degree_ge_one p _ N hp
    (fun n _ => prime_quotientSection_finrank_pos P i hi n)

theorem prime_eventual_hilbert_coefficient_ge_one
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (i : σ) (hi : MvPolynomial.X i ∉ P)
    (p : Polynomial ℚ) (N d : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection P n) : ℚ))
    (hd : p.natDegree = d) :
    1 ≤ p.coeff d * (d.factorial : ℚ) := by
  simpa [Polynomial.leadingCoeff, hd] using
    prime_eventual_hilbert_degree_ge_one P i hi p N hp

end PiExponentJets.W27

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_HilbertGrowthComparison
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

open Polynomial

theorem natDegree_le_of_eventual_polynomial_le (p q : Polynomial ℚ)
    (hp : 0 < p.leadingCoeff) (N : ℕ)
    (hle : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) ≤ q.eval (n : ℚ)) :
    p.natDegree ≤ q.natDegree := by
  by_contra hn
  have hdeg : q.degree < p.degree := degree_lt_degree (Nat.lt_of_not_ge hn)
  have hnonneg := W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg
    (q - p) N (fun n hn => by simpa only [eval_sub] using sub_nonneg.mpr (hle n hn))
  rw [leadingCoeff_sub_of_degree_lt' hdeg] at hnonneg
  exact (not_le_of_gt hp) (neg_nonneg.mp hnonneg)

end PiExponentJets.W24

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
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeDegreeExistence
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W27
open PiExponentJets.W64
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

omit [Fintype σ] in
theorem quotient_eventual_hilbert_coefficient_nonneg
    (I : Ideal (MvPolynomial σ k)) (p : Polynomial ℚ) (N d : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection I n) : ℚ))
    (hd : p.natDegree ≤ d) : 0 ≤ p.coeff d * (d.factorial : ℚ) := by
  have hl : 0 ≤ p.leadingCoeff :=
    polynomial_leadingCoeff_nonneg_of_eventually_nonneg p N (by
      intro n hn
      rw [hp n hn]
      positivity)
  rcases eq_or_lt_of_le hd with heq | hlt
  · rw [← heq, ← Polynomial.leadingCoeff]
    exact mul_nonneg hl (by positivity)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_mul]

end PiExponentJets.W27

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_ColonHilbertPolynomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

theorem shiftHilbertPolynomial_top_coeff (p : Polynomial ℚ) (d t : ℕ)
    (hp : p.natDegree ≤ t) :
    (shiftHilbertPolynomial p d).coeff t = p.coeff t := by
  by_cases he : p.natDegree = t
  · rw [← he]
    calc
      (shiftHilbertPolynomial p d).coeff p.natDegree =
          (shiftHilbertPolynomial p d).coeff (shiftHilbertPolynomial p d).natDegree := by
            rw [shiftHilbertPolynomial_natDegree]
      _ = (shiftHilbertPolynomial p d).leadingCoeff := Polynomial.coeff_natDegree
      _ = p.leadingCoeff := shiftHilbertPolynomial_leadingCoeff p d
      _ = p.coeff p.natDegree := Polynomial.coeff_natDegree.symm
  · have ht : p.natDegree < t := lt_of_le_of_ne hp he
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by simpa using ht : (shiftHilbertPolynomial p d).natDegree < t),
      Polynomial.coeff_eq_zero_of_natDegree_lt ht]

theorem colon_hilbert_polynomial_eventually
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (pJ pP : Polynomial ℚ) (NJ NP : ℕ)
    (hJ : ∀ n : ℕ, NJ < n →
      (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) = pJ.eval (n : ℚ))
    (hP : ∀ n : ℕ, NP < n →
      (Module.finrank k (quotientSection (I.colon {f}) n) : ℚ) = pP.eval (n : ℚ)) :
    ∀ n : ℕ, NJ + NP + d < n →
      (Module.finrank k (quotientSection I n) : ℚ) =
        (pJ + shiftHilbertPolynomial pP d).eval (n : ℚ) := by
  intro n hn
  have hdn : d ≤ n := by omega
  have hnJ : NJ < n := by omega
  have hnP : NP < n-d := by omega
  have h := colon_hilbert_step I hI f hf (n-d)
  rw [Nat.sub_add_cancel hdn] at h
  have hc : (Module.finrank k (quotientSection I n) : ℚ) =
      (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) +
      (Module.finrank k (quotientSection (I.colon {f}) (n-d)) : ℚ) := by
    exact_mod_cast h.symm
  rw [hc, hJ n hnJ, hP (n-d) hnP,
    Polynomial.eval_add, shiftHilbertPolynomial_eval pP d n hdn]

end PiExponentJets.W64

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

theorem actualHP_congr {I J : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (h : I = J) :
    actualHP I hI = actualHP J hJ := by
  subst J
  rfl

theorem actualHP_top
    (h : (⊤ : Ideal (MvPolynomial σ k)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k)) : actualHP ⊤ h = 0 := by
  apply actualHP_unique _ h 0 0
  intro n _
  have hz : Module.finrank k (quotientSection (⊤ : Ideal (MvPolynomial σ k)) n) = 0 :=
    Module.finrank_eq_zero_of_subsingleton k _
  simp only [hz, Nat.cast_zero, Polynomial.eval_zero]

theorem actualHP_leadingCoeff_nonneg (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    0 ≤ (actualHP I hI).leadingCoeff := by
  obtain ⟨N, hN⟩ := actualHP_eventually I hI
  apply W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg _ (N + 1)
  intro n hn
  rw [← hN n (by omega)]
  positivity

theorem actualHP_natDegree_antitone {I J : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (hIJ : I ≤ J) :
    (actualHP J hJ).natDegree ≤ (actualHP I hI).natDegree := by
  by_cases hz : actualHP J hJ = 0
  · simp only [hz, Polynomial.natDegree_zero, Nat.zero_le]
  have hpos : 0 < (actualHP J hJ).leadingCoeff :=
    lt_of_le_of_ne (actualHP_leadingCoeff_nonneg J hJ)
      (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hz))
  obtain ⟨NI, hNI⟩ := actualHP_eventually I hI
  obtain ⟨NJ, hNJ⟩ := actualHP_eventually J hJ
  apply W24.natDegree_le_of_eventual_polynomial_le _ _ hpos (NI + NJ + 1)
  intro n hn
  rw [← hNI n (by omega), ← hNJ n (by omega)]
  have hdim := (quotientSectionFactor I J hIJ n).finrank_range_le
  rw [LinearMap.range_eq_top.mpr (quotientSectionFactor_surjective I J hIJ n),
    finrank_top] at hdim
  exact_mod_cast hdim

theorem actualHP_colon_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hJ : (Ideal.span {f} ⊔ I).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hP : (I.colon {f}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    actualHP I hI = actualHP (Ideal.span {f} ⊔ I) hJ +
      shiftHilbertPolynomial (actualHP (I.colon {f}) hP) d := by
  obtain ⟨NJ, hNJ⟩ := actualHP_eventually (Ideal.span {f} ⊔ I) hJ
  obtain ⟨NP, hNP⟩ := actualHP_eventually (I.colon {f}) hP
  apply actualHP_unique I hI _ (NJ + NP + d)
  exact colon_hilbert_polynomial_eventually I hI f hf _ _ NJ NP hNJ hNP

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_HilbertMultiplicityFiltration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem actualMultiplicity_congr {I J : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (h : I = J) (d : ℕ) :
    actualMultiplicity I hI d = actualMultiplicity J hJ d := by
  unfold actualMultiplicity
  rw [actualHP_congr hI hJ h]

theorem actualMultiplicity_nonneg (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (d : ℕ)
    (hd : (actualHP I hI).natDegree ≤ d) : 0 ≤ actualMultiplicity I hI d := by
  obtain ⟨N, hN⟩ := actualHP_eventually I hI
  exact W27.quotient_eventual_hilbert_coefficient_nonneg I (actualHP I hI) (N+1) d
    (fun n hn => (hN n (by omega)).symm) hd

theorem actualMultiplicity_top
    (h : (⊤ : Ideal (MvPolynomial σ k)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k)) (d : ℕ) :
    actualMultiplicity ⊤ h d = 0 := by
  simp only [actualMultiplicity, actualHP_top h, Polynomial.coeff_zero, zero_mul]

theorem actualMultiplicity_cyclic_step
    (I J : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {s : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous s)
    (hstep : J = I ⊔ Ideal.span {f})
    (hP : (I.colon {f}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (d : ℕ) (hd : (actualHP (I.colon {f}) hP).natDegree ≤ d) :
    actualMultiplicity I hI d =
      actualMultiplicity J hJ d + actualMultiplicity (I.colon {f}) hP d := by
  have hJs : (Ideal.span {f} ⊔ I).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) := by
    simpa only [hstep, sup_comm] using hJ
  have heq : Ideal.span {f} ⊔ I = J := (sup_comm _ _).trans hstep.symm
  unfold actualMultiplicity
  rw [actualHP_colon_step I hI f hf hJs hP, Polynomial.coeff_add,
    shiftHilbertPolynomial_top_coeff _ _ d hd, add_mul,
    actualHP_congr hJs hJ heq]

theorem rational_filtration_telescope (U V : ℕ → ℚ) :
    ∀ n : ℕ, (∀ i < n, U i = U (i+1) + V i) →
      U 0 = (∑ i ∈ Finset.range n, V i) + U n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hs
    have hprev := ih (fun i hi => hs i (Nat.lt_succ_of_lt hi))
    rw [hprev, hs n (Nat.lt_succ_self n), Finset.sum_range_succ]
    ring

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

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ComponentMultiplicitySum
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

theorem distinct_selected_factor_weight_le
    {τ β : Type*} [Fintype τ] (Q : τ → β) (hQinj : Function.Injective Q)
    (P : β) (W : τ → ℚ) (V : ℚ) (hV : 0 ≤ V)
    (hmatch : ∀ a, P = Q a → W a = V) :
    (∑ a, if P = Q a then W a else 0) ≤ V := by
  classical
  by_cases hex : ∃ a, P = Q a
  · obtain ⟨a, ha⟩ := hex
    have hsum : (∑ b, if P = Q b then W b else 0) = W a := by
      rw [Finset.sum_eq_single a]
      · simp only [ite_eq_left ha]
      · intro b _ hba
        have hb : P ≠ Q b := by
          intro hb
          exact hba (hQinj (hb.symm.trans ha))
        exact ite_eq_right hb
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ a))
    rw [hsum, hmatch a ha]
  · have hzero : (∑ a, if P = Q a then W a else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact ite_eq_right (fun ha => hex ⟨a, ha⟩)
    rw [hzero]
    exact hV

theorem grouped_count_weighted_sum_eq
    {τ β : Type*} [Fintype τ] (n : ℕ) (P : ℕ → β) (Q : τ → β) (W : τ → ℚ) :
    (∑ a, ((∑ i ∈ Finset.range n, if P i = Q a then 1 else 0 : ℕ) : ℚ) * W a) =
      ∑ i ∈ Finset.range n, ∑ a, if P i = Q a then W a else 0 := by
  classical
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  exact Finset.sum_comm

variable {k σ τ : Type*} [Field k] [Fintype σ] [Fintype τ]

theorem component_multiplicity_sum_bound_q68_oai
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (Q : τ → Ideal (MvPolynomial σ k)) [∀ a, (Q a).IsPrime]
    (hQinj : Function.Injective Q)
    (hQhom : ∀ a, (Q a).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : ∀ a, Q a ∈ I.minimalPrimes)
    (v : τ → σ) (hv : ∀ a, MvPolynomial.X (v a) ∉ Q a)
    (hdegree : ∀ a, (actualHP (Q a) (hQhom a)).natDegree = (actualHP I hI).natDegree) :
    ∃ m : τ → ℕ,
      (∀ a, Module.length (Localization.AtPrime (Q a))
        (Localization.AtPrime (Q a) ⧸ I.map
          (algebraMap (MvPolynomial σ k) (Localization.AtPrime (Q a)))) = m a) ∧
      (∀ a, 1 ≤ actualMultiplicity (Q a) (hQhom a) (actualHP I hI).natDegree) ∧
      (∑ a, (m a : ℚ) * actualMultiplicity (Q a) (hQhom a)
        (actualHP I hI).natDegree) ≤ actualMultiplicity I hI (actualHP I hI).natDegree := by
  classical
  obtain ⟨n, J, f, degrees, hmono, hstart, hend, hdata⟩ :=
    exists_homogeneous_cyclic_filtration_nat I hI
  let D := (actualHP I hI).natDegree
  have hJ : ∀ i, (J i).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
    intro i
    by_cases hi : i < n
    · exact (hdata i hi).1
    · have heq : J i = ⊤ := by
        apply top_unique
        rw [← hend]
        exact (monotone_nat_of_le_succ hmono) (Nat.le_of_not_gt hi)
      rw [heq]
      exact Ideal.IsHomogeneous.top (MvPolynomial.homogeneousSubmodule σ k)
  have hIle : ∀ i, I ≤ J i := fun i =>
    hstart.symm.le.trans ((monotone_nat_of_le_succ hmono) (Nat.zero_le i))
  let P : Fin n → Ideal (MvPolynomial σ k) := fun i => (J i).colon {f i}
  have hP : ∀ i : Fin n, (P i).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) :=
    fun i => homogeneous_colon_singleton (J i) (hJ i) (hdata i i.isLt).2.1
  have hIP : ∀ i : Fin n, I ≤ P i := fun i =>
    (hIle i).trans (ideal_le_colon_singleton (J i) (f i))
  have hPdeg : ∀ i : Fin n, (actualHP (P i) (hP i)).natDegree ≤ D :=
    fun i => actualHP_natDegree_antitone hI (hP i) (hIP i)
  let U : ℕ → ℚ := fun i => actualMultiplicity (J i) (hJ i) D
  let V : ℕ → ℚ := fun i =>
    if hi : i < n then actualMultiplicity (P ⟨i, hi⟩) (hP ⟨i, hi⟩) D else 0
  have hUstep : ∀ i < n, U i = U (i+1) + V i := by
    intro i hi
    simp only [U, V, dite_eq_left hi]
    exact actualMultiplicity_cyclic_step (J i) (J (i+1)) (hJ i) (hJ (i+1))
      (f i) (hdata i hi).2.1 (hdata i hi).2.2.2.2 (hP ⟨i, hi⟩) D (hPdeg ⟨i, hi⟩)
  have hUzero : U 0 = actualMultiplicity I hI D :=
    actualMultiplicity_congr (hJ 0) hI hstart D
  have hUend : U n = 0 := by
    have htop := Ideal.IsHomogeneous.top (MvPolynomial.homogeneousSubmodule σ k)
    exact (actualMultiplicity_congr (hJ n) htop hend D).trans (actualMultiplicity_top htop D)
  have hsum : actualMultiplicity I hI D = ∑ i ∈ Finset.range n, V i := by
    have ht := rational_filtration_telescope U V n hUstep
    rw [hUzero, hUend, add_zero] at ht
    exact ht
  let m : τ → ℕ := fun a =>
    ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q a then 1 else 0
  have hm : ∀ a, Module.length (Localization.AtPrime (Q a))
      (Localization.AtPrime (Q a) ⧸ I.map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime (Q a)))) = m a := by
    intro a
    have hlength := localized_cyclic_filtration_length_q68 I (Q a) (hQ a)
      J hmono hstart n hend f
      (fun i hi => (hdata i hi).2.2.2.2) (fun i hi => (hdata i hi).2.2.2.1)
    rw [hlength]
    simp only [m, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hpositive : ∀ a, 1 ≤ actualMultiplicity (Q a) (hQhom a) D := by
    intro a
    obtain ⟨N, hN⟩ := actualHP_eventually (Q a) (hQhom a)
    exact W27.prime_eventual_hilbert_coefficient_ge_one (Q a) (v a) (hv a)
      (actualHP (Q a) (hQhom a)) (N+1) D
      (fun t ht => (hN t (by omega)).symm) (hdegree a)
  refine ⟨m, hm, hpositive, ?_⟩
  change (∑ a, (m a : ℚ) * actualMultiplicity (Q a) (hQhom a) D) ≤
    actualMultiplicity I hI D
  rw [hsum]
  have hgroup := grouped_count_weighted_sum_eq n
    (fun i => (J i).colon {f i}) Q (fun a => actualMultiplicity (Q a) (hQhom a) D)
  change (∑ a, (m a : ℚ) * actualMultiplicity (Q a) (hQhom a) D) = _ at hgroup
  rw [hgroup]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hnonneg : 0 ≤ V i := by
    simp only [V, dite_eq_left hin]
    exact actualMultiplicity_nonneg (P ⟨i, hin⟩) (hP ⟨i, hin⟩) D (hPdeg ⟨i, hin⟩)
  apply distinct_selected_factor_weight_le Q hQinj ((J i).colon {f i})
    (fun a => actualMultiplicity (Q a) (hQhom a) D) (V i) hnonneg
  intro a heq
  simp only [V, dite_eq_left hin]
  exact (actualMultiplicity_congr (hP ⟨i, hin⟩) (hQhom a) heq D).symm

end PiExponentJets.W22

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.PiExponentJets.W22.component_multiplicity_sum_bound_q68_oai.{u_1, u_2, u_3} := @OAI.PiExponentJets.W22.component_multiplicity_sum_bound_q68_oai.{u_1, u_2, u_3}
