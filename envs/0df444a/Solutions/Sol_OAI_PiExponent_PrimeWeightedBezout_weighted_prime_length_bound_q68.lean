-- Prove2me | solution 1 for OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:07:40.735209+00:00
-- url     : https://prove2.me/submissions/9c96a8e0-8e62-4d1f-b568-686006d96c6a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A026
import Theorems.Thm_OAI_PiExponent_CoordinateSliceComparison_length_eq_sliceFamily_of_normalBasis_q68
import Theorems.Thm_OAI_PiExponent_CoordinateSliceComparison_sliceFamily_mem_minimalPrimes_of_normalBasis_q68
import Theorems.Thm_OAI_PiExponent_localIsolatedBezout_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedSliceDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem supportBound_zero (ρ : σ → ℝ) (N : ℝ) :
    SupportBound ρ N (0 : MvPolynomial σ E) := by
  intro d hd
  simp at hd

theorem supportBound_C (ρ : σ → ℝ) (c : E) :
    SupportBound ρ 0 (MvPolynomial.C c) := by
  intro d hd
  have he : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp

theorem supportBound_X (ρ : σ → ℝ) (i : σ) :
    SupportBound ρ (ρ i) (MvPolynomial.X i : MvPolynomial σ E) := by
  classical
  intro d hd
  have he : d = Finsupp.single i 1 := by simpa only [MvPolynomial.support_X, Finset.mem_singleton] using hd
  subst d
  simp [Finsupp.weight_single]

theorem SupportBound.add {ρ : σ → ℝ} {N : ℝ} {p q : MvPolynomial σ E}
    (hp : SupportBound ρ N p) (hq : SupportBound ρ N q) : SupportBound ρ N (p + q) := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hp d h
  · exact hq d h

theorem SupportBound.mul {ρ : σ → ℝ} {M N : ℝ} {p q : MvPolynomial σ E}
    (hp : SupportBound ρ M p) (hq : SupportBound ρ N q) : SupportBound ρ (M + N) (p * q) := by
  classical
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  simpa only [map_add] using add_le_add (hp a ha) (hq b hb)

theorem SupportBound.pow {ρ : σ → ℝ} {N : ℝ} {p : MvPolynomial σ E}
    (hp : SupportBound ρ N p) (m : ℕ) : SupportBound ρ ((m : ℝ) * N) (p ^ m) := by
  induction m with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_mul, MvPolynomial.C_1] using supportBound_C ρ (1 : E)
  | succ m ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hp

theorem supportBound_prod {α : Type*} (s : Finset α) (ρ : σ → ℝ)
    (p : α → MvPolynomial σ E) (N : α → ℝ)
    (hp : ∀ i ∈ s, SupportBound ρ (N i) (p i)) :
    SupportBound ρ (∑ i ∈ s, N i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Finset.prod_empty, MvPolynomial.C_1] using supportBound_C ρ (1 : E)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem supportBound_sum {α : Type*} (s : Finset α) (ρ : σ → ℝ)
    (p : α → MvPolynomial σ E) (N : ℝ)
    (hp : ∀ i ∈ s, SupportBound ρ N (p i)) :
    SupportBound ρ N (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using supportBound_zero ρ N
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem supportBound_aeval_monomial (ρ : ι → ℝ) (κ : σ → ℝ)
    (g : ι → MvPolynomial σ E) (hg : ∀ i, SupportBound κ (ρ i) (g i))
    (d : ι →₀ ℕ) (c : C) :
    SupportBound κ (Finsupp.weight ρ d) (MvPolynomial.aeval g (MvPolynomial.monomial d c)) := by
  classical
  rw [MvPolynomial.aeval_monomial]
  have hC : SupportBound κ 0 (algebraMap C (MvPolynomial σ E) c) :=
    supportBound_C κ (algebraMap C E c)
  have hprod := supportBound_prod d.support κ (fun i => g i ^ d i)
    (fun i => (d i : ℝ) * ρ i) (fun i _ => (hg i).pow (d i))
  have h := hC.mul hprod
  simpa only [zero_add, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Finsupp.prod] using h

theorem supportBound_aeval (ρ : ι → ℝ) (κ : σ → ℝ)
    (g : ι → MvPolynomial σ E) (hg : ∀ i, SupportBound κ (ρ i) (g i))
    (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N) :
    SupportBound κ N (MvPolynomial.aeval g p) := by
  classical
  conv_rhs => rw [MvPolynomial.as_sum p, map_sum]
  exact supportBound_sum p.support κ _ N
    (fun d hd => (supportBound_aeval_monomial ρ κ g hg d (p.coeff d)).mono (hp d hd))

theorem supportBound_sliceMap (A : Finset ι) (b : ι → E)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N) :
    SupportBound (fun i : A => ρ i) N (sliceMap A b p) := by
  classical
  let g : ι → MvPolynomial A E := fun i =>
    if h : i ∈ A then MvPolynomial.X ⟨i, h⟩ else MvPolynomial.C (b i)
  change SupportBound (fun i : A => ρ i) N (MvPolynomial.aeval g p)
  have hg : ∀ i, SupportBound (fun j : A => ρ j) (ρ i) (g i) := by
    intro i
    dsimp only [g]
    split_ifs with hi
    · exact supportBound_X (E := E) (fun j : A => ρ j) ⟨i, hi⟩
    · exact (supportBound_C (fun j : A => ρ j) (b i)).mono (hρ i)
  exact supportBound_aeval ρ (fun i : A => ρ i) g hg N p hp

theorem supportBound_renameEquiv (e : ι ≃ σ) (ρ : ι → ℝ) (N : ℝ)
    (p : MvPolynomial ι E) (hp : SupportBound ρ N p) :
    SupportBound (fun j => ρ (e.symm j)) N (MvPolynomial.rename e p) := by
  rw [MvPolynomial.rename_eq_aeval]
  apply supportBound_aeval (C := E) ρ (fun j => ρ (e.symm j)) (MvPolynomial.X ∘ e) _ N p hp
  intro i
  simpa only [Function.comp_apply, e.symm_apply_apply] using
    supportBound_X (E := E) (fun j => ρ (e.symm j)) (e i)

theorem supportBound_enumeratedSliceMap (A : Finset ι) (b : ι → E)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N) :
    SupportBound (fun j : Fin A.card => ρ (A.equivFin.symm j)) N
      (enumeratedSliceMap A b p) :=
  supportBound_renameEquiv A.equivFin (fun i : A => ρ i) N (sliceMap A b p)
    (supportBound_sliceMap A b ρ hρ N p hp)

theorem supportBound_enumeratedSliceMap_sum (A : Finset ι) (b : ι → E)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, (∑ i ∈ d.support, (d i : ℝ) * ρ i) ≤ N) :
    ∀ d ∈ (enumeratedSliceMap A b p).support,
      (∑ j ∈ d.support, (d j : ℝ) * ρ (A.equivFin.symm j)) ≤ N := by
  have h := supportBound_enumeratedSliceMap A b ρ hρ N p (by
    simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul] using hp)
  simpa only [SupportBound, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul] using h

end PiExponent.WeightedSliceDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_WeightedBezout
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.RamifiedLocalLength.translatedPowerLocalMap_isLocalHom _root_.OAI.PiExponent.SeparablePointLength.pointLocalMap_isLocalHom _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedBezout

open scoped BigOperators

variable {k σ τ : Type*} [Field k]

theorem totalDegree_aeval_monomial_le (w : σ → ℕ) (g : σ → MvPolynomial τ k)
    (hg : ∀ i, (g i).totalDegree ≤ w i) (d : σ →₀ ℕ) (c : k) :
    (MvPolynomial.aeval g (MvPolynomial.monomial d c)).totalDegree ≤
      Finsupp.weight w d := by
  classical
  rw [MvPolynomial.aeval_monomial]
  calc
    _ ≤ (MvPolynomial.C c).totalDegree +
        (d.prod fun i e => g i ^ e).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ ∑ i ∈ d.support, d i * w i := by
      simp only [MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
      apply (MvPolynomial.totalDegree_finsetProd _ _).trans
      exact Finset.sum_le_sum (fun i hi => (MvPolynomial.totalDegree_pow (g i) (d i)).trans
        (Nat.mul_le_mul_left (d i) (hg i)))
    _ = _ := by simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]

theorem totalDegree_aeval_le_weighted (w : σ → ℕ) (g : σ → MvPolynomial τ k)
    (hg : ∀ i, (g i).totalDegree ≤ w i) (p : MvPolynomial σ k) :
    (MvPolynomial.aeval g p).totalDegree ≤ p.weightedTotalDegree w := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p, map_sum]
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro d hd
  exact (totalDegree_aeval_monomial_le w g hg d (p.coeff d)).trans
    (MvPolynomial.le_weightedTotalDegree w hd)

theorem translatedPowerSubstitution_totalDegree (w : σ → ℕ) (a : σ → k)
    (p : MvPolynomial σ k) :
    (translatedPowerSubstitution w a p).totalDegree ≤ p.weightedTotalDegree w := by
  apply totalDegree_aeval_le_weighted
  intro i
  exact (MvPolynomial.totalDegree_add _ _).trans (by simp)

theorem prime_over_pointIdeal_eq_origin (w : σ → ℕ) (a : σ → k)
    (Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hQ : pointIdeal a ≤ Q.comap (translatedPowerSubstitution w a).toRingHom) :
    Q = pointIdeal (0 : σ → k) := by
  have hle : pointIdeal (0 : σ → k) ≤ Q := by
    rw [pointIdeal_eq_span]
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    have hi : MvPolynomial.X i - MvPolynomial.C (a i) ∈ pointIdeal a := by simp
    have hp := hQ hi
    change translatedPowerSubstitution w a (MvPolynomial.X i - MvPolynomial.C (a i)) ∈ Q at hp
    have hpow : MvPolynomial.X i ^ w i ∈ Q := by
      simpa only [map_sub, translatedPowerSubstitution_X, translatedPowerSubstitution_C,
        add_sub_cancel_left] using hp
    change MvPolynomial.X i - MvPolynomial.C (0 : k) ∈ Q
    rw [MvPolynomial.C_0, sub_zero]
    exact (inferInstance : Q.IsPrime).mem_of_pow_mem (w i) hpow
  exact ((inferInstance : (pointIdeal (0 : σ → k)).IsMaximal).eq_of_le
    (inferInstance : Q.IsPrime).ne_top hle).symm

theorem translatedPowerSubstitution_totalDegree_real (w : σ → ℕ) (a : σ → k)
    (ρ : σ → ℝ) (M N : ℝ) (hM : 0 ≤ M) (hMN : 0 ≤ M * N)
    (hw : ∀ i, (w i : ℝ) = M * ρ i) (p : MvPolynomial σ k)
    (hp : ∀ d ∈ p.support, (∑ i ∈ d.support, (d i : ℝ) * ρ i) ≤ N) :
    ((translatedPowerSubstitution w a p).totalDegree : ℝ) ≤ M * N := by
  have hb : p.weightedTotalDegree w ≤ ⌊M * N⌋₊ := by
    apply Finset.sup_le
    intro d hd
    apply (Nat.le_floor_iff hMN).mpr
    calc
      (Finsupp.weight w d : ℝ) = M * ∑ i ∈ d.support, (d i : ℝ) * ρ i := by
        rw [Finsupp.weight_apply]
        simp only [Finsupp.sum, smul_eq_mul, Nat.cast_sum, Nat.cast_mul]
        simp_rw [hw]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ M * N := mul_le_mul_of_nonneg_left (hp d hd) hM
  have hd := (translatedPowerSubstitution_totalDegree w a p).trans hb
  exact (Nat.cast_le.mpr hd).trans (Nat.floor_le hMN)

theorem origin_minimalPrimes_map (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) (I : Ideal (MvPolynomial σ k))
    (hI : pointIdeal a ∈ I.minimalPrimes) :
    pointIdeal (0 : σ → k) ∈
      (I.map (translatedPowerSubstitution w a).toRingHom).minimalPrimes := by
  let φ := (translatedPowerSubstitution w a).toRingHom
  have hc : (pointIdeal (0 : σ → k)).comap φ = pointIdeal a :=
    translatedPowerSubstitution_comap_origin w a hw
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    rw [hc]
    exact hI.1.2
  · intro Q hQ hQle
    let : Q.IsPrime := hQ.1
    have hIQ : I ≤ Q.comap φ := Ideal.map_le_iff_le_comap.mp hQ.2
    have hQP : Q.comap φ ≤ pointIdeal a := by
      rw [← hc]
      exact Ideal.comap_mono hQle
    have hPQ : pointIdeal a ≤ Q.comap φ := hI.2 ⟨inferInstance, hIQ⟩ hQP
    have heq := prime_over_pointIdeal_eq_origin w a Q hPQ
    exact heq.symm.le

end PiExponent.WeightedBezout

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialMaximalHeight
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W09

variable (K : Type*) [Field K]

theorem polynomialMaximal_height (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal] :
    m.height = (n : ℕ∞) := by
  induction n with
  | zero =>
      let e := MvPolynomial.isEmptyAlgEquiv K (Fin 0)
      let p : Ideal K := m.comap e.symm.toRingHom
      let : p.IsMaximal := Ideal.comap_isMaximal_of_equiv e.symm
      have hp : p = ⊥ := p.eq_bot_or_top.resolve_right (Ideal.IsMaximal.ne_top (inferInstance : p.IsMaximal))
      calc
        m.height = p.height := (e.symm.toRingEquiv.height_comap m).symm
        _ = (0 : ℕ∞) := by rw [hp, Ideal.height_bot]
  | succ n ih =>
      let e := MvPolynomial.finSuccEquiv K n
      let P : Ideal (Polynomial (MvPolynomial (Fin n) K)) :=
        m.comap e.symm.toRingHom
      let : P.IsMaximal := Ideal.comap_isMaximal_of_equiv e.symm
      let p : Ideal (MvPolynomial (Fin n) K) := P.comap Polynomial.C
      let : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
      let : P.LiesOver p := ⟨rfl⟩
      calc
        m.height = P.height := (e.symm.toRingEquiv.height_comap m).symm
        _ = p.height + 1 := Polynomial.height_eq_height_add_one p P
        _ = ((n + 1 : ℕ) : ℕ∞) := by rw [ih p]; simp

end PiExponentSiegelAux.W09

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RamifiedLocalLength
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open IsLocalRing TensorProduct

namespace PiExponent.RamifiedLocalLength

theorem residueField_map_surjective_of_mod_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsMaximal]
    (f : R →+* S) (hPQ : P = Q.comap f)
    (hs : ∀ y : S, ∃ x : R, y - f x ∈ Q) :
    Function.Surjective (Ideal.ResidueField.map P Q f hPQ) := by
  intro z
  obtain ⟨y, rfl⟩ := Q.algebraMap_residueField_surjective z
  obtain ⟨x, hx⟩ := hs y
  refine ⟨algebraMap R P.ResidueField x, ?_⟩
  rw [Ideal.ResidueField.map_algebraMap]
  have hz := (Ideal.algebraMap_residueField_eq_zero (I := Q)).mpr hx
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

variable {A B : Type*} [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [Module.Free A B] [Module.Finite A B]

theorem closed_fibre_length_eq_finrank
    (hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField B))) :
    Module.length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) =
      (Module.finrank A B : ℕ∞) := by
  let I : Ideal B := (maximalIdeal A).map (algebraMap A B)
  have hreslen : Module.length (ResidueField A) (ResidueField B) = 1 := by
    rw [Module.length_eq_of_surjective hres]
    exact Module.length_eq_one _ _
  have hrestrict := IsLocalRing.length_restrictScalars A B (B ⧸ I)
  rw [hreslen, mul_one] at hrestrict
  rw [← hrestrict]
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  let : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ I) :=
    Module.Finite.of_restrictScalars_finite A _ _
  calc
    Module.length A (B ⧸ I) = Module.length (A ⧸ maximalIdeal A) (B ⧸ I) :=
      Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
    _ = (Module.finrank (A ⧸ maximalIdeal A) (B ⧸ I) : ℕ∞) :=
      Module.length_eq_finrank _ _
    _ = (Module.finrank A B : ℕ∞) := by
      rw [IsLocalRing.finrank_quotient_map]

theorem length_baseChange_eq_finrank_mul
    (hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField B)))
    (M : Type*) [AddCommGroup M] [Module A M] :
    Module.length B (B ⊗[A] M) =
      Module.length A M * (Module.finrank A B : ℕ∞) := by
  rw [IsLocalRing.length_baseChange, closed_fibre_length_eq_finrank hres]

theorem length_quotient_map_eq_finrank_mul
    (hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField B)))
    (I : Ideal A) :
    Module.length B (B ⧸ I.map (algebraMap A B)) =
      Module.length A (A ⧸ I) * (Module.finrank A B : ℕ∞) := by
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq]
  exact length_baseChange_eq_finrank_mul hres (A ⧸ I)

end PiExponent.RamifiedLocalLength

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RamifiedPointMap
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.SeparablePointLength.pointLocalMap_isLocalHom _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.RamifiedLocalLength

open IsLocalRing WeightedBezout

variable {k σ : Type*} [Field k]

theorem translatedPowerLocalResidue_surjective (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    Function.Surjective (IsLocalRing.ResidueField.map
      (translatedPowerLocalMap w a hw).toRingHom) := by
  apply residueField_map_surjective_of_mod_surjective
    (pointIdeal a) (pointIdeal (0 : σ → k))
    (translatedPowerSubstitution w a).toRingHom
    (translatedPowerSubstitution_comap_origin w a hw).symm
  intro p
  refine ⟨MvPolynomial.C (MvPolynomial.aeval (0 : σ → k) p), ?_⟩
  simp [mem_pointIdeal]

theorem translatedPowerLocalMap_ideal_map (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) (I : Ideal (MvPolynomial σ k)) :
    (I.map (algebraMap _ (Localization.AtPrime (pointIdeal a)))).map
        (translatedPowerLocalMap w a hw).toRingHom =
      (I.map (translatedPowerSubstitution w a).toRingHom).map
        (algebraMap _ (Localization.AtPrime (pointIdeal (0 : σ → k)))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  exact translatedPowerLocalMap_algebraMap w a hw p

end PiExponent.RamifiedLocalLength

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RamifiedPowerLength
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.SeparablePointLength.pointLocalMap_isLocalHom _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.RamifiedLocalLength

open WeightedBezout
open scoped BigOperators

noncomputable section

variable {σ k : Type*} [Fintype σ] [Field k]

theorem translatedPowerLocal_finrank (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    letI := translatedPowerLocalAlgebra w a hw
    Module.finrank (Localization.AtPrime (pointIdeal a))
      (Localization.AtPrime (pointIdeal (0 : σ → k))) = ∏ i, w i := by
  classical
  let := translatedPowerLocalAlgebra w a hw
  rw [Module.finrank_eq_card_basis (translatedPowerLocalBasis w a hw)]
  simp [Fintype.card_pi]

theorem translatedPowerLocal_quotient_length (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) (I : Ideal (MvPolynomial σ k)) :
    Module.length (Localization.AtPrime (pointIdeal (0 : σ → k)))
      (Localization.AtPrime (pointIdeal (0 : σ → k)) ⧸
        (I.map (translatedPowerSubstitution w a).toRingHom).map
          (algebraMap _ (Localization.AtPrime (pointIdeal (0 : σ → k))))) =
    Module.length (Localization.AtPrime (pointIdeal a))
      (Localization.AtPrime (pointIdeal a) ⧸
        I.map (algebraMap _ (Localization.AtPrime (pointIdeal a)))) *
      ((∏ i, w i : ℕ) : ℕ∞) := by
  classical
  let A := Localization.AtPrime (pointIdeal a)
  let B := Localization.AtPrime (pointIdeal (0 : σ → k))
  let := translatedPowerLocalAlgebra w a hw
  let : IsLocalHom (algebraMap A B) := translatedPowerLocalMap_isLocalHom w a hw
  let : Module.Free A B := Module.Free.of_basis (translatedPowerLocalBasis w a hw)
  let : Module.Finite A B := Module.Finite.of_basis (translatedPowerLocalBasis w a hw)
  have hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)) := translatedPowerLocalResidue_surjective w a hw
  have h := length_quotient_map_eq_finrank_mul hres (I.map (algebraMap _ A))
  rw [translatedPowerLocal_finrank w a hw] at h
  change Module.length B (B ⧸ (I.map (algebraMap _ A)).map
    (translatedPowerLocalMap w a hw).toRingHom) = _ at h
  rw [translatedPowerLocalMap_ideal_map] at h
  exact h

end
end PiExponent.RamifiedLocalLength

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_WeightedBezoutBound
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.SeparablePointLength.pointLocalMap_isLocalHom _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace PiExponent.WeightedBezout

theorem finite_length_of_rank_bound {L : ℕ∞} {r B : ℕ}
    (hr : 0 < r) (h : L * (r : ℕ∞) ≤ (B : ℕ∞)) :
    ∃ l : ℕ, L = (l : ℕ∞) ∧ l * r ≤ B := by
  have hfin : L ≠ ⊤ := by
    intro ht
    have hr0 : (r : ℕ∞) ≠ 0 := by exact_mod_cast hr.ne'
    rw [ht, ENat.top_mul hr0] at h
    exact (ENat.natCast_ne_top B) (top_le_iff.mp h)
  refine ⟨L.toNat, (ENat.natCast_toNat hfin).symm, ?_⟩
  have hn : ((L.toNat * r : ℕ) : ℕ∞) ≤ B := by
    simpa only [Nat.cast_mul, ENat.natCast_toNat hfin] using h
  exact_mod_cast hn

theorem weighted_bound_of_scaled_natural {n M L B : ℕ}
    (ρ : Fin n → ℝ) (w : Fin n → ℕ) (N : ℝ)
    (hM : 0 < M) (hρ : ∀ i, 0 < ρ i)
    (hw : ∀ i, (w i : ℝ) = (M : ℝ) * ρ i)
    (hbound : L * ∏ i, w i ≤ B ^ n)
    (hdegree : (B : ℝ) ≤ (M : ℝ) * N) :
    (L : ℝ) ≤ N ^ n / ∏ i, ρ i := by
  have hp : 0 < ∏ i, ρ i := Finset.prod_pos (fun i _ => hρ i)
  have hscale : 0 < (M : ℝ) ^ n := pow_pos (by exact_mod_cast hM) _
  have hprod : (∏ i, (w i : ℝ)) = (M : ℝ) ^ n * ∏ i, ρ i := by
    simp_rw [hw]
    rw [Finset.prod_mul_distrib]
    simp
  apply (le_div_iff₀ hp).mpr
  apply (mul_le_mul_iff_right₀ hscale).mp
  calc
    (M : ℝ) ^ n * ((L : ℝ) * ∏ i, ρ i) = (L : ℝ) * ∏ i, (w i : ℝ) := by
      rw [hprod]
      ring
    _ ≤ (B : ℝ) ^ n := by exact_mod_cast hbound
    _ ≤ ((M : ℝ) * N) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg B) hdegree n
    _ = (M : ℝ) ^ n * N ^ n := by rw [mul_pow]

theorem pointLength_mul_le_of_substituted_degree
    (k : Type) [Field k] [Infinite k] {n : ℕ} {J : Type*}
    (f : J → MvPolynomial (Fin n) k) (a : Fin n → k)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (D : ℕ)
    (hdegree : ∀ j, (translatedPowerSubstitution w a (f j)).totalDegree ≤ D)
    (hminimal : pointIdeal a ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    pointLength a (Ideal.span (Set.range f)) * (∏ i, w i : ℕ) ≤ (D ^ n : ℕ) := by
  let I := Ideal.span (Set.range f)
  let g : J → MvPolynomial (Fin n) k := fun j => translatedPowerSubstitution w a (f j)
  have hmap : I.map (translatedPowerSubstitution w a).toRingHom =
      Ideal.span (Set.range g) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hminimal0 := origin_minimalPrimes_map w a hw I hminimal
  rw [hmap] at hminimal0
  have hheight := PiExponentSiegelAux.W09.polynomialMaximal_height k n
    (pointIdeal (0 : Fin n → k))
  have hb := PiExponent.localIsolatedBezout_q68 k n g D n hdegree
    (pointIdeal (0 : Fin n → k)) hminimal0 hheight le_rfl
  rw [← hmap] at hb
  rw [RamifiedLocalLength.translatedPowerLocal_quotient_length w a hw I] at hb
  exact hb

theorem rational_pointLength_bound
    (k : Type) [Field k] [Infinite k] {n : ℕ} {J : Type*}
    (f : J → MvPolynomial (Fin n) k) (a : Fin n → k)
    (ρ : Fin n → ℚ) (hρ : ∀ i, 0 < ρ i) (N : ℝ) (hN : 0 ≤ N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (ρ i : ℝ)) ≤ N)
    (hminimal : pointIdeal a ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    ∃ L : ℕ, pointLength a (Ideal.span (Set.range f)) = (L : ℕ∞) ∧
      (L : ℝ) ≤ N ^ n / ∏ i, (ρ i : ℝ) := by
  classical
  obtain ⟨M, hM, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hscale : ∀ i, (w i : ℝ) = (M : ℝ) * (ρ i : ℝ) := by
    intro i
    rw [hweights i]
    field_simp
  have hMN : 0 ≤ (M : ℝ) * N := mul_nonneg hMreal.le hN
  let D : ℕ := ⌊(M : ℝ) * N⌋₊
  have hD : ∀ j, (translatedPowerSubstitution w a (f j)).totalDegree ≤ D := by
    intro j
    apply (Nat.le_floor_iff hMN).mpr
    exact translatedPowerSubstitution_totalDegree_real w a
      (fun i => (ρ i : ℝ)) M N hMreal.le hMN hscale (f j) (hdegree j)
  have hbound := pointLength_mul_le_of_substituted_degree k f a w hw D hD hminimal
  have hprod : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  obtain ⟨L, hL, hLbound⟩ := finite_length_of_rank_bound hprod hbound
  refine ⟨L, hL, ?_⟩
  exact weighted_bound_of_scaled_natural (fun i => (ρ i : ℝ)) w N hM
    (fun i => by exact_mod_cast hρ i) hscale hLbound (Nat.floor_le hMN)

end PiExponent.WeightedBezout

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeWeightedBezout
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PrimeWeightedBezout

open scoped BigOperators
open CoordinateFiniteSlice CoordinateSliceComparison NormalBasisRigidity WeightedSliceDegree

theorem weighted_prime_length_bound_q68_oai {n : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime]
    (A : Finset (Fin n))
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    {J : Type*} (f : J → MvPolynomial (Fin n) ℂ)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (N : ℝ) (hN : 0 ≤ N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N) :
    ∃ L : ℕ, primeLength Q (Ideal.span (Set.range f)) = L ∧
      (L : ℝ) ≤ N ^ A.card / ∏ i ∈ A, (rho i : ℝ) := by
  let : Infinite Q.ResidueField := Infinite.of_injective
    (algebraMap ℂ Q.ResidueField) (algebraMap ℂ Q.ResidueField).injective
  have hminimal := sliceFamily_mem_minimalPrimes_of_normalBasis_q68 Q A hA f hQ
  have hlength := length_eq_sliceFamily_of_normalBasis_q68 Q A hA f
  have hrhoR (i : Fin n) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have hsliceDegree : ∀ j, ∀ d ∈
      (enumeratedSliceMap A (residueCoordinates Q) (f j)).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho (A.equivFin.symm i) : ℝ)) ≤ N := by
    intro j
    exact supportBound_enumeratedSliceMap_sum A (residueCoordinates Q)
      (fun i => (rho i : ℝ)) (fun i => (hrhoR i).le) N (f j) (hdegree j)
  obtain ⟨L, hL, hupper⟩ := WeightedBezout.rational_pointLength_bound
    Q.ResidueField (fun j => enumeratedSliceMap A (residueCoordinates Q) (f j))
    (slicePoint Q A) (fun i => rho (A.equivFin.symm i)) (fun i => hrho _) N hN
    hsliceDegree hminimal
  refine ⟨L, hlength.trans hL, ?_⟩
  have hp : (∏ i : Fin A.card, (rho (A.equivFin.symm i) : ℝ)) =
      ∏ i ∈ A, (rho i : ℝ) := by
    calc
      _ = ∏ i : A, (rho i : ℝ) :=
        Fintype.prod_equiv A.equivFin.symm _ _ (fun _ => rfl)
      _ = _ := Finset.prod_coe_sort A (fun i => (rho i : ℝ))
  simpa only [hp] using hupper

end PiExponent.PrimeWeightedBezout
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound_q68_oai.{u_1} := @OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound_q68_oai.{u_1}
