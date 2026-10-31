-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_all_short_smooth_cubic_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:01:02.579528+00:00
-- url     : https://prove2.me/submissions/d3071c4b-81ad-42ae-b34f-9d6b6592c6d5

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A022
import Theorems.Thm_OAI_CubicFirstMoment_bounded_cubic_moment
import Theorems.Thm_OAI_CubicFirstMoment_gramDualTerm_dyad_rapidDecay

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein lattice counts and arbitrarily small divisor losses. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_finset_prod {α : Type*} (s : Finset α) (f : α → Eisenstein) :
    norm (∏ p ∈ s, f p) = ∏ p ∈ s, norm (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih => simp [hp, ih]

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primeDivisorWeight_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Eisenstein, primary a → Squarefree a →
      (2 : ℝ)^(primaryPrimeFactors a).card ≤ C * norm a ^ ε := by
  let R : ℝ := (2 : ℝ)^(1/ε)
  let U : Finset Eisenstein := (finite_norm_le R).toFinset
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  have hRe : R^ε = 2 := by
    dsimp [R]
    rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hε.ne', Real.rpow_one]
  refine ⟨(2 : ℝ)^U.card, by positivity, ?_⟩
  intro a ha hsa
  let P := primaryPrimeFactors a
  have hpoint : ∀ p ∈ P, (2 : ℝ) ≤ (if p ∈ U then 2 else 1) * norm p ^ ε := by
    intro p hp
    have hn1 := one_le_norm (primaryPrimeFactor_spec ha hp).1.2.ne_zero
    by_cases hpU : p ∈ U
    · simp only [ite_eq_left hpU]
      nlinarith [Real.one_le_rpow hn1 hε.le]
    · simp only [ite_eq_right hpU, one_mul]
      have hRp : R ≤ norm p := le_of_lt (not_le.mp (by
        intro he
        exact hpU (by simpa [U] using he)))
      rw [← hRe]
      exact Real.rpow_le_rpow hR.le hRp hε.le
  have hprod := Finset.prod_le_prod (s := P) (fun _ _ => (by norm_num : (0 : ℝ) ≤ 2)) hpoint
  rw [Finset.prod_const, Finset.prod_mul_distrib] at hprod
  have hsmall : (∏ p ∈ P, if p ∈ U then (2 : ℝ) else 1) ≤ (2 : ℝ)^U.card := by
    rw [Finset.prod_ite_mem, Finset.prod_const]
    exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (Finset.inter_subset_right))
  have heq : (∏ p ∈ P, norm p ^ ε) = norm a ^ ε := by
    rw [Real.finsetProd_rpow P norm (fun p _ => norm_nonneg p), ← norm_finset_prod]
    rw [primaryPrimeFactors_prod ha hsa]
  rw [heq] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (norm_nonneg a) _))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_FrequencyGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime, squarefree and mixed frequency Gauss evaluation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mixedFrequencyGauss_zero {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hne : a ≠ b) : mixedFrequencyGauss a b 0 = 0 := by
  rw [mixedFrequencyGauss_squarefree ha hb hsa hsb hab]
  by_cases ha1 : a = 1
  · have hb1 : b ≠ 1 := fun hb1 => hne (ha1.trans hb1.symm)
    have hnc : ¬ IsCoprime b 0 := fun hc =>
      hb1 (primary_unit_eq_one (isCoprime_zero_right.mp hc) hb)
    rw [cubicSymbol_eq_zero_of_not_isCoprime hb hnc]
    simp
  · have hnc : ¬ IsCoprime a 0 := fun hc =>
      ha1 (primary_unit_eq_one (isCoprime_zero_right.mp hc) ha)
    rw [cubicSymbol_eq_zero_of_not_isCoprime ha hnc]
    simp

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MixedPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primary mixed characters and squarefree coset Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma traceFourier_affine (f : 𝓢(ℂ, ℂ)) (z q : ℂ) (hq : q ≠ 0) (w : ℂ) :
    traceFourier (fun x => f (z + q * x)) w =
      (Complex.normSq q)⁻¹ • ((Real.fourierChar (tracePair z (w/q)) : ℂ) *
        traceFourier f (w/q)) := by
  simpa only [traceFourier_translation] using
    (traceFourier_complexMul q hq (fun y => f (z+y)) w)

theorem poisson_eisenstein_periodic_coset (c : Eisenstein) (hc : c ≠ 0)
    (ψ : Residues c → ℂ) (f : 𝓢(ℂ, ℂ)) (z q : ℂ) (hq : q ≠ 0) :
    ∑' a : Eisenstein, ψ (Ideal.Quotient.mk (modulus c) a) * f (z+q*(a : ℂ)) =
      (2 / (Real.sqrt 3 * norm c * Complex.normSq q) : ℝ) • ∑' h : Eisenstein,
        (∑' v : Residues c, ψ v *
          (Real.fourierChar (tracePair (residueRepresentative c v : ℂ)
            ((h : ℂ) / ((c : ℂ) * traceLambda))) : ℂ)) *
        (Real.fourierChar (tracePair z ((h : ℂ) / (q*(c : ℂ)*traceLambda))) : ℂ) *
        traceFourier f ((h : ℂ) / (q*(c : ℂ)*traceLambda)) := by
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexMulEquiv q hq)
    (f.compSubConstCLM ℂ (-z))
  have hg : (g : ℂ → ℂ) = (fun x => f (z+q*x)) := by
    funext x
    simp [g, add_comm]
  have he := poisson_eisenstein_periodic c hc ψ g
  rw [hg] at he
  simp_rw [traceFourier_affine f z q hq] at he
  have hfreq (h : Eisenstein) : ((h : ℂ) / ((c : ℂ)*traceLambda)) / q =
      (h : ℂ) / (q*(c : ℂ)*traceLambda) := by ring
  simp_rw [hfreq, mul_smul_comm, ← mul_assoc] at he
  rw [tsum_const_smul'', smul_smul] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end CubicFirstMoment

namespace CubicFirstMoment

theorem poisson_primary_mixed_squarefree {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (f : 𝓢(ℂ, ℂ)) :
    ∑' s : Eisenstein, mixedSymbol a b (a*b+3*s) * f ((a*b+3*s : Eisenstein) : ℂ) =
      (2 / (Real.sqrt 3 * norm (a*b) * 9) : ℝ) • ∑' h : Eisenstein,
        ((Real.sqrt (norm (a*b)) : ℂ) * (gauss a * star (gauss b)) *
          (star (cubicSymbol a h) * cubicSymbol b h)) *
        (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ) *
        traceFourier f ((h : ℂ) / (3*((a*b : Eisenstein) : ℂ)*traceLambda)) := by
  have hc0 := primary_ne_zero (primary_mul ha hb)
  have hc0' : ((a*b : Eisenstein) : ℂ) ≠ 0 := fun h => hc0 (Subtype.ext h)
  let ψ (v : Residues (a*b)) := mixedSymbol a b (3*residueRepresentative (a*b) v)
  have hψ (s : Eisenstein) : ψ (Ideal.Quotient.mk (modulus (a*b)) s) =
      mixedSymbol a b (a*b+3*s) := by
    apply mixedSymbol_congr
    simp only [map_mul, map_add, residueRepresentative_spec]
    have hz : Ideal.Quotient.mk (modulus (a*b)) (a*b) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton (a*b)))
    rw [map_mul] at hz
    rw [hz, zero_add]
  have hphase (h : Eisenstein) : tracePair ((a*b : Eisenstein) : ℂ)
      ((h : ℂ) / (3*((a*b : Eisenstein) : ℂ)*traceLambda)) =
      tracePair (h : ℂ) (1 / (3*traceLambda)) := by
    unfold tracePair
    congr 2
    field_simp
  have hfin (h : Eisenstein) : (∑' v : Residues (a*b), ψ v *
      (Real.fourierChar (tracePair (residueRepresentative (a*b) v : ℂ)
        ((h : ℂ) / (((a*b : Eisenstein) : ℂ)*traceLambda))) : ℂ)) =
      (Real.sqrt (norm (a*b)) : ℂ) * (gauss a * star (gauss b)) *
        (star (cubicSymbol a h) * cubicSymbol b h) :=
    primaryMixedFourier_squarefree ha hb hsa hsb hab h
  have he := poisson_eisenstein_periodic_coset (a*b) hc0 ψ f
    ((a*b : Eisenstein) : ℂ) 3 (by norm_num)
  simp_rw [hψ, hfin, hphase] at he
  have h3 : ((3 : Eisenstein) : ℂ) = 3 := rfl
  norm_num [Subalgebra.coe_add, Subalgebra.coe_mul, Complex.normSq_ofNat, h3] at he ⊢
  exact he

end CubicFirstMoment
end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GramPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal character Gram kernel and normalized radial Poisson expansion. -/

section

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

noncomputable section
open Filter
open scoped ContDiff

namespace CubicFirstMoment

lemma primaryCosetMap_bijective (c : Eisenstein) (hc : primary c) :
    Function.Bijective (primaryCosetMap c hc) := by
  constructor
  · intro s t hst
    have he : c+3*s=c+3*t := congrArg Subtype.val hst
    have hn : (3 : Eisenstein) ≠ 0 := by norm_num
    exact mul_left_cancel₀ hn (add_left_cancel he)
  · intro n
    obtain ⟨u, hu⟩ := n.property
    obtain ⟨v, hv⟩ := hc
    refine ⟨u-v, Subtype.ext ?_⟩
    change c+3*(u-v) = n.val
    linear_combination hv - hu

lemma tsum_primary_eq_coset (c : Eisenstein) (hc : primary c) (F : Eisenstein → ℂ) :
    (∑' n : Eisenstein, if primary n then F n else 0) =
      ∑' s : Eisenstein, F (c+3*s) := by
  have he := (Equiv.ofBijective (primaryCosetMap c hc)
    (primaryCosetMap_bijective c hc)).tsum_eq (fun n => F n.val)
  change (∑' n : Eisenstein, Set.indicator {n | primary n} F n) = _
  rw [← tsum_subtype]
  exact he.symm

end CubicFirstMoment

namespace CubicFirstMoment

lemma traceFourier_normProfile (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 0 < Z) (w : ℂ) :
    traceFourier (normProfileSchwartz W hW hW' Z hZ) w =
      Z • traceFourier (fun z : ℂ => W (Complex.normSq z)) ((Real.sqrt Z : ℂ)*w) := by
  have hs : Real.sqrt Z ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hZ)
  have hs' : (Real.sqrt Z : ℂ) ≠ 0 := by exact_mod_cast hs
  have hn : Complex.normSq ((Real.sqrt Z : ℂ)⁻¹) = Z⁻¹ := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal, Real.mul_self_sqrt (le_of_lt hZ)]
  have hf : (normProfileSchwartz W hW hW' Z hZ : ℂ → ℂ) =
      fun z : ℂ => W (Complex.normSq ((Real.sqrt Z : ℂ)⁻¹*z)) := by
    funext z
    simp only [normProfileSchwartz_apply, Complex.normSq_mul, hn]
    congr 1
    ring
  rw [hf, traceFourier_complexMul _ (inv_ne_zero hs')
    (fun z => W (Complex.normSq z)) w, hn, inv_inv]
  congr 2
  simp only [div_inv_eq_mul, mul_comm]

theorem primaryCharacterGram_poisson {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 0 < Z) :
    primaryCharacterGram a b W Z =
      (2 / (Real.sqrt 3 * norm (a*b) * 9) : ℝ) • ∑' h : Eisenstein,
        ((Real.sqrt (norm (a*b)) : ℂ) * (gauss a * star (gauss b)) *
          (star (cubicSymbol a h) * cubicSymbol b h)) *
        (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ) *
        (Z • traceFourier (fun z : ℂ => W (Complex.normSq z))
          ((Real.sqrt Z : ℂ) * ((h : ℂ) / (3*((a*b : Eisenstein) : ℂ)*traceLambda)))) := by
  unfold primaryCharacterGram
  rw [tsum_primary_eq_coset (a*b) (primary_mul ha hb)
    (fun n => W (norm n / Z) * cubicSymbol a n * star (cubicSymbol b n))]
  have he := poisson_primary_mixed_squarefree ha hb hsa hsb hab
    (normProfileSchwartz W hW hW' Z hZ)
  simp_rw [traceFourier_normProfile W hW hW' hZ] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply tsum_congr
  intro s
  simp only [normProfileSchwartz_apply, mixedSymbol, norm]
  ring

end CubicFirstMoment

namespace CubicFirstMoment

lemma norm_gramGauss_scalar {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b) :
    ‖gauss a * star (gauss b)‖ = 1 := by
  rw [norm_mul, norm_star, norm_gauss_of_squarefree ha hsa,
    norm_gauss_of_squarefree hb hsb, one_mul]

lemma gramDualTerm_zero {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hne : a ≠ b) (W : ℝ → ℂ) (Z : ℝ) :
    gramDualTerm a b W Z 0 = 0 := by
  have hz := mixedFrequencyGauss_zero ha hb hsa hsb hab hne
  rw [mixedFrequencyGauss_squarefree ha hb hsa hsb hab] at hz
  have hg : gauss a * star (gauss b) ≠ 0 := by
    intro h
    have hn := norm_gramGauss_scalar ha hb hsa hsb
    rw [h, norm_zero] at hn
    norm_num at hn
  have hχ := (mul_eq_zero.mp hz).resolve_left hg
  simp only [gramDualTerm, hχ, zero_mul]

theorem primaryCharacterGram_poisson_normalized {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 0 < Z) :
    primaryCharacterGram a b W Z =
      ((Z / (9*Real.sqrt (norm (a*b))) : ℝ) : ℂ) * (gauss a * star (gauss b)) *
        ∑' h : Eisenstein, gramDualTerm a b W Z h := by
  have hN : 0 < norm (a*b) := Complex.normSq_pos.mpr
    (fun h => primary_ne_zero (primary_mul ha hb) (Subtype.ext h))
  have hsqrt : Real.sqrt (norm (a*b)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have hc : (2 / (Real.sqrt 3 * norm (a*b) * 9)) * Real.sqrt (norm (a*b)) * Z =
      (Z / (9*Real.sqrt (norm (a*b)))) * (2 / Real.sqrt 3) := by
    nth_rw 1 [← Real.sq_sqrt (le_of_lt hN)]
    field_simp
  have hc' := congrArg (fun x : ℝ => (x : ℂ)) hc
  push_cast at hc'
  rw [primaryCharacterGram_poisson ha hb hsa hsb hab W hW hW' hZ]
  simp only [Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro h
  simp only [gramDualTerm, normProfileFourier, Complex.real_smul]
  push_cast
  linear_combination (gauss a * star (gauss b) *
    (star (cubicSymbol a h) * cubicSymbol b h) *
    (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ) *
    traceFourier (fun z : ℂ => W (Complex.normSq z))
      ((Real.sqrt Z : ℂ) * ((h : ℂ) / (3*((a*b : Eisenstein) : ℂ)*traceLambda)))) * hc'

theorem norm_primaryCharacterGram_poisson {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 0 < Z) :
    ‖primaryCharacterGram a b W Z‖ =
      (Z / (9*Real.sqrt (norm (a*b)))) *
        ‖∑' h : Eisenstein, gramDualTerm a b W Z h‖ := by
  rw [primaryCharacterGram_poisson_normalized ha hb hsa hsb hab W hW hW' hZ,
    norm_mul, norm_mul, norm_gramGauss_scalar ha hb hsa hsb, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ideal Moebius weights and exact prime-factor subset identities. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma idealMoebius_sq (b : Eisenstein) :
    (idealMoebius b : ℝ)^2 = if Squarefree b then 1 else 0 := by
  unfold idealMoebius UniqueFactorizationMonoid.moebius
  split_ifs <;> push_cast
  · rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  · norm_num

lemma idealMoebius_mul {a b : Eisenstein} (h : IsCoprime a b) :
    idealMoebius (a*b) = idealMoebius a * idealMoebius b :=
  (isRelPrime_iff_isCoprime.mpr h).moebius_mul

lemma idealMoebius_primaryPrime {p : Eisenstein} (hp : primaryPrime p) :
    idealMoebius p = -1 := hp.2.irreducible.moebius_eq

lemma idealMoebius_prod_primaryPrimes (s : Finset Eisenstein)
    (hp : ∀ p ∈ s, primaryPrime p) :
    idealMoebius (∏ p ∈ s, p) = (-1 : ℤ)^s.card := by
  induction s using Finset.induction_on with
  | empty => simp [idealMoebius]
  | @insert p s hps ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hc : IsCoprime p (∏ q ∈ s, q) := by
      apply IsCoprime.prod_right
      intro q hq
      exact primaryPrimes_isCoprime hp' (hs q hq) (fun h => hps (h ▸ hq))
    rw [Finset.prod_insert hps, idealMoebius_mul hc, idealMoebius_primaryPrime hp',
      ih hs, Finset.card_insert_of_notMem hps, pow_succ]
    ring

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CommonFactors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moebius removal of common factors and coprime Gram decomposition. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mixedSymbol_remove_common {k a b : Eisenstein} (hk : primary k)
    (ha : primary a) (hb : primary b) (n : Eisenstein) :
    mixedSymbol (k*a) (k*b) n =
      if IsCoprime k n then mixedSymbol a b n else 0 := by
  rw [mixedSymbol, cubicSymbol_mul_lower (primary_ne_zero hk) (primary_ne_zero ha),
    cubicSymbol_mul_lower (primary_ne_zero hk) (primary_ne_zero hb), star_mul]
  by_cases hc : IsCoprime k n
  · rw [ite_eq_left hc]
    have hu : cubicSymbol k n * star (cubicSymbol k n) = 1 := by
      change cubicSymbol k n * starRingEnd ℂ (cubicSymbol k n) = 1
      rw [Complex.mul_conj', norm_cubicSymbol_of_isCoprime hk hc]
      norm_num
    simp only [mixedSymbol]
    linear_combination (cubicSymbol a n * star (cubicSymbol b n)) * hu
  · rw [ite_eq_right hc, cubicSymbol_eq_zero_of_not_isCoprime hk hc]
    simp

lemma primary_subsets_prod_dvd {k : Eisenstein} (hk : primary k)
    {s : Finset Eisenstein} (hs : s ⊆ primaryPrimeFactors k) (n : Eisenstein) :
    (∏ p ∈ s, p) ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  constructor
  · intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp) h
  · intro h
    apply Finset.prod_dvd_of_coprime _ h
    intro p hp q hq hpq
    exact primaryPrimes_isCoprime (primaryPrimeFactor_spec hk (hs hp)).1
      (primaryPrimeFactor_spec hk (hs hq)).1 hpq

theorem primary_moebius_coprimality {k : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) (n : Eisenstein) :
    (if IsCoprime k n then (1 : ℂ) else 0) =
      ∑ s ∈ (primaryPrimeFactors k).powerset,
        (idealMoebius (∏ p ∈ s, p) : ℂ) *
          (if (∏ p ∈ s, p) ∣ n then 1 else 0) := by
  let P := primaryPrimeFactors k
  have hprod : (∏ p ∈ P, (1 - (if p ∣ n then (1 : ℂ) else 0))) =
      if IsCoprime k n then 1 else 0 := by
    by_cases h : IsCoprime k n
    · rw [ite_eq_left h]
      apply Finset.prod_eq_one
      intro p hp
      have hpn : ¬p ∣ n := by
        intro hd
        exact (primaryPrimeFactor_spec hk hp).1.2.not_isUnit
          (h.isUnit_of_dvd' (primaryPrimeFactor_spec hk hp).2 hd)
      simp [hpn]
    · rw [ite_eq_right h]
      have hex : ∃ p ∈ P, p ∣ n := by
        by_contra hn
        have hall : ∀ p ∈ P, IsCoprime p n := by
          intro p hp
          exact ((primaryPrimeFactor_spec hk hp).1.2.irreducible.coprime_iff_not_dvd).mpr
            (fun hd => hn ⟨p, hp, hd⟩)
        have := IsCoprime.prod_left hall
        rw [primaryPrimeFactors_prod hk hsk] at this
        exact h this
      obtain ⟨p, hp, hpn⟩ := hex
      apply Finset.prod_eq_zero hp
      simp [hpn]
  rw [← hprod]
  have hex := Finset.prod_add (fun p : Eisenstein => -(if p ∣ n then (1 : ℂ) else 0))
    (fun _ => (1 : ℂ)) P
  simp only [Finset.prod_const_one, mul_one, ← sub_eq_neg_add] at hex
  rw [hex]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub : s ⊆ primaryPrimeFactors k := Finset.mem_powerset.mp hs
  rw [idealMoebius_prod_primaryPrimes s
    (fun p hp => (primaryPrimeFactor_spec hk (hsub hp)).1), Finset.prod_neg]
  push_cast
  congr 1
  by_cases h : (∏ p ∈ s, p) ∣ n
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro p hp
    simp [(primary_subsets_prod_dvd hk hsub n).mp h p hp]
  · rw [ite_eq_right h]
    have hex : ∃ p ∈ s, ¬p ∣ n := by
      by_contra hn
      apply h
      apply (primary_subsets_prod_dvd hk hsub n).mpr
      intro p hp
      by_contra hpn
      exact hn ⟨p, hp, hpn⟩
    obtain ⟨p, hp, hpn⟩ := hex
    exact Finset.prod_eq_zero hp (by simp [hpn])

end CubicFirstMoment

namespace CubicFirstMoment

lemma summable_gram_restricted {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) (S : Eisenstein → Prop) :
    Summable (fun n : Eisenstein => if primary n ∧ S n then
      W (norm n / Z) * cubicSymbol a n * star (cubicSymbol b n) else 0) := by
  apply Summable.of_norm_bounded
    (schwartz_summable_eisenstein (normProfileSchwartz W hW hW' Z hZ)).norm
  intro n
  change ‖ite _ _ _‖ ≤ ‖W (norm n / Z)‖
  split_ifs with hn
  · rw [norm_mul, norm_mul, norm_star]
    calc
      _ ≤ ‖W (norm n / Z)‖ * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (norm_cubicSymbol_le_one ha n)
          (_root_.norm_nonneg _)) (norm_cubicSymbol_le_one hb n)
            (_root_.norm_nonneg _) (by positivity)
      _ = _ := by ring
  · simp

lemma multiplesMap_bijective {m : Eisenstein} (hm : m ≠ 0) :
    Function.Bijective (multiplesMap m) := by
  constructor
  · intro x y h
    exact mul_left_cancel₀ hm (congrArg Subtype.val h)
  · intro n
    obtain ⟨x, hx⟩ := n.property
    exact ⟨x, Subtype.ext hx.symm⟩

lemma tsum_dvd_eq_multiples {m : Eisenstein} (hm : m ≠ 0) (F : Eisenstein → ℂ) :
    (∑' n : Eisenstein, if m ∣ n then F n else 0) =
      ∑' x : Eisenstein, F (m*x) := by
  have he := (Equiv.ofBijective (multiplesMap m) (multiplesMap_bijective hm)).tsum_eq
    (fun n => F n.val)
  change (∑' n : Eisenstein, Set.indicator {n | m ∣ n} F n) = _
  rw [← tsum_subtype]
  exact he.symm

lemma tsum_primary_dvd_eq_multiples {m : Eisenstein} (hm : primary m)
    (F : Eisenstein → ℂ) :
    (∑' n : Eisenstein, if primary n ∧ m ∣ n then F n else 0) =
      ∑' x : Eisenstein, if primary x then F (m*x) else 0 := by
  have he := tsum_dvd_eq_multiples (primary_ne_zero hm)
    (fun n => if primary n then F n else 0)
  convert he using 1
  · apply tsum_congr
    intro n
    by_cases hn : primary n <;> by_cases hd : m ∣ n <;> simp [hn, hd]
  · apply tsum_congr
    intro n
    have hp : primary (m*n) ↔ primary n := ⟨primary_of_mul hm, primary_mul hm⟩
    simp only [hp]

theorem primaryCharacterGram_divisor_scale {a b m : Eisenstein} (ha : primary a)
    (hb : primary b) (hm : primary m) (W : ℝ → ℂ) (Z : ℝ) :
    (∑' n : Eisenstein, if primary n ∧ m ∣ n then
      W (norm n / Z) * cubicSymbol a n * star (cubicSymbol b n) else 0) =
      mixedSymbol a b m * primaryCharacterGram a b W (Z / norm m) := by
  rw [tsum_primary_dvd_eq_multiples hm
    (fun n => W (norm n / Z) * cubicSymbol a n * star (cubicSymbol b n))]
  unfold primaryCharacterGram
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : primary n
  · have hnorm : norm (m*n) = norm m * norm n := Complex.normSq_mul _ _
    simp only [ite_eq_left hn, hnorm, div_div_eq_mul_div, cubicSymbol_mul_upper ha,
      cubicSymbol_mul_upper hb, star_mul, mixedSymbol]
    rw [show norm m * norm n / Z = norm n * norm m / Z by ring]
    ring
  · simp only [ite_eq_right hn, mul_zero]

theorem primaryCharacterGram_common_factor {k a b : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) :
    primaryCharacterGram (k*a) (k*b) W Z =
      ∑ s ∈ (primaryPrimeFactors k).powerset,
        (idealMoebius (∏ p ∈ s, p) : ℂ) *
          mixedSymbol a b (∏ p ∈ s, p) *
            primaryCharacterGram a b W (Z / norm (∏ p ∈ s, p)) := by
  let P := (primaryPrimeFactors k).powerset
  let T (s : Finset Eisenstein) (n : Eisenstein) : ℂ :=
    (idealMoebius (∏ p ∈ s, p) : ℂ) *
      (if primary n ∧ (∏ p ∈ s, p) ∣ n then
        W (norm n / Z) * cubicSymbol a n * star (cubicSymbol b n) else 0)
  have hsumm (s : Finset Eisenstein) : Summable (T s) :=
    (summable_gram_restricted ha hb W hW hW' hZ (fun n => (∏ p ∈ s, p) ∣ n)).mul_left _
  have hpoint (n : Eisenstein) :
      (if primary n then W (norm n / Z) * cubicSymbol (k*a) n *
        star (cubicSymbol (k*b) n) else 0) = ∑ s ∈ P, T s n := by
    by_cases hn : primary n
    · simp only [ite_eq_left hn]
      rw [mul_assoc]
      change W (norm n / Z) * mixedSymbol (k*a) (k*b) n = _
      rw [mixedSymbol_remove_common hk ha hb]
      have he := primary_moebius_coprimality hk hsk n
      have hmul := congrArg (fun z : ℂ => z *
        (W (norm n / Z) * mixedSymbol a b n)) he
      simp only [Finset.sum_mul] at hmul
      convert hmul using 1
      · split_ifs <;> ring
      · apply Finset.sum_congr rfl
        intro s hs
        simp only [T, hn, true_and, mixedSymbol]
        split_ifs <;> ring
    · simp only [T, hn, false_and, ite_false, if_false, mul_zero, Finset.sum_const_zero]
  change (∑' n : Eisenstein, if primary n then _ else 0) = _
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun s _ => hsumm s)]
  apply Finset.sum_congr rfl
  intro s hs
  change (∑' n, (idealMoebius (∏ p ∈ s, p) : ℂ) * _) = _
  rw [tsum_mul_left]
  have hm : primary (∏ p ∈ s, p) := primary_finset_prod _ _
    (fun p hp => (primaryPrimeFactor_spec hk (Finset.mem_powerset.mp hs hp)).1.1)
  rw [primaryCharacterGram_divisor_scale ha hb hm]
  ring

end CubicFirstMoment

namespace CubicFirstMoment

theorem primarySquarefree_common_decomposition {p q : Eisenstein}
    (hp : primary p) (hq : primary q) (hsp : Squarefree p) (hsq : Squarefree q) :
    ∃ k a b : Eisenstein, primary k ∧ primary a ∧ primary b ∧
      Squarefree k ∧ Squarefree a ∧ Squarefree b ∧
      IsCoprime a b ∧ IsCoprime k a ∧ IsCoprime k b ∧ p = k*a ∧ q = k*b := by
  let P := primaryPrimeFactors p
  let Q := primaryPrimeFactors q
  let k := ∏ r ∈ P ∩ Q, r
  let a := ∏ r ∈ P \ Q, r
  let b := ∏ r ∈ Q \ P, r
  have hk : primary k := primary_finset_prod _ _
    (fun r hr => (primaryPrimeFactor_spec hp (Finset.mem_inter.mp hr).1).1.1)
  have ha : primary a := primary_finset_prod _ _
    (fun r hr => (primaryPrimeFactor_spec hp (Finset.mem_sdiff.mp hr).1).1.1)
  have hb : primary b := primary_finset_prod _ _
    (fun r hr => (primaryPrimeFactor_spec hq (Finset.mem_sdiff.mp hr).1).1.1)
  have hep : k*a = p :=
    (Finset.prod_inter_mul_prod_sdiff P Q (fun r : Eisenstein => r)).trans
      (primaryPrimeFactors_prod hp hsp)
  have heq : k*b = q := by
    change (∏ r ∈ P ∩ Q, r) * (∏ r ∈ Q \ P, r) = q
    rw [Finset.inter_comm P Q]
    exact (Finset.prod_inter_mul_prod_sdiff Q P (fun r : Eisenstein => r)).trans
      (primaryPrimeFactors_prod hq hsq)
  have hab : IsCoprime a b := by
    apply IsCoprime.prod_left
    intro r hr
    apply IsCoprime.prod_right
    intro s hs
    apply primaryPrimes_isCoprime (primaryPrimeFactor_spec hp (Finset.mem_sdiff.mp hr).1).1
      (primaryPrimeFactor_spec hq (Finset.mem_sdiff.mp hs).1).1
    intro he
    exact (Finset.mem_sdiff.mp hr).2 (he ▸ (Finset.mem_sdiff.mp hs).1)
  have hka : IsCoprime k a := by
    apply IsCoprime.prod_left
    intro r hr
    apply IsCoprime.prod_right
    intro s hs
    apply primaryPrimes_isCoprime (primaryPrimeFactor_spec hp (Finset.mem_inter.mp hr).1).1
      (primaryPrimeFactor_spec hp (Finset.mem_sdiff.mp hs).1).1
    intro he
    exact (Finset.mem_sdiff.mp hs).2 (he ▸ (Finset.mem_inter.mp hr).2)
  have hkb : IsCoprime k b := by
    apply IsCoprime.prod_left
    intro r hr
    apply IsCoprime.prod_right
    intro s hs
    apply primaryPrimes_isCoprime (primaryPrimeFactor_spec hp (Finset.mem_inter.mp hr).1).1
      (primaryPrimeFactor_spec hq (Finset.mem_sdiff.mp hs).1).1
    intro he
    exact (Finset.mem_sdiff.mp hs).2 (he ▸ (Finset.mem_inter.mp hr).1)
  exact ⟨k, a, b, hk, ha, hb,
    Squarefree.squarefree_of_dvd (hep ▸ dvd_mul_right k a) hsp, Squarefree.squarefree_of_dvd (hep ▸ dvd_mul_left a k) hsp,
    Squarefree.squarefree_of_dvd (heq ▸ dvd_mul_left b k) hsq, hab, hka, hkb, hep.symm, heq.symm⟩

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic sieve operators, bilinear norms and coprime completion. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

open UniqueFactorizationMonoid

namespace CubicFirstMoment

lemma norm_idealMoebius_le_one (m : Eisenstein) : ‖(idealMoebius m : ℂ)‖ ≤ 1 := by
  have hs : (idealMoebius m : ℝ)^2 ≤ 1 := by
    rw [idealMoebius_sq]
    split_ifs <;> norm_num
  have hn : ‖(idealMoebius m : ℂ)‖ = |(idealMoebius m : ℝ)| :=
    Complex.norm_intCast _
  rw [hn]
  nlinarith [sq_abs (idealMoebius m : ℝ), abs_nonneg (idealMoebius m : ℝ)]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frequency dyads and summable base Gram recurrences. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_frequencyDyad {j : ℕ} {h : Eisenstein} :
    h ∈ frequencyDyad j ↔ h ≠ 0 ∧ Nat.log 2 (normNat h) = j := by
  simp only [frequencyDyad, Finset.mem_filter, mem_nonzeroNormBall]
  refine ⟨fun h => ⟨h.1.2,h.2⟩,fun hh => ⟨⟨?_,hh.1⟩,hh.2⟩⟩
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at ht
  rw [← normNat_cast]
  exact_mod_cast ht.le

lemma summable_gramDualTerm {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) : Summable (gramDualTerm a b W Z) := by
  let q : ℂ := (Real.sqrt Z : ℂ)/(3*((a*b : Eisenstein) : ℂ)*traceLambda)
  have hq : q ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hZ)
    · exact mul_ne_zero (mul_ne_zero (by norm_num)
        (fun hz => mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb) (Subtype.ext hz)))
        traceLambda_ne_zero
  have hs := (schwartz_summable_eisenstein_coset
    (normProfileFourierSchwartz W hW hW') q hq 0).norm
  apply Summable.of_norm_bounded hs
  intro h
  rw [zero_add,normProfileFourierSchwartz_apply]
  dsimp only [q]
  have he : ((Real.sqrt Z : ℂ)/(3*((a*b : Eisenstein) : ℂ)*traceLambda))*(h : ℂ) =
      (Real.sqrt Z : ℂ)*((h : ℂ)/(3*((a*b : Eisenstein) : ℂ)*traceLambda)) := by ring
  rw [he]
  simp only [gramDualTerm,norm_mul,norm_star,Circle.norm_coe,mul_one]
  apply mul_le_of_le_one_left (_root_.norm_nonneg _)
  exact (mul_le_mul (norm_cubicSymbol_le_one ha h) (norm_cubicSymbol_le_one hb h)
    (_root_.norm_nonneg _) (by norm_num)).trans (by norm_num)

lemma hasSum_frequencyDyad (F : Eisenstein → ℂ) (hF : Summable F) (h0 : F 0 = 0) :
    HasSum (fun j : ℕ => ∑ h ∈ frequencyDyad j, F h) (∑' h : Eisenstein, F h) := by
  have he := hF.hasSum.tsum_fiberwise (fun h : Eisenstein => Nat.log 2 (normNat h))
  have hf (j : ℕ) : (∑' h : ((fun h : Eisenstein => Nat.log 2 (normNat h)) ⁻¹' {j}), F h) =
      ∑ h ∈ frequencyDyad j, F h := by
    rw [tsum_subtype]
    calc
      _ = ∑ h ∈ frequencyDyad j,
          Set.indicator ((fun h : Eisenstein => Nat.log 2 (normNat h)) ⁻¹' {j}) F h := by
        apply tsum_eq_sum
        intro h hh
        by_cases hz : h = 0
        · subst h; simp [h0]
        · have hj : Nat.log 2 (normNat h) ≠ j := fun hj => hh (mem_frequencyDyad.mpr ⟨hz,hj⟩)
          simp [hj]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h hh
        have hm : h ∈ ((fun h : Eisenstein => Nat.log 2 (normNat h)) ⁻¹' {j}) :=
          (mem_frequencyDyad.mp hh).2
        exact Set.indicator_of_mem hm F

  simpa only [hf] using he

end CubicFirstMoment

namespace CubicFirstMoment

lemma dyadic_decay_step {c : ℝ} (hc : 0 < c) (j : ℕ) :
    (2 : ℝ)^j / (1+c*2^j)^2 ≤
      (2/c)*(1/(1+c*2^j)-1/(1+c*2^(j+1))) := by
  have hJ : 0 < (2 : ℝ)^j := by positivity
  have h1 : 0 < 1+c*2^j := by positivity
  have h2 : 0 < 1+2*c*2^j := by positivity
  calc
    _ ≤ 2*2^j / ((1+c*2^j)*(1+2*c*2^j)) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos h1) (mul_pos h1 h2)).mpr
      nlinarith [sq_nonneg (c*2^j),sq_nonneg ((2 : ℝ)^j), mul_pos hc hJ]
    _ = _ := by
      rw [pow_succ]
      have h2' : 1+c*((2 : ℝ)^j*2) ≠ 0 := by positivity
      field_simp
      ring

lemma dyadic_decay_partial_sum {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (∑ j ∈ Finset.range n, (2 : ℝ)^j/(1+c*2^j)^2) ≤ 2/c := by
  have h := Finset.sum_le_sum (s := Finset.range n) (fun j _ => dyadic_decay_step hc j)
  rw [← Finset.mul_sum] at h
  have ht : (∑ j ∈ Finset.range n, (1/(1+c*2^j)-1/(1+c*2^(j+1)))) =
      1/(1+c) - 1/(1+c*2^n) := by
    have hh := Finset.sum_range_sub (fun j => (1 : ℝ)/(1+c*2^j)) n
    rw [Finset.sum_sub_distrib] at hh ⊢
    simp only [pow_zero,mul_one] at hh
    linarith
  rw [ht] at h
  have hc0 : 0 ≤ 2/c := by positivity
  have hfirst : 1/(1+c) ≤ (1 : ℝ) := (div_le_one (by positivity)).mpr (by linarith)
  have hlast : (0 : ℝ) ≤ 1/(1+c*2^n) := by positivity
  exact h.trans ((mul_le_mul_of_nonneg_left (by linarith : 1/(1+c)-1/(1+c*2^n) ≤ 1) hc0).trans_eq (mul_one _))

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CommonRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact common-factor row reindexing and matrix decomposition. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_residualRows {S : Finset Eisenstein} {k a : Eisenstein} (hk : k ≠ 0) :
    a ∈ residualRows S k ↔ k*a ∈ S := by
  simp [residualRows,hk]

lemma primaryPrimeFactors_coprime_overlap {k a b : Eisenstein}
    (hk : primary k) (ha : primary a) (hb : primary b) (hab : IsCoprime a b) :
    primaryPrimeFactors (k*a) ∩ primaryPrimeFactors (k*b) = primaryPrimeFactors k := by
  ext p
  rw [Finset.mem_inter, primaryPrime_mem_factors_iff (primary_mul hk ha),
    primaryPrime_mem_factors_iff (primary_mul hk hb), primaryPrime_mem_factors_iff hk]
  constructor
  · rintro ⟨⟨hp,hpa⟩,⟨_,hpb⟩⟩
    refine ⟨hp,?_⟩
    rcases hp.2.dvd_mul.mp hpa with hd | hd
    · exact hd
    rcases hp.2.dvd_mul.mp hpb with hd' | hd'
    · exact hd'
    exact (hp.2.not_isUnit (hab.isUnit_of_dvd' hd hd')).elim
  · rintro ⟨hp,hd⟩
    exact ⟨⟨hp,hd.trans (dvd_mul_right k a)⟩,⟨hp,hd.trans (dvd_mul_right k b)⟩⟩

lemma primaryCommonFactor_mul {k a b : Eisenstein}
    (hk : primary k) (hsk : Squarefree k) (ha : primary a) (hb : primary b)
    (hab : IsCoprime a b) : primaryCommonFactor (k*a) (k*b) = k := by
  unfold primaryCommonFactor
  rw [primaryPrimeFactors_coprime_overlap hk ha hb hab,primaryPrimeFactors_prod hk hsk]

lemma primaryCommonFactor_decomposition {p q : Eisenstein}
    (hp : primary p) (hq : primary q) (hsp : Squarefree p) (hsq : Squarefree q) :
    ∃ a b : Eisenstein, primary a ∧ primary b ∧ Squarefree a ∧ Squarefree b ∧
      IsCoprime a b ∧ p = primaryCommonFactor p q*a ∧ q = primaryCommonFactor p q*b := by
  obtain ⟨k,a,b,hk,ha,hb,hsk,hsa,hsb,hab,_,_,hpa,hqb⟩ :=
    primarySquarefree_common_decomposition hp hq hsp hsq
  have he : primaryCommonFactor p q = k := hpa ▸ hqb ▸ primaryCommonFactor_mul hk hsk ha hb hab
  exact ⟨a,b,ha,hb,hsa,hsb,hab,by simpa [he] using hpa,by simpa [he] using hqb⟩

lemma primaryCommonFactor_spec {p q : Eisenstein}
    (hp : primary p) (hq : primary q) (hsp : Squarefree p) (hsq : Squarefree q) :
    primary (primaryCommonFactor p q) ∧ Squarefree (primaryCommonFactor p q) ∧
      primaryCommonFactor p q ∣ p ∧ primaryCommonFactor p q ∣ q := by
  obtain ⟨k,a,b,hk,ha,hb,hsk,hsa,hsb,hab,_,_,hpa,hqb⟩ :=
    primarySquarefree_common_decomposition hp hq hsp hsq
  have he : primaryCommonFactor p q = k := hpa ▸ hqb ▸ primaryCommonFactor_mul hk hsk ha hb hab
  rw [he,hpa,hqb]
  exact ⟨hk,hsk,dvd_mul_right k a,dvd_mul_right k b⟩

lemma commonFactor_eq_iff_coprime {k a b : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) (ha : primary a) (hb : primary b)
    (hsa : Squarefree (k*a)) (hsb : Squarefree (k*b)) :
    primaryCommonFactor (k*a) (k*b) = k ↔ IsCoprime a b := by
  constructor
  · intro he
    obtain ⟨a',b',_,_,_,_,hab,hpa,hqb⟩ := primaryCommonFactor_decomposition
      (primary_mul hk ha) (primary_mul hk hb) hsa hsb
    rw [he] at hpa hqb
    have hea := mul_left_cancel₀ (primary_ne_zero hk) hpa
    have heb := mul_left_cancel₀ (primary_ne_zero hk) hqb
    simpa only [← hea,← heb] using hab
  · exact primaryCommonFactor_mul hk hsk ha hb

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact sieve majorants and common-factor energy bounds. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryCharacterGram_one_one_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : Continuous W) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 0 < Z → ‖primaryCharacterGram 1 1 W Z‖ ≤ C*Z := by
  obtain ⟨R,hR,hR0⟩ := hW.exists_pos_le_norm
  obtain ⟨L,hL⟩ := hW'.bounded_above_of_compact_support hW
  let K := max L 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hLK : L ≤ K := le_max_left _ _
  refine ⟨18*R*K,by positivity,?_⟩
  intro Z hZ
  have hs : primaryCharacterGram 1 1 W Z =
      ∑ n ∈ nonzeroNormBall (R*Z), if primary n then
        W (norm n/Z)*cubicSymbol 1 n*star (cubicSymbol 1 n) else 0 := by
    apply tsum_eq_sum
    intro n hn
    split_ifs with hp
    · have hn' : R*Z < norm n := lt_of_not_ge (fun h =>
        hn (mem_nonzeroNormBall.mpr ⟨h,primary_ne_zero hp⟩))
      have hw : W (norm n/Z) = 0 := hR0 _ (by
        rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) (le_of_lt hZ))]
        exact (le_div_iff₀ hZ).mpr hn'.le)
      simp [hw]
    · rfl
  rw [hs]
  calc
    _ ≤ ∑ n ∈ nonzeroNormBall (R*Z),
        ‖if primary n then W (norm n/Z)*cubicSymbol 1 n*star (cubicSymbol 1 n) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ nonzeroNormBall (R*Z), K := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs with hp
      · rw [norm_mul,norm_mul,norm_star]
        calc
          _ ≤ ‖W (norm n/Z)‖*1*1 := by
            gcongr <;> exact norm_cubicSymbol_le_one primary_one n
          _ ≤ K := by simpa using (hL (norm n/Z)).trans hLK
      · simpa using hK.le
    _ = (nonzeroNormBall (R*Z)).card*K := by simp
    _ ≤ (18*(R*Z))*K := mul_le_mul_of_nonneg_right (nonzeroNormBall_card_le (by positivity)) hK.le
    _ = _ := by ring

lemma cubicSieveCutoff_compact : HasCompactSupport cubicSieveCutoff :=
  gramLogBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

lemma cubicSieveCutoff_smooth : ContDiff ℝ ∞ cubicSieveCutoff :=
  Complex.ofRealCLM.contDiff.comp gramLogBump.contDiff

lemma cubicSieveCutoff_zero {t : ℝ} (ht : 2 ≤ |t|) : cubicSieveCutoff t = 0 := by
  have h := gramLogBump.zero_of_le_dist (x := t)
  have he : gramLogBump t = 0 := h (by
    simpa only [Real.dist_eq,sub_zero,gramLogBump] using ht)
  simp [cubicSieveCutoff,he]

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrimeFactors_subset_of_dvd {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hab : a ∣ b) : primaryPrimeFactors a ⊆ primaryPrimeFactors b := by
  intro p hp
  obtain ⟨hpp,hpa⟩ := primaryPrimeFactor_spec ha hp
  exact primaryPrime_mem_factors hb hpp (hpa.trans hab)

lemma primary_divisors_card_le (T : Finset Eisenstein)
    (hT : ∀ k ∈ T, primary k ∧ Squarefree k) {p : Eisenstein} (hp : primary p) :
    ((T.filter (· ∣ p)).card : ℝ) ≤ (2 : ℝ)^(primaryPrimeFactors p).card := by
  have hmaps : ∀ k ∈ T.filter (· ∣ p), primaryPrimeFactors k ∈ (primaryPrimeFactors p).powerset := by
    intro k hk
    rw [Finset.mem_filter] at hk
    exact Finset.mem_powerset.mpr (primaryPrimeFactors_subset_of_dvd (hT k hk.1).1 hp hk.2)
  have hinj : Set.InjOn primaryPrimeFactors (↑(T.filter (· ∣ p)) : Set Eisenstein) := by
    intro k hk l hl he
    have hk' := hT k (Finset.mem_filter.mp hk).1
    have hl' := hT l (Finset.mem_filter.mp hl).1
    rw [← primaryPrimeFactors_prod hk'.1 hk'.2,← primaryPrimeFactors_prod hl'.1 hl'.2,he]
  have hc := (Finset.card_image_iff.mpr hinj).symm.le.trans
    (Finset.card_le_card (Finset.image_subset_iff.mpr hmaps))
  rw [Finset.card_powerset] at hc
  exact_mod_cast hc

lemma residualRows_sum_image (S : Finset Eisenstein) {k : Eisenstein} (hk : k ≠ 0)
    (f : Eisenstein → ℝ) :
    (∑ a ∈ residualRows S k, f (k*a)) = ∑ p ∈ S, if k ∣ p then f p else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun a _ => k*a)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨(mem_residualRows hk).mp ha, dvd_mul_right _ _⟩
  · intro a ha b hb hab
    exact mul_left_cancel₀ hk hab
  · intro p hp
    obtain ⟨a,rfl⟩ := (Finset.mem_filter.mp hp).2
    exact ⟨a,(mem_residualRows hk).mpr (Finset.mem_filter.mp hp).1,rfl⟩
  · intro a ha
    rfl

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ramified residual factors and full cube decomposition. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_le_of_dvd {a b : Eisenstein} (hb : b ≠ 0) (hd : a ∣ b) :
    norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := hd
  have hc : c ≠ 0 := by intro h; simp [h] at hb
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg a) (one_le_norm hc)

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeEstimates
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric decay, cube frequency dyads and numerical block inequalities. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma geometric_decay_step {q d : ℝ} (hq : 1 < q) (hd : 0 < d) (j : ℕ) :
    q^j/(1+d*q^j)^2 ≤
      (q/(d*(q-1)))*(1/(1+d*q^j)-1/(1+d*q^(j+1))) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have ht : 0 < q^j := by positivity
  have h1 : 0 < 1+d*q^j := by positivity
  have h2 : 0 < 1+d*q^j*q := by positivity
  have hdq : 0 < d*(q-1) := by positivity
  have he : (q/(d*(q-1)))*(1/(1+d*q^j)-1/(1+d*q^(j+1))) =
      q*q^j/((1+d*q^j)*(1+d*q^j*q)) := by
    rw [pow_succ]
    have hqm : q-1 ≠ 0 := by linarith
    field_simp
    ring
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos h1) (mul_pos h1 h2)).mpr
  have ht' : 0 ≤ q^j*(1+d*q^j) := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hq.le) ht']

lemma geometric_decay_partial_sum {q d : ℝ} (hq : 1 < q) (hd : 0 < d) (n : ℕ) :
    (∑ j ∈ Finset.range n, q^j/(1+d*q^j)^2) ≤ q/(d*(q-1)) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have h := Finset.sum_le_sum (s := Finset.range n) (fun j _ => geometric_decay_step hq hd j)
  rw [← Finset.mul_sum] at h
  have ht : (∑ j ∈ Finset.range n, (1/(1+d*q^j)-1/(1+d*q^(j+1)))) =
      1/(1+d) - 1/(1+d*q^n) := by
    have hh := Finset.sum_range_sub (fun j => (1 : ℝ)/(1+d*q^j)) n
    rw [Finset.sum_sub_distrib] at hh ⊢
    simp only [pow_zero,mul_one] at hh
    linarith
  rw [ht] at h
  have hdq : 0 ≤ q/(d*(q-1)) := by positivity
  have hfirst : 1/(1+d) ≤ (1 : ℝ) := (div_le_one (by positivity)).mpr (by linarith)
  have hlast : (0 : ℝ) ≤ 1/(1+d*q^n) := by positivity
  exact h.trans ((mul_le_mul_of_nonneg_left (by linarith : 1/(1+d)-1/(1+d*q^n) ≤ 1) hdq).trans_eq (mul_one _))

lemma geometric_decay_tsum {q d : ℝ} (hq : 1 < q) (hd : 0 < d) :
    Summable (fun j : ℕ => q^j/(1+d*q^j)^2) ∧
      (∑' j : ℕ, q^j/(1+d*q^j)^2) ≤ q/(d*(q-1)) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hs := summable_of_sum_range_le (fun j => by positivity : ∀ j : ℕ, 0 ≤ q^j/(1+d*q^j)^2)
    (geometric_decay_partial_sum hq hd)
  exact ⟨hs,hs.tsum_le_of_sum_range_le (geometric_decay_partial_sum hq hd)⟩

lemma rpow_cutoff_comparison {α x : ℝ} (hα : 0 < α) (hα4 : α ≤ 4) (hx : 0 ≤ x) :
    (1+x^α)^2 ≤ 4*(1+x)^8 := by
  by_cases hx1 : x ≤ 1
  · have hp := Real.rpow_le_rpow hx hx1 hα.le
    rw [Real.one_rpow] at hp
    have hn := Real.rpow_nonneg hx α
    have hb : 1 ≤ (1+x)^8 := one_le_pow₀ (by linarith)
    nlinarith
  · have hx1 : 1 ≤ x := le_of_not_ge hx1
    have hp : x^α ≤ x^4 := by simpa using Real.rpow_le_rpow_of_exponent_le hx1 hα4
    have hn := Real.rpow_nonneg hx α
    have he : (1+x^α)^2 ≤ (1+x^4)^2 := by gcongr
    have hpow : 1+x^4 ≤ (1+x)^4 := by simpa using pow_add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hx (by norm_num : (4 : ℕ) ≠ 0)
    have he' : (1+x^4)^2 ≤ (1+x)^8 := by
      have := pow_le_pow_left₀ (by positivity) hpow 2
      simpa only [← pow_mul] using this
    have hb : 0 ≤ (1+x)^8 := by positivity
    linarith

lemma real_dyadic_decay (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 4) {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℕ => ((2 : ℝ)^j)^α/(1+c*2^j)^8) ∧
      (∑' j : ℕ, ((2 : ℝ)^j)^α/(1+c*2^j)^8) ≤
        (4*2^α/(2^α-1))*c^(-α) := by
  have hq : (1 : ℝ) < 2^α := Real.one_lt_rpow (by norm_num) hα
  have hd : 0 < c^α := Real.rpow_pos_of_pos hc α
  have he (j : ℕ) : ((2 : ℝ)^j)^α = (2^α)^j := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
  have hmajor (j : ℕ) : ((2 : ℝ)^j)^α/(1+c*2^j)^8 ≤
      4*((2^α)^j/(1+c^α*(2^α)^j)^2) := by
    have hnum : 0 ≤ ((2 : ℝ)^j)^α := by positivity
    have hi : (1+(c*2^j)^α)^2 ≤ 4*(1+c*2^j)^8 := rpow_cutoff_comparison hα hα4 (by positivity)
    rw [Real.mul_rpow hc.le (by positivity),he] at hi
    rw [he]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : 0 < (1+c*2^j)^8)
      (by positivity : 0 < (1+c^α*(2^α)^j)^2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ (2^α)^j by positivity)]
  have hs := (geometric_decay_tsum hq hd).1.mul_left 4
  have hs' := hs.of_nonneg_of_le (fun _ => by positivity) hmajor
  refine ⟨hs',?_⟩
  calc
    _ ≤ ∑' j : ℕ, 4*((2^α)^j/(1+c^α*(2^α)^j)^2) := hs'.tsum_le_tsum hmajor hs
    _ = 4*∑' j : ℕ, (2^α)^j/(1+c^α*(2^α)^j)^2 := tsum_mul_left
    _ ≤ 4*(2^α/(c^α*(2^α-1))) := mul_le_mul_of_nonneg_left (geometric_decay_tsum hq hd).2 (by norm_num)
    _ = _ := by rw [Real.rpow_neg hc.le]; field_simp

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GramDyad
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted dyadic row summation and explicit coprime Gram bounds. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_sum_sq_weighted {ι : Type*} (I : Finset ι) (v : ι → ℂ)
    (w : ι → ℝ) (hw : ∀ i ∈ I, 0 < w i) :
    ‖∑ i ∈ I, v i‖^2 ≤ (∑ i ∈ I, w i)*(∑ i ∈ I, ‖v i‖^2/w i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq I (fun i => Real.sqrt (w i))
    (fun i => ‖v i‖/Real.sqrt (w i))
  have h1 : (∑ i ∈ I, Real.sqrt (w i)*(‖v i‖/Real.sqrt (w i))) =
      ∑ i ∈ I, ‖v i‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hw i hi))]
  have h2 : (∑ i ∈ I, (Real.sqrt (w i))^2) = ∑ i ∈ I, w i := by
    exact Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hw i hi).le)
  have h3 : (∑ i ∈ I, (‖v i‖/Real.sqrt (w i))^2) = ∑ i ∈ I, ‖v i‖^2/w i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_pow,Real.sq_sqrt (hw i hi).le]
  rw [h1,h2,h3] at h
  exact (pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_sum_le I v) 2).trans h

lemma finite_rows_weighted_sum (P : Finset Eisenstein) (n : ℕ)
    (F : ℕ → Eisenstein → ℂ) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j) :
    (∑ b ∈ P, ‖∑ j ∈ Finset.range n, F j b‖^2) ≤
      (∑ j ∈ Finset.range n, w j)*
        (∑ j ∈ Finset.range n, (∑ b ∈ P, ‖F j b‖^2)/w j) := by
  calc
    _ ≤ ∑ b ∈ P, (∑ j ∈ Finset.range n, w j)*
        (∑ j ∈ Finset.range n, ‖F j b‖^2/w j) :=
      Finset.sum_le_sum (fun b _ => norm_sum_sq_weighted _ (fun j => F j b) w (fun j _ => hw j))
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp_rw [Finset.sum_div]

lemma dyadic_weight_partial_sum {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (∑ j ∈ Finset.range n, (c*2^j)/(1+c*2^j)^2) ≤ 2 := by
  have h := mul_le_mul_of_nonneg_left (dyadic_decay_partial_sum hc n) hc.le
  simp_rw [Finset.mul_sum,← mul_div_assoc] at h
  have he : c*2/c = (2 : ℝ) := by field_simp
  simpa only [he] using h

lemma gramDyadConstant_pos {p : ℝ} (hp : 0 < p) : 0 < gramDyadConstant p := by
  have h := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hp
  unfold gramDyadConstant
  positivity

lemma gram_power_partial_sum {p c : ℝ} (hp : 0 < p) (hp4 : p ≤ 4)
    (hc : 0 < c) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((2 : ℝ)^j)^p/(1+c*2^j)^8) ≤
      gramDyadConstant p * c^(-p) := by
  have h := real_dyadic_decay p hp hp4 hc
  exact (h.1.sum_le_tsum (Finset.range n) (fun j _ => by positivity)).trans h.2

lemma gram_envelope_weight {N c J ε : ℝ} (hN : 0 < N) (hc : 0 < c) (hJ : 0 < J) :
    ((N*J)^ε*J*(N+J+(N*J)^(2/3 : ℝ))/(1+c*J)^10) /
        (c*J/(1+c*J)^2) =
      (N^ε/c)*(N*J^ε/(1+c*J)^8 + J^(1+ε)/(1+c*J)^8 +
        N^(2/3 : ℝ)*J^(2/3+ε : ℝ)/(1+c*J)^8) := by
  rw [Real.mul_rpow hN.le hJ.le,Real.mul_rpow hN.le hJ.le,
    Real.rpow_add hJ,Real.rpow_add hJ,Real.rpow_one]
  have hd : 1+c*J ≠ 0 := by positivity
  field_simp

lemma gram_dyad_partial_rows (P : Finset Eisenstein) (F : ℕ → Eisenstein → ℂ)
    {N c ε C : ℝ} (hN : 0 < N) (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC : 0 ≤ C)
    (hF : ∀ j : ℕ, (1+c*2^j)^10 * (∑ b ∈ P, ‖F j b‖^2) ≤
      C*(N*(2 : ℝ)^j)^ε*(2 : ℝ)^j*(N+(2 : ℝ)^j+(N*(2 : ℝ)^j)^(2/3 : ℝ)))
    (n : ℕ) :
    (∑ b ∈ P, ‖∑ j ∈ Finset.range n, F j b‖^2) ≤
      2*C*(N^ε/c)*(N*gramDyadConstant ε*c^(-ε) +
        gramDyadConstant (1+ε)*c^(-(1+ε)) +
        N^(2/3 : ℝ)*gramDyadConstant (2/3+ε)*c^(-(2/3+ε))) := by
  let w : ℕ → ℝ := fun j => c*2^j/(1+c*2^j)^2
  have hw j : 0 < w j := by dsimp [w]; positivity
  have h := finite_rows_weighted_sum P n F w hw
  have hrow j : (∑ b ∈ P, ‖F j b‖^2)/w j ≤
      C*(N^ε/c)*(N*((2 : ℝ)^j)^ε/(1+c*2^j)^8 +
        ((2 : ℝ)^j)^(1+ε)/(1+c*2^j)^8 +
        N^(2/3 : ℝ)*((2 : ℝ)^j)^(2/3+ε : ℝ)/(1+c*2^j)^8) := by
    have hh := (le_div_iff₀' (by positivity : 0 < (1+c*2^j)^10)).mpr (hF j)
    have hd := div_le_div_of_nonneg_right hh (hw j).le
    apply hd.trans_eq
    dsimp [w]
    rw [show C*(N*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
      (N+(2 : ℝ)^j+(N*(2 : ℝ)^j)^(2/3 : ℝ)) =
      C*((N*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
      (N+(2 : ℝ)^j+(N*(2 : ℝ)^j)^(2/3 : ℝ))) by ring]
    rw [mul_div_assoc,mul_div_assoc,gram_envelope_weight hN hc (by positivity)]
    ring
  have he := Finset.sum_le_sum (s := Finset.range n) (fun j _ => hrow j)
  simp_rw [← Finset.mul_sum,Finset.sum_add_distrib,mul_div_assoc,← Finset.mul_sum] at he
  have hp0 := gram_power_partial_sum hε (by linarith : ε ≤ 4) hc n
  have hp1 := gram_power_partial_sum (by linarith : 0 < 1+ε) (by linarith : 1+ε ≤ 4) hc n
  have hp2 := gram_power_partial_sum (by linarith : 0 < 2/3+ε) (by linarith : 2/3+ε ≤ 4) hc n
  have ht := dyadic_weight_partial_sum hc n
  apply h.trans
  calc
    _ ≤ 2 * (C*(N^ε/c)*(N*(gramDyadConstant ε*c^(-ε)) +
        gramDyadConstant (1+ε)*c^(-(1+ε)) +
        N^(2/3 : ℝ)*(gramDyadConstant (2/3+ε)*c^(-(2/3+ε))))) := by
      apply mul_le_mul ht _ (Finset.sum_nonneg (fun j _ => div_nonneg (by positivity) (hw j).le)) (by norm_num)
      apply he.trans
      gcongr
    _ = _ := by ring

theorem gramDualTerm_rows_explicit (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ 2*N →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ N ≤ norm b ∧ norm b ≤ 2*N) →
      ∀ (a : Eisenstein), primary a → Squarefree a →
      (∀ b ∈ P, IsCoprime a b ∧ a ≠ b) → ∀ (Z : ℝ), 0 < Z →
      let c := Z/(27*norm a*N)
      (∑ b ∈ P, ‖∑' n : Eisenstein, gramDualTerm a b W Z n‖^2) ≤
        C*((2*N)^ε/c)*((2*N)*gramDyadConstant ε*c^(-ε) +
          gramDyadConstant (1+ε)*c^(-(1+ε)) +
          (2*N)^(2/3 : ℝ)*gramDyadConstant (2/3+ε)*c^(-(2/3+ε))) := by
  obtain ⟨C,hC,hc⟩ := gramDualTerm_dyad_rapidDecay W hW hW' hε 5
  refine ⟨2*C,by positivity,?_⟩
  intro P N hN hP a ha hsa hab Z hZ
  have hNpos : 0 < N := by linarith
  dsimp only
  let c : ℝ := Z/(27*norm a*N)
  have han : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero ha)
  have hc0 : 0 < c := by dsimp [c]; positivity
  let F : ℕ → Eisenstein → ℂ := fun j b => ∑ n ∈ frequencyDyad j, gramDualTerm a b W Z n
  have hf j : (1+c*2^j)^10*(∑ b ∈ P, ‖F j b‖^2) ≤
      C*((2*N)*(2 : ℝ)^j)^ε*(2 : ℝ)^j*(2*N+(2 : ℝ)^j+((2*N)*(2 : ℝ)^j)^(2/3 : ℝ)) := by
    have h := hc P N hN hP a ha Z hZ.le j
    have he : Z*(2 : ℝ)^j/(27*norm a*N) = c*2^j := by dsimp [c]; ring
    simpa only [he,show 2*5=10 from rfl,F] using h
  have hp n := gram_dyad_partial_rows P F (by positivity : 0 < 2*N) hc0 hε hε1 hC.le hf n
  have hs b (hb : b ∈ P) : HasSum (fun j => F j b) (∑' n, gramDualTerm a b W Z n) :=
    hasSum_frequencyDyad _ (summable_gramDualTerm ha (hP b hb).1 W hW hW' hZ)
      (gramDualTerm_zero ha (hP b hb).1 hsa (hP b hb).2.1 (hab b hb).1 (hab b hb).2 W Z)
  have ht := tendsto_finsetSum P (fun b hb => ((hs b hb).tendsto_sum_nat.norm.pow 2))
  exact le_of_tendsto ht (Filter.Eventually.of_forall hp)

theorem primaryCharacterGram_coprime_explicit (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ 2*N →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ N ≤ norm b ∧ norm b ≤ 2*N) →
      ∀ (a : Eisenstein), primary a → Squarefree a →
      (∀ b ∈ P, IsCoprime a b ∧ a ≠ b) → ∀ (Z : ℝ), 0 < Z →
      let c := Z/(27*norm a*N)
      (∑ b ∈ P, ‖primaryCharacterGram a b W Z‖^2) ≤
        (Z^2/(81*norm a*N)) *
        (C*((2*N)^ε/c)*((2*N)*gramDyadConstant ε*c^(-ε) +
          gramDyadConstant (1+ε)*c^(-(1+ε)) +
          (2*N)^(2/3 : ℝ)*gramDyadConstant (2/3+ε)*c^(-(2/3+ε)))) := by
  obtain ⟨C,hC,hc⟩ := gramDualTerm_rows_explicit W hW hW' hε hε1
  refine ⟨C,hC,?_⟩
  intro P N hN hP a ha hsa hab Z hZ
  have hNpos : 0 < N := by linarith
  dsimp only
  have han : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero ha)
  have hrow b (hb : b ∈ P) : ‖primaryCharacterGram a b W Z‖^2 ≤
      (Z^2/(81*norm a*N))*‖∑' n : Eisenstein, gramDualTerm a b W Z n‖^2 := by
    rw [norm_primaryCharacterGram_poisson ha (hP b hb).1 hsa (hP b hb).2.1 (hab b hb).1 W hW hW' hZ,
      mul_pow,div_pow,mul_pow,Real.sq_sqrt (norm_nonneg (a*b))]
    have hn : norm (a*b) = norm a * norm b := Complex.normSq_mul _ _
    rw [hn]
    norm_num only [show (9 : ℝ)^2 = 81 from by norm_num]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith [(hP b hb).2.2.1]
  calc
    _ ≤ ∑ b ∈ P, (Z^2/(81*norm a*N))*‖∑' n : Eisenstein, gramDualTerm a b W Z n‖^2 :=
      Finset.sum_le_sum hrow
    _ = (Z^2/(81*norm a*N))*(∑ b ∈ P, ‖∑' n : Eisenstein, gramDualTerm a b W Z n‖^2) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hc P N hN hP a ha hsa hab Z hZ) (by positivity)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GramNormalize
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale-normalized coprime envelopes and divisor losses. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gram_coprime_envelope {N a Z ε : ℝ} (hN : 0 < N) (ha : 0 < a)
    (haN : a ≤ 2*N) (hZ : 0 < Z) (hε : 0 < ε) :
    let c := Z/(27*a*N)
    (Z^2/(81*a*N))*(((2*N)^ε/c)*((2*N)*gramDyadConstant ε*c^(-ε) +
      gramDyadConstant (1+ε)*c^(-(1+ε)) +
      (2*N)^(2/3 : ℝ)*gramDyadConstant (2/3+ε)*c^(-(2/3+ε)))) ≤
    (108*(gramDyadConstant ε+gramDyadConstant (1+ε)+gramDyadConstant (2/3+ε))*(108 : ℝ)^ε) *
      (N^3/Z)^ε*(Z*N+N^2+N^2*Z^(1/3 : ℝ)) := by
  let q : ℝ := 27*a*N/Z
  have hq : 0 < q := by dsimp [q]; positivity
  have hi : Z/(27*a*N) = q⁻¹ := by dsimp [q]; rw [inv_div]
  dsimp only
  rw [hi]
  have hp (p : ℝ) : (q⁻¹)^(-p) = q^p := by
    rw [Real.inv_rpow hq.le,Real.rpow_neg hq.le,inv_inv]
  rw [hp,hp,hp,Real.rpow_add hq,Real.rpow_add hq,Real.rpow_one]
  let D := gramDyadConstant ε+gramDyadConstant (1+ε)+gramDyadConstant (2/3+ε)
  have hk0 := gramDyadConstant_pos hε
  have hk1 := gramDyadConstant_pos (by linarith : 0 < 1+ε)
  have hk2 := gramDyadConstant_pos (by linarith : 0 < 2/3+ε)
  have hD : 0 < D := by dsimp [D]; positivity
  have he : Z^2/(81*a*N)*((2*N)^ε/q⁻¹*(2*N*gramDyadConstant ε*q^ε +
      gramDyadConstant (1+ε)*(q*q^ε)+(2*N)^(2/3 : ℝ)*gramDyadConstant (2/3+ε)*(q^(2/3 : ℝ)*q^ε))) =
      (1/3 : ℝ)*(2*N*q)^ε*(2*N*gramDyadConstant ε*Z+
        gramDyadConstant (1+ε)*(Z*q)+gramDyadConstant (2/3+ε)*Z*(2*N*q)^(2/3 : ℝ)) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 2*N) hq.le,
      Real.mul_rpow (by positivity : 0 ≤ 2*N) hq.le]
    dsimp [q]
    field_simp
    ring
  rw [he]
  have hB : 2*N*q ≤ 108*(N^3/Z) := by
    dsimp [q]
    calc
      2*N*(27*a*N/Z) = (54*a*N^2)/Z := by ring
      _ ≤ (108*N^3)/Z := div_le_div_of_nonneg_right (by
        nlinarith [mul_nonneg (by linarith : 0 ≤ 2*N-a) (sq_nonneg N)]) hZ.le
      _ = _ := by ring
  have heps := Real.rpow_le_rpow (by positivity : 0 ≤ 2*N*q) hB hε.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 108) (by positivity : 0 ≤ N^3/Z)] at heps
  have hqbound : Z*q ≤ 54*N^2 := by dsimp [q]; field_simp; nlinarith
  have hthird : Z*(2*N*q)^(2/3 : ℝ) ≤ 108*N^2*Z^(1/3 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity : 0 ≤ 2*N*q) hB (by norm_num : (0 : ℝ) ≤ 2/3)) hZ.le
    have hr : Z*(108*(N^3/Z))^(2/3 : ℝ) = (108 : ℝ)^(2/3 : ℝ)*N^2*Z^(1/3 : ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 108) (by positivity : 0 ≤ N^3/Z),
        Real.div_rpow (by positivity : 0 ≤ N^3) hZ.le,← Real.rpow_natCast,
        ← Real.rpow_mul hN.le]
      norm_num
      have heZ : Z/(Z^(2/3 : ℝ)) = Z^(1/3 : ℝ) := by
        nth_rw 1 [← Real.rpow_one Z]
        rw [← Real.rpow_sub hZ]
        norm_num
      rw [show Z*((108 : ℝ)^(2/3 : ℝ)*(N^2/Z^(2/3 : ℝ))) =
        (108 : ℝ)^(2/3 : ℝ)*N^2*(Z/Z^(2/3 : ℝ)) by ring,heZ]
    rw [hr] at h
    apply h.trans
    gcongr
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 108)
      (by norm_num : (2/3 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  have hb : 2*N*gramDyadConstant ε*Z+gramDyadConstant (1+ε)*(Z*q)+
      gramDyadConstant (2/3+ε)*Z*(2*N*q)^(2/3 : ℝ) ≤
      108*D*(Z*N+N^2+N^2*Z^(1/3 : ℝ)) := by
    have hk0D : gramDyadConstant ε ≤ D := by dsimp [D]; linarith
    have hk1D : gramDyadConstant (1+ε) ≤ D := by dsimp [D]; linarith
    have hk2D : gramDyadConstant (2/3+ε) ≤ D := by dsimp [D]; linarith
    calc
      _ ≤ D*(2*N*Z+(54*N^2)+(108*N^2*Z^(1/3 : ℝ))) := by
        have h0 := mul_le_mul_of_nonneg_right hk0D (by positivity : 0 ≤ 2*N*Z)
        have h1 := mul_le_mul hk1D hqbound (by positivity) hD.le
        have h2 := mul_le_mul hk2D hthird (by positivity) hD.le
        nlinarith
      _ ≤ _ := by nlinarith [mul_nonneg (hD.le) (by positivity : 0 ≤ Z*N),
        mul_nonneg hD.le (sq_nonneg N)]
  have h := mul_le_mul heps hb (by positivity) (by positivity)
  have hL : 0 ≤ (2*N*q)^ε*(2*N*gramDyadConstant ε*Z+gramDyadConstant (1+ε)*(Z*q)+
      gramDyadConstant (2/3+ε)*Z*(2*N*q)^(2/3 : ℝ)) := by positivity
  dsimp [D] at h
  nlinarith

theorem primaryCharacterGram_coprime_normalized (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (N : ℝ), 1 ≤ 2*N →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ N ≤ norm b ∧ norm b ≤ 2*N) →
      ∀ (a : Eisenstein), primary a → Squarefree a → norm a ≤ 2*N →
      (∀ b ∈ S, IsCoprime a b ∧ a ≠ b) → ∀ (Z : ℝ), 0 < Z →
      (∑ b ∈ S, ‖primaryCharacterGram a b W Z‖^2) ≤
        C*(N^3/Z)^ε*(Z*N+N^2+N^2*Z^(1/3 : ℝ)) := by
  obtain ⟨C,hC,hc⟩ := primaryCharacterGram_coprime_explicit W hW hW' hε hε1
  have hk0 := gramDyadConstant_pos hε
  have hk1 := gramDyadConstant_pos (by linarith : 0 < 1+ε)
  have hk2 := gramDyadConstant_pos (by linarith : 0 < 2/3+ε)
  refine ⟨C*(108*(gramDyadConstant ε+gramDyadConstant (1+ε)+
    gramDyadConstant (2/3+ε))*(108 : ℝ)^ε),by positivity,?_⟩
  intro S N hN hS a ha hsa han hab Z hZ
  have hNa : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero ha)
  have h := mul_le_mul_of_nonneg_left (gram_coprime_envelope (by linarith) hNa han hZ hε) hC.le
  have hh := hc S N hN hS a ha hsa hab Z hZ
  dsimp only at h hh
  nlinarith

lemma gram_scaled_loss {P Z K M ε : ℝ} (hP : 1 ≤ P) (hZ : 1 ≤ Z)
    (hK : 1 ≤ K) (hM : 1 ≤ M) (hMP : M ≤ 2*P) (hε : 0 < ε) :
    ((P/K)^3/(Z/M))^ε * ((Z/M)*(P/K)+(P/K)^2+(P/K)^2*(Z/M)^(1/3 : ℝ)) ≤
    (2 : ℝ)^ε * P^(4*ε) * (Z*P+P^2+P^2*Z^(1/3 : ℝ)) := by
  have hP0 : 0 < P := by linarith
  have hZ0 : 0 < Z := by linarith
  have hK0 : 0 < K := by linarith
  have hM0 : 0 < M := by linarith
  have hnP : P/K ≤ P := div_le_self hP0.le hK
  have hzZ : Z/M ≤ Z := div_le_self hZ0.le hM
  have hx : (P/K)^3/(Z/M) ≤ 2*P^4 := by
    rw [div_div_eq_mul_div]
    calc
      _ ≤ (P^3*(2*P))/1 := by gcongr
      _ = _ := by ring
  have hxpow := Real.rpow_le_rpow (by positivity : 0 ≤ (P/K)^3/(Z/M)) hx hε.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ P^4),
    ← Real.rpow_natCast P 4,← Real.rpow_mul hP0.le] at hxpow
  have hshape : (Z/M)*(P/K)+(P/K)^2+(P/K)^2*(Z/M)^(1/3 : ℝ) ≤
      Z*P+P^2+P^2*Z^(1/3 : ℝ) := by gcongr
  exact mul_le_mul hxpow hshape (by positivity) (by positivity)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GramCommon
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Squared common-factor blocks of the character Gram matrix. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryCharacterGram_common_sq {k a b : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) :
    ‖primaryCharacterGram (k*a) (k*b) W Z‖^2 ≤
      (2 : ℝ)^(primaryPrimeFactors k).card *
      ∑ s ∈ (primaryPrimeFactors k).powerset,
        ‖primaryCharacterGram a b W (Z/norm (∏ p ∈ s, p))‖^2 := by
  rw [primaryCharacterGram_common_factor hk hsk ha hb W hW hW' hZ]
  have h := norm_sum_sq_weighted (primaryPrimeFactors k).powerset
    (fun s => (idealMoebius (∏ p ∈ s, p) : ℂ)*mixedSymbol a b (∏ p ∈ s,p)*
      primaryCharacterGram a b W (Z/norm (∏ p ∈ s,p))) (fun _ => 1) (by simp)
  simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,mul_one,Nat.cast_pow,
    Nat.cast_ofNat,div_one] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro s hs
  apply pow_le_pow_left₀ (_root_.norm_nonneg _)
  simp only [norm_mul,mixedSymbol,norm_star]
  calc
    _ ≤ 1*1*1*‖primaryCharacterGram a b W (Z/norm (∏ p ∈ s,p))‖ := by
      gcongr
      · simpa only [one_mul] using norm_idealMoebius_le_one (∏ p ∈ s,p)
      · simpa only [one_mul] using mul_le_mul (norm_cubicSymbol_le_one ha (∏ p ∈ s,p))
          (norm_cubicSymbol_le_one hb (∏ p ∈ s,p)) (_root_.norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by ring

theorem primaryCharacterGram_common_block (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Finset Eisenstein) (P Z : ℝ) (p k : Eisenstein),
      1 ≤ P → 1 ≤ Z → gramDyad P p →
      (∀ q ∈ Q, gramDyad P q ∧ q ≠ p ∧ primaryCommonFactor p q = k) →
      primary k → Squarefree k → k ∣ p →
      (∑ q ∈ Q, ‖primaryCharacterGram p q W Z‖^2) ≤
        ((2 : ℝ)^(primaryPrimeFactors k).card)^2 *
          (C*(2 : ℝ)^ε*P^(4*ε)*(Z*P+P^2+P^2*Z^(1/3 : ℝ))) := by
  obtain ⟨C,hC,hc⟩ := primaryCharacterGram_coprime_normalized W hW hW' hε hε1
  refine ⟨C,hC,?_⟩
  intro Q P Z p k hP hZ hp hQ hk hsk hkp
  obtain ⟨a,hpa⟩ := hkp
  have hak : primary a := primary_of_mul hk (hpa ▸ hp.1)
  have hasa : Squarefree a := (hpa ▸ hp.2.1).of_mul_right
  have han : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero hak)
  have hk1 := one_le_norm (primary_ne_zero hk)
  have hk0 : 0 < norm k := by linarith
  have hnorm : norm p = norm k*norm a := by rw [hpa]; exact Complex.normSq_mul _ _
  have hkP : norm k ≤ 2*P := (norm_le_of_dvd (primary_ne_zero hp.1) ⟨a,hpa⟩).trans hp.2.2.2.le
  have hN : 1 ≤ 2*(P/norm k) := by rw [← mul_div_assoc]; apply (le_div_iff₀ hk0).mpr; nlinarith
  have haN : norm a ≤ 2*(P/norm k) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hk0).mpr
    nlinarith [hp.2.2.2]
  let B := residualRows Q k
  have hbmem b (hb : b ∈ B) : k*b ∈ Q := (mem_residualRows (primary_ne_zero hk)).mp hb
  have hB b (hb : b ∈ B) : primary b ∧ Squarefree b ∧ P/norm k ≤ norm b ∧ norm b ≤ 2*(P/norm k) := by
    have hq := (hQ (k*b) (hbmem b hb)).1
    have hn : norm (k*b) = norm k*norm b := Complex.normSq_mul _ _
    refine ⟨primary_of_mul hk hq.1,hq.2.1.of_mul_right,?_,?_⟩
    · apply (div_le_iff₀ hk0).mpr
      nlinarith [hq.2.2.1]
    · rw [← mul_div_assoc]
      apply (le_div_iff₀ hk0).mpr
      nlinarith [hq.2.2.2]
  have hab b (hb : b ∈ B) : IsCoprime a b ∧ a ≠ b := by
    have hh := hQ (k*b) (hbmem b hb)
    constructor
    · apply (commonFactor_eq_iff_coprime hk hsk hak (hB b hb).1
        (hpa ▸ hp.2.1) hh.1.2.1).mp
      simpa only [← hpa] using hh.2.2
    · intro he
      exact hh.2.1 (by rw [← he,← hpa])
  have hreindex : (∑ q ∈ Q, ‖primaryCharacterGram p q W Z‖^2) =
      ∑ b ∈ B, ‖primaryCharacterGram (k*a) (k*b) W Z‖^2 := by
    rw [← hpa]
    change _ = ∑ b ∈ residualRows Q k, _
    rw [residualRows_sum_image Q (primary_ne_zero hk) (fun q => ‖primaryCharacterGram p q W Z‖^2)]
    apply Finset.sum_congr rfl
    intro q hq
    have hdiv := (primaryCommonFactor_spec hp.1 (hQ q hq).1.1 hp.2.1 (hQ q hq).1.2.1).2.2.2
    rw [(hQ q hq).2.2] at hdiv
    simp only [ite_eq_left hdiv]
  rw [hreindex]
  have hsum := Finset.sum_le_sum (s := B) (fun b hb =>
    primaryCharacterGram_common_sq hk hsk hak (hB b hb).1 W hW hW' (by linarith : 0 < Z))
  rw [← Finset.mul_sum,Finset.sum_comm] at hsum
  have hrow s (hs : s ∈ (primaryPrimeFactors k).powerset) :
      (∑ b ∈ B, ‖primaryCharacterGram a b W (Z/norm (∏ p ∈ s,p))‖^2) ≤
        C*(2 : ℝ)^ε*P^(4*ε)*(Z*P+P^2+P^2*Z^(1/3 : ℝ)) := by
    let m := ∏ p ∈ s,p
    have hm : primary m := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk (Finset.mem_powerset.mp hs hp)).1.1)
    have hmk : m ∣ k := (primary_subsets_prod_dvd hk (Finset.mem_powerset.mp hs) k).mpr
      (fun p hp => (primaryPrimeFactor_spec hk (Finset.mem_powerset.mp hs hp)).2)
    have hm1 := one_le_norm (primary_ne_zero hm)
    have hmP : norm m ≤ 2*P := (norm_le_of_dvd (primary_ne_zero hk) hmk).trans hkP
    have hh := hc B (P/norm k) hN hB a hak hasa haN hab (Z/norm m) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left (gram_scaled_loss hP hZ hk1 hm1 hmP hε) hC.le
    exact hh.trans (by convert hh' using 1 <;> ring)
  apply hsum.trans
  calc
    _ ≤ (2 : ℝ)^(primaryPrimeFactors k).card *
        ∑ s ∈ (primaryPrimeFactors k).powerset,
          C*(2 : ℝ)^ε*P^(4*ε)*(Z*P+P^2+P^2*Z^(1/3 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CharacterGram
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full epsilon-uniform off-diagonal character Gram estimate. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

 theorem primaryCharacterGram_finite_divisor_bound (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Finset Eisenstein) (P Z : ℝ) (p : Eisenstein),
      1 ≤ P → 1 ≤ Z → gramDyad P p →
      (∀ q ∈ Q, gramDyad P q ∧ q ≠ p) →
      (∑ q ∈ Q, ‖primaryCharacterGram p q W Z‖^2) ≤
        ((2 : ℝ)^(primaryPrimeFactors p).card)^3 *
          (C*(2 : ℝ)^ε*P^(4*ε)*(Z*P+P^2+P^2*Z^(1/3 : ℝ))) := by
  obtain ⟨C,hC,hc⟩ := primaryCharacterGram_common_block W hW hW' hε hε1
  refine ⟨C,hC,?_⟩
  intro Q P Z p hP hZ hp hQ
  let T := Q.image (primaryCommonFactor p)
  let d : ℝ := (2 : ℝ)^(primaryPrimeFactors p).card
  let R : ℝ := C*(2 : ℝ)^ε*P^(4*ε)*(Z*P+P^2+P^2*Z^(1/3 : ℝ))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hT k (hk : k ∈ T) : primary k ∧ Squarefree k ∧ k ∣ p := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hk
    have hh := primaryCommonFactor_spec hp.1 (hQ q hq).1.1 hp.2.1 (hQ q hq).1.2.1
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  have hcard : (T.card : ℝ) ≤ d := by
    have h := primary_divisors_card_le T (fun k hk => ⟨(hT k hk).1,(hT k hk).2.1⟩) hp.1
    have he : T.filter (· ∣ p) = T := Finset.filter_eq_self.mpr (fun k hk => (hT k hk).2.2)
    simpa only [he,d] using h
  have hblock k (hk : k ∈ T) :
      (∑ q ∈ Q.filter (fun q => primaryCommonFactor p q = k), ‖primaryCharacterGram p q W Z‖^2) ≤ d^2*R := by
    have hh := hc (Q.filter (fun q => primaryCommonFactor p q = k)) P Z p k hP hZ hp
      (fun q hq => ⟨(hQ q (Finset.mem_filter.mp hq).1).1,
        (hQ q (Finset.mem_filter.mp hq).1).2,(Finset.mem_filter.mp hq).2⟩)
      (hT k hk).1 (hT k hk).2.1 (hT k hk).2.2
    have hd : (2 : ℝ)^(primaryPrimeFactors k).card ≤ d :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_card
        (primaryPrimeFactors_subset_of_dvd (hT k hk).1 hp.1 (hT k hk).2.2))
    exact hh.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hd 2) hR)
  have he := Finset.sum_fiberwise_of_maps_to (s := Q) (t := T) (g := primaryCommonFactor p)
    (fun q hq => Finset.mem_image.mpr ⟨q,hq,rfl⟩) (fun q => ‖primaryCharacterGram p q W Z‖^2)
  calc
    _ = ∑ k ∈ T, ∑ q ∈ Q.filter (fun q => primaryCommonFactor p q = k),
        ‖primaryCharacterGram p q W Z‖^2 := he.symm
    _ ≤ ∑ k ∈ T, d^2*R := Finset.sum_le_sum hblock
    _ = (T.card : ℝ)*d^2*R := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ d*d^2*R := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (sq_nonneg d)) hR
    _ = _ := by dsimp [d,R]; ring

lemma gram_shape_le {P Z : ℝ} (hP : 0 < P) (hZ : 1 ≤ Z) :
    Z*P+P^2+P^2*Z^(1/3 : ℝ) ≤ 2*Z*(P+(P^3/Z)^(2/3 : ℝ)) := by
  have hZ0 : 0 < Z := by linarith
  have he : Z*(P^3/Z)^(2/3 : ℝ) = P^2*Z^(1/3 : ℝ) := by
    rw [Real.div_rpow (by positivity : 0 ≤ P^3) hZ0.le,
      ← Real.rpow_natCast P 3,← Real.rpow_mul hP.le]
    norm_num
    have hz : Z/Z^(2/3 : ℝ) = Z^(1/3 : ℝ) := by
      nth_rw 1 [← Real.rpow_one Z]
      rw [← Real.rpow_sub hZ0]
      norm_num
    calc _ = P^2*(Z/Z^(2/3 : ℝ)) := by ring
         _ = _ := by rw [hz]
  have hz1 := Real.one_le_rpow hZ (by norm_num : (0 : ℝ) ≤ 1/3)
  nlinarith [mul_nonneg (sq_nonneg P) (by linarith : 0 ≤ Z^(1/3 : ℝ)-1)]

theorem primaryCharacterGram_finite (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Finset Eisenstein) (P Z : ℝ) (p : Eisenstein),
      1 ≤ P → 1 ≤ Z → gramDyad P p →
      (∀ q ∈ Q, gramDyad P q ∧ q ≠ p) →
      (∑ q ∈ Q, ‖primaryCharacterGram p q W Z‖^2) ≤
        C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ)) := by
  let η : ℝ := min (ε/8) (1/2)
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hηε : 7*η ≤ ε := by have h := min_le_left (ε/8) (1/2); change η ≤ ε/8 at h; linarith
  obtain ⟨C,hC,hc⟩ := primaryCharacterGram_finite_divisor_bound W hW hW' hη hη1
  obtain ⟨D,hD,hd⟩ := primeDivisorWeight_small_power η hη
  refine ⟨2*C*D^3*(2 : ℝ)^(4*η),by positivity,?_⟩
  intro Q P Z p hP hZ hp hQ
  have hP0 : 0 < P := by linarith
  have hZ0 : 0 < Z := by linarith
  have hdiv : (2 : ℝ)^(primaryPrimeFactors p).card ≤ D*(2*P)^η :=
    (hd p hp.1 hp.2.1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg p) hp.2.2.2.le hη.le) hD.le)
  have hdiv3 := pow_le_pow_left₀ (by positivity) hdiv 3
  have hpow : P^(7*η) ≤ (P*Z)^ε := by
    apply (Real.rpow_le_rpow_of_exponent_le hP hηε).trans
    exact Real.rpow_le_rpow hP0.le (by nlinarith) hε.le
  have hh := hc Q P Z p hP hZ hp hQ
  have he : (D*(2*P)^η)^3 * (C*(2 : ℝ)^η*P^(4*η)) =
      C*D^3*(2 : ℝ)^(4*η)*P^(7*η) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hP0.le,mul_pow,mul_pow,
      ← Real.rpow_natCast ((2 : ℝ)^η) 3,← Real.rpow_natCast (P^η) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),← Real.rpow_mul hP0.le]
    calc
      _ = C*D^3*((2 : ℝ)^(η*3)*(2 : ℝ)^η)*(P^(η*3)*P^(4*η)) := by ring_nf
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),← Real.rpow_add hP0]; ring_nf
  calc
    _ ≤ (D*(2*P)^η)^3 * (C*(2 : ℝ)^η*P^(4*η)) * (Z*P+P^2+P^2*Z^(1/3 : ℝ)) := by
      apply hh.trans
      have h := mul_le_mul_of_nonneg_right hdiv3
        (by positivity : 0 ≤ C*(2 : ℝ)^η*P^(4*η)*(Z*P+P^2+P^2*Z^(1/3 : ℝ)))
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ = C*D^3*(2 : ℝ)^(4*η)*P^(7*η)*(Z*P+P^2+P^2*Z^(1/3 : ℝ)) := by rw [he]
    _ ≤ C*D^3*(2 : ℝ)^(4*η)*(P*Z)^ε*(2*Z*(P+(P^3/Z)^(2/3 : ℝ))) := by
      apply mul_le_mul _ (gram_shape_le hP0 hZ) (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The short Möbius identity on Eisenstein ideals

Nonzero Eisenstein ideals are represented by their finite prime-ideal
exponent vectors. Their arithmetic functions form the multivariate power
series ring: its multiplication is exactly finite Dirichlet convolution.
The norm below is the norm of the product of prime representatives, so
the support statements retain the actual multiplicative ideal norm.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_norm {a : Eisenstein} (ha : a ≠ 0) :
    idealExponentNorm (idealExponentOf a) = norm a := by
  unfold idealExponentNorm
  rw [associated_normNat (idealExponentOf_associated ha), normNat_cast]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMoebiusBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler products identify and bound the arithmetic Möbius coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma shortIdealMoebius_abs_le_one (F : ℝ) (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν (shortIdealMoebius F)| ≤ 1 := by
  change |if idealExponentNorm ν ≤ Real.sqrt F then _ else (0 : ℝ)| ≤ 1
  split_ifs
  · exact idealMoebiusSeries_abs_le_one ν
  · norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite-order Hecke prime input

The finite-order Hecke prime-sum input specializes to independent prime
factors using the elementary character laws.

The input is the cubic-character consequence of Thorner--Zaman,
*A unified and improved Chebotarev density theorem*, Algebra & Number
Theory 13 (2019), Theorem 1.4, in the Siegel–Walfisz form for cubic Hecke characters.  Only finite-order characters occur in this input;
smooth weights and norm twists follow by partial summation.
-/

noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CubicFirstMoment

/-- The character of an ordered tuple splits into the characters of its
individual factors. Repeated prime factors are still permitted here;
the squarefree restriction in the manuscript is imposed separately. -/
theorem mixedCubic_prod {ι : Type*} (s : Finset ι) (f : ι → Eisenstein)
    {q₁ q₂ : Eisenstein} (h₁ : primary q₁) (h₂ : primary q₂) :
    mixedCubic q₁ q₂ (∏ i ∈ s, f i) = ∏ i ∈ s, mixedCubic q₁ q₂ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mixedCubic_one h₁ h₂]
  | @insert i s hi ih => simp [hi, mixedCubic_mul h₁ h₂, ih]

/-- Exact factorization of an independent prime-tuple character sum.
The supports may be distinct smooth norm dyads, with their weights already
included in `w`. No condition coupling the tuple's product is inserted. -/
theorem independent_prime_tuple_character_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (supports : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ)
    {q₁ q₂ : Eisenstein} (h₁ : primary q₁) (h₂ : primary q₂) :
    (∑ f ∈ Fintype.piFinset supports,
      (∏ i, w i (f i)) * mixedCubic q₁ q₂ (∏ i, f i)) =
      ∏ i, ∑ p ∈ supports i, w i p * mixedCubic q₁ q₂ p := by
  classical
  simp_rw [mixedCubic_prod _ _ h₁ h₂, ← Finset.prod_mul_distrib]
  exact (Finset.prod_univ_sum supports (fun i p => w i p * mixedCubic q₁ q₂ p)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite ordered prime convolutions used in the exceptional moments.
The weights are independent on the prime factors; the squarefree cutoff
is exposed exactly as the repeated-prime discrepancy. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact collection of the ordered tuples by their product. -/
theorem orderedConvolution_sum (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ)
    (χ : Eisenstein → ℂ) :
    (∑ b ∈ orderedConvolutionSupport S, orderedConvolution S w b * χ b) =
      ∑ f ∈ Fintype.piFinset S, (∏ i, w i (f i))*χ (∏ i, f i) := by
  unfold orderedConvolution orderedConvolutionSupport
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ b ∈ (Fintype.piFinset S).image (fun f => ∏ i, f i),
        ∑ f ∈ Fintype.piFinset S with (∏ i, f i) = b,
          (∏ i, w i (f i))*χ (∏ i, f i) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro f hf
      rw [(Finset.mem_filter.mp hf).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun f hf => Finset.mem_image_of_mem _ hf) _

/-- The full independent convolution separates exactly against the primitive
mixed character; no product cutoff is inserted in this identity. -/
theorem orderedConvolution_mixedCubic (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) :
    (∑ b ∈ orderedConvolutionSupport S, orderedConvolution S w b * mixedCubic q₁ q₂ b) =
      ∏ i, ∑ p ∈ S i, w i p * mixedCubic q₁ q₂ p := by
  rw [orderedConvolution_sum]
  exact independent_prime_tuple_character_sum S w h₁ h₂

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite primary ideal polynomials and their actual Eisenstein-element
realizations. These sums omit the ramified prime above three. They are
not identified with the complete ideal series of `IdealMellinSeries`. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma mem_primaryIdealBall {ν : EisensteinIdealExponent} {Y : ℝ} :
    ν ∈ primaryIdealBall Y ↔ primary (idealPrimaryGenerator ν) ∧ idealExponentNorm ν ≤ Y := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ha,hN⟩ := mem_primaryElementBall.mp ha
    rw [idealPrimaryGenerator_at_element ha,idealExponentOf_norm (primary_ne_zero ha)]
    exact ⟨ha,hN⟩
  · rintro ⟨hν,hN⟩
    exact Finset.mem_image.mpr ⟨idealPrimaryGenerator ν,
      mem_primaryElementBall.mpr ⟨hν,(idealPrimaryGenerator_norm ν).trans_le hN⟩,
      idealExponentOf_primaryGenerator ν⟩

theorem primaryIdealPolynomial_eq_elements (Y : ℝ) (A : EisensteinArithmeticFunction)
    (χ : Eisenstein → ℂ) :
    primaryIdealPolynomial Y A χ =
      ∑ a ∈ primaryElementBall Y, ((MvPowerSeries.coeff (idealExponentOf a) A : ℝ) : ℂ)*χ a := by
  unfold primaryIdealPolynomial primaryIdealBall
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    simp only [idealCharacterCoeff,idealPrimaryGenerator_at_element (mem_primaryElementBall.mp ha).1]
  · intro a ha b hb he
    have ha' := (mem_primaryElementBall.mp ha).1
    have hb' := (mem_primaryElementBall.mp hb).1
    have h := congrArg idealPrimaryGenerator he
    simpa only [idealPrimaryGenerator_at_element ha',idealPrimaryGenerator_at_element hb'] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler exclusions on the complete ideal lattice. The full norm
ball includes the ramified prime; excluding it is an explicit choice of
prime set, and every rescaling factor is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma mem_fullIdealBall {ν : EisensteinIdealExponent} {Y : ℝ} :
    ν ∈ fullIdealBall Y ↔ idealExponentNorm ν ≤ Y := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    rw [idealExponentOf_norm (mem_nonzeroNormBall.mp ha).2]
    exact (mem_nonzeroNormBall.mp ha).1
  · intro h
    exact Finset.mem_image.mpr ⟨idealExponentGenerator ν,
      mem_nonzeroNormBall.mpr ⟨by simpa only [idealExponentNorm,normNat_cast] using h,
        idealExponentGenerator_ne_zero ν⟩,idealExponentOf_generator ν⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact corrected-dispersion identities

The polynomials below are those in `eq:dispersion-polynomials` of the
manuscript. The factorization is valid even with a common prime factor:
the already proved Gauss-sum multiplication law then makes the summand zero.
The norm estimates here do not assume the new dispersion bounds.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

/-- Finite Cauchy--Schwarz for the actual complex row sum. -/
theorem complex_bilinear_rows_sq {ι : Type*} (A : Finset ι) (α F : ι → ℂ) :
    ‖∑ a ∈ A, α a * F a‖ ^ 2 ≤
      (∑ a ∈ A, ‖α a‖ ^ 2) * ∑ a ∈ A, ‖F a‖ ^ 2 := by
  calc
    _ ≤ (∑ a ∈ A, ‖α a * F a‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (norm_sum_le _ _) 2
    _ = (∑ a ∈ A, ‖α a‖ * ‖F a‖) ^ 2 := by simp_rw [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq A _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramSchur
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite Gram row-sum bound

This is the linear algebra step in the exceptional-moment argument: a
symmetric absolute Gram kernel bounds its quadratic form by its largest
row sum. Both variables are retained in the estimate.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

theorem nonnegative_schur_bound {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (K : ι → ι → ℝ) (R : ℝ)
    (hK : ∀ p ∈ P, ∀ q ∈ P, 0 ≤ K p q)
    (hsym : ∀ p ∈ P, ∀ q ∈ P, K p q = K q p)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, K p q ≤ R) :
    (∑ p ∈ P, ∑ q ∈ P, x p * x q * K p q) ≤ R * ∑ p ∈ P, (x p)^2 := by
  have hpairs : (∑ p ∈ P, ∑ q ∈ P, 2 * (x p * x q * K p q)) ≤
      ∑ p ∈ P, ∑ q ∈ P, ((x p)^2 + (x q)^2) * K p q := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro q hq
    have h := mul_nonneg (sq_nonneg (x p-x q)) (hK p hp q hq)
    nlinarith only [h]
  have hswap : (∑ p ∈ P, ∑ q ∈ P, (x q)^2 * K p q) =
      ∑ p ∈ P, ∑ q ∈ P, (x p)^2 * K p q := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hsym q hq p hp]
  have hrow' : (∑ p ∈ P, ∑ q ∈ P, (x p)^2 * K p q) ≤
      R * ∑ p ∈ P, (x p)^2 := by
    simp only [← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow p hp) (sq_nonneg (x p))
  have he : (∑ p ∈ P, ∑ q ∈ P, ((x p)^2 + (x q)^2) * K p q) =
      2 * ∑ p ∈ P, ∑ q ∈ P, (x p)^2 * K p q := by
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hswap]
    ring
  rw [he] at hpairs
  simp only [← Finset.mul_sum] at hpairs hrow'
  linarith

/-- The complex Gram quadratic form is bounded using only absolute row
sums and Hermitian symmetry of their norms. -/
theorem complex_schur_bound {ι : Type*} (P : Finset ι) (z : ι → ℂ)
    (K : ι → ι → ℂ) (R : ℝ)
    (hsym : ∀ p ∈ P, ∀ q ∈ P, ‖K p q‖ = ‖K q p‖)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, ‖K p q‖ ≤ R) :
    ‖∑ p ∈ P, ∑ q ∈ P, z p * star (z q) * K p q‖ ≤
      R * ∑ p ∈ P, ‖z p‖^2 := by
  calc
    _ ≤ ∑ p ∈ P, ‖∑ q ∈ P, z p * star (z q) * K p q‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, ‖z p * star (z q) * K p q‖ :=
      Finset.sum_le_sum (fun p hp => norm_sum_le _ _)
    _ = ∑ p ∈ P, ∑ q ∈ P, ‖z p‖ * ‖z q‖ * ‖K p q‖ := by
      simp only [norm_mul, norm_star]
    _ ≤ _ := nonnegative_schur_bound P (fun p => ‖z p‖) (fun p q => ‖K p q‖) R
      (fun p hp q hq => _root_.norm_nonneg _) hsym hrow

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramOperator
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From Gram row sums to character-polynomial bounds

Finite duality turns the row-sum bound into an operator estimate. This is
the Cauchy/Gram step used after the multiplicity argument in the exceptional-character-moment argument.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

lemma complex_sum_norm_sq_expansion {ι : Type*} (P : Finset ι) (z : ι → ℂ) :
    ((‖∑ p ∈ P, z p‖^2 : ℝ) : ℂ) = ∑ p ∈ P, ∑ q ∈ P, z p * star (z q) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [starRingEnd_apply, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma finiteGram_star {ι κ : Type*} (N : Finset κ) (T : ι → κ → ℂ) (p q : ι) :
    star (finiteGram N T q p) = finiteGram N T p q := by
  simp only [finiteGram, star_sum, star_mul, star_star]

lemma finite_gram_identity {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (z : ι → ℂ) (T : ι → κ → ℂ) :
    ((∑ n ∈ N, ‖∑ p ∈ P, z p * T p n‖^2 : ℝ) : ℂ) =
      ∑ p ∈ P, ∑ q ∈ P, z p * star (z q) * finiteGram N T p q := by
  have hcast : ((∑ n ∈ N, ‖∑ p ∈ P, z p * T p n‖^2 : ℝ) : ℂ) =
      ∑ n ∈ N, ((‖∑ p ∈ P, z p * T p n‖^2 : ℝ) : ℂ) :=
    map_sum Complex.ofRealHom _ _
  rw [hcast]
  simp_rw [complex_sum_norm_sq_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [finiteGram, Finset.mul_sum, star_mul]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem finite_gram_energy_le {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (z : ι → ℂ) (T : ι → κ → ℂ) (R : ℝ)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, ‖finiteGram N T p q‖ ≤ R) :
    (∑ n ∈ N, ‖∑ p ∈ P, z p * T p n‖^2) ≤ R * ∑ p ∈ P, ‖z p‖^2 := by
  have hs : ∀ p ∈ P, ∀ q ∈ P, ‖finiteGram N T p q‖ = ‖finiteGram N T q p‖ := by
    intro p hp q hq
    rw [← finiteGram_star N T p q, norm_star]
  have h := complex_schur_bound P z (finiteGram N T) R hs hrow
  rw [← finite_gram_identity P N z T, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at h
  exact h

/-- Duality exchanges rows and columns without loss. -/
theorem finite_gram_operator_le {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (v : κ → ℂ) (T : ι → κ → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, ‖finiteGram N T p q‖ ≤ R) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n * T p n‖^2) ≤ R * ∑ n ∈ N, ‖v n‖^2 := by
  let f : ι → ℂ := fun p => ∑ n ∈ N, v n * T p n
  let g : κ → ℂ := fun n => ∑ p ∈ P, f p * star (T p n)
  let E : ℝ := ∑ p ∈ P, ‖f p‖^2
  let V : ℝ := ∑ n ∈ N, ‖v n‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdual : (E : ℂ) = ∑ n ∈ N, v n * star (g n) := by
    change ((∑ p ∈ P, ‖f p‖^2 : ℝ) : ℂ) = _
    have hcast : ((∑ p ∈ P, ‖f p‖^2 : ℝ) : ℂ) =
        ∑ p ∈ P, ((‖f p‖^2 : ℝ) : ℂ) := map_sum Complex.ofRealHom _ _
    rw [hcast]
    have he : ∀ p, ((‖f p‖^2 : ℝ) : ℂ) = f p * star (f p) := by
      intro p
      rw [Complex.ofReal_pow]
      exact (Complex.mul_conj' (f p)).symm
    simp_rw [he]
    conv_lhs => arg 2; ext p; lhs; unfold f
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [g, star_sum, star_mul, star_star, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hrow' : ∀ p ∈ P,
      ∑ q ∈ P, ‖finiteGram N (fun p n => star (T p n)) p q‖ ≤ R := by
    intro p hp
    have he : ∀ q, finiteGram N (fun p n => star (T p n)) p q = star (finiteGram N T p q) := by
      intro q
      simp only [finiteGram, star_sum, star_mul, star_star, mul_comm]
    simpa only [he, norm_star] using hrow p hp
  have hg := finite_gram_energy_le P N f (fun p n => star (T p n)) R hrow'
  change (∑ n ∈ N, ‖g n‖^2) ≤ R*E at hg
  have hc := complex_bilinear_rows_sq N v (fun n => star (g n))
  rw [← hdual, Complex.norm_real, Real.norm_of_nonneg hE] at hc
  simp only [norm_star] at hc
  change E^2 ≤ V * (∑ n ∈ N, ‖g n‖^2) at hc
  have hm := mul_le_mul_of_nonneg_left hg hV
  change E ≤ R*V
  by_cases hzero : E = 0
  · rw [hzero]
    exact mul_nonneg hR hV
  · have hpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
    nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Divisor and pair-product multiplicities with a bounded number of prime bases. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_inj_primary {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (h : idealExponentOf a = idealExponentOf b) : a = b := by
  have hA := idealExponentOf_associated (primary_ne_zero ha)
  have hB := idealExponentOf_associated (primary_ne_zero hb)
  rw [h] at hA
  exact primary_associated_eq ha hb (hA.symm.trans hB)

lemma primary_divisor_card_exponents (T : Finset Eisenstein)
    (hT : ∀ a ∈ T, primary a) {b : Eisenstein} (hb : b ≠ 0) :
    (T.filter (fun a => a ∣ b)).card ≤
      ∏ p ∈ (idealExponentOf b).support, (idealExponentOf b p + 1) := by
  let D := T.filter (fun a => a ∣ b)
  have hinj : Set.InjOn idealExponentOf (D : Set Eisenstein) := by
    intro a ha c hc he
    exact idealExponentOf_inj_primary (hT a (Finset.mem_filter.mp ha).1)
      (hT c (Finset.mem_filter.mp hc).1) he
  have hsub : D.image idealExponentOf ⊆ Finset.Iic (idealExponentOf b) := by
    intro ν hν
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hν
    exact Finset.mem_Iic.mpr (idealExponentOf_le_of_dvd
      (primary_ne_zero (hT a (Finset.mem_filter.mp ha).1)) hb (Finset.mem_filter.mp ha).2)
  calc
    D.card = (D.image idealExponentOf).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.Iic (idealExponentOf b)).card := Finset.card_le_card hsub
    _ = _ := by rw [Finsupp.card_Iic]; simp

lemma idealPrimeRepresentative_normNat_ge_two (p : EisensteinIdealPrime) :
    2 ≤ normNat (idealPrimeRepresentative p) := by
  have hp := idealPrimeRepresentative_irreducible p
  have hz := normNat_ne_zero hp.ne_zero
  have ho : normNat (idealPrimeRepresentative p) ≠ 1 := by
    intro h
    apply hp.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [← normNat_cast, h]
    norm_num
  omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDivisorPower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary-exponent ideal divisor bounds for the short-convolution
polynomials. No bound on the number of distinct prime bases is assumed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma exponent_add_one_le_two_pow (n : ℕ) : (n : ℝ)+1 ≤ (2:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    push_cast
    rw [pow_succ]
    have hnon : 1 ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
    nlinarith

private lemma exponent_factor_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n : ℕ, (n:ℝ)+1 ≤ A*(2:ℝ)^(ε*n) := by
  let L : ℝ := ε*Real.log 2
  have hL : 0 < L := mul_pos hε (Real.log_pos (by norm_num))
  refine ⟨1+1/L,by linarith [div_pos (zero_lt_one : (0:ℝ) < 1) hL],?_⟩
  intro n
  have hE1 : 1 ≤ Real.exp (L*n) := Real.one_le_exp_iff.mpr (by positivity)
  have hn : (n:ℝ) ≤ Real.exp (L*n)/L := by
    apply (le_div_iff₀ hL).mpr
    nlinarith [Real.add_one_le_exp (L*n)]
  have hE : Real.exp (L*n) = (2:ℝ)^(ε*n) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    dsimp [L]
    congr 1
    ring
  calc
    _ ≤ Real.exp (L*n)/L+Real.exp (L*n) := add_le_add hn hE1
    _ = (1+1/L)*Real.exp (L*n) := by ring
    _ = _ := by rw [hE]

/-- The full ideal divisor product is bounded by every positive norm
power. Small prime ideals form a finite set, while large prime ideals
absorb every exponent directly. -/
theorem ideal_divisor_product_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : EisensteinIdealExponent,
      (∏ p ∈ ν.support, ((ν p:ℝ)+1)) ≤ C*idealExponentNorm ν^ε := by
  obtain ⟨A,hA,hA_bound⟩ := exponent_factor_uniform hε
  let R : ℝ := (2:ℝ)^(1/ε)
  let T : Finset EisensteinIdealPrime :=
    (fullIdealBall R).biUnion (fun ν => ν.support)
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  have hRe : R^ε = 2 := by
    dsimp [R]
    rw [← Real.rpow_mul (by norm_num),one_div_mul_cancel hε.ne',Real.rpow_one]
  have hT (p : EisensteinIdealPrime) :
      (normNat (idealPrimeRepresentative p):ℝ) ≤ R → p ∈ T := by
    intro hp
    apply Finset.mem_biUnion.mpr
    refine ⟨Finsupp.single p 1,?_,by simp⟩
    apply mem_fullIdealBall.mpr
    simpa only [idealExponentNorm_single,pow_one] using hp
  refine ⟨A^T.card,pow_pos (zero_lt_one.trans_le hA) _,?_⟩
  intro ν
  have hpoint : ∀ p ∈ ν.support, (ν p:ℝ)+1 ≤
      (if p ∈ T then A else 1)*(normNat (idealPrimeRepresentative p):ℝ)^(ε*ν p) := by
    intro p hp
    have hNp : (2:ℝ) ≤ normNat (idealPrimeRepresentative p) := by
      exact_mod_cast idealPrimeRepresentative_normNat_ge_two p
    by_cases hpT : p ∈ T
    · simp only [ite_eq_left hpT]
      exact (hA_bound (ν p)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by norm_num) hNp (by positivity)) (zero_le_one.trans hA))
    · simp only [ite_eq_right hpT,one_mul]
      have hRp : R ≤ (normNat (idealPrimeRepresentative p):ℝ) := le_of_lt
        (lt_of_not_ge (fun h => hpT (hT p h)))
      have hbase : (2:ℝ) ≤ (normNat (idealPrimeRepresentative p):ℝ)^ε := by
        rw [← hRe]
        exact Real.rpow_le_rpow hR.le hRp hε.le
      calc
        _ ≤ (2:ℝ)^ν p := exponent_add_one_le_two_pow _
        _ ≤ ((normNat (idealPrimeRepresentative p):ℝ)^ε)^ν p :=
          pow_le_pow_left₀ (by norm_num) hbase _
        _ = _ := by rw [← Real.rpow_mul_natCast (by positivity)]
  have hprod := Finset.prod_le_prod (s := ν.support)
    (fun p _ => (by positivity : 0 ≤ (ν p:ℝ)+1)) hpoint
  rw [Finset.prod_mul_distrib] at hprod
  have hsmall : (∏ p ∈ ν.support, if p ∈ T then A else 1) ≤ A^T.card := by
    rw [Finset.prod_ite_mem,Finset.prod_const]
    exact pow_le_pow_right₀ hA (Finset.card_le_card Finset.inter_subset_right)
  have hnorm : (∏ p ∈ ν.support,
      (normNat (idealPrimeRepresentative p):ℝ)^(ε*ν p)) = idealExponentNorm ν^ε := by
    calc
      _ = ∏ p ∈ ν.support, ((normNat (idealPrimeRepresentative p):ℝ)^ν p)^ε := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
        congr 1
        ring
      _ = (∏ p ∈ ν.support, (normNat (idealPrimeRepresentative p):ℝ)^ν p)^ε :=
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity) ε
      _ = _ := by rw [idealExponentNorm_eq_prod]
  rw [hnorm] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hsmall
    (Real.rpow_nonneg (idealExponentNorm_pos ν).le _))

/-- Arbitrary primary divisors, with no squarefree or bounded-prime-support
restriction on the ambient element. -/
theorem primary_divisor_card_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset Eisenstein),
      (∀ a ∈ T, primary a) → ∀ b : Eisenstein, b ≠ 0 →
      ((T.filter (fun a => a ∣ b)).card : ℝ) ≤ C*norm b^ε := by
  obtain ⟨C,hC,hbound⟩ := ideal_divisor_product_small_power hε
  refine ⟨C,hC,?_⟩
  intro T hT b hb
  have h : ((T.filter (fun a => a ∣ b)).card : ℝ) ≤
      ((∏ p ∈ (idealExponentOf b).support, (idealExponentOf b p+1) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (primary_divisor_card_exponents T hT hb)
  push_cast at h
  exact h.trans ((hbound (idealExponentOf b)).trans_eq (by rw [idealExponentOf_norm hb]))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy and actual character moments of fixed-length independent prime products. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeCubicProductPolynomial_eq (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {a : Eisenstein} (ha : primary a) :
    primeCubicProductPolynomial S w a =
      ∑ b ∈ orderedConvolutionSupport S, orderedConvolution S w b*cubicSymbol a b := by
  have h := orderedConvolution_mixedCubic S w ha (by simp [primary] : primary 1)
  simpa only [mixedCubic, cubicSymbol_one_lower, star_one, mul_one,
    primeCubicProductPolynomial] using h.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryConvolutionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-length convolutions of arbitrary primary elements. The divisor
bound absorbs the tuple multiplicity in any positive norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedPrimarySupport_primary (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ a ∈ S i, primary a) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport S) : primary b := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  exact primary_finset_prod _ _ (fun i _ => hS i (f i) (Fintype.mem_piFinset.mp hf i))

/-- The tuple multiplicity is uniformly a small power even when each
factor has arbitrarily many distinct prime divisors. -/
theorem primary_tuple_fiber_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein),
      (∀ i, ∀ a ∈ S i, primary a) → ∀ Y : ℝ, 1 ≤ Y →
      ∀ b ∈ orderedConvolutionSupport S, norm b ≤ Y →
      (((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card : ℝ) ≤ C*Y^ε := by
  let k : ℝ := Fintype.card ι
  let δ : ℝ := ε/(k+1)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : δ*k ≤ ε := by
    have h := div_mul_cancel₀ ε (show k+1 ≠ 0 by positivity)
    change δ*(k+1) = ε at h
    nlinarith
  obtain ⟨D,hD,hdiv⟩ := primary_divisor_card_small_power hδ
  refine ⟨D^(Fintype.card ι),pow_pos hD _,?_⟩
  intro S hS Y hY b hb hbY
  have hb0 := primary_ne_zero (orderedPrimarySupport_primary S hS hb)
  have hsub : (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b) ⊆
      Fintype.piFinset (fun i => (S i).filter (fun a => a ∣ b)) := by
    intro f hf
    obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
    apply Fintype.mem_piFinset.mpr
    intro i
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hfs i,?_⟩
    rw [← hfb]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  have hcard (i : ι) : (((S i).filter (fun a => a ∣ b)).card : ℝ) ≤ D*Y^δ :=
    (hdiv (S i) (hS i) b hb0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg b) hbY hδ.le) hD.le)
  calc
    _ ≤ ((Fintype.piFinset (fun i => (S i).filter (fun a => a ∣ b))).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = ∏ i, (((S i).filter (fun a => a ∣ b)).card : ℝ) := by
      rw [Fintype.card_piFinset,Nat.cast_prod]
    _ ≤ ∏ _i : ι, D*Y^δ := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
      (fun i _ => hcard i)
    _ = D^(Fintype.card ι)*Y^(δ*k) := by
      rw [Finset.prod_const,Finset.card_univ,mul_pow,← Real.rpow_mul_natCast (by linarith)]
    _ ≤ D^(Fintype.card ι)*Y^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hY hδε) (by positivity)

/-- Exact independent coefficient energies, with only a small norm-power
loss when collecting arbitrary primary tuples by their product. -/
theorem primary_orderedConvolution_energy {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ), (∀ i, ∀ a ∈ S i, primary a) →
      ∀ Y : ℝ, 1 ≤ Y → (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∑ b ∈ orderedConvolutionSupport S, ‖orderedConvolution S w b‖^2) ≤
        C*Y^ε*primeConvolutionEnergy S w := by
  obtain ⟨C,hC,hfiber⟩ := primary_tuple_fiber_small_power (ι := ι) hε
  refine ⟨C,hC,?_⟩
  intro S w hS Y hY hprod
  let T := Fintype.piFinset S
  let W : (ι → Eisenstein) → ℂ := fun f => ∏ i, w i (f i)
  have hrow (b : Eisenstein) (hb : b ∈ orderedConvolutionSupport S) :
      ‖orderedConvolution S w b‖^2 ≤
        C*Y^ε*∑ f ∈ T with (∏ i, f i) = b, ‖W f‖^2 := by
    have hCS := complex_bilinear_rows_sq (T.filter (fun f => (∏ i, f i) = b))
      (fun _ => (1:ℂ)) W
    simp only [one_mul,norm_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hCS
    change ‖orderedConvolution S w b‖^2 ≤ _ at hCS
    apply hCS.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    apply hfiber S hS Y hY b hb
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
    exact hprod f hf
  calc
    _ ≤ ∑ b ∈ orderedConvolutionSupport S,
        C*Y^ε*∑ f ∈ T with (∏ i, f i) = b, ‖W f‖^2 := Finset.sum_le_sum hrow
    _ = C*Y^ε*∑ f ∈ T, ‖W f‖^2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to
        (fun f hf => Finset.mem_image_of_mem _ hf) _
    _ = _ := by
      congr 1
      simp only [W,norm_prod,← Finset.prod_pow]
      exact (Finset.prod_univ_sum S (fun i a => ‖w i a‖^2)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpPrimaryMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp bounded-coefficient cubic sieve, specialized to actual
primary convolutions. The pointwise divisor bound is essential here. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pointwise coefficient bound for the actual independent primary
convolution, uniform in its supports and independent factor weights. -/
theorem primary_orderedConvolution_norm {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) → ∀ Y : ℝ, 1 ≤ Y →
      ∀ b ∈ orderedConvolutionSupport S, norm b ≤ Y →
      ‖orderedConvolution S w b‖ ≤ C*Y^δ*(∏ i, M i) := by
  obtain ⟨C,hC,hfiber⟩ := primary_tuple_fiber_small_power (ι := ι) hδ
  refine ⟨C,hC,?_⟩
  intro S w M hS hM hw Y hY b hb hbY
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  unfold orderedConvolution
  calc
    _ ≤ ∑ f ∈ T, ‖∏ i, w i (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ T, ∏ i, M i := by
      apply Finset.sum_le_sum
      intro f hf
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => _root_.norm_nonneg _)
        (fun i _ => hw i (f i) (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 i))
    _ = (T.card:ℝ)*(∏ i, M i) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (hfiber S hS Y hY b hb hbY)
      (Finset.prod_nonneg (fun i _ => hM i))

/-- Sharp cubic moment for the actual collected primary convolution,
including any fixed coefficient twist of norm at most one. -/
theorem primaryConvolution_sharp_twisted_moment {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ (P : Finset Eisenstein) (N Y : ℝ), 1 ≤ N → 1 ≤ Y →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ orderedConvolutionSupport S, ‖χ b‖ ≤ 1) →
      (∑ a ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        (orderedConvolution S w b*χ b)*cubicSymbol a b‖^2) ≤
        C*(N*Y)^ε*Y*(N+Y+(N*Y)^(2/3:ℝ))*(Y^δ*(∏ i, M i)^2) := by
  obtain ⟨C,hC,hbound⟩ := bounded_cubic_moment hε
  obtain ⟨D,hD,hnorm⟩ := primary_orderedConvolution_norm (ι := ι)
    (show 0 < δ/2 by linarith)
  refine ⟨C*D^2,mul_pos hC (sq_pos_of_pos hD),?_⟩
  intro S w M hS hM hw P N Y hN hY hP hprod χ hχ
  have hMprod : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  have hH : ∀ b ∈ orderedConvolutionSupport S, b ≠ 0 ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨primary_ne_zero (orderedPrimarySupport_primary S hS hb),?_⟩
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
    exact hprod f hf
  have h := hbound P (orderedConvolutionSupport S) N Y (D*Y^(δ/2)*(∏ i, M i))
    hN hY (by positivity) hP hH (fun b => orderedConvolution S w b*χ b) (by
      intro b hb
      rw [norm_mul]
      exact (mul_le_of_le_one_right (_root_.norm_nonneg _) (hχ b hb)).trans
        (hnorm S w M hS hM hw Y hY b hb (hH b hb).2))
  have hpow : (Y^(δ/2))^2 = Y^δ := by
    rw [← Real.rpow_mul_natCast (by linarith)]
    congr 1
    norm_num
  simpa only [mul_pow,hpow,mul_assoc,mul_left_comm,mul_comm] using h

/-- The untwisted product polynomial has the same sharp moment; every
factor is permitted to be an arbitrary primary-element polynomial. -/
theorem primaryConvolution_sharp_product_moment {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ (P : Finset Eisenstein) (N Y : ℝ), 1 ≤ N → 1 ≤ Y →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∑ a ∈ P, ‖primeCubicProductPolynomial S w a‖^2) ≤
        C*(N*Y)^ε*Y*(N+Y+(N*Y)^(2/3:ℝ))*(Y^δ*(∏ i, M i)^2) := by
  obtain ⟨C,hC,hbound⟩ := primaryConvolution_sharp_twisted_moment (ι := ι) hε hδ
  refine ⟨C,hC,?_⟩
  intro S w M hS hM hw P N Y hN hY hP hprod
  have h := hbound S w M hS hM hw P N Y hN hY hP hprod (fun _ => 1) (by simp)
  have he : (∑ a ∈ P, ‖primeCubicProductPolynomial S w a‖^2) =
      ∑ a ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        (orderedConvolution S w b*1)*cubicSymbol a b‖^2 := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [mul_one,primeCubicProductPolynomial_eq S w (hP a ha).1]
  rw [he]
  exact h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryMultiplicity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual fixed multiplicities in the exceptional-moment argument. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private lemma prod_fixed_copies {M : Type*} [CommMonoid M]
    (k : ι → ℕ) (v : ι → M) :
    (∏ j : (Σ i, Fin (k i)), v j.1) = ∏ i, (v i)^(k i) := by
  rw [Fintype.prod_sigma]
  simp

private lemma fixed_copies_norm_bound (k : ι → ℕ)
    (S : ι → Finset Eisenstein) (X : ι → ℝ)
    (hSX : ∀ i, ∀ a ∈ S i, norm a ≤ X i)
    (f : (Σ i, Fin (k i)) → Eisenstein)
    (hf : f ∈ Fintype.piFinset (fun j : (Σ i, Fin (k i)) => S j.1)) :
    norm (∏ j, f j) ≤ ∏ i, (X i)^(k i) := by
  rw [norm_finset_prod]
  calc
    _ ≤ ∏ j : (Σ i, Fin (k i)), X j.1 := Finset.prod_le_prod
      (fun _ _ => norm_nonneg _)
      (fun j _ => hSX j.1 (f j) (Fintype.mem_piFinset.mp hf j))
    _ = _ := prod_fixed_copies k X

/-- Every fixed multiplicity vector gives the actual power product of
the primary polynomials, with the sharp cubic-sieve length factor. -/
theorem primaryPolynomial_multiplicity_moment (k : ι → ℕ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M X : ι → ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ S i, norm a ≤ X i) →
      ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∑ a ∈ P, ‖∏ i, (∑ n ∈ S i, w i n*cubicSymbol a n)^(k i)‖^2) ≤
        C*(N*(∏ i, (X i)^(k i)))^ε*(∏ i, (X i)^(k i))*
          (N+(∏ i, (X i)^(k i))+(N*(∏ i, (X i)^(k i)))^(2/3:ℝ))*
          ((∏ i, (X i)^(k i))^δ*(∏ i, (M i)^(k i))^2) := by
  obtain ⟨C,hC,hbound⟩ := primaryConvolution_sharp_product_moment
    (ι := Σ i, Fin (k i)) hε hδ
  refine ⟨C,hC,?_⟩
  intro S w M X hS hM hw hX hSX P N hN hP
  have hL : 1 ≤ ∏ i, (X i)^(k i) :=
    Finset.one_le_prod (fun i _ => one_le_pow₀ (hX i))
  have h := hbound (fun j => S j.1) (fun j => w j.1) (fun j => M j.1)
    (fun j => hS j.1) (fun j => hM j.1) (fun j => hw j.1)
    P N (∏ i, (X i)^(k i)) hN hL hP
    (fixed_copies_norm_bound k S X hSX)
  simpa only [primeCubicProductPolynomial,Fintype.prod_sigma,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual short Möbius, zeta and logarithmic factors occurring in
the finite ideal convolution identity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma shortArithmeticFactor_norm {F X : ℝ} {A : EisensteinArithmeticFunction}
    (hA : ShortArithmeticFactor F A) (hX : 1 ≤ X) {a : Eisenstein}
    (ha : a ∈ primaryElementBall X) :
    ‖((MvPowerSeries.coeff (idealExponentOf a) A : ℝ) : ℂ)‖ ≤ 1+Real.log X := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  obtain ⟨ha,hNa⟩ := mem_primaryElementBall.mp ha
  rcases hA with rfl | rfl | rfl
  · rw [Complex.norm_real,Real.norm_eq_abs]
    exact (shortIdealMoebius_abs_le_one F _).trans (by linarith)
  · simp only [MvPowerSeries.coeff_apply,idealZeta,Complex.ofReal_one,norm_one]
    linarith
  · rw [MvPowerSeries.coeff_apply,idealLogNorm,idealExponentOf_norm (primary_ne_zero ha),
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (one_le_norm (primary_ne_zero ha)))]
    have h := Real.log_le_log (norm_pos_of_ne_zero (primary_ne_zero ha)) hNa
    linarith

lemma shortArithmeticFactor_twisted_norm {F X : ℝ} {A : EisensteinArithmeticFunction}
    (hA : ShortArithmeticFactor F A) (hX : 1 ≤ X) {a : Eisenstein}
    (ha : a ∈ primaryElementBall X) (u : ℂ) (hu : ‖u‖ ≤ 1) :
    ‖((MvPowerSeries.coeff (idealExponentOf a) A : ℝ) : ℂ)*u‖ ≤ 1+Real.log X := by
  rw [norm_mul]
  exact (mul_le_of_le_one_right (_root_.norm_nonneg _) hu).trans
    (shortArithmeticFactor_norm hA hX ha)

lemma primaryElementBall_card_le {X : ℝ} (hX : 0 ≤ X) :
    ((primaryElementBall X).card : ℝ) ≤ 18*X :=
  (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (nonzeroNormBall_card_le hX)

lemma shortArithmeticFactor_energy {F X : ℝ} {A : EisensteinArithmeticFunction}
    (hA : ShortArithmeticFactor F A) (hX : 1 ≤ X) (u : Eisenstein → ℂ)
    (hu : ∀ a ∈ primaryElementBall X, ‖u a‖ ≤ 1) :
    (∑ a ∈ primaryElementBall X,
      ‖((MvPowerSeries.coeff (idealExponentOf a) A : ℝ) : ℂ)*u a‖^2) ≤
      18*X*(1+Real.log X)^2 := by
  calc
    _ ≤ ∑ _a ∈ primaryElementBall X, (1+Real.log X)^2 :=
      Finset.sum_le_sum (fun a ha => pow_le_pow_left₀ (_root_.norm_nonneg _)
        (shortArithmeticFactor_twisted_norm hA hX ha (u a) (hu a ha)) 2)
    _ = ((primaryElementBall X).card:ℝ)*(1+Real.log X)^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (primaryElementBall_card_le (by linarith))
      (sq_nonneg _)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The fixed-multiplicity sharp cubic moment for the exact ideal
polynomials supplied by the short Möbius identity. -/
theorem shortFactor_multiplicity_moment (k : ι → ℕ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ),
      (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ primaryElementBall (X i), ‖u i a‖ ≤ 1) →
      ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∑ a ∈ P, ‖∏ i,
        (primaryIdealPolynomial (X i) (A i) (fun n => u i n*cubicSymbol a n))^(k i)‖^2) ≤
        C*(N*(∏ i, (X i)^(k i)))^ε*(∏ i, (X i)^(k i))*
          (N+(∏ i, (X i)^(k i))+(N*(∏ i, (X i)^(k i)))^(2/3:ℝ))*
          ((∏ i, (X i)^(k i))^δ*(∏ i, (1+Real.log (X i))^(k i))^2) := by
  obtain ⟨C,hC,hbound⟩ := primaryPolynomial_multiplicity_moment k hε hδ
  refine ⟨C,hC,?_⟩
  intro F X A u hA hX hu P N hN hP
  have h := hbound (fun i => primaryElementBall (X i))
    (fun i a => ((MvPowerSeries.coeff (idealExponentOf a) (A i):ℝ):ℂ)*u i a)
    (fun i => 1+Real.log (X i)) X
    (fun _ _ ha => (mem_primaryElementBall.mp ha).1)
    (fun i => by linarith [Real.log_nonneg (hX i)])
    (fun i a ha => shortArithmeticFactor_twisted_norm (hA i) (hX i) ha _ (hu i a ha))
    hX (fun _ _ ha => (mem_primaryElementBall.mp ha).2) P N hN hP
  simpa only [primaryIdealPolynomial_eq_elements,mul_assoc] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogSmoothWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic full factors are exact linear combinations of two smooth
weights. No logarithmic coefficient is silently discarded. -/
noncomputable section
open Set Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_weighted_smooth_finite (c : Eisenstein → ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) :
    (∑' a : Eisenstein, if primary a then c a*W (norm a/Z) else 0) =
      ∑ a ∈ primaryElementBall (B*Z), c a*W (norm a/Z) := by
  calc
    _ = ∑ a ∈ primaryElementBall (B*Z), if primary a then c a*W (norm a/Z) else 0 := by
      apply tsum_eq_sum
      intro a ha
      by_cases hprim : primary a
      · have hN : B*Z < norm a := lt_of_not_ge (fun h => ha (mem_primaryElementBall.mpr ⟨hprim,h⟩))
        rw [ite_eq_left hprim,hW _ ((lt_div_iff₀ hZ).mpr hN),mul_zero]
      · rw [ite_eq_right hprim]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [ite_eq_left (mem_primaryElementBall.mp ha).1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularFullSmoothFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact classification of the full smooth factors from the short inverse.
The short Möbius alternative vanishes once the dyad lies above its support. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryAngularShortSmoothSum_eq_polynomial (ℓ : ℤ) (A : EisensteinArithmeticFunction)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    primaryAngularShortSmoothSum ℓ A a b q η W Z t =
      primaryIdealPolynomial (B*Z) A (fun x =>
        mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*theta ℓ x*mellinPhase t (norm x)*W (norm x/Z)) := by
  rw [primaryIdealPolynomial_eq_elements]
  unfold primaryAngularShortSmoothSum
  rw [primary_weighted_smooth_finite _ W hZ hW]
  apply Finset.sum_congr rfl
  intro x _
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExceptionalExponents
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponent contradictions in the exceptional character moments

These are the real-variable steps in the proof of the exceptional-character-moment proposition
(`prop:dual`) in *An unconditional first moment for cubic Gauss sums*.  The analytic
large-sieve and Gram estimates are separate inputs to these numerical
steps.
-/

namespace CubicFirstMoment

/-- On the useful range, the mixed term in the cubic sieve dominates both
endpoint terms. -/
theorem cubicSieve_exponent {z : ℝ} (hz₀ : 1 / 2 ≤ z) (hz₁ : z ≤ 2) :
    z + max (max 1 z) (2 * (1 + z) / 3) = 2 / 3 + 5 * z / 3 := by
  have h₁ : 1 ≤ 2 * (1 + z) / 3 := by linarith
  have h₂ : z ≤ 2 * (1 + z) / 3 := by linarith
  rw [max_eq_right (max_le h₁ h₂)]
  ring

/-- A positive short factor can be copied a fixed integer number of times
so that its exponent is strictly inside the Gram range. -/
theorem exists_copies_in_gram_range {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1 / 2) :
    ∃ m : ℕ, 4 / 3 < (m : ℝ) * a ∧ (m : ℝ) * a < 2 := by
  let q : ℝ := (4 / 3) / a
  let m : ℕ := ⌊q⌋₊ + 1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hlower : q < (m : ℝ) := by
    simpa [m] using Nat.lt_floor_add_one q
  have hupper : (m : ℝ) ≤ q + 1 := by
    dsimp [m]
    push_cast
    linarith [Nat.floor_le hq]
  have hqa : q * a = 4 / 3 := by
    dsimp [q]
    exact div_mul_cancel₀ _ ha.ne'
  refine ⟨m, ?_, ?_⟩
  · nlinarith [mul_lt_mul_of_pos_right hlower ha]
  · nlinarith [mul_le_mul_of_nonneg_right hupper ha.le]

/-- The all-ones multiplicity vector and the vector with one extra copy
force that factor's defect to be nonpositive. -/
theorem multiplicity_defect_nonpos {r total defect : ℝ}
    (hlower : 2 / 3 - 2 * total ≤ r)
    (hextra : r ≤ 2 / 3 - 2 * (total + defect)) : defect ≤ 0 := by
  linarith

end CubicFirstMoment
open scoped BigOperators

namespace CubicFirstMoment

private theorem sum_omit_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (j : ι) :
    (∑ i, if i = j then 0 else v i) = (∑ i, v i) - v j := by
  calc
    _ = ∑ i, (v i - if i = j then v i else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp_all
    _ = _ := by simp [Finset.sum_sub_distrib]

/-- The fixed-multiplicity argument in the first exceptional configuration.
It forces every factor to have the same `5/6` exponent and forces the row
count exponent to be `2/3`, before the off-diagonal Gram estimate is applied.

Here `d i` is `v i - 5 * a i / 6`. The two sides of the large-value and
large-sieve inequalities have already been expressed in terms of these
factor defects. -/
theorem exceptional_multiplicity_rigidity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a d : ι → ℝ) (r : ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i < 1) (hsum : ∑ i, a i = 1)
    (hlarge : 2 / 3 - 2 * (∑ i, d i) ≤ r)
    (hmoment : ∀ k : ι → ℕ,
      1 / 2 ≤ (∑ i, (k i : ℝ) * a i) → (∑ i, (k i : ℝ) * a i) ≤ 2 →
      r ≤ 2 / 3 - 2 * (∑ i, (k i : ℝ) * d i)) :
    (∀ i, d i = 0) ∧ r = 2 / 3 := by
  have hnonpos (j : ι) : d j ≤ 0 := by
    let k : ι → ℕ := fun i => 1 + if i = j then 1 else 0
    have hk (v : ι → ℝ) : (∑ i, (k i : ℝ) * v i) = (∑ i, v i) + v j := by
      simp [k, add_mul, Finset.sum_add_distrib]
    have hbound := hmoment k (by rw [hk, hsum]; linarith [(ha j).1])
      (by rw [hk, hsum]; linarith [(ha j).2])
    rw [hk] at hbound
    exact multiplicity_defect_nonpos hlarge hbound
  have hshort (j : ι) (hj : a j ≤ 1 / 2) : d j = 0 := by
    let k : ι → ℕ := fun i => if i = j then 0 else 1
    have hk (v : ι → ℝ) : (∑ i, (k i : ℝ) * v i) = (∑ i, v i) - v j := by
      simpa [k] using sum_omit_one v j
    have hbound := hmoment k (by rw [hk, hsum]; linarith)
      (by rw [hk, hsum]; linarith [(ha j).1])
    rw [hk] at hbound
    linarith [hnonpos j]
  have hzero : ∀ i, d i = 0 := by
    by_cases hall : ∀ i, a i ≤ 1 / 2
    · exact fun i => hshort i (hall i)
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      have hothers (i : ι) (hij : i ≠ j) : d i = 0 := by
        apply hshort
        have hsmall : a i ≤ ∑ k ∈ (Finset.univ : Finset ι).erase j, a k :=
          Finset.single_le_sum (fun k _ => (ha k).1) (by simp [hij])
        have hrest := Finset.sum_erase_add (Finset.univ : Finset ι) a (Finset.mem_univ j)
        rw [hsum] at hrest
        linarith
      have htotal : (∑ i, d i) = d j := by
        apply Finset.sum_eq_single j
        · intro i _ hij
          exact hothers i hij
        · simp
      obtain ⟨m, hm₀, hm₁⟩ := exists_copies_in_gram_range
        (a := 1 - a j) (by linarith [(ha j).2]) (by linarith)
      let k : ι → ℕ := fun i => if i = j then 0 else m
      have hka : (∑ i, (k i : ℝ) * a i) = (m : ℝ) * (1 - a j) := by
        calc
          _ = (m : ℝ) * ∑ i, (if i = j then 0 else a i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            simp only [k]
            split_ifs <;> simp
          _ = _ := by rw [sum_omit_one, hsum]
      have hkd : (∑ i, (k i : ℝ) * d i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        by_cases hij : i = j
        · simp [k, hij]
        · simp [k, hij, hothers i hij]
      have hbound := hmoment k (by rw [hka]; linarith) (by rw [hka]; linarith)
      rw [hkd, mul_zero, sub_zero] at hbound
      have hdj : d j = 0 := by
        rw [htotal] at hlarge
        linarith [hnonpos j]
      intro i
      by_cases hij : i = j
      · simpa [hij] using hdj
      · exact hothers i hij
  refine ⟨hzero, ?_⟩
  have htotal : (∑ i, d i) = 0 := by simp [hzero]
  rw [htotal, mul_zero, sub_zero] at hlarge
  have hone := hmoment (fun _ => 1) (by norm_num [hsum]) (by norm_num [hsum])
  have hupper : r ≤ 2 / 3 := by simpa [hzero] using hone
  exact le_antisymm hupper hlarge

end CubicFirstMoment

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorbing the explicit logarithmic factors in the short-polynomial
moments, without making subpower growth an assumption. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma one_add_log_small_power {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 ≤ x → 1+Real.log x ≤ A*x^η := by
  refine ⟨1+1/η,by positivity,?_⟩
  intro x hx
  have hp := Real.one_le_rpow hx hη.le
  have hl := Real.log_le_rpow_div (zero_le_one.trans hx) hη
  calc
    _ ≤ x^η+x^η/η := add_le_add hp hl
    _ = _ := by ring

lemma shortFactorPolynomial_norm_le {F X : ℝ} {A : EisensteinArithmeticFunction}
    (hA : ShortArithmeticFactor F A) (hX : 1 ≤ X) (u : Eisenstein → ℂ)
    (hu : ∀ a ∈ primaryElementBall X, ‖u a‖ ≤ 1) :
    ‖primaryIdealPolynomial X A u‖ ≤ 18*X*(1+Real.log X) := by
  rw [primaryIdealPolynomial_eq_elements]
  calc
    _ ≤ ∑ a ∈ primaryElementBall X,
        ‖((MvPowerSeries.coeff (idealExponentOf a) A:ℝ):ℂ)*u a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ primaryElementBall X, (1+Real.log X) :=
      Finset.sum_le_sum (fun a ha => shortArithmeticFactor_twisted_norm hA hX ha _ (hu a ha))
    _ = ((primaryElementBall X).card:ℝ)*(1+Real.log X) := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (primaryElementBall_card_le (by linarith))
      (by linarith [Real.log_nonneg hX])

theorem shortFactorPolynomial_norm_small_power {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F X : ℝ) (A : EisensteinArithmeticFunction),
      ShortArithmeticFactor F A → 1 ≤ X → ∀ u : Eisenstein → ℂ,
      (∀ a ∈ primaryElementBall X, ‖u a‖ ≤ 1) →
      ‖primaryIdealPolynomial X A u‖ ≤ C*X^(1+η) := by
  obtain ⟨C,hC,hbound⟩ := one_add_log_small_power hη
  refine ⟨18*C,by positivity,?_⟩
  intro F X A hA hX u hu
  apply (shortFactorPolynomial_norm_le hA hX u hu).trans
  calc
    _ ≤ 18*X*(C*X^η) := mul_le_mul_of_nonneg_left (hbound X hX) (by positivity)
    _ = (18*C)*X^(1+η) := by
      rw [Real.rpow_add (zero_lt_one.trans_le hX),Real.rpow_one]
      ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem logarithmic_factor_product (k : ι → ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ι → ℝ, (∀ i, 1 ≤ X i) →
      (∏ i, (1+Real.log (X i))^(k i)) ≤ C*(∏ i, (X i)^(k i))^η := by
  obtain ⟨A,hA,hbound⟩ := one_add_log_small_power hη
  refine ⟨∏ i, A^(k i),Finset.prod_pos (fun _ _ => pow_pos hA _),?_⟩
  intro X hX
  have hp (i : ι) : ((X i)^η)^(k i) = ((X i)^(k i))^η := by
    rw [← Real.rpow_mul_natCast (zero_le_one.trans (hX i)),
      ← Real.rpow_natCast_mul (zero_le_one.trans (hX i))]
    congr 1
    ring
  calc
    _ ≤ ∏ i, (A*(X i)^η)^(k i) := Finset.prod_le_prod
      (fun i _ => pow_nonneg (by linarith [Real.log_nonneg (hX i)]) _)
      (fun i _ => pow_le_pow_left₀ (by linarith [Real.log_nonneg (hX i)]) (hbound _ (hX i)) _)
    _ = (∏ i, A^(k i))*(∏ i, ((X i)^(k i))^η) := by
      simp_rw [mul_pow,hp]
      rw [Finset.prod_mul_distrib]
    _ = _ := by rw [Real.finsetProd_rpow _ _ (fun i _ => pow_nonneg (zero_le_one.trans (hX i)) _) η]

private lemma half_power_absorb {N L ε : ℝ} (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hε : 0 ≤ ε) : (N*L)^(ε/2)*L^(ε/2) ≤ (N*L)^ε := by
  calc
    _ ≤ (N*L)^(ε/2)*(N*L)^(ε/2) := by
      gcongr
      exact le_mul_of_one_le_left (zero_le_one.trans hL) hN
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

/-- The exact short-factor cubic moments have the clean subpower-loss
form used to extract the limiting multiplicity inequalities. -/
theorem shortFactor_multiplicity_power (k : ι → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ),
      (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ primaryElementBall (X i), ‖u i a‖ ≤ 1) →
      ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∑ a ∈ P, ‖∏ i,
        (primaryIdealPolynomial (X i) (A i) (fun n => u i n*cubicSymbol a n))^(k i)‖^2) ≤
        C*(N*(∏ i, (X i)^(k i)))^ε*(∏ i, (X i)^(k i))*
          (N+(∏ i, (X i)^(k i))+(N*(∏ i, (X i)^(k i)))^(2/3:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := shortFactor_multiplicity_moment k
    (show 0 < ε/2 by linarith) (show 0 < ε/4 by linarith)
  obtain ⟨B,hB,hlog⟩ := logarithmic_factor_product k (show 0 < ε/8 by linarith)
  refine ⟨C*B^2,by positivity,?_⟩
  intro F X A u hA hX hu P N hN hP
  let L : ℝ := ∏ i, (X i)^(k i)
  let G : ℝ := ∏ i, (1+Real.log (X i))^(k i)
  have hL : 1 ≤ L := Finset.one_le_prod (fun i _ => one_le_pow₀ (hX i))
  have hG : 0 ≤ G := Finset.prod_nonneg
    (fun i _ => pow_nonneg (by linarith [Real.log_nonneg (hX i)]) _)
  have hpow : (L^(ε/8))^2 = L^(ε/4) := by
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hL)]
    congr 1
    ring
  have hG2 : G^2 ≤ B^2*L^(ε/4) := by
    have h := pow_le_pow_left₀ hG (hlog X hX) 2
    change G^2 ≤ (B*L^(ε/8))^2 at h
    simpa only [mul_pow,hpow] using h
  apply (hbound F X A u hA hX hu P N hN hP).trans
  change C*(N*L)^(ε/2)*L*(N+L+(N*L)^(2/3:ℝ))*(L^(ε/4)*G^2) ≤ _
  calc
    _ ≤ C*(N*L)^(ε/2)*L*(N+L+(N*L)^(2/3:ℝ))*(L^(ε/4)*(B^2*L^(ε/4))) := by
      gcongr
    _ = (C*B^2)*((N*L)^(ε/2)*L^(ε/2))*L*(N+L+(N*L)^(2/3:ℝ)) := by
      have hp : L^(ε/4)*L^(ε/4) = L^(ε/2) := by
        rw [← Real.rpow_add (zero_lt_one.trans_le hL)]
        congr 1
        ring
      calc
        _ = (C*B^2)*((N*L)^(ε/2)*(L^(ε/4)*L^(ε/4)))*L*(N+L+(N*L)^(2/3:ℝ)) := by ring
        _ = _ := by rw [hp]
    _ ≤ (C*B^2)*(N*L)^ε*L*(N+L+(N*L)^(2/3:ℝ)) := by
      gcongr
      exact half_power_absorb hN hL hε.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MomentExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic exponents of actual positive sequences and the limits
of the proved moment inequalities. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace CubicFirstMoment

theorem HasPowerExponent.const {Y : ℕ → ℝ} (hY : Tendsto Y atTop atTop)
    (C : ℝ) : HasPowerExponent Y (fun _ => C) 0 :=
  (Real.tendsto_log_atTop.comp hY).const_div_atTop _

theorem HasPowerExponent.mul {Y f g : ℕ → ℝ} {a b : ℝ}
    (hf : HasPowerExponent Y f a) (hg : HasPowerExponent Y g b)
    (hfp : ∀ᶠ j in atTop, 0 < f j) (hgp : ∀ᶠ j in atTop, 0 < g j) :
    HasPowerExponent Y (fun j => f j*g j) (a+b) := by
  apply (hf.add hg).congr'
  filter_upwards [hfp,hgp] with j hfj hgj
  simp only [Real.log_mul hfj.ne' hgj.ne',add_div]

theorem HasPowerExponent.rpow {Y f : ℕ → ℝ} {a : ℝ}
    (hf : HasPowerExponent Y f a) (hfp : ∀ᶠ j in atTop, 0 < f j) (p : ℝ) :
    HasPowerExponent Y (fun j => (f j)^p) (p*a) := by
  apply (hf.const_mul p).congr'
  filter_upwards [hfp] with j hfj
  simp only [Real.log_rpow hfj,mul_div_assoc]

theorem HasPowerExponent.natPow {Y f : ℕ → ℝ} {a : ℝ}
    (hf : HasPowerExponent Y f a) (k : ℕ) :
    HasPowerExponent Y (fun j => (f j)^k) ((k:ℝ)*a) := by
  apply (hf.const_mul (k:ℝ)).congr'
  filter_upwards [] with j
  simp only [Real.log_pow,mul_div_assoc]

private lemma log_max_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (max x y) = max (Real.log x) (Real.log y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h,max_eq_right (Real.log_le_log hx h)]
  · rw [max_eq_left h,max_eq_left (Real.log_le_log hy h)]

theorem HasPowerExponent.add {Y f g : ℕ → ℝ} {a b : ℝ}
    (hf : HasPowerExponent Y f a) (hg : HasPowerExponent Y g b)
    (hY : Tendsto Y atTop atTop)
    (hfp : ∀ᶠ j in atTop, 0 < f j) (hgp : ∀ᶠ j in atTop, 0 < g j) :
    HasPowerExponent Y (fun j => f j+g j) (max a b) := by
  have hmax : HasPowerExponent Y (fun j => max (f j) (g j)) (max a b) := by
    apply (hf.max hg).congr'
    filter_upwards [hY.eventually_gt_atTop 1,hfp,hgp] with j hYj hfj hgj
    rw [log_max_pos hfj hgj,← max_div_div_right (Real.log_pos hYj).le]
  have hu : Tendsto
      (fun j => Real.log 2/Real.log (Y j)+Real.log (max (f j) (g j))/Real.log (Y j))
      atTop (𝓝 (max a b)) := by
    simpa only [zero_add,Function.comp_def] using ((Real.tendsto_log_atTop.comp hY).const_div_atTop
      (Real.log 2)).add hmax
  apply hmax.squeeze' hu
  · filter_upwards [hY.eventually_gt_atTop 1,hfp,hgp] with j hYj hfj hgj
    apply div_le_div_of_nonneg_right _ (Real.log_pos hYj).le
    exact Real.log_le_log (lt_max_of_lt_left hfj) (max_le (by linarith) (by linarith))
  · filter_upwards [hY.eventually_gt_atTop 1,hfp,hgp] with j hYj hfj hgj
    rw [← add_div,← Real.log_mul (by norm_num : (2:ℝ) ≠ 0)
      (ne_of_gt (lt_max_of_lt_left hfj))]
    apply div_le_div_of_nonneg_right _ (Real.log_pos hYj).le
    apply Real.log_le_log (add_pos hfj hgj)
    have hfmax := le_max_left (f j) (g j)
    have hgmax := le_max_right (f j) (g j)
    linarith

theorem HasPowerExponent.mono {Y f g : ℕ → ℝ} {a b : ℝ}
    (hf : HasPowerExponent Y f a) (hg : HasPowerExponent Y g b)
    (hY : Tendsto Y atTop atTop)
    (hfp : ∀ᶠ j in atTop, 0 < f j) (hle : ∀ᶠ j in atTop, f j ≤ g j) : a ≤ b := by
  apply le_of_tendsto_of_tendsto hf hg
  filter_upwards [hY.eventually_gt_atTop 1,hfp,hle] with j hYj hfj hle
  exact div_le_div_of_nonneg_right (Real.log_le_log hfj hle) (Real.log_pos hYj).le

private lemma remove_positive_loss {a b c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ ε*c+b) : a ≤ b := by
  by_contra hab
  have hgap : 0 < a-b := sub_pos.mpr (lt_of_not_ge hab)
  let ε : ℝ := (a-b)/(2*(|c|+1))
  have hε : 0 < ε := div_pos hgap (by positivity)
  have he : ε*(2*(|c|+1)) = a-b := div_mul_cancel₀ _ (by positivity)
  have hc := mul_le_mul_of_nonneg_left (le_abs_self c) hε.le
  have hb := h ε hε
  nlinarith [mul_nonneg hε.le (abs_nonneg c)]

/-- Taking actual logarithmic limits of the sharp cubic moment gives
the numerical inequality used in the first exceptional configuration. -/
theorem cubic_moment_exponent {Y R V N L : ℕ → ℝ} {r v n z : ℝ}
    (hY : Tendsto Y atTop atTop)
    (hRp : ∀ᶠ j in atTop, 0 < R j) (hVp : ∀ᶠ j in atTop, 0 < V j)
    (hNp : ∀ᶠ j in atTop, 0 < N j) (hLp : ∀ᶠ j in atTop, 0 < L j)
    (hR : HasPowerExponent Y R r) (hV : HasPowerExponent Y V v)
    (hN : HasPowerExponent Y N n) (hL : HasPowerExponent Y L z)
    (hmoment : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ j in atTop, R j*(V j)^2 ≤
        C*(N j*L j)^ε*L j*(N j+L j+(N j*L j)^(2/3:ℝ))) :
    r+2*v ≤ z+max (max n z) ((2/3:ℝ)*(n+z)) := by
  apply remove_positive_loss (c := n+z)
  intro ε hε
  obtain ⟨C,hC,hm⟩ := hmoment ε hε
  have hNL := hN.mul hL hNp hLp
  have hNLp : ∀ᶠ j in atTop, 0 < N j*L j := by
    filter_upwards [hNp,hLp] with j hn hl using mul_pos hn hl
  have hsum := (hN.add hL hY hNp hLp).add (hNL.rpow hNLp (2/3:ℝ)) hY
    (by filter_upwards [hNp,hLp] with j hn hl using add_pos hn hl)
    (by filter_upwards [hNLp] with j h using Real.rpow_pos_of_pos h _)
  have hleft := hR.mul (hV.natPow 2) hRp
    (by filter_upwards [hVp] with j h using sq_pos_of_pos h)
  have hright := (((HasPowerExponent.const hY C).mul (hNL.rpow hNLp ε)
    (Eventually.of_forall (fun _ => hC))
    (by filter_upwards [hNLp] with j h using Real.rpow_pos_of_pos h _)).mul hL
    (by filter_upwards [hNLp] with j h using mul_pos hC (Real.rpow_pos_of_pos h _)) hLp).mul hsum
    (by filter_upwards [hNLp,hLp] with j h hl using mul_pos (mul_pos hC
      (Real.rpow_pos_of_pos h _)) hl)
    (by filter_upwards [hNp,hLp,hNLp] with j hn hl h using
      add_pos (add_pos hn hl) (Real.rpow_pos_of_pos h _))
  have h := hleft.mono hright hY
    (by filter_upwards [hRp,hVp] with j hr hv using mul_pos hr (sq_pos_of_pos hv)) hm
  simpa only [Nat.cast_ofNat,zero_add,add_assoc] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MomentRigidity
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical consequences of the actual moment exponents. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rewriting the first configuration's sharp moment inequalities in
terms of factor defects yields the manuscript's rigidity conclusion. -/
theorem first_shape_multiplicity_rigidity (a v : ι → ℝ) (r : ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i < 1) (hsum : ∑ i, a i = 1)
    (hlarge : 7/3-2*(∑ i, v i) ≤ r)
    (hmoment : ∀ k : ι → ℕ,
      1/2 ≤ (∑ i, (k i:ℝ)*a i) → (∑ i, (k i:ℝ)*a i) ≤ 2 →
      r+2*(∑ i, (k i:ℝ)*v i) ≤ 2/3+(5/3)*(∑ i, (k i:ℝ)*a i)) :
    (∀ i, v i = 5*a i/6) ∧ r = 2/3 := by
  let d : ι → ℝ := fun i => v i-5*a i/6
  have hd (k : ι → ℕ) : (∑ i, (k i:ℝ)*d i) =
      (∑ i, (k i:ℝ)*v i)-(5/6)*(∑ i, (k i:ℝ)*a i) := by
    calc
      _ = ∑ i, ((k i:ℝ)*v i-(5/6)*((k i:ℝ)*a i)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [d]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib,Finset.mul_sum]
  have hdone : (∑ i, d i) = (∑ i, v i)-5/6 := by
    simpa only [Nat.cast_one,one_mul,hsum,mul_one] using hd (fun _ => 1)
  have hlarge' : 2/3-2*(∑ i, d i) ≤ r := by rw [hdone]; linarith
  have hm : ∀ k : ι → ℕ,
      1/2 ≤ (∑ i, (k i:ℝ)*a i) → (∑ i, (k i:ℝ)*a i) ≤ 2 →
      r ≤ 2/3-2*(∑ i, (k i:ℝ)*d i) := by
    intro k hk₀ hk₁
    rw [hd]
    linarith [hmoment k hk₀ hk₁]
  obtain ⟨hz,hr⟩ := exceptional_multiplicity_rigidity a d r ha hsum hlarge' hm
  refine ⟨?_,hr⟩
  intro i
  have hi := hz i
  dsimp [d] at hi
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorLargeValues
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual large-value rows for the short ideal factors. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finite_power_product_large_values {ι κ : Type*} [Fintype ι]
    (P : Finset κ) (k : ι → ℕ) (F : ι → κ → ℂ) (B : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hrow : ∀ p ∈ P, ∀ i, B i ≤ ‖F i p‖) :
    (P.card:ℝ)*(∏ i, (B i)^(k i))^2 ≤ ∑ p ∈ P, ‖∏ i, (F i p)^(k i)‖^2 := by
  have hprod : 0 ≤ ∏ i, (B i)^(k i) :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (hB i) _)
  calc
    _ = ∑ _p ∈ P, (∏ i, (B i)^(k i))^2 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_prod]
      simp only [norm_pow]
      apply pow_le_pow_left₀ hprod
      exact Finset.prod_le_prod (fun i _ => pow_nonneg (hB i) _)
        (fun i _ => pow_le_pow_left₀ (hB i) (hrow p hp i) _)

theorem HasPowerExponent.finset_prod {ι : Type*} (S : Finset ι)
    {Y : ℕ → ℝ} {f : ι → ℕ → ℝ} {a : ι → ℝ}
    (hf : ∀ i ∈ S, HasPowerExponent Y (f i) (a i))
    (hp : ∀ i ∈ S, ∀ᶠ j in atTop, 0 < f i j) :
    HasPowerExponent Y (fun j => ∏ i ∈ S, f i j) (∑ i ∈ S, a i) := by
  apply (tendsto_finsetSum S hf).congr'
  filter_upwards [(S.eventually_all).mpr hp] with j hj
  rw [Real.log_prod (fun i hi => (hj i hi).ne'),Finset.sum_div]

theorem HasPowerExponent.prod_natPowers {ι : Type*} [Fintype ι]
    (k : ι → ℕ) {Y : ℕ → ℝ} {f : ι → ℕ → ℝ} {a : ι → ℝ}
    (hf : ∀ i, HasPowerExponent Y (f i) (a i))
    (hp : ∀ i, ∀ᶠ j in atTop, 0 < f i j) :
    HasPowerExponent Y (fun j => ∏ i, (f i j)^(k i)) (∑ i, (k i:ℝ)*a i) := by
  apply HasPowerExponent.finset_prod Finset.univ (fun i _ => (hf i).natPow (k i))
  intro i _
  filter_upwards [hp i] with j hj using pow_pos hj _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The first limiting moment inequality follows from the actual
short-factor moment and the actual large-value rows. -/
theorem ShortFactorFamily.cubic_large_values_exponent (F : ShortFactorFamily ι)
    (k : ι → ℕ) {Y N : ℕ → ℝ} (P : ℕ → Finset Eisenstein)
    (B : ℕ → ι → ℝ) {a v : ι → ℝ} {r n : ℝ}
    (hY : Tendsto Y atTop atTop) (hN : ∀ j, 1 ≤ N j)
    (hP : ∀ j, ∀ x ∈ P j, primary x ∧ Squarefree x ∧ norm x ≤ N j)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ x ∈ P j, ∀ i, B j i ≤ ‖F.cubicValue j i x‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hNexp : HasPowerExponent Y N n)
    (hXexp : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hBexp : ∀ i, HasPowerExponent Y (fun j => B j i) (v i)) :
    r+2*(∑ i, (k i:ℝ)*v i) ≤ (∑ i, (k i:ℝ)*a i)+
      max (max n (∑ i, (k i:ℝ)*a i)) ((2/3:ℝ)*(n+∑ i, (k i:ℝ)*a i)) := by
  let L : ℕ → ℝ := fun j => ∏ i, (F.length j i)^(k i)
  let V : ℕ → ℝ := fun j => ∏ i, (B j i)^(k i)
  have hLp : ∀ᶠ j in atTop, 0 < L j := Eventually.of_forall (fun j =>
    Finset.prod_pos (fun i _ => pow_pos (zero_lt_one.trans_le (F.length_ge_one j i)) _))
  have hVp : ∀ᶠ j in atTop, 0 < V j := Eventually.of_forall (fun j =>
    Finset.prod_pos (fun i _ => pow_pos (hB j i) _))
  have hLexp := HasPowerExponent.prod_natPowers k hXexp (fun i =>
    Eventually.of_forall (fun j => zero_lt_one.trans_le (F.length_ge_one j i)))
  have hVexp := HasPowerExponent.prod_natPowers k hBexp (fun i =>
    Eventually.of_forall (fun j => hB j i))
  apply cubic_moment_exponent hY
    (Eventually.of_forall (fun j => Nat.cast_pos.mpr (Finset.card_pos.mpr (hPne j)))) hVp
    (Eventually.of_forall (fun j => zero_lt_one.trans_le (hN j))) hLp
    hRexp hVexp hNexp hLexp
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := shortFactor_multiplicity_power k hε
  refine ⟨C,hC,Eventually.of_forall (fun j => ?_)⟩
  exact (finite_power_product_large_values (P j) k (F.cubicValue j) (B j)
    (fun i => (hB j i).le) (hrow j)).trans
    (hbound (F.cutoff j) (F.length j) (F.coefficient j) (F.twist j)
      (F.factor_spec j) (F.length_ge_one j) (F.twist_bound j) (P j) (N j) (hN j) (hP j))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExceptionalRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rigidity and contradiction for actual short-factor large-value rows. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem ShortFactorFamily.length_exponent_nonneg {ι : Type*}
    (F : ShortFactorFamily ι) {Y : ℕ → ℝ} {a : ι → ℝ}
    (hY : Tendsto Y atTop atTop)
    (hX : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i)) (i : ι) :
    0 ≤ a i :=
  (HasPowerExponent.const hY 1).mono (hX i) hY
    (Eventually.of_forall (fun _ => zero_lt_one))
    (Eventually.of_forall (fun j => F.length_ge_one j i))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual first-configuration short factors and their sharp moments force
all values to have exponent `5/6` of their length and exactly `2/3` rows. -/
theorem ShortFactorFamily.cubic_rows_rigidity (F : ShortFactorFamily ι)
    {Y N : ℕ → ℝ} (P : ℕ → Finset Eisenstein) (B : ℕ → ι → ℝ)
    {a v : ι → ℝ} {r : ℝ}
    (hY : Tendsto Y atTop atTop) (hN : ∀ j, 1 ≤ N j)
    (hP : ∀ j, ∀ x ∈ P j, primary x ∧ Squarefree x ∧ norm x ≤ N j)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ x ∈ P j, ∀ i, B j i ≤ ‖F.cubicValue j i x‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hNexp : HasPowerExponent Y N 1)
    (hXexp : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hBexp : ∀ i, HasPowerExponent Y (fun j => B j i) (v i))
    (ha : ∀ i, a i < 1) (hsum : ∑ i, a i = 1)
    (hlarge : 7/3-2*(∑ i, v i) ≤ r) :
    (∀ i, v i = 5*a i/6) ∧ r = 2/3 := by
  apply first_shape_multiplicity_rigidity a v r
    (fun i => ⟨F.length_exponent_nonneg hY hXexp i,ha i⟩) hsum hlarge
  intro k hk₀ hk₁
  calc
    _ ≤ (∑ i, (k i:ℝ)*a i)+max (max 1 (∑ i, (k i:ℝ)*a i))
        ((2/3:ℝ)*(1+∑ i, (k i:ℝ)*a i)) :=
      F.cubic_large_values_exponent k P B hY hN hP hPne hB hrow hRexp hNexp hXexp hBexp
    _ = _ := by
      convert cubicSieve_exponent hk₀ hk₁ using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedGram
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A smooth majorant in the Gram bound

The majorant needs to be at least one only on the coefficient support.
It may vanish elsewhere. This is the weighted Cauchy step used to pass
from smooth character Gram estimates to finite Dirichlet polynomials.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

theorem weightedFiniteGram_eq {ι κ : Type*} (N : Finset κ) (w : κ → ℝ)
    (T : ι → κ → ℂ) (hw : ∀ n ∈ N, 0 ≤ w n) (p q : ι) :
    weightedFiniteGram N w T p q =
      finiteGram N (fun p n => (Real.sqrt (w n) : ℂ) * T p n) p q := by
  unfold weightedFiniteGram finiteGram
  apply Finset.sum_congr rfl
  intro n hn
  have he : (Real.sqrt (w n) : ℂ)^2 = (w n : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (hw n hn)
  have hs : star (Real.sqrt (w n) : ℂ) = (Real.sqrt (w n) : ℂ) :=
    Complex.conj_ofReal _
  simp only [star_mul, hs]
  linear_combination - T p n * star (T q n) * he

/-- The Gram row bound controls coefficients beneath any nonnegative
smooth majorant which is at least one on their support. -/
theorem weighted_gram_operator_le {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (v : κ → ℂ) (T : ι → κ → ℂ) (w : κ → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hw : ∀ n ∈ N, 0 ≤ w n) (hv : ∀ n ∈ N, v n ≠ 0 → 1 ≤ w n)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, ‖weightedFiniteGram N w T p q‖ ≤ R) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n * T p n‖^2) ≤ R * ∑ n ∈ N, ‖v n‖^2 := by
  let v' : κ → ℂ := fun n => v n / (Real.sqrt (w n) : ℂ)
  let T' : ι → κ → ℂ := fun p n => (Real.sqrt (w n) : ℂ) * T p n
  have hroot (n : κ) (hn : n ∈ N) (hv0 : v n ≠ 0) : 1 ≤ Real.sqrt (w n) := by
    exact Real.one_le_sqrt.mpr (hv n hn hv0)
  have hsame (p : ι) : (∑ n ∈ N, v' n * T' p n) = ∑ n ∈ N, v n * T p n := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hv0 : v n = 0
    · simp [v', T', hv0]
    · have hr : (Real.sqrt (w n) : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (hroot n hn hv0)))
      dsimp [v', T']
      field_simp
  have henergy : (∑ n ∈ N, ‖v' n‖^2) ≤ ∑ n ∈ N, ‖v n‖^2 := by
    apply Finset.sum_le_sum
    intro n hn
    by_cases hv0 : v n = 0
    · simp [v', hv0]
    · apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
      dsimp [v']
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact div_le_self (_root_.norm_nonneg _) (hroot n hn hv0)
  have hr : ∀ p ∈ P, ∑ q ∈ P, ‖finiteGram N T' p q‖ ≤ R := by
    intro p hp
    simpa only [T', ← weightedFiniteGram_eq N w T hw] using hrow p hp
  have h := finite_gram_operator_le P N v' T' hR hr
  simp only [hsame] at h
  exact h.trans (mul_le_mul_of_nonneg_left henergy hR)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicMomentGram
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Gram estimate for a finite cubic-character moment

This supplies the near-orthogonality inequality in the exceptional-character-moment argument
for the actual character polynomials. The only analytic estimate used
here is the cubic Gram theorem.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma primarySieveWeight_nonneg (Z : ℝ) (n : Eisenstein) :
    0 ≤ primarySieveWeight Z n := by
  unfold primarySieveWeight
  split_ifs
  · exact gramLogBump.nonneg
  · exact le_rfl

lemma cutoff_gram_finite (p q : Eisenstein) {Z : ℝ} (hZ : 0 < Z) :
    primaryCharacterGram p q cubicSieveCutoff Z =
      weightedFiniteGram (nonzeroNormBall (2*Z)) (primarySieveWeight Z) cubicSymbol p q := by
  have hzero (n : Eisenstein) (hn : n ∉ nonzeroNormBall (2*Z)) :
      (if primary n then cubicSieveCutoff (norm n/Z)*cubicSymbol p n*
        star (cubicSymbol q n) else 0) = 0 := by
    split_ifs with hp
    · have hn' : 2*Z < norm n := lt_of_not_ge (fun h =>
        hn (mem_nonzeroNormBall.mpr ⟨h,primary_ne_zero hp⟩))
      have hw : cubicSieveCutoff (norm n/Z) = 0 := cubicSieveCutoff_zero (by
        rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hZ.le)]
        exact (le_div_iff₀ hZ).mpr hn'.le)
      simp [hw]
    · rfl
  rw [primaryCharacterGram, tsum_eq_sum hzero]
  unfold weightedFiniteGram
  apply Finset.sum_congr rfl
  intro n hn
  simp only [primarySieveWeight, cubicSieveCutoff]
  split_ifs <;> simp

lemma cutoff_gram_diagonal_le {p : Eisenstein} (hp : primary p)
    {Z : ℝ} (hZ : 0 < Z) :
    ‖primaryCharacterGram p p cubicSieveCutoff Z‖ ≤
      ‖primaryCharacterGram 1 1 cubicSieveCutoff Z‖ := by
  rw [cutoff_gram_finite p p hZ, cutoff_gram_finite 1 1 hZ]
  have he : weightedFiniteGram (nonzeroNormBall (2*Z)) (primarySieveWeight Z)
      cubicSymbol 1 1 = ((∑ n ∈ nonzeroNormBall (2*Z), primarySieveWeight Z n : ℝ) : ℂ) := by
    simp only [weightedFiniteGram, cubicSymbol_one_lower, star_one, mul_one]
    exact (map_sum Complex.ofRealHom _ _).symm
  rw [he, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg (fun n _ => primarySieveWeight_nonneg Z n))]
  calc
    _ ≤ ∑ n ∈ nonzeroNormBall (2*Z),
        ‖(primarySieveWeight Z n : ℂ)*cubicSymbol p n*star (cubicSymbol p n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ nonzeroNormBall (2*Z), primarySieveWeight Z n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real,
        Real.norm_of_nonneg (primarySieveWeight_nonneg Z n)]
      calc
        _ ≤ primarySieveWeight Z n * 1 * 1 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (norm_cubicSymbol_le_one hp n)
              (primarySieveWeight_nonneg Z n))
            (norm_cubicSymbol_le_one hp n) (_root_.norm_nonneg _)
            (by simpa using primarySieveWeight_nonneg Z n)
        _ = _ := by ring

lemma cutoff_gram_row_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (Q : Finset Eisenstein) (P Z : ℝ), 1 ≤ P → 1 ≤ Z →
      (∀ p ∈ Q, gramDyad P p) → ∀ p ∈ Q,
      (∑ q ∈ Q, ‖primaryCharacterGram p q cubicSieveCutoff Z‖) ≤
        D*Z + Real.sqrt ((Q.card : ℝ)*
          (C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ)))) := by
  obtain ⟨C,hC,hgram⟩ := primaryCharacterGram_finite cubicSieveCutoff
    cubicSieveCutoff_compact cubicSieveCutoff_smooth hε
  obtain ⟨D,hD,hdiag⟩ := primaryCharacterGram_one_one_bound cubicSieveCutoff
    cubicSieveCutoff_compact cubicSieveCutoff_smooth.continuous
  refine ⟨C,D,hC,hD,?_⟩
  intro Q P Z hP hZ hQ p hp
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hsquares := hgram (Q.erase p) P Z p hP hZ (hQ p hp)
    (fun q hq => ⟨hQ q (Finset.mem_of_mem_erase hq), (Finset.mem_erase.mp hq).1⟩)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Q.erase p) (fun _ => (1 : ℝ))
    (fun q => ‖primaryCharacterGram p q cubicSieveCutoff Z‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have hcard : ((Q.erase p).card : ℝ) ≤ (Q.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.erase_subset p Q)
  have hB : 0 ≤ C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ)) := by positivity
  have hbound : (∑ q ∈ Q.erase p, ‖primaryCharacterGram p q cubicSieveCutoff Z‖)^2 ≤
      (Q.card : ℝ)*(C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ))) :=
    hc.trans ((mul_le_mul_of_nonneg_left hsquares (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hcard hB))
  have hsqrt : (∑ q ∈ Q.erase p, ‖primaryCharacterGram p q cubicSieveCutoff Z‖) ≤
      Real.sqrt ((Q.card : ℝ)*(C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ)))) := by
    exact (Real.le_sqrt (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) hB)).mpr hbound
  rw [← Finset.add_sum_erase Q (fun q => ‖primaryCharacterGram p q cubicSieveCutoff Z‖) hp]
  exact add_le_add ((cutoff_gram_diagonal_le (hQ p hp).1 hZ0).trans (hdiag Z hZ0)) hsqrt

/-- A concrete smooth majorant converts the proved Gram theorem into a
bound for any finite primary-supported cubic-character polynomial. -/
theorem cubic_moment_gram_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (Q N : Finset Eisenstein) (P Z : ℝ) (v : Eisenstein → ℂ),
      1 ≤ P → 1 ≤ Z → (∀ p ∈ Q, gramDyad P p) →
      (∀ n ∈ N, primary n ∧ norm n ≤ Z) →
      (∑ p ∈ Q, ‖∑ n ∈ N, v n*cubicSymbol p n‖^2) ≤
        (D*Z + Real.sqrt ((Q.card : ℝ)*
          (C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ))))) * ∑ n ∈ N, ‖v n‖^2 := by
  obtain ⟨C,D,hC,hD,hrow⟩ := cutoff_gram_row_le hε
  refine ⟨C,D,hC,hD,?_⟩
  intro Q N P Z v hP hZ hQ hN
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  let M := nonzeroNormBall (2*Z)
  let u : Eisenstein → ℂ := fun n => if n ∈ N then v n else 0
  have hNM : N ⊆ M := by
    intro n hn
    exact mem_nonzeroNormBall.mpr ⟨(hN n hn).2.trans (by linarith),
      primary_ne_zero (hN n hn).1⟩
  have hsum (p : Eisenstein) : (∑ n ∈ M, u n*cubicSymbol p n) =
      ∑ n ∈ N, v n*cubicSymbol p n := by
    calc
      _ = ∑ n ∈ N, u n*cubicSymbol p n :=
        (Finset.sum_subset hNM (fun n _ hnot => by simp [u,hnot])).symm
      _ = _ := Finset.sum_congr rfl (fun n hn => by simp [u,hn])
  have henergy : (∑ n ∈ M, ‖u n‖^2) = ∑ n ∈ N, ‖v n‖^2 := by
    calc
      _ = ∑ n ∈ N, ‖u n‖^2 :=
        (Finset.sum_subset hNM (fun n _ hnot => by simp [u,hnot])).symm
      _ = _ := Finset.sum_congr rfl (fun n hn => by simp [u,hn])
  have hmajor (n : Eisenstein) (hn : n ∈ M) (hu : u n ≠ 0) :
      1 ≤ primarySieveWeight Z n := by
    have hnN : n ∈ N := by by_contra h; exact hu (by simp [u,h])
    have hb : gramLogBump (norm n/Z) = 1 := gramLogBump.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, gramLogBump,
        abs_of_nonneg (div_nonneg (norm_nonneg _) hZ0.le)] using
          (div_le_one hZ0).mpr (hN n hnN).2)
    simp [primarySieveWeight,(hN n hnN).1,hb]
  have h := weighted_gram_operator_le Q M u cubicSymbol (primarySieveWeight Z)
    (R := D*Z + Real.sqrt ((Q.card : ℝ)*(C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ)))))
    (by positivity) (fun n _ => primarySieveWeight_nonneg Z n) hmajor
    (fun p hp => by
      simpa only [M, ← cutoff_gram_finite _ _ hZ0] using hrow Q P Z hP hZ hQ p hp)
  simpa only [hsum,henergy] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramLargeValues
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Large values from the cubic Gram bound

Eliminating the row count from the square root preserves the saving in
the near-orthogonality argument. No large-value estimate is assumed.
-/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma gram_scalar_large_values {R L E A B : ℝ}
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : R*L^2 ≤ E*(A + Real.sqrt (R*B))) :
    R*L^4 ≤ 2*E*A*L^2 + E^2*B := by
  have hs := Real.sq_sqrt (mul_nonneg hR hB)
  have hs0 := Real.sqrt_nonneg (R*B)
  by_cases hsmall : R*L^2 ≤ E*A
  · have hmul := mul_le_mul_of_nonneg_right hsmall (sq_nonneg L)
    have ha := mul_nonneg (mul_nonneg hE hA) (sq_nonneg L)
    nlinarith [mul_nonneg (sq_nonneg E) hB]
  · have hdiff : 0 ≤ R*L^2-E*A := by linarith
    have hupper : R*L^2-E*A ≤ E*Real.sqrt (R*B) := by nlinarith
    have hsquare := pow_le_pow_left₀ hdiff hupper 2
    have hraw : R*(R*L^4-2*E*A*L^2-E^2*B) ≤ 0 := by
      nlinarith [sq_nonneg (E*A)]
    rcases hR.eq_or_lt with hr | hr
    · have hz : R = 0 := hr.symm
      rw [hz, zero_mul]
      exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hE) hA)
        (sq_nonneg L)) (mul_nonneg (sq_nonneg E) hB)
    · exact le_of_not_gt (fun hbad => (not_lt_of_ge hraw)
        (mul_pos hr (by linarith)))

/-- All rows exceeding `L` force an explicit cardinality bound. This
is the finite large-value inequality needed before taking exponents. -/
theorem cubic_gram_large_value_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (Q N : Finset Eisenstein) (P Z L E : ℝ) (v : Eisenstein → ℂ),
      1 ≤ P → 1 ≤ Z → 0 < L → 0 ≤ E →
      (∀ p ∈ Q, gramDyad P p) →
      (∀ n ∈ N, primary n ∧ norm n ≤ Z) →
      (∑ n ∈ N, ‖v n‖^2) ≤ E →
      (∀ p ∈ Q, L ≤ ‖∑ n ∈ N, v n*cubicSymbol p n‖) →
      (Q.card : ℝ)*L^4 ≤ 2*E*(D*Z)*L^2 +
        E^2*(C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ))) := by
  obtain ⟨C,D,hC,hD,hgram⟩ := cubic_moment_gram_bound hε
  refine ⟨C,D,hC,hD,?_⟩
  intro Q N P Z L E v hP hZ hL hE hQ hN henergy hlarge
  have hlow : (Q.card : ℝ)*L^2 ≤ ∑ p ∈ Q, ‖∑ n ∈ N, v n*cubicSymbol p n‖^2 := by
    calc
      _ = ∑ _p ∈ Q, L^2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun p hp => pow_le_pow_left₀ hL.le (hlarge p hp) 2)
  apply gram_scalar_large_values (Nat.cast_nonneg _) hE (by positivity) (by positivity)
  have hmono := mul_le_mul_of_nonneg_left henergy
    (show 0 ≤ D*Z + Real.sqrt ((Q.card : ℝ)*
      (C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ)))) from by positivity)
  exact hlow.trans ((hgram Q N P Z v hP hZ hQ hN).trans
    (by simpa only [mul_comm E] using hmono))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorGram
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated short factors in the final Gram estimate. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma shortRepeatedSupport_mem {m : ℕ} {X : ℝ} {b : Eisenstein}
    (hb : b ∈ shortRepeatedSupport m X) : primary b ∧ norm b ≤ X^m := by
  refine ⟨orderedPrimarySupport_primary _ (fun _ _ hn =>
    (mem_primaryElementBall.mp hn).1) hb,?_⟩
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  rw [norm_finset_prod]
  calc
    _ ≤ ∏ _i : Fin m, X := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i _ => (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hf i)).2)
    _ = _ := by simp

lemma shortRepeated_polynomial (m : ℕ) (X : ℝ) (A : EisensteinArithmeticFunction)
    (u : Eisenstein → ℂ) {a : Eisenstein} (ha : primary a) :
    (∑ b ∈ shortRepeatedSupport m X,
      shortRepeatedCoefficient m X A u b*cubicSymbol a b) =
      (primaryIdealPolynomial X A (fun n => u n*cubicSymbol a n))^m := by
  rw [shortRepeatedSupport,shortRepeatedCoefficient,← primeCubicProductPolynomial_eq _ _ ha]
  simp only [primeCubicProductPolynomial,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    primaryIdealPolynomial_eq_elements,mul_assoc]

/-- The actual coefficient energy has only an arbitrarily small power loss;
all logarithmic weights and repeated factorizations are included. -/
theorem shortRepeated_energy (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F X : ℝ) (A : EisensteinArithmeticFunction)
      (u : Eisenstein → ℂ), ShortArithmeticFactor F A → 1 ≤ X →
      (∀ n ∈ primaryElementBall X, ‖u n‖ ≤ 1) →
      (∑ b ∈ shortRepeatedSupport m X, ‖shortRepeatedCoefficient m X A u b‖^2) ≤
        C*(X^m)^(1+ε) := by
  obtain ⟨C,hC,henergy⟩ := primary_orderedConvolution_energy (ι := Fin m)
    (show 0 < ε/2 by positivity)
  obtain ⟨B,hB,hlog⟩ := one_add_log_small_power (show 0 < ε/4 by positivity)
  refine ⟨C*(18*B^2)^m,by positivity,?_⟩
  intro F X A u hA hX hu
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 1 ≤ X^m := one_le_pow₀ hX
  have htuple (f : Fin m → Eisenstein)
      (hf : f ∈ Fintype.piFinset (fun _ : Fin m => primaryElementBall X)) :
      norm (∏ i, f i) ≤ X^m := by
    rw [norm_finset_prod]
    calc
      _ ≤ ∏ _i : Fin m, X := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun i _ => (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hf i)).2)
      _ = _ := by simp
  have he := henergy (fun _ : Fin m => primaryElementBall X)
    (fun _ n => ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*u n)
    (fun _ _ hn => (mem_primaryElementBall.mp hn).1) (X^m) hL htuple
  have hfactor := shortArithmeticFactor_energy hA hX u hu
  have hlog2 : (1+Real.log X)^2 ≤ B^2*X^(ε/2) := by
    have h := pow_le_pow_left₀ (by linarith [Real.log_nonneg hX]) (hlog X hX) 2
    rw [mul_pow,← Real.rpow_mul_natCast hXp.le] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  have hfactor' : (∑ n ∈ primaryElementBall X,
      ‖((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*u n‖^2) ≤
      (18*B^2)*X^(1+ε/2) := by
    apply hfactor.trans
    calc
      _ ≤ 18*X*(B^2*X^(ε/2)) := mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ = _ := by rw [Real.rpow_add hXp,Real.rpow_one]; ring
  apply he.trans
  simp only [primeConvolutionEnergy,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  calc
    _ ≤ C*(X^m)^(ε/2)*((18*B^2)*X^(1+ε/2))^m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hfactor' m) (by positivity)
    _ = (C*(18*B^2)^m)*(X^m)^(1+ε) := by
      have hp : (X^(1+ε/2))^m = (X^m)^(1+ε/2) := by
        rw [← Real.rpow_mul_natCast hXp.le,← Real.rpow_natCast_mul hXp.le]
        congr 1
        ring
      have heps : (X^m)^(ε/2)*(X^m)^(1+ε/2) = (X^m)^(1+ε) := by
        rw [← Real.rpow_add (pow_pos hXp m)]
        congr 1
        ring
      rw [mul_pow,hp]
      calc
        _ = (C*(18*B^2)^m)*((X^m)^(ε/2)*(X^m)^(1+ε/2)) := by ring
        _ = _ := by rw [heps]

/-- Applying the proved Gram theorem to the literal copied factor gives
an exact finite large-value inequality with its true coefficient energy. -/
theorem shortRepeated_gram_large_values (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C D E : ℝ, 0 < C ∧ 0 < D ∧ 0 < E ∧
      ∀ (F X P V : ℝ) (A : EisensteinArithmeticFunction) (u : Eisenstein → ℂ)
        (Q : Finset Eisenstein), ShortArithmeticFactor F A → 1 ≤ X → 1 ≤ P → 0 < V →
        (∀ n ∈ primaryElementBall X, ‖u n‖ ≤ 1) →
        (∀ p ∈ Q, gramDyad P p) →
        (∀ p ∈ Q, V ≤ ‖primaryIdealPolynomial X A
          (fun n => u n*cubicSymbol p n)‖^m) →
        (Q.card:ℝ)*V^4 ≤ 2*(E*(X^m)^(1+ε))*(D*(X^m))*V^2+
          (E*(X^m)^(1+ε))^2*
            (C*(P*(X^m))^ε*(X^m)*(P+(P^3/(X^m))^(2/3:ℝ))) := by
  obtain ⟨C,D,hC,hD,hgram⟩ := cubic_gram_large_value_count hε
  obtain ⟨E,hE,henergy⟩ := shortRepeated_energy m hε
  refine ⟨C,D,E,hC,hD,hE,?_⟩
  intro F X P V A u Q hA hX hP hV hu hQ hlarge
  apply hgram Q (shortRepeatedSupport m X) P (X^m) V (E*(X^m)^(1+ε))
    (shortRepeatedCoefficient m X A u) hP (one_le_pow₀ hX) hV (by positivity) hQ
    (fun _ hb => shortRepeatedSupport_mem hb) (henergy F X A u hA hX hu)
  intro p hp
  rw [shortRepeated_polynomial m X A u (hQ p hp).1,norm_pow]
  exact hlarge p hp


lemma HasPowerExponent.const_mul {Y f : ℕ → ℝ} {a C : ℝ}
    (hf : HasPowerExponent Y f a) (hY : Tendsto Y atTop atTop) (hC : 0 < C)
    (hfp : ∀ᶠ j in atTop, 0 < f j) :
    HasPowerExponent Y (fun j => C*f j) a := by
  simpa only [zero_add] using (HasPowerExponent.const hY C).mul hf
    (Eventually.of_forall (fun _ => hC)) hfp

lemma HasPowerExponent.div {Y f g : ℕ → ℝ} {a b : ℝ}
    (hf : HasPowerExponent Y f a) (hg : HasPowerExponent Y g b)
    (hfp : ∀ᶠ j in atTop, 0 < f j) (hgp : ∀ᶠ j in atTop, 0 < g j) :
    HasPowerExponent Y (fun j => f j/g j) (a-b) := by
  apply (hf.sub hg).congr'
  filter_upwards [hfp,hgp] with j hfj hgj
  rw [Real.log_div hfj.ne' hgj.ne',sub_div]

private lemma remove_gram_loss {a b c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ b+ε*c) : a ≤ b := by
  by_contra hab
  have hgap : 0 < a-b := sub_pos.mpr (lt_of_not_ge hab)
  let ε : ℝ := (a-b)/(2*(|c|+1))
  have hε : 0 < ε := div_pos hgap (by positivity)
  have he : ε*(2*(|c|+1)) = a-b := div_mul_cancel₀ _ (by positivity)
  have hc := mul_le_mul_of_nonneg_left (le_abs_self c) hε.le
  have hb := h ε hε
  nlinarith [mul_nonneg hε.le (abs_nonneg c)]

/-- The root-free Gram inequality has a strict limiting exponent gap.
This takes limits of the actual finite inequality, including the energy loss. -/
theorem gram_large_values_exponent {Y R V N L : ℕ → ℝ} {r v z : ℝ}
    (hY : Tendsto Y atTop atTop) (hz : 0 ≤ z)
    (hRp : ∀ᶠ j in atTop, 0 < R j) (hVp : ∀ᶠ j in atTop, 0 < V j)
    (hNp : ∀ᶠ j in atTop, 0 < N j) (hLp : ∀ᶠ j in atTop, 0 < L j)
    (hR : HasPowerExponent Y R r) (hV : HasPowerExponent Y V v)
    (hN : HasPowerExponent Y N 1) (hL : HasPowerExponent Y L z)
    (hgram : ∀ ε : ℝ, 0 < ε → ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ᶠ j in atTop, R j*(V j)^4 ≤
        A*(L j)^(2+ε)*(V j)^2+
        B*(L j)^(3+2*ε)*(N j*L j)^ε*
          (N j+((N j)^3/L j)^(2/3:ℝ))) :
    r+4*v ≤ max (2*z+2*v) (3*z+max 1 (2-2*z/3)) := by
  apply remove_gram_loss (c := 1+3*z)
  intro ε hε
  obtain ⟨A,B,hA,hB,hbound⟩ := hgram ε hε
  have hLpow (t : ℝ) : ∀ᶠ j in atTop, 0 < (L j)^t := by
    filter_upwards [hLp] with j hj using Real.rpow_pos_of_pos hj _
  have hV2p : ∀ᶠ j in atTop, 0 < (V j)^2 := by
    filter_upwards [hVp] with j hj using sq_pos_of_pos hj
  have hV4p : ∀ᶠ j in atTop, 0 < (V j)^4 := by
    filter_upwards [hVp] with j hj using pow_pos hj _
  have hNLp : ∀ᶠ j in atTop, 0 < N j*L j := by
    filter_upwards [hNp,hLp] with j hn hl using mul_pos hn hl
  have hdualP : ∀ᶠ j in atTop, 0 < ((N j)^3/L j)^(2/3:ℝ) := by
    filter_upwards [hNp,hLp] with j hn hl
    exact Real.rpow_pos_of_pos (div_pos (pow_pos hn _) hl) _
  have hinnerP : ∀ᶠ j in atTop, 0 < N j+((N j)^3/L j)^(2/3:ℝ) := by
    filter_upwards [hNp,hdualP] with j hn hd using add_pos hn hd
  have hinner := hN.add (((hN.natPow 3).div hL
    (by filter_upwards [hNp] with j hn using pow_pos hn _) hLp).rpow
      (by filter_upwards [hNp,hLp] with j hn hl using div_pos (pow_pos hn _) hl) (2/3:ℝ))
        hY hNp hdualP
  have hfirst := ((hL.rpow hLp (2+ε)).mul (hV.natPow 2)
    (hLpow _) hV2p).const_mul hY hA
      (by filter_upwards [hLpow (2+ε),hV2p] with j hl hv using mul_pos hl hv)
  have hprod := ((hL.rpow hLp (3+2*ε)).mul ((hN.mul hL hNp hLp).rpow hNLp ε)
    (hLpow _) (by filter_upwards [hNLp] with j hn using Real.rpow_pos_of_pos hn _))
  have hprodP : ∀ᶠ j in atTop, 0 < (L j)^(3+2*ε)*(N j*L j)^ε := by
    filter_upwards [hLp,hNLp] with j hl hn
    exact mul_pos (Real.rpow_pos_of_pos hl _) (Real.rpow_pos_of_pos hn _)
  have hsecond := (hprod.mul hinner hprodP hinnerP).const_mul hY hB
    (by filter_upwards [hprodP,hinnerP] with j hp hi using mul_pos hp hi)
  have hright := hfirst.add hsecond hY
    (by filter_upwards [hLp,hVp] with j hl hv using
      mul_pos hA (mul_pos (Real.rpow_pos_of_pos hl _) (sq_pos_of_pos hv)))
    (by filter_upwards [hprodP,hinnerP] with j hp hi using mul_pos hB (mul_pos hp hi))
  have h := (hR.mul (hV.natPow 4) hRp hV4p).mono hright hY
    (by filter_upwards [hRp,hV4p] with j hr hv using mul_pos hr hv)
      (by filter_upwards [hbound] with j hj; simpa only [mul_assoc] using hj)
  have hn : (2/3:ℝ)*((3:ℝ)*1-z) = 2-2*z/3 := by norm_num; ring
  simp only [Nat.cast_ofNat,hn] at h
  have h₁ : (2+ε)*z+2*v ≤ max (2*z+2*v) (3*z+max 1 (2-2*z/3))+ε*(1+3*z) := by
    nlinarith [le_max_left (2*z+2*v) (3*z+max 1 (2-2*z/3)),mul_nonneg hε.le hz]
  have h₂ : (3+2*ε)*z+ε*(1+z)+max 1 (2-2*z/3) ≤
      max (2*z+2*v) (3*z+max 1 (2-2*z/3))+ε*(1+3*z) := by
    nlinarith [le_max_right (2*z+2*v) (3*z+max 1 (2-2*z/3))]
  exact h.trans (max_le h₁ h₂)


private lemma gram_energy_group {L : ℝ} (hL : 0 < L) (ε E C D P V T : ℝ) :
    2*(E*L^(1+ε))*(D*L)*V^2+(E*L^(1+ε))^2*(C*(P*L)^ε*L*T) =
      (2*E*D)*L^(2+ε)*V^2+(E^2*C)*L^(3+2*ε)*(P*L)^ε*T := by
  have h₁ : L^(1+ε)*L = L^(2+ε) := by
    nth_rw 2 [← Real.rpow_one L]
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have h₂ : (L^(1+ε))^2*L = L^(3+2*ε) := by
    rw [← Real.rpow_mul_natCast hL.le]
    nth_rw 2 [← Real.rpow_one L]
    rw [← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ = (2*E*D)*(L^(1+ε)*L)*V^2+(E^2*C)*((L^(1+ε))^2*L)*(P*L)^ε*T := by ring
    _ = _ := by rw [h₁,h₂]

/-- A fixed number of copies of an actual short factor satisfies the
limiting Gram inequality; no coefficient-energy exponent is assumed. -/
theorem ShortFactorFamily.copied_rows_gram_exponent {ι : Type*}
    (F : ShortFactorFamily ι) (i : ι) (m : ℕ)
    {Y N : ℕ → ℝ} (P : ℕ → Finset Eisenstein) (B : ℕ → ℝ)
    {r a v : ℝ} (hY : Tendsto Y atTop atTop) (hN : ∀ j, 1 ≤ N j)
    (hP : ∀ j, ∀ p ∈ P j, gramDyad (N j) p)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j, 0 < B j)
    (hrow : ∀ j, ∀ p ∈ P j, B j ≤ ‖F.cubicValue j i p‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hNexp : HasPowerExponent Y N 1)
    (hXexp : HasPowerExponent Y (fun j => F.length j i) a)
    (hBexp : HasPowerExponent Y B v) :
    r+4*((m:ℝ)*v) ≤ max (2*((m:ℝ)*a)+2*((m:ℝ)*v))
      (3*((m:ℝ)*a)+max 1 (2-2*((m:ℝ)*a)/3)) := by
  have hap : 0 ≤ a := (HasPowerExponent.const hY 1).mono hXexp hY
    (Eventually.of_forall (fun _ => zero_lt_one))
    (Eventually.of_forall (fun j => F.length_ge_one j i))
  apply gram_large_values_exponent hY (mul_nonneg (Nat.cast_nonneg _) hap)
    (Eventually.of_forall (fun j => Nat.cast_pos.mpr (Finset.card_pos.mpr (hPne j))))
    (Eventually.of_forall (fun j => pow_pos (hB j) m))
    (Eventually.of_forall (fun j => zero_lt_one.trans_le (hN j)))
    (Eventually.of_forall (fun j => pow_pos (zero_lt_one.trans_le (F.length_ge_one j i)) m))
    hRexp (hBexp.natPow m) hNexp (hXexp.natPow m)
  intro ε hε
  obtain ⟨C,D,E,hC,hD,hE,hgram⟩ := shortRepeated_gram_large_values m hε
  refine ⟨2*E*D,E^2*C,by positivity,by positivity,Eventually.of_forall (fun j => ?_)⟩
  have h := hgram (F.cutoff j) (F.length j i) (N j) ((B j)^m)
    (F.coefficient j i) (F.twist j i) (P j) (F.factor_spec j i)
    (F.length_ge_one j i) (hN j) (pow_pos (hB j) m) (F.twist_bound j i) (hP j)
    (fun p hp => pow_le_pow_left₀ (hB j).le (hrow j p hp) m)
  rwa [gram_energy_group (pow_pos (zero_lt_one.trans_le (F.length_ge_one j i)) m)] at h

/-- The saturated first configuration cannot contain a positive short
factor with a fixed number of copies in the interior Gram range. -/
theorem ShortFactorFamily.copied_rows_gram_contradiction {ι : Type*}
    (F : ShortFactorFamily ι) (i : ι) (m : ℕ)
    {Y N : ℕ → ℝ} (P : ℕ → Finset Eisenstein) (B : ℕ → ℝ)
    {a : ℝ} (hY : Tendsto Y atTop atTop) (hN : ∀ j, 1 ≤ N j)
    (hP : ∀ j, ∀ p ∈ P j, gramDyad (N j) p)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j, 0 < B j)
    (hrow : ∀ j, ∀ p ∈ P j, B j ≤ ‖F.cubicValue j i p‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) (2/3))
    (hNexp : HasPowerExponent Y N 1)
    (hXexp : HasPowerExponent Y (fun j => F.length j i) a)
    (hBexp : HasPowerExponent Y B (5*a/6))
    (hz₀ : 4/3 < (m:ℝ)*a) (hz₁ : (m:ℝ)*a < 2) : False := by
  have h := F.copied_rows_gram_exponent i m P B hY hN hP hPne hB hrow
    hRexp hNexp hXexp hBexp
  let z : ℝ := (m:ℝ)*a
  have hv : (m:ℝ)*(5*a/6) = 5*z/6 := by dsimp [z]; ring
  change 2/3+4*((m:ℝ)*(5*a/6)) ≤ max (2*z+2*((m:ℝ)*(5*a/6)))
    (3*z+max 1 (2-2*z/3)) at h
  rw [hv] at h
  have hgap : max (2*z+2*(5*z/6)) (3*z+max 1 (2-2*z/3)) < 2/3+4*(5*z/6) := by
    apply max_lt
    · change z < 2 at hz₁
      linarith
    · rcases le_total (1:ℝ) (2-2*z/3) with hcase | hcase
      · rw [max_eq_right hcase]
        change 4/3 < z at hz₀
        linarith
      · rw [max_eq_left hcase]
        change 4/3 < z at hz₀
        linarith
  exact not_lt_of_ge h hgap

private lemma exists_positive_short_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i < 1) (hsum : ∑ i, a i = 1) :
    ∃ i, 0 < a i ∧ a i ≤ 1/2 := by
  have hex : ∃ j, 0 < a j := by
    by_contra! h
    have hn := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    linarith
  obtain ⟨j,hj⟩ := hex
  by_cases hjhalf : a j ≤ 1/2
  · exact ⟨j,hj,hjhalf⟩
  have hrest := Finset.sum_erase_add Finset.univ a (Finset.mem_univ j)
  rw [hsum] at hrest
  have hrestpos : 0 < ∑ i ∈ Finset.univ.erase j, a i := by linarith [(ha j).2]
  obtain ⟨i,hi,hipos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun i _ => (ha i).1)).mp hrestpos
  have hile := Finset.single_le_sum (fun i _ => (ha i).1) hi
  exact ⟨i,hipos,by linarith⟩

/-- The complete short-factor contradiction in the first exceptional
configuration. Both the rigidity and the final Gram bound apply to the
literal polynomials defined by the given arithmetic family. -/
theorem ShortFactorFamily.first_rows_contradiction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ShortFactorFamily ι) {Y N : ℕ → ℝ}
    (P : ℕ → Finset Eisenstein) (B : ℕ → ι → ℝ) {a v : ι → ℝ} {r : ℝ}
    (hY : Tendsto Y atTop atTop) (hN : ∀ j, 1 ≤ N j)
    (hP : ∀ j, ∀ p ∈ P j, gramDyad (N j) p)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ p ∈ P j, ∀ i, B j i ≤ ‖F.cubicValue j i p‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hNexp : HasPowerExponent Y N 1)
    (hXexp : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hBexp : ∀ i, HasPowerExponent Y (fun j => B j i) (v i))
    (ha : ∀ i, a i < 1) (hsum : ∑ i, a i = 1)
    (hlarge : 7/3-2*(∑ i, v i) ≤ r) : False := by
  have hNpos : ∀ᶠ j in atTop, 0 < N j :=
    Eventually.of_forall (fun j => zero_lt_one.trans_le (hN j))
  have hN2exp := hNexp.const_mul hY (by norm_num : (0:ℝ) < 2) hNpos
  obtain ⟨hv,hr⟩ := F.cubic_rows_rigidity (N := fun j => 2*N j) P B hY
    (fun j => by linarith [hN j])
    (fun j p hp => ⟨(hP j p hp).1,(hP j p hp).2.1,(hP j p hp).2.2.2.le⟩)
    hPne hB hrow hRexp hN2exp hXexp hBexp ha hsum hlarge
  obtain ⟨i,hi,hihalf⟩ := exists_positive_short_factor a
    (fun i => ⟨F.length_exponent_nonneg hY hXexp i,ha i⟩) hsum
  obtain ⟨m,hm₀,hm₁⟩ := exists_copies_in_gram_range hi hihalf
  apply F.copied_rows_gram_contradiction i m P (fun j => B j i) hY hN hP hPne
    (fun j => hB j i) (fun j p hp => hrow j p hp i)
    (by simpa only [hr] using hRexp) hNexp (hXexp i)
    (by simpa only [hv i] using hBexp i) hm₀ hm₁

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeValueExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite logarithmic pigeonholing and compact extraction of large rows. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Unit-width logarithmic bins have an absolute multiplicative width. -/
lemma logarithmic_bucket {τ x : ℝ} (hτ : 0 < τ) (hx : τ ≤ x) :
    τ*Real.exp (⌊Real.log (x/τ)⌋₊:ℝ) ≤ x ∧
      x ≤ Real.exp 1*(τ*Real.exp (⌊Real.log (x/τ)⌋₊:ℝ)) := by
  have hxp : 0 < x := hτ.trans_le hx
  have hquot : 1 ≤ x/τ := (le_div_iff₀ hτ).mpr (by simpa using hx)
  have hlog : 0 ≤ Real.log (x/τ) := Real.log_nonneg hquot
  have hlo := Real.exp_le_exp.mpr (Nat.floor_le hlog)
  have hhi := Real.exp_le_exp.mpr (Nat.lt_floor_add_one (Real.log (x/τ))).le
  rw [Real.exp_log (div_pos hxp hτ)] at hlo hhi
  rw [Real.exp_add] at hhi
  constructor
  · exact (mul_le_mul_of_nonneg_left hlo hτ.le).trans_eq (mul_div_cancel₀ x hτ.ne')
  · have h := mul_le_mul_of_nonneg_left hhi hτ.le
    rw [mul_div_cancel₀ x hτ.ne'] at h
    nlinarith [Real.exp_pos (⌊Real.log (x/τ)⌋₊:ℝ)]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- An actual finite moment has a nonempty logarithmic box carrying at
least its average energy. The loss is the explicit number of boxes. -/
theorem finite_logarithmic_large_values (S : Finset κ) (f : ι → κ → ℝ)
    {τ U : ℝ} (hτ : 0 < τ)
    (hlo : ∀ x ∈ S, ∀ i, τ ≤ f i x) (hhi : ∀ x ∈ S, ∀ i, f i x ≤ U)
    (hm : 0 < ∑ x ∈ S, (∏ i, f i x)^2) :
    ∃ (P : Finset κ) (B : ι → ℝ), P.Nonempty ∧ P ⊆ S ∧
      (∀ i, τ ≤ B i ∧ B i ≤ U) ∧
      (∀ x ∈ P, ∀ i, B i ≤ f i x ∧ f i x ≤ Real.exp 1*B i) ∧
      (∑ x ∈ S, (∏ i, f i x)^2) ≤
        ((⌊Real.log (U/τ)⌋₊+1:ℕ)^Fintype.card ι:ℝ)*
          (Real.exp 1)^(2*Fintype.card ι)*(P.card:ℝ)*(∏ i, B i)^2 := by
  let K : ℕ := ⌊Real.log (U/τ)⌋₊+1
  let T : Finset (ι → ℕ) := Fintype.piFinset (fun _ => Finset.range K)
  let label : κ → ι → ℕ := fun x i => ⌊Real.log (f i x/τ)⌋₊
  have hTne : T.Nonempty := by
    refine ⟨fun _ => 0,Fintype.mem_piFinset.mpr (fun _ => ?_)⟩
    exact Finset.mem_range.mpr (Nat.zero_lt_succ _)
  have hlabel : ∀ x ∈ S, label x ∈ T := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    apply Real.log_le_log (div_pos (hτ.trans_le (hlo x hx i)) hτ)
    exact div_le_div_of_nonneg_right (hhi x hx i) hτ.le
  have hcard : 0 < (T.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hTne)
  obtain ⟨k,hk,hweight⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    hlabel hTne (show T.card • ((∑ x ∈ S, (∏ i, f i x)^2)/(T.card:ℝ)) ≤
      ∑ x ∈ S, (∏ i, f i x)^2 by
      rw [nsmul_eq_mul,mul_div_cancel₀ _ hcard.ne'])
  let P := S.filter (fun x => label x = k)
  let B : ι → ℝ := fun i => τ*Real.exp (k i:ℝ)
  have hPne : P.Nonempty := by
    by_contra hn
    have he : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change (∑ x ∈ S, (∏ i, f i x)^2)/(T.card:ℝ) ≤ ∑ x ∈ P, (∏ i, f i x)^2 at hweight
    rw [he,Finset.sum_empty] at hweight
    exact (not_lt_of_ge hweight) (div_pos hm hcard)
  have hPsub : P ⊆ S := Finset.filter_subset _ _
  have hrows : ∀ x ∈ P, ∀ i, B i ≤ f i x ∧ f i x ≤ Real.exp 1*B i := by
    intro x hx i
    obtain ⟨hxS,hxk⟩ := Finset.mem_filter.mp hx
    have he : label x i = k i := congrFun hxk i
    have h := logarithmic_bucket hτ (hlo x hxS i)
    simpa only [B,← he,label] using h
  have hB : ∀ i, τ ≤ B i ∧ B i ≤ U := by
    obtain ⟨x,hx⟩ := hPne
    intro i
    refine ⟨?_,(hrows x hx i).1.trans (hhi x (hPsub hx) i)⟩
    change τ ≤ τ*Real.exp (k i:ℝ)
    have he := Real.one_le_exp_iff.mpr (Nat.cast_nonneg (k i))
    nlinarith
  have hbound : ∑ x ∈ P, (∏ i, f i x)^2 ≤
      (P.card:ℝ)*(Real.exp 1)^(2*Fintype.card ι)*(∏ i, B i)^2 := by
    calc
      _ ≤ ∑ _x ∈ P, ((Real.exp 1)^(Fintype.card ι)*(∏ i, B i))^2 := by
        apply Finset.sum_le_sum
        intro x hx
        apply pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => (hτ.trans_le (hlo x (hPsub hx) i)).le))
        have h := Finset.prod_le_prod (s := Finset.univ)
          (fun i _ => (hτ.trans_le (hlo x (hPsub hx) i)).le)
          (fun i _ => (hrows x hx i).2)
        simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] using h
      _ = _ := by
        rw [Finset.sum_const,nsmul_eq_mul,mul_pow,← pow_mul]
        ring
  have htotal : (∑ x ∈ S, (∏ i, f i x)^2) ≤
      (T.card:ℝ)*((P.card:ℝ)*(Real.exp 1)^(2*Fintype.card ι)*(∏ i, B i)^2) := by
    simpa only [mul_comm] using (div_le_iff₀ hcard).mp (hweight.trans hbound)
  refine ⟨P,B,hPne,hPsub,hB,hrows,?_⟩
  have hTc : T.card = K^(Fintype.card ι) := by
    simp [T,Fintype.card_piFinset]
  rw [hTc] at htotal
  dsimp [K] at htotal
  push_cast at htotal ⊢
  convert htotal using 1
  all_goals try with_reducible_and_instances rfl
  ring


private lemma product_le_small_factor (f : ι → ℝ) {τ U : ℝ}
    (hf : ∀ i, 0 ≤ f i) (hU : 1 ≤ U) (hbound : ∀ i, f i ≤ U)
    (i : ι) (hi : f i ≤ τ) : (∏ j, f j) ≤ τ*U^(Fintype.card ι) := by
  have hτ : 0 ≤ τ := (hf i).trans hi
  rw [← Finset.prod_erase_mul Finset.univ f (Finset.mem_univ i)]
  have hprod : (∏ j ∈ Finset.univ.erase i, f j) ≤ U^((Finset.univ.erase i).card) := by
    simpa only [Finset.prod_const] using Finset.prod_le_prod
      (fun j _ => hf j) (fun j _ => hbound j)
  calc
    _ ≤ U^((Finset.univ.erase i).card)*τ := mul_le_mul hprod hi (hf i)
      (pow_nonneg (zero_le_one.trans hU) _)
    _ ≤ U^(Fintype.card ι)*τ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hU (by simpa only [Finset.card_univ] using Finset.card_le_card (Finset.erase_subset i Finset.univ))) hτ
    _ = _ := mul_comm _ _

/-- Rows with an extremely small factor have uniformly negligible total
energy once all other factors have their elementary upper bound. -/
theorem discard_small_factor_moment (S : Finset κ) (f : ι → κ → ℝ)
    {τ U : ℝ} (hU : 1 ≤ U)
    (hf : ∀ x ∈ S, ∀ i, 0 ≤ f i x)
    (hbound : ∀ x ∈ S, ∀ i, f i x ≤ U) :
    (∑ x ∈ S, (∏ i, f i x)^2) ≤
      (∑ x ∈ S with ∀ i, τ ≤ f i x, (∏ i, f i x)^2)+
        (S.card:ℝ)*(τ*U^(Fintype.card ι))^2 := by
  have hbad : (∑ x ∈ S with ¬∀ i, τ ≤ f i x, (∏ i, f i x)^2) ≤
      (S.card:ℝ)*(τ*U^(Fintype.card ι))^2 := by
    calc
      _ ≤ ∑ _x ∈ S.filter (fun x => ¬∀ i, τ ≤ f i x),
          (τ*U^(Fintype.card ι))^2 := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hxS,hxsmall⟩ := Finset.mem_filter.mp hx
        push Not at hxsmall
        obtain ⟨i,hi⟩ := hxsmall
        exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => hf x hxS i))
          (product_le_small_factor (fun i => f i x) (hf x hxS) hU (hbound x hxS) i hi.le) 2
      _ ≤ _ := by
        rw [Finset.sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (sq_nonneg _)
  have he := Finset.sum_filter_add_sum_filter_not S (fun x => ∀ i, τ ≤ f i x)
    (fun x => (∏ i, f i x)^2)
  linarith

/-- Compactness supplies simultaneous limiting exponents of the actual
selected row counts and factor scales. -/
theorem bounded_logarithms_subsequence {δ : Type*} [Finite δ]
    (Y : ℕ → ℝ) (f : δ → ℕ → ℝ) (l u : δ → ℝ)
    (hbound : ∀ j i, l i ≤ Real.log (f i j)/Real.log (Y j) ∧
      Real.log (f i j)/Real.log (Y j) ≤ u i) :
    ∃ (a : δ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, l i ≤ a i ∧ a i ≤ u i) ∧
      ∀ i, HasPowerExponent (Y ∘ φ) (f i ∘ φ) (a i) := by
  let x : ℕ → δ → ℝ := fun j i => Real.log (f i j)/Real.log (Y j)
  have hc : IsCompact {x : δ → ℝ | ∀ i, x i ∈ Set.Icc (l i) (u i)} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨a,ha,φ,hφ,hlim⟩ := hc.tendsto_subseq (fun j i => hbound j i)
  refine ⟨a,φ,hφ,ha,?_⟩
  intro i
  exact (tendsto_pi_nhds.mp hlim) i

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogarithmicLoss
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit loss in logarithmic pigeonholing has exponent zero. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

theorem HasPowerExponent.logarithm {Y : ℕ → ℝ} (hY : Tendsto Y atTop atTop) :
    HasPowerExponent Y (fun j => Real.log (Y j)) 0 := by
  simpa only [HasPowerExponent,Function.comp_def,id_eq] using
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (Real.tendsto_log_atTop.comp hY)

lemma logarithmicBoxLoss_exponent (t : ℕ) {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K)
    {Y : ℕ → ℝ} (hY : Tendsto Y atTop atTop) (hY₁ : ∀ j, 1 < Y j) :
    HasPowerExponent Y (fun j => logarithmicBoxLoss t H K (Y j)) 0 := by
  let c : ℝ := 1+H+K
  have hc : 0 < c := by dsimp [c]; positivity
  have hlogp : ∀ᶠ j in atTop, 0 < Real.log (Y j) :=
    Eventually.of_forall (fun j => Real.log_pos (hY₁ j))
  have hg : HasPowerExponent Y (fun j => 1+c*Real.log (Y j)) 0 := by
    simpa only [max_self] using (HasPowerExponent.const hY 1).add
      ((HasPowerExponent.logarithm hY).const_mul hY hc hlogp) hY
      (Eventually.of_forall (fun _ => zero_lt_one))
      (by filter_upwards [hlogp] with j hj using mul_pos hc hj)
  have hgp : ∀ᶠ j in atTop, 0 < 1+c*Real.log (Y j) := by
    filter_upwards [hlogp] with j hj
    positivity
  have hUpper : HasPowerExponent Y
      (fun j => (Real.exp 1)^(2*t)*(1+c*Real.log (Y j))^t) 0 := by
    simpa only [mul_zero] using (hg.natPow t).const_mul hY (pow_pos (Real.exp_pos _) _) 
      (by filter_upwards [hgp] with j hj using pow_pos hj t)
  have hb (j : ℕ) : 1 ≤ logarithmicBoxLoss t H K (Y j) ∧
      logarithmicBoxLoss t H K (Y j) ≤ (Real.exp 1)^(2*t)*(1+c*Real.log (Y j))^t := by
    have hYp : 0 < Y j := lt_trans zero_lt_one (hY₁ j)
    have hlog : 0 ≤ Real.log (Y j) := (Real.log_pos (hY₁ j)).le
    have he : Real.log ((Y j)^H/(Y j)^(-K)) = (H+K)*Real.log (Y j) := by
      rw [Real.log_div (Real.rpow_pos_of_pos hYp _).ne' (Real.rpow_pos_of_pos hYp _).ne',
        Real.log_rpow hYp,Real.log_rpow hYp]
      ring
    have hn : (1:ℝ) ≤ (⌊Real.log ((Y j)^H/(Y j)^(-K))⌋₊+1:ℕ) := by
      exact_mod_cast Nat.succ_pos _
    have hnu : ((⌊Real.log ((Y j)^H/(Y j)^(-K))⌋₊+1:ℕ):ℝ) ≤
        1+c*Real.log (Y j) := by
      push_cast
      rw [he]
      have hfloor := Nat.floor_le (mul_nonneg (add_nonneg hH hK) hlog)
      dsimp [c]
      nlinarith
    have hpow := one_le_pow₀ hn (n := t)
    have hexp := one_le_pow₀ (Real.one_le_exp_iff.mpr (show (0:ℝ) ≤ 1 by norm_num)) (n := 2*t)
    push_cast at hn hnu hpow
    constructor
    · unfold logarithmicBoxLoss
      push_cast
      nlinarith
    · unfold logarithmicBoxLoss
      push_cast
      have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hn) hnu t)
        (pow_nonneg (Real.exp_pos 1).le (2*t))
      simpa only [mul_comm] using h
  apply (HasPowerExponent.const hY 1).squeeze' hUpper
  · filter_upwards [] with j
    simpa only [Real.log_one,zero_div] using
      div_nonneg (Real.log_nonneg (hb j).1) (Real.log_pos (hY₁ j)).le
  · filter_upwards [] with j
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (zero_lt_one.trans_le (hb j).1) (hb j).2)
      (Real.log_pos (hY₁ j)).le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeValueSubsequence
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A large-value subsequence is extracted from the actual finite moment. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma logarithmic_power_bounds {Y x l u : ℝ} (hY : 1 < Y)
    (hlo : Y^l ≤ x) (hhi : x ≤ Y^u) :
    l ≤ Real.log x/Real.log Y ∧ Real.log x/Real.log Y ≤ u := by
  have hYp : 0 < Y := zero_lt_one.trans hY
  have hxp : 0 < x := (Real.rpow_pos_of_pos hYp l).trans_le hlo
  constructor
  · apply (le_div_iff₀ (Real.log_pos hY)).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hYp l) hlo
    rwa [Real.log_rpow hYp] at h
  · apply (div_le_iff₀ (Real.log_pos hY)).mpr
    have h := Real.log_le_log hxp hhi
    rwa [Real.log_rpow hYp] at h

/-- Uniform elementary bounds and an unsaved moment yield actual selected
rows and simultaneous logarithmic limits. Their exponents satisfy the
large-value inequality, rather than having it as an assumption. -/
theorem extract_large_value_subsequence {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (Y G : ℕ → ℝ) (S : ℕ → Finset κ) (f : ℕ → ι → κ → ℝ)
    {H K D s : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hY : Tendsto Y atTop atTop) (hY₁ : ∀ j, 1 < Y j)
    (hG : ∀ j, 0 < G j) (hGexp : HasPowerExponent Y G s)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ (Y j)^D)
    (hlo : ∀ j, ∀ x ∈ S j, ∀ i, (Y j)^(-K) ≤ f j i x)
    (hhi : ∀ j, ∀ x ∈ S j, ∀ i, f j i x ≤ (Y j)^H)
    (hmoment : ∀ j, G j ≤ ∑ x ∈ S j, (∏ i, f j i x)^2) :
    ∃ (φ : ℕ → ℕ) (P : ℕ → Finset κ) (B : ℕ → ι → ℝ) (r : ℝ) (v : ι → ℝ),
      StrictMono φ ∧ (∀ j, (P j).Nonempty ∧ P j ⊆ S (φ j)) ∧
      (∀ j i, (Y (φ j))^(-K) ≤ B j i ∧ B j i ≤ (Y (φ j))^H) ∧
      (∀ j, ∀ x ∈ P j, ∀ i, B j i ≤ f (φ j) i x ∧
        f (φ j) i x ≤ Real.exp 1*B j i) ∧
      HasPowerExponent (Y ∘ φ) (fun j => ((P j).card:ℝ)) r ∧
      (∀ i, HasPowerExponent (Y ∘ φ) (fun j => B j i) (v i)) ∧
      (0 ≤ r ∧ r ≤ D) ∧ (∀ i, -K ≤ v i ∧ v i ≤ H) ∧ s ≤ r+2*(∑ i, v i) := by
  have hex (j : ℕ) := finite_logarithmic_large_values (S j) (f j)
    (Real.rpow_pos_of_pos (zero_lt_one.trans (hY₁ j)) (-K)) (hlo j) (hhi j)
    ((hG j).trans_le (hmoment j))
  choose P B hPne hPsub hBb hrows hm using hex
  let R : ℕ → ℝ := fun j => ((P j).card:ℝ)
  have hRp (j : ℕ) : 0 < R j := Nat.cast_pos.mpr (Finset.card_pos.mpr (hPne j))
  have hRc (j : ℕ) : R j ≤ (Y j)^D :=
    (Nat.cast_le.mpr (Finset.card_le_card (hPsub j))).trans (hcard j)
  have hRlo (j : ℕ) : (Y j)^(0:ℝ) ≤ R j := by
    rw [Real.rpow_zero]
    change (1:ℝ) ≤ ((P j).card:ℝ)
    exact_mod_cast Finset.one_le_card.mpr (hPne j)
  let g : Option ι → ℕ → ℝ := fun i => match i with | none => R | some i => fun j => B j i
  let l : Option ι → ℝ := fun i => match i with | none => 0 | some _ => -K
  let u : Option ι → ℝ := fun i => match i with | none => D | some _ => H
  have hg : ∀ j i, l i ≤ Real.log (g i j)/Real.log (Y j) ∧
      Real.log (g i j)/Real.log (Y j) ≤ u i := by
    intro j i
    cases i with
    | none => exact logarithmic_power_bounds (hY₁ j) (hRlo j) (hRc j)
    | some i => exact logarithmic_power_bounds (hY₁ j) (hBb j i).1 (hBb j i).2
  obtain ⟨a,φ,hφ,ha,hlim⟩ := bounded_logarithms_subsequence Y g l u hg
  let r := a none
  let v : ι → ℝ := fun i => a (some i)
  have hRlim : HasPowerExponent (Y ∘ φ) (fun j => ((P (φ j)).card:ℝ)) r := hlim none
  have hBlim (i : ι) : HasPowerExponent (Y ∘ φ) (fun j => B (φ j) i) (v i) := hlim (some i)
  have hYφ : Tendsto (Y ∘ φ) atTop atTop := hY.comp hφ.tendsto_atTop
  have hGφ : HasPowerExponent (Y ∘ φ) (G ∘ φ) s := hGexp.comp hφ.tendsto_atTop
  have hcost : HasPowerExponent (Y ∘ φ)
      (fun j => logarithmicBoxLoss (Fintype.card ι) H K (Y (φ j))) 0 :=
    (logarithmicBoxLoss_exponent (Fintype.card ι) hH hK hY hY₁).comp hφ.tendsto_atTop
  have hBpos (j : ℕ) (i : ι) : 0 < B (φ j) i :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans (hY₁ (φ j))) _).trans_le (hBb (φ j) i).1
  have hprod := HasPowerExponent.prod_natPowers (fun _ : ι => 1) hBlim
    (fun i => Eventually.of_forall (fun j => hBpos j i))
  simp only [Nat.cast_one,one_mul,pow_one] at hprod
  have hprodP : ∀ᶠ j in atTop, 0 < ∏ i, B (φ j) i :=
    Eventually.of_forall (fun j => Finset.prod_pos (fun i _ => hBpos j i))
  have hRP : ∀ᶠ j in atTop, 0 < ((P (φ j)).card:ℝ) :=
    Eventually.of_forall (fun j => hRp (φ j))
  have hM := hRlim.mul (hprod.natPow 2) hRP
    (by filter_upwards [hprodP] with j hj using sq_pos_of_pos hj)
  have hcostP : ∀ᶠ j in atTop, 0 < logarithmicBoxLoss (Fintype.card ι) H K (Y (φ j)) :=
    Eventually.of_forall (fun j => by
      unfold logarithmicBoxLoss
      positivity)
  have hboundlim := hcost.mul hM hcostP
    (by filter_upwards [hRP,hprodP] with j hr hp using mul_pos hr (sq_pos_of_pos hp))
  have hexponent := hGφ.mono hboundlim hYφ
    (Eventually.of_forall (fun j => hG (φ j))) (Eventually.of_forall (fun j => by
      have h := (hmoment (φ j)).trans (hm (φ j))
      simpa only [logarithmicBoxLoss,mul_assoc,Function.comp_def] using h))
  refine ⟨φ,fun j => P (φ j),fun j i => B (φ j) i,r,v,hφ,?_,?_,?_,hRlim,hBlim,?_,?_,?_⟩
  · intro j
    exact ⟨hPne (φ j),hPsub (φ j)⟩
  · exact fun j i => hBb (φ j) i
  · exact fun j x hx i => hrows (φ j) x hx i
  · exact ha none
  · exact fun i => ha (some i)
  · simpa only [zero_add,Nat.cast_ofNat] using hexponent

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TruncatedLargeValues
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing tiny factors before extracting the actual large-value rows. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Variable powers have exactly the exponent approached by their powers.
This includes the lower sequences arising from successively smaller saving losses. -/
theorem HasPowerExponent.variable_rpow {Y a : ℕ → ℝ} {s : ℝ}
    (hY : Tendsto Y atTop atTop) (ha : Tendsto a atTop (𝓝 s)) :
    HasPowerExponent Y (fun j => (Y j)^(a j)) s := by
  apply ha.congr'
  filter_upwards [hY.eventually_gt_atTop 1] with j hj
  rw [Real.log_rpow (zero_lt_one.trans hj),mul_div_cancel_right₀ _ (Real.log_pos hj).ne']

private lemma small_factor_power_identity {Y : ℝ} (hY : 0 < Y)
    (D H K : ℝ) (t : ℕ) :
    Y^D*(Y^(-K)*(Y^H)^t)^2 = Y^(D-2*K+2*(t:ℝ)*H) := by
  rw [← Real.rpow_mul_natCast hY.le,← Real.rpow_add hY,
    ← Real.rpow_mul_natCast hY.le,← Real.rpow_add hY]
  congr 1
  ring

/-- The full finite moment retains at least half its lower bound after
removing every row with a tiny factor. The exponent of the cutoff is fixed. -/
theorem retain_large_factor_moment {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset κ) (f : ι → κ → ℝ) {Y G D H K : ℝ}
    (hY : 2 ≤ Y) (hG : 1 ≤ G) (hH : 0 ≤ H)
    (hK : D+2*(Fintype.card ι:ℝ)*H-2*K ≤ -2)
    (hcard : (S.card:ℝ) ≤ Y^D)
    (hf : ∀ x ∈ S, ∀ i, 0 ≤ f i x)
    (hhi : ∀ x ∈ S, ∀ i, f i x ≤ Y^H)
    (hmoment : G ≤ ∑ x ∈ S, (∏ i, f i x)^2) :
    G/2 ≤ ∑ x ∈ S with ∀ i, Y^(-K) ≤ f i x, (∏ i, f i x)^2 := by
  have hY₁ : 1 ≤ Y := by linarith
  have hYp : 0 < Y := by linarith
  have hU : 1 ≤ Y^H := Real.one_le_rpow hY₁ hH
  have hdiscard := discard_small_factor_moment S f (τ := Y^(-K)) hU hf hhi
  have htail : (S.card:ℝ)*(Y^(-K)*(Y^H)^(Fintype.card ι))^2 ≤ 1/4 := by
    calc
      _ ≤ Y^D*(Y^(-K)*(Y^H)^(Fintype.card ι))^2 :=
        mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = Y^(D-2*K+2*(Fintype.card ι:ℝ)*H) := small_factor_power_identity hYp D H K _
      _ ≤ Y^(-2:ℝ) := Real.rpow_le_rpow_of_exponent_le hY₁ (by linarith)
      _ ≤ (2:ℝ)^(-2:ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hY (by norm_num)
      _ = 1/4 := by norm_num [Real.rpow_neg,Real.rpow_two]
  linarith

/-- An unsaved actual moment with boundedly many polynomially bounded
factor amplitudes produces genuine large-value rows and their limiting
exponents. Zero and arbitrarily tiny values are allowed in the input. -/
theorem extract_unsaved_moment_subsequence {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (Y G : ℕ → ℝ) (S : ℕ → Finset κ) (f : ℕ → ι → κ → ℝ)
    {H K D s : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hcut : D+2*(Fintype.card ι:ℝ)*H-2*K ≤ -2)
    (hY : Tendsto Y atTop atTop) (hY₂ : ∀ j, 2 ≤ Y j)
    (hG : ∀ j, 1 ≤ G j) (hGexp : HasPowerExponent Y G s)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ (Y j)^D)
    (hf : ∀ j, ∀ x ∈ S j, ∀ i, 0 ≤ f j i x)
    (hhi : ∀ j, ∀ x ∈ S j, ∀ i, f j i x ≤ (Y j)^H)
    (hmoment : ∀ j, G j ≤ ∑ x ∈ S j, (∏ i, f j i x)^2) :
    ∃ (φ : ℕ → ℕ) (P : ℕ → Finset κ) (B : ℕ → ι → ℝ) (r : ℝ) (v : ι → ℝ),
      StrictMono φ ∧ (∀ j, (P j).Nonempty ∧ P j ⊆ S (φ j)) ∧
      (∀ j i, (Y (φ j))^(-K) ≤ B j i ∧ B j i ≤ (Y (φ j))^H) ∧
      (∀ j, ∀ x ∈ P j, ∀ i, B j i ≤ f (φ j) i x ∧
        f (φ j) i x ≤ Real.exp 1*B j i) ∧
      HasPowerExponent (Y ∘ φ) (fun j => ((P j).card:ℝ)) r ∧
      (∀ i, HasPowerExponent (Y ∘ φ) (fun j => B j i) (v i)) ∧
      (0 ≤ r ∧ r ≤ D) ∧ (∀ i, -K ≤ v i ∧ v i ≤ H) ∧ s ≤ r+2*(∑ i, v i) := by
  let T : ℕ → Finset κ := fun j => (S j).filter (fun x => ∀ i, (Y j)^(-K) ≤ f j i x)
  have hT (j : ℕ) : T j ⊆ S j := Finset.filter_subset _ _
  have hhalf : HasPowerExponent Y (fun j => G j/2) s := by
    have h := hGexp.const_mul hY (by norm_num : (0:ℝ) < 1/2)
      (Eventually.of_forall (fun j => zero_lt_one.trans_le (hG j)))
    simpa only [div_eq_mul_inv,mul_comm,one_mul] using h
  obtain ⟨φ,P,B,r,v,hφ,hP,hB,hrows,hRexp,hBexp,hr,hv,hs⟩ :=
    extract_large_value_subsequence Y (fun j => G j/2) T f hH hK hY
      (fun j => by linarith [hY₂ j]) (fun j => by linarith [hG j]) hhalf
      (fun j => (Nat.cast_le.mpr (Finset.card_le_card (hT j))).trans (hcard j))
      (fun j x hx i => (Finset.mem_filter.mp hx).2 i)
      (fun j x hx i => hhi j x (hT j hx) i)
      (fun j => retain_large_factor_moment (S j) (f j) (hY₂ j) (hG j) hH hcut
        (hcard j) (hf j) (hhi j) (hmoment j))
  exact ⟨φ,P,B,r,v,hφ,fun j => ⟨(hP j).1,(hP j).2.trans (hT (φ j))⟩,
    hB,hrows,hRexp,hBexp,hr,hv,hs⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorSequences
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual all-short families cannot have an unsaved moment sequence. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Compactness produces the length exponents too. Thus the subsequent
moment argument does not assume either the value or the length limits. -/
theorem ShortFactorFamily.lengths_subsequence (F : ShortFactorFamily ι)
    {Y : ℕ → ℝ} {δ : ℝ} (_hY : Tendsto Y atTop atTop) (hY₁ : ∀ j, 1 < Y j)
    (hshort : ∀ j i, F.length j i ≤ (Y j)^(1-δ))
    (htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1) :
    ∃ (φ : ℕ → ℕ) (a : ι → ℝ), StrictMono φ ∧
      (∀ i, 0 ≤ a i ∧ a i ≤ 1-δ) ∧ (∑ i, a i = 1) ∧
      ∀ i, HasPowerExponent (Y ∘ φ) (fun j => F.length (φ j) i) (a i) := by
  have hb (j : ℕ) (i : ι) : 0 ≤ Real.log (F.length j i)/Real.log (Y j) ∧
      Real.log (F.length j i)/Real.log (Y j) ≤ 1-δ :=
    logarithmic_power_bounds (hY₁ j) (by simpa using F.length_ge_one j i) (hshort j i)
  obtain ⟨a,φ,hφ,ha,hexp⟩ := bounded_logarithms_subsequence Y
    (fun i j => F.length j i) (fun _ => 0) (fun _ => 1-δ) hb
  have hprod := HasPowerExponent.prod_natPowers (fun _ : ι => 1) hexp
    (fun i => Eventually.of_forall (fun j => zero_lt_one.trans_le (F.length_ge_one (φ j) i)))
  simp only [Nat.cast_one,one_mul,pow_one] at hprod
  have htotal' : HasPowerExponent (Y ∘ φ) (fun j => ∏ i, F.length (φ j) i) 1 :=
    htotal.comp hφ.tendsto_atTop
  exact ⟨φ,a,hφ,ha,tendsto_nhds_unique hprod htotal',hexp⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorUniform
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform power saving from the proved actual-sequence contradictions. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Multiplicative comparability is enough to identify the total logarithmic
length exponent; the bounded dyadic discrepancy disappears in the limit. -/
lemma HasPowerExponent.of_comparable {Y f : ℕ → ℝ} {C : ℝ}
    (hY : Tendsto Y atTop atTop) (hC : 0 < C)
    (hbound : ∀ᶠ j in atTop, Y j/C ≤ f j ∧ f j ≤ C*Y j) :
    HasPowerExponent Y f 1 := by
  have hbase : HasPowerExponent Y Y 1 := by
    simpa only [Real.rpow_one] using HasPowerExponent.variable_rpow hY
      (tendsto_const_nhds (x := (1:ℝ)))
  have hpos := hY.eventually_gt_atTop 0
  apply (hbase.const_mul hY (inv_pos.mpr hC) hpos).squeeze'
    (hbase.const_mul hY hC hpos)
  · filter_upwards [hbound,hY.eventually_gt_atTop 1] with j hj hYj
    apply div_le_div_of_nonneg_right _ (Real.log_pos hYj).le
    apply Real.log_le_log (mul_pos (inv_pos.mpr hC) (by linarith))
    simpa only [div_eq_mul_inv,mul_comm] using hj.1
  · filter_upwards [hbound,hY.eventually_gt_atTop 1] with j hj hYj
    apply div_le_div_of_nonneg_right _ (Real.log_pos hYj).le
    exact Real.log_le_log ((div_pos (by linarith) hC).trans_le hj.1) hj.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorSize
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The auxiliary size cutoffs in the uniform short-factor estimate are automatic. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma shortFactorPolynomial_uniform_quadratic_size :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ (F X Y : ℝ) (A : EisensteinArithmeticFunction)
      (u : Eisenstein → ℂ), ShortArithmeticFactor F A → 1 ≤ X → X ≤ Y → T ≤ Y →
      (∀ n ∈ primaryElementBall X, ‖u n‖ ≤ 1) →
      ‖primaryIdealPolynomial X A u‖ ≤ Y^2 := by
  obtain ⟨C,hC,hbound⟩ := shortFactorPolynomial_norm_small_power
    (show (0:ℝ) < 1/2 by norm_num)
  refine ⟨max 1 (C^2),le_max_left _ _,?_⟩
  intro F X Y A u hA hX hXY hTY hu
  have hY : 1 ≤ Y := (le_max_left _ _).trans hTY
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hCsq : C^2 ≤ Y := (le_max_right _ _).trans hTY
  have hCroot : C ≤ Real.sqrt Y := (Real.le_sqrt hC.le hYp.le).mpr hCsq
  have hCpow : C ≤ Y^(1/2:ℝ) := by simpa only [Real.sqrt_eq_rpow] using hCroot
  calc
    _ ≤ C*X^(1+(1/2:ℝ)) := hbound F X A hA hX u hu
    _ ≤ C*Y^(1+(1/2:ℝ)) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (zero_le_one.trans hX) hXY (by norm_num)) hC.le
    _ ≤ Y^(1/2:ℝ)*Y^(1+(1/2:ℝ)) := mul_le_mul_of_nonneg_right hCpow
      (Real.rpow_nonneg hYp.le _)
    _ = Y^2 := by rw [← Real.rpow_add hYp]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmoothShortFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructing the actual smooth short-factor family used in the exceptional
moments. Finite characters, norm phases and smooth dyads are explicit. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angularShortFamily_mixedValue {ι : Type*} (ℓ : ℤ) (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hq : ∀ i, q i ≠ 0) (hW : ∀ i x, ‖W i x‖ ≤ 1)
    (hcut : ∀ i x, 2 < x → W i x = 0) (j : ℕ) (i : ι) (p : Eisenstein × Eisenstein) :
    (angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW).mixedValue j i p =
      primaryAngularShortSmoothSum ℓ (A i) p.1 p.2 (q i) (η i) (W i) (X i/2) (t i) := by
  rw [primaryAngularShortSmoothSum_eq_polynomial ℓ (A i) p.1 p.2 (q i) (η i) (W i)
    (by linarith [hX i] : 0 < X i/2) (hcut i)]
  have hx : 2*(X i/2) = X i := by ring
  rw [hx]
  unfold ShortFactorFamily.mixedValue
  change primaryIdealPolynomial (X i) (A i) (fun n =>
    smoothAngularShortTwist ℓ (η i) (W i) (X i) (t i) n*mixedCubic p.1 p.2 n) = _
  congr 1
  funext n
  unfold smoothAngularShortTwist smoothShortTwist
  ring

lemma angularShortFamily_cubicValue {ι : Type*} (ℓ : ℤ) (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hq : ∀ i, q i ≠ 0) (hW : ∀ i x, ‖W i x‖ ≤ 1)
    (hcut : ∀ i x, 2 < x → W i x = 0) (j : ℕ) (i : ι) (a : Eisenstein) :
    (angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW).cubicValue j i a =
      primaryAngularShortSmoothSum ℓ (A i) a 1 (q i) (η i) (W i) (X i/2) (t i) := by
  rw [← angularShortFamily_mixedValue ℓ F X A q η W t hA hX hq hW hcut j i (a,1)]
  unfold ShortFactorFamily.cubicValue ShortFactorFamily.mixedValue
  congr 1
  funext n
  simp only [mixedCubic,cubicSymbol_one_lower,star_one,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_VaryingConductorSequences
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional short-factor contradictions allow conductor scales
with the required limiting exponent, without fixing the scales to exact powers. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- With a fixed gap below length one, an actual first-configuration
moment cannot remain at exponent `7/3`. All subsequences are constructed. -/
theorem ShortFactorFamily.first_varying_conductor_sequence_impossible (F : ShortFactorFamily ι)
    (Y N G : ℕ → ℝ) (S : ℕ → Finset Eisenstein) {δ H D : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hY : Tendsto Y atTop atTop) (hY₂ : ∀ j, 2 ≤ Y j)
    (hG : ∀ j, 1 ≤ G j) (hGexp : HasPowerExponent Y G (7/3))
    (hN : ∀ j, 1 ≤ N j) (hNexp : HasPowerExponent Y N 1)
    (hS : ∀ j, ∀ p ∈ S j, gramDyad (N j) p)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ (Y j)^D)
    (hshort : ∀ j i, F.length j i ≤ (Y j)^(1-δ))
    (htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1)
    (hbound : ∀ j, ∀ p ∈ S j, ∀ i, ‖F.cubicValue j i p‖ ≤ (Y j)^H)
    (hmoment : ∀ j, G j ≤ ∑ p ∈ S j, ‖∏ i, F.cubicValue j i p‖^2) : False := by
  obtain ⟨φ,a,hφ,ha,hasum,haexp⟩ := F.lengths_subsequence hY
    (fun j => by linarith [hY₂ j]) hshort htotal
  let K : ℝ := D/2+(Fintype.card ι:ℝ)*H+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcut : D+2*(Fintype.card ι:ℝ)*H-2*K ≤ -2 := by dsimp [K]; linarith
  have hGφ : HasPowerExponent (Y ∘ φ) (G ∘ φ) (7/3) := hGexp.comp hφ.tendsto_atTop
  obtain ⟨ψ,P,B,r,v,hψ,hP,hB,hrow,hRexp,hVexp,_,_,hlarge⟩ :=
    extract_unsaved_moment_subsequence (Y ∘ φ) (G ∘ φ) (S ∘ φ)
      (fun j i p => ‖F.cubicValue (φ j) i p‖) hH hK hcut
      (hY.comp hφ.tendsto_atTop) (fun j => hY₂ (φ j)) (fun j => hG (φ j)) hGφ
      (fun j => hcard (φ j)) (fun _ _ _ _ => _root_.norm_nonneg _)
      (fun j => hbound (φ j)) (fun j => by simpa only [norm_prod,Function.comp_def] using hmoment (φ j))
  have hYφψ : Tendsto ((Y ∘ φ) ∘ ψ) atTop atTop :=
    (hY.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  apply ((F.comp φ).comp ψ).first_rows_contradiction P B hYφψ
    (fun j => hN (φ (ψ j)))
    (fun j p hp => hS (φ (ψ j)) p ((hP j).2 hp))
    (fun j => (hP j).1)
    (fun j i => (Real.rpow_pos_of_pos (by simpa only [Function.comp_def] using
      (show 0 < Y (φ (ψ j)) by linarith [hY₂ (φ (ψ j))])) _).trans_le (hB j i).1)
    (fun j p hp i => (hrow j p hp i).1) hRexp ((hNexp.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop)
    (fun i => (haexp i).comp hψ.tendsto_atTop) hVexp
    (fun i => lt_of_le_of_lt (ha i).2 (by linarith)) hasum (by linarith)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ConductorNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform exceptional moments hold throughout a fixed open neighborhood
of each exceptional conductor exponent. The neighborhoods are constructed by
contradiction from actual short-factor sequences, not assumed as analytic inputs. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma HasPowerExponent.of_shrinking_window {Y N δ : ℕ → ℝ} {a : ℝ}
    (hY : Tendsto Y atTop atTop) (hY₁ : ∀ j, 1 < Y j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hb : ∀ j, (Y j)^(a-δ j) ≤ N j ∧ N j ≤ (Y j)^(a+δ j)) :
    HasPowerExponent Y N a := by
  have hlo : HasPowerExponent Y (fun j => (Y j)^(a-δ j)) a := by
    apply HasPowerExponent.variable_rpow hY
    simpa only [sub_zero] using tendsto_const_nhds.sub hδ
  have hhi : HasPowerExponent Y (fun j => (Y j)^(a+δ j)) a := by
    apply HasPowerExponent.variable_rpow hY
    simpa only [add_zero] using tendsto_const_nhds.add hδ
  apply hlo.squeeze' hhi
  · filter_upwards with j
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (Real.rpow_pos_of_pos (by linarith [hY₁ j]) _) (hb j).1)
      (Real.log_pos (hY₁ j)).le
  · filter_upwards with j
    exact div_le_div_of_nonneg_right
      (Real.log_le_log ((Real.rpow_pos_of_pos (by linarith [hY₁ j]) _).trans_le
        (hb j).1) (hb j).2) (Real.log_pos (hY₁ j)).le

private theorem neighborhood_saving_of_no_countersequence {T : Type*}
    (scale mass : T → ℝ) (valid : ℝ → T → Prop)
    (hno : ∀ x : ℕ → T, (∀ j : ℕ, valid (1/((j:ℝ)+1)) (x j)) →
      (∀ j : ℕ, (j:ℝ)+2 ≤ scale (x j)) →
      (∀ j : ℕ, (scale (x j))^(7/3-1/((j:ℝ)+1)) ≤ mass (x j)) → False) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ x : T,
      valid κ x → Y₀ ≤ scale x → mass x ≤ (scale x)^(7/3-ε) := by
  by_contra h
  push Not at h
  have hex (j : ℕ) : ∃ x : T, valid (1/((j:ℝ)+1)) x ∧
      (j:ℝ)+2 ≤ scale x ∧ (scale x)^(7/3-1/((j:ℝ)+1)) ≤ mass x := by
    obtain ⟨x,hx,hY,hm⟩ := h (1/((j:ℝ)+1)) (by positivity)
      (1/((j:ℝ)+1)) (by positivity) ((j:ℝ)+2)
    exact ⟨x,hx,hY,hm.le⟩
  choose x hx hY hm using hex
  exact hno x hx hY hm

private lemma neighborhood_scale_tendsto {Y : ℕ → ℝ}
    (hY : ∀ j : ℕ, (j:ℝ)+2 ≤ Y j) : Tendsto Y atTop atTop :=
  tendsto_atTop_mono (fun j => by linarith [hY j])
    (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop)

private lemma neighborhood_lower_exponent {Y : ℕ → ℝ}
    (hY : Tendsto Y atTop atTop) :
    HasPowerExponent Y (fun j => (Y j)^(7/3-1/((j:ℝ)+1))) (7/3) := by
  apply HasPowerExponent.variable_rpow hY
  simpa only [sub_zero] using (tendsto_const_nhds (x := (7/3:ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private lemma neighborhood_lower_ge_one {Y : ℕ → ℝ}
    (hY : ∀ j : ℕ, (j:ℝ)+2 ≤ Y j) (j : ℕ) :
    1 ≤ (Y j)^(7/3-1/((j:ℝ)+1)) := by
  apply Real.one_le_rpow (by linarith [hY j,Nat.cast_nonneg (α := ℝ) j])
  have hdiv : 1/((j:ℝ)+1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cubic_short_neighborhood_power {δ H D C : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ x : ConductorMomentInstance ι Eisenstein,
        cubicNeighborhoodAdmissible δ H D C κ x → Y₀ ≤ x.scale →
          cubicInstanceMoment x.toShortMomentInstance ≤ x.scale^(7/3-ε) := by
  apply neighborhood_saving_of_no_countersequence
    (fun x : ConductorMomentInstance ι Eisenstein => x.scale)
    (fun x => cubicInstanceMoment x.toShortMomentInstance)
    (cubicNeighborhoodAdmissible δ H D C)
  intro x hx hY hm
  let Y : ℕ → ℝ := fun j => (x j).scale
  let N : ℕ → ℝ := fun j => (x j).conductorScale
  let G : ℕ → ℝ := fun j => (Y j)^(7/3-1/((j:ℝ)+1))
  let F := neighborhoodFamily x
  have hYlim : Tendsto Y atTop atTop := neighborhood_scale_tendsto hY
  have hY₂ (j : ℕ) : 2 ≤ Y j := by linarith [hY j,Nat.cast_nonneg (α := ℝ) j]
  have htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1 :=
    HasPowerExponent.of_comparable hYlim hC
      (Eventually.of_forall (fun j => ⟨(hx j).2.1,(hx j).2.2.1⟩))
  have hNexp : HasPowerExponent Y N 1 :=
    HasPowerExponent.of_shrinking_window hYlim (fun j => by linarith [hY₂ j])
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (fun j => (hx j).2.2.2.2.1)
  exact F.first_varying_conductor_sequence_impossible Y N G (fun j => (x j).rows)
    hδ hH hD hYlim hY₂ (neighborhood_lower_ge_one hY)
    (neighborhood_lower_exponent hYlim) (fun j => (hx j).2.2.2.1) hNexp
    (fun j => (hx j).2.2.2.2.2.1) (fun j => (hx j).2.2.2.2.2.2.1)
    (fun j => (hx j).1) htotal (fun j => (hx j).2.2.2.2.2.2.2) hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_AllShortNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conductor-neighborhood savings for the literal short factors,
with cardinality and amplitude bounds derived from their finite supports. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma short_neighborhood_length {X Y δ : ℝ} (hY : 1 ≤ Y) (hδ : 0 ≤ δ)
    (hX : X ≤ Y^(1-δ)) : X ≤ Y := by
  simpa only [Real.rpow_one] using hX.trans
    (Real.rpow_le_rpow_of_exponent_le hY (by linarith : 1-δ ≤ 1))

lemma neighborhood_cubic_card (S : Finset Eisenstein) {Y N : ℝ}
    (hY : 36 ≤ Y) (hN : 1 ≤ N) (hNY : N ≤ Y^2)
    (hS : ∀ p ∈ S, gramDyad N p) : (S.card:ℝ) ≤ Y^4 := by
  have hsub : S ⊆ nonzeroNormBall (2*N) := fun p hp =>
    mem_nonzeroNormBall.mpr ⟨(hS p hp).2.2.2.le,primary_ne_zero (hS p hp).1⟩
  have hc := (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)).trans
    (nonzeroNormBall_card_le (show 0 ≤ 2*N by positivity))
  calc
    _ ≤ 36*N := by linarith
    _ ≤ 36*Y^2 := by gcongr
    _ ≤ Y^2*Y^2 := by gcongr; nlinarith
    _ = _ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem all_short_cubic_neighborhood {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/2 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (F : ShortFactorFamily ι) (j : ℕ) (Y N : ℝ) (S : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) →
      (∀ i, F.length j i ≤ Y^(1-δ)) →
      Y/C ≤ ∏ i, F.length j i → (∏ i, F.length j i) ≤ C*Y →
      (∀ p ∈ S, gramDyad N p) →
      (∑ p ∈ S, ‖∏ i, F.cubicValue j i p‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,ε,hε,T₀,huniform⟩ := cubic_short_neighborhood_power (ι := ι)
    (H := 2) (D := 4) hδ (by norm_num) (by norm_num) hC
  obtain ⟨T,hT,hsize⟩ := shortFactorPolynomial_uniform_quadratic_size
  refine ⟨min κ (1/2),by positivity,min_le_right _ _,ε,hε,max T₀ (max T 36),?_⟩
  intro F j Y N S hY hNlo hNhi hshort hlo hhi hS
  have hYT : T ≤ Y := (le_max_left T 36).trans ((le_max_right _ _).trans hY)
  have hY₁ : 1 ≤ Y := hT.trans hYT
  have hY₃₆ : 36 ≤ Y := (le_max_right T 36).trans ((le_max_right _ _).trans hY)
  have hN : 1 ≤ N := (Real.one_le_rpow hY₁
    (by have := min_le_right κ (1/2); linarith)).trans hNlo
  have hNY : N ≤ Y^2 := by
    simpa only [Real.rpow_two] using hNhi.trans
      (Real.rpow_le_rpow_of_exponent_le hY₁
        (by have := min_le_right κ (1/2); linarith : 1+min κ (1/2) ≤ 2))
  let x : ConductorMomentInstance ι Eisenstein := ⟨⟨Y,F.comp (fun _ => j),S⟩,N⟩
  have hx : cubicNeighborhoodAdmissible δ 2 4 C κ x := by
    refine ⟨hshort,hlo,hhi,hN,⟨?_,?_⟩,hS,?_,?_⟩
    · exact (Real.rpow_le_rpow_of_exponent_le hY₁
        (by have := min_le_left κ (1/2); linarith)).trans hNlo
    · exact hNhi.trans (Real.rpow_le_rpow_of_exponent_le hY₁
        (by have := min_le_left κ (1/2); linarith))
    · change (S.card:ℝ) ≤ Y^(4:ℝ)
      convert neighborhood_cubic_card S hY₃₆ hN hNY hS using 1
      all_goals try with_reducible_and_instances rfl
      norm_num
    · intro p hp i
      change ‖F.cubicValue j i p‖ ≤ Y^(2:ℝ)
      rw [Real.rpow_two]
      apply hsize (F.cutoff j) (F.length j i) Y (F.coefficient j i)
        (fun n => F.twist j i n*cubicSymbol p n) (F.factor_spec j i)
        (F.length_ge_one j i) (short_neighborhood_length hY₁ hδ.le (hshort i)) hYT
      intro n hn
      rw [norm_mul]
      exact (mul_le_mul (F.twist_bound j i n hn) (norm_cubicSymbol_le_one (hS p hp).1 n)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact huniform x hx ((le_max_left _ _).trans hY)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmoothShortNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional-moment machinery applied to constructed smooth factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_all_short_smooth_cubic_neighborhood_oai (ℓ : ℤ) {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/2 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (F Y N : ℝ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
        (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
        (W : ι → ℝ → ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
      (∀ i, X i ≤ Y^(1-δ)) → Y/C ≤ ∏ i, X i → (∏ i, X i) ≤ C*Y →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖∏ i, primaryAngularShortSmoothSum ℓ (A i) a 1 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := all_short_cubic_neighborhood (ι := ι) hδ hC
  refine ⟨κ,hκ,hκhi,ε,hε,T,?_⟩
  intro F Y N X A q η W t P hY hNlo hNhi hA hX hq hW hcut hshort hlo hhi hP
  let K := angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW
  have h := hbound K 0 Y N P hY hNlo hNhi hshort hlo hhi hP
  simpa only [K,angularShortFamily_cubicValue ℓ F X A q η W t hA hX hq hW hcut] using h


end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.angular_all_short_smooth_cubic_neighborhood_oai.{u_1} := @OAI.CubicFirstMoment.angular_all_short_smooth_cubic_neighborhood_oai.{u_1}
