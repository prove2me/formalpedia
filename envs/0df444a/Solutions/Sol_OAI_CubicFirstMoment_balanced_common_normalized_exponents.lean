-- Prove2me | solution 1 for OAI.CubicFirstMoment.balanced_common_normalized_exponents
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:23:05.235989+00:00
-- url     : https://prove2.me/submissions/fb6e0173-4d7c-48bf-8197-c13a8e58f3bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_dominant_balanced_full_factor_neighborhood

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_SieveMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAdditiveSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published additive large-sieve input over the Eisenstein integers

M. N. Huxley, *The large sieve inequality for algebraic number fields*,
Mathematika 15 (1968), 178–187. The precise imaginary-quadratic form used
here is displayed in P. Gao and L. Zhao, *The large sieve with power moduli
in imaginary quadratic number fields*, IJNT 18 (2022), 1713–1733,
arXiv:2101.00811v2, equation (1.2).

This is an explicit hypothesis type. The primitive multiplicative
character inequality is to be derived by finite Gauss expansion and
orthogonality; it is not assumed here.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxleyModulusMass_nonneg (q : Eisenstein) (N : Finset Eisenstein)
    (v : Eisenstein → ℂ) : 0 ≤ huxleyModulusMass q N v := by
  apply tsum_nonneg
  intro h
  split_ifs <;> positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MultiplicativeBessel
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite-character orthogonality step in the ordinary large sieve. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {R : Type*} [CommRing R] [Fintype R]

lemma mulChar_gram (χ ψ : MulChar R ℂ) :
    (∑ x : R, χ x*star (ψ x)) = if χ = ψ then (Fintype.card Rˣ:ℂ) else 0 := by
  simp_rw [MulChar.star_apply',← MulChar.mul_apply]
  by_cases h : χ = ψ
  · subst ψ
    rw [mul_inv_cancel,ite_eq_left rfl]
    exact MulChar.sum_one_eq_card_units
  · rw [ite_eq_right h]
    exact MulChar.sum_eq_zero_of_ne_one (fun he => h (mul_inv_eq_one.mp he))

/-- Bessel inequality for any selected finite set of distinct multiplicative
characters, with the exact unit-group cardinality. -/
theorem mulChar_bessel (C : Finset (MulChar R ℂ)) (v : R → ℂ) :
    (∑ χ ∈ C, ‖∑ x : R, v x*χ x‖^2) ≤
      (Fintype.card Rˣ:ℝ)*∑ x : R, ‖v x‖^2 := by
  apply finite_gram_operator_le C Finset.univ v (fun χ x => χ x)
    (show (0:ℝ) ≤ Fintype.card Rˣ by positivity)
  intro χ hχ
  change (∑ ψ ∈ C, ‖∑ x : R, χ x*star (ψ x)‖) ≤ _
  simp_rw [mulChar_gram]
  simp only [apply_ite, norm_zero, Complex.norm_natCast]
  simp [hχ]

/-- Gauss expansion transfers a character family to its additive sums
without a conductor loss. The hypotheses are finite Fourier identities,
not an analytic large-sieve estimate. -/
theorem gauss_transform_bessel {ι : Type*} (N : Finset ι)
    (C : Finset (MulChar R ℂ)) (v : ι → ℂ)
    (phase : R → ι → ℂ) (t : MulChar R ℂ → ι → ℂ)
    (g : MulChar R ℂ → ℂ)
    (hR : 0 < Fintype.card R)
    (hg : ∀ χ ∈ C, ‖g χ‖^2 = Fintype.card R)
    (htransform : ∀ χ ∈ C, ∀ n ∈ N,
      g χ*t χ n = ∑ x : R, χ x*phase x n) :
    (∑ χ ∈ C, ‖∑ n ∈ N, v n*t χ n‖^2) ≤
      ∑ x : R, ‖∑ n ∈ N, v n*phase x n‖^2 := by
  let S (x : R) := ∑ n ∈ N, v n*phase x n
  have hidentity (χ : MulChar R ℂ) (hχ : χ ∈ C) :
      g χ*(∑ n ∈ N, v n*t χ n) = ∑ x : R, S x*χ x := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ n ∈ N, v n*(∑ x : R, χ x*phase x n) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [← htransform χ hχ n hn]
        ring
      _ = _ := by
        simp only [S,Finset.mul_sum,Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro n hn
        ring
  have hbound := mulChar_bessel C S
  have he : (Fintype.card R:ℝ)*(∑ χ ∈ C, ‖∑ n ∈ N, v n*t χ n‖^2) =
      ∑ χ ∈ C, ‖∑ x : R, S x*χ x‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [← hidentity χ hχ,norm_mul,mul_pow,hg χ hχ]
  have hcard : Fintype.card Rˣ ≤ Fintype.card R :=
    Fintype.card_le_of_injective (fun x : Rˣ => (x:R)) Units.val_injective
  have hnonneg : 0 ≤ ∑ x : R, ‖S x‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hupper := hbound.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hnonneg)
  rw [← he] at hupper
  exact (mul_le_mul_iff_right₀ (by exact_mod_cast hR : (0:ℝ) < Fintype.card R)).mp hupper

/-- The same transfer with the additive side restricted to units. This is the
restriction appearing in the published additive large sieve. -/
theorem gauss_transform_unit_bessel {ι : Type*} (N : Finset ι)
    (C : Finset (MulChar R ℂ)) (v : ι → ℂ)
    (phase : R → ι → ℂ) (t : MulChar R ℂ → ι → ℂ)
    (g : MulChar R ℂ → ℂ)
    (hR : 0 < Fintype.card R)
    (hg : ∀ χ ∈ C, ‖g χ‖^2 = Fintype.card R)
    (htransform : ∀ χ ∈ C, ∀ n ∈ N,
      g χ*t χ n = ∑ x : R, χ x*phase x n) :
    (∑ χ ∈ C, ‖∑ n ∈ N, v n*t χ n‖^2) ≤
      ∑ x : R, if IsUnit x then ‖∑ n ∈ N, v n*phase x n‖^2 else 0 := by
  let phase' (x : R) (n : ι) := if IsUnit x then phase x n else 0
  have ht : ∀ χ ∈ C, ∀ n ∈ N, g χ*t χ n = ∑ x : R, χ x*phase' x n := by
    intro χ hχ n hn
    rw [htransform χ hχ n hn]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hu : IsUnit x
    · simp only [phase',hu,ite_true, if_true]
    · simp only [phase',hu,ite_false, if_false,MulChar.map_nonunit χ hu,zero_mul]
  have h := gauss_transform_bessel N C v phase' t g hR hg ht
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hu : IsUnit x <;> simp [phase',hu]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MixedCharacterSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conductor-by-conductor Gauss transfer for actual squarefree mixed characters. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_mixedGaussFactor {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hsa : Squarefree a) (hsb : Squarefree b) :
    ‖((Real.sqrt (norm (a*b)):ℂ)*(gauss a*star (gauss b)) / mixedCubic a b 3)‖^2 =
      norm (a*b) := by
  rw [norm_div,norm_mul,norm_mul,norm_star,norm_gauss_of_squarefree ha hsa,
    norm_gauss_of_squarefree hb hsb,
    mixedCubic_norm_of_coprime ha hb (primary_coprime_three (primary_mul ha hb))]
  simp only [mul_one,div_one,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (norm_nonneg _)

/-- Each actual primitive mixed cubic character is bounded by the unit-residue
additive energy at the same conductor. No analytic hypothesis is used. -/
theorem mixedCharacter_unit_energy (N : Finset Eisenstein) (v : Eisenstein → ℂ)
    {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hsa : Squarefree a) (hsb : Squarefree b) (hab : IsCoprime a b) :
    ‖∑ n ∈ N, v n*star (mixedCubic a b n)‖^2 ≤ huxleyModulusMass (a*b) N v := by
  have hq : a*b ≠ 0 := mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb)
  let : Finite (Residues (a*b)) := finite_residues hq
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let χ := mixedResidueChar a b ha hb
  let phase (x : Residues (a*b)) (n : Eisenstein) :=
    huxleyPhase (a*b) (residueRepresentative (a*b) x) n
  let t (_ : MulChar (Residues (a*b)) ℂ) (n : Eisenstein) := star (mixedCubic a b n)
  let g (_ : MulChar (Residues (a*b)) ℂ) :=
    ((Real.sqrt (norm (a*b)):ℂ)*(gauss a*star (gauss b)) / mixedCubic a b 3)
  have hcard : (Fintype.card (Residues (a*b)):ℝ) = norm (a*b) := by
    rw [← Nat.card_eq_fintype_card,residues_card hq,normNat_cast]
  have hR : 0 < Fintype.card (Residues (a*b)) := by
    apply Nat.pos_of_ne_zero
    rw [← Nat.card_eq_fintype_card,residues_card hq]
    exact normNat_ne_zero hq
  have hg : ∀ ψ ∈ ({χ} : Finset (MulChar (Residues (a*b)) ℂ)),
      ‖g ψ‖^2 = Fintype.card (Residues (a*b)) := by
    intro ψ hψ
    rw [hcard]
    exact norm_mixedGaussFactor ha hb hsa hsb
  have ht : ∀ ψ ∈ ({χ} : Finset (MulChar (Residues (a*b)) ℂ)), ∀ n ∈ N,
      g ψ*t ψ n = ∑ x : Residues (a*b), ψ x*phase x n := by
    intro ψ hψ n hn
    have he : ψ = χ := Finset.mem_singleton.mp hψ
    subst ψ
    exact (mixedResidueChar_fourier ha hb hsa hsb hab n).symm
  have h := gauss_transform_unit_bessel N {χ} v phase t g hR hg ht
  simp only [Finset.sum_singleton,t] at h
  refine h.trans_eq ?_
  rw [huxleyModulusMass,tsum_fintype]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hu : IsUnit x <;> simp [hu,phase,additiveSievePolynomial]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OrdinaryMixedSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary mixed cubic character sieve, derived from Huxley's additive
large sieve. The only extra loss is the proved arbitrarily small divisor power. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma pairConductor_primary {p : Eisenstein × Eisenstein} (hp : PrimarySquarefreePair p) :
    primary (pairConductor p) := primary_mul hp.1 hp.2.1

lemma pairConductor_squarefree {p : Eisenstein × Eisenstein} (hp : PrimarySquarefreePair p) :
    Squarefree (pairConductor p) := squarefree_mul_iff.mpr ⟨hp.2.2.2.2.isRelPrime,hp.2.2.1,hp.2.2.2.1⟩

/-- A product determines the second factor, so conductor multiplicity is at
most the number of primary squarefree divisors. -/
lemma pairConductor_fiber_card (P : Finset (Eisenstein × Eisenstein))
    (hP : ∀ p ∈ P, PrimarySquarefreePair p) {q : Eisenstein} (hq : primary q) :
    ((P.filter (fun p => pairConductor p = q)).card : ℝ) ≤
      (2:ℝ)^(primaryPrimeFactors q).card := by
  let F := P.filter (fun p => pairConductor p = q)
  let T := P.image Prod.fst
  have hinj : Set.InjOn Prod.fst (↑F : Set (Eisenstein × Eisenstein)) := by
    intro x hx y hy he
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    apply Prod.ext he
    apply mul_left_cancel₀ (primary_ne_zero (hP x hx'.1).1)
    calc
      x.1*x.2 = q := hx'.2
      _ = y.1*y.2 := hy'.2.symm
      _ = x.1*y.2 := by rw [he]
  have hT : ∀ a ∈ T, primary a ∧ Squarefree a := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨(hP p hp).1,(hP p hp).2.2.1⟩
  have hsub : F.image Prod.fst ⊆ T.filter (· ∣ q) := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hp'.1,
      hp'.2 ▸ dvd_mul_right p.1 p.2⟩
  calc
    (F.card:ℝ) = ((F.image Prod.fst).card:ℝ) := by rw [Finset.card_image_iff.mpr hinj]
    _ ≤ ((T.filter (· ∣ q)).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := primary_divisors_card_le T hT hq

/-- Finite collection of the single-conductor energy inequalities. -/
theorem mixedCharacter_energy_collection {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ) (N : Finset Eisenstein)
      (P : Finset (Eisenstein × Eisenstein)), 1 ≤ Q →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ n ∈ N, v n*star (mixedCubic p.1 p.2 n)‖^2) ≤
        K*Q^ε*∑ q ∈ nonzeroNormBall Q, huxleyModulusMass q N v := by
  obtain ⟨K,hK,hweight⟩ := primeDivisorWeight_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro Q N P hQ hP v
  have hmaps : ∀ p ∈ P, pairConductor p ∈ nonzeroNormBall Q := by
    intro p hp
    exact mem_nonzeroNormBall.mpr ⟨(hP p hp).2,
      primary_ne_zero (pairConductor_primary (hP p hp).1)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  let F := P.filter (fun p => pairConductor p = q)
  by_cases hF : F.Nonempty
  · obtain ⟨p,hp⟩ := hF
    have hp' := Finset.mem_filter.mp hp
    have hqp : primary q := hp'.2 ▸ pairConductor_primary (hP p hp'.1).1
    have hqs : Squarefree q := hp'.2 ▸ pairConductor_squarefree (hP p hp'.1).1
    have hqn : norm q ≤ Q := by rw [← hp'.2]; exact (hP p hp'.1).2
    have hcard : (F.card:ℝ) ≤ K*Q^ε :=
      (pairConductor_fiber_card P (fun p hp => (hP p hp).1) hqp).trans
        ((hweight q hqp hqs).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg q) hqn hε.le) hK.le))
    calc
      _ ≤ ∑ _p ∈ F, huxleyModulusMass q N v := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hh := (hP p hp'.1).1
        have hb := mixedCharacter_unit_energy N v hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2
        simpa only [← hp'.2,pairConductor] using hb
      _ = (F.card:ℝ)*huxleyModulusMass q N v := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (huxleyModulusMass_nonneg q N v)
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (∑ p ∈ F, _) ≤ _
    rw [he,Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by linarith) _))
      (huxleyModulusMass_nonneg q N v)

/-- The ordinary large sieve for actual squarefree coprime cubic pairs. Its
sole analytic hypothesis is the cited additive `Q²+Z` inequality. -/
theorem ordinary_mixed_cubic_sieve (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z : ℝ, 1 ≤ Q → 1 ≤ Z →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ n ∈ nonzeroNormBall Z, v n*star (mixedCubic p.1 p.2 n)‖^2) ≤
        C*Q^ε*(Q^2+Z)*∑ n ∈ nonzeroNormBall Z, ‖v n‖^2 := by
  obtain ⟨K,hK,hcollect⟩ := mixedCharacter_energy_collection hε
  obtain ⟨H,hH,hadd⟩ := hHuxley
  refine ⟨K*H,mul_pos hK hH,?_⟩
  intro Q Z hQ hZ P hP v
  apply (hcollect Q (nonzeroNormBall Z) P hQ hP v).trans
  have hh := mul_le_mul_of_nonneg_left (hadd Q Z hQ hZ v)
    (mul_nonneg hK.le (Real.rpow_nonneg (show 0 ≤ Q by linarith) ε))
  dsimp only [huxleySieveMass] at hh
  convert hh using 1 <;> first | rfl | ring

/-- Conjugating the coefficients gives the other character orientation. -/
theorem ordinary_mixed_cubic_sieve_unstar (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z : ℝ, 1 ≤ Q → 1 ≤ Z →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ n ∈ nonzeroNormBall Z, v n*mixedCubic p.1 p.2 n‖^2) ≤
        C*Q^ε*(Q^2+Z)*∑ n ∈ nonzeroNormBall Z, ‖v n‖^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve hHuxley hε
  refine ⟨C,hC,?_⟩
  intro Q Z hQ hZ P hP v
  have h := hbound Q Z hQ hZ P hP (fun n => star (v n))
  simpa only [← star_mul,← star_sum,norm_star,mul_comm] using h

/-- Restriction to an arbitrary finite coefficient support costs nothing. -/
theorem ordinary_mixed_cubic_sieve_finite (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z : ℝ, 1 ≤ Q → 1 ≤ Z →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (B : Finset Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ b ∈ B, b ≠ 0 ∧ norm b ≤ Z) → ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ n ∈ B, v n*mixedCubic p.1 p.2 n‖^2) ≤
        C*Q^ε*(Q^2+Z)*∑ n ∈ B, ‖v n‖^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve_unstar hHuxley hε
  refine ⟨C,hC,?_⟩
  intro Q Z hQ hZ P B hP hB v
  let w (n : Eisenstein) := if n ∈ B then v n else 0
  have hsub : B ⊆ nonzeroNormBall Z := fun n hn =>
    mem_nonzeroNormBall.mpr ⟨(hB n hn).2,(hB n hn).1⟩
  have hsum (p : Eisenstein × Eisenstein) :
      (∑ n ∈ nonzeroNormBall Z, w n*mixedCubic p.1 p.2 n) =
        ∑ n ∈ B, v n*mixedCubic p.1 p.2 n := by
    rw [← Finset.sum_subset hsub (fun n _ hn => by simp [w,hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [w,hn,ite_true, if_true]
  have henergy : (∑ n ∈ nonzeroNormBall Z, ‖w n‖^2) = ∑ n ∈ B, ‖v n‖^2 := by
    rw [← Finset.sum_subset hsub (fun n _ hn => by simp [w,hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [w,hn,ite_true, if_true]
  simpa only [hsum,henergy] using hbound Q Z hQ hZ P hP w

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialMeanValue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ordinary mean values after collecting Eisenstein norms

The input `MontgomeryVaughanBound` is the ordinary Dirichlet-polynomial
mean-square theorem of Montgomery--Vaughan, *Hilbert's inequality*,
J. London Math. Soc. (2) 8 (1974), Corollary 3, p. 75, equation (1.11),
in the form explicitly recorded
in the manuscript as `eq:ordinary-mean-value`.

The deductions below collect the actual Eisenstein norms, record their
multiplicity cost, and preserve an arbitrary fixed angular weight and
an arbitrary translated height. These are the ordinary mean-value steps
in `eq:dispersion-height-small` and `eq:angular-completed-height`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

lemma mellinPhase_add (t u x : ℝ) :
    mellinPhase (t + u) x = mellinPhase t x * mellinPhase u x := by
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean values of the squarefree prime-convolution discrepancy

The ordinary Montgomery--Vaughan input is specialized to the actual
coefficients obtained from independent prime factors.  The full polynomial
factors exactly; removing repeated primes costs the energy already proved
in `RepeatedPrimeSupport`.  The maximum multiplicity of an integer norm is
kept explicit, so no divisor estimate is hidden in this deduction.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma norm_mixedCubic_le_one {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) (b : Eisenstein) :
    ‖mixedCubic q₁ q₂ b‖ ≤ 1 := by
  rw [mixedCubic, norm_mul, norm_star]
  simpa only [mul_one] using
    mul_le_mul (norm_cubicSymbol_le_one h₁ b) (norm_cubicSymbol_le_one h₂ b)
      (_root_.norm_nonneg _) zero_le_one

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedErrorMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The repeated-prime discrepancy is negligible in the balanced
exceptional family. Both its fourth moment and the number of rows are
derived from the actual finite supports. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma balanced_pair_card (P : Finset (Eisenstein × Eisenstein)) {L : ℝ}
    (hL : 0 ≤ L) (hP : ∀ p ∈ P, primary p.1 ∧ primary p.2 ∧
      norm p.1 ≤ L ∧ norm p.2 ≤ L) : (P.card:ℝ) ≤ 324*L^2 := by
  have hsub : P ⊆ (nonzeroNormBall L).product (nonzeroNormBall L) := by
    intro p hp
    obtain ⟨hp₁,hp₂,hN₁,hN₂⟩ := hP p hp
    exact Finset.mem_product.mpr ⟨mem_nonzeroNormBall.mpr ⟨hN₁,primary_ne_zero hp₁⟩,
      mem_nonzeroNormBall.mpr ⟨hN₂,primary_ne_zero hp₂⟩⟩
  calc
    (P.card:ℝ) ≤ ((nonzeroNormBall L).card:ℝ)^2 := by
      have h := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
      simpa only [Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul,pow_two] using h
    _ ≤ (18*L)^2 := pow_le_pow_left₀ (by positivity) (nonzeroNormBall_card_le hL) 2
    _ = _ := by ring

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

/-- Cardinality and the fourth moment force saturation in the balanced
exceptional configuration. -/
theorem balanced_moment_saturation {r v : ℝ}
    (hlarge : 7 / 3 - 2 * v ≤ r) (hcard : r ≤ 2 / 3)
    (hfourth : r + 4 * v ≤ 4) : r = 2 / 3 ∧ v = 5 / 6 := by
  constructor <;> linarith

/-- Repeating an intermediate factor improves the balanced fourth-moment
bound strictly beyond the saturated row count. -/
theorem balanced_extra_factor_gap {z : ℝ} (hz₀ : 1 < z) (hz₁ : z < 2) :
    max (4 / 3) z - 2 * z / 3 < 2 / 3 := by
  rcases le_total (4 / 3 : ℝ) z with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

end CubicFirstMoment
open scoped BigOperators

namespace CubicFirstMoment

/-- In the balanced exceptional configuration, a saturated total value
forces at least one positive-length factor to attain its `5/6` share.
This is the factor that is repeated in the extra-moment argument. -/
theorem exists_balanced_factor {ι : Type*} [Fintype ι]
    (a v : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, v i ≤ a i)
    (ha_sum : ∑ i, a i = 1) (hv_sum : ∑ i, v i = 5 / 6) :
    ∃ i, 0 < a i ∧ 5 * a i / 6 ≤ v i := by
  classical
  by_contra! hn
  have hle (i : ι) : v i ≤ 5 * a i / 6 := by
    by_cases hi : 0 < a i
    · exact (hn i hi).le
    · have hz : a i = 0 := le_antisymm (not_lt.mp hi) (ha i)
      simpa [hz] using hv i
  have hex : ∃ i, 0 < a i := by
    by_contra! h
    have hs : (∑ i, a i) ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    linarith
  obtain ⟨j, hj⟩ := hex
  have hs : (∑ i, v i) < ∑ i, 5 * a i / 6 :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ j, hn j hj⟩
  have heq : (∑ i, 5 * a i / 6) = 5 / 6 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, ha_sum]
    norm_num
  linarith

end CubicFirstMoment

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic properties of the actual compactly supported smooth norm
weights. Passing to logarithmic coordinates realizes every vertical
Mellin line as a Schwartz Fourier transform. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

lemma mellinVerticalSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ t : ℝ) :
    mellinVerticalSchwartz W hW hpos hsm σ t = mellin W (σ + (t : ℂ)*Complex.I) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rfl

theorem smooth_mellin_vertical_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin W) σ := by
  change Integrable (fun t : ℝ => mellin W (σ + (t : ℂ)*Complex.I))
  have hi : Integrable (mellinVerticalSchwartz W hW hpos hsm σ) :=
    (mellinVerticalSchwartz W hW hpos hsm σ).integrable
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  exact (mellinVerticalSchwartz_apply W hW hpos hsm σ t).symm

/-- The Mellin inversion used for a single norm weight, with convergence
and the vertical integral discharged from its actual smooth support. -/
theorem smooth_mellin_inversion (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ)
    {x : ℝ} (hx : 0 < x) : mellinInv σ (mellin W) x = W x :=
  mellinInv_mellin_eq σ W hx (smooth_mellin_convergent W hW hpos hsm.continuous σ)
    (smooth_mellin_vertical_integrable W hW hpos hsm σ) hsm.continuous.continuousAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute sum-integral interchange for the full norm Dirichlet series
in Mellin inversion. No smooth-duality formula is an input. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

/-- The complete smoothed series has the exact Mellin representation on
any line of absolute convergence of its norm Dirichlet series. -/
theorem smooth_mellin_series {ι : Type*} [Countable ι]
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (σ : ℝ)
    (habs : Summable (fun i => ‖a i‖*(N i)^(-σ)))
    {Z : ℝ} (hZ : 0 < Z) :
    (∑' i, a i*W (N i/Z)) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W (σ+(τ:ℂ)*Complex.I) * (Z:ℂ)^(σ+(τ:ℂ)*Complex.I) *
        normDirichletSeries a N (σ+(τ:ℂ)*Complex.I) := by
  let s (τ : ℝ) : ℂ := σ+(τ:ℂ)*Complex.I
  let F (i : ι) (τ : ℝ) : ℂ :=
    (a i*(N i:ℂ)^(-s τ))*((Z:ℂ)^(s τ)*mellin W (s τ))
  have hsre (τ : ℝ) : (s τ).re = σ := by simp [s]
  have hsnre (τ : ℝ) : (-s τ).re = -σ := by simp [hsre]
  have hnorm (i : ι) (τ : ℝ) : ‖F i τ‖ =
      (‖a i‖*(N i)^(-σ))*Z^σ*‖mellin W (s τ)‖ := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i),
      Complex.norm_cpow_eq_rpow_re_of_pos hZ,hsre,hsnre]
    ring
  have hm : Integrable (fun τ => mellin W (s τ)) :=
    smooth_mellin_vertical_integrable W hW hpos hsm σ
  have hFi (i : ι) : Integrable (F i) := by
    have hn0 : (N i:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hN i).ne'
    have hz0 : (Z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
    have : NeZero (N i:ℂ) := ⟨hn0⟩
    have : NeZero (Z:ℂ) := ⟨hz0⟩
    have hs : Continuous s := by dsimp [s]; fun_prop
    have hc : Continuous (F i) :=
      (continuous_const.mul ((differentiable_const_cpow_of_neZero _).continuous.comp hs.neg)).mul
        (((differentiable_const_cpow_of_neZero _).continuous.comp hs).mul
          ((smooth_mellin_entire W hW hpos hsm.continuous).continuous.comp hs))
    exact (hm.norm.const_mul ((‖a i‖*(N i)^(-σ))*Z^σ)).mono'
      hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun τ => (hnorm i τ).le))
  have hsum : Summable (fun i => ∫ τ : ℝ, ‖F i τ‖) := by
    have he (i : ι) : (∫ τ : ℝ, ‖F i τ‖) =
        (‖a i‖*(N i)^(-σ))*(Z^σ*(∫ τ : ℝ, ‖mellin W (s τ)‖)) := by
      simp_rw [hnorm]
      rw [integral_const_mul]
      ring
    simpa only [he] using habs.mul_right (Z^σ*(∫ τ : ℝ, ‖mellin W (s τ)‖))
  have hi := integral_tsum_of_summable_integral_norm hFi hsum
  have hsingle (i : ι) : a i*W (N i/Z) =
      ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F i τ) := by
    rw [← smooth_mellin_inversion W hW hpos hsm σ (div_pos (hN i) hZ),mellinInv]
    simp only [RCLike.real_smul_eq_coe_mul]
    rw [← mul_assoc,mul_comm (a i),mul_assoc,← integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with τ
    rw [mellin_scale_cpow (hN i) hZ]
    dsimp [F,s]
    ring
  calc
    _ = ∑' i, ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F i τ) := tsum_congr hsingle
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∑' i, ∫ τ : ℝ, F i τ) := tsum_mul_left
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, ∑' i, F i τ) := by rw [hi]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with τ
      simp only [F,normDirichletSeries]
      rw [tsum_mul_right]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma idealExponentNorm_mono {ν κ : EisensteinIdealExponent} (h : ν ≤ κ) :
    idealExponentNorm ν ≤ idealExponentNorm κ := by
  rw [← add_tsub_cancel_of_le h, idealExponentNorm_add]
  exact le_mul_of_one_le_right (idealExponentNorm_pos ν).le (idealExponentNorm_ge_one _)

lemma idealZeta_mul_moebiusSeries : idealZeta * idealMoebiusSeries = 1 := by
  rw [mul_comm, idealMoebiusSeries_mul_zeta]

private lemma exponent_fst_le {ν : EisensteinIdealExponent}
    {p : EisensteinIdealExponent × EisensteinIdealExponent}
    (hp : p ∈ Finset.HasAntidiagonal.antidiagonal ν) :
    p.1 ≤ ν := by
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← h]
  exact le_add_of_nonneg_right zero_le

/-- The truncated Möbius inverse agrees with the full inverse on every
divisor of an ideal whose norm is at most the truncation threshold. -/
lemma shortMoebiusResidual_low_norm (F : ℝ) (ν : EisensteinIdealExponent)
    (hν : idealExponentNorm ν ≤ Real.sqrt F) :
    MvPowerSeries.coeff ν (shortMoebiusResidual F) = 0 := by
  have he : MvPowerSeries.coeff ν (shortIdealMoebius F * idealZeta) =
      MvPowerSeries.coeff ν (idealMoebiusSeries * idealZeta) := by
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hn := (idealExponentNorm_mono (exponent_fst_le hp)).trans hν
    simp only [MvPowerSeries.coeff_apply, shortIdealMoebius, ite_eq_left hn]
  change MvPowerSeries.coeff ν (1 - shortIdealMoebius F * idealZeta) = 0
  rw [map_sub, he, idealMoebiusSeries_mul_zeta, sub_self]

/-- Both nonzero factors of the residual must have norm greater than
`sqrt F`; hence its square vanishes throughout the actual norm ball `F`. -/
lemma shortMoebiusResidual_sq_low_norm {F : ℝ} (hF : 0 ≤ F)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν ((shortMoebiusResidual F) ^ 2) = 0 := by
  rw [pow_two, MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hfst : idealExponentNorm p.1 ≤ Real.sqrt F
  · rw [shortMoebiusResidual_low_norm F p.1 hfst, zero_mul]
  · have hsnd : idealExponentNorm p.2 ≤ Real.sqrt F := by
      have hprod : idealExponentNorm p.1 * idealExponentNorm p.2 ≤ F := by
        rw [← idealExponentNorm_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
        exact hν
      have hroot := Real.sqrt_nonneg F
      have hsq := Real.sq_sqrt hF
      by_contra h
      have ha := lt_of_not_ge hfst
      have hb := lt_of_not_ge h
      nlinarith
    rw [shortMoebiusResidual_low_norm F p.2 hsnd, mul_zero]

lemma shortMoebiusResidual_sq_mul_low_norm {F : ℝ} (hF : 0 ≤ F)
    (L : EisensteinArithmeticFunction) (ν : EisensteinIdealExponent)
    (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν ((shortMoebiusResidual F) ^ 2 * L) = 0 := by
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [shortMoebiusResidual_sq_low_norm hF p.1
    ((idealExponentNorm_mono (exponent_fst_le hp)).trans hν), zero_mul]

lemma idealZeta_mul_vonMangoldt : idealZeta * idealVonMangoldt = idealLogNorm := by
  rw [idealVonMangoldt, ← mul_assoc, idealZeta_mul_moebiusSeries, one_mul]

/-- The short Möbius convolution identity throughout the sharp norm ball. -/
theorem short_moebius_identity {F : ℝ} (hF : 0 ≤ F)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      MvPowerSeries.coeff ν
        ((2 * shortIdealMoebius F - shortIdealMoebius F * shortIdealMoebius F * idealZeta) *
          idealLogNorm) := by
  have halg : idealVonMangoldt -
      (2 * shortIdealMoebius F - shortIdealMoebius F * shortIdealMoebius F * idealZeta) *
        (idealZeta * idealVonMangoldt) = (shortMoebiusResidual F) ^ 2 * idealVonMangoldt := by
    unfold shortMoebiusResidual
    ring
  have h := congrArg (MvPowerSeries.coeff ν) halg
  rw [map_sub, idealZeta_mul_vonMangoldt,
    shortMoebiusResidual_sq_mul_low_norm hF idealVonMangoldt ν hν] at h
  exact sub_eq_zero.mp h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMoebiusBounds
attribute [-instance] _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealVonMangoldt
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The convolution definition of ideal von Mangoldt has exactly its usual
prime-power coefficients. This is the arithmetic bridge for prime replacement
in the short Möbius decomposition. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealLogNorm_prime_difference (ν : EisensteinIdealExponent)
    (p : EisensteinIdealPrime) (hp : 1 ≤ ν p) :
    MvPowerSeries.coeff ν idealLogNorm -
        MvPowerSeries.coeff (ν - Finsupp.single p 1) idealLogNorm =
      Real.log (normNat (idealPrimeRepresentative p)) := by
  have hle : Finsupp.single p 1 ≤ ν := Finsupp.single_le_iff.mpr hp
  have he : ν = (ν - Finsupp.single p 1) + Finsupp.single p 1 :=
    (tsub_add_cancel_of_le hle).symm
  change Real.log (idealExponentNorm ν) -
    Real.log (idealExponentNorm (ν - Finsupp.single p 1)) = _
  conv_lhs => lhs; rw [he, idealExponentNorm_add]
  rw [Real.log_mul (idealExponentNorm_pos _).ne' (idealExponentNorm_pos _).ne',
    idealExponentNorm_single, pow_one]
  ring

private lemma coeff_logNorm_finite_nonempty (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) (hS : S.Nonempty) (hν : S ⊆ ν.support) :
    MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius S) =
      if S.card = 1 then ∑ p ∈ S, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty => exact (Finset.not_nonempty_empty hS).elim
  | @insert p S hp ih =>
    have hνp : 1 ≤ ν p := Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp (hν (Finset.mem_insert_self _ _)))
    have he : idealLogNorm * finiteIdealMoebius (insert p S) =
        (idealLogNorm * finiteIdealMoebius S) * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, mul_sub, mul_one, map_sub, MvPowerSeries.X_def,
      MvPowerSeries.coeff_mul_monomial]
    simp only [Finsupp.single_le_iff, ite_eq_left hνp, mul_one]
    by_cases hSE : S = ∅
    · subst S
      simpa [finiteIdealMoebius] using idealLogNorm_prime_difference ν p hνp
    · have hS' : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSE
      have hνS : S ⊆ ν.support := fun q hq => hν (Finset.mem_insert_of_mem hq)
      have hνS' : S ⊆ (ν - Finsupp.single p 1 : EisensteinIdealExponent).support := by
        intro q hq
        apply Finsupp.mem_support_iff.mpr
        have hqp : q ≠ p := ne_of_mem_of_not_mem hq hp
        simpa [Finsupp.tsub_apply, hqp] using Finsupp.mem_support_iff.mp (hνS hq)
      rw [ih ν hS' hνS, ih _ hS' hνS', sub_self]
      have hc : (insert p S).card ≠ 1 := by
        rw [Finset.card_insert_of_notMem hp]
        have := Finset.card_pos.mpr hS'
        omega
      simp [hc]

lemma idealVonMangoldt_coeff_eq_finite (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius ν.support) := by
  rw [idealVonMangoldt, mul_comm idealLogNorm, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hle : a.1 ≤ ν := by
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp ha]
    exact le_add_of_nonneg_right zero_le
  rw [coeff_idealMoebiusSeries_eq_finite ν.support a.1 (Finsupp.support_mono hle)]

/-- The von Mangoldt coefficient is supported precisely on prime-ideal
powers and has weight the logarithm of that prime-ideal norm. -/
lemma idealVonMangoldt_coeff (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      if ν.support.card = 1 then
        ∑ p ∈ ν.support, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  rw [idealVonMangoldt_coeff_eq_finite]
  by_cases hs : ν.support.Nonempty
  · exact coeff_logNorm_finite_nonempty _ _ hs (Finset.Subset.refl _)
  · have hz : ν = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
    subst ν
    simp only [Finsupp.support_zero, finiteIdealMoebius, Finset.prod_empty, mul_one,
      Finset.card_empty, Nat.zero_ne_one, ite_false, if_false]
    change Real.log (idealExponentNorm 0) = 0
    simp [idealExponentNorm, idealExponentGenerator]

lemma idealVonMangoldt_not_prime_power (ν : EisensteinIdealExponent)
    (hν : ν.support.card ≠ 1) :
    MvPowerSeries.coeff ν idealVonMangoldt = 0 := by
  rw [idealVonMangoldt_coeff, ite_eq_right hν]

lemma idealVonMangoldt_coeff_nonneg (ν : EisensteinIdealExponent) :
    0 ≤ MvPowerSeries.coeff ν idealVonMangoldt := by
  rw [idealVonMangoldt_coeff]
  split_ifs
  · apply Finset.sum_nonneg
    intro p hp
    apply Real.log_nonneg
    simpa only [idealExponentNorm_single, pow_one] using
      idealExponentNorm_ge_one (Finsupp.single p 1)
  · exact le_rfl

lemma idealVonMangoldt_coeff_le_logNorm (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt ≤ Real.log (idealExponentNorm ν) := by
  by_cases hc : ν.support.card = 1
  · obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hc
    have hlog : 0 ≤ Real.log (normNat (idealPrimeRepresentative p)) := by
      apply Real.log_nonneg
      simpa only [idealExponentNorm_single, pow_one] using
        idealExponentNorm_ge_one (Finsupp.single p 1)
    have hn : (1 : ℝ) ≤ (ν p : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
    rw [idealVonMangoldt_coeff, ite_eq_left hc, he, Finsupp.support_single _ hp,
      Finset.sum_singleton, idealExponentNorm_single, Real.log_pow]
    exact le_mul_of_one_le_left hlog hn
  · rw [idealVonMangoldt_not_prime_power ν hc]
    exact Real.log_nonneg (idealExponentNorm_ge_one ν)

lemma idealVonMangoldt_coeff_abs_le_logNorm (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν idealVonMangoldt| ≤ Real.log (idealExponentNorm ν) := by
  rw [abs_of_nonneg (idealVonMangoldt_coeff_nonneg ν)]
  exact idealVonMangoldt_coeff_le_logNorm ν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryConvolutionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- The corresponding ordinary mixed-character moment for actual
independent primary factors. Huxley's additive large sieve is the only
published analytic assumption. -/
theorem primaryConvolution_mixed_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ), (∀ i, ∀ a ∈ S i, primary a) →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (Q Y : ℝ), 1 ≤ Q → 1 ≤ Y →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∑ p ∈ P, ‖∏ i, ∑ a ∈ S i, w i a*mixedCubic p.1 p.2 a‖^2) ≤
        C*Q^ε*(Q^2+Y)*(Y^δ*primeConvolutionEnergy S w) := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve_finite hHuxley hε
  obtain ⟨D,hD,henergy⟩ := primary_orderedConvolution_energy (ι := ι) hδ
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro S w hS P Q Y hQ hY hP hprod
  have hH : ∀ b ∈ orderedConvolutionSupport S, b ≠ 0 ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨primary_ne_zero (orderedPrimarySupport_primary S hS hb),?_⟩
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
    exact hprod f hf
  have he : (∑ p ∈ P, ‖∏ i, ∑ a ∈ S i, w i a*mixedCubic p.1 p.2 a‖^2) =
      ∑ p ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        orderedConvolution S w b*mixedCubic p.1 p.2 b‖^2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [orderedConvolution_mixedCubic S w (hP p hp).1.1 (hP p hp).1.2.1]
  rw [he]
  apply (hbound Q Y hQ hY P (orderedConvolutionSupport S) hP hH
    (orderedConvolution S w)).trans
  have h := mul_le_mul_of_nonneg_left (henergy S w hS Y hY hprod)
    (show 0 ≤ C*Q^ε*(Q^2+Y) by positivity)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryMultiplicity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- The same fixed copies in the ordinary mixed-character sieve retain
the exact product of quadratic factor energies. -/
theorem primaryPolynomial_mixed_multiplicity_moment
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ι → ℕ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (X : ι → ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ S i, norm a ≤ X i) →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (Q : ℝ), 1 ≤ Q →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∑ p ∈ P, ‖∏ i, (∑ n ∈ S i, w i n*mixedCubic p.1 p.2 n)^(k i)‖^2) ≤
        C*Q^ε*(Q^2+(∏ i, (X i)^(k i)))*
          ((∏ i, (X i)^(k i))^δ*(∏ i, (∑ n ∈ S i, ‖w i n‖^2)^(k i))) := by
  obtain ⟨C,hC,hbound⟩ := primaryConvolution_mixed_moment
    (ι := Σ i, Fin (k i)) hHuxley hε hδ
  refine ⟨C,hC,?_⟩
  intro S w X hS hX hSX P Q hQ hP
  have hL : 1 ≤ ∏ i, (X i)^(k i) :=
    Finset.one_le_prod (fun i _ => one_le_pow₀ (hX i))
  have h := hbound (fun j => S j.1) (fun j => w j.1) (fun j => hS j.1)
    P Q (∏ i, (X i)^(k i)) hQ hL hP
    (fixed_copies_norm_bound k S X hSX)
  simpa only [primeConvolutionEnergy,Fintype.prod_sigma,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- Actual short-factor mixed moments, with all individual coefficient
energies bounded explicitly. Huxley's additive sieve is the sole input. -/
theorem shortFactor_mixed_multiplicity_moment
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ι → ℕ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ),
      (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ primaryElementBall (X i), ‖u i a‖ ≤ 1) →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (Q : ℝ), 1 ≤ Q →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∑ p ∈ P, ‖∏ i, (primaryIdealPolynomial (X i) (A i)
        (fun n => u i n*mixedCubic p.1 p.2 n))^(k i)‖^2) ≤
        C*Q^ε*(Q^2+(∏ i, (X i)^(k i)))*
          ((∏ i, (X i)^(k i))^δ*(∏ i, (18*X i*(1+Real.log (X i))^2)^(k i))) := by
  obtain ⟨C,hC,hbound⟩ := primaryPolynomial_mixed_multiplicity_moment hHuxley k hε hδ
  refine ⟨C,hC,?_⟩
  intro F X A u hA hX hu P Q hQ hP
  let w : ι → Eisenstein → ℂ := fun i a =>
    ((MvPowerSeries.coeff (idealExponentOf a) (A i):ℝ):ℂ)*u i a
  have h := hbound (fun i => primaryElementBall (X i)) w X
    (fun _ _ ha => (mem_primaryElementBall.mp ha).1)
    hX (fun _ _ ha => (mem_primaryElementBall.mp ha).2) P Q hQ hP
  have henergy : (∏ i, (∑ n ∈ primaryElementBall (X i), ‖w i n‖^2)^(k i)) ≤
      ∏ i, (18*X i*(1+Real.log (X i))^2)^(k i) := by
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro i _
    exact pow_le_pow_left₀ (by positivity)
      (shortArithmeticFactor_energy (hA i) (hX i) (u i) (hu i)) _
  have hL : 0 ≤ ∏ i, (X i)^(k i) :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (zero_le_one.trans (hX i)) _)
  have hLδ : 0 ≤ (∏ i, (X i)^(k i))^δ := Real.rpow_nonneg hL _
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left henergy (by positivity)) (by positivity))
  simpa only [primaryIdealPolynomial_eq_elements,w,mul_assoc] using h'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

 /-- The ordinary mixed moments have the same fully absorbed loss. -/
theorem shortFactor_mixed_multiplicity_power
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ι → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ),
      (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ primaryElementBall (X i), ‖u i a‖ ≤ 1) →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (Q : ℝ), 1 ≤ Q →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∑ p ∈ P, ‖∏ i, (primaryIdealPolynomial (X i) (A i)
        (fun n => u i n*mixedCubic p.1 p.2 n))^(k i)‖^2) ≤
        C*(Q*(∏ i, (X i)^(k i)))^ε*(∏ i, (X i)^(k i))*
          (Q^2+(∏ i, (X i)^(k i))) := by
  obtain ⟨C,hC,hbound⟩ := shortFactor_mixed_multiplicity_moment hHuxley k hε
    (show 0 < ε/2 by linarith)
  obtain ⟨B,hB,hlog⟩ := logarithmic_factor_product k (show 0 < ε/4 by linarith)
  let T : ℝ := ∏ i, (18:ℝ)^(k i)
  have hT : 0 < T := Finset.prod_pos (fun _ _ => by positivity)
  refine ⟨C*T*B^2,by positivity,?_⟩
  intro F X A u hA hX hu P Q hQ hP
  let L : ℝ := ∏ i, (X i)^(k i)
  let G : ℝ := ∏ i, (1+Real.log (X i))^(k i)
  have hL : 1 ≤ L := Finset.one_le_prod (fun i _ => one_le_pow₀ (hX i))
  have hG : 0 ≤ G := Finset.prod_nonneg
    (fun i _ => pow_nonneg (by linarith [Real.log_nonneg (hX i)]) _)
  have hpow : (L^(ε/4))^2 = L^(ε/2) := by
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hL)]
    congr 1
    ring
  have hG2 : G^2 ≤ B^2*L^(ε/2) := by
    have h := pow_le_pow_left₀ hG (hlog X hX) 2
    change G^2 ≤ (B*L^(ε/4))^2 at h
    simpa only [mul_pow,hpow] using h
  have hE : (∏ i, (18*X i*(1+Real.log (X i))^2)^(k i)) = T*L*G^2 := by
    calc
      _ = ∏ i, (18:ℝ)^(k i)*(X i)^(k i)*((1+Real.log (X i))^(k i))^2 := by
        apply Finset.prod_congr rfl
        intro i _
        rw [mul_pow,mul_pow,pow_right_comm]
      _ = _ := by
        rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_pow]
  apply (hbound F X A u hA hX hu P Q hQ hP).trans
  rw [hE]
  change C*Q^ε*(Q^2+L)*(L^(ε/2)*(T*L*G^2)) ≤ _
  calc
    _ ≤ C*Q^ε*(Q^2+L)*(L^(ε/2)*(T*L*(B^2*L^(ε/2)))) := by gcongr
    _ = (C*T*B^2)*(Q*L)^ε*L*(Q^2+L) := by
      have hp : L^(ε/2)*L^(ε/2) = L^ε := by
        rw [← Real.rpow_add (zero_lt_one.trans_le hL)]
        congr 1
        ring
      rw [Real.mul_rpow (zero_le_one.trans hQ) (zero_le_one.trans hL)]
      calc
        _ = (C*T*B^2)*Q^ε*(L^(ε/2)*L^(ε/2))*L*(Q^2+L) := by ring
        _ = _ := by rw [hp]; ring

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

/-- The ordinary mixed-character moment gives the second configuration's
limiting exponent, again by taking limits of actual inequalities. -/
theorem ordinary_moment_exponent {Y R V Q L : ℕ → ℝ} {r v q z : ℝ}
    (hY : Tendsto Y atTop atTop)
    (hRp : ∀ᶠ j in atTop, 0 < R j) (hVp : ∀ᶠ j in atTop, 0 < V j)
    (hQp : ∀ᶠ j in atTop, 0 < Q j) (hLp : ∀ᶠ j in atTop, 0 < L j)
    (hR : HasPowerExponent Y R r) (hV : HasPowerExponent Y V v)
    (hQ : HasPowerExponent Y Q q) (hL : HasPowerExponent Y L z)
    (hmoment : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ j in atTop, R j*(V j)^2 ≤ C*(Q j*L j)^ε*L j*((Q j)^2+L j)) :
    r+2*v ≤ z+max (2*q) z := by
  apply remove_positive_loss (c := q+z)
  intro ε hε
  obtain ⟨C,hC,hm⟩ := hmoment ε hε
  have hQL := hQ.mul hL hQp hLp
  have hQLp : ∀ᶠ j in atTop, 0 < Q j*L j := by
    filter_upwards [hQp,hLp] with j hq hl using mul_pos hq hl
  have hsum := (hQ.natPow 2).add hL hY
    (by filter_upwards [hQp] with j hq using sq_pos_of_pos hq) hLp
  have hleft := hR.mul (hV.natPow 2) hRp
    (by filter_upwards [hVp] with j h using sq_pos_of_pos h)
  have hright := (((HasPowerExponent.const hY C).mul (hQL.rpow hQLp ε)
    (Eventually.of_forall (fun _ => hC))
    (by filter_upwards [hQLp] with j h using Real.rpow_pos_of_pos h _)).mul hL
    (by filter_upwards [hQLp] with j h using mul_pos hC (Real.rpow_pos_of_pos h _)) hLp).mul hsum
    (by filter_upwards [hQLp,hLp] with j h hl using mul_pos (mul_pos hC
      (Real.rpow_pos_of_pos h _)) hl)
    (by filter_upwards [hQp,hLp] with j hq hl using add_pos (sq_pos_of_pos hq) hl)
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

/-- In the balanced configuration, the second moment lower bound and
all actual fixed-copy ordinary moments contradict every factor having
length exponent strictly below one. -/
theorem balanced_multiplicity_contradiction (a v : ι → ℝ) (r : ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i < 1) (hv : ∀ i, v i ≤ a i)
    (hsum : ∑ i, a i = 1) (hlarge : 7/3-2*(∑ i, v i) ≤ r)
    (hcard : r ≤ 2/3)
    (hmoment : ∀ k : ι → ℕ, r+2*(∑ i, (k i:ℝ)*v i) ≤
      (∑ i, (k i:ℝ)*a i)+max (4/3) (∑ i, (k i:ℝ)*a i)) : False := by
  have hk2 (f : ι → ℝ) : (∑ i, ((2:ℕ):ℝ)*f i) = 2*(∑ i, f i) := by
    rw [Finset.mul_sum]
    norm_num
  have h2 := hmoment (fun _ => 2)
  simp only [hk2,hsum] at h2
  norm_num at h2
  have hfourth : r+4*(∑ i, v i) ≤ 4 := by linarith
  obtain ⟨hr,hvsum⟩ := balanced_moment_saturation hlarge hcard hfourth
  obtain ⟨j,hj,hvj⟩ := exists_balanced_factor a v (fun i => (ha i).1) hv hsum hvsum
  let k : ι → ℕ := fun i => 1+if i=j then 1 else 0
  have hk (f : ι → ℝ) : (∑ i, (k i:ℝ)*f i) = (∑ i, f i)+f j := by
    simp [k,add_mul,Finset.sum_add_distrib]
  have hb := hmoment k
  simp only [hk,hsum,hvsum,hr] at hb
  have hgap := balanced_extra_factor_gap (z := 1+a j) (by linarith) (by linarith [(ha j).2])
  have hbad : 2/3 ≤ max (4/3) (1+a j)-2*(1+a j)/3 := by nlinarith
  exact not_lt_of_ge hbad hgap

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorLargeValues
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- The second limiting moment inequality retains the genuine ordinary
mixed-character input and the same actual short factors. -/
theorem ShortFactorFamily.mixed_large_values_exponent (F : ShortFactorFamily ι)
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ι → ℕ)
    {Y Q : ℕ → ℝ} (P : ℕ → Finset (Eisenstein × Eisenstein))
    (B : ℕ → ι → ℝ) {a v : ι → ℝ} {r q : ℝ}
    (hY : Tendsto Y atTop atTop) (hQ : ∀ j, 1 ≤ Q j)
    (hP : ∀ j, ∀ p ∈ P j, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q j)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ p ∈ P j, ∀ i, B j i ≤ ‖F.mixedValue j i p‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hQexp : HasPowerExponent Y Q q)
    (hXexp : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hBexp : ∀ i, HasPowerExponent Y (fun j => B j i) (v i)) :
    r+2*(∑ i, (k i:ℝ)*v i) ≤ (∑ i, (k i:ℝ)*a i)+
      max (2*q) (∑ i, (k i:ℝ)*a i) := by
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
  apply ordinary_moment_exponent hY
    (Eventually.of_forall (fun j => Nat.cast_pos.mpr (Finset.card_pos.mpr (hPne j)))) hVp
    (Eventually.of_forall (fun j => zero_lt_one.trans_le (hQ j))) hLp
    hRexp hVexp hQexp hLexp
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := shortFactor_mixed_multiplicity_power hHuxley k hε
  refine ⟨C,hC,Eventually.of_forall (fun j => ?_)⟩
  exact (finite_power_product_large_values (P j) k (F.mixedValue j) (B j)
    (fun i => (hB j i).le) (hrow j)).trans
    (hbound (F.cutoff j) (F.length j) (F.coefficient j) (F.twist j)
      (F.factor_spec j) (F.length_ge_one j) (F.twist_bound j) (P j) (Q j) (hQ j) (hP j))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExceptionalRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- A bound by every arbitrarily enlarged power passes to the exact
logarithmic exponent. The constants are allowed to depend on the enlargement. -/
theorem HasPowerExponent.le_of_small_power {Y f g : ℕ → ℝ} {a b : ℝ}
    (hf : HasPowerExponent Y f a) (hg : HasPowerExponent Y g b)
    (hY : Tendsto Y atTop atTop)
    (hfp : ∀ᶠ j in atTop, 0 < f j) (hgp : ∀ᶠ j in atTop, 0 < g j)
    (hbound : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ j in atTop, f j ≤ C*(g j)^(1+η)) : a ≤ b := by
  have hη (η : ℝ) (hη : 0 < η) : a ≤ η*b+b := by
    obtain ⟨C,hC,hCbound⟩ := hbound η hη
    have hr := (HasPowerExponent.const hY C).mul (hg.rpow hgp (1+η))
      (Eventually.of_forall (fun _ => hC))
      (by filter_upwards [hgp] with j hj using Real.rpow_pos_of_pos hj _)
    have h := hf.mono hr hY hfp hCbound
    simpa only [zero_add,add_zero,add_mul,one_mul,add_comm] using h
  by_contra hab
  have hgap : 0 < a-b := sub_pos.mpr (lt_of_not_ge hab)
  let η : ℝ := (a-b)/(2*(|b|+1))
  have hηpos : 0 < η := div_pos hgap (by positivity)
  have he : η*(2*(|b|+1)) = a-b := div_mul_cancel₀ _ (by positivity)
  have hb := mul_le_mul_of_nonneg_left (le_abs_self b) hηpos.le
  have h := hη η hηpos
  nlinarith [mul_nonneg hηpos.le (abs_nonneg b)]

theorem ShortFactorFamily.mixedValue_small_power {ι : Type*}
    (F : ShortFactorFamily ι) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (i : ι) (p : Eisenstein × Eisenstein),
      primary p.1 → primary p.2 →
      ‖F.mixedValue j i p‖ ≤ C*(F.length j i)^(1+η) := by
  obtain ⟨C,hC,hbound⟩ := shortFactorPolynomial_norm_small_power hη
  refine ⟨C,hC,?_⟩
  intro j i p h₁ h₂
  apply hbound (F.cutoff j) (F.length j i) (F.coefficient j i)
    (F.factor_spec j i) (F.length_ge_one j i)
  intro n hn
  rw [norm_mul]
  exact (mul_le_mul (F.twist_bound j i n hn) (norm_mixedCubic_le_one h₁ h₂ n)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem ShortFactorFamily.length_exponent_nonneg {ι : Type*}
    (F : ShortFactorFamily ι) {Y : ℕ → ℝ} {a : ι → ℝ}
    (hY : Tendsto Y atTop atTop)
    (hX : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i)) (i : ι) :
    0 ≤ a i :=
  (HasPowerExponent.const hY 1).mono (hX i) hY
    (Eventually.of_forall (fun _ => zero_lt_one))
    (Eventually.of_forall (fun j => F.length_ge_one j i))

theorem ShortFactorFamily.mixed_value_exponent_le {ι : Type*}
    (F : ShortFactorFamily ι) {Y : ℕ → ℝ} (P : ℕ → Finset (Eisenstein × Eisenstein))
    (B : ℕ → ι → ℝ) {a v : ι → ℝ}
    (hY : Tendsto Y atTop atTop)
    (hP : ∀ j, ∀ p ∈ P j, primary p.1 ∧ primary p.2)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ p ∈ P j, ∀ i, B j i ≤ ‖F.mixedValue j i p‖)
    (hX : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hV : ∀ i, HasPowerExponent Y (fun j => B j i) (v i)) (i : ι) :
    v i ≤ a i := by
  apply (hV i).le_of_small_power (hX i) hY
    (Eventually.of_forall (fun j => hB j i))
    (Eventually.of_forall (fun j => zero_lt_one.trans_le (F.length_ge_one j i)))
  intro η hη
  obtain ⟨C,hC,hbound⟩ := F.mixedValue_small_power hη
  refine ⟨C,hC,Eventually.of_forall (fun j => ?_)⟩
  obtain ⟨p,hp⟩ := hPne j
  exact (hrow j p hp i).trans (hbound j i p (hP j p hp).1 (hP j p hp).2)

/-- The exponent `2/3` for balanced row cardinality is proved from the
actual two component norm cutoffs, rather than imposed on the row count. -/
theorem balanced_rows_exponent_le {Y L : ℕ → ℝ}
    (P : ℕ → Finset (Eisenstein × Eisenstein)) {r : ℝ}
    (hY : Tendsto Y atTop atTop) (hL : ∀ j, 1 ≤ L j)
    (hP : ∀ j, ∀ p ∈ P j, primary p.1 ∧ primary p.2 ∧
      norm p.1 ≤ L j ∧ norm p.2 ≤ L j)
    (hPne : ∀ j, (P j).Nonempty)
    (hR : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hLexp : HasPowerExponent Y L (1/3)) : r ≤ 2/3 := by
  have hr := (HasPowerExponent.const hY 324).mul (hLexp.natPow 2)
    (Eventually.of_forall (fun _ => by norm_num))
    (Eventually.of_forall (fun j => sq_pos_of_pos (zero_lt_one.trans_le (hL j))))
  have h := hR.mono hr hY
    (Eventually.of_forall (fun j => Nat.cast_pos.mpr (Finset.card_pos.mpr (hPne j))))
    (Eventually.of_forall (fun j => balanced_pair_card (P j)
      (zero_le_one.trans (hL j)) (hP j)))
  norm_num at h ⊢
  exact h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- No balanced sequence of actual short-factor large-value rows can
satisfy the unsaved moment lower bound when every factor is shorter than
one. The only published assumption here is Huxley's additive large sieve. -/
theorem ShortFactorFamily.balanced_rows_contradiction (F : ShortFactorFamily ι)
    (hHuxley : HuxleyAdditiveLargeSieve) {Y Q L : ℕ → ℝ}
    (P : ℕ → Finset (Eisenstein × Eisenstein)) (B : ℕ → ι → ℝ)
    {a v : ι → ℝ} {r : ℝ}
    (hY : Tendsto Y atTop atTop) (hQ : ∀ j, 1 ≤ Q j) (hL : ∀ j, 1 ≤ L j)
    (hP : ∀ j, ∀ p ∈ P j, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q j)
    (hLP : ∀ j, ∀ p ∈ P j, norm p.1 ≤ L j ∧ norm p.2 ≤ L j)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ p ∈ P j, ∀ i, B j i ≤ ‖F.mixedValue j i p‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hQexp : HasPowerExponent Y Q (2/3)) (hLexp : HasPowerExponent Y L (1/3))
    (hXexp : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hBexp : ∀ i, HasPowerExponent Y (fun j => B j i) (v i))
    (ha : ∀ i, a i < 1) (hsum : ∑ i, a i = 1)
    (hlarge : 7/3-2*(∑ i, v i) ≤ r) : False := by
  have hprim : ∀ j, ∀ p ∈ P j, primary p.1 ∧ primary p.2 :=
    fun j p hp => ⟨(hP j p hp).1.1,(hP j p hp).1.2.1⟩
  have hcard := balanced_rows_exponent_le P hY hL
    (fun j p hp => ⟨(hprim j p hp).1,(hprim j p hp).2,
      (hLP j p hp).1,(hLP j p hp).2⟩) hPne hRexp hLexp
  apply balanced_multiplicity_contradiction a v r
    (fun i => ⟨F.length_exponent_nonneg hY hXexp i,ha i⟩)
    (F.mixed_value_exponent_le P B hY hprim hPne hB hrow hXexp hBexp)
    hsum hlarge hcard
  intro k
  have h := F.mixed_large_values_exponent hHuxley k P B hY hQ hP hPne hB hrow
    hRexp hQexp hXexp hBexp
  norm_num at h ⊢
  exact h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorGram
attribute [-instance] _root_.instMeasurableSpace
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


lemma HasPowerExponent.const_mul {Y f : ℕ → ℝ} {a C : ℝ}
    (hf : HasPowerExponent Y f a) (hY : Tendsto Y atTop atTop) (hC : 0 < C)
    (hfp : ∀ᶠ j in atTop, 0 < f j) :
    HasPowerExponent Y (fun j => C*f j) a := by
  simpa only [zero_add] using (HasPowerExponent.const hY C).mul hf
    (Eventually.of_forall (fun _ => hC)) hfp

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_VaryingConductorSequences
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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


/-- The balanced actual short-factor family also cannot retain an unsaved
moment; its row and value limits are extracted inside the proof. -/
theorem ShortFactorFamily.balanced_varying_conductor_sequence_impossible (F : ShortFactorFamily ι)
    (hHuxley : HuxleyAdditiveLargeSieve) (Y L G : ℕ → ℝ)
    (S : ℕ → Finset (Eisenstein × Eisenstein)) {δ H D : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hY : Tendsto Y atTop atTop) (hY₂ : ∀ j, 2 ≤ Y j)
    (hG : ∀ j, 1 ≤ G j) (hGexp : HasPowerExponent Y G (7/3))
    (hL : ∀ j, 1 ≤ L j) (hLexp : HasPowerExponent Y L (1/3))
    (hS : ∀ j, ∀ p ∈ S j, PrimarySquarefreePair p ∧
      norm p.1 ≤ L j ∧ norm p.2 ≤ L j)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ (Y j)^D)
    (hshort : ∀ j i, F.length j i ≤ (Y j)^(1-δ))
    (htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1)
    (hbound : ∀ j, ∀ p ∈ S j, ∀ i, ‖F.mixedValue j i p‖ ≤ (Y j)^H)
    (hmoment : ∀ j, G j ≤ ∑ p ∈ S j, ‖∏ i, F.mixedValue j i p‖^2) : False := by
  obtain ⟨φ,a,hφ,ha,hasum,haexp⟩ := F.lengths_subsequence hY
    (fun j => by linarith [hY₂ j]) hshort htotal
  let K : ℝ := D/2+(Fintype.card ι:ℝ)*H+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcut : D+2*(Fintype.card ι:ℝ)*H-2*K ≤ -2 := by dsimp [K]; linarith
  have hGφ : HasPowerExponent (Y ∘ φ) (G ∘ φ) (7/3) := hGexp.comp hφ.tendsto_atTop
  obtain ⟨ψ,P,B,r,v,hψ,hP,hB,hrow,hRexp,hVexp,_,_,hlarge⟩ :=
    extract_unsaved_moment_subsequence (Y ∘ φ) (G ∘ φ) (S ∘ φ)
      (fun j i p => ‖F.mixedValue (φ j) i p‖) hH hK hcut
      (hY.comp hφ.tendsto_atTop) (fun j => hY₂ (φ j)) (fun j => hG (φ j)) hGφ
      (fun j => hcard (φ j)) (fun _ _ _ _ => _root_.norm_nonneg _)
      (fun j => hbound (φ j)) (fun j => by simpa only [norm_prod,Function.comp_def] using hmoment (φ j))
  let Z : ℕ → ℝ := (Y ∘ φ) ∘ ψ
  have hZ : Tendsto Z atTop atTop := (hY.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  have hZ₁ (j : ℕ) : 1 ≤ Z j := by dsimp [Z]; linarith [hY₂ (φ (ψ j))]
  have hZp (j : ℕ) : 0 < Z j := zero_lt_one.trans_le (hZ₁ j)
  let L' : ℕ → ℝ := (L ∘ φ) ∘ ψ
  have hL' (j : ℕ) : 1 ≤ L' j := hL (φ (ψ j))
  have hLexp' : HasPowerExponent Z L' (1/3) :=
    (hLexp.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  have hQexp : HasPowerExponent Z (fun j => (L' j)^2) (2/3) := by
    convert hLexp'.natPow 2 using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hP' (j : ℕ) (p : Eisenstein × Eisenstein) (hp : p ∈ P j) :
      PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ (L' j)^2 := by
    have hs := hS (φ (ψ j)) p ((hP j).2 hp)
    refine ⟨hs.1,?_⟩
    rw [pairConductor,norm_mul_eq]
    calc
      _ ≤ L' j * L' j :=
        mul_le_mul hs.2.1 hs.2.2 (norm_nonneg _) (zero_le_one.trans (hL' j))
      _ = _ := by ring
  apply ((F.comp φ).comp ψ).balanced_rows_contradiction hHuxley P B hZ
    (fun j => one_le_pow₀ (hL' j)) hL' hP'
    (fun j p hp => (hS (φ (ψ j)) p ((hP j).2 hp)).2)
    (fun j => (hP j).1)
    (fun j i => (Real.rpow_pos_of_pos (hZp j) (-K)).trans_le (hB j i).1)
    (fun j p hp i => (hrow j p hp i).1) hRexp hQexp hLexp'
    (fun i => (haexp i).comp hψ.tendsto_atTop) hVexp
    (fun i => lt_of_le_of_lt (ha i).2 (by linarith)) hasum (by linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ConductorNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem mixed_short_neighborhood_power (hHuxley : HuxleyAdditiveLargeSieve)
    {δ H D C : ℝ} (hδ : 0 < δ) (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ x : ConductorMomentInstance ι (Eisenstein × Eisenstein),
        mixedNeighborhoodAdmissible δ H D C κ x → Y₀ ≤ x.scale →
          mixedInstanceMoment x.toShortMomentInstance ≤ x.scale^(7/3-ε) := by
  apply neighborhood_saving_of_no_countersequence
    (fun x : ConductorMomentInstance ι (Eisenstein × Eisenstein) => x.scale)
    (fun x => mixedInstanceMoment x.toShortMomentInstance)
    (mixedNeighborhoodAdmissible δ H D C)
  intro x hx hY hm
  let Y : ℕ → ℝ := fun j => (x j).scale
  let L : ℕ → ℝ := fun j => (x j).conductorScale
  let G : ℕ → ℝ := fun j => (Y j)^(7/3-1/((j:ℝ)+1))
  let F := neighborhoodFamily x
  have hYlim : Tendsto Y atTop atTop := neighborhood_scale_tendsto hY
  have hY₂ (j : ℕ) : 2 ≤ Y j := by linarith [hY j,Nat.cast_nonneg (α := ℝ) j]
  have htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1 :=
    HasPowerExponent.of_comparable hYlim hC
      (Eventually.of_forall (fun j => ⟨(hx j).2.1,(hx j).2.2.1⟩))
  have hLexp : HasPowerExponent Y L (1/3) :=
    HasPowerExponent.of_shrinking_window hYlim (fun j => by linarith [hY₂ j])
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (fun j => (hx j).2.2.2.2.1)
  exact F.balanced_varying_conductor_sequence_impossible hHuxley Y L G
    (fun j => (x j).rows) hδ hH hD hYlim hY₂ (neighborhood_lower_ge_one hY)
    (neighborhood_lower_exponent hYlim) (fun j => (hx j).2.2.2.1) hLexp
    (fun j => (hx j).2.2.2.2.2.1) (fun j => (hx j).2.2.2.2.2.2.1)
    (fun j => (hx j).1) htotal (fun j => (hx j).2.2.2.2.2.2.2) hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_AllShortNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma neighborhood_balanced_card (S : Finset (Eisenstein × Eisenstein))
    {Y L : ℝ} (hY : 324 ≤ Y) (hL : 0 ≤ L) (hLY : L ≤ Y)
    (hS : ∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ L ∧ norm p.2 ≤ L) :
    (S.card:ℝ) ≤ Y^4 := by
  have hc := balanced_pair_card S hL
    (fun p hp => ⟨(hS p hp).1.1,(hS p hp).1.2.1,(hS p hp).2⟩)
  calc
    _ ≤ 324*L^2 := hc
    _ ≤ 324*Y^2 := by gcongr
    _ ≤ Y^2*Y^2 := by gcongr; nlinarith
    _ = _ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem all_short_mixed_neighborhood (hHuxley : HuxleyAdditiveLargeSieve)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/3 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (F : ShortFactorFamily ι) (j : ℕ) (Y : ℝ)
        (S : Finset (Eisenstein × Eisenstein)), Y₀ ≤ Y →
      (∀ i, F.length j i ≤ Y^(1-δ)) →
      Y/C ≤ ∏ i, F.length j i → (∏ i, F.length j i) ≤ C*Y →
      (∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3+κ) ∧
        norm p.2 ≤ Y^(1/3+κ)) →
      (∑ p ∈ S, ‖∏ i, F.mixedValue j i p‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,ε,hε,T₀,huniform⟩ := mixed_short_neighborhood_power (ι := ι) hHuxley
    (H := 2) (D := 4) hδ (by norm_num) (by norm_num) hC
  obtain ⟨T,hT,hsize⟩ := shortFactorPolynomial_uniform_quadratic_size
  refine ⟨min κ (1/3),by positivity,min_le_right _ _,ε,hε,max T₀ (max T 324),?_⟩
  intro F j Y S hY hshort hlo hhi hS
  have hYT : T ≤ Y := (le_max_left T 324).trans ((le_max_right _ _).trans hY)
  have hY₁ : 1 ≤ Y := hT.trans hYT
  have hY₃₂₄ : 324 ≤ Y := (le_max_right T 324).trans ((le_max_right _ _).trans hY)
  let L : ℝ := Y^(1/3+min κ (1/3))
  have hL : 1 ≤ L := Real.one_le_rpow hY₁ (by have := lt_min hκ (by norm_num : (0:ℝ) < 1/3); linarith)
  have hLY : L ≤ Y := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY₁
      (by have := min_le_right κ (1/3); linarith : 1/3+min κ (1/3) ≤ 1)
  let x : ConductorMomentInstance ι (Eisenstein × Eisenstein) :=
    ⟨⟨Y,F.comp (fun _ => j),S⟩,L⟩
  have hx : mixedNeighborhoodAdmissible δ 2 4 C κ x := by
    refine ⟨hshort,hlo,hhi,hL,⟨?_,?_⟩,hS,?_,?_⟩
    · change Y^(1/3-κ) ≤ Y^(1/3+min κ (1/3))
      apply Real.rpow_le_rpow_of_exponent_le hY₁
      have hm := lt_min hκ (by norm_num : (0:ℝ) < 1/3)
      linarith
    · exact Real.rpow_le_rpow_of_exponent_le hY₁
        (by have := min_le_left κ (1/3); linarith)
    · change (S.card:ℝ) ≤ Y^(4:ℝ)
      convert neighborhood_balanced_card S hY₃₂₄ (zero_le_one.trans hL) hLY hS using 1
      all_goals try with_reducible_and_instances rfl
      norm_num
    · intro p hp i
      change ‖F.mixedValue j i p‖ ≤ Y^(2:ℝ)
      rw [Real.rpow_two]
      apply hsize (F.cutoff j) (F.length j i) Y (F.coefficient j i)
        (fun n => F.twist j i n*mixedCubic p.1 p.2 n) (F.factor_spec j i)
        (F.length_ge_one j i) (short_neighborhood_length hY₁ hδ.le (hshort i)) hYT
      intro n hn
      rw [norm_mul]
      exact (mul_le_mul (F.twist_bound j i n hn)
        (norm_mixedCubic_le_one (hS p hp).1.1 (hS p hp).1.2.1 n)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact huniform x hx ((le_max_left _ _).trans hY)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DualPolynomialScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact `sqrt(Z/J)` normalization of a retained dual norm block.
The normalized coefficients are independent of the character conductor. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma positive_cpow_phase {x : ℝ} (hx : 0 < x) (σ u : ℝ) :
    (x:ℂ)^((σ:ℂ)+(u:ℂ)*Complex.I) = (x^σ:ℝ)*mellinPhase u x := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le,Real.rpow_def_of_pos hx,Complex.ofReal_exp]
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeSmoothDual
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From the ordinary analytic properties of a primitive Hecke series
to a truncated smooth dual sum. The smooth-duality conclusion follows from the contour shift. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma mellinPhase_eq_cpow {x : ℝ} (hx : 0 < x) (t : ℝ) :
    mellinPhase t x = (x:ℂ)^((t:ℂ)*Complex.I) := by
  simpa only [Complex.ofReal_zero,zero_add,Real.rpow_zero,Complex.ofReal_one,one_mul]
    using (positive_cpow_phase hx 0 t).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueIdealCharacters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite residue character as an actual complete ideal character,
and exact restoration of Euler factors after primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma residueIdealChar_add (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ν κ : EisensteinIdealExponent) :
    residueIdealChar q χ (ν+κ) = residueIdealChar q χ ν*residueIdealChar q χ κ := by
  simp only [residueIdealChar,idealExponentGenerator_add,map_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ConductorLocal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local detection of the squarefree cubic conductor. A nontrivial
prime character survives every inducing modulus, as witnessed by CRT. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma residueIdealChar_primaryNormalize {d : Eisenstein} (ψ : MulChar (Residues d) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (ν : EisensteinIdealExponent) :
    residueIdealChar d ψ ν = ψ (Ideal.Quotient.mk (modulus d) (idealPrimaryGenerator ν)) := by
  obtain ⟨u,hassoc⟩ := primaryNormalize_associated (idealExponentGenerator ν)
  change ψ (Ideal.Quotient.mk (modulus d) (idealExponentGenerator ν)) =
    ψ (Ideal.Quotient.mk (modulus d) (primaryNormalize (idealExponentGenerator ν)))
  rw [← hassoc,map_mul,map_mul,hu,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RamifiedIdealParts
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the finitely many primes above three in the
complete ideal lattice. No ramified Euler term is discarded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellinPhase_mul_pos (u : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    mellinPhase u (x*y) = mellinPhase u x*mellinPhase u y := by
  unfold mellinPhase
  rw [Real.log_mul hx.ne' hy.ne',mul_add,Complex.ofReal_add,add_mul,Complex.exp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusProducts
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short Möbius identity remains valid inside any fixed product of
prime-weight factors. This is the algebraic replacement before smoothing. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma shortVonMangoldt_two_four (F : ℝ) :
    shortVonMangoldt F = 2*shortTwoFactor F-shortFourFactor F := by
  unfold shortVonMangoldt shortTwoFactor shortFourFactor
  ring

lemma shortVonMangoldt_local {F : ℝ} (hF : 0 ≤ F) :
    NormLocalEq F idealVonMangoldt (shortVonMangoldt F) :=
  fun ν hν => short_moebius_identity hF ν hν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArithmeticTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Twisting actual ideal arithmetic functions by a residue character and
norm phase commutes with convolution. Different original factors may
therefore retain different Mellin heights throughout short inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma residueNormTwist_add (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (ν κ : EisensteinIdealExponent) :
    residueNormTwist q η t (ν+κ) = residueNormTwist q η t ν*residueNormTwist q η t κ := by
  rw [residueNormTwist,residueIdealChar_add,idealExponentNorm_add,
    mellinPhase_mul_pos t (idealExponentNorm_pos ν) (idealExponentNorm_pos κ)]
  unfold residueNormTwist
  ring

lemma twistArithmetic_mul (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A B : EisensteinArithmeticFunction) :
    twistArithmetic q η t (A*B) = twistArithmetic q η t A*twistArithmetic q η t B := by
  apply MvPowerSeries.ext
  intro ν
  change ((MvPowerSeries.coeff ν (A*B):ℝ):ℂ)*residueNormTwist q η t ν = _
  rw [MvPowerSeries.coeff_mul,Complex.ofReal_sum,Finset.sum_mul,MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  change ((MvPowerSeries.coeff p.1 A*MvPowerSeries.coeff p.2 B:ℝ):ℂ)*
      residueNormTwist q η t ν = _
  rw [← he,residueNormTwist_add,Complex.ofReal_mul]
  change _ = (((MvPowerSeries.coeff p.1 A:ℝ):ℂ)*residueNormTwist q η t p.1)*
    (((MvPowerSeries.coeff p.2 B:ℝ):ℂ)*residueNormTwist q η t p.2)
  ring

lemma twistArithmetic_add (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A B : EisensteinArithmeticFunction) :
    twistArithmetic q η t (A+B) = twistArithmetic q η t A+twistArithmetic q η t B := by
  ext ν
  change ((MvPowerSeries.coeff ν (A+B):ℝ):ℂ)*residueNormTwist q η t ν =
    ((MvPowerSeries.coeff ν A:ℝ):ℂ)*residueNormTwist q η t ν +
      ((MvPowerSeries.coeff ν B:ℝ):ℂ)*residueNormTwist q η t ν
  rw [map_add,Complex.ofReal_add,add_mul]

lemma twistArithmetic_sub (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A B : EisensteinArithmeticFunction) :
    twistArithmetic q η t (A-B) = twistArithmetic q η t A-twistArithmetic q η t B := by
  ext ν
  change ((MvPowerSeries.coeff ν (A-B):ℝ):ℂ)*residueNormTwist q η t ν =
    ((MvPowerSeries.coeff ν A:ℝ):ℂ)*residueNormTwist q η t ν -
      ((MvPowerSeries.coeff ν B:ℝ):ℂ)*residueNormTwist q η t ν
  rw [map_sub,Complex.ofReal_sub,sub_mul]

lemma twistArithmetic_coeff_primary (q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (hu : ∀ e : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) e) = 1)
    (t : ℝ) (A : EisensteinArithmeticFunction) {n : Eisenstein} (hn : primary n) :
    MvPowerSeries.coeff (idealExponentOf n) (twistArithmetic q η t A) =
      ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
        η (Ideal.Quotient.mk (modulus q) n)*mellinPhase t (norm n) := by
  change ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
    (residueIdealChar q η (idealExponentOf n)*mellinPhase t (idealExponentNorm (idealExponentOf n))) = _
  rw [residueIdealChar_primaryNormalize η hu,idealPrimaryGenerator_at_element hn,
    idealExponentOf_norm (primary_ne_zero hn)]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogSmoothWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullSmoothFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primaryShortSmoothSum_eq_polynomial (A : EisensteinArithmeticFunction)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    primaryShortSmoothSum A a b q η W Z t =
      primaryIdealPolynomial (B*Z) A (fun x =>
        mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*mellinPhase t (norm x)*W (norm x/Z)) := by
  rw [primaryIdealPolynomial_eq_elements]
  unfold primaryShortSmoothSum
  rw [primary_weighted_smooth_finite _ W hZ hW]
  apply Finset.sum_congr rfl
  intro x _
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DominantFactorLengths
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining lengths and values after selecting a dominant short factor. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Removing a factor of length at least `Y^(1-δ)` leaves total length at
most `C*Y^δ`, including the fixed dyadic discrepancy `C`. -/
theorem remaining_length_bound (X : ι → ℝ) (i : ι) {Y C δ : ℝ}
    (hY : 0 < Y) (hX : ∀ k, 0 ≤ X k) (_hC : 0 ≤ C)
    (htotal : (∏ k, X k) ≤ C*Y) (hlong : Y^(1-δ) ≤ X i) :
    (∏ k ∈ Finset.univ.erase i, X k) ≤ C*Y^δ := by
  have hrem : 0 ≤ ∏ k ∈ Finset.univ.erase i, X k :=
    Finset.prod_nonneg (fun k _ => hX k)
  have hprod : Y^(1-δ)*(∏ k ∈ Finset.univ.erase i, X k) ≤ C*Y := by
    calc
      _ ≤ X i*(∏ k ∈ Finset.univ.erase i, X k) := mul_le_mul_of_nonneg_right hlong hrem
      _ = ∏ k, X k := Finset.mul_prod_erase Finset.univ X (Finset.mem_univ i)
      _ ≤ C*Y := htotal
  have hid : Y^(1-δ)*(C*Y^δ) = C*Y := by
    rw [mul_left_comm,← Real.rpow_add hY]
    simp only [sub_add_cancel,Real.rpow_one]
  exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hY (1-δ))).mp (hprod.trans_eq hid.symm)

private lemma remaining_value_product_bound (X : ι → ℝ) (f : ι → ℂ) (i : ι)
    {Y C K δ η : ℝ} (hY : 1 ≤ Y) (hC : 0 < C) (hK : 1 ≤ K)
    (hX : ∀ k, 1 ≤ X k) (hη : 0 ≤ η)
    (hrem : (∏ k ∈ Finset.univ.erase i, X k) ≤ C*Y^δ)
    (hf : ∀ k ∈ Finset.univ.erase i, ‖f k‖ ≤ K*(X k)^(1+η)) :
    ‖∏ k ∈ Finset.univ.erase i, f k‖ ≤
      K^(Fintype.card ι)*C^(1+η)*Y^(δ*(1+η)) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hXpos : ∀ k, 0 ≤ X k := fun k => zero_le_one.trans (hX k)
  have hp : K^((Finset.univ.erase i).card) ≤ K^(Fintype.card ι) :=
    pow_le_pow_right₀ hK (by simpa only [Finset.card_univ] using
      (Finset.card_le_card (Finset.erase_subset i Finset.univ)))
  calc
    _ = ∏ k ∈ Finset.univ.erase i, ‖f k‖ := norm_prod _ _
    _ ≤ ∏ k ∈ Finset.univ.erase i, (K*(X k)^(1+η)) :=
      Finset.prod_le_prod (fun _ _ => _root_.norm_nonneg _) hf
    _ = K^((Finset.univ.erase i).card)*(∏ k ∈ Finset.univ.erase i, X k)^(1+η) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,
        Real.finsetProd_rpow _ _ (fun k _ => hXpos k)]
    _ ≤ K^(Fintype.card ι)*(C*Y^δ)^(1+η) :=
      mul_le_mul hp (Real.rpow_le_rpow (Finset.prod_nonneg (fun k _ => hXpos k)) hrem
        (by linarith)) (Real.rpow_nonneg (Finset.prod_nonneg (fun k _ => hXpos k)) _)
        (pow_nonneg (zero_le_one.trans hK) _)
    _ = _ := by
      rw [Real.mul_rpow hC.le (Real.rpow_nonneg hYp.le δ),← Real.rpow_mul hYp.le]
      ring

/-- Uniformly bounded twists of the actual short arithmetic polynomials
have a small remaining product after one dominant factor is removed. -/
theorem short_remaining_polynomial_bound {C δ ε : ℝ}
    (hC : 0 < C) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ) (i : ι),
      1 ≤ Y → (∀ k, 1 ≤ X k) → (∀ k, ShortArithmeticFactor F (A k)) →
      (∀ k, ∀ n ∈ primaryElementBall (X k), ‖u k n‖ ≤ 1) →
      (∏ k, X k) ≤ C*Y → Y^(1-δ) ≤ X i →
      ‖∏ k ∈ Finset.univ.erase i, primaryIdealPolynomial (X k) (A k) (u k)‖ ≤
        M*Y^(δ+ε) := by
  let η : ℝ := ε/(δ+1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hηδ : δ*(1+η) ≤ δ+ε := by
    have he : η*(δ+1) = ε := div_mul_cancel₀ _ (by linarith)
    nlinarith
  obtain ⟨K₀,hK₀,hbound⟩ := shortFactorPolynomial_norm_small_power hη
  let K : ℝ := max 1 K₀
  have hK : 1 ≤ K := le_max_left _ _
  have hKM : K₀ ≤ K := le_max_right _ _
  refine ⟨K^(Fintype.card ι)*C^(1+η),mul_pos
    (pow_pos (zero_lt_one.trans_le hK) _) (Real.rpow_pos_of_pos hC _),?_⟩
  intro F Y X A u i hY hX hA hu htotal hlong
  have hr := remaining_length_bound X i (zero_lt_one.trans_le hY)
    (fun k => zero_le_one.trans (hX k)) hC.le htotal hlong
  have hf (k : ι) (_hk : k ∈ Finset.univ.erase i) :
      ‖primaryIdealPolynomial (X k) (A k) (u k)‖ ≤ K*(X k)^(1+η) :=
    (hbound F (X k) (A k) (hA k) (hX k) (u k) (hu k)).trans
      (mul_le_mul_of_nonneg_right hKM (Real.rpow_nonneg (zero_le_one.trans (hX k)) _))
  exact (remaining_value_product_bound X
    (fun k => primaryIdealPolynomial (X k) (A k) (u k)) i hY hC hK hX hη.le hr hf).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY hηδ)
        (mul_nonneg (pow_nonneg (zero_le_one.trans hK) _) (Real.rpow_nonneg hC.le _)))

/-- The same remaining-product bound for the actual mixed cubic values. -/
theorem remaining_mixed_values_bound {C δ ε : ℝ}
    (hC : 0 < C) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (F : ShortFactorFamily ι) (j : ℕ) (Y : ℝ) (i : ι)
      (p : Eisenstein × Eisenstein), 1 ≤ Y → primary p.1 → primary p.2 →
      (∏ k, F.length j k) ≤ C*Y → Y^(1-δ) ≤ F.length j i →
      ‖∏ k ∈ Finset.univ.erase i, F.mixedValue j k p‖ ≤ M*Y^(δ+ε) := by
  obtain ⟨M,hM,hbound⟩ := short_remaining_polynomial_bound (ι := ι) hC hδ hε
  refine ⟨M,hM,?_⟩
  intro F j Y i p hY hp hq htotal hlong
  apply hbound (F.cutoff j) Y (F.length j) (F.coefficient j)
    (fun k n => F.twist j k n*mixedCubic p.1 p.2 n) i hY (F.length_ge_one j) (F.factor_spec j)
    ?_ htotal hlong
  intro k n hn
  rw [norm_mul]
  exact (mul_le_mul (F.twist_bound j k n hn) (norm_mixedCubic_le_one hp hq n)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- A common bound for the other factors reduces the full product moment
to the moment of a single fixed dominant factor. -/
theorem moment_le_dominant_factor {κ : Type*} (S : Finset κ)
    (f : ι → κ → ℂ) (i : ι) (B : ℝ)
    (hB : ∀ r ∈ S, ‖∏ k ∈ Finset.univ.erase i, f k r‖ ≤ B) :
    (∑ r ∈ S, ‖∏ k, f k r‖^2) ≤ B^2*(∑ r ∈ S, ‖f i r‖^2) := by
  calc
    _ ≤ ∑ r ∈ S, B^2*‖f i r‖^2 := by
      apply Finset.sum_le_sum
      intro r hr
      rw [← Finset.mul_prod_erase Finset.univ (fun k => f k r) (Finset.mem_univ i),
        norm_mul,mul_pow]
      have hsq := pow_le_pow_left₀ (_root_.norm_nonneg _ ) (hB r hr) 2
      nlinarith [sq_nonneg ‖f i r‖]
    _ = _ := (Finset.mul_sum S (fun r => ‖f i r‖^2) (B^2)).symm

/-- The corresponding moment reduction for a dominant mixed cubic factor. -/
theorem dominant_mixed_moment_reduction {C δ ε : ℝ}
    (hC : 0 < C) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (F : ShortFactorFamily ι) (j : ℕ) (Y : ℝ) (i : ι)
      (S : Finset (Eisenstein × Eisenstein)), 1 ≤ Y →
      (∀ p ∈ S, primary p.1 ∧ primary p.2) →
      (∏ k, F.length j k) ≤ C*Y → Y^(1-δ) ≤ F.length j i →
      (∑ p ∈ S, ‖∏ k, F.mixedValue j k p‖^2) ≤
        (M*Y^(δ+ε))^2*(∑ p ∈ S, ‖F.mixedValue j i p‖^2) := by
  obtain ⟨M,hM,hbound⟩ := remaining_mixed_values_bound (ι := ι) hC hδ hε
  refine ⟨M,hM,?_⟩
  intro F j Y i S hY hS htotal hlong
  exact moment_le_dominant_factor S (F.mixedValue j) i (M*Y^(δ+ε))
    (fun p hp => hbound F j Y i p hY (hS p hp).1 (hS p hp).2 htotal hlong)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothShortFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma smoothShortFamily_mixedValue {ι : Type*} (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hq : ∀ i, q i ≠ 0) (hW : ∀ i x, ‖W i x‖ ≤ 1)
    (hcut : ∀ i x, 2 < x → W i x = 0) (j : ℕ) (i : ι) (p : Eisenstein × Eisenstein) :
    (shortFamilyOfSmoothWeights F X A q η W t hA hX hq hW).mixedValue j i p =
      primaryShortSmoothSum (A i) p.1 p.2 (q i) (η i) (W i) (X i/2) (t i) := by
  rw [primaryShortSmoothSum_eq_polynomial (A i) p.1 p.2 (q i) (η i) (W i)
    (by linarith [hX i] : 0 < X i/2) (hcut i)]
  have hx : 2*(X i/2) = X i := by ring
  rw [hx]
  unfold ShortFactorFamily.mixedValue
  change primaryIdealPolynomial (X i) (A i) (fun n =>
    smoothShortTwist (η i) (W i) (X i) (t i) n*mixedCubic p.1 p.2 n) = _
  congr 1
  funext n
  unfold smoothShortTwist
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothShortMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem dominant_smooth_mixed_moment_reduction {C δ ε : ℝ}
    (hC : 0 < C) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
      (P : Finset (Eisenstein × Eisenstein)) (i : ι),
      (∀ k, ShortArithmeticFactor F (A k)) → (∀ k, 1 ≤ X k) →
      (∀ k, q k ≠ 0) → (∀ k x, ‖W k x‖ ≤ 1) → (∀ k x, 2 < x → W k x = 0) →
      1 ≤ Y → (∀ p ∈ P, primary p.1 ∧ primary p.2) → (∏ k, X k) ≤ C*Y → Y^(1-δ) ≤ X i →
      (∑ p ∈ P, ‖∏ k, primaryShortSmoothSum (A k) p.1 p.2 (q k) (η k) (W k) (X k/2) (t k)‖^2) ≤
        (M*Y^(δ+ε))^2*(∑ p ∈ P, ‖primaryShortSmoothSum (A i) p.1 p.2 (q i) (η i) (W i) (X i/2) (t i)‖^2) := by
  obtain ⟨M,hM,hbound⟩ := dominant_mixed_moment_reduction (ι := ι) hC hδ hε
  refine ⟨M,hM,?_⟩
  intro F Y X A q η W t P i hA hX hq hW hcut hY hP htotal hlong
  let K := shortFamilyOfSmoothWeights F X A q η W t hA hX hq hW
  have h := hbound K 0 Y i P hY hP htotal hlong
  simpa only [K,smoothShortFamily_mixedValue F X A q η W t hA hX hq hW hcut] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothShortNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem all_short_smooth_mixed_neighborhood (hHuxley : HuxleyAdditiveLargeSieve)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/3 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (F Y : ℝ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
        (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
        (W : ι → ℝ → ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
      (∀ i, X i ≤ Y^(1-δ)) → Y/C ≤ ∏ i, X i → (∏ i, X i) ≤ C*Y →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3+κ) ∧ norm p.2 ≤ Y^(1/3+κ)) →
      (∑ p ∈ P, ‖∏ i, primaryShortSmoothSum (A i) p.1 p.2 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := all_short_mixed_neighborhood (ι := ι) hHuxley hδ hC
  refine ⟨κ,hκ,hκhi,ε,hε,T,?_⟩
  intro F Y X A q η W t P hY hA hX hq hW hcut hshort hlo hhi hP
  let K := shortFamilyOfSmoothWeights F X A q η W t hA hX hq hW
  have h := hbound K 0 Y P hY hshort hlo hhi hP
  simpa only [K,smoothShortFamily_mixedValue F X A q η W t hA hX hq hW hcut] using h


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedSmoothNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The balanced exceptional moment for the actual product of smooth
short-inverse factors. Both the all-short and dominant cases are proved. -/
noncomputable section
open Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem balanced_smooth_product_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (W : ι → ℝ → ℂ) (hW : ∀ i, HasCompactSupport (W i))
    (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0) (hsm : ∀ i, ContDiff ℝ ∞ (W i))
    (hWlow : ∀ i x, x < 1 → W i x = 0) (hWup : ∀ i x, 2 < x → W i x = 0)
    (hWnorm : ∀ i x, ‖W i x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(37/100:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖∏ i, primaryShortSmoothSum (A i) a.1 a.2 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,_,ε,hε,T₀,hshort⟩ := all_short_smooth_mixed_neighborhood (ι := ι) hHuxley
    (show (0:ℝ) < 1/10000 by norm_num) hD
  obtain ⟨M,hM,hred⟩ := dominant_smooth_mixed_moment_reduction (ι := ι) hD
    (show (0:ℝ) ≤ 1/10000 by norm_num) (show (0:ℝ) < 1/10000 by norm_num)
  choose K T hK hT hfull using fun i => dominant_balanced_full_factor_neighborhood hpub
    (W i) (hW i) (hpos i) (hsm i) (hWlow i) hGI hGQ D
  let B : ℝ := M^2*∑ i, K i
  have hKall : 0 ≤ ∑ i, K i := Finset.sum_nonneg (fun i _ => hK i)
  obtain ⟨T₁,hpow⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 137/1250 by norm_num)).eventually_ge_atTop B)
  refine ⟨min κ (1/10000),by positivity,min_le_right _ _,min ε (1/300),lt_min hε (by norm_num),max 2 (max T₀ (max (∑ i, T i) T₁)),?_⟩
  intro F Y X A q η t P hY hF hA hX hlo hhi hq hη hqY ht hP
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT : (∑ i, T i) ≤ Y := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  by_cases hall : ∀ i, X i ≤ Y^(1-(1/10000:ℝ))
  · exact (hshort F Y X A q η W t P hYT₀ hA hX hq hWnorm hWup hall hlo hhi (fun a ha => ⟨(hP a ha).1,
        (hP a ha).2.1.trans (Real.rpow_le_rpow_of_exponent_le hY1
          (by have := min_le_left κ (1/10000); linarith)),
        (hP a ha).2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hY1
          (by have := min_le_left κ (1/10000); linarith))⟩)).trans
      (Real.rpow_le_rpow_of_exponent_le hY1 (by have := min_le_left ε (1/300); linarith))
  · push Not at hall
    obtain ⟨i,hi⟩ := hall
    have hlong : Y^(1-(1/10000:ℝ)) ≤ X i := hi.le
    have hXi : X i ≤ D*Y := by
      apply le_trans _ hhi
      calc
        X i = ∏ j ∈ ({i} : Finset ι), X j := by simp
        _ ≤ ∏ j, X j := Finset.prod_le_prod_of_subset_of_one_le (by simp)
          (fun j _ => zero_le_one.trans (hX j)) (fun j _ _ => hX j)
    have hTi : T i ≤ Y := (Finset.single_le_sum (fun j _ => by linarith [hT j]) (Finset.mem_univ i)).trans hYT
    have hfulli := hfull i P (q i) (η i) (A i) F Y (X i) (t i)
      hTi (hA i) hF (hq i) (hη i) (hqY i) (ht i)
      (by convert hlong using 1; norm_num) hXi (fun a ha => ⟨(hP a ha).1,
        (hP a ha).2.1.trans (Real.rpow_le_rpow_of_exponent_le hY1
          (by have := min_le_right κ (1/10000); linarith)),
        (hP a ha).2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hY1
          (by have := min_le_right κ (1/10000); linarith)),(hP a ha).2.2.2⟩)
    have hreduce := hred F Y X A q η W t P i hA hX hq hWnorm hWup hY1
      (fun a ha => ⟨(hP a ha).1.1,(hP a ha).1.2.1⟩) hhi hlong
    have hKi : K i ≤ ∑ j, K j := Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)
    have hp : (Y^((1/10000:ℝ)+1/10000))^2*Y^(111/50:ℝ) = Y^(5551/2500:ℝ) := by
      rw [← Real.rpow_mul_natCast hY0.le,← Real.rpow_add hY0]
      norm_num
    calc
      _ ≤ (M*Y^((1/10000:ℝ)+1/10000))^2*(K i*Y^(111/50:ℝ)) :=
        hreduce.trans (mul_le_mul_of_nonneg_left hfulli (sq_nonneg _))
      _ ≤ (M*Y^((1/10000:ℝ)+1/10000))^2*((∑ j, K j)*Y^(111/50:ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKi (Real.rpow_nonneg hY0.le _)) (sq_nonneg _)
      _ = B*Y^(5551/2500:ℝ) := by dsimp [B]; rw [mul_pow]; rw [← hp]; ring
      _ ≤ Y^(137/1250:ℝ)*Y^(5551/2500:ℝ) :=
        mul_le_mul_of_nonneg_right (hpow Y hYT₁) (Real.rpow_nonneg hY0.le _)
      _ = Y^(233/100:ℝ) := by rw [← Real.rpow_add hY0]; norm_num
      _ ≤ Y^(7/3-min ε (1/300)) := Real.rpow_le_rpow_of_exponent_le hY1
        (by have := min_le_right ε (1/300); linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothNormPartition
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit finite smooth partition on every bounded positive norm range.
Its fixed weight is supported in `[1,2]`, as required by the smooth
short-factor estimates. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma normPartitionWeight_norm (x : ℝ) : ‖normPartitionWeight x‖ ≤ 1 := by
  by_cases hx : x < 1
  · rw [normPartitionWeight_low hx,norm_zero]
    norm_num
  have hmono : normPartitionStep (3*x/4) ≤ normPartitionStep x :=
    Real.smoothTransition.monotone (by linarith)
  have hnonneg := Real.smoothTransition.nonneg (3*(3*x/4-1))
  have hone := Real.smoothTransition.le_one (3*(x-1))
  rw [normPartitionWeight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hmono)]
  dsimp [normPartitionStep] at *
  linarith

lemma normPartitionWeight_telescope (x : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, normPartitionWeight (x/(4/3:ℝ)^k)) =
      (normPartitionStep x - normPartitionStep (x/(4/3:ℝ)^N) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,normPartitionWeight]
    have he : 3*(x/(4/3:ℝ)^N)/4 = x/(4/3:ℝ)^(N+1) := by
      rw [pow_succ]
      ring
    rw [he]
    push_cast
    ring

theorem normPartitionWeight_partition {B x : ℝ} {N : ℕ}
    (hx : 1 ≤ x) (hB : x ≤ B) (hN : 2*B ≤ (4/3:ℝ)^N) :
    (∑ k ∈ Finset.range N, normPartitionWeight (2*x/(4/3:ℝ)^k)) = 1 := by
  rw [normPartitionWeight_telescope,
    normPartitionStep_one (show 4/3 ≤ 2*x by linarith)]
  have hpow : 0 < (4/3:ℝ)^N := pow_pos (by norm_num) _
  rw [normPartitionStep_zero ((div_le_one hpow).mpr (by linarith))]
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteMellinProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Mellin separation of a finite product-norm weight. This is the
exact analytic bridge used after the smooth short-convolution partition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem smooth_mellin_finite {κ : Type*} [Fintype κ]
    (a : κ → ℂ) (N : κ → ℝ) (hN : ∀ i, 0 < N i)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (σ : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    (∑ i, a i*W (N i/Z)) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
        (∑ i, a i*(N i:ℂ)^(-(σ+(τ:ℂ)*Complex.I))) := by
  simpa only [normDirichletSeries,tsum_fintype] using
    smooth_mellin_series a N hN W hW hpos hsm σ (hasSum_fintype _).summable hZ

lemma nonnegative_product_cpow {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (hN : ∀ i ∈ S, 0 ≤ N i) (s : ℂ) :
    ((∏ i ∈ S, N i : ℝ):ℂ)^s = ∏ i ∈ S, (N i:ℂ)^s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hN i (Finset.mem_insert_self i S))
        (Finset.prod_nonneg (fun j hj => hN j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hN j (Finset.mem_insert_of_mem hj)),Finset.prod_insert hi]

theorem smooth_mellin_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (a : (i : ι) → κ i → ℂ) (N : (i : ι) → κ i → ℝ)
    (hN : ∀ i x, 0 < N i x)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (σ : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    (∑ x : (i : ι) → κ i, (∏ i, a i (x i))*W ((∏ i, N i (x i))/Z)) =
      ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
          ∏ i, (∑ x : κ i, a i x*(N i x:ℂ)^(-(σ+(τ:ℂ)*Complex.I))) := by
  rw [smooth_mellin_finite (fun x : (i : ι) → κ i => ∏ i, a i (x i))
    (fun x => ∏ i, N i (x i)) (fun x => Finset.prod_pos (fun i _ => hN i (x i)))
    W hW hpos hsm σ hZ]
  congr 1
  apply integral_congr_ae
  filter_upwards with τ
  congr 1
  rw [Fintype.prod_sum (fun (i : ι) (x : κ i) =>
    a i x*(N i x:ℂ)^(-(σ+(τ:ℂ)*Complex.I)))]
  apply Finset.sum_congr rfl
  intro x _
  rw [nonnegative_product_cpow _ _ (fun i _ => (hN i (x i)).le),Finset.prod_mul_distrib]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinMomentTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing an actual uniform finite-row moment through an integrable Mellin
weight. The proof is the triangle inequality in the finite Euclidean space. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem finite_row_integral_moment {Ω κ : Type*} [MeasurableSpace Ω]
    [Fintype κ] {μ : Measure Ω} (f : κ → Ω → ℂ) (w : Ω → ℂ)
    (hf : AEStronglyMeasurable (fun t => WithLp.toLp 2 (fun r => f r t)) μ)
    (hw : Integrable w μ) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ᵐ t ∂μ, (∑ r, ‖f r t‖^2) ≤ B) :
    (∑ r, ‖∫ t, w t*f r t ∂μ‖^2) ≤ (∫ t, ‖w t‖ ∂μ)^2*B := by
  let F : Ω → EuclideanSpace ℂ κ := fun t => WithLp.toLp 2 (fun r => f r t)
  let G : Ω → EuclideanSpace ℂ κ := fun t => w t • F t
  have hFn : ∀ᵐ t ∂μ, ‖F t‖ ≤ Real.sqrt B := by
    filter_upwards [hb] with t ht
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_sqrt ht
  have hGn : ∀ᵐ t ∂μ, ‖G t‖ ≤ ‖w t‖*Real.sqrt B := by
    filter_upwards [hFn] with t ht
    dsimp [G]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ht (_root_.norm_nonneg _)
  have hG : Integrable G μ := (hw.norm.mul_const (Real.sqrt B)).mono'
    (hw.aestronglyMeasurable.smul hf) hGn
  have hcoord (r : κ) : (∫ t, G t ∂μ) r = ∫ t, w t*f r t ∂μ := by
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : κ => ℂ) r).integral_comp_comm hG).symm
  have hbound : ‖∫ t, G t ∂μ‖ ≤ (∫ t, ‖w t‖ ∂μ)*Real.sqrt B := by
    apply (norm_integral_le_integral_norm G).trans
    rw [← integral_mul_const]
    exact integral_mono_ae hG.norm (hw.norm.mul_const _) hGn
  calc
    _ = ‖∫ t, G t ∂μ‖^2 := by rw [EuclideanSpace.norm_sq_eq]; simp_rw [hcoord]
    _ ≤ ((∫ t, ‖w t‖ ∂μ)*Real.sqrt B)^2 :=
      pow_le_pow_left₀ (_root_.norm_nonneg _) hbound 2
    _ = _ := by rw [mul_pow,Real.sq_sqrt hB]

theorem finite_interval_integral_moment {κ : Type*} [Fintype κ]
    (f : κ → ℝ → ℂ) (hf : ∀ r, Continuous (f r)) (w : ℝ → ℂ)
    (hw : Integrable w) (T B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t ∈ Set.Icc (-T) T, (∑ r, ‖f r t‖^2) ≤ B) :
    (∑ r, ‖∫ t in Set.Icc (-T) T, w t*f r t‖^2) ≤
      (∫ t, ‖w t‖)^2*B := by
  have hc : Continuous (fun t => WithLp.toLp 2 (fun r => f r t)) :=
    (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp (continuous_pi hf)
  have ha : ∀ᵐ t ∂(volume.restrict (Set.Icc (-T) T)), (∑ r, ‖f r t‖^2) ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hb t ht
  have h := finite_row_integral_moment f w hc.aestronglyMeasurable hw.restrict hB ha
  apply h.trans
  have hm : (∫ t in Set.Icc (-T) T, ‖w t‖) ≤ ∫ t, ‖w t‖ :=
    setIntegral_le_integral hw.norm (Filter.Eventually.of_forall (fun _ => _root_.norm_nonneg _))
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (integral_nonneg (fun _ => _root_.norm_nonneg _)) hm 2) hB

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortTupleMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin separation for the actual smooth short-inverse factors. The
integrand is a product of the original primary sums, with a common shift. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellinPhase_mul_neg_cpow {x : ℝ} (hx : 0 < x) (t τ : ℝ) :
    mellinPhase t x*(x:ℂ)^(-((τ:ℂ)*Complex.I)) = mellinPhase (t-τ) x := by
  rw [show -((τ:ℂ)*Complex.I) = ((-τ:ℝ):ℂ)*Complex.I by push_cast; ring,
    ← mellinPhase_eq_cpow hx]
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma primaryShortSmoothSum_eq_subtype (A : EisensteinArithmeticFunction)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ)
    {X : ℝ} (hX : 0 < X) (hW : ∀ x : ℝ, 2 < x → W x = 0) (t : ℝ) :
    primaryShortSmoothSum A a b q η W (X/2) t =
      ∑ n : primaryElementBall X,
        ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
          (mixedCubic a b n*η (Ideal.Quotient.mk (modulus q) n)*mellinPhase t (norm n))*
            W (norm n/(X/2)) := by
  rw [primaryShortSmoothSum_eq_polynomial A a b q η W (by linarith : 0 < X/2) hW,
    show 2*(X/2) = X by ring,primaryIdealPolynomial_eq_elements]
  symm
  change (∑ n ∈ (primaryElementBall X).attach, _) = _
  rw [Finset.sum_attach (f := fun n : Eisenstein =>
    ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
      (mixedCubic a b n*η (Ideal.Quotient.mk (modulus q) n)*mellinPhase t (norm n))*
        W (norm n/(X/2)))]
  apply Finset.sum_congr rfl
  intro n _
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primaryShortTupleSum_mellin (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hW : ∀ i x, 2 < x → W i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z) :
    primaryShortTupleSum X A a b q η W t V Z =
      ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin V ((τ:ℂ)*Complex.I)*(Z:ℂ)^((τ:ℂ)*Complex.I)*
          ∏ i, primaryShortSmoothSum (A i) a b (q i) (η i) (W i) (X i/2) (t i-τ) := by
  unfold primaryShortTupleSum
  rw [smooth_mellin_product
    (fun i (n : primaryElementBall (X i)) =>
      ((MvPowerSeries.coeff (idealExponentOf n) (A i):ℝ):ℂ)*
        (mixedCubic a b n*η i (Ideal.Quotient.mk (modulus (q i)) n)*
          mellinPhase (t i) (norm n))*W i (norm n/(X i/2)))
    (fun i (n : primaryElementBall (X i)) => norm n)
    (fun i n => norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp n.property).1))
    V hV hpos hsm 0 hZ]
  simp only [Complex.ofReal_zero,zero_add]
  congr 1
  apply integral_congr_ae
  filter_upwards with τ
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [primaryShortSmoothSum_eq_subtype (A i) a b (q i) (η i) (W i) (hX i) (hW i)]
  apply Finset.sum_congr rfl
  intro n _
  have hn : 0 < norm (n:Eisenstein) :=
    norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp n.property).1)
  rw [← mellinPhase_mul_neg_cpow hn]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothShortContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and Mellin weights for actual finite smooth short sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem continuous_primaryShortSmoothSum (A : EisensteinArithmeticFunction)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ)
    {X : ℝ} (hX : 0 < X) (hW : ∀ x : ℝ, 2 < x → W x = 0) :
    Continuous (primaryShortSmoothSum A a b q η W (X/2)) := by
  have he := funext (primaryShortSmoothSum_eq_subtype A a b q η W hX hW)
  rw [he]
  apply continuous_finsetSum
  intro n _
  unfold mellinPhase
  fun_prop

lemma zeroLineMellinWeight_norm (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (τ : ℝ) :
    ‖zeroLineMellinWeight V Z τ‖ =
      (1/(2*Real.pi))*‖mellin V ((τ:ℂ)*Complex.I)‖ := by
  rw [zeroLineMellinWeight,norm_mul,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,sub_self,Real.rpow_zero,mul_one,
    Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : (0:ℝ) < 1/(2*Real.pi))]

theorem zeroLineMellinWeight_integrable (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z) :
    Integrable (zeroLineMellinWeight V Z) := by
  have hm : Integrable (fun τ : ℝ => mellin V ((τ:ℂ)*Complex.I)) := by
    have h := smooth_mellin_vertical_integrable V hV hpos hsm 0
    change Integrable (fun τ : ℝ => mellin V ((0:ℂ)+(τ:ℂ)*Complex.I)) at h
    simpa only [zero_add] using h
  have hz : NeZero (Z:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hZ.ne'⟩
  have hp : Continuous (fun τ : ℝ => (Z:ℂ)^((τ:ℂ)*Complex.I)) :=
    (differentiable_const_cpow_of_neZero _).continuous.comp (by fun_prop)
  have ha : AEStronglyMeasurable (zeroLineMellinWeight V Z) :=
    ((hm.aestronglyMeasurable.const_mul _).mul hp.aestronglyMeasurable)
  exact (hm.norm.const_mul (1/(2*Real.pi))).mono' ha
    (Filter.Eventually.of_forall (fun τ => (zeroLineMellinWeight_norm V hZ τ).le))

lemma zeroLineMellinWeight_mass (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) :
    (∫ τ : ℝ, ‖zeroLineMellinWeight V Z τ‖) = zeroLineMellinMass V := by
  simp_rw [zeroLineMellinWeight_norm V hZ]
  exact integral_const_mul _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TruncatedProductMoment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The central Mellin integral inherits the proved exceptional product
moment, with a constant independent of the outer norm scale. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eventual_shifted_height_bound :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ t τ : ℝ,
      |t| ≤ Y^(361/1000:ℝ) → |τ| ≤ Y^(9/25:ℝ) → |t-τ| ≤ Y^(37/100:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 9/1000 by norm_num)).eventually_ge_atTop (2:ℝ))
  refine ⟨max 1 T,?_⟩
  intro Y hY t τ ht hτ
  have hYp : 0 < Y := zero_lt_one.trans_le ((le_max_left _ _).trans hY)
  have hτ' : |τ| ≤ Y^(361/1000:ℝ) := hτ.trans
    (Real.rpow_le_rpow_of_exponent_le ((le_max_left _ _).trans hY) (by norm_num))
  calc
    _ ≤ |t|+|τ| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le t 0 τ
    _ ≤ 2*Y^(361/1000:ℝ) := by linarith
    _ ≤ Y^(9/1000:ℝ)*Y^(361/1000:ℝ) :=
      mul_le_mul_of_nonneg_right (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedTruncatedNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Central Mellin transfer preserving the proved conductor neighborhood. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem balanced_truncated_neighborhood_moment (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein))
      (V : ℝ → ℂ) (Z : ℝ),
      Y₀ ≤ Y → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) → HasCompactSupport V → tsupport V ⊆ Ioi 0 →
      ContDiff ℝ ∞ V → 0 < Z →
      (∑ a : P, ‖∫ τ in Icc (-(Y^(9/25:ℝ))) (Y^(9/25:ℝ)),
        zeroLineMellinWeight V Z τ*
          ∏ i, primaryShortSmoothSum (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)‖^2) ≤
        (zeroLineMellinMass V)^2*Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := balanced_smooth_product_neighborhood hpub hHuxley
    (fun _ : ι => normPartitionWeight) (fun _ => normPartitionWeight_compact)
    (fun _ => normPartitionWeight_positive_support) (fun _ => normPartitionWeight_smooth)
    (fun _ _ hx => normPartitionWeight_low hx) (fun _ _ hx => normPartitionWeight_high hx)
    (fun _ => normPartitionWeight_norm) hGI hGQ hD
  obtain ⟨T₁,hheight⟩ := eventual_shifted_height_bound
  refine ⟨κ,hκ,hκhi,ε,hε,max 1 (max T T₁),?_⟩
  intro F Y X A q η t P V Z hY hF hA hX hlo hhi hq hη hqY ht hP hV hpos hsm hZ
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYT : T ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hY)
  let f : P → ℝ → ℂ := fun a τ =>
    ∏ i, primaryShortSmoothSum (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)
  have hf (a : P) : Continuous (f a) := by
    apply continuous_finsetProd
    intro i _
    exact (continuous_primaryShortSmoothSum (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight
      (by linarith [hX i]) (fun _ hx => normPartitionWeight_high hx)).comp
        (continuous_const.sub continuous_id)
  have hb (τ : ℝ) (hτ : τ ∈ Icc (-(Y^(9/25:ℝ))) (Y^(9/25:ℝ))) :
      (∑ a : P, ‖f a τ‖^2) ≤ Y^(7/3-ε) := by
    have hτabs : |τ| ≤ Y^(9/25:ℝ) := abs_le.mpr hτ
    have hm := hbound F Y X A q η (fun i => t i-τ) P hYT hF hA hX hlo hhi hq hη hqY
      (fun i => hheight Y hYT₁ (t i) τ (ht i) hτabs) hP
    change (∑ a ∈ P.attach, ‖f a τ‖^2) ≤ _
    dsimp only [f]
    rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
      ‖∏ i, primaryShortSmoothSum (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i)
        normPartitionWeight (X i/2) (t i-τ)‖^2)]
    exact hm
  have hm := finite_interval_integral_moment f hf (zeroLineMellinWeight V Z)
    (zeroLineMellinWeight_integrable V hV hpos hsm hZ) (Y^(9/25:ℝ))
    (Y^(7/3-ε)) (Real.rpow_nonneg (zero_le_one.trans hY1) _) hb
  rwa [zeroLineMellinWeight_mass V hZ] at hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinHeightTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rapid Mellin truncation with an explicit integrable moment. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma outside_interval_abs {T t : ℝ} (ht : t ∈ (Icc (-T) T)ᶜ) : T ≤ |t| := by
  by_contra h
  have ha : |t| < T := lt_of_not_ge h
  exact ht ⟨by linarith [neg_abs_le t],by linarith [le_abs_self t]⟩

lemma weighted_height_tail (w : ℝ → ℂ) (hw : Integrable w) (A : ℕ)
    (hA : Integrable (fun t : ℝ => |t|^A*‖w t‖)) {T : ℝ} (hT : 0 < T) :
    (∫ t in (Icc (-T) T)ᶜ, ‖w t‖) ≤
      (∫ t : ℝ, |t|^A*‖w t‖)/T^A := by
  apply (le_div_iff₀ (pow_pos hT A)).mpr
  rw [mul_comm,← integral_const_mul]
  apply (integral_mono_ae (hw.norm.restrict.const_mul _) hA.restrict ?_).trans
    (setIntegral_le_integral hA (Filter.Eventually.of_forall (fun _ => by positivity)))
  filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hT.le (outside_interval_abs ht) A) (_root_.norm_nonneg _)

lemma bounded_product_height_tail (w f : ℝ → ℂ) (hw : Integrable w) (A : ℕ)
    (hA : Integrable (fun t : ℝ => |t|^A*‖w t‖)) {T B : ℝ}
    (hT : 0 < T) (hB : 0 ≤ B) (hf : ∀ t, ‖f t‖ ≤ B) :
    ‖∫ t in (Icc (-T) T)ᶜ, w t*f t‖ ≤
      (B/T^A)*(∫ t : ℝ, |t|^A*‖w t‖) := by
  have hn : ‖∫ t in (Icc (-T) T)ᶜ, w t*f t‖ ≤
      B*(∫ t in (Icc (-T) T)ᶜ, ‖w t‖) := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hw.norm.restrict.const_mul B)
    filter_upwards with t
    rw [norm_mul,mul_comm B]
    exact mul_le_mul_of_nonneg_left (hf t) (_root_.norm_nonneg _)
  calc
    _ ≤ B*(∫ t in (Icc (-T) T)ᶜ, ‖w t‖) := hn
    _ ≤ B*((∫ t : ℝ, |t|^A*‖w t‖)/T^A) :=
      mul_le_mul_of_nonneg_left (weighted_height_tail w hw A hA hT) hB
    _ = _ := by ring

theorem zeroLineMellinWeight_moment_integrable (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ V)
    {Z : ℝ} (hZ : 0 < Z) (A : ℕ) :
    Integrable (fun t : ℝ => |t|^A*‖zeroLineMellinWeight V Z t‖) := by
  let F := mellinVerticalSchwartz V hV hpos hsm 0
  have h := (F.integrable_pow_mul volume A).const_mul (1/(2*Real.pi))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  rw [zeroLineMellinWeight_norm V hZ]
  dsimp [F]
  rw [mellinVerticalSchwartz_apply]
  simp only [Complex.ofReal_zero,zero_add]
  ring

lemma zeroLineMellinWeight_moment (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (A : ℕ) :
    (∫ t : ℝ, |t|^A*‖zeroLineMellinWeight V Z t‖) =
      (1/(2*Real.pi))*(∫ t : ℝ, |t|^A*‖mellin V ((t:ℂ)*Complex.I)‖) := by
  simp_rw [zeroLineMellinWeight_norm V hZ]
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullMellinMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joining the central Mellin moment to a proved rapid tail bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma norm_square_le_central_tail (x y : ℂ) {H : ℝ} (h : ‖x-y‖ ≤ H) :
    ‖x‖^2 ≤ 2*‖y‖^2+2*H^2 := by
  have hx : ‖x‖ ≤ ‖y‖+H := by
    calc
      _ = ‖y+(x-y)‖ := by congr 1; ring
      _ ≤ ‖y‖+‖x-y‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl h
  have hH : 0 ≤ H := (_root_.norm_nonneg _).trans h
  have hsq := pow_le_pow_left₀ (_root_.norm_nonneg _) hx 2
  nlinarith [sq_nonneg (‖y‖-H),sq_nonneg ‖x‖]

theorem full_mellin_moment_of_central {κ : Type*} [Fintype κ]
    (f : κ → ℝ → ℂ) (hf : ∀ r, Continuous (f r)) (w : ℝ → ℂ)
    (hw : Integrable w) (A : ℕ) (hA : Integrable (fun t : ℝ => |t|^A*‖w t‖))
    {T L M : ℝ} (hT : 0 < T) (hL : 0 ≤ L) (hsize : ∀ r t, ‖f r t‖ ≤ L)
    (hcentral : (∑ r, ‖∫ t in Icc (-T) T, w t*f r t‖^2) ≤ M) :
    (∑ r, ‖∫ t, w t*f r t‖^2) ≤ 2*M+
      2*(Fintype.card κ:ℝ)*((L/T^A)*(∫ t : ℝ, |t|^A*‖w t‖))^2 := by
  let H := (L/T^A)*(∫ t : ℝ, |t|^A*‖w t‖)
  have happrox (r : κ) :
      ‖(∫ t, w t*f r t)-(∫ t in Icc (-T) T, w t*f r t)‖ ≤ H := by
    have hi : Integrable (fun t => w t*f r t) := (hw.norm.mul_const L).mono'
      (hw.aestronglyMeasurable.mul (hf r).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun t => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hsize r t) (_root_.norm_nonneg _)))
    rw [← integral_add_compl measurableSet_Icc hi,add_sub_cancel_left]
    exact bounded_product_height_tail w (f r) hw A hA hT hL (hsize r)
  calc
    _ ≤ ∑ r, (2*‖∫ t in Icc (-T) T, w t*f r t‖^2+2*H^2) :=
      Finset.sum_le_sum (fun r _ => norm_square_le_central_tail _ _ (happrox r))
    _ = 2*(∑ r, ‖∫ t in Icc (-T) T, w t*f r t‖^2)+2*(Fintype.card κ:ℝ)*H^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _ ≤ _ := by dsimp [H]; nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinMomentPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed powers in the central-plus-tail short-convolution estimate. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem absorb_short_mellin_bounds {ε : ℝ} (hε : 0 < ε) (C E : ℝ)
    (hC : 0 ≤ C) (hE : 0 ≤ E) :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      C*Y^(7/3-ε)+E*Y^(-42/5:ℝ) ≤ Y^(7/3-min ε (1/3)/2) := by
  let η := min ε (1/3:ℝ)
  have hη : 0 < η := lt_min hε (by norm_num)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < η/2 by linarith)).eventually_ge_atTop (C+E))
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hηε : η ≤ ε := min_le_left _ _
  have hη3 : η ≤ 1/3 := min_le_right _ _
  calc
    _ ≤ C*Y^(7/3-η)+E*Y^(7/3-η) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)) hC
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)) hE
    _ = (C+E)*Y^(7/3-η) := by ring
    _ ≤ Y^(η/2)*Y^(7/3-η) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; dsimp [η]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortProductSize
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform trivial product bound used only to control Mellin tails. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem short_family_product_size :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ShortFactorFamily ι) (j : ℕ) (a b : Eisenstein),
      primary a → primary b →
      ‖∏ i, F.mixedValue j i (a,b)‖ ≤ C*(∏ i, F.length j i)^2 := by
  obtain ⟨K,hK,hbound⟩ := shortFactorPolynomial_norm_small_power (show (0:ℝ) < 1 by norm_num)
  refine ⟨K^(Fintype.card ι),pow_pos hK _,?_⟩
  intro F j a b ha hb
  have hi (i : ι) : ‖F.mixedValue j i (a,b)‖ ≤ K*(F.length j i)^2 := by
    have h := hbound (F.cutoff j) (F.length j i) (F.coefficient j i)
      (F.factor_spec j i) (F.length_ge_one j i)
      (fun n => F.twist j i n*mixedCubic a b n) (by
        intro n hn
        rw [norm_mul]
        exact (mul_le_mul (F.twist_bound j i n hn) (norm_mixedCubic_le_one ha hb n)
          (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    simpa only [ShortFactorFamily.mixedValue,show (1+(1:ℝ)) = 2 by norm_num,
      Real.rpow_two] using h
  calc
    _ = ∏ i, ‖F.mixedValue j i (a,b)‖ := norm_prod _ _
    _ ≤ ∏ i, K*(F.length j i)^2 := Finset.prod_le_prod
      (fun _ _ => _root_.norm_nonneg _) (fun i _ => hi i)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.prod_pow,Finset.card_univ]

omit [DecidableEq ι] in
theorem smooth_short_product_size {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ)
      (t : ι → ℝ) (a b : Eisenstein),
      (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
      (∏ i, X i) ≤ D*Y → primary a → primary b →
      ‖∏ i, primaryShortSmoothSum (A i) a b (q i) (η i) (W i) (X i/2) (t i)‖ ≤ C*Y^2 := by
  obtain ⟨C,hC,hbound⟩ := short_family_product_size (ι := ι)
  refine ⟨C*D^2,mul_pos hC (sq_pos_of_pos hD),?_⟩
  intro F Y X A q η W t a b hA hX hq hW hcut hprod ha hb
  let K := shortFamilyOfSmoothWeights F X A q η W t hA hX hq hW
  have h := hbound K 0 a b ha hb
  simp only [K,smoothShortFamily_mixedValue F X A q η W t hA hX hq hW hcut] at h
  apply h.trans
  have hp := pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hX i))) hprod 2
  calc
    _ ≤ C*(D*Y)^2 := mul_le_mul_of_nonneg_left hp hC.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FirstWeightedTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full first-configuration moment for the actual smooth weighted
short-factor tuple. Mellin separation includes the complementary tails. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primaryShortTupleSum_integral (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hW : ∀ i x, 2 < x → W i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z) :
    primaryShortTupleSum X A a b q η W t V Z =
      ∫ τ : ℝ, zeroLineMellinWeight V Z τ*
        ∏ i, primaryShortSmoothSum (A i) a b (q i) (η i) (W i) (X i/2) (t i-τ) := by
  rw [primaryShortTupleSum_mellin X A a b q η W t hX hW V hV hpos hsm hZ,
    ← integral_const_mul]
  congr 1
  funext τ
  unfold zeroLineMellinWeight
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothTuplePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit smooth partition inserted into finite convolution tuples.
Nonzero pieces automatically have the required product-length comparability. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normTupleWeight_partition {B : ℝ} {N : ℕ} (x : ι → ℝ)
    (hx : ∀ i, 1 ≤ x i) (hB : ∀ i, x i ≤ B) (hN : 2*B ≤ (4/3:ℝ)^N) :
    (∑ k : ι → Fin N, normTupleWeight k x) = 1 := by
  unfold normTupleWeight
  rw [← Fintype.prod_sum (fun (i : ι) (k : Fin N) =>
    normPartitionWeight (2*x i/(4/3:ℝ)^k.val))]
  have hi (i : ι) : (∑ k : Fin N, normPartitionWeight (2*x i/(4/3:ℝ)^k.val)) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => normPartitionWeight (2*x i/(4/3:ℝ)^k))]
    exact normPartitionWeight_partition (hx i) (hB i) hN
  simp_rw [hi]
  simp

theorem finite_sum_normTupleWeight {κ : Type*} (S : Finset κ) (f : κ → ℂ)
    (x : κ → ι → ℝ) {B : ℝ} {N : ℕ}
    (hx : ∀ a ∈ S, ∀ i, 1 ≤ x a i) (hB : ∀ a ∈ S, ∀ i, x a i ≤ B)
    (hN : 2*B ≤ (4/3:ℝ)^N) :
    (∑ a ∈ S, f a) = ∑ k : ι → Fin N, ∑ a ∈ S, f a*normTupleWeight k (x a) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.mul_sum,normTupleWeight_partition (x a) (hx a ha) (hB a ha) hN,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothPartitionCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete truncation and subpower cost for the smooth norm partition. -/
noncomputable section
namespace CubicFirstMoment

lemma normPartitionCount_covers {B : ℝ} (hB : 1 ≤ B) :
    2*B ≤ (4/3:ℝ)^normPartitionCount B := by
  have hr : 0 < Real.log (4/3:ℝ) := Real.log_pos (by norm_num)
  apply (Real.log_le_log_iff (by linarith : 0 < 2*B)
    (pow_pos (by norm_num : (0:ℝ) < 4/3) _)).mp
  rw [Real.log_pow]
  exact (div_le_iff₀ hr).mp (Nat.le_ceil _)

theorem normPartitionCount_log_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ B : ℝ, 1 ≤ B →
      (normPartitionCount B : ℝ) ≤ K*(1+Real.log B) := by
  let r := Real.log (4/3:ℝ)
  have hr : 0 < r := Real.log_pos (by norm_num)
  let a := 1+Real.log 2/r
  let b := 1/r
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨a+b,by linarith,?_⟩
  intro B hB
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hn := (Nat.ceil_lt_add_one
    (div_nonneg (Real.log_nonneg (by linarith : 1 ≤ 2*B)) hr.le)).le
  change (normPartitionCount B : ℝ) ≤ _ at hn
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by linarith : B ≠ 0),add_div] at hn
  have he : Real.log 2/r+Real.log B/r+1 = a+b*Real.log B := by dsimp [a,b]; ring
  apply hn.trans
  rw [he]
  nlinarith [mul_nonneg ha hlog]

theorem normPartitionCount_power_bound (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      (normPartitionCount B : ℝ)^d ≤ C*B^ε := by
  obtain ⟨K,hK,hcount⟩ := normPartitionCount_log_bound
  have hd : 0 < (d:ℝ)+1 := by positivity
  obtain ⟨A,hA,hlog⟩ := one_add_log_small_power (div_pos hε hd)
  refine ⟨(K*A)^d,pow_pos (mul_pos hK hA) _,?_⟩
  intro B hB
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hnb : (normPartitionCount B : ℝ) ≤ (K*A)*B^(ε/((d:ℝ)+1)) :=
    (hcount B hB).trans (by
      calc
        K*(1+Real.log B) ≤ K*(A*B^(ε/((d:ℝ)+1))) :=
          mul_le_mul_of_nonneg_left (hlog B hB) hK.le
        _ = _ := by ring)
  have he : ε/((d:ℝ)+1)*(d:ℝ) ≤ ε := by
    have hm := div_mul_cancel₀ ε hd.ne'
    have hp : 0 < ε/((d:ℝ)+1) := div_pos hε hd
    nlinarith
  calc
    _ ≤ ((K*A)*B^(ε/((d:ℝ)+1)))^d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hnb d
    _ = (K*A)^d*B^(ε/((d:ℝ)+1)*(d:ℝ)) := by
      rw [mul_pow,← Real.rpow_mul_natCast hBp.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB he) (pow_nonneg (mul_pos hK hA).le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PartitionMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the explicit smooth norm partition loses only a small part of
an established power saving. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_piece_moment {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (f : κ → ρ → ℂ) :
    (∑ r, ‖∑ k, f k r‖^2) ≤ (Fintype.card κ:ℝ)*(∑ k, ∑ r, ‖f k r‖^2) := by
  calc
    _ ≤ ∑ r, (Fintype.card κ:ℝ)*(∑ k, ‖f k r‖^2) := by
      apply Finset.sum_le_sum
      intro r _
      apply (pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_sum_le _ _) 2).trans
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : κ => (1:ℝ))
        (fun k => ‖f k r‖)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_partition_moment_power {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y → ∀ (ρ : Type*) [Fintype ρ]
      (f : (ι → Fin (normPartitionCount (2*Y))) → ρ → ℂ),
      (∀ k, (∑ r, ‖f k r‖^2) ≤ Y^(7/3-ε)) →
      (∑ r, ‖∑ k, f k r‖^2) ≤ Y^(7/3-ε/2) := by
  obtain ⟨C,hC,hcount⟩ := normPartitionCount_power_bound (2*Fintype.card ι)
    (show 0 < ε/4 by linarith)
  let K : ℝ := C*2^(ε/4)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < ε/4 by linarith)).eventually_ge_atTop K)
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY ρ _ f hf
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hc : ((Fintype.card (ι → Fin (normPartitionCount (2*Y)))):ℝ)^2 ≤ K*Y^(ε/4) := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,← pow_mul]
    rw [Nat.mul_comm]
    apply (hcount (2*Y) (by linarith)).trans_eq
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hYp.le]
    dsimp [K]
    ring
  calc
    _ ≤ (Fintype.card (ι → Fin (normPartitionCount (2*Y))):ℝ)*
        (∑ k, ∑ r, ‖f k r‖^2) := finite_piece_moment f
    _ ≤ (Fintype.card (ι → Fin (normPartitionCount (2*Y))):ℝ)^2*Y^(7/3-ε) := by
      calc
        _ ≤ (Fintype.card (ι → Fin (normPartitionCount (2*Y))):ℝ)*
            (∑ _k : ι → Fin (normPartitionCount (2*Y)), Y^(7/3-ε)) := by
          apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hf k))
            (Nat.cast_nonneg _)
        _ = _ := by simp; ring
    _ ≤ (K*Y^(ε/4))*Y^(7/3-ε) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hYp.le _)
    _ = K*Y^(7/3-3*ε/4) := by
      rw [mul_assoc,← Real.rpow_add hYp,
        show ε/4+(7/3-ε) = 7/3-3*ε/4 by ring]
    _ ≤ Y^(ε/4)*Y^(7/3-3*ε/4) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortTupleScales
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonzero smooth convolution piece automatically has comparable total
length. Thus the moment hypotheses need not be imposed on empty pieces. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma normPartitionWeight_nonzero_length {x X : ℝ} (hX : 0 < X)
    (h : normPartitionWeight (x/(X/2)) ≠ 0) : x ≤ X ∧ X ≤ 2*x := by
  have hp : 0 < X/2 := by linarith
  have hlo : 1 ≤ x/(X/2) := by
    by_contra hn
    exact h (normPartitionWeight_low (lt_of_not_ge hn))
  have hhi : x/(X/2) ≤ 2 := by
    by_contra hn
    exact h (normPartitionWeight_high (lt_of_not_ge hn))
  have h₁ := (le_div_iff₀ hp).mp hlo
  have h₂ := (div_le_iff₀ hp).mp hhi
  constructor <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primaryShortTupleSum_nonzero_scales (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hX : ∀ i, 0 < X i) (hZ : 0 < Z)
    (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (h : primaryShortTupleSum X A a b q η (fun _ => normPartitionWeight) t V Z ≠ 0) :
    Z ≤ ∏ i, X i ∧ (∏ i, X i) ≤ (2:ℝ)^(Fintype.card ι+1)*Z := by
  unfold primaryShortTupleSum at h
  obtain ⟨n,_,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hp := (mul_ne_zero_iff.mp hn).1
  have hv := (mul_ne_zero_iff.mp hn).2
  have hi (i : ι) : norm (n i:Eisenstein) ≤ X i ∧ X i ≤ 2*norm (n i:Eisenstein) := by
    apply normPartitionWeight_nonzero_length (hX i)
    exact (mul_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i))).2
  have hlo : 1 ≤ (∏ i, norm (n i:Eisenstein))/Z := by
    by_contra hlt
    exact hv (hVlo _ (lt_of_not_ge hlt))
  have hhi : (∏ i, norm (n i:Eisenstein))/Z ≤ 2 := by
    by_contra hgt
    exact hv (hVhi _ (lt_of_not_ge hgt))
  constructor
  · simpa only [one_mul] using ((le_div_iff₀ hZ).mp hlo).trans
      (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (hi i).1))
  · calc
      _ ≤ ∏ i, 2*norm (n i:Eisenstein) := Finset.prod_le_prod
        (fun i _ => (hX i).le) (fun i _ => (hi i).2)
      _ = (2:ℝ)^(Fintype.card ι)*(∏ i, norm (n i:Eisenstein)) := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
      _ ≤ (2:ℝ)^(Fintype.card ι)*(2*Z) :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hZ).mp hhi) (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem primaryShortTupleSum_zero_outside_scales (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hX : ∀ i, 0 < X i) (hZ : 0 < Z)
    (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hscale : ¬(Z ≤ ∏ i, X i ∧ (∏ i, X i) ≤ (2:ℝ)^(Fintype.card ι+1)*Z)) :
    primaryShortTupleSum X A a b q η (fun _ => normPartitionWeight) t V Z = 0 := by
  by_contra h
  exact hscale (primaryShortTupleSum_nonzero_scales X A a b q η t V hX hZ hVlo hVhi h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortTuplePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction of the original finite convolution from smooth
norm pieces. The common ball is forced by the global product cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_primary_pi (X : ι → ℝ) (f : (ι → Eisenstein) → ℂ) :
    (∑ n : (i : ι) → primaryElementBall (X i), f (fun i => n i)) =
      ∑ n ∈ Fintype.piFinset (fun i => primaryElementBall (X i)), f n := by
  apply Finset.sum_bij (fun n _ i => (n i : Eisenstein))
  · intro n _
    exact Fintype.mem_piFinset.mpr (fun i => (n i).property)
  · intro n _ m _ h
    funext i
    exact Subtype.ext (congrFun h i)
  · intro n hn
    exact ⟨fun i => ⟨n i,(Fintype.mem_piFinset.mp hn) i⟩,Finset.mem_univ _,rfl⟩
  · intro n _
    rfl

lemma primaryShortTupleSum_eq_core (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) (Z : ℝ) :
    primaryShortTupleSum X A a b q η (fun _ => normPartitionWeight) t V Z =
      ∑ n ∈ Fintype.piFinset (fun i => primaryElementBall (X i)),
        primaryTupleCore A a b q η t V Z n*
          ∏ i, normPartitionWeight (norm (n i)/(X i/2)) := by
  unfold primaryShortTupleSum
  calc
    _ = ∑ n : (i : ι) → primaryElementBall (X i),
        primaryTupleCore A a b q η t V Z (fun i => n i)*
          ∏ i, normPartitionWeight (norm (n i)/(X i/2)) := by
      apply Finset.sum_congr rfl
      intro n _
      unfold primaryTupleCore
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := sum_primary_pi X (fun n => primaryTupleCore A a b q η t V Z n*
      ∏ i, normPartitionWeight (norm (n i)/(X i/2)))

omit [DecidableEq ι] in
lemma primaryTupleCore_support (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (hV : ∀ x, 2 < x → V x = 0)
    (n : ι → Eisenstein) (hn : ∀ i, primary (n i))
    (h : primaryTupleCore A a b q η t V Z n ≠ 0) (i : ι) : norm (n i) ≤ 2*Z := by
  have hv := (mul_ne_zero_iff.mp h).2
  have hp : (∏ j, norm (n j))/Z ≤ 2 := by
    by_contra hgt
    exact hv (hV _ (lt_of_not_ge hgt))
  have hni : norm (n i) ≤ ∏ j, norm (n j) := by
    calc
      _ = ∏ j ∈ ({i} : Finset ι), norm (n j) := by simp
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le (by simp)
        (fun j _ => norm_nonneg _) (fun j _ _ => one_le_norm (primary_ne_zero (hn j)))
  exact hni.trans ((div_le_iff₀ hZ).mp hp)

lemma primaryShortTupleSum_common_ball (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (hV : ∀ x, 2 < x → V x = 0)
    (hX : ∀ i, 0 < X i) :
    primaryShortTupleSum X A a b q η (fun _ => normPartitionWeight) t V Z =
      ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Z)),
        primaryTupleCore A a b q η t V Z n*
          ∏ i, normPartitionWeight (norm (n i)/(X i/2)) := by
  rw [primaryShortTupleSum_eq_core]
  apply Finset.sum_bij_ne_zero (fun n _ _ => n)
  · intro n hn h
    have hc := (mul_ne_zero_iff.mp h).1
    exact Fintype.mem_piFinset.mpr (fun i => mem_primaryElementBall.mpr
      ⟨(mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1,
        primaryTupleCore_support A a b q η t V hZ hV n
          (fun j => (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) j)).1) hc i⟩)
  · intro n _ _ m _ _ h
    exact h
  · intro n hn h
    refine ⟨n,Fintype.mem_piFinset.mpr (fun i => ?_),h,rfl⟩
    have hw := (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp h).2) i (Finset.mem_univ i)
    exact mem_primaryElementBall.mpr
      ⟨(mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1,
        (normPartitionWeight_nonzero_length (hX i) hw).1⟩
  · intro n _ _
    rfl

/-- The unsplit finite tuple sum is exactly the sum of its explicit smooth
pieces. No decomposition hypothesis is assumed. -/
theorem primaryShortTupleSum_partition (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hZ : 1 ≤ Z) (hV : ∀ x, 2 < x → V x = 0) :
    (∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Z)),
      primaryTupleCore A a b q η t V Z n) =
      ∑ k : ι → Fin (normPartitionCount (2*Z)),
        primaryShortTupleSum (fun i => (4/3:ℝ)^(k i).val) A a b q η
          (fun _ => normPartitionWeight) t V Z := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  rw [finite_sum_normTupleWeight (Fintype.piFinset (fun _ : ι => primaryElementBall (2*Z)))
    (primaryTupleCore A a b q η t V Z) (fun n i => norm (n i))
    (fun n hn i => one_le_norm (primary_ne_zero
      (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1))
    (fun n hn i => (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).2)
    (normPartitionCount_covers (by linarith : 1 ≤ 2*Z))]
  apply Finset.sum_congr rfl
  intro k _
  rw [primaryShortTupleSum_common_ball _ A a b q η t V hZp hV
    (fun i => pow_pos (by norm_num) _)]
  apply Finset.sum_congr rfl
  intro n _
  unfold normTupleWeight
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NeighborhoodTailPower
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A thirtieth Mellin moment handles the larger row count uniformly across
both exceptional conductor neighborhoods. -/
noncomputable section
namespace CubicFirstMoment

lemma neighborhood_mellin_tail_power {Y K J : ℝ} (hY : 0 < Y) :
    2*Y^4*((K*Y^2/(Y^(9/25:ℝ))^30)*J)^2 =
      (2*K^2*J^2)*Y^(-68/5:ℝ) := by
  have hp : (Y^(9/25:ℝ))^30 = Y^(54/5:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le]
    norm_num
  have hd : Y^2/Y^(54/5:ℝ) = Y^(-44/5:ℝ) := by
    rw [← Real.rpow_two,← Real.rpow_sub hY]
    norm_num
  rw [hp,show K*Y^2/Y^(54/5:ℝ) = K*(Y^2/Y^(54/5:ℝ)) by ring,hd]
  have he : Y^4*(Y^(-44/5:ℝ))^2 = Y^(-68/5:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le,← Real.rpow_natCast,← Real.rpow_add hY]
    norm_num
  calc
    _ = (2*K^2*J^2)*(Y^4*(Y^(-44/5:ℝ))^2) := by ring
    _ = _ := by rw [he]

lemma neighborhood_mellin_tail_le {Y K J : ℝ} (hY : 1 ≤ Y) :
    2*Y^4*((K*Y^2/(Y^(9/25:ℝ))^30)*J)^2 ≤
      (2*K^2*J^2)*Y^(-42/5:ℝ) := by
  rw [neighborhood_mellin_tail_power (zero_lt_one.trans_le hY)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedWeightedNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full weighted short-tuple moments throughout the exceptional conductor
neighborhood, with an explicit thirtieth-moment tail. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem balanced_weighted_tuple_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)) (Z : ℝ),
      Y₀ ≤ Y → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) → 0 < Z →
      (∑ a ∈ P, ‖primaryShortTupleSum X A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η
        (fun _ => normPartitionWeight) t V Z‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hcentral⟩ := balanced_truncated_neighborhood_moment (ι := ι) hpub hHuxley hGI hGQ hD
  obtain ⟨K,hK,hsize⟩ := smooth_short_product_size (ι := ι) hD
  let J : ℝ := (1/(2*Real.pi))*(∫ τ : ℝ, |τ|^30*‖mellin V ((τ:ℂ)*Complex.I)‖)
  obtain ⟨T₁,hT₁,habsorb⟩ := absorb_short_mellin_bounds hε
    (2*(zeroLineMellinMass V)^2) (2*K^2*J^2) (by positivity) (by positivity)
  refine ⟨κ,hκ,hκhi,min ε (1/3)/2,div_pos (lt_min hε (by norm_num)) (by norm_num),
    max 324 (max T T₁),?_⟩
  intro F Y X A q η t P Z hY hF hA hX hlo hhi hq hη hqY ht hP hZ
  have hY324 : 324 ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 < Y := by linarith
  have hYT : T ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hY)
  let f : P → ℝ → ℂ := fun a τ =>
    ∏ i, primaryShortSmoothSum (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)
  have hf (a : P) : Continuous (f a) := by
    apply continuous_finsetProd
    intro i _
    exact (continuous_primaryShortSmoothSum (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight
      (by linarith [hX i]) (fun _ hx => normPartitionWeight_high hx)).comp
        (continuous_const.sub continuous_id)
  have hs (a : P) (τ : ℝ) : ‖f a τ‖ ≤ K*Y^2 := by
    exact hsize F Y X A q η (fun _ => normPartitionWeight) (fun i => t i-τ) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2
      hA hX hq (fun _ => normPartitionWeight_norm)
      (fun _ _ hx => normPartitionWeight_high hx) hhi (hP a a.property).1.1 (hP a a.property).1.2.1
  have hc := hcentral F Y X A q η t P V Z hYT hF hA hX hlo hhi hq hη hqY ht hP hV hpos hsm hZ
  have hm := full_mellin_moment_of_central f hf (zeroLineMellinWeight V Z)
    (zeroLineMellinWeight_integrable V hV hpos hsm hZ) 30
    (zeroLineMellinWeight_moment_integrable V hV hpos hsm hZ 30)
    (Real.rpow_pos_of_pos hY0 _) (mul_nonneg hK.le (sq_nonneg Y)) hs hc
  rw [zeroLineMellinWeight_moment V hZ 30] at hm
  have hY1 : 1 ≤ Y := by linarith
  have hLY : Y^(1/3+κ) ≤ Y := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY1
      (by linarith : 1/3+κ ≤ 1)
  have hcard : (Fintype.card P:ℝ) ≤ Y^4 := by
    simpa only [Fintype.card_coe] using neighborhood_balanced_card P hY324
      (Real.rpow_nonneg hY0.le _) hLY
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.1⟩)
  have he (a : Eisenstein × Eisenstein) : primaryShortTupleSum X A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η
      (fun _ => normPartitionWeight) t V Z = ∫ τ, zeroLineMellinWeight V Z τ*
        ∏ i, primaryShortSmoothSum (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight (X i/2) (t i-τ) :=
    primaryShortTupleSum_integral X A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun _ => normPartitionWeight) t
      (fun i => by linarith [hX i]) (fun _ _ hx => normPartitionWeight_high hx) V hV hpos hsm hZ
  apply le_trans _ (habsorb Y hYT₁)
  calc
    _ = ∑ a : P, ‖∫ τ, zeroLineMellinWeight V Z τ*f a τ‖^2 := by
      simp_rw [he]
      symm
      change (∑ a ∈ P.attach, _) = _
      exact Finset.sum_attach P (fun a =>
        ‖∫ τ, zeroLineMellinWeight V Z τ*∏ i,
          primaryShortSmoothSum (A i) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)‖^2)
    _ ≤ 2*((zeroLineMellinMass V)^2*Y^(7/3-ε))+
        2*(Fintype.card P:ℝ)*((K*Y^2/(Y^(9/25:ℝ))^30)*J)^2 := hm
    _ ≤ 2*((zeroLineMellinMass V)^2*Y^(7/3-ε))+
        2*Y^4*((K*Y^2/(Y^(9/25:ℝ))^30)*J)^2 := by gcongr
    _ ≤ (2*(zeroLineMellinMass V)^2)*Y^(7/3-ε)+(2*K^2*J^2)*Y^(-42/5:ℝ) := by
      simpa only [mul_assoc] using add_le_add
        (le_refl (2*((zeroLineMellinMass V)^2*Y^(7/3-ε))))
        (neighborhood_mellin_tail_le (K := K) (J := J) hY1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedUnsplitNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact norm-partition reconstruction preserves the exceptional neighborhood. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem balanced_unsplit_tuple_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → F ≤ 2*Y → (∀ i, ShortArithmeticFactor F (A i)) →
      (∀ i, q i ≠ 0) → (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryUnsplitTuple A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t V Y‖^2) ≤ Y^(7/3-ε) := by
  let D : ℝ := 2^(Fintype.card ι+1)
  have hD1 : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hD2 : 2 ≤ D := by
    dsimp [D]
    rw [pow_succ]
    have h := one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := Fintype.card ι)
    linarith
  have hD : 0 < D := zero_lt_one.trans_le hD1
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hw⟩ := balanced_weighted_tuple_neighborhood (ι := ι) hpub hHuxley V hV hpos hsm hGI hGQ hD
  obtain ⟨T₁,hT₁,hpart⟩ := norm_partition_moment_power (ι := ι) hε
  refine ⟨κ,hκ,hκhi,ε/2,by positivity,max T T₁,?_⟩
  intro F Y A q η t P hY hF hA hq hη hqY ht hP
  have hYT : T ≤ Y := (le_max_left _ _).trans hY
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans hY
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  let f : (ι → Fin (normPartitionCount (2*Y))) → P → ℂ := fun k a =>
    primaryShortTupleSum (fun i => (4/3:ℝ)^(k i).val) A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η
      (fun _ => normPartitionWeight) t V Y
  have hf (k : ι → Fin (normPartitionCount (2*Y))) : (∑ a : P, ‖f k a‖^2) ≤ Y^(7/3-ε) := by
    by_cases hg : Y ≤ (∏ i, (4/3:ℝ)^(k i).val) ∧ (∏ i, (4/3:ℝ)^(k i).val) ≤ D*Y
    · have h := hw F Y (fun i => (4/3:ℝ)^(k i).val) A q η t P Y hYT
        (hF.trans (mul_le_mul_of_nonneg_right hD2 hYp.le)) hA
        (fun i => one_le_pow₀ (by norm_num)) ((div_le_self hYp.le hD1).trans hg.1)
        hg.2 hq hη hqY ht hP hYp
      change (∑ a ∈ P.attach, ‖f k a‖^2) ≤ _
      dsimp only [f]
      rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
        ‖primaryShortTupleSum (fun i => (4/3:ℝ)^(k i).val) A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η
          (fun _ => normPartitionWeight) t V Y‖^2)]
      exact h
    · have hz (a : P) : f k a = 0 := primaryShortTupleSum_zero_outside_scales _ A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t V
        (fun i => pow_pos (by norm_num) _) hYp hVlo hVhi hg
      simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
      exact Real.rpow_nonneg hYp.le _
  have hm := hpart Y hYT₁ P f hf
  have he (a : Eisenstein × Eisenstein) : primaryUnsplitTuple A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t V Y =
      ∑ k : ι → Fin (normPartitionCount (2*Y)),
        primaryShortTupleSum (fun i => (4/3:ℝ)^(k i).val) A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η
          (fun _ => normPartitionWeight) t V Y :=
    primaryShortTupleSum_partition A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t V hY1 hVhi
  simp_rw [he]
  change (∑ a ∈ P.attach, ‖∑ k, f k a‖^2) ≤ _ at hm
  dsimp only [f] at hm
  rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
    ‖∑ k : ι → Fin (normPartitionCount (2*Y)),
      primaryShortTupleSum (fun i => (4/3:ℝ)^(k i).val) A (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η
        (fun _ => normPartitionWeight) t V Y‖^2)] at hm
  exact hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoordinateNeighborhoodPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint Mellin tail with the larger neighborhood row count. -/
noncomputable section
namespace CubicFirstMoment

lemma coordinate_neighborhood_tail_power (k : ℕ) {Y K J : ℝ} (hY : 0 < Y) :
    2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^(1000*(2*k+7)))*J)^2 =
      (2*K^2*J^2)*Y^(-10:ℝ) := by
  have hp : (Y^(1/1000:ℝ))^(1000*(2*k+7)) = Y^(2*k+7) := by
    rw [← Real.rpow_mul_natCast hY.le]
    have he : (1/1000:ℝ)*(1000*(2*k+7):ℕ) = ((2*k+7:ℕ):ℝ) := by push_cast; ring
    rw [he,Real.rpow_natCast]
  have hd : Y^(2*k)/Y^(2*k+7) = Y^(-7:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_sub hY]
    congr 1
    push_cast
    ring
  rw [hp,show K*Y^(2*k)/Y^(2*k+7) = K*(Y^(2*k)/Y^(2*k+7)) by ring,hd]
  have he : Y^4*(Y^(-7:ℝ))^2 = Y^(-10:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le,← Real.rpow_natCast,← Real.rpow_add hY]
    norm_num
  calc
    _ = (2*K^2*J^2)*(Y^4*(Y^(-7:ℝ))^2) := by ring
    _ = _ := by rw [he]

lemma coordinate_neighborhood_tail_le_short_tail (k : ℕ) {Y K J : ℝ} (hY : 1 ≤ Y) :
    2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^(1000*(2*k+7)))*J)^2 ≤
      (2*K^2*J^2)*Y^(-42/5:ℝ) := by
  rw [coordinate_neighborhood_tail_power k (zero_lt_one.trans_le hY)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation of independent coordinate weights on a finite
arithmetic sum. The joint weight has explicitly factored L1 mass. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellin_point (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {N X : ℝ} (hN : 0 < N) (hX : 0 < X) :
    W (N/X) = ∫ τ : ℝ, zeroLineMellinWeight W X τ*mellinPhase (-τ) N := by
  have h : W (N/X) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W ((τ:ℂ)*Complex.I)*(X:ℂ)^((τ:ℂ)*Complex.I)*
        (N:ℂ)^(-((τ:ℂ)*Complex.I)) := by
    simpa using smooth_mellin_finite (fun _ : Unit => (1:ℂ)) (fun _ : Unit => N)
      (fun _ => hN) W hW hpos hsm 0 hX
  rw [h,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with τ
  rw [mellinPhase_eq_cpow hN]
  have he : ((-τ:ℝ):ℂ)*Complex.I = -((τ:ℂ)*Complex.I) := by push_cast; ring
  rw [he]
  unfold zeroLineMellinWeight
  ring

lemma integrable_zeroLineMellin_phase (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (N : ℝ) :
    Integrable (fun τ : ℝ => zeroLineMellinWeight W X τ*mellinPhase (-τ) N) := by
  have hw := zeroLineMellinWeight_integrable W hW hpos hsm hX
  have hp : Continuous (fun τ : ℝ => mellinPhase (-τ) N) := by
    unfold mellinPhase
    fun_prop
  apply hw.norm.mono' (hw.aestronglyMeasurable.mul hp.aestronglyMeasurable)
  filter_upwards with τ
  change ‖zeroLineMellinWeight W X τ*mellinPhase (-τ) N‖ ≤ ‖zeroLineMellinWeight W X τ‖
  rw [norm_mul,mellinPhase_norm,mul_one]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma independentMellinWeight_integrable (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) :
    Integrable (independentMellinWeight W X) :=
  Integrable.fintype_prod (fun i => zeroLineMellinWeight_integrable (W i) (hW i) (hpos i) (hsm i) (hX i))

lemma independentMellinWeight_mass (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i) :
    (∫ τ : ι → ℝ, ‖independentMellinWeight W X τ‖) = ∏ i, zeroLineMellinMass (W i) := by
  simp only [independentMellinWeight,norm_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun (i : ι) (t : ℝ) => ‖zeroLineMellinWeight (W i) (X i) t‖)]
  simp_rw [zeroLineMellinWeight_mass _ (hX _)]

/-- All original factor weights are separated simultaneously. No cutoff or
Mellin-tail assumption is used in this identity. -/
theorem independent_mellin_finite (a : κ → ℂ) (N : ι → κ → ℝ)
    (hN : ∀ i n, 0 < N i n) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) :
    (∑ n, a n*∏ i, W i (N i n/X i)) =
      ∫ τ : ι → ℝ, independentMellinWeight W X τ *
        ∑ n, a n*∏ i, mellinPhase (-(τ i)) (N i n) := by
  have hi (n : κ) : Integrable (fun τ : ι → ℝ =>
      a n*∏ i, zeroLineMellinWeight (W i) (X i) (τ i)*mellinPhase (-(τ i)) (N i n)) :=
    (Integrable.fintype_prod (fun i =>
      integrable_zeroLineMellin_phase (W i) (hW i) (hpos i) (hsm i) (hX i) (N i n))).const_mul (a n)
  calc
    _ = ∑ n, a n*∫ τ : ι → ℝ,
        ∏ i, zeroLineMellinWeight (W i) (X i) (τ i)*mellinPhase (-(τ i)) (N i n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [integral_fintype_prod_volume_eq_prod (fun (i : ι) (τ : ℝ) =>
        zeroLineMellinWeight (W i) (X i) τ*mellinPhase (-τ) (N i n))]
      simp_rw [← zeroLineMellin_point (W _) (hW _) (hpos _) (hsm _) (hN _ n) (hX _)]
    _ = ∫ τ : ι → ℝ, ∑ n, a n*
        ∏ i, zeroLineMellinWeight (W i) (X i) (τ i)*mellinPhase (-(τ i)) (N i n) := by
      simp_rw [← integral_const_mul]
      exact (integral_finsetSum _ (fun n _ => hi n)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with τ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.prod_mul_distrib]
      unfold independentMellinWeight
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentMellinTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-coordinate tail of the genuine product Mellin weight is bounded
by its explicit finite sum of coordinate moments. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma measurableSet_mellinHeightBox (T : ℝ) : MeasurableSet (mellinHeightBox (ι := ι) T) := by
  have he : mellinHeightBox (ι := ι) T = ⋂ i, {τ : ι → ℝ | |τ i| ≤ T} := by
    ext τ
    simp [mellinHeightBox]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_pi_apply i).abs measurable_const)

omit [DecidableEq ι] in
lemma mellinHeightPower_nonneg (A : ℕ) (τ : ι → ℝ) : 0 ≤ mellinHeightPower A τ :=
  Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg (τ i)) A)

omit [DecidableEq ι] in
lemma mellinHeightPower_large {T : ℝ} (hT : 0 ≤ T) (A : ℕ) {τ : ι → ℝ}
    (hτ : τ ∈ (mellinHeightBox T)ᶜ) : T^A ≤ mellinHeightPower A τ := by
  have h : ∃ i, T < |τ i| := by
    simpa only [mellinHeightBox,mem_compl_iff,mem_ofPred_eq,not_forall,not_le] using hτ
  obtain ⟨i,hi⟩ := h
  exact (pow_le_pow_left₀ hT hi.le A).trans
    (Finset.single_le_sum (fun j _ => pow_nonneg (abs_nonneg (τ j)) A) (Finset.mem_univ i))

omit [DecidableEq ι] in
theorem multivariate_weighted_tail (w : (ι → ℝ) → ℂ) (hw : Integrable w)
    (A : ℕ) (hA : Integrable (fun τ => mellinHeightPower A τ*‖w τ‖))
    {T : ℝ} (hT : 0 < T) :
    (∫ τ in (mellinHeightBox T)ᶜ, ‖w τ‖) ≤
      (∫ τ : ι → ℝ, mellinHeightPower A τ*‖w τ‖)/T^A := by
  apply (le_div_iff₀ (pow_pos hT A)).mpr
  rw [mul_comm,← integral_const_mul]
  apply (integral_mono_ae (hw.norm.restrict.const_mul _) hA.restrict ?_).trans
    (setIntegral_le_integral hA (Filter.Eventually.of_forall
      (fun τ => mul_nonneg (mellinHeightPower_nonneg A τ) (_root_.norm_nonneg _))))
  filter_upwards [ae_restrict_mem (measurableSet_mellinHeightBox T).compl] with τ hτ
  exact mul_le_mul_of_nonneg_right (mellinHeightPower_large hT.le A hτ) (_root_.norm_nonneg _)

lemma prod_one_coordinate (f : ι → ℝ) (i : ι) (c : ℝ) :
    (∏ j, if j=i then c*f j else f j) = c*∏ j, f j := by
  classical
  have he (j : ι) : (if j=i then c*f j else f j) = (if j=i then c else 1)*f j := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

lemma independentMellinWeight_coordinate_moment_integrable
    (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ) (i : ι) :
    Integrable (fun τ : ι → ℝ => |τ i|^A*‖independentMellinWeight W X τ‖) := by
  have hh (j : ι) : Integrable (fun t : ℝ =>
      if j=i then |t|^A*‖zeroLineMellinWeight (W j) (X j) t‖ else
        ‖zeroLineMellinWeight (W j) (X j) t‖) := by
    by_cases hj : j=i
    · simp only [hj,ite_true, if_true]
      exact zeroLineMellinWeight_moment_integrable (W i) (hW i) (hpos i) (hsm i) (hX i) A
    · simp only [hj,ite_false, if_false]
      exact (zeroLineMellinWeight_integrable (W j) (hW j) (hpos j) (hsm j) (hX j)).norm
  have hp := Integrable.fintype_prod hh
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  funext τ
  rw [independentMellinWeight,norm_prod]
  symm
  convert prod_one_coordinate (fun j => ‖zeroLineMellinWeight (W j) (X j) (τ j)‖) i (|τ i|^A) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j=i <;> simp [hj]

lemma independentMellinWeight_moment_integrable
    (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ) :
    Integrable (fun τ : ι → ℝ => mellinHeightPower A τ*‖independentMellinWeight W X τ‖) := by
  simp only [mellinHeightPower,Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _ =>
    independentMellinWeight_coordinate_moment_integrable W X hW hpos hsm hX A i)

omit [DecidableEq ι] in
lemma independentMellinWeight_norm_scale (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (τ : ι → ℝ) :
    ‖independentMellinWeight W X τ‖ = ‖independentMellinWeight W (fun _ => 1) τ‖ := by
  simp only [independentMellinWeight,norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [zeroLineMellinWeight_norm (W i) (hX i),
    zeroLineMellinWeight_norm (W i) (by norm_num)]

omit [DecidableEq ι] in
lemma independentMellinMoment_nonneg (W : ι → ℝ → ℂ) (A : ℕ) :
    0 ≤ independentMellinMoment W A :=
  integral_nonneg (fun τ => mul_nonneg (mellinHeightPower_nonneg A τ) (_root_.norm_nonneg _))

omit [DecidableEq ι] in
lemma independentMellinWeight_moment (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (A : ℕ) :
    (∫ τ : ι → ℝ, mellinHeightPower A τ*‖independentMellinWeight W X τ‖) =
      independentMellinMoment W A := by
  simp_rw [independentMellinWeight_norm_scale W X hX]
  rfl

theorem independentMellinWeight_tail (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ)
    {T : ℝ} (hT : 0 < T) :
    (∫ τ in (mellinHeightBox T)ᶜ, ‖independentMellinWeight W X τ‖) ≤
      independentMellinMoment W A/T^A := by
  have h := multivariate_weighted_tail (independentMellinWeight W X)
    (independentMellinWeight_integrable W X hW hpos hsm hX) A
    (independentMellinWeight_moment_integrable W X hW hpos hsm hX A) hT
  rwa [independentMellinWeight_moment W X hX A] at h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentMellinMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-row L2 transfer for independently separated norm weights, with a
proved tail outside the simultaneous height window. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
lemma finite_box_integral_moment (f : κ → (ι → ℝ) → ℂ)
    (hf : ∀ r, Continuous (f r)) (w : (ι → ℝ) → ℂ) (hw : Integrable w)
    (T B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ τ ∈ mellinHeightBox T, (∑ r, ‖f r τ‖^2) ≤ B) :
    (∑ r, ‖∫ τ in mellinHeightBox T, w τ*f r τ‖^2) ≤
      (∫ τ, ‖w τ‖)^2*B := by
  have hc : Continuous (fun τ => WithLp.toLp 2 (fun r => f r τ)) :=
    (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp (continuous_pi hf)
  have ha : ∀ᵐ τ ∂(volume.restrict (mellinHeightBox T)), (∑ r, ‖f r τ‖^2) ≤ B := by
    filter_upwards [ae_restrict_mem (measurableSet_mellinHeightBox T)] with τ hτ
    exact hb τ hτ
  have hm := finite_row_integral_moment f w hc.aestronglyMeasurable hw.restrict hB ha
  apply hm.trans
  have hmass : (∫ τ in mellinHeightBox T, ‖w τ‖) ≤ ∫ τ, ‖w τ‖ :=
    setIntegral_le_integral hw.norm (Filter.Eventually.of_forall (fun _ => _root_.norm_nonneg _))
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (integral_nonneg (fun _ => _root_.norm_nonneg _)) hmass 2) hB

theorem independent_mellin_integral_moment (f : κ → (ι → ℝ) → ℂ)
    (hf : ∀ r, Continuous (f r)) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ)
    {T L B : ℝ} (hT : 0 < T) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hsize : ∀ r τ, ‖f r τ‖ ≤ L)
    (hbound : ∀ τ ∈ mellinHeightBox T, (∑ r, ‖f r τ‖^2) ≤ B) :
    (∑ r, ‖∫ τ, independentMellinWeight W X τ*f r τ‖^2) ≤
      2*(∏ i, zeroLineMellinMass (W i))^2*B+
        2*(Fintype.card κ:ℝ)*((L/T^A)*independentMellinMoment W A)^2 := by
  let w := independentMellinWeight W X
  have hw : Integrable w := independentMellinWeight_integrable W X hW hpos hsm hX
  have hc := finite_box_integral_moment f hf w hw T B hB hbound
  rw [independentMellinWeight_mass W X hX] at hc
  let H := (L/T^A)*independentMellinMoment W A
  have ht (r : κ) : ‖∫ τ in (mellinHeightBox T)ᶜ, w τ*f r τ‖ ≤ H := by
    calc
      _ ≤ L*(∫ τ in (mellinHeightBox T)ᶜ, ‖w τ‖) := by
        rw [← integral_const_mul]
        apply norm_integral_le_of_norm_le (hw.norm.restrict.const_mul L)
        filter_upwards with τ
        rw [norm_mul,mul_comm L]
        exact mul_le_mul_of_nonneg_left (hsize r τ) (_root_.norm_nonneg _)
      _ ≤ L*(independentMellinMoment W A/T^A) :=
        mul_le_mul_of_nonneg_left (independentMellinWeight_tail W X hW hpos hsm hX A hT) hL
      _ = H := by dsimp [H]; ring
  have ha (r : κ) :
      ‖(∫ τ, w τ*f r τ)-(∫ τ in mellinHeightBox T, w τ*f r τ)‖ ≤ H := by
    have hi : Integrable (fun τ => w τ*f r τ) := (hw.norm.mul_const L).mono'
      (hw.aestronglyMeasurable.mul (hf r).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun τ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hsize r τ) (_root_.norm_nonneg _)))
    rw [← integral_add_compl (measurableSet_mellinHeightBox T) hi,add_sub_cancel_left]
    exact ht r
  calc
    _ ≤ ∑ r, (2*‖∫ τ in mellinHeightBox T, w τ*f r τ‖^2+2*H^2) :=
      Finset.sum_le_sum (fun r _ => norm_square_le_central_tail _ _ (ha r))
    _ = 2*(∑ r, ‖∫ τ in mellinHeightBox T, w τ*f r τ‖^2)+2*(Fintype.card κ:ℝ)*H^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _ ≤ _ := by dsimp [H]; nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryProductCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of ideal convolution coefficients with the finite
fibres of products of primary Eisenstein elements. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealExponentOf_primary_prod {ι : Type*} (S : Finset ι) (n : ι → Eisenstein)
    (hn : ∀ i ∈ S, primary (n i)) :
    idealExponentOf (∏ i ∈ S, n i) = ∑ i ∈ S, idealExponentOf (n i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,Finset.sum_empty]
    simpa [idealExponentGenerator] using idealExponentOf_generator (0 : EisensteinIdealExponent)
  | @insert i S hi ih =>
    have hS : ∀ j ∈ S, primary (n j) := fun j hj => hn j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,Finset.sum_insert hi,
      idealExponentOf_mul (primary_ne_zero (hn i (Finset.mem_insert_self _ _)))
        (primary_ne_zero (primary_finset_prod S n hS)),ih hS]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coeff_product_primary_fiber {R : Type*} [CommSemiring R]
    (A : ι → MvPowerSeries EisensteinIdealPrime R)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i) =
      ∑ n ∈ (Fintype.piFinset (fun _ : ι => primaryElementBall F)).filter
        (fun n => (∏ i, n i) = b), ∏ i, MvPowerSeries.coeff (idealExponentOf (n i)) (A i) := by
  rw [MvPowerSeries.coeff_prod]
  let g : (ι →₀ EisensteinIdealExponent) → ι → Eisenstein :=
    fun l i => idealPrimaryGenerator (l i)
  have hle (l : ι →₀ EisensteinIdealExponent)
      (hl : l ∈ Finset.finsuppAntidiag Finset.univ (idealExponentOf b)) (i : ι) :
      l i ≤ idealExponentOf b := by
    rw [← (Finset.mem_finsuppAntidiag.mp hl).1]
    exact Finset.single_le_sum (fun j _ => (show 0 ≤ l j from zero_le)) (Finset.mem_univ i)
  have hg (l : ι →₀ EisensteinIdealExponent)
      (hl : l ∈ Finset.finsuppAntidiag Finset.univ (idealExponentOf b)) :
      ∀ i, primary (g l i) := fun i => idealPrimaryGenerator_primary hb (hle l hl i)
  apply Finset.sum_bij (fun l _ => g l)
  · intro l hl
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => mem_primaryElementBall.mpr ⟨hg l hl i,?_⟩),?_⟩
    · rw [idealPrimaryGenerator_norm]
      exact ((idealExponentNorm_mono (hle l hl i)).trans_eq
        (idealExponentOf_norm (primary_ne_zero hb))).trans hbF
    · apply primary_eq_of_idealExponentOf_eq (primary_finset_prod _ _ (fun i _ => hg l hl i)) hb
      rw [idealExponentOf_primary_prod _ _ (fun i _ => hg l hl i)]
      simpa only [g,idealExponentOf_primaryGenerator] using (Finset.mem_finsuppAntidiag.mp hl).1
  · intro l _ m _ h
    apply Finsupp.ext
    intro i
    have hi := congrArg idealExponentOf (congrFun h i)
    simpa only [g,idealExponentOf_primaryGenerator] using hi
  · intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hnp (i : ι) : primary (n i) :=
      (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hmem.1) i)).1
    let l : ι →₀ EisensteinIdealExponent :=
      Finsupp.onFinset Finset.univ (fun i => idealExponentOf (n i)) (by simp)
    have hli (i : ι) : l i = idealExponentOf (n i) := rfl
    refine ⟨l,Finset.mem_finsuppAntidiag.mpr ⟨?_,Finset.subset_univ _⟩,?_⟩
    · simp_rw [hli]
      rw [← idealExponentOf_primary_prod _ _ (fun i _ => hnp i),hmem.2]
    · funext i
      exact idealPrimaryGenerator_at_element (hnp i)
  · intro l _
    apply Finset.prod_congr rfl
    intro i _
    simp only [g,idealExponentOf_primaryGenerator]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual prime-power convolution coefficients: bounded prime support absorbs
all tuple multiplicities in an arbitrarily small norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_eq_zero_of_not_mem (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {b : Eisenstein}
    (hb : b ∉ orderedConvolutionSupport S) : orderedConvolution S w b = 0 := by
  unfold orderedConvolution
  apply Finset.sum_eq_zero
  intro f hf
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  exact False.elim (hb (Finset.mem_image.mpr ⟨f,hfs,hfb⟩))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ComplexWeightedConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex coefficient collection retains the distinct norm and residue
twists of each original prime factor during short inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complex_coeff_product_eq_convolution (A : ι → MvPowerSeries EisensteinIdealPrime ℂ)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i) =
      orderedConvolution (fun _ : ι => primaryElementBall F)
        (fun i n => MvPowerSeries.coeff (idealExponentOf n) (A i)) b := by
  rw [coeff_product_primary_fiber A hb hbF]
  rfl

/-- The global smooth cutoff permits collection on one finite primary
ball, although the unrestricted product support is much larger. -/
theorem primaryComplexProductPolynomial_eq_tuple (A : ι → MvPowerSeries EisensteinIdealPrime ℂ)
    (χ : Eisenstein → ℂ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryComplexProductPolynomial A χ V Y =
      ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        (∏ i, MvPowerSeries.coeff (idealExponentOf (n i)) (A i))*
          χ (∏ i, n i)*V ((∏ i, norm (n i))/Y) := by
  let S : ι → Finset Eisenstein := fun _ => primaryElementBall (2*Y)
  let w : ι → Eisenstein → ℂ := fun i n =>
    MvPowerSeries.coeff (idealExponentOf n) (A i)
  have hc (b : Eisenstein) (hb : b ∈ primaryElementBall (2*Y)) :
      MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i) = orderedConvolution S w b :=
    complex_coeff_product_eq_convolution A (mem_primaryElementBall.mp hb).1 (mem_primaryElementBall.mp hb).2
  unfold primaryComplexProductPolynomial
  have hs : (∑ b ∈ primaryElementBall (2*Y), orderedConvolution S w b*(χ b*V (norm b/Y))) =
      ∑ b ∈ orderedConvolutionSupport S, orderedConvolution S w b*(χ b*V (norm b/Y)) := by
    apply Finset.sum_bij_ne_zero (fun b _ _ => b)
    · intro b _ hn
      by_contra hb
      rw [orderedConvolution_eq_zero_of_not_mem S w hb,zero_mul] at hn
      exact hn rfl
    · intro b _ _ c _ _ h
      exact h
    · intro b hb hn
      have hp : primary b := by
        change b ∈ (Fintype.piFinset S).image (fun n => ∏ i, n i) at hb
        obtain ⟨n,hnmem,rfl⟩ := Finset.mem_image.mp hb
        have hn' : n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)) := hnmem
        have hni (i : ι) : n i ∈ primaryElementBall (2*Y) := (Fintype.mem_piFinset.mp hn') i
        exact primary_finset_prod Finset.univ n (fun i _ => (mem_primaryElementBall.mp (hni i)).1)
      have hv : V (norm b/Y) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).2).2
      have hbn : norm b ≤ 2*Y := by
        by_contra hgt
        exact hv (hV _ ((lt_div_iff₀ hY).mpr (lt_of_not_ge hgt)))
      exact ⟨b,mem_primaryElementBall.mpr ⟨hp,hbn⟩,hn,rfl⟩
    · intro b _ _
      rfl
  calc
    _ = ∑ b ∈ primaryElementBall (2*Y), orderedConvolution S w b*χ b*V (norm b/Y) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hc b hb]
    _ = ∑ b ∈ primaryElementBall (2*Y), orderedConvolution S w b*(χ b*V (norm b/Y)) := by
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := hs
    _ = _ := by
      rw [orderedConvolution_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [norm_finset_prod]
      dsimp only [w]
      ring

/-- Independent residue characters and Mellin heights remain attached to
individual factors after exact collection. -/
theorem twistedProductPolynomial_eq_unsplit (A : ι → EisensteinArithmeticFunction)
    {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hη : ∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1)
    (t : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryComplexProductPolynomial (fun i => twistArithmetic (q i) (η i) (t i) (A i))
      (mixedCubic a b) V Y = primaryUnsplitTuple A a b q η t V Y := by
  rw [primaryComplexProductPolynomial_eq_tuple _ _ V hY hV]
  unfold primaryUnsplitTuple
  apply Finset.sum_congr rfl
  intro n hn
  have hp (i : ι) : primary (n i) :=
    (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1
  simp_rw [twistArithmetic_coeff_primary _ _ (hη _) _ _ (hp _)]
  rw [mixedCubic_prod _ _ ha hb]
  unfold primaryTupleCore
  rw [← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoordinateWeightedTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent smooth weights on the original arithmetic factors, with the
exact Mellin representation by the unweighted convolutions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma primaryTupleCore_shift (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t τ : ι → ℝ)
    (V : ℝ → ℂ) (Y : ℝ) (n : ι → Eisenstein) :
    primaryTupleCore A a b q η t V Y n * ∏ i, mellinPhase (-(τ i)) (norm (n i)) =
      primaryTupleCore A a b q η (fun i => t i-τ i) V Y n := by
  unfold primaryTupleCore
  rw [mul_right_comm,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_assoc,mul_assoc,← mellinPhase_add]
  congr 2

lemma continuous_primaryUnsplitTuple (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (V : ℝ → ℂ) (Y : ℝ) :
    Continuous (fun t : ι → ℝ => primaryUnsplitTuple A a b q η t V Y) := by
  unfold primaryUnsplitTuple primaryTupleCore mellinPhase
  fun_prop

 theorem primaryCoordinateWeightedTuple_mellin (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) :
    primaryCoordinateWeightedTuple A a b q η t W X V Y =
      ∫ τ : ι → ℝ, independentMellinWeight W X τ *
        primaryUnsplitTuple A a b q η (fun i => t i-τ i) V Y := by
  let S := Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y))
  have hN (i : ι) (n : S) : 0 < norm (n.val i) :=
    norm_pos_of_ne_zero (primary_ne_zero
      (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp n.property) i)).1)
  have hm := independent_mellin_finite
    (fun n : S => primaryTupleCore A a b q η t V Y n.val)
    (fun i (n : S) => norm (n.val i)) hN W X hW hpos hsm hX
  have hl : (∑ n : S, primaryTupleCore A a b q η t V Y n.val *
      ∏ i, W i (norm (n.val i)/X i)) = primaryCoordinateWeightedTuple A a b q η t W X V Y := by
    change (∑ n ∈ S.attach, _) = _
    rw [Finset.sum_attach (f := fun n : ι → Eisenstein =>
      primaryTupleCore A a b q η t V Y n * ∏ i, W i (norm (n i)/X i))]
    rfl
  rw [hl] at hm
  rw [hm]
  apply integral_congr_ae
  filter_upwards with τ
  congr 1
  simp_rw [primaryTupleCore_shift]
  change (∑ n ∈ S.attach, primaryTupleCore A a b q η (fun i => t i-τ i) V Y n.val) = _
  rw [Finset.sum_attach (f := fun n : ι → Eisenstein =>
    primaryTupleCore A a b q η (fun i => t i-τ i) V Y n)]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleSize
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial bound for the actual von Mangoldt tuple sum. This coarse
bound is used only against arbitrarily rapid Mellin tails. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma vonMangoldt_coeff_norm_le {Y : ℝ} {n : Eisenstein}
    (hn : n ∈ primaryElementBall (2*Y)) :
    ‖((MvPowerSeries.coeff (idealExponentOf n) idealVonMangoldt:ℝ):ℂ)‖ ≤ 2*Y := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  have hp := (mem_primaryElementBall.mp hn).1
  have h := idealVonMangoldt_coeff_abs_le_logNorm (idealExponentOf n)
  rw [idealExponentOf_norm (primary_ne_zero hp)] at h
  exact h.trans ((Real.log_le_self (norm_nonneg n)).trans (mem_primaryElementBall.mp hn).2)

lemma vonMangoldt_tuple_core_bound (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (V : ℝ → ℂ)
    {M Y : ℝ} (_hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y)
    (n : ι → Eisenstein) (hn : n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y))) :
    ‖primaryTupleCore (fun _ : ι => idealVonMangoldt) a b q η t V Y n‖ ≤
      (2*Y)^(Fintype.card ι)*M := by
  have hi (i : ι) :
      ‖((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*mellinPhase (t i) (norm (n i)))‖ ≤ 2*Y := by
    have htw : ‖mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        mellinPhase (t i) (norm (n i))‖ ≤ 1 := by
      rw [norm_mul,mellinPhase_norm,mul_one,norm_mul]
      exact (mul_le_mul (norm_mixedCubic_le_one ha hb _) (residueChar_norm_le_one (hq i) (η i) _)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (_root_.norm_nonneg _) htw).trans
      (vonMangoldt_coeff_norm_le ((Fintype.mem_piFinset.mp hn) i))
  unfold primaryTupleCore
  rw [norm_mul,norm_prod]
  have hp : (∏ i, ‖((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*mellinPhase (t i) (norm (n i)))‖) ≤
      (2*Y)^(Fintype.card ι) := by
    calc
      _ ≤ ∏ _i : ι, 2*Y :=
        Finset.prod_le_prod (fun i _ => _root_.norm_nonneg _) (fun i _ => hi i)
      _ = _ := by simp
  exact mul_le_mul hp (hV _) (_root_.norm_nonneg _) (pow_nonneg (by positivity) _)

 theorem vonMangoldt_unsplit_size (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (V : ℝ → ℂ)
    {M Y : ℝ} (hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y) :
    ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt) a b q η t V Y‖ ≤
      (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) := by
  unfold primaryUnsplitTuple
  calc
    _ ≤ ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        ‖primaryTupleCore (fun _ : ι => idealVonMangoldt) a b q η t V Y n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        (2*Y)^(Fintype.card ι)*M :=
      Finset.sum_le_sum (fun n hn => vonMangoldt_tuple_core_bound a b ha hb q η hq t V hM hV hY n hn)
    _ = ((primaryElementBall (2*Y)).card:ℝ)^(Fintype.card ι)*((2*Y)^(Fintype.card ι)*M) := by
      simp [Fintype.card_piFinset,Finset.prod_const]
    _ ≤ (36*Y)^(Fintype.card ι)*((2*Y)^(Fintype.card ι)*M) := by
      apply mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _) (mul_nonneg (pow_nonneg (by positivity) _) hM)
      nlinarith [primaryElementBall_card_le (show 0 ≤ 2*Y by positivity)]
    _ = M*((36*Y)*(2*Y))^(Fintype.card ι) := by
      rw [mul_pow (36*Y) (2*Y)]
      ring
    _ = M*(72*Y^2)^(Fintype.card ι) := by congr 1; congr 1; ring
    _ = _ := by rw [mul_pow,pow_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoordinatePrimeMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate Mellin transfer for the actual independently weighted
von Mangoldt tuple sum, with a polynomial bound for every tail row. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

 theorem coordinate_vonMangoldt_moment_bound (r : κ → Eisenstein × Eisenstein)
    (hr : ∀ j, primary (r j).1 ∧ primary (r j).2)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i)
    (V : ℝ → ℂ) {M Y : ℝ} (hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y)
    (A : ℕ) {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hbound : ∀ τ ∈ mellinHeightBox T,
      (∑ j, ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt)
        (r j).1 (r j).2 q η (fun i => t i-τ i) V Y‖^2) ≤ B) :
    (∑ j, ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
      (r j).1 (r j).2 q η t W X V Y‖^2) ≤
      2*(∏ i, zeroLineMellinMass (W i))^2*B+
        2*(Fintype.card κ:ℝ)*
          (((M*72^(Fintype.card ι))*Y^(2*Fintype.card ι)/T^A)*independentMellinMoment W A)^2 := by
  let f : κ → (ι → ℝ) → ℂ := fun j τ =>
    primaryUnsplitTuple (fun _ : ι => idealVonMangoldt) (r j).1 (r j).2 q η
      (fun i => t i-τ i) V Y
  have hf (j : κ) : Continuous (f j) :=
    (continuous_primaryUnsplitTuple _ _ _ q η V Y).comp (by fun_prop)
  have hsize (j : κ) (τ : ι → ℝ) :
      ‖f j τ‖ ≤ (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) :=
    vonMangoldt_unsplit_size _ _ (hr j).1 (hr j).2 q η hq _ V hM hV hY
  have hm := independent_mellin_integral_moment f hf W X hW hpos hsm hX A hT
    (show 0 ≤ (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) by positivity) hB hsize hbound
  have he (j : κ) := primaryCoordinateWeightedTuple_mellin (fun _ : ι => idealVonMangoldt)
    (r j).1 (r j).2 q η t W X V Y hW hpos hsm hX
  simpa only [he] using hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteMomentSaving
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite linear combination preserves a positive moment saving. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_positive_lower_bound {κ : Type*} [Fintype κ] (e : κ → ℝ)
    (he : ∀ k, 0 < e k) : ∃ d : ℝ, 0 < d ∧ ∀ k, d ≤ e k := by
  classical
  have h : ∀ S : Finset κ, ∃ d : ℝ, 0 < d ∧ ∀ k ∈ S, d ≤ e k := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert k S hk ih =>
      obtain ⟨d,hd,hde⟩ := ih
      refine ⟨min d (e k),lt_min hd (he k),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hde j hj)
  obtain ⟨d,hd,hde⟩ := h Finset.univ
  exact ⟨d,hd,fun k => hde k (Finset.mem_univ k)⟩

theorem finite_weighted_moment_saving {κ : Type*} [Fintype κ]
    (e : κ → ℝ) (he : ∀ k, 0 < e k) (c : κ → ℂ) :
    ∃ d : ℝ, 0 < d ∧ ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y →
      ∀ (ρ : Type*) [Fintype ρ] (f : κ → ρ → ℂ),
      (∀ k, (∑ r, ‖f k r‖^2) ≤ Y^(7/3-e k)) →
      (∑ r, ‖∑ k, c k*f k r‖^2) ≤ Y^(7/3-d) := by
  obtain ⟨d,hd,hde⟩ := finite_positive_lower_bound e he
  let C : ℝ := (Fintype.card κ)*(∑ k, ‖c k‖^2)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < d/2 by linarith)).eventually_ge_atTop C)
  refine ⟨d/2,by positivity,max 1 T,le_max_left _ _,?_⟩
  intro Y hY ρ _ f hf
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hf' (k : κ) : (∑ r, ‖f k r‖^2) ≤ Y^(7/3-d) :=
    (hf k).trans (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith [hde k]))
  calc
    _ ≤ (Fintype.card κ:ℝ)*(∑ k, ∑ r, ‖c k*f k r‖^2) :=
      finite_piece_moment (fun k r => c k*f k r)
    _ = (Fintype.card κ:ℝ)*(∑ k, ‖c k‖^2*(∑ r, ‖f k r‖^2)) := by
      simp_rw [norm_mul,mul_pow,← Finset.mul_sum]
    _ ≤ (Fintype.card κ:ℝ)*(∑ k, ‖c k‖^2*Y^(7/3-d)) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hf' k) (sq_nonneg _)))
        (Nat.cast_nonneg _)
    _ = C*Y^(7/3-d) := by rw [← Finset.sum_mul]; dsimp [C]; ring
    _ ≤ Y^(d/2)*Y^(7/3-d) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedConvolutionNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional moments for actual complex convolutions with an independent
residue character and Mellin height on each factor. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem balanced_twisted_convolution_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → F ≤ 2*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) → (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryComplexProductPolynomial (fun i => twistArithmetic (q i) (η i) (t i) (A i)) (mixedCubic a.1 a.2) V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := balanced_unsplit_tuple_neighborhood (ι := ι)
    hpub hHuxley V hV hpos hsm hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,ε,hε,max 1 T,?_⟩
  intro F Y A q η t P hY hF hA hq hη hqY ht hP
  have hYp : 0 < Y := zero_lt_one.trans_le ((le_max_left _ _).trans hY)
  have he (a : Eisenstein × Eisenstein) (ha : a ∈ P) :
      primaryComplexProductPolynomial (fun i => twistArithmetic (q i) (η i) (t i) (A i)) (mixedCubic a.1 a.2) V Y =
        primaryUnsplitTuple A a.1 a.2 q η t V Y :=
    twistedProductPolynomial_eq_unsplit A (hP a ha).1.1 (hP a ha).1.2.1
      q η hη t V hYp hVhi
  calc
    _ = ∑ a ∈ P, ‖primaryUnsplitTuple A a.1 a.2 q η t V Y‖^2 :=
      Finset.sum_congr rfl (fun a ha => by rw [he a ha])
    _ ≤ _ := hbound F Y A q η t P
      ((le_max_right _ _).trans hY) hF hA hq hη hqY ht hP

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortConvolutionExpansion
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each term of the short Möbius product expansion is an actual finite
family of the three permitted arithmetic factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma shortBranchFactor_spec (F : ℝ) (S : Finset ι) (i : shortBranchIndex S) :
    ShortArithmeticFactor F (shortBranchFactor F S i) := by
  rcases i with ⟨i,j⟩ | ⟨i,j⟩
  · fin_cases j <;> simp [shortBranchFactor,ShortArithmeticFactor]
  · fin_cases j <;> simp [shortBranchFactor,ShortArithmeticFactor]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedShortProducts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short inversion with a different residue character and Mellin height
on each original prime factor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma twistArithmetic_two (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A : EisensteinArithmeticFunction) :
    twistArithmetic q η t (2*A) = 2*twistArithmetic q η t A := by
  rw [two_mul,twistArithmetic_add,two_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem twisted_short_product_coeff {F : ℝ} (hF : 0 ≤ F)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (t : ι → ℝ) (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν (∏ i, twistArithmetic (q i) (η i) (t i) idealVonMangoldt) =
      MvPowerSeries.coeff ν (∏ i, twistArithmetic (q i) (η i) (t i) (shortVonMangoldt F)) := by
  have h : ∀ S : Finset ι, ∀ κ : EisensteinIdealExponent, idealExponentNorm κ ≤ F →
      MvPowerSeries.coeff κ (∏ i ∈ S, twistArithmetic (q i) (η i) (t i) idealVonMangoldt) =
      MvPowerSeries.coeff κ (∏ i ∈ S, twistArithmetic (q i) (η i) (t i) (shortVonMangoldt F)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intros; rfl
    | @insert i S hi ih =>
      intro κ hκ
      rw [Finset.prod_insert hi,Finset.prod_insert hi,MvPowerSeries.coeff_mul,MvPowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have h₁ : p.1 ≤ κ := by rw [← he]; exact le_add_of_nonneg_right zero_le
      have h₂ : p.2 ≤ κ := by rw [← he]; exact le_add_of_nonneg_left zero_le
      rw [ih p.2 ((idealExponentNorm_mono h₂).trans hκ)]
      congr 1
      change ((MvPowerSeries.coeff p.1 idealVonMangoldt:ℝ):ℂ)*residueNormTwist (q i) (η i) (t i) p.1 =
        ((MvPowerSeries.coeff p.1 (shortVonMangoldt F):ℝ):ℂ)*residueNormTwist (q i) (η i) (t i) p.1
      rw [shortVonMangoldt_local hF p.1 ((idealExponentNorm_mono h₁).trans hκ)]
  exact h Finset.univ ν hν

lemma twisted_branch_product (F : ℝ) (S : Finset ι) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) :
    (∏ j : shortBranchIndex S,
      twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor F S j)) =
      (∏ i ∈ S, twistArithmetic (q i) (η i) (t i) (shortFourFactor F))*
        ∏ i ∈ Finset.univ\S, twistArithmetic (q i) (η i) (t i) (shortTwoFactor F) := by
  rw [Fintype.prod_sum_type,Fintype.prod_prod_type,Fintype.prod_prod_type]
  simp only [shortBranchSource,shortBranchFactor,Fin.prod_univ_four,Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  simp only [← twistArithmetic_mul]
  change (∏ x : S, twistArithmetic (q x) (η x) (t x) (shortFourFactor F))*
    (∏ x : ↥(Finset.univ\S), twistArithmetic (q x) (η x) (t x) (shortTwoFactor F)) = _
  rw [Finset.prod_coe_sort (s := S) (f := fun i => twistArithmetic (q i) (η i) (t i) (shortFourFactor F)),
    Finset.prod_coe_sort (s := Finset.univ\S) (f := fun i => twistArithmetic (q i) (η i) (t i) (shortTwoFactor F))]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedPrimeExpansion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact short inversion with independent residue and norm twists on every
original von Mangoldt factor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma twisted_short_series_expansion (F : ℝ) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) :
    (∏ i, twistArithmetic (q i) (η i) (t i) (shortVonMangoldt F)) =
      ∑ S : Finset ι, MvPowerSeries.C (shortBranchScalar S)*
        ∏ j : shortBranchIndex S,
          twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
            (t (shortBranchSource S j)) (shortBranchFactor F S j) := by
  simp_rw [shortVonMangoldt_two_four,twistArithmetic_sub,twistArithmetic_two]
  rw [Finset.prod_sub,Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S _
  rw [twisted_branch_product]
  have hp : (∏ i ∈ Finset.univ\S, 2*twistArithmetic (q i) (η i) (t i) (shortTwoFactor F)) =
      (2 : MvPowerSeries EisensteinIdealPrime ℂ)^(Fintype.card ι-S.card)*
        ∏ i ∈ Finset.univ\S, twistArithmetic (q i) (η i) (t i) (shortTwoFactor F) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ]
  rw [hp]
  simp only [shortBranchScalar,map_mul,map_pow,map_neg,map_one,map_ofNat]
  ring

theorem twisted_prime_coeff_expansion {F : ℝ} (hF : 0 ≤ F)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν (∏ i, twistArithmetic (q i) (η i) (t i) idealVonMangoldt) =
      ∑ S : Finset ι, shortBranchScalar S * MvPowerSeries.coeff ν
        (∏ j : shortBranchIndex S,
          twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
            (t (shortBranchSource S j)) (shortBranchFactor F S j)) := by
  rw [twisted_short_product_coeff hF q η t ν hν,
    twisted_short_series_expansion F q η t,map_sum]
  simp only [MvPowerSeries.coeff_C_mul]

theorem primaryTwistedPrimeWeight_expansion (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (χ : Eisenstein → ℂ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y) :
    primaryComplexProductPolynomial (fun i => twistArithmetic (q i) (η i) (t i) idealVonMangoldt) χ V Y =
      ∑ S : Finset ι, shortBranchScalar S * primaryComplexProductPolynomial
        (fun j : shortBranchIndex S =>
          twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
            (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) χ V Y := by
  unfold primaryComplexProductPolynomial
  calc
    _ = ∑ b ∈ primaryElementBall (2*Y), ∑ S : Finset ι, shortBranchScalar S *
        MvPowerSeries.coeff (idealExponentOf b)
          (∏ j : shortBranchIndex S,
            twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
              (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j))*χ b*V (norm b/Y) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' := mem_primaryElementBall.mp hb
      have hN : idealExponentNorm (idealExponentOf b) ≤ 2*Y := by
        simpa only [idealExponentOf_norm (primary_ne_zero hb'.1)] using hb'.2
      rw [twisted_prime_coeff_expansion (by positivity : 0 ≤ 2*Y) q η t _ hN,
        Finset.sum_mul,Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedPrimeNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original von Mangoldt convolutions with independent factor twists inherit
the short-factor power saving by an exact finite expansion. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem balanced_twisted_vonMangoldt_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (Y : ℝ) (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)), Y₀ ≤ Y → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) → (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryComplexProductPolynomial (fun i => twistArithmetic (q i) (η i) (t i) idealVonMangoldt)
        (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y‖^2) ≤ Y^(7/3-ε) := by
  choose κ hκ hκhi e he T hb using fun S : Finset ι =>
    balanced_twisted_convolution_neighborhood (ι := shortBranchIndex S) hpub hHuxley V hV hpos hsm hVlo hVhi hGI hGQ
  obtain ⟨κ₀,hκ₀,hκall⟩ := finite_positive_lower_bound κ hκ
  obtain ⟨d,hd,T₁,hT₁,hsave⟩ := finite_weighted_moment_saving e he (shortBranchScalar (ι := ι))
  refine ⟨min κ₀ (1/10000),by positivity,min_le_right _ _,d,hd,max T₁ (1+∑ S, |T S|),?_⟩
  intro Y q η t P hY hq hη hqY ht hP
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hYT (S : Finset ι) : T S ≤ Y := by
    have hS : |T S| ≤ ∑ U : Finset ι, |T U| :=
      Finset.single_le_sum (fun U _ => abs_nonneg (T U)) (Finset.mem_univ S)
    have hh : 1+∑ U : Finset ι, |T U| ≤ Y := (le_max_right _ _).trans hY
    linarith [le_abs_self (T S)]
  let f : Finset ι → P → ℂ := fun S a =>
    primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y
  have hf (S : Finset ι) : (∑ a : P, ‖f S a‖^2) ≤ Y^(7/3-e S) := by
    have h := hb S (2*Y) Y (shortBranchFactor (2*Y) S)
      (fun j => q (shortBranchSource S j)) (fun j => η (shortBranchSource S j))
      (fun j => t (shortBranchSource S j)) P
      (hYT S) le_rfl (shortBranchFactor_spec (2*Y) S)
      (fun j => hq _) (fun j => hη _) (fun j => hqY _) (fun j => ht _)
      (fun a ha => ⟨(hP a ha).1,
        (hP a ha).2.1.trans (Real.rpow_le_rpow_of_exponent_le hY1
          (by have := (min_le_left κ₀ (1/10000)).trans (hκall S); linarith)),
        (hP a ha).2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hY1
          (by have := (min_le_left κ₀ (1/10000)).trans (hκall S); linarith)),(hP a ha).2.2.2⟩)
    change (∑ a ∈ P.attach, ‖f S a‖^2) ≤ _
    dsimp only [f]
    rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
      ‖primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y‖^2)]
    exact h
  have hm := hsave Y hYT₁ P f hf
  simp_rw [primaryTwistedPrimeWeight_expansion q η t _ V hYp]
  change (∑ a ∈ P.attach, ‖∑ S, shortBranchScalar S*f S a‖^2) ≤ _ at hm
  dsimp only [f] at hm
  rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
    ‖∑ S : Finset ι, shortBranchScalar S*
      primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y‖^2)] at hm
  exact hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeightFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Mellin estimates for the smooth weight families occurring in
Type I. The hypotheses state common support and derivative bounds in
logarithmic coordinates. No transform or moment estimate is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology SchwartzMap ContDiff FourierTransform BigOperators
namespace CubicFirstMoment

private lemma weight_exp_derivative_bound {M R σ u : ℝ} (hM : 0 ≤ M)
    (hσ : |σ| ≤ M) (hu : |u| ≤ R) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v : ℝ => Real.exp (-σ*v)) u‖ ≤
      M^n * Real.exp (M*R) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_exp_const_mul]
  simp only [norm_mul,Real.norm_eq_abs,abs_pow,abs_neg,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hσ n) _ (by positivity) (by positivity)
  apply Real.exp_le_exp.mpr
  calc
    -σ*u ≤ |-σ*u| := le_abs_self _
    _ = |σ| *|u| := by rw [abs_mul,abs_neg]
    _ ≤ M*R := mul_le_mul hσ hu (abs_nonneg _) hM

lemma UniformLogWeights.log_seminorms {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i σ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n
        (mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) ≤ C := by
  choose B hB hder using h.derivative_bound
  let M' := max M 0
  let A := ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*
    (M'^j*Real.exp (M'*h.radius))*B (n-j)
  have hM : 0 ≤ M' := le_max_right _ _
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j hj => by
    have hjB := hB (n-j)
    positivity)
  refine ⟨h.radius^k*A,mul_nonneg (pow_nonneg h.radius_nonneg _) hA,?_⟩
  intro i σ hσ
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (pow_nonneg h.radius_nonneg _) hA)
  intro u
  by_cases hu : |u| ≤ h.radius
  · have he : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (-σ*v)) := by fun_prop
    have hw : ContDiff ℝ ∞ (fun v : ℝ => W i (Real.exp (-v))) :=
      (h.smooth i).comp (Real.contDiff_exp.comp contDiff_id.neg)
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) he hw u (n := n) (mod_cast le_top)
    have hb : ‖iteratedFDeriv ℝ n
        (mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) u‖ ≤ A := by
      change ‖iteratedFDeriv ℝ n (fun v : ℝ =>
        Real.exp (-σ*v) • W i (Real.exp (-v))) u‖ ≤ A
      apply hd.trans
      apply Finset.sum_le_sum
      intro j hj
      have hjB := hB (n-j)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (weight_exp_derivative_bound hM (hσ.trans (le_max_left _ _)) hu j) (by positivity)
      · exact hder (n-j) i u
      · positivity
      · positivity
    simpa only [Real.norm_eq_abs] using
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu k) hb
        (_root_.norm_nonneg _) (pow_nonneg h.radius_nonneg _)
  · have hz : iteratedFDeriv ℝ n
        (mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) u = 0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
        (f := mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) n hn
      have hs' : u ∈ tsupport (fun v : ℝ => W i (Real.exp (-v))) :=
        tsupport_smul_subset_right (fun v : ℝ => Real.exp (-σ*v))
          (fun v : ℝ => W i (Real.exp (-v))) hs
      exact hu (h.support_bound i u hs')
    rw [hz,norm_zero,mul_zero]
    exact mul_nonneg (pow_nonneg h.radius_nonneg _) hA

lemma UniformLogWeights.vertical_bounded {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) :
    Bornology.IsVonNBounded ℝ
      ((fun p : ι × ℝ => mellinVerticalSchwartz (W p.1) (h.compact p.1)
        (h.positive p.1) (h.smooth p.1) p.2) '' {p | |p.2| ≤ M}) := by
  let f : ι × ℝ → 𝓢(ℝ,ℂ) := fun p =>
    mellinLogSchwartz (W p.1) (h.compact p.1) (h.positive p.1) (h.smooth p.1) p.2
  have hb : Bornology.IsVonNBounded ℝ (f '' {p | |p.2| ≤ M}) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro a
    obtain ⟨C,hC,hbound⟩ := h.log_seminorms M a.1 a.2
    exact ⟨C+1,by linarith,fun p hp => (hbound p.1 p.2 hp).trans_lt (by linarith)⟩
  let L : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.compCLM ℝ (by
      simp only [div_eq_mul_inv]
      fun_prop : (fun t : ℝ => t/(2*Real.pi)).HasTemperateGrowth)
      mellin_frequency_growth).comp (SchwartzMap.fourierTransformCLM ℝ)
  convert hb.image L using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Set.image_comp]
  rfl

lemma UniformLogWeights.vertical_seminorms {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i σ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n
        (mellinVerticalSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) ≤ C := by
  obtain ⟨C,hC,hb⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded
      (fun p : ι × ℝ => mellinVerticalSchwartz (W p.1) (h.compact p.1)
        (h.positive p.1) (h.smooth p.1) p.2) |>.mp (h.vertical_bounded M) (k,n)
  exact ⟨C,hC,fun i σ hσ => (hb (i,σ) hσ).le⟩

lemma UniformLogWeights.mellin_norm_moment {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i σ, |σ| ≤ M →
      (∫ t : ℝ, |t|^k*‖mellin (W i) ((σ:ℂ)+(t:ℂ)*Complex.I)‖) ≤ C := by
  let n : ℕ := (volume : Measure ℝ).integrablePower
  obtain ⟨C₀,hC₀,h₀⟩ := h.vertical_seminorms M 0 0
  obtain ⟨C₁,hC₁,h₁⟩ := h.vertical_seminorms M (k+n) 0
  let A : ℝ := 2^n*(∫ t : ℝ, (1+‖t‖)^(-(n:ℝ)))
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg (by norm_num) _)
    (integral_nonneg (fun _ => Real.rpow_nonneg (by positivity) _))
  refine ⟨A*(C₀+C₁),mul_nonneg hA (by positivity),?_⟩
  intro i σ hσ
  let F := mellinVerticalSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ
  have hb := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume F k 0
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hb
  change (∫ t : ℝ, |t|^k*‖F t‖) ≤ A*
    (SchwartzMap.seminorm ℝ 0 0 F+SchwartzMap.seminorm ℝ (k+n) 0 F) at hb
  calc
    _ = ∫ t : ℝ, |t|^k*‖F t‖ := by
      congr 1
      ext t
      rw [mellinVerticalSchwartz_apply]
    _ ≤ A*(SchwartzMap.seminorm ℝ 0 0 F+SchwartzMap.seminorm ℝ (k+n) 0 F) := hb
    _ ≤ A*(C₀+C₁) := mul_le_mul_of_nonneg_left
      (add_le_add (h₀ i σ hσ) (h₁ i σ hσ)) hA

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformCoordinateWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform joint Mellin moments from the actual common support and derivative
bounds of the coordinate weights. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellinMass_nonneg (W : ℝ → ℂ) : 0 ≤ zeroLineMellinMass W := by
  unfold zeroLineMellinMass
  positivity

lemma UniformLogWeights.zeroLine_moment {γ : Type*} {W : γ → ℝ → ℂ}
    (h : UniformLogWeights W) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, (∫ t : ℝ, |t|^A*‖zeroLineMellinWeight (W i) 1 t‖) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := h.mellin_norm_moment 0 A
  refine ⟨(1/(2*Real.pi))*C,by positivity,?_⟩
  intro i
  rw [zeroLineMellinWeight_moment (W i) (by norm_num) A]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Complex.ofReal_zero,zero_add] using hbound i 0 (by norm_num)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma independentMellinMoment_factorization (W : ι → ℝ → ℂ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (A : ℕ) :
    independentMellinMoment W A = ∑ i, ∏ j,
      (∫ t : ℝ, if j=i then |t|^A*‖zeroLineMellinWeight (W j) 1 t‖
        else ‖zeroLineMellinWeight (W j) 1 t‖) := by
  unfold independentMellinMoment mellinHeightPower
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ =>
    independentMellinWeight_coordinate_moment_integrable W (fun _ => 1) hW hpos hsm
      (fun _ => by norm_num) A i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_fintype_prod_volume_eq_prod (fun (j : ι) (t : ℝ) =>
    if j=i then |t|^A*‖zeroLineMellinWeight (W j) 1 t‖
      else ‖zeroLineMellinWeight (W j) 1 t‖)]
  apply integral_congr_ae
  filter_upwards with τ
  rw [independentMellinWeight,norm_prod]
  symm
  convert prod_one_coordinate (fun j => ‖zeroLineMellinWeight (W j) 1 (τ j)‖)
    i (|τ i|^A) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j=i <;> simp [hj]

/-- One bound controls the product L1 mass and the genuine joint tail moment
for every member of a uniformly smooth coordinate family. -/
theorem UniformLogWeights.coordinate_moments {γ : Type*} {W : γ → ι → ℝ → ℂ}
    (h : UniformLogWeights (fun z : γ × ι => W z.1 z.2)) (A : ℕ) :
    ∃ C J : ℝ, 0 ≤ C ∧ 0 ≤ J ∧ ∀ u : γ,
      (∏ i, zeroLineMellinMass (W u i)) ≤ C ∧ independentMellinMoment (W u) A ≤ J := by
  obtain ⟨C₀,hC₀,h₀⟩ := h.zeroLine_moment 0
  obtain ⟨C₁,hC₁,h₁⟩ := h.zeroLine_moment A
  let K := max C₀ C₁
  have hK : 0 ≤ K := hC₀.trans (le_max_left _ _)
  refine ⟨K^(Fintype.card ι),(Fintype.card ι:ℝ)*K^(Fintype.card ι),
    pow_nonneg hK _,by positivity,?_⟩
  intro u
  have hmass (i : ι) : zeroLineMellinMass (W u i) ≤ K := by
    have hh := (h₀ (u,i)).trans (le_max_left C₀ C₁)
    simp only [pow_zero,one_mul] at hh
    rw [zeroLineMellinWeight_mass (W u i) (Z := 1) (by norm_num)] at hh
    exact hh
  constructor
  · calc
      _ ≤ ∏ _i : ι, K := Finset.prod_le_prod (fun i _ => zeroLineMellinMass_nonneg (W u i))
        (fun i _ => hmass i)
      _ = _ := by simp
  · rw [independentMellinMoment_factorization (W u) (fun i => h.compact (u,i))
        (fun i => h.positive (u,i)) (fun i => h.smooth (u,i)) A]
    calc
      _ ≤ ∑ _i : ι, K^(Fintype.card ι) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ∏ _j : ι, K := by
            apply Finset.prod_le_prod
            · intro j _
              exact integral_nonneg (fun t => by split_ifs <;> positivity)
            · intro j _
              by_cases hj : j=i
              · simp only [hj,ite_true, if_true]
                exact (h₁ (u,i)).trans (le_max_right _ _)
              · simp only [hj,ite_false, if_false]
                rw [zeroLineMellinWeight_mass (W u j) (Z := 1) (by norm_num)]
                exact hmass j
          _ = _ := by simp
      _ = _ := by simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DilatedMomentPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventual_dilated_shift_height_bound :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ t τ : ℝ,
      |t| ≤ Y^(721/2000:ℝ) → |τ| ≤ Y^(1/1000:ℝ) → |t-τ| ≤ Y^(361/1000:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 1/2000 by norm_num)).eventually_ge_atTop (2:ℝ))
  refine ⟨max 1 T,?_⟩
  intro Y hY t τ ht hτ
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hτ' : |τ| ≤ Y^(721/2000:ℝ) := hτ.trans
    (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
  calc
    _ ≤ |t|+|τ| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le t 0 τ
    _ ≤ 2*Y^(721/2000:ℝ) := by linarith
    _ ≤ Y^(1/2000:ℝ)*Y^(721/2000:ℝ) :=
      mul_le_mul_of_nonneg_right (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonCoordinateExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional exponent is chosen before the smooth-weight family.
Only the threshold depends on its derivative constants. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]


 theorem balanced_common_coordinate_exponents (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      ∃ Y₀ : ℝ, ∀ (u : γ) (Y : ℝ) (X : ι → ℝ)
      (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → (∀ i, 0 < X i) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
        (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t (W u) X V Y‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,e,he,T,hraw⟩ := balanced_twisted_vonMangoldt_neighborhood (ι := ι)
    hpub hHuxley V hV hposV hsmV hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,min e (1/3)/2,by positivity,?_⟩
  intro W hW
  obtain ⟨M,hM⟩ := hV.exists_bound_of_continuous hsmV.continuous
  have hM0 : 0 ≤ M := (_root_.norm_nonneg (V 0)).trans (hM 0)
  let k := Fintype.card ι
  let A := 1000*(2*k+7)
  let K : ℝ := M*72^k
  obtain ⟨L,J,hL,hJ,hMoments⟩ := hW.coordinate_moments A
  obtain ⟨T₁,hshift⟩ := eventual_dilated_shift_height_bound
  obtain ⟨T₂,hT₂,habs⟩ := absorb_short_mellin_bounds he (2*L^2) (2*K^2*J^2)
    (by positivity) (by positivity)
  refine ⟨max 324 (max T (max T₁ T₂)),?_⟩
  intro u Y X q η t P hY hX hq hη hqY ht hP
  have hY324 : 324 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := by linarith
  have hYp : 0 < Y := by linarith
  have hYT : T ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYT₂ : T₂ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hb (τ : ι → ℝ) (hτ : τ ∈ mellinHeightBox (Y^(1/1000:ℝ))) :
      (∑ a : P, ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt)
        (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun i => t i-τ i) V Y‖^2) ≤ Y^(7/3-e) := by
    have hh := hraw Y q η (fun i => t i-τ i) P hYT hq hη hqY
      (fun i => hshift Y hYT₁ _ _ (ht i) (hτ i)) hP
    have heq (a : Eisenstein × Eisenstein) (ha : a ∈ P) :=
      twistedProductPolynomial_eq_unsplit (fun _ : ι => idealVonMangoldt)
        (hP a ha).1.1 (hP a ha).1.2.1 q η hη (fun i => t i-τ i) V hYp hVhi
    have hh' : (∑ a ∈ P, ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt)
        (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun i => t i-τ i) V Y‖^2) ≤ Y^(7/3-e) := by
      calc
        _ = ∑ a ∈ P, ‖primaryComplexProductPolynomial
            (fun i => twistArithmetic (q i) (η i) (t i-τ i) idealVonMangoldt) (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y‖^2 :=
          Finset.sum_congr rfl (fun a ha => by rw [heq a ha])
        _ ≤ _ := hh
    change (∑ a ∈ P.attach, ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt)
      (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun i => t i-τ i) V Y‖^2) ≤ _
    rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
      ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun i => t i-τ i) V Y‖^2)]
    exact hh'
  have hm := coordinate_vonMangoldt_moment_bound (fun a : P => (a : Eisenstein × Eisenstein))
    (fun a => ⟨(hP a a.property).1.1,(hP a a.property).1.2.1⟩) q η hq t (W u) X
    (fun i => hW.compact (u,i)) (fun i => hW.positive (u,i))
    (fun i => hW.smooth (u,i)) hX V hM0 hM hYp.le A (Real.rpow_pos_of_pos hYp _)
    (Real.rpow_nonneg hYp.le _) hb
  have hcard : (Fintype.card P:ℝ) ≤ Y^4 := by
    have hLY : Y^(1/3+κ) ≤ Y := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY1
        (by linarith : 1/3+κ ≤ 1)
    simpa only [Fintype.card_coe] using neighborhood_balanced_card P hY324
      (Real.rpow_nonneg hYp.le _) hLY
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.1⟩)
  have hm' : (∑ a ∈ P, ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
      (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t (W u) X V Y‖^2) ≤ 2*L^2*Y^(7/3-e)+
        2*(Fintype.card P:ℝ)*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := by
    change (∑ a ∈ P.attach, _) ≤ _ at hm
    rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
      ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t (W u) X V Y‖^2)] at hm
    have hmass0 : 0 ≤ ∏ i, zeroLineMellinMass (W u i) :=
      Finset.prod_nonneg (fun i _ => zeroLineMellinMass_nonneg _)
    have hjoint0 := independentMellinMoment_nonneg (W u) A
    apply hm.trans
    gcongr
    · exact (hMoments u).1
    · exact (hMoments u).2
  calc
    _ ≤ 2*L^2*Y^(7/3-e)+2*(Fintype.card P:ℝ)*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := hm'
    _ ≤ 2*L^2*Y^(7/3-e)+2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := by gcongr
    _ ≤ 2*L^2*Y^(7/3-e)+(2*K^2*J^2)*Y^(-42/5:ℝ) := by
      exact add_le_add le_rfl (coordinate_neighborhood_tail_le_short_tail (K := K) (J := J) k hY1)
    _ ≤ _ := habs Y hYT₂

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothLogDenominator
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth, globally defined extensions of the logarithmic denominator
weights. The extension equals the literal reciprocal on the application
range, so no pole can interfere with parameter-uniform differentiation. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CubicFirstMoment

lemma positiveSmoothExtension_eq {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    positiveSmoothExtension c x = x := by
  have h : 1 ≤ 2*x/c-1 := by
    have hd : 2 ≤ 2*x/c := (le_div_iff₀ hc).mpr (by linarith)
    linarith
  simp [positiveSmoothExtension,Real.smoothTransition.one_of_one_le h]

lemma smoothReciprocal_eq {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    smoothReciprocal c x = x⁻¹ := by
  simp only [smoothReciprocal,positiveSmoothExtension_eq hc hx]

lemma smoothLog_eq {x : ℝ} (hx : 1 ≤ x) : smoothLog x = Real.log x := by
  simp only [smoothLog,positiveSmoothExtension_eq (by norm_num : (0:ℝ) < 1) hx]

lemma logDenominatorWeight_eq {c : ℝ} (hc : 0 < c) (w : ℝ → ℂ)
    {p : ℝ × ℝ} (ha : c ≤ p.1) (ht : 0 ≤ p.2) {x : ℝ} (hx : 1 ≤ x) :
    logDenominatorWeight c w p x = w x/(p.1+p.2*Real.log x:ℝ) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hd : c ≤ p.1+p.2*Real.log x := by nlinarith
  rw [logDenominatorWeight,smoothLog_eq hx,smoothReciprocal_eq hc hd]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideLogDenominator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic coordinate range accommodates the fixed dilations in
an output norm partition. The denominator identities need no upper range. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

lemma wideLogWeightParameters_mem {c Y X : ℝ} (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y)
    (hlo : Y^c ≤ X) (hhi : X ≤ Y^2) :
    (Real.log X/Real.log Y,1/Real.log Y) ∈ wideLogWeightParameters c := by
  have hlogY : 0 < Real.log Y := by linarith
  have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
  refine ⟨⟨?_,?_⟩,⟨by positivity,?_⟩⟩
  · apply (le_div_iff₀ hlogY).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hY0 c) hlo
    rw [Real.log_rpow hY0] at h
    nlinarith
  · apply (div_le_iff₀ hlogY).mpr
    have h := Real.log_le_log hX hhi
    rw [Real.log_pow] at h
    norm_num at h ⊢
    linarith
  · exact (one_div_le_one_div_of_le (by norm_num) hY).trans_eq (by norm_num)

lemma logDenominatorWeight_scale_lower {c Y X x : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (hlo : Y^c ≤ X) (hx : 1 ≤ x)
    (w : ℝ → ℂ) :
    logDenominatorWeight c w (Real.log X/Real.log Y,1/Real.log Y) x =
      (Real.log Y:ℂ)*w x/(Real.log (X*x):ℂ) := by
  have hlogY : 0 < Real.log Y := by linarith
  have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
  have hp : c ≤ Real.log X/Real.log Y := by
    apply (le_div_iff₀ hlogY).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hY0 c) hlo
    rw [Real.log_rpow hY0] at h
    linarith
  have hx0 : 0 < x := by linarith
  rw [logDenominatorWeight_eq hc w hp (by positivity) hx,Real.log_mul hX.ne' hx0.ne']
  push_cast
  have hCY : (Real.log Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogY.ne'
  field_simp

lemma normalizedVonMangoldt_weight_lower {c Y X : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (hlo : Y^c ≤ X)
    (w : ℝ → ℂ) (hw : ∀ x, x < 1 → w x = 0) (a : Eisenstein) :
    (normalizedVonMangoldt a:ℂ)*w (norm a/X) =
      (1/(Real.log Y:ℂ))*((MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt:ℝ):ℂ)*
        logDenominatorWeight c w (Real.log X/Real.log Y,1/Real.log Y) (norm a/X) := by
  by_cases hx : 1 ≤ norm a/X
  · have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
    rw [logDenominatorWeight_scale_lower hc hY0 hY hlo hx]
    have he : X*(norm a/X) = norm a := by field_simp
    rw [he]
    unfold normalizedVonMangoldt
    push_cast
    have hCY : (Real.log Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith))
    field_simp
  · have hz := hw _ (lt_of_not_ge hx)
    simp only [hz,mul_zero,logDenominatorWeight]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primaryNormalizedVonMangoldtTuple_eq_lower {c Y : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) :
    primaryNormalizedVonMangoldtTuple a b q η t W X V Y =
      (1/(Real.log Y:ℂ))^(Fintype.card ι)*
      primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y := by
  unfold primaryNormalizedVonMangoldtTuple primaryCoordinateWeightedTuple primaryTupleCore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [normalizedVonMangoldt_weight_lower hc hY0 hY (hXlo _) _ (hWlo _)]
  have he (i : ι) :
      1/(Real.log Y:ℂ)*((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        logDenominatorWeight c (W i) (Real.log (X i)/Real.log Y,1/Real.log Y) (norm (n i)/X i)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
          mellinPhase (t i) (norm (n i))) =
      (1/(Real.log Y:ℂ))*
        (((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
          mellinPhase (t i) (norm (n i))))*
        logDenominatorWeight c (W i) (Real.log (X i)/Real.log Y,1/Real.log Y) (norm (n i)/X i) := by ring
  simp_rw [he,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  ring

lemma normalizedCoordinate_norm_le_lower {c Y : ℝ} (hc : 0 < c) (hY0 : 0 < Y)
    (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) :
    ‖primaryNormalizedVonMangoldtTuple a b q η t W X V Y‖ ≤
      ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y‖ := by
  rw [primaryNormalizedVonMangoldtTuple_eq_lower hc hY0 hY a b q η t W X V hWlo hXlo,
    norm_mul,norm_pow]
  apply mul_le_of_le_one_left (_root_.norm_nonneg _)
  apply pow_le_one₀ (_root_.norm_nonneg _) _
  rw [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
  exact (div_le_one (by linarith)).mpr hY

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonNormalizedExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both normalized prime moments uniformly over actual smooth-weight families. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem balanced_common_normalized_exponents_oai (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → 0 < Y → 1 ≤ Real.log Y →
      (∀ i, Y^c ≤ X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryNormalizedVonMangoldtTuple a.1 a.2 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,e,he,hraw⟩ := balanced_common_coordinate_exponents
    (γ := γ × (ι → wideLogWeightParameters c)) (ι := ι) hpub hHuxley V hV hposV hsmV hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,e,he,?_⟩
  intro W hW hWlo
  let L : (γ × (ι → wideLogWeightParameters c)) → ι → ℝ → ℂ :=
    fun r i => logDenominatorWeight c (W r.1 i) (r.2 i)
  have hL : UniformLogWeights (fun z : (γ × (ι → wideLogWeightParameters c)) × ι => L z.1 z.2) :=
    uniformCoordinateWideLogDenominatorWeights hc hW
  obtain ⟨T,hfamily⟩ := hraw L hL
  refine ⟨T,?_⟩
  intro r Y X q η t P hYT hY0 hlog hXlo hXhi hq hη hqY ht hP
  let p : ι → wideLogWeightParameters c := fun i =>
    ⟨(Real.log (X i)/Real.log Y,1/Real.log Y),wideLogWeightParameters_mem hY0 hlog (hXlo i) (hXhi i)⟩
  have hb := hfamily (r,p) Y X q η t P hYT
    (fun i => (Real.rpow_pos_of_pos hY0 c).trans_le (hXlo i)) hq hη hqY ht hP
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro a ha
  exact pow_le_pow_left₀ (_root_.norm_nonneg _)
    (normalizedCoordinate_norm_le_lower hc hY0 hlog a.1 a.2 q η t (W r) X V (hWlo r) hXlo) 2

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CubicFirstMoment.balanced_common_normalized_exponents_oai.{u_1, u_2} := @OAI.CubicFirstMoment.balanced_common_normalized_exponents_oai.{u_1, u_2}
