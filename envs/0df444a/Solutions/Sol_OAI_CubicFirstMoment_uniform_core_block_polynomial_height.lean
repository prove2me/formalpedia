-- Prove2me | solution 1 for OAI.CubicFirstMoment.uniform_core_block_polynomial_height
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:10:00.438071+00:00
-- url     : https://prove2.me/submissions/68dcbdb3-7a8f-4462-ad87-77944de48eee

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A020
import Definitions.Def_OAIQ096A023
import Theorems.Thm_OAI_CubicFirstMoment_balanced_common_normalized_exponents
import Theorems.Thm_OAI_CubicFirstMoment_dilated_noncube_three_sieve_bounds
import Theorems.Thm_OAI_CubicFirstMoment_first_unweighted_structured_moment

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma normNat_ne_zero_of_ne_zero {h : Eisenstein} (hh : h ≠ 0) : normNat h ≠ 0 := by
  intro hz
  apply hh
  apply norm_eq_zero_iff.mp
  rw [← normNat_cast,hz,Nat.cast_zero]

lemma mem_frequencyDyad {j : ℕ} {h : Eisenstein} :
    h ∈ frequencyDyad j ↔ h ≠ 0 ∧ Nat.log 2 (normNat h) = j := by
  simp only [frequencyDyad, Finset.mem_filter, mem_nonzeroNormBall]
  refine ⟨fun h => ⟨h.1.2,h.2⟩,fun hh => ⟨⟨?_,hh.1⟩,hh.2⟩⟩
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at ht
  rw [← normNat_cast]
  exact_mod_cast ht.le

lemma frequencyDyad_norm {j : ℕ} {h : Eisenstein} (hh : h ∈ frequencyDyad j) :
    (2 : ℝ)^j ≤ norm h ∧ norm h ≤ 2*(2 : ℝ)^j := by
  rw [mem_frequencyDyad] at hh
  have hl := Nat.pow_log_le_self 2 (normNat_ne_zero_of_ne_zero hh.1)
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at hl ht
  rw [← normNat_cast]
  constructor
  · exact_mod_cast hl
  · have ht' : (normNat h : ℝ) ≤ (2 : ℝ)^(j+1) := by exact_mod_cast ht.le
    simpa [pow_succ,mul_comm] using ht'

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma mem_squarefreePrimaryDyad {n : Eisenstein} {j : ℕ} :
    n ∈ squarefreePrimaryDyad j ↔ n ∈ frequencyDyad j ∧ primary n ∧ Squarefree n := by
  simp [squarefreePrimaryDyad]

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma rpow_third_cube {x : ℝ} (hx : 0 ≤ x) : (x^(1/3 : ℝ))^3 = x := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]
  norm_num

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergent norm series on the Eisenstein lattice

These elementary lattice bounds provide a quantitative tail for the
Möbius residue sum after square-divisor truncation.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment

lemma norm_rpow_tail_pointwise {D s t : ℝ} (hD : 0 < D) (hst : s < t)
    {a : Eisenstein} (ha : D < norm a) :
    norm a^(-t) ≤ D^(s-t)*norm a^(-s) := by
  have hn : 0 < norm a := hD.trans ha
  calc
    _ = norm a^(s-t)*norm a^(-s) := by
      rw [← Real.rpow_add hn]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hD ha.le (by linarith))
      (Real.rpow_nonneg hn.le _)

/-- A stronger convergent exponent gives a power tail without losing a
factor to the norm fibers. -/
theorem eisenstein_norm_rpow_tail {D s t : ℝ} (hD : 0 < D)
    (hs : 1 < s) (hst : s < t) :
    (∑' a : Eisenstein, if D < norm a then norm a^(-t) else 0) ≤
      D^(s-t)*(∑' a : Eisenstein, norm a^(-s)) := by
  have ht := summable_eisenstein_norm_rpow (hs.trans hst)
  have htail := ht.indicator (fun a => D < norm a)
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ htail ((summable_eisenstein_norm_rpow hs).mul_left _)
  intro a
  change (if D < norm a then norm a^(-t) else 0) ≤ D^(s-t)*norm a^(-s)
  by_cases ha : D < norm a
  · simpa only [ha,ite_true, if_true] using norm_rpow_tail_pointwise hD hst ha
  · simp only [ha,ite_false, if_false]
    exact mul_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg (norm_nonneg a) _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAdditiveSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem normTwist_mul (u : ℝ) {a b : Eisenstein}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    normTwist u (a * b) = normTwist u a * normTwist u b := by
  have han : norm a ≠ 0 := (norm_eq_zero_iff.not.mpr ha)
  have hbn : norm b ≠ 0 := (norm_eq_zero_iff.not.mpr hb)
  have hn : norm (a * b) = norm a * norm b := Complex.normSq_mul _ _
  simp only [normTwist, hn, Real.log_mul han hbn, mul_add, Complex.ofReal_add,
    add_mul, Complex.exp_add]

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
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth weights and Mellin twists

The derivative cost below explains why the unweighted published Hecke
estimate continues to give any prescribed logarithmic saving after a
fixed-logarithmic-height norm twist. It is used with `weighted_cubic_prime_bound`.
-/

noncomputable section

namespace CubicFirstMoment

theorem normTwist_eq_mellinPhase (u : ℝ) (a : Eisenstein) :
    normTwist u a = mellinPhase u (norm a) := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeSquareSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse support from a large square divisor, used to remove repeated
large primes in the exceptional character moments. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma square_multiples_normBall {Y : ℝ} {d b : Eisenstein}
    (hd : d ≠ 0) (hb : b ∈ nonzeroNormBall Y) (hdiv : d^2 ∣ b) :
    b ∈ (nonzeroNormBall (Y/(norm d)^2)).image (fun c => d^2*c) := by
  obtain ⟨c,rfl⟩ := hdiv
  have hspec := mem_nonzeroNormBall.mp hb
  have hc : c ≠ 0 := by intro h; simp [h] at hspec
  have hnorm : norm (d^2*c) = (norm d)^2*norm c := by
    simp [pow_two,mul_assoc]
  apply Finset.mem_image.mpr
  refine ⟨c,mem_nonzeroNormBall.mpr ⟨?_,hc⟩,rfl⟩
  apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_of_ne_zero hd))).mpr
  have h := hspec.1
  rw [hnorm] at h
  nlinarith

/-- Cardinality is at most `C Y / sqrt D`, uniformly for positive `D`.
The proof uses only planar lattice counting and a convergent norm series. -/
theorem largeSquareSupport_card_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y D : ℝ, 0 ≤ Y → 0 < D →
      ((largeSquareSupport Y D).card:ℝ) ≤ C*Y*D^(-(1/2:ℝ)) := by
  let Z := ∑' d : Eisenstein, norm d^(-(3/2:ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  refine ⟨18*Z+1,by positivity,?_⟩
  intro Y D hY hD
  let T := (nonzeroNormBall Y).filter (fun d => D < norm d)
  let F (d : Eisenstein) := (nonzeroNormBall (Y/(norm d)^2)).image (fun c => d^2*c)
  have hcover : largeSquareSupport Y D ⊆ T.biUnion F := by
    intro b hb
    obtain ⟨hball,d,hd,hdiv⟩ := Finset.mem_filter.mp hb
    have hd0 : d ≠ 0 := norm_eq_zero_iff.not.mp (ne_of_gt (hD.trans hd))
    have hdvd : d ∣ b := (dvd_pow_self d (by norm_num : 2 ≠ 0)).trans hdiv
    have hdb : norm d ≤ norm b := norm_le_of_dvd (mem_nonzeroNormBall.mp hball).2 hdvd
    apply Finset.mem_biUnion.mpr
    refine ⟨d,Finset.mem_filter.mpr ⟨mem_nonzeroNormBall.mpr
      ⟨hdb.trans (mem_nonzeroNormBall.mp hball).1,hd0⟩,hd⟩,?_⟩
    exact square_multiples_normBall hd0 hball hdiv
  have hcard : ((largeSquareSupport Y D).card:ℝ) ≤ ∑ d ∈ T, ((F d).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hsum : (∑ d ∈ T, 1/(norm d)^2) ≤ D^(-(1/2:ℝ))*Z := by
    have htail := eisenstein_norm_rpow_tail (s := (3/2:ℝ)) (t := 2) hD
      (by norm_num) (by norm_num)
    norm_num only at htail
    apply le_trans _ htail
    have hs := (summable_eisenstein_norm_rpow (s := 2) (by norm_num)).indicator
      (fun d => D < norm d)
    calc
      _ = ∑ d ∈ T, if D < norm d then norm d^(-(2:ℝ)) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hn := (Finset.mem_filter.mp hd).2
        rw [ite_eq_left hn,Real.rpow_neg (norm_nonneg d),Real.rpow_two,one_div]
      _ ≤ _ := hs.sum_le_tsum T (fun d _ => by
        split_ifs
        · exact Real.rpow_nonneg (norm_nonneg d) _
        · exact le_rfl)
  calc
    _ ≤ ∑ d ∈ T, ((F d).card:ℝ) := hcard
    _ ≤ ∑ d ∈ T, 18*(Y/(norm d)^2) := by
      apply Finset.sum_le_sum
      intro d hd
      have hi : ((F d).card:ℝ) ≤ ((nonzeroNormBall (Y/(norm d)^2)).card:ℝ) := by
        exact_mod_cast Finset.card_image_le
      exact hi.trans (nonzeroNormBall_card_le (by positivity))
    _ = 18*Y*(∑ d ∈ T, 1/(norm d)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 18*Y*(D^(-(1/2:ℝ))*Z) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := by nlinarith [Real.rpow_nonneg hD.le (-(1/2:ℝ))]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coefficient bounds for a bounded number of ordered prime factors. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Every prime in another tuple with the same product occurs in the
reference tuple. This includes repeated primes. -/
lemma prime_tuple_range_subset (f g : ι → Eisenstein)
    (hf : ∀ i, primaryPrime (f i)) (hg : ∀ i, primaryPrime (g i))
    (hprod : (∏ i, g i) = ∏ i, f i) (i : ι) :
    g i ∈ Finset.univ.image f := by
  have hd : g i ∣ ∏ j, f j := hprod ▸ Finset.dvd_prod_of_mem g (Finset.mem_univ i)
  obtain ⟨j,_,hj⟩ := ((hg i).2.dvd_finsetProd_iff f).mp hd
  have he : g i = f j := primary_associated_eq (hg i).1 (hf j).1
    (((hg i).2.dvd_prime_iff_associated (hf j).2).mp hj)
  exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he.symm⟩

/-- The deliberately generous `k^k` bound avoids ordering conventions and
is uniform in the norm and in all independent supports. -/
theorem prime_tuple_fiber_card (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (b : Eisenstein) :
    ((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card ≤
      (Fintype.card ι)^(Fintype.card ι) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  by_cases ht : T.Nonempty
  · obtain ⟨f,hf⟩ := ht
    have hfs := (Finset.mem_filter.mp hf).1
    have hfb := (Finset.mem_filter.mp hf).2
    have hprime : ∀ i, primaryPrime (f i) :=
      fun i => hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)
    have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.univ.image f) := by
      intro g hg
      obtain ⟨hgs,hgb⟩ := Finset.mem_filter.mp hg
      apply Fintype.mem_piFinset.mpr
      exact prime_tuple_range_subset f g hprime
        (fun i => hS i (g i) ((Fintype.mem_piFinset.mp hgs) i)) (hgb.trans hfb.symm)
    calc
      T.card ≤ (Fintype.piFinset (fun _ : ι => Finset.univ.image f)).card :=
        Finset.card_le_card hsub
      _ = ((Finset.univ.image f).card)^(Fintype.card ι) := by
        simp [Fintype.card_piFinset]
      _ ≤ _ := Nat.pow_le_pow_left (by
        simpa using (Finset.card_image_le (s := (Finset.univ:Finset ι)) (f := f))) _
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change T.card ≤ _
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

/-- The coefficient bound depends only on the number of prime factors
and on their separate weight bounds, including for nonsquarefree products. -/
theorem orderedConvolution_norm_bound (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (M : ι → ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (hM : ∀ i, 0 ≤ M i) (hw : ∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i)
    (b : Eisenstein) :
    ‖orderedConvolution S w b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  have hprod : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  unfold orderedConvolution
  calc
    _ ≤ ∑ f ∈ T, ‖∏ i, w i (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ T, ∏ i, M i := by
      apply Finset.sum_le_sum
      intro f hf
      rw [norm_prod]
      exact Finset.prod_le_prod (fun i _ => _root_.norm_nonneg _)
        (fun i _ => hw i (f i) ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1) i))
    _ = (T.card:ℝ)*(∏ i, M i) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (prime_tuple_fiber_card S hS b)) hprod

/-- Removing nonsquarefree products never enlarges a coefficient; its
error also obeys the same uniform coefficient bound. -/
theorem convolutionError_norm_bound (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (M : ι → ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (hM : ∀ i, 0 ≤ M i) (hw : ∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i)
    (b : Eisenstein) :
    ‖orderedConvolution S w b-squarefreeConvolution S w b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  by_cases hs : Squarefree b
  · simp only [squarefreeConvolution,ite_eq_left hs,sub_self,norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))
  · simpa only [squarefreeConvolution,ite_eq_right hs,sub_zero] using
      orderedConvolution_norm_bound S w M hS hM hw b

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- A character bounded by one does not increase coefficient energy,
including at primes dividing its conductor, where it may vanish. -/
lemma coefficient_twist_energy_le (B : Finset Eisenstein)
    (β χ : Eisenstein → ℂ) (hχ : ∀ b ∈ B, ‖χ b‖ ≤ 1) :
    (∑ b ∈ B, ‖β b * χ b‖ ^ 2) ≤ ∑ b ∈ B, ‖β b‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro b hb
  apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
  rw [norm_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hχ b hb) (_root_.norm_nonneg (β b))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseFourthMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square of a structured error polynomial has controlled coefficient
energy. This supplies the fourth-moment estimate in the balanced range. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma second_moment_sq_le_card_fourth {ι : Type*} (P : Finset ι) (v : ι → ℂ) :
    (∑ p ∈ P, ‖v p‖^2)^2 ≤ (P.card:ℝ)*∑ p ∈ P, ‖v p‖^4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq P (fun _ => (1:ℝ)) (fun p => ‖v p‖^2)
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,← pow_mul] using h

lemma squareConvolution_character (B : Finset Eisenstein) (v χ : Eisenstein → ℂ)
    (hχ : ∀ a b, χ (a*b) = χ a*χ b) :
    (∑ n ∈ productSupport B, squareConvolution B v n*χ n) =
      (∑ b ∈ B, v b*χ b)^2 := by
  unfold squareConvolution productSupport
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ n ∈ (B.product B).image (fun z => z.1*z.2),
        ∑ z ∈ B.product B with z.1*z.2 = n, (v z.1*v z.2)*χ (z.1*z.2) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2]
    _ = ∑ z ∈ B.product B, (v z.1*v z.2)*χ (z.1*z.2) :=
      Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem _ hz) _
    _ = _ := by
      rw [Finset.product_eq_sprod,Finset.sum_product B B _,pow_two,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [hχ]
      ring

lemma squareConvolution_energy (B : Finset Eisenstein) (v : Eisenstein → ℂ)
    {K : ℝ} (hK : ∀ n ∈ productSupport B,
      (((B.product B).filter (fun z => z.1*z.2 = n)).card:ℝ) ≤ K) :
    (∑ n ∈ productSupport B, ‖squareConvolution B v n‖^2) ≤
      K*(∑ b ∈ B, ‖v b‖^2)^2 := by
  have hrow (n : Eisenstein) (hn : n ∈ productSupport B) :
      ‖squareConvolution B v n‖^2 ≤
        K * ∑ z ∈ B.product B with z.1*z.2 = n, ‖v z.1*v z.2‖^2 := by
    let T := (B.product B).filter (fun z => z.1*z.2 = n)
    have hc := complex_bilinear_rows_sq T (fun _ => (1:ℂ)) (fun z => v z.1*v z.2)
    simp only [one_mul,norm_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right (hK n hn)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  calc
    _ ≤ ∑ n ∈ productSupport B,
        K * ∑ z ∈ B.product B with z.1*z.2 = n, ‖v z.1*v z.2‖^2 :=
      Finset.sum_le_sum hrow
    _ = K * ∑ z ∈ B.product B, ‖v z.1*v z.2‖^2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem _ hz) _
    _ = _ := by
      simp only [norm_mul,mul_pow]
      rw [Finset.product_eq_sprod,Finset.sum_product B B _]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul,pow_two]

/-- Apply the ordinary character sieve to the actual squared polynomial.
The input multiplicity is purely arithmetic and is discharged below for
bounded-length products of primes. -/
theorem ordinary_mixed_fourth_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q Z : ℝ), 1 ≤ Q → 1 ≤ Z →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (B : Finset Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ b ∈ B, b ≠ 0 ∧ norm b ≤ Z) →
      ∀ (K : ℝ), (∀ n ∈ productSupport B,
        (((B.product B).filter (fun z => z.1*z.2 = n)).card:ℝ) ≤ K) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^4) ≤
        C*Q^ε*(Q^2+Z^2)*K*(∑ b ∈ B, ‖v b‖^2)^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve_finite hHuxley hε
  refine ⟨C,hC,?_⟩
  intro Q Z hQ hZ P B hP hB K hK v
  have hBB : ∀ n ∈ productSupport B, n ≠ 0 ∧ norm n ≤ Z^2 := by
    intro n hn
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    refine ⟨mul_ne_zero (hB a ha).1 (hB b hb).1,?_⟩
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul (hB a ha).2 (hB b hb).2 (norm_nonneg b) (by linarith)
  have he (p : Eisenstein × Eisenstein) (hp : p ∈ P) :
      ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^4 =
      ‖∑ n ∈ productSupport B, squareConvolution B v n*mixedCubic p.1 p.2 n‖^2 := by
    rw [squareConvolution_character B v _ (mixedCubic_mul (hP p hp).1.1 (hP p hp).1.2.1),
      norm_pow]
    ring
  calc
    _ = ∑ p ∈ P, ‖∑ n ∈ productSupport B,
        squareConvolution B v n*mixedCubic p.1 p.2 n‖^2 := Finset.sum_congr rfl he
    _ ≤ C*Q^ε*(Q^2+Z^2)*∑ n ∈ productSupport B, ‖squareConvolution B v n‖^2 :=
      hbound Q (Z^2) hQ (one_le_pow₀ hZ) P (productSupport B) hP hBB _
    _ ≤ C*Q^ε*(Q^2+Z^2)*(K*(∑ b ∈ B, ‖v b‖^2)^2) :=
      mul_le_mul_of_nonneg_left (squareConvolution_energy B v hK) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedErrorMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- On the powers of one prime ideal, Dirichlet convolution with the
constant-one function is the ordinary partial sum of coefficients. -/
lemma coeff_mul_zeta_single (A : EisensteinArithmeticFunction)
    (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p n) (A * idealZeta) =
      ∑ k ∈ Finset.range (n + 1), MvPowerSeries.coeff (Finsupp.single p k) A := by
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk,
    MvPowerSeries.coeff_apply, idealZeta, mul_one]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k _ => A (Finsupp.single p k)) n

lemma coeff_single_eq_zeta_difference (A : EisensteinArithmeticFunction)
    (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p (n + 1)) A =
      MvPowerSeries.coeff (Finsupp.single p (n + 1)) (A * idealZeta) -
        MvPowerSeries.coeff (Finsupp.single p n) (A * idealZeta) := by
  rw [coeff_mul_zeta_single, coeff_mul_zeta_single, Finset.sum_range_succ]
  ring

lemma idealZeta_mul_moebiusSeries : idealZeta * idealMoebiusSeries = 1 := by
  rw [mul_comm, idealMoebiusSeries_mul_zeta]

lemma idealZeta_mul_vonMangoldt : idealZeta * idealVonMangoldt = idealLogNorm := by
  rw [idealVonMangoldt, ← mul_assoc, idealZeta_mul_moebiusSeries, one_mul]

/-- The ideal von Mangoldt weight on every positive prime power is
exactly the logarithm of the prime-ideal norm. -/
lemma idealVonMangoldt_prime_power (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p (n + 1)) idealVonMangoldt =
      Real.log (normNat (idealPrimeRepresentative p)) := by
  rw [coeff_single_eq_zeta_difference, mul_comm idealVonMangoldt idealZeta,
    idealZeta_mul_vonMangoldt]
  simp only [MvPowerSeries.coeff_apply, idealLogNorm, idealExponentNorm_single,
    Real.log_pow]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMoebiusBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma idealExponentOf_support_card {a : Eisenstein} (ha : Squarefree a) :
    (idealExponentOf a).support.card = (UniqueFactorizationMonoid.factors a).card := by
  have hnodup : (Associates.factors' a).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    exact (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha
  change (Associates.factors' a).toFinset.card = _
  rw [Multiset.toFinset_card_of_nodup hnodup]
  have h := congrArg Multiset.card (Associates.map_subtype_coe_factors' (a := a))
  simpa only [Multiset.card_map] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealVonMangoldt
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma idealVonMangoldt_at_prime {a : Eisenstein} (ha : Prime a) :
    MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt = Real.log (norm a) := by
  have hcard : (idealExponentOf a).support.card = 1 := by
    rw [idealExponentOf_support_card ha.irreducible.squarefree,
      UniqueFactorizationMonoid.card_factors_of_irreducible ha.irreducible]
  obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hcard
  have hone : idealExponentOf a p = 1 := by
    have hle := (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha.irreducible.squarefree p
    omega
  calc
    _ = MvPowerSeries.coeff (Finsupp.single p 1) idealVonMangoldt := by rw [he, hone]
    _ = Real.log (normNat (idealPrimeRepresentative p)) := idealVonMangoldt_prime_power p 0
    _ = Real.log (idealExponentNorm (idealExponentOf a)) := by
      rw [he, hone, idealExponentNorm_single, pow_one]
    _ = _ := by rw [idealExponentOf_norm ha.ne_zero]

/-- A nonzero von Mangoldt coefficient at an actual primary element
comes from an actual power of a primary prime, with no residual unit. -/
lemma idealVonMangoldt_primary_support {a : Eisenstein} (ha : primary a)
    (hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≠ 0) :
    ∃ p : Eisenstein, ∃ j : ℕ, primaryPrime p ∧ 0 < j ∧ a = p ^ j := by
  have hcard : (idealExponentOf a).support.card = 1 := by
    by_contra h
    exact hΛ (idealVonMangoldt_not_prime_power _ h)
  obtain ⟨p, hp, he⟩ := Finsupp.card_support_eq_one.mp hcard
  let j := idealExponentOf a p
  let r := idealPrimeRepresentative p
  have hj : 0 < j := Nat.pos_of_ne_zero hp
  have hgen : idealExponentGenerator (idealExponentOf a) = r ^ j := by
    rw [he]
    exact Finsupp.prod_single_index (h := fun q k => idealPrimeRepresentative q ^ k)
      (pow_zero _)
  have hassoc : Associated (r ^ j) a := by
    rw [← hgen]
    exact idealExponentOf_associated (primary_ne_zero ha)
  have hrdiv : r ∣ a := (dvd_pow_self r hj.ne').trans hassoc.dvd
  have hr : Prime r := (idealPrimeRepresentative_irreducible p).prime
  let q := primaryNormalize r
  have hq : primaryPrime q := ⟨primaryNormalize_primary
    (unit_residue_of_dvd_primary ha hrdiv), prime_primaryNormalize hr⟩
  have hqp : primary (q ^ j) := by
    induction j with
    | zero => simp [primary]
    | succ n ih => simpa only [pow_succ] using primary_mul ih hq.1
  refine ⟨q, j, hq, hj, ?_⟩
  apply primary_associated_eq ha hqp
  exact hassoc.symm.trans ((primaryNormalize_associated r).pow_pow (n := j))

lemma idealVonMangoldt_primary_nonprime_support {a : Eisenstein} (ha : primary a)
    (hprime : ¬ Prime a)
    (hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≠ 0) :
    ∃ p : Eisenstein, ∃ j : ℕ, primaryPrime p ∧ 2 ≤ j ∧ a = p ^ j := by
  obtain ⟨p,j,hp,hj,he⟩ := idealVonMangoldt_primary_support ha hΛ
  refine ⟨p,j,hp,?_,he⟩
  by_contra h
  have hje : j = 1 := by omega
  have hae : a = p := by simpa [hje] using he
  apply hprime
  rw [hae]
  exact hp.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- For primary factors, fixing the first divisor determines the second. -/
lemma primary_pair_fiber_le_divisors (B : Finset Eisenstein)
    (hB : ∀ a ∈ B, primary a) (n : Eisenstein) :
    ((B.product B).filter (fun z => z.1*z.2 = n)).card ≤
      (B.filter (fun a => a ∣ n)).card := by
  let T := (B.product B).filter (fun z => z.1*z.2 = n)
  have hinj : Set.InjOn Prod.fst (T : Set (Eisenstein × Eisenstein)) := by
    intro a ha b hb he
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply Prod.ext he
    have hn : a.1 ≠ 0 := primary_ne_zero (hB a.1 (Finset.mem_product.mp ha'.1).1)
    apply mul_left_cancel₀ hn
    calc
      a.1*a.2 = n := ha'.2
      _ = b.1*b.2 := hb'.2.symm
      _ = a.1*b.2 := by rw [he]
  have hsub : T.image Prod.fst ⊆ B.filter (fun a => a ∣ n) := by
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hz,hzn⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hz).1,?_⟩
    exact ⟨z.2,hzn.symm⟩
  exact (Finset.card_image_iff.mpr hinj).symm.le.trans (Finset.card_le_card hsub)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDivisorPower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher prime powers in the von Mangoldt replacement have sparse support,
even when the underlying prime is small. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primePower_norm_pow (p : Eisenstein) (j : ℕ) : norm (p^j) = norm p^j := by
  induction j with
  | zero => simp [norm]
  | succ j ih => rw [pow_succ,norm_mul_eq,ih,pow_succ]

/-- Extracting half the exponent produces a genuinely large square divisor.
The bound depends on the prime-power norm, not the prime norm. -/
lemma large_square_of_prime_power {p b : Eisenstein} (hp : p ≠ 0) {j : ℕ}
    (hj : 2 ≤ j) {Y c : ℝ} (hY : 0 < Y)
    (hlarge : Y^c < norm (p^j)) (hdiv : p^j ∣ b) :
    ∃ d : Eisenstein, Y^(c/4) < norm d ∧ d^2 ∣ b := by
  refine ⟨p^(j/2),?_,?_⟩
  · have he : j ≤ 4*(j/2) := by omega
    have hpow : norm (p^j) ≤ norm (p^(j/2))^4 := by
      rw [primePower_norm_pow,primePower_norm_pow,← pow_mul]
      rw [Nat.mul_comm (j/2) 4]
      exact pow_le_pow_right₀ (one_le_norm hp) he
    have hYpow : (Y^(c/4))^4 = Y^c := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hY.le]
      congr 1
      norm_num
    by_contra! hn
    have hd := pow_le_pow_left₀ (norm_nonneg _) hn 4
    rw [hYpow] at hd
    exact (hlarge.trans_le hpow).not_ge hd
  · apply dvd_trans _ hdiv
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega)

lemma largePrimePowerSupport_subset {Y c : ℝ} (hY : 0 < Y) :
    largePrimePowerSupport Y c ⊆ largeSquareSupport Y (Y^(c/4)) := by
  intro b hb
  obtain ⟨hball,p,j,hp,hj,hlarge,hdiv⟩ := Finset.mem_filter.mp hb
  obtain ⟨d,hd,hdvd⟩ := large_square_of_prime_power hp.2.ne_zero hj hY hlarge hdiv
  exact Finset.mem_filter.mpr ⟨hball,d,hd,hdvd⟩

/-- A fixed positive power is saved for every higher-prime-power error support. -/
theorem largePrimePowerSupport_card_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y c : ℝ), 0 < Y →
      ((largePrimePowerSupport Y c).card:ℝ) ≤ K*Y^(1-c/8) := by
  obtain ⟨K,hK,hbound⟩ := largeSquareSupport_card_bound
  refine ⟨K,hK,?_⟩
  intro Y c hY
  have h := hbound Y (Y^(c/4)) hY.le (Real.rpow_pos_of_pos hY _)
  have hcard : ((largePrimePowerSupport Y c).card:ℝ) ≤
      ((largeSquareSupport Y (Y^(c/4))).card:ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (largePrimePowerSupport_subset hY))
  have he : K*Y*(Y^(c/4))^(-(1/2:ℝ)) = K*Y^(1-c/8) := by
    rw [mul_assoc]
    congr 1
    calc
      _ = Y^(1:ℝ)*Y^(c/4*(-(1/2:ℝ))) := by
        rw [Real.rpow_one,← Real.rpow_mul hY.le]
      _ = Y^(1+c/4*(-(1/2:ℝ))) := (Real.rpow_add hY _ _).symm
      _ = _ := by congr 1; ring
  exact hcard.trans (h.trans_eq he)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryHeckeCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite character attached to the primary mixed cubic
symbol. Including the modulus 3 makes primary normalization periodic
and removes its dependence on the choice of a unit associate. -/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryNormalize_unit {x : Eisenstein} (hx : IsUnit x) : primaryNormalize x = 1 :=
  primary_unit_eq_one ((primaryNormalize_associated x).isUnit_iff.mp hx)
    (primaryNormalize_primary (hx.map (Ideal.Quotient.mk (modulus 3))))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueProducts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Products of the actual finite residue characters, including overlapping
moduli. The ideal coefficients are exactly the products of the two factors. -/
noncomputable section
namespace CubicFirstMoment

lemma productResidueChar_units {q r : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (η : MulChar (Residues r) ℂ)
    (hχ : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) u) = 1)
    (u : Eisensteinˣ) : productResidueChar χ η (Ideal.Quotient.mk (modulus (q*r)) u) = 1 := by
  rw [productResidueChar_mk,hχ,hη,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullMellinMoment
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedScalePowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed dilations preserve every strict exponent margin used by the
finite output partition. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventually_const_mul_rpow_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ Y : ℝ in atTop, C*Y^a ≤ Y^b := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C] with Y hY hC
  calc
    _ ≤ Y^(b-a)*Y^a := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hY.le _)
    _ = _ := by rw [← Real.rpow_add hY]; congr 1; ring

lemma eventually_rpow_le_const_mul {a b C : ℝ} (hab : a < b) (hC : 0 < C) :
    ∀ᶠ Y : ℝ in atTop, Y^a ≤ C*Y^b := by
  filter_upwards [eventually_const_mul_rpow_le hab C⁻¹] with Y hY
  calc
    _ = C*(C⁻¹*Y^a) := by rw [← mul_assoc,mul_inv_cancel₀ hC.ne',one_mul]
    _ ≤ C*Y^b := mul_le_mul_of_nonneg_left hY hC.le

lemma eventually_scaled_rpow_le {a b σ : ℝ} (hab : a < b) (hσ : 0 < σ) :
    ∀ᶠ Y : ℝ in atTop, (σ*Y)^a ≤ Y^b := by
  filter_upwards [eventually_ge_atTop (0:ℝ),eventually_const_mul_rpow_le hab (σ^a)] with Y hY h
  rwa [Real.mul_rpow hσ.le hY]

lemma eventually_rpow_le_scaled {a b σ : ℝ} (hab : a < b) (hσ : 0 < σ) :
    ∀ᶠ Y : ℝ in atTop, Y^a ≤ (σ*Y)^b := by
  filter_upwards [eventually_ge_atTop (0:ℝ),eventually_rpow_le_const_mul hab
    (Real.rpow_pos_of_pos hσ b)] with Y hY h
  rwa [Real.mul_rpow hσ.le hY]

lemma eventually_scaled_power_window (a : ℝ) {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    ∀ᶠ Y : ℝ in atTop,
      (σ*Y)^(a-κ) ≤ Y^(a-κ/2) ∧ Y^(a+κ/2) ≤ (σ*Y)^(a+κ) := by
  exact (eventually_scaled_rpow_le (by linarith : a-κ < a-κ/2) hσ).and
    (eventually_rpow_le_scaled (by linarith : a+κ/2 < a+κ) hσ)

lemma eventually_scaled_coordinate_lower {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) :
    ∀ᶠ Y : ℝ in atTop, (2*(σ*Y))^(c/2) ≤ (2*Y)^c := by
  have h₁ := eventually_scaled_rpow_le (by linarith : c/2 < 3*c/4)
    (mul_pos (by norm_num : (0:ℝ) < 2) hσ)
  have h₂ := eventually_rpow_le_scaled (by linarith : 3*c/4 < c) (by norm_num : (0:ℝ) < 2)
  filter_upwards [h₁,h₂] with Y h₁ h₂
  have h₁' : (2*(σ*Y))^(c/2) ≤ Y^(3*c/4) := by simpa only [mul_assoc] using h₁
  exact h₁'.trans h₂

lemma eventually_fixed_scale_moment_bounds {σ κ c ε : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hc : 0 < c) (hε : 0 < ε) (T : ℝ) :
    ∀ᶠ Y : ℝ in atTop, FixedScaleMomentBounds Y σ κ c ε T := by
  have hlim : Tendsto (fun Y : ℝ => σ*Y) atTop atTop :=
    Tendsto.const_mul_atTop' hσ tendsto_id
  filter_upwards [hlim.eventually_ge_atTop T,
    (Real.tendsto_log_atTop.comp hlim).eventually_ge_atTop 1,
    eventually_scaled_power_window 1 hκ hσ,
    eventually_scaled_power_window (1/3) hκ hσ,
    eventually_rpow_le_scaled (by linarith : κ/2 < κ) hσ,
    eventually_rpow_le_scaled (by norm_num : (9/25:ℝ) < 721/2000) hσ,
    eventually_rpow_le_scaled (by norm_num : (1:ℝ) < 2) hσ,
    eventually_scaled_coordinate_lower hc hσ,
    eventually_scaled_rpow_le (by linarith : 7/3-ε < 7/3-ε/2) hσ]
    with Y hT hlog hfirst hbal hsmall hheight hupper hlower hsave
  refine ⟨hT,hlog,hfirst,hbal,hsmall,hheight,?_,hlower,hsave⟩
  simpa only [Real.rpow_one,Real.rpow_two] using hupper

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogReplacement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact replacement of a prime indicator by von Mangoldt divided by log norm.
The discrepancy is bounded and is supported on actual higher primary prime powers. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_norm_gt_one {p : Eisenstein} (hp : Prime p) : 1 < norm p := by
  have hn := one_le_norm hp.ne_zero
  apply lt_of_le_of_ne hn
  intro he
  exact hp.not_isUnit (isUnit_of_norm_eq_one he.symm)

lemma normalizedVonMangoldt_at_prime {p : Eisenstein} (hp : Prime p) :
    normalizedVonMangoldt p = 1 := by
  rw [normalizedVonMangoldt,idealVonMangoldt_at_prime hp]
  exact div_self (Real.log_pos (prime_norm_gt_one hp)).ne'

lemma normalizedVonMangoldt_nonneg {a : Eisenstein} (ha : primary a) :
    0 ≤ normalizedVonMangoldt a :=
  div_nonneg (idealVonMangoldt_coeff_nonneg _)
    (Real.log_nonneg (one_le_norm (primary_ne_zero ha)))

lemma normalizedVonMangoldt_le_one {a : Eisenstein} (ha : primary a) :
    normalizedVonMangoldt a ≤ 1 := by
  have hlog : 0 ≤ Real.log (norm a) := Real.log_nonneg (one_le_norm (primary_ne_zero ha))
  have hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≤ Real.log (norm a) := by
    simpa only [idealExponentOf_norm (primary_ne_zero ha)] using
      idealVonMangoldt_coeff_le_logNorm (idealExponentOf a)
  by_cases hz : Real.log (norm a) = 0
  · simp only [normalizedVonMangoldt,hz,div_zero]
    norm_num
  · exact (div_le_one (lt_of_le_of_ne hlog (Ne.symm hz))).mpr hΛ

lemma primeLogCorrection_at_prime {p : Eisenstein} (hp : Prime p) :
    primeLogCorrection p = 0 := by
  simp only [primeLogCorrection,normalizedVonMangoldt_at_prime hp,primeIndicator,
    ite_eq_left hp,sub_self]

lemma primeLogCorrection_support {a : Eisenstein} (ha : primary a)
    (he : primeLogCorrection a ≠ 0) :
    ∃ p : Eisenstein, ∃ j : ℕ, primaryPrime p ∧ 2 ≤ j ∧ a = p^j := by
  have hp : ¬ Prime a := fun hp => he (primeLogCorrection_at_prime hp)
  have hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≠ 0 := by
    intro hz
    apply he
    simp only [primeLogCorrection,primeIndicator,ite_eq_right hp,normalizedVonMangoldt,hz,
      zero_div,sub_self]
  exact idealVonMangoldt_primary_nonprime_support ha hp hΛ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformWeightMultiplier
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform support and derivative bounds survive the compact family
of logarithmic-denominator multipliers used in the original coefficients. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma UniformLogWeights.norm_bound {γ : Type*} {W : γ → ℝ → ℂ}
    (h : UniformLogWeights W) : ∃ M : ℝ, 0 ≤ M ∧ ∀ i x, ‖W i x‖ ≤ M := by
  obtain ⟨M,hM,hbound⟩ := h.derivative_bound 0
  refine ⟨M,hM,?_⟩
  intro i x
  by_cases hx : 0 < x
  · have he : Real.exp (-(-Real.log x)) = x := by simp [Real.exp_log hx]
    have hb := hbound i (-Real.log x)
    simpa only [norm_iteratedFDeriv_zero,he] using hb
  · have hz : W i x = 0 := by
      by_contra hn
      have hp := h.positive i (subset_closure hn)
      exact hx hp
    simpa only [hz,norm_zero] using hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary power margins used to return from a global cutoff at
2Y to the original exceptional conductor neighborhoods. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma balanced_prime_error_rows {Y κ c : ℝ} (hY : 1 ≤ Y) (hc : 0 < c)
    (hκ : κ ≤ c/256) (a : Eisenstein × Eisenstein)
    (ha : PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
      norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) :
    PrimarySquarefreePair a ∧ norm a.1 ≤ (2*Y)^(1/3+c/256) ∧
      norm a.2 ≤ (2*Y)^(1/3+c/256) := by
  have hp : Y^(1/3+κ) ≤ (2*Y)^(1/3+c/256) :=
    (Real.rpow_le_rpow_of_exponent_le hY (by linarith)).trans
      (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
  exact ⟨ha.1,ha.2.1.trans hp,ha.2.2.1.trans hp⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExplicitMomentAbsorption
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit error exponents, independent of the coefficient-bound constants. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma absorb_prime_coordinate_error_explicit {e d C : ℝ} (he : 0 < e) (hd : 0 < d)
    (hC : 0 ≤ C) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y →
      2*Y^(7/3-e)+2*C*(2*Y)^(7/3-d) ≤ Y^(7/3-min e d/2) := by
  let δ := min e d
  let K := 2+2*C*2^(7/3-d)
  have hδ : 0 < δ := lt_min he hd
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < δ/2 by positivity)).eventually_ge_atTop K)
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have h₁ : Y^(7/3-e) ≤ Y^(7/3-δ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by dsimp [δ]; linarith [min_le_left e d])
  have h₂ : Y^(7/3-d) ≤ Y^(7/3-δ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by dsimp [δ]; linarith [min_le_right e d])
  calc
    _ = 2*Y^(7/3-e)+(2*C*2^(7/3-d))*Y^(7/3-d) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hYp.le]
      ring
    _ ≤ 2*Y^(7/3-δ)+(2*C*2^(7/3-d))*Y^(7/3-δ) := by gcongr
    _ = K*Y^(7/3-δ) := by dsimp [K]; ring
    _ ≤ Y^(δ/2)*Y^(7/3-δ) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual error in replacing a convolution of prime indicators by
normalized von Mangoldt coefficients has sparse prime-power support. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeLogConvolutionError_sum (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (b : Eisenstein) :
    primeLogConvolutionError S w b =
      ∑ f ∈ (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b),
        ((∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i))-
          ∏ i, (primeIndicator (f i):ℂ)*w i (f i)) := by
  unfold primeLogConvolutionError orderedConvolution
  rw [Finset.sum_sub_distrib]

lemma primeLogConvolutionError_support_of_norm_le (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {Y c : ℝ}
    (hS : ∀ i, ∀ a ∈ S i, primary a ∧ Y^c < norm a)
    {b : Eisenstein} (hbY : norm b ≤ Y) (hb : primeLogConvolutionError S w b ≠ 0) :
    b ∈ largePrimePowerSupport Y c := by
  rw [primeLogConvolutionError_sum] at hb
  obtain ⟨f,hf,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  have hex : ∃ i, primeLogCorrection (f i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    have he : (∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i)) =
        ∏ i, (primeIndicator (f i):ℂ)*w i (f i) := by
      apply Finset.prod_congr rfl
      intro i _
      have hi : normalizedVonMangoldt (f i) = primeIndicator (f i) :=
        sub_eq_zero.mp (h i)
      rw [hi]
    exact sub_eq_zero.mpr he
  obtain ⟨i,hi⟩ := hex
  have hfi := hS i (f i) (Fintype.mem_piFinset.mp hfs i)
  obtain ⟨p,j,hp,hj,he⟩ := primeLogCorrection_support hfi.1 hi
  have hprod0 : (∏ i, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => primary_ne_zero (hS i (f i) (Fintype.mem_piFinset.mp hfs i)).1)
  refine Finset.mem_filter.mpr ⟨mem_nonzeroNormBall.mpr
    ⟨hbY,hfb ▸ hprod0⟩,p,j,hp,hj,?_,?_⟩
  · rw [← he]
    exact hfi.2
  · rw [← he,← hfb]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)


lemma primeLog_factor_norm_le (w : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    {a : Eisenstein} (ha : primary a) (hw : ‖w a‖ ≤ M) :
    ‖(normalizedVonMangoldt a:ℂ)*w a‖ ≤ M ∧
    ‖(primeIndicator a:ℂ)*w a‖ ≤ M := by
  constructor
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (normalizedVonMangoldt_nonneg ha)]
    exact (mul_le_mul (normalizedVonMangoldt_le_one ha) hw (_root_.norm_nonneg _) zero_le_one).trans_eq
      (one_mul M)
  · by_cases hp : Prime a
    · simpa only [primeIndicator,ite_eq_left hp,Complex.ofReal_one,one_mul] using hw
    · simp only [primeIndicator,ite_eq_right hp,Complex.ofReal_zero,zero_mul,norm_zero]
      exact hM

/-- A divisor bound gives the genuine error coefficient a subpower amplitude. -/
theorem primeLogConvolutionError_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) → 1 ≤ Y →
      ∀ b ∈ orderedConvolutionSupport S, norm b ≤ Y →
      ‖primeLogConvolutionError S w b‖ ≤ C*Y^ε*(∏ i, M i) := by
  obtain ⟨C,hC,hfiber⟩ := primary_tuple_fiber_small_power (ι := ι) hε
  refine ⟨2*C,by positivity,?_⟩
  intro S w M Y hS hM hw hY b hb hbY
  have hMp : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  have ht (f : ι → Eisenstein) (hf : f ∈ Fintype.piFinset S) :
      ‖(∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i))-
        ∏ i, (primeIndicator (f i):ℂ)*w i (f i)‖ ≤ 2*∏ i, M i := by
    have hl (i : ι) := primeLog_factor_norm_le (w i) (hM i)
      (hS i (f i) (Fintype.mem_piFinset.mp hf i))
      (hw i (f i) (Fintype.mem_piFinset.mp hf i))
    have h1 : ‖∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i)‖ ≤ ∏ i, M i := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => _root_.norm_nonneg _) (fun i _ => (hl i).1)
    have h2 : ‖∏ i, (primeIndicator (f i):ℂ)*w i (f i)‖ ≤ ∏ i, M i := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => _root_.norm_nonneg _) (fun i _ => (hl i).2)
    exact (norm_sub_le _ _).trans (by linarith)
  rw [primeLogConvolutionError_sum]
  calc
    _ ≤ ∑ f ∈ (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b),
        ‖(∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i))-
          ∏ i, (primeIndicator (f i):ℂ)*w i (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b), 2*∏ i, M i :=
      Finset.sum_le_sum (fun f hf => ht f (Finset.mem_filter.mp hf).1)
    _ = (((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card:ℝ)*(2*∏ i, M i) := by simp
    _ ≤ (C*Y^ε)*(2*∏ i, M i) :=
      mul_le_mul_of_nonneg_right (hfiber S hS Y hY b hb hbY) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the original independently weighted prime tuples,
with the individual support and the global norm cutoff both retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinateSupport_primary (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    ∀ i, ∀ n ∈ coordinateSupport W X Y i, primary n := by
  intro i n hn
  exact (mem_primaryElementBall.mp (Finset.mem_filter.mp hn).1).1

omit [Fintype ι] [DecidableEq ι] in
lemma coordinateSupport_lower (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y R : ℝ)
    (hW : ∀ i x, x < 1 → W i x = 0) (hX : ∀ i, 0 < X i)
    (hRX : ∀ i, R < X i) :
    ∀ i, ∀ n ∈ coordinateSupport W X Y i, primary n ∧ R < norm n := by
  intro i n hn
  obtain ⟨hn,hne⟩ := Finset.mem_filter.mp hn
  refine ⟨(mem_primaryElementBall.mp hn).1,(hRX i).trans_le ?_⟩
  have hlo : 1 ≤ norm n/X i := by
    by_contra h
    exact hne (hW i _ (lt_of_not_ge h))
  simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hlo

omit [Fintype ι] [DecidableEq ι] in
lemma coordinateFactor_bound (q : ι → Eisenstein) (hq : ∀ i, q i ≠ 0)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (M : ι → ℝ)
    (hM : ∀ i x, ‖W i x‖ ≤ M i) (i : ι) (n : Eisenstein) :
    ‖coordinateFactor q η t W X i n‖ ≤ M i := by
  unfold coordinateFactor
  rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
  exact (mul_le_of_le_one_right (_root_.norm_nonneg _)
    (residueChar_norm_le_one (hq i) (η i) _)).trans (hM i _)

/-- Collection and support restriction are identities for arbitrary
coefficient functions; the prime and normalized prime cases specialize it. -/
lemma coordinate_convolution_collection (A : Eisenstein → ℂ)
    (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    (∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
      (∏ i, A (n i)*W i (norm (n i)/X i)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
          mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y)) =
    ∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
      orderedConvolution (coordinateSupport W X Y)
        (fun i n => A n*coordinateFactor q η t W X i n) z*
        (mixedCubic a b z*V (norm z/Y)) := by
  rw [orderedConvolution_sum]
  let S : ι → Finset Eisenstein := fun _ => primaryElementBall (2*Y)
  let F : (ι → Eisenstein) → ℂ := fun n =>
    (∏ i, A (n i)*W i (norm (n i)/X i)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y)
  have hsub : Fintype.piFinset (coordinateSupport W X Y) ⊆ Fintype.piFinset S := by
    intro n hn
    exact Fintype.mem_piFinset.mpr (fun i => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1)
  have he : (∑ n ∈ Fintype.piFinset (coordinateSupport W X Y), F n) =
      ∑ n ∈ Fintype.piFinset S, F n := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hex : ∃ i, W i (norm (n i)/X i) = 0 := by
      by_contra hh
      push Not at hh
      exact hnot (Fintype.mem_piFinset.mpr (fun i =>
        Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hn i,hh i⟩))
    obtain ⟨i,hi⟩ := hex
    dsimp [F]
    have hz : (∏ j, A (n j)*W j (norm (n j)/X j)*
      (mixedCubic a b (n j)*η j (Ideal.Quotient.mk (modulus (q j)) (n j))*
        mellinPhase (t j) (norm (n j)))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hi,mul_zero,zero_mul]
    rw [hz,zero_mul]
  change (∑ n ∈ Fintype.piFinset S, F n) = _
  rw [← he]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [F,coordinateFactor]
  rw [mixedCubic_prod _ _ ha hb,norm_finset_prod]
  rw [← mul_assoc,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateDifference
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact difference between normalized von Mangoldt tuples and
original prime-indicator tuples on the global smooth cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma coordinateProductCutoff_spec (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    coordinateProductCutoff W X Y ⊆ orderedConvolutionSupport (coordinateSupport W X Y) ∧
      ∀ b ∈ coordinateProductCutoff W X Y, norm b ≤ 2*Y :=
  ⟨Finset.filter_subset _ _,fun _ hb => (Finset.mem_filter.mp hb).2⟩

lemma normalized_prime_tuple_difference (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryNormalizedVonMangoldtTuple a b q η t W X V Y-
        primaryPrimeIndicatorTuple a b q η t W X V Y =
      ∑ z ∈ coordinateProductCutoff W X Y,
        primeLogConvolutionError (coordinateSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*V (norm z/Y)) := by
  have hn := coordinate_convolution_collection (fun n => (normalizedVonMangoldt n:ℂ))
    a b ha hb q η t W X V Y
  have hp := coordinate_convolution_collection (fun n => (primeIndicator n:ℂ))
    a b ha hb q η t W X V Y
  change primaryNormalizedVonMangoldtTuple a b q η t W X V Y = _ at hn
  change primaryPrimeIndicatorTuple a b q η t W X V Y = _ at hp
  rw [hn,hp,← Finset.sum_sub_distrib]
  have he : (∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
      (orderedConvolution (coordinateSupport W X Y)
        (fun i n => (normalizedVonMangoldt n:ℂ)*coordinateFactor q η t W X i n) z*
          (mixedCubic a b z*V (norm z/Y))-
       orderedConvolution (coordinateSupport W X Y)
        (fun i n => (primeIndicator n:ℂ)*coordinateFactor q η t W X i n) z*
          (mixedCubic a b z*V (norm z/Y)))) =
      ∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
        primeLogConvolutionError (coordinateSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*V (norm z/Y)) := by
    apply Finset.sum_congr rfl
    intro z hz
    unfold primeLogConvolutionError
    ring
  rw [he]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hlarge : 2*Y < norm z := lt_of_not_ge (fun h => hnot (Finset.mem_filter.mpr ⟨hz,h⟩))
  have hv := hV (norm z/Y) ((lt_div_iff₀ hY).mpr hlarge)
  rw [hv,mul_zero,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimarySparseMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse coefficient energy in the balanced conductor region. The pair
multiplicity is bounded using actual primary divisors, with no restriction
on the number of prime bases. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_pair_fiber_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Finset Eisenstein) (Y : ℝ), 1 ≤ Y →
      (∀ b ∈ B, primary b ∧ norm b ≤ Y) → ∀ n ∈ productSupport B,
      (((B.product B).filter (fun z => z.1*z.2 = n)).card:ℝ) ≤ C*Y^ε := by
  obtain ⟨C,hC,hbound⟩ := primary_divisor_card_small_power
    (show 0 < ε/2 by positivity)
  refine ⟨C,hC,?_⟩
  intro B Y hY hB n hn
  obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp hn
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  have hn0 : n ≠ 0 := by
    rw [← he]
    exact mul_ne_zero (primary_ne_zero (hB a ha).1) (primary_ne_zero (hB b hb).1)
  have hnN : norm n ≤ Y^2 := by
    rw [← he,norm_mul_eq,pow_two]
    exact mul_le_mul (hB a ha).2 (hB b hb).2 (norm_nonneg _) (by linarith)
  calc
    _ ≤ ((B.filter (fun a => a ∣ n)).card:ℝ) :=
      Nat.cast_le.mpr (primary_pair_fiber_le_divisors B (fun b hb => (hB b hb).1) n)
    _ ≤ C*norm n^(ε/2) := hbound B (fun b hb => (hB b hb).1) n hn0
    _ ≤ C*(Y^2)^(ε/2) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hnN (by positivity)) hC.le
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ Y)]
      congr 2
      ring

theorem primary_mixed_fourth_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q Y : ℝ), 1 ≤ Q → 1 ≤ Y →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (B : Finset Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ b ∈ B, primary b ∧ norm b ≤ Y) → ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^4) ≤
        C*Q^ε*(Q^2+Y^2)*Y^ε*(∑ b ∈ B, ‖v b‖^2)^2 := by
  obtain ⟨C,hC,hfourth⟩ := ordinary_mixed_fourth_moment hHuxley hε
  obtain ⟨K,hK,hfiber⟩ := primary_pair_fiber_power hε
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro Q Y hQ hY P B hP hB v
  exact (hfourth Q Y hQ hY P B hP
    (fun b hb => ⟨primary_ne_zero (hB b hb).1,(hB b hb).2⟩)
    (K*Y^ε) (hfiber B Y hY hB) v).trans_eq (by ring)

private lemma balancedPrimary_power {Y θ C E m₂ m₄ : ℝ}
    (hY : 1 ≤ Y) (hθ : 0 < θ) (hC : 0 < C) (hE : 0 ≤ E) (hm₂ : 0 ≤ m₂)
    (hCS : m₂^2 ≤ (324*Y^(2/3+θ/8))*m₄)
    (hfourth : m₄ ≤ 2*C*Y^(4-15*θ/8)*E^2) :
    m₂ ≤ Real.sqrt (648*C)*Y^(7/3-θ/2)*E := by
  have hY0 : 0 < Y := by linarith
  have hp : Y^(2/3+θ/8)*Y^(4-15*θ/8) = Y^(14/3-7*θ/4) := by
    rw [← Real.rpow_add hY0]
    congr 1
    ring
  have hs : m₂^2 ≤ 648*C*Y^(14/3-θ)*E^2 := by
    calc
      _ ≤ (324*Y^(2/3+θ/8))*(2*C*Y^(4-15*θ/8)*E^2) :=
        hCS.trans (mul_le_mul_of_nonneg_left hfourth (by positivity))
      _ = 648*C*(Y^(2/3+θ/8)*Y^(4-15*θ/8))*E^2 := by ring
      _ = 648*C*Y^(14/3-7*θ/4)*E^2 := by rw [hp]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg E)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  apply (sq_le_sq₀ hm₂ (by positivity)).mp
  have hp₂ : (Y^(7/3-θ/2))^2 = Y^(14/3-θ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
    congr 1
    ring
  have he : (Real.sqrt (648*C)*Y^(7/3-θ/2)*E)^2 = 648*C*Y^(14/3-θ)*E^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),hp₂]
  exact hs.trans_eq he.symm

/-- The sparse coefficient energy and the primary divisor bound
suffice for the actual balanced mixed-character second moment. -/
theorem primary_balanced_sparse_moment
    (hHuxley : HuxleyAdditiveLargeSieve) {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y E : ℝ), 1 ≤ Y → 0 ≤ E →
      ∀ B : Finset Eisenstein,
      (∀ b ∈ B, primary b ∧ norm b ≤ Y) →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧
        norm p.1 ≤ Y^(1/3+θ/16) ∧ norm p.2 ≤ Y^(1/3+θ/16)) →
      ∀ v : Eisenstein → ℂ, (∑ b ∈ B, ‖v b‖^2) ≤ E*Y^(1-θ) →
      (∑ p ∈ P, ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^2) ≤
        C*Y^(7/3-θ/2)*E := by
  obtain ⟨C,hC,hfourth⟩ := primary_mixed_fourth_moment hHuxley
    (show 0 < θ/16 by positivity)
  refine ⟨Real.sqrt (648*C),Real.sqrt_pos.mpr (by positivity),?_⟩
  intro Y E hY hE B hB P hP v hv
  have hY0 : 0 < Y := by linarith
  have hq : 2/3+θ/8 ≤ 1 := by linarith
  have hQ : 1 ≤ Y^(2/3+θ/8) := Real.one_le_rpow hY (by positivity)
  have hpair : ∀ p ∈ P, PrimarySquarefreePair p ∧
      norm (pairConductor p) ≤ Y^(2/3+θ/8) := by
    intro p hp
    refine ⟨(hP p hp).1,?_⟩
    unfold pairConductor
    rw [norm_mul_eq]
    have h := mul_le_mul (hP p hp).2.1 (hP p hp).2.2 (norm_nonneg _) (by positivity)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [← Real.rpow_add hY0]
    congr 1
    ring
  have hcard : (P.card:ℝ) ≤ 324*Y^(2/3+θ/8) := by
    have h := balanced_pair_card P (by positivity : 0 ≤ Y^(1/3+θ/16))
      (fun p hp => ⟨(hP p hp).1.1,(hP p hp).1.2.1,(hP p hp).2⟩)
    have hp : (Y^(1/3+θ/16))^2 = Y^(2/3+θ/8) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
      congr 1
      ring
    exact h.trans_eq (by rw [hp])
  let f (p : Eisenstein × Eisenstein) := ∑ b ∈ B, v b*mixedCubic p.1 p.2 b
  have hCS : (∑ p ∈ P, ‖f p‖^2)^2 ≤
      (324*Y^(2/3+θ/8))*∑ p ∈ P, ‖f p‖^4 :=
    (second_moment_sq_le_card_fourth P f).trans (mul_le_mul_of_nonneg_right hcard
      (Finset.sum_nonneg (fun _ _ => pow_nonneg (_root_.norm_nonneg _) _)))
  have hf := hfourth (Y^(2/3+θ/8)) Y hQ hY P B hpair hB v
  have hw : (Y^(2/3+θ/8))^(θ/16) ≤ Y^(θ/16) := by
    rw [← Real.rpow_mul hY0.le]
    exact Real.rpow_le_rpow_of_exponent_le hY (by nlinarith)
  have hl : (Y^(2/3+θ/8))^2 ≤ Y^2 := by
    have hbase : Y^(2/3+θ/8) ≤ Y := by
      nth_rw 2 [← Real.rpow_one Y]
      exact Real.rpow_le_rpow_of_exponent_le hY hq
    exact pow_le_pow_left₀ (by positivity) hbase 2
  have he : (Y^(1-θ))^2 = Y^(2-2*θ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
    congr 1
    ring
  have hp : Y^(θ/16)*Y^(2:ℝ)*Y^(θ/16)*Y^(2-2*θ) = Y^(4-15*θ/8) := by
    rw [← Real.rpow_add hY0,← Real.rpow_add hY0,← Real.rpow_add hY0]
    congr 1
    ring
  have hfour : (∑ p ∈ P, ‖f p‖^4) ≤ 2*C*Y^(4-15*θ/8)*E^2 := by
    calc
      _ ≤ C*Y^(θ/16)*(2*Y^2)*Y^(θ/16)*(E*Y^(1-θ))^2 := by
        apply hf.trans
        gcongr
        linarith
      _ = 2*C*(Y^(θ/16)*Y^(2:ℝ)*Y^(θ/16)*Y^(2-2*θ))*E^2 := by
        rw [mul_pow,he,← Real.rpow_two Y]
        ring
      _ = _ := by rw [hp]
  exact balancedPrimary_power hY hθ hC hE
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hCS hfour

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogCutoffEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A power saving for the exact higher-prime-power replacement error.
Both the sparse support and the coefficient amplitude are proved. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primeLogConvolutionError_cutoff_energy {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ), 1 ≤ Y →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, primary a ∧ Y^c < norm a) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      (∑ b ∈ B, ‖primeLogConvolutionError S w b‖^2) ≤
        K*Y^(1-c/16)*(∏ i, M i)^2 := by
  obtain ⟨C,hC,hamp⟩ := primeLogConvolutionError_bound (ι := ι)
    (show 0 < c/32 by positivity)
  obtain ⟨D,hD,hcount⟩ := largePrimePowerSupport_card_bound
  refine ⟨D*C^2,by positivity,?_⟩
  intro S w M Y hY hM hS B hB hBY hw
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  let T := B.filter (fun b => primeLogConvolutionError S w b ≠ 0)
  have hsub : T ⊆ largePrimePowerSupport Y c := fun b hb =>
    primeLogConvolutionError_support_of_norm_le S w hS
      (hBY b (Finset.mem_filter.mp hb).1) (Finset.mem_filter.mp hb).2
  have hcard : (T.card:ℝ) ≤ D*Y^(1-c/8) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount Y c hYp)
  have hsum : (∑ b ∈ T, ‖primeLogConvolutionError S w b‖^2) =
      ∑ b ∈ B, ‖primeLogConvolutionError S w b‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hn
    have hz : primeLogConvolutionError S w b = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hb,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  rw [← hsum]
  have hMp : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  have he : Y^(1-c/8)*(Y^(c/32))^2 = Y^(1-c/16) := by
    rw [← Real.rpow_mul_natCast hYp.le,← Real.rpow_add hYp]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ∑ _b ∈ T, (C*Y^(c/32)*(∏ i, M i))^2 := by
      apply Finset.sum_le_sum
      intro b hb
      have hbB := (Finset.mem_filter.mp hb).1
      have hbS := hB hbB
      have hbY : norm b ≤ Y := hBY b hbB
      exact pow_le_pow_left₀ (_root_.norm_nonneg _)
        (hamp S w M Y (fun i a ha => (hS i a ha).1) hM hw hY b hbS hbY) 2
    _ = (T.card:ℝ)*(C*Y^(c/32)*(∏ i, M i))^2 := by simp
    _ ≤ (D*Y^(1-c/8))*(C*Y^(c/32)*(∏ i, M i))^2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = (D*C^2)*(Y^(1-c/8)*(Y^(c/32))^2)*(∏ i, M i)^2 := by ring
    _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogCutoffMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime-log replacement moments on the actual global norm cutoff. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem primeLogConvolution_balanced_cutoff_moment (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ), 1 ≤ Y →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, primary a ∧ Y^c < norm a) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3+c/256) ∧
        norm p.2 ≤ Y^(1/3+c/256)) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ B, ‖χ b‖ ≤ 1) →
      (∑ p ∈ P, ‖∑ b ∈ B,
        (primeLogConvolutionError S w b*χ b)*mixedCubic p.1 p.2 b‖^2) ≤
        C*(∏ i, M i)^2*Y^(7/3-c/32) := by
  obtain ⟨C,hC,hbound⟩ := primary_balanced_sparse_moment hHuxley
    (show 0 < c/16 by positivity) (show c/16 ≤ 1 by linarith)
  obtain ⟨K,hK,henergy⟩ := primeLogConvolutionError_cutoff_energy (ι := ι) hc
  have h₁ : c/16/16 = c/256 := by ring
  have h₂ : c/16/2 = c/32 := by ring
  simp only [h₁,h₂] at hbound
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro S w M Y hY hM hS B hB hBY hw P hP χ hχ
  have hH : ∀ b ∈ B, primary b ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨orderedPrimarySupport_primary S
      (fun i a ha => (hS i a ha).1) (hB hb),?_⟩
    exact hBY b hb
  have hE : (∑ b ∈ B,
      ‖primeLogConvolutionError S w b*χ b‖^2) ≤
      (K*(∏ i, M i)^2)*Y^(1-c/16) :=
    ((coefficient_twist_energy_le B
      (primeLogConvolutionError S w) χ hχ).trans
      (henergy S w M Y hY hM hS B hB hBY hw)).trans_eq (by ring)
  exact (hbound Y (K*(∏ i, M i)^2) hY (by positivity) B hH P hP
    (fun b => primeLogConvolutionError S w b*χ b) hE).trans_eq (by ring)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateErrors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual prime-indicator replacement errors in the two exceptional regions. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem balanced_primeCoordinateError_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
      (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ (2*Y)^(1/3+c/256) ∧
        norm a.2 ≤ (2*Y)^(1/3+c/256)) →
      (∑ a ∈ P, ‖primeCoordinateError a.1 a.2 q η t W X V Y‖^2) ≤
        C*(∏ i, M i)^2*(2*Y)^(7/3-c/32) := by
  obtain ⟨C,hC,hbound⟩ := primeLogConvolution_balanced_cutoff_moment (ι := ι) hHuxley hc hc₁
  refine ⟨C,hC,?_⟩
  intro q η t W M X V Y hY hq hM hW hWlo hX hV P hP
  have hYp : 0 < 2*Y := by linarith
  have hXpos : ∀ i, 0 < X i := fun i => (Real.rpow_pos_of_pos hYp c).trans (hX i)
  have hS := coordinateSupport_lower W X Y ((2*Y)^c) hWlo hXpos hX
  have hB := coordinateProductCutoff_spec W X Y
  have hh := hbound (coordinateSupport W X Y) (coordinateFactor q η t W X) M (2*Y)
    (by linarith) hM hS (coordinateProductCutoff W X Y) hB.1 hB.2
    (fun i n _ => coordinateFactor_bound q hq η t W X M hW i n) P hP
    (fun z => V (norm z/Y)) (fun z _ => hV _)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  apply Finset.sum_congr rfl
  intro z hz
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorMomentTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact normalized-prime discrepancy transfers second moments to
original prime-indicator convolutions. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeIndicator_moment_transfer {ρ : Type*} (P : Finset ρ)
    (a b : ρ → Eisenstein) (hab : ∀ r ∈ P, primary (a r) ∧ primary (b r))
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    (∑ r ∈ P, ‖primaryPrimeIndicatorTuple (a r) (b r) q η t W X V Y‖^2) ≤
      2*(∑ r ∈ P, ‖primaryNormalizedVonMangoldtTuple (a r) (b r) q η t W X V Y‖^2)+
      2*(∑ r ∈ P, ‖primeCoordinateError (a r) (b r) q η t W X V Y‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  apply norm_square_le_central_tail
  rw [norm_sub_rev,normalized_prime_tuple_difference (a r) (b r)
    (hab r hr).1 (hab r hr).2 q η t W X V hY hV]
  exact le_rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonPrimeIndicatorExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weight-independent exponents for uniform smooth families. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]


 theorem balanced_common_prime_exponents (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → 1 ≤ Real.log Y →
      (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryPrimeIndicatorTuple a.1 a.2 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ₀,hκ₀,hκ₀hi,e,he,hfamily⟩ := balanced_common_normalized_exponents (γ := γ) (ι := ι)
    hpub hHuxley hc V hV hposV hsmV hVlo hVhi hGI hGQ
  obtain ⟨C,hC,herr⟩ := balanced_primeCoordinateError_moment (ι := ι) hHuxley hc hc₁
  let κ := min κ₀ (c/256)
  have hκ : 0 < κ := lt_min hκ₀ (by positivity)
  have hκle : κ ≤ κ₀ := min_le_left _ _
  have hκc : κ ≤ c/256 := min_le_right _ _
  refine ⟨κ,hκ,hκle.trans hκ₀hi,min e (c/32)/2,by positivity,?_⟩
  intro W hW hWlo
  obtain ⟨T₀,hnorm⟩ := hfamily W hW hWlo
  obtain ⟨K,hK,hbound⟩ := hW.norm_bound
  let M : ι → ℝ := fun _ => K
  have hM0 : ∀ i, 0 ≤ M i := fun _ => hK
  let E := C*(∏ i, M i)^2
  obtain ⟨T₁,hT₁,habs⟩ := absorb_prime_coordinate_error_explicit he
    (show 0 < c/32 by positivity) (show 0 ≤ E by dsimp [E]; positivity)
  refine ⟨max T₀ T₁,?_⟩
  intro r Y X q η t P hYT hlog hXlo hXhi hq hη hqY ht hP
  have hM : ∀ i x, ‖W r i x‖ ≤ M i := fun i x => hbound (r,i) x
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans hYT
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans hYT
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hNXlo : ∀ i, Y^c ≤ X i := fun i =>
    (Real.rpow_le_rpow hYp.le (by linarith : Y ≤ 2*Y) hc.le).trans (hXlo i).le
  have hP₀ : ∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ₀) ∧
      norm a.2 ≤ Y^(1/3+κ₀) ∧ Y^(1/1000:ℝ) ≤ norm a.1 := by
    intro a ha
    have hp : Y^(1/3+κ) ≤ Y^(1/3+κ₀) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    exact ⟨(hP a ha).1,(hP a ha).2.1.trans hp,(hP a ha).2.2.1.trans hp,(hP a ha).2.2.2⟩
  have hn := hnorm r Y X q η t P hYT₀ hYp hlog hNXlo hXhi hq hη hqY ht hP₀
  have hd := herr q η t (W r) M X V Y hY1 hq hM0 hM (hWlo r) hXlo hVnorm P
    (fun a ha => balanced_prime_error_rows hY1 hc hκc a (hP a ha))
  have hm := primeIndicator_moment_transfer P Prod.fst Prod.snd
    (fun a ha => ⟨(hP a ha).1.1,(hP a ha).1.2.1⟩) q η t (W r) X V hYp hVhi
  calc
    _ ≤ 2*(∑ a ∈ P, ‖primaryNormalizedVonMangoldtTuple a.1 a.2 q η t (W r) X V Y‖^2)+
        2*(∑ a ∈ P, ‖primeCoordinateError a.1 a.2 q η t (W r) X V Y‖^2) := hm
    _ ≤ 2*Y^(7/3-e)+2*E*(2*Y)^(7/3-c/32) := by dsimp [E]; linarith
    _ ≤ _ := habs Y hYT₁

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting the indicator convolution to genuine primary primes,
followed by the exact squarefree discrepancy. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_primeIndicator (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (b : Eisenstein) :
    orderedConvolution S (fun i n => (primeIndicator n:ℂ)*w i n) b =
      orderedConvolution (fun i => (S i).filter Prime) w b := by
  unfold orderedConvolution
  let T := (Fintype.piFinset S).filter (fun n => (∏ i, n i) = b)
  let U := (Fintype.piFinset (fun i => (S i).filter Prime)).filter (fun n => (∏ i, n i) = b)
  have hsub : U ⊆ T := by
    intro n hn
    obtain ⟨hn,hprod⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i =>
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1),hprod⟩
  have he : (∑ n ∈ U, ∏ i, (primeIndicator (n i):ℂ)*w i (n i)) =
      ∑ n ∈ T, ∏ i, (primeIndicator (n i):ℂ)*w i (n i) := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hex : ∃ i, ¬Prime (n i) := by
      by_contra h
      push Not at h
      have ht := Finset.mem_filter.mp hn
      exact hnot (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr
        (fun i => Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp ht.1 i,h i⟩),ht.2⟩)
    obtain ⟨i,hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [primeIndicator,ite_eq_right hi,Complex.ofReal_zero,zero_mul]
  change (∑ n ∈ T, _) = ∑ n ∈ U, _
  rw [← he]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.prod_congr rfl
  intro i hi
  have hp := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 i)).2
  simp only [primeIndicator,ite_eq_left hp,Complex.ofReal_one,one_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_primary (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    ∀ i, ∀ p ∈ coordinatePrimeSupport W X Y i, primaryPrime p := by
  intro i p hp
  exact ⟨coordinateSupport_primary W X Y i p (Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2⟩

lemma primeIndicatorTuple_eq_prime_convolution (a b : Eisenstein)
    (ha : primary a) (hb : primary b) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    primaryPrimeIndicatorTuple a b q η t W X V Y =
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
        orderedConvolution (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*V (norm z/Y)) := by
  have hp := coordinate_convolution_collection (fun n => (primeIndicator n:ℂ))
    a b ha hb q η t W X V Y
  change primaryPrimeIndicatorTuple a b q η t W X V Y = _ at hp
  rw [hp]
  simp_rw [orderedConvolution_primeIndicator]
  symm
  apply Finset.sum_subset
  · intro z hz
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨n,Fintype.mem_piFinset.mpr (fun i =>
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1),rfl⟩
  · intro z hz hnot
    rw [orderedConvolution_eq_zero_of_not_mem _ _ hnot,zero_mul]

lemma primeIndicator_sub_squarefree (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    primaryPrimeIndicatorTuple a b q η t W X V Y-primarySquarefreePrimeTuple a b q η t W X V Y =
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
        squarefreeConvolutionError (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*V (norm z/Y)) := by
  rw [primeIndicatorTuple_eq_prime_convolution a b ha hb]
  simp only [primarySquarefreePrimeTuple,squarefreeConvolutionError,sub_mul,Finset.sum_sub_distrib]

lemma coordinatePrimeCutoff_spec (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    coordinatePrimeCutoff W X Y ⊆ orderedConvolutionSupport (coordinatePrimeSupport W X Y) ∧
      ∀ b ∈ coordinatePrimeCutoff W X Y, norm b ≤ 2*Y :=
  ⟨Finset.filter_subset _ _,fun _ hb => (Finset.mem_filter.mp hb).2⟩

lemma primeIndicator_sub_squarefree_cutoff (a b : Eisenstein)
    (ha : primary a) (hb : primary b) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryPrimeIndicatorTuple a b q η t W X V Y-primarySquarefreePrimeTuple a b q η t W X V Y =
      ∑ z ∈ coordinatePrimeCutoff W X Y,
        squarefreeConvolutionError (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*V (norm z/Y)) := by
  rw [primeIndicator_sub_squarefree a b ha hb]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hlarge : 2*Y < norm z := lt_of_not_ge (fun h => hnot (Finset.mem_filter.mpr ⟨hz,h⟩))
  have hv := hV (norm z/Y) ((lt_div_iff₀ hY).mpr hlarge)
  rw [hv,mul_zero,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RepeatedPrimeCutoffEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated-prime energy on the actual global norm cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma convolutionError_mem_largeSquareSupport_of_norm
    (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ) (Y D : ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p)
    {b : Eisenstein} (hbY : norm b ≤ Y) (hb : squarefreeConvolutionError S w b ≠ 0) :
    b ∈ largeSquareSupport Y D := by
  have hns : ¬Squarefree b := by
    intro hs
    simp [squarefreeConvolutionError,squarefreeConvolution,hs] at hb
  have ho : orderedConvolution S w b ≠ 0 := by
    simpa only [squarefreeConvolutionError,squarefreeConvolution,ite_eq_right hns,sub_zero] using hb
  obtain ⟨f,hf,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero ho
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  have hprime : ∀ i, primaryPrime (f i) :=
    fun i => (hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)).1
  have hnot : ¬Function.Injective f := by
    intro hi
    exact hns (hfb ▸ (squarefree_prime_tuple_iff f hprime).mpr hi)
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hnot
  have hdvd : (f i)^2 ∣ ∏ k, f k := by
    have h := Finset.prod_dvd_prod_of_subset ({i,j}:Finset ι) Finset.univ f
      (Finset.subset_univ _)
    simpa [hne,hij,pow_two] using h
  have hprod0 : (∏ i, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => (hprime i).2.ne_zero)
  apply Finset.mem_filter.mpr
  refine ⟨mem_nonzeroNormBall.mpr ⟨?_,?_⟩,f i,?_,?_⟩
  · exact hbY
  · exact hfb ▸ hprod0
  · exact (hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)).2
  · exact hfb ▸ hdvd

private theorem convolutionError_cutoff_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (Y D E : ℝ),
      0 ≤ Y → 0 < D → 0 ≤ E →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ b ∈ B, ‖squarefreeConvolutionError S w b‖ ≤ E) →
      (∑ b ∈ B, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y*D^(-(1/2:ℝ))*E^2 := by
  obtain ⟨C,hC,hcount⟩ := largeSquareSupport_card_bound
  refine ⟨C,hC,?_⟩
  intro S w Y D E hY hD hE hS B hB hBY hbound
  let T := B.filter (fun b => squarefreeConvolutionError S w b ≠ 0)
  have hsub : T ⊆ largeSquareSupport Y D := by
    intro b hb
    exact convolutionError_mem_largeSquareSupport_of_norm S w Y D hS
      (hBY b (Finset.mem_filter.mp hb).1) (Finset.mem_filter.mp hb).2
  have hcard : (T.card:ℝ) ≤ C*Y*D^(-(1/2:ℝ)) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount Y D hY hD)
  have heq : (∑ b ∈ T, ‖squarefreeConvolutionError S w b‖^2) =
      ∑ b ∈ B, ‖squarefreeConvolutionError S w b‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hnot
    have hz : squarefreeConvolutionError S w b = 0 := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨hb,hn⟩)
    simp [hz]
  rw [← heq]
  calc
    _ ≤ ∑ _b ∈ T, E^2 := by
      apply Finset.sum_le_sum
      intro b hb
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) (hbound b (Finset.mem_filter.mp hb).1) 2
    _ = (T.card:ℝ)*E^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg E)

theorem primeConvolutionError_cutoff_power_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y c : ℝ),
      0 < Y → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ Y^c < norm p) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      (∑ b ∈ B, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y^(1-c/2)*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  obtain ⟨C,hC,hbound⟩ := convolutionError_cutoff_energy_bound (ι := ι)
  refine ⟨C,hC,?_⟩
  intro S w M Y c hY hM hS B hB hBY hw
  have hA : 0 ≤ ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))
  have hh := hbound S w Y (Y^c) _ hY.le (Real.rpow_pos_of_pos hY _) hA
    hS B hB hBY (fun b _ => convolutionError_norm_bound S w M
      (fun i p hp => (hS i p hp).1) hM hw b)
  have he : C*Y*(Y^c)^(-(1/2:ℝ)) = C*Y^(1-c/2) := by
    rw [← Real.rpow_mul hY.le]
    nth_rw 1 [← Real.rpow_one Y]
    rw [mul_assoc,← Real.rpow_add hY]
    congr 2
    ring
  simpa only [he] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RepeatedPrimeCutoffMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The repeated-prime replacement moments on the actual global norm cutoff. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem repeatedPrime_balanced_cutoff_moment (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ), 1 ≤ Y →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, primaryPrime a ∧ Y^c < norm a) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3+c/32) ∧
        norm p.2 ≤ Y^(1/3+c/32)) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ B, ‖χ b‖ ≤ 1) →
      (∑ p ∈ P, ‖∑ b ∈ B,
        (squarefreeConvolutionError S w b*χ b)*mixedCubic p.1 p.2 b‖^2) ≤
        C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2*Y^(7/3-c/4) := by
  obtain ⟨C,hC,hbound⟩ := primary_balanced_sparse_moment hHuxley
    (show 0 < c/2 by positivity) (show c/2 ≤ 1 by linarith)
  obtain ⟨K,hK,henergy⟩ := primeConvolutionError_cutoff_power_energy (ι := ι)
  have h₁ : c/2/16 = c/32 := by ring
  have h₂ : c/2/2 = c/4 := by ring
  simp only [h₁,h₂] at hbound
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro S w M Y hY hM hS B hB hBY hw P hP χ hχ
  have hH : ∀ b ∈ B, primary b ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨orderedPrimarySupport_primary S
      (fun i a ha => (hS i a ha).1.1) (hB hb),?_⟩
    exact hBY b hb
  have hE : (∑ b ∈ B,
      ‖squarefreeConvolutionError S w b*χ b‖^2) ≤
      (K*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2)*Y^(1-c/2) :=
    ((coefficient_twist_energy_le B
      (squarefreeConvolutionError S w) χ hχ).trans
      (henergy S w M Y c (by linarith) hM hS B hB hBY hw)).trans_eq (by ring)
  exact (hbound Y (K*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2) hY (by positivity) B hH P hP
    (fun b => squarefreeConvolutionError S w b*χ b) hE).trans_eq (by ring)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeCoordinateErrors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual squarefree replacement errors in the two exceptional regions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem balanced_squarefreeCoordinateError_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
      (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ (2*Y)^(1/3+c/32) ∧
        norm a.2 ≤ (2*Y)^(1/3+c/32)) →
      (∑ a ∈ P, ‖squarefreeCoordinateError a.1 a.2 q η t W X V Y‖^2) ≤
        C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2*(2*Y)^(7/3-c/4) := by
  obtain ⟨C,hC,hbound⟩ := repeatedPrime_balanced_cutoff_moment (ι := ι) hHuxley hc hc₁
  refine ⟨C,hC,?_⟩
  intro q η t W M X V Y hY hq hM hW hWlo hX hV P hP
  have hYp : 0 < 2*Y := by linarith
  have hXpos : ∀ i, 0 < X i := fun i => (Real.rpow_pos_of_pos hYp c).trans (hX i)
  have hS : ∀ i, ∀ p ∈ coordinatePrimeSupport W X Y i,
      primaryPrime p ∧ (2*Y)^c < norm p := by
    intro i p hp
    exact ⟨coordinatePrimeSupport_primary W X Y i p hp,
      (coordinateSupport_lower W X Y ((2*Y)^c) hWlo hXpos hX i p
        (Finset.mem_filter.mp hp).1).2⟩
  have hB := coordinatePrimeCutoff_spec W X Y
  have hh := hbound (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) M (2*Y)
    (by linarith) hM hS (coordinatePrimeCutoff W X Y) hB.1 hB.2
    (fun i n _ => coordinateFactor_bound q hq η t W X M hW i n) P hP
    (fun z => V (norm z/Y)) (fun z _ => hV _)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  apply Finset.sum_congr rfl
  intro z hz
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeMomentTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact squarefree discrepancy transfers prime moments to
the squarefree coefficient in the manuscript. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma squarefreePrime_moment_transfer {ρ : Type*} (P : Finset ρ)
    (a b : ρ → Eisenstein) (hab : ∀ r ∈ P, primary (a r) ∧ primary (b r))
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    (∑ r ∈ P, ‖primarySquarefreePrimeTuple (a r) (b r) q η t W X V Y‖^2) ≤
      2*(∑ r ∈ P, ‖primaryPrimeIndicatorTuple (a r) (b r) q η t W X V Y‖^2)+
      2*(∑ r ∈ P, ‖squarefreeCoordinateError (a r) (b r) q η t W X V Y‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  apply norm_square_le_central_tail
  rw [norm_sub_rev,primeIndicator_sub_squarefree_cutoff (a r) (b r)
    (hab r hr).1 (hab r hr).2 q η t W X V hY hV]
  exact le_rfl

lemma balanced_squarefree_error_rows {Y κ c : ℝ} (hY : 1 ≤ Y) (hc : 0 < c)
    (hκ : κ ≤ c/256) (a : Eisenstein × Eisenstein)
    (ha : PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
      norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) :
    PrimarySquarefreePair a ∧ norm a.1 ≤ (2*Y)^(1/3+c/32) ∧
      norm a.2 ≤ (2*Y)^(1/3+c/32) := by
  have hp := balanced_prime_error_rows hY hc hκ a ha
  have he : (2*Y)^(1/3+c/256) ≤ (2*Y)^(1/3+c/32) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  exact ⟨hp.1,hp.2.1.trans he,hp.2.2.trans he⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonSquarefreePrimeExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weight-independent exponents for uniform smooth families. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]


 theorem balanced_common_squarefree_exponents (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → 1 ≤ Real.log Y →
      (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primarySquarefreePrimeTuple a.1 a.2 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ₀,hκ₀,hκ₀hi,e,he,hfamily⟩ := balanced_common_prime_exponents (γ := γ) (ι := ι)
    hpub hHuxley hc hc₁ V hV hposV hsmV hVlo hVhi hVnorm hGI hGQ
  obtain ⟨C,hC,herr⟩ := balanced_squarefreeCoordinateError_moment (ι := ι) hHuxley hc hc₁
  let κ := min κ₀ (c/256)
  have hκ : 0 < κ := lt_min hκ₀ (by positivity)
  have hκle : κ ≤ κ₀ := min_le_left _ _
  have hκc : κ ≤ c/256 := min_le_right _ _
  refine ⟨κ,hκ,hκle.trans hκ₀hi,min e (c/4)/2,by positivity,?_⟩
  intro W hW hWlo
  obtain ⟨T₀,hnorm⟩ := hfamily W hW hWlo
  obtain ⟨K,hK,hbound⟩ := hW.norm_bound
  let M : ι → ℝ := fun _ => K
  have hM0 : ∀ i, 0 ≤ M i := fun _ => hK
  let E := C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2
  obtain ⟨T₁,hT₁,habs⟩ := absorb_prime_coordinate_error_explicit he
    (show 0 < c/4 by positivity) (show 0 ≤ E by dsimp [E]; positivity)
  refine ⟨max T₀ T₁,?_⟩
  intro r Y X q η t P hYT hlog hXlo hXhi hq hη hqY ht hP
  have hM : ∀ i x, ‖W r i x‖ ≤ M i := fun i x => hbound (r,i) x
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans hYT
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans hYT
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hP₀ : ∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ₀) ∧
      norm a.2 ≤ Y^(1/3+κ₀) ∧ Y^(1/1000:ℝ) ≤ norm a.1 := by
    intro a ha
    have hp : Y^(1/3+κ) ≤ Y^(1/3+κ₀) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    exact ⟨(hP a ha).1,(hP a ha).2.1.trans hp,(hP a ha).2.2.1.trans hp,(hP a ha).2.2.2⟩
  have hn := hnorm r Y X q η t P hYT₀ hlog hXlo hXhi hq hη hqY ht hP₀
  have hd := herr q η t (W r) M X V Y hY1 hq hM0 hM (hWlo r) hXlo hVnorm P
    (fun a ha => balanced_squarefree_error_rows hY1 hc hκc a (hP a ha))
  have hm := squarefreePrime_moment_transfer P Prod.fst Prod.snd
    (fun a ha => ⟨(hP a ha).1.1,(hP a ha).1.2.1⟩) q η t (W r) X V hYp hVhi
  calc
    _ ≤ 2*(∑ a ∈ P, ‖primaryPrimeIndicatorTuple a.1 a.2 q η t (W r) X V Y‖^2)+
        2*(∑ a ∈ P, ‖squarefreeCoordinateError a.1 a.2 q η t (W r) X V Y‖^2) := hm
    _ ≤ 2*Y^(7/3-e)+2*E*(2*Y)^(7/3-c/4) := by dsimp [E]; linarith
    _ ≤ _ := habs Y hYT₁

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicNumeratorCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite numerator character needed for arbitrary v in the
exceptional moments. The only conditional input here is the periodicity
consequence of cubic reciprocity and the unit/ramified supplementary laws:
Dunn–Radziwiłł (2024), equations (1.4)–(1.5). -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicNumeratorLift_unit (v : Eisenstein) {x : Eisenstein} (hx : IsUnit x) :
    cubicNumeratorLift v x = 1 := by
  rw [cubicNumeratorLift,ite_eq_left (hx.map (Ideal.Quotient.mk (modulus 3))),
    primaryNormalize_unit hx,cubicSymbol_one_lower]

lemma cubicNumeratorChar_units (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (u : Eisensteinˣ) :
    cubicNumeratorChar hpub v hv (Ideal.Quotient.mk (modulus (9*v)) u) = 1 := by
  rw [cubicNumeratorChar_mk,cubicNumeratorLift_unit v u.isUnit]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeTwists
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplicative twists of the manuscript's squarefree prime coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_mul_character (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (χ : Eisenstein →* ℂ) (z : Eisenstein) :
    orderedConvolution S (fun i n => w i n*χ n) z = orderedConvolution S w z*χ z := by
  unfold orderedConvolution
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.prod_mul_distrib,← map_prod, (Finset.mem_filter.mp hn).2]

lemma squarefreeConvolution_mul_character (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (χ : Eisenstein →* ℂ) (z : Eisenstein) :
    squarefreeConvolution S (fun i n => w i n*χ n) z = squarefreeConvolution S w z*χ z := by
  by_cases hs : Squarefree z
  · simp only [squarefreeConvolution,ite_eq_left hs,orderedConvolution_mul_character]
  · simp only [squarefreeConvolution,ite_eq_right hs,zero_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinateFactor_product_character (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (r : Eisenstein) (ψ : MulChar (Residues r) ℂ)
    (i : ι) (n : Eisenstein) :
    coordinateFactor (fun i => q i*r) (fun i => productResidueChar (η i) ψ) t W X i n =
      coordinateFactor q η t W X i n*ψ (Ideal.Quotient.mk (modulus r) n) := by
  simp only [coordinateFactor,productResidueChar_mk]
  ring

lemma squarefreePrimeTuple_product_character (a b : Eisenstein)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ)
    (r : Eisenstein) (ψ : MulChar (Residues r) ℂ) :
    primarySquarefreePrimeTuple a b (fun i => q i*r)
      (fun i => productResidueChar (η i) ψ) t W X V Y =
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
        squarefreeConvolution (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*ψ (Ideal.Quotient.mk (modulus r) z)*V (norm z/Y)) := by
  unfold primarySquarefreePrimeTuple
  apply Finset.sum_congr rfl
  intro z hz
  have hf : coordinateFactor (fun i => q i*r)
      (fun i => productResidueChar (η i) ψ) t W X =
      fun i n => coordinateFactor q η t W X i n*ψ (Ideal.Quotient.mk (modulus r) n) := by
    funext i n
    exact coordinateFactor_product_character q η t W X r ψ i n
  rw [hf]
  let χ : Eisenstein →* ℂ := ψ.toMonoidHom.comp (Ideal.Quotient.mk (modulus r)).toMonoidHom
  change squarefreeConvolution _ (fun i n => coordinateFactor q η t W X i n*χ n) z*_
    = _
  rw [squarefreeConvolution_mul_character]
  change (_*ψ (Ideal.Quotient.mk (modulus r) z))*_ = _
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeMomentCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the structured moment with the original
squarefree ordered-prime coefficient, including numerator and exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mellinPhase_norm_prod {α : Type*} (S : Finset α) (f : α → Eisenstein)
    (u : ℝ) (hf : ∀ i ∈ S, f i ≠ 0) :
    mellinPhase u (norm (∏ i ∈ S, f i)) = ∏ i ∈ S, mellinPhase u (norm (f i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [mellinPhase,norm]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,← normTwist_eq_mellinPhase,
      normTwist_mul u (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      normTwist_eq_mellinPhase,normTwist_eq_mellinPhase,
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma orderedConvolution_norm_twist (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ n ∈ S i, n ≠ 0) (w : ι → Eisenstein → ℂ) (u : ℝ) (z : Eisenstein) :
    orderedConvolution S (fun i n => w i n*mellinPhase u (norm n)) z =
      orderedConvolution S w z*mellinPhase u (norm z) := by
  unfold orderedConvolution
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.prod_mul_distrib,← mellinPhase_norm_prod Finset.univ n u
    (fun i _ => hS i (n i) (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 i)),
    (Finset.mem_filter.mp hn).2]

lemma squarefreeConvolution_norm_twist (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ n ∈ S i, n ≠ 0) (w : ι → Eisenstein → ℂ) (u : ℝ) (z : Eisenstein) :
    squarefreeConvolution S (fun i n => w i n*mellinPhase u (norm n)) z =
      squarefreeConvolution S w z*mellinPhase u (norm z) := by
  by_cases hs : Squarefree z
  · simp only [squarefreeConvolution,ite_eq_left hs,orderedConvolution_norm_twist S hS]
  · simp only [squarefreeConvolution,ite_eq_right hs,zero_mul]

lemma mixedCubic_numerator {a b z : Eisenstein} (ha : primary a) (hb : primary b)
    (hz : primary z) : mixedCubic a b z = cubicSymbol z (a*b^2) := by
  rw [mixedCubic,cubic_reciprocity ha hz,cubic_reciprocity hb hz,
    pow_two,cubicSymbol_mul_upper hz,cubicSymbol_mul_upper hz,← cubicSymbol_sq_eq_star hz]
  ring

lemma principal_residue_value (e z : Eisenstein) :
    (1 : MulChar (Residues e) ℂ) (Ideal.Quotient.mk (modulus e) z) =
      if IsCoprime z e then 1 else 0 := by
  by_cases hc : IsCoprime z e
  · rw [ite_eq_left hc,MulChar.one_apply (residue_isUnit_of_isCoprime hc.symm)]
  · rw [ite_eq_right hc]
    exact MulChar.map_nonunit _ (fun h => hc (isCoprime_of_residue_isUnit h).symm)

/-- The literal numerator and excluded-prime factors are assembled into
one explicitly constructed finite character of modulus 9ve. -/
lemma structuredPrimeMoment_eq_tuple (hpub : CubicSupplementaryPeriodicity)
    (a b v e : Eisenstein) (ha : primary a) (hb : primary b) (hv : v ≠ 0)
    (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    structuredPrimeMoment a b v e u W X V Y =
      primarySquarefreePrimeTuple a b (fun _ : ι => 1*((9*v)*e))
        (fun _ => productResidueChar (1 : MulChar (Residues (1:Eisenstein)) ℂ)
          (productResidueChar (cubicNumeratorChar hpub v hv) (1 : MulChar (Residues e) ℂ)))
        (fun _ => u) W X V Y := by
  rw [squarefreePrimeTuple_product_character]
  have hf : coordinateFactor (fun _ : ι => 1) (fun _ => 1) (fun _ => u) W X =
      fun i n => W i (norm n/X i)*mellinPhase u (norm n) := by
    funext i n
    simp only [coordinateFactor,MulChar.one_apply (residue_isUnit_of_isCoprime isCoprime_one_left),mul_one]
  rw [hf,structuredPrimeMoment,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have hzprim := orderedPrimarySupport_primary (coordinatePrimeSupport W X Y)
    (fun i n hn => (coordinatePrimeSupport_primary W X Y i n hn).1) hz
  rw [squarefreeConvolution_norm_twist _
    (fun i n hn => (coordinatePrimeSupport_primary W X Y i n hn).2.ne_zero),
    productResidueChar_mk,cubicNumeratorChar_primary hpub v hv hzprim,principal_residue_value]
  by_cases hcop : IsCoprime z e
  · rw [ite_eq_left hcop,ite_eq_left hcop,mul_one,mixedCubic_numerator ha hb hzprim,
      cubicSymbol_mul_upper hzprim]
    simp only [cubicSymbol_mul_upper hzprim]
    unfold primeMomentCoefficient
    ring
  · simp only [ite_eq_right hcop,mul_zero,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMomentTwists
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact modulus and unit condition for the numerator/exclusion twist. -/
noncomputable section
namespace CubicFirstMoment

lemma structuredTwistModulus_ne_zero {v e : Eisenstein} (hv : v ≠ 0) (he : e ≠ 0) :
    structuredTwistModulus v e ≠ 0 := by
  exact mul_ne_zero one_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hv) he)

lemma structuredTwistCharacter_units (hpub : CubicSupplementaryPeriodicity)
    (v e : Eisenstein) (hv : v ≠ 0) (u : Eisensteinˣ) :
    structuredTwistCharacter hpub v e hv
      (Ideal.Quotient.mk (modulus (structuredTwistModulus v e)) u) = 1 := by
  apply productResidueChar_units
  · intro w
    exact MulChar.one_apply (w.isUnit.map (Ideal.Quotient.mk (modulus (1:Eisenstein))))
  · intro w
    apply productResidueChar_units
    · exact cubicNumeratorChar_units hpub v hv
    · intro w
      exact MulChar.one_apply (w.isUnit.map (Ideal.Quotient.mk (modulus e)))

lemma structuredTwistModulus_bound {Y δ d : ℝ} (hY : 1 ≤ Y) (hd : 3*δ ≤ d)
    (h81 : 81 ≤ Y^δ) {v e : Eisenstein} (hv : norm v ≤ Y^δ) (he : norm e ≤ Y^δ) :
    norm (structuredTwistModulus v e) ≤ Y^d := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have h9 : norm (9:Eisenstein) = 81 := by
    change Complex.normSq (9:ℂ) = 81
    norm_num
  calc
    norm (structuredTwistModulus v e) = 81*(norm v*norm e) := by
      simp only [structuredTwistModulus,one_mul,norm_mul_eq,h9]
      ring
    _ ≤ 81*(Y^δ*Y^δ) := by gcongr; exact norm_nonneg e
    _ ≤ Y^δ*(Y^δ*Y^δ) := by gcongr
    _ = Y^(3*δ) := by rw [← Real.rpow_add hYp,← Real.rpow_add hYp]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY hd

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonBalancedStructuredMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal structured character moment, with numerator v and
coprimality exclusion e, for fixed smooth coordinate weights. -/
noncomputable section
open Set Filter
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem balanced_common_structured_exponents (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y : ℝ) (X : ι → ℝ) (v e : Eisenstein) (u : ℝ)
        (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → 1 ≤ Real.log Y →
      (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → v ≠ 0 → e ≠ 0 →
      norm v ≤ Y^δ → norm e ≤ Y^δ → |u| ≤ Y^(721/2000:ℝ) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+δ) ∧
        norm a.2 ≤ Y^(1/3+δ) ∧ Y^(1/3-δ) ≤ norm a.1) →
      (∑ a ∈ P, ‖structuredPrimeMoment a.1 a.2 v e u (W r) X V Y‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,hfamily⟩ := balanced_common_squarefree_exponents (γ := γ) (ι := ι)
    hpub hHuxley hc hc₁ V hV hposV hsmV hVlo hVhi hVnorm hGI hGQ
  let δ := min κ (1/100000)/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδκ : δ ≤ κ := by dsimp [δ]; linarith [min_le_left κ (1/100000)]
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hδ).eventually_ge_atTop (81:ℝ))
  refine ⟨δ,hδ,hδκ.trans hκhi,ε,hε,?_⟩
  intro W hW hWlo
  obtain ⟨T₀,hraw⟩ := hfamily W hW hWlo
  refine ⟨max 1 (max T₀ T₁),?_⟩
  intro r Y X v e u P hYT hlog hXlo hXhi hv he hvY heY hu hP
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hYT
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hYT)
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hYT)
  have hq : ∀ _i : ι, structuredTwistModulus v e ≠ 0 :=
    fun _ => structuredTwistModulus_ne_zero hv he
  have hqY : ∀ _i : ι, norm (structuredTwistModulus v e) ≤ Y^(1/100000:ℝ) := fun _ =>
    structuredTwistModulus_bound hY1 (by dsimp [δ]; linarith [min_le_right κ (1/100000)]) (hT₁ Y hYT₁) hvY heY
  have hPκ : ∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
      norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1 := by
    intro a ha
    have hupp : Y^(1/3+δ) ≤ Y^(1/3+κ) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    have hlo : Y^(1/1000:ℝ) ≤ Y^(1/3-δ) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    exact ⟨(hP a ha).1,(hP a ha).2.1.trans hupp,(hP a ha).2.2.1.trans hupp,
      hlo.trans (hP a ha).2.2.2⟩
  have hh := hraw r Y X (fun _ => structuredTwistModulus v e)
    (fun _ => structuredTwistCharacter hperiod v e hv) (fun _ => u) P hYT₀ hlog hXlo hXhi hq
    (fun _ => structuredTwistCharacter_units hperiod v e hv) hqY (fun _ => hu) hPκ
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a ha
  rw [structuredPrimeMoment_eq_tuple hperiod a.1 a.2 v e (hP a ha).1.1 (hP a ha).1.2.1 hv u (W r) X V Y]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredWeightScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scaling of the original structured prime weights. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_mul_weights (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (c : ι → ℂ) (z : Eisenstein) :
    orderedConvolution S (fun i n => c i*w i n) z =
      (∏ i, c i)*orderedConvolution S w z := by
  unfold orderedConvolution
  simp_rw [Finset.prod_mul_distrib]
  rw [Finset.mul_sum]

lemma squarefreeConvolution_mul_weights (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (c : ι → ℂ) (z : Eisenstein) :
    squarefreeConvolution S (fun i n => c i*w i n) z =
      (∏ i, c i)*squarefreeConvolution S w z := by
  by_cases hz : Squarefree z
  · simp only [squarefreeConvolution,ite_eq_left hz,orderedConvolution_mul_weights]
  · simp only [squarefreeConvolution,ite_eq_right hz,mul_zero]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_mul_weights (W : ι → ℝ → ℂ) (c : ι → ℂ)
    (hc : ∀ i, c i ≠ 0) (X : ι → ℝ) (Y : ℝ) :
    coordinatePrimeSupport (fun i x => c i*W i x) X Y = coordinatePrimeSupport W X Y := by
  funext i
  ext n
  simp only [coordinatePrimeSupport,coordinateSupport,Finset.mem_filter,mul_ne_zero_iff]
  tauto

lemma structuredPrimeMoment_mul_weights (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0)
    (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    structuredPrimeMoment a b v e u (fun i x => c i*W i x) X V Y =
      (∏ i, c i)*structuredPrimeMoment a b v e u W X V Y := by
  unfold structuredPrimeMoment primeMomentCoefficient
  rw [coordinatePrimeSupport_mul_weights W c hc]
  simp_rw [squarefreeConvolution_mul_weights]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

lemma structuredPrimeMoment_log_scaling_base (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Z : ℝ) {Y : ℝ} (hY : 0 < Y) (s : ℝ) :
    structuredPrimeMoment a b v e u W X V Z =
      ((Y^(s*(Fintype.card ι:ℝ)):ℝ):ℂ)*
        structuredPrimeMoment a b v e u (fun i x => ((Y^(-s):ℝ):ℂ)*W i x) X V Z := by
  have hw : (fun i x => ((Y^s:ℝ):ℂ)*(((Y^(-s):ℝ):ℂ)*W i x)) = W := by
    funext i x
    rw [← mul_assoc,← Complex.ofReal_mul,← Real.rpow_add hY]
    simp
  have h := structuredPrimeMoment_mul_weights a b v e u
    (fun i x => ((Y^(-s):ℝ):ℂ)*W i x) (fun _ => ((Y^s:ℝ):ℂ))
    (fun _ => Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hY s).ne') X V Z
  rw [hw] at h
  simpa only [Finset.prod_const,Finset.card_univ,← Complex.ofReal_pow,
    ← Real.rpow_natCast,← Real.rpow_mul hY.le] using h

lemma normalized_energy_transfer {α : Type*} (S : Finset α)
    (f g : α → ℂ) {Y e d : ℝ} (hY : 1 ≤ Y)
    (hscale : ∀ i ∈ S, f i = ((Y^d:ℝ):ℂ)*g i)
    (hbound : (∑ i ∈ S, ‖g i‖^2) ≤ Y^(7/3-e)) (hd : 2*d ≤ e/2) :
    (∑ i ∈ S, ‖f i‖^2) ≤ Y^(7/3-e/2) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  calc
    _ = Y^(2*d)*(∑ i ∈ S, ‖g i‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hscale i hi,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hYp.le _),mul_pow,
        ← Real.rpow_natCast,← Real.rpow_mul hYp.le]
      congr 2
      ring
    _ ≤ Y^(2*d)*Y^(7/3-e) := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hYp.le _)
    _ = Y^(2*d+(7/3-e)) := (Real.rpow_add hYp _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY (by linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedScaledStructuredMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balanced structured moments on finitely many fixed output scales,
with the original logarithmically varying coordinate weights retained. -/
noncomputable section
open Set Filter
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ']

theorem balanced_scaled_structured_moment (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (σ : κ' → ℝ) (hσ : ∀ k, 0 < σ k)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ T : ℝ,
      ∀ (r : γ) (X : ι → ℝ) (v e : Eisenstein) (u : ℝ) (P : Finset (Eisenstein × Eisenstein)),
      T ≤ L r →
      (∀ i, (2*L r)^c < X i) → (∀ i, X i ≤ L r) → v ≠ 0 → e ≠ 0 →
      norm v ≤ (L r)^δ → norm e ≤ (L r)^δ → |u| ≤ (L r)^(9/25:ℝ) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ (L r)^(1/3+δ) ∧
        norm a.2 ≤ (L r)^(1/3+δ) ∧ (L r)^(1/3-δ) ≤ norm a.1) →
      ∀ k, (∑ a ∈ P, ‖structuredPrimeMoment a.1 a.2 v e u (W r) X V (σ k*L r)‖^2) ≤ (L r)^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,hraw⟩ := balanced_common_structured_exponents
    (γ := γ) (ι := ι) hpub hHuxley hperiod (c := c/2) (by positivity) (by linarith)
    V hV hposV hsmV hVlo hVhi hVnorm hGI hGQ
  refine ⟨κ/2,by positivity,by linarith,ε/4,by positivity,?_⟩
  intro L W hL hW hWlo
  let s := ε/(16*((Fintype.card ι:ℝ)+1))
  have hs : 0 < s := by dsimp [s]; positivity
  let U : γ → ι → ℝ → ℂ := fun r i x => ((L r^(-s):ℝ):ℂ)*W r i x
  have hU : UniformLogWeights (fun z : γ × ι => U z.1 z.2) := by
    have heq : (fun z : γ × ι => U z.1 z.2) =
        normalizedLogWeight (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) s := by
      funext z x
      simp only [U,normalizedLogWeight,Complex.real_smul]
    rw [heq]
    exact hW.normalize hs
  obtain ⟨T₀,hbound⟩ := hraw U hU (fun r i x hx => by simp only [U,hWlo r i x hx,mul_zero])
  obtain ⟨T,hdata⟩ := eventually_atTop.mp (eventually_all.mpr (fun k =>
    eventually_fixed_scale_moment_bounds (hσ k) hκ hc hε T₀))
  have hsd : 2*(s*(Fintype.card ι:ℝ)) ≤ (ε/2)/2 := by
    have heq : s*(16*((Fintype.card ι:ℝ)+1)) = ε := by dsimp [s]; field_simp
    nlinarith
  refine ⟨max 1 T,?_⟩
  intro r X v e u P hT hXlo hXhi hv he hvY heY hu hP k
  have hY1 : 1 ≤ L r := hL r
  have hYp : 0 < L r := zero_lt_one.trans_le hY1
  have hd := hdata (L r) ((le_max_right _ _).trans hT) k
  have hrows : ∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ (σ k*L r)^(1/3+κ) ∧
      norm a.2 ≤ (σ k*L r)^(1/3+κ) ∧ (σ k*L r)^(1/3-κ) ≤ norm a.1 := by
    intro a ha
    exact ⟨(hP a ha).1,(hP a ha).2.1.trans hd.balanced_window.2,
      (hP a ha).2.2.1.trans hd.balanced_window.2,hd.balanced_window.1.trans (hP a ha).2.2.2⟩
  have hb := hbound r (σ k*L r) X v e u P hd.threshold hd.log_bound
    (fun i => hd.lower_bound.trans_lt (hXlo i)) (fun i => (hXhi i).trans hd.upper_bound)
    hv he (hvY.trans hd.small_bound) (heY.trans hd.small_bound)
    (hu.trans hd.height_bound) hrows
  have hh := normalized_energy_transfer P
    (fun z => structuredPrimeMoment z.1 z.2 v e u (W r) X V (σ k*L r))
    (fun z => structuredPrimeMoment z.1 z.2 v e u (U r) X V (σ k*L r)) hY1
    (fun z _ => structuredPrimeMoment_log_scaling_base z.1 z.2 v e u (W r) X V
      (σ k*L r) hYp s) (hb.trans hd.saving_bound) hsd
  have heq : ε/2/2 = ε/4 := by ring
  simpa only [heq] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredCutoffConsistency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The factor cutoff may be moved to the current output dyad. It does
not impose a new condition on a product whose norm is already in that dyad. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_filter_norm (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {z : Eisenstein} {R : ℝ}
    (hz : z ≠ 0) (hR : norm z ≤ R) :
    orderedConvolution (fun i => (S i).filter (fun n => norm n ≤ R)) w z =
      orderedConvolution S w z := by
  have heq : (Fintype.piFinset (fun i => (S i).filter (fun n => norm n ≤ R))).filter
      (fun n => (∏ i, n i) = z) =
      (Fintype.piFinset S).filter (fun n => (∏ i, n i) = z) := by
    ext n
    simp only [Finset.mem_filter,Fintype.mem_piFinset]
    constructor
    · rintro ⟨hn,hprod⟩
      exact ⟨fun i => (hn i).1,hprod⟩
    · rintro ⟨hn,hprod⟩
      refine ⟨fun i => ⟨hn i,?_⟩,hprod⟩
      apply (norm_le_of_dvd hz ?_).trans hR
      rw [← hprod]
      exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  unfold orderedConvolution
  rw [heq]

lemma squarefreeConvolution_filter_norm (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {z : Eisenstein} {R : ℝ}
    (hz : z ≠ 0) (hR : norm z ≤ R) :
    squarefreeConvolution (fun i => (S i).filter (fun n => norm n ≤ R)) w z =
      squarefreeConvolution S w z := by
  unfold squarefreeConvolution
  rw [orderedConvolution_filter_norm S w hz hR]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_trim (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    coordinatePrimeSupport W X Y =
      fun i => (coordinatePrimeSupport W X Z i).filter (fun n => norm n ≤ 2*Y) := by
  funext i
  ext n
  simp only [coordinatePrimeSupport,coordinateSupport,Finset.mem_filter,mem_primaryElementBall]
  constructor
  · rintro ⟨⟨⟨hp,hY⟩,hw⟩,hq⟩
    exact ⟨⟨⟨⟨hp,by linarith⟩,hw⟩,hq⟩,hY⟩
  · rintro ⟨⟨⟨⟨hp,_⟩,hw⟩,hq⟩,hY⟩
    exact ⟨⟨⟨hp,hY⟩,hw⟩,hq⟩

lemma primeMomentCoefficient_dyad_consistent (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {Y Z : ℝ} (hYZ : Y ≤ Z) {z : Eisenstein} (hz : z ≠ 0) (hN : norm z ≤ 2*Y) :
    primeMomentCoefficient W X Y z = primeMomentCoefficient W X Z z := by
  unfold primeMomentCoefficient
  rw [coordinatePrimeSupport_trim W X hYZ,squarefreeConvolution_filter_norm _ _ hz hN]

lemma orderedSupport_filter_norm (S : ι → Finset Eisenstein)
    {z : Eisenstein} {R : ℝ} (hz : z ≠ 0) (hR : norm z ≤ R)
    (hmem : z ∈ orderedConvolutionSupport S) :
    z ∈ orderedConvolutionSupport (fun i => (S i).filter (fun n => norm n ≤ R)) := by
  obtain ⟨n,hn,hprod⟩ := Finset.mem_image.mp hmem
  apply Finset.mem_image.mpr
  refine ⟨n,Fintype.mem_piFinset.mpr (fun i => Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hn i,?_⟩),hprod⟩
  apply (norm_le_of_dvd hz ?_).trans hR
  rw [← hprod]
  exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)

lemma structuredPrimeMomentAt_eq (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) {Y Z : ℝ} (hY : 0 < Y) (hYZ : Y ≤ Z)
    (V : ℝ → ℂ) (hVhi : ∀ x, 2 < x → V x = 0) :
    structuredPrimeMomentAt a b v e u W X Z V Y =
      structuredPrimeMoment a b v e u W X V Y := by
  let T := (orderedConvolutionSupport (coordinatePrimeSupport W X Y)).filter
    (fun z => IsCoprime z e)
  let U := (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter
    (fun z => IsCoprime z e)
  have hsub : T ⊆ U := by
    intro z hz
    obtain ⟨hz,hcop⟩ := Finset.mem_filter.mp hz
    obtain ⟨n,hn,hprod⟩ := Finset.mem_image.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨n,?_,hprod⟩,hcop⟩
    rw [coordinatePrimeSupport_trim W X hYZ] at hn
    exact Fintype.mem_piFinset.mpr (fun i => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1)
  have hzero (z : Eisenstein) (hz : z ∈ U) (hnorm : ¬norm z ≤ 2*Y) :
      V (norm z/Y) = 0 := hVhi _ ((lt_div_iff₀ hY).mpr (lt_of_not_ge hnorm))
  have hnonzero (z : Eisenstein) (hz : z ∈ U) : z ≠ 0 :=
    primary_ne_zero (orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
      (fun i n hn => (coordinatePrimeSupport_primary W X Z i n hn).1)
      (Finset.mem_filter.mp hz).1)
  symm
  change (∑ z ∈ T, _) = ∑ z ∈ U, _
  calc
    _ = ∑ z ∈ T, primeMomentCoefficient W X Z z*mellinPhase u (norm z)*
        cubicSymbol z (v*a*b^2)*V (norm z/Y) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hN : norm z ≤ 2*Y
      · rw [primeMomentCoefficient_dyad_consistent W X hYZ (hnonzero z (hsub hz)) hN]
      · rw [hzero z (hsub hz) hN]
        simp only [mul_zero]
    _ = _ := Finset.sum_subset hsub (by
      intro z hz hnot
      have hN : ¬norm z ≤ 2*Y := by
        intro hN
        have hm := orderedSupport_filter_norm (coordinatePrimeSupport W X Z) (hnonzero z hz) hN
          (Finset.mem_filter.mp hz).1
        rw [← coordinatePrimeSupport_trim W X hYZ] at hm
        exact hnot (Finset.mem_filter.mpr ⟨hm,(Finset.mem_filter.mp hz).2⟩)
      rw [hzero z hz hN,mul_zero])

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite smooth decomposition of the original structured sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normPartitionWeight_scaled (x D : ℝ) {L : ℝ} (hL : L ≠ 0) (hD : D ≠ 0) :
    normPartitionWeight (x/(L*(D/2))) = normPartitionWeight (2*(x/L)/D) := by
  congr 1
  field_simp

lemma structuredPrimeSum_partition (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ)
    {L B : ℝ} (hL : 0 < L) (N : ℕ) (hN : 2*B ≤ (4/3:ℝ)^N)
    (hrange : ∀ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
      L ≤ norm z ∧ norm z ≤ B*L) :
    structuredPrimeSum a b v e u W X Z =
      ∑ k ∈ Finset.range N,
        structuredPrimeMomentAt a b v e u W X Z normPartitionWeight (L*((4/3:ℝ)^k/2)) := by
  unfold structuredPrimeSum structuredPrimeMomentAt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  have hr := hrange z (Finset.mem_filter.mp hz).1
  have hm := normPartitionWeight_partition
    (show 1 ≤ norm z/L by exact (le_div_iff₀ hL).mpr (by simpa using hr.1))
    (show norm z/L ≤ B by exact (div_le_iff₀ hL).mpr hr.2) hN
  have heq : (∑ k ∈ Finset.range N,
      normPartitionWeight (norm z/(L*((4/3:ℝ)^k/2)))) = 1 := by
    simp_rw [normPartitionWeight_scaled _ _ hL.ne' (pow_ne_zero _ (by norm_num : (4/3:ℝ) ≠ 0))]
    exact hm
  rw [heq,mul_one]

lemma structuredPrimeSum_partition_dyads (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ)
    {L B : ℝ} (hL : 0 < L) (N : ℕ) (hN : 2*B ≤ (4/3:ℝ)^N)
    (hrange : ∀ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
      L ≤ norm z ∧ norm z ≤ B*L)
    (hZ : ∀ k ∈ Finset.range N, L*((4/3:ℝ)^k/2) ≤ Z) :
    structuredPrimeSum a b v e u W X Z =
      ∑ k ∈ Finset.range N,
        structuredPrimeMoment a b v e u W X normPartitionWeight (L*((4/3:ℝ)^k/2)) := by
  rw [structuredPrimeSum_partition a b v e u W X Z hL N hN hrange]
  apply Finset.sum_congr rfl
  intro k hk
  exact structuredPrimeMomentAt_eq a b v e u W X
    (mul_pos hL (div_pos (pow_pos (by norm_num : (0:ℝ) < 4/3) _) (by norm_num)))
    (hZ k hk) normPartitionWeight (fun _ => normPartitionWeight_high)

lemma finite_piece_moment_on {α κ : Type*} [Fintype κ] (S : Finset α)
    (f : κ → α → ℂ) :
    (∑ a ∈ S, ‖∑ k, f k a‖^2) ≤ (Fintype.card κ:ℝ)*(∑ k, ∑ a ∈ S, ‖f k a‖^2) := by
  calc
    _ ≤ ∑ a ∈ S, (Fintype.card κ:ℝ)*(∑ k, ‖f k a‖^2) := by
      apply Finset.sum_le_sum
      intro a ha
      apply (pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_sum_le _ _) 2).trans
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : κ => (1:ℝ))
        (fun k => ‖f k a‖)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredSupportBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The output norm range is derived from the independent coordinate
supports; no product-range hypothesis is imposed on the coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_norm_bounds (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) {R : ℝ}
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (Z : ℝ) (i : ι) (p : Eisenstein) (hp : p ∈ coordinatePrimeSupport W X Z i) :
    X i ≤ norm p ∧ norm p ≤ R*X i := by
  have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  constructor
  · have h : 1 ≤ norm p/X i := le_of_not_gt (fun h => hn (hlo i _ h))
    simpa only [one_mul] using (le_div_iff₀ (hX i)).mp h
  · have h : norm p/X i ≤ R := le_of_not_gt (fun h => hn (hhi i _ h))
    exact (div_le_iff₀ (hX i)).mp h

lemma coordinatePrimeProduct_norm_bounds (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) {R : ℝ} (_hR : 0 ≤ R)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (Z : ℝ) (z : Eisenstein) (hz : z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z)) :
    (∏ i, X i) ≤ norm z ∧ norm z ≤ R^(Fintype.card ι)*(∏ i, X i) := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
  have hb (i : ι) := coordinatePrimeSupport_norm_bounds W X hX hlo hhi Z i (n i)
    (Fintype.mem_piFinset.mp hn i)
  rw [norm_finset_prod]
  constructor
  · exact Finset.prod_le_prod (fun i _ => (hX i).le) (fun i _ => (hb i).1)
  · calc
      _ ≤ ∏ i, R*X i := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (hb i).2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedUnweightedStructuredMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual balanced structured moment without an auxiliary output cutoff. -/
noncomputable section
open Set Filter
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem balanced_unweighted_structured_moment (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity) {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (hR : 1 ≤ R) (J : ℕ) (hJ : 2*R^(Fintype.card ι) ≤ (4/3:ℝ)^J)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) → ∃ T : ℝ,
      ∀ (r : γ) (X : ι → ℝ) (v e : Eisenstein) (u : ℝ) (P : Finset (Eisenstein × Eisenstein)),
      T ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) → (∀ i, X i ≤ L r) → v ≠ 0 → e ≠ 0 →
      norm v ≤ (L r)^δ → norm e ≤ (L r)^δ → |u| ≤ (L r)^(9/25:ℝ) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ (L r)^(1/3+δ) ∧
        norm a.2 ≤ (L r)^(1/3+δ) ∧ (L r)^(1/3-δ) ≤ norm a.1) →
      (∑ a ∈ P, ‖structuredPrimeSum a.1 a.2 v e u (W r) X (((4/3:ℝ)^J/2)*L r)‖^2) ≤ (L r)^(7/3-ε) := by
  let σ : Fin J → ℝ := fun k => (4/3:ℝ)^k.val/2
  have hσ : ∀ k, 0 < σ k := fun k => div_pos (pow_pos (by norm_num) _) (by norm_num)
  obtain ⟨δ,hδ,hδhi,ε,hε,hraw⟩ := balanced_scaled_structured_moment
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ σ hσ normPartitionWeight
    normPartitionWeight_compact normPartitionWeight_positive_support normPartitionWeight_smooth
    (fun _ => normPartitionWeight_low) (fun _ => normPartitionWeight_high)
    normPartitionWeight_norm hGI hGQ
  refine ⟨δ,hδ,hδhi,ε/2,by positivity,?_⟩
  intro L W hL hW hWlo hWhi
  obtain ⟨T₀,hbound⟩ := hraw L W hL hW hWlo
  obtain ⟨T₁,habs⟩ := eventually_atTop.mp (eventually_const_mul_rpow_le
    (by linarith : 7/3-ε < 7/3-ε/2) ((J:ℝ)^2))
  refine ⟨max T₀ T₁,?_⟩
  intro r X v e u P hT hprod hXlo hXhi hv he hvY heY hu hP
  have hYp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hX : ∀ i, 0 < X i := fun i => (Real.rpow_pos_of_pos (show 0 < 2*L r by positivity) c).trans (hXlo i)
  let Z := ((4/3:ℝ)^J/2)*L r
  have hpart (a b : Eisenstein) : structuredPrimeSum a b v e u (W r) X Z =
      ∑ k : Fin J, structuredPrimeMoment a b v e u (W r) X normPartitionWeight (σ k*L r) := by
    have hrange := fun z hz => coordinatePrimeProduct_norm_bounds (W r) X hX
      (show 0 ≤ R by linarith) (hWlo r) (hWhi r) Z z hz
    have hp := structuredPrimeSum_partition_dyads a b v e u (W r) X Z hYp J hJ
      (fun z hz => by simpa only [hprod] using hrange z hz) (by
        intro k hk
        dsimp [Z]
        have hpow : (4/3:ℝ)^k ≤ (4/3:ℝ)^J :=
          pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hk).le
        nlinarith [mul_le_mul_of_nonneg_right hpow hYp.le])
    dsimp only [σ]
    rw [Fin.sum_univ_eq_sum_range (fun k => structuredPrimeMoment a b v e u
      (W r) X normPartitionWeight ((4/3:ℝ)^k/2*L r))]
    simpa only [mul_comm] using hp
  have hb := hbound r X v e u P ((le_max_left _ _).trans hT)
    hXlo hXhi hv he hvY heY hu hP
  calc
    _ = ∑ z ∈ P, ‖∑ k : Fin J,
        structuredPrimeMoment z.1 z.2 v e u (W r) X normPartitionWeight (σ k*L r)‖^2 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hpart]
    _ ≤ (J:ℝ)*(∑ k : Fin J, ∑ z ∈ P,
        ‖structuredPrimeMoment z.1 z.2 v e u (W r) X normPartitionWeight (σ k*L r)‖^2) := by
      simpa only [Fintype.card_fin] using finite_piece_moment_on P
        (fun k z => structuredPrimeMoment z.1 z.2 v e u (W r) X normPartitionWeight (σ k*L r))
    _ ≤ (J:ℝ)*(∑ _k : Fin J, (L r)^(7/3-ε)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun k _ => hb k)
    _ = (J:ℝ)^2*(L r)^(7/3-ε) := by simp; ring
    _ ≤ _ := habs (L r) ((le_max_right _ _).trans hT)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogarithmicPrimeWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial derivative bounds of a logarithmic family, used to apply
the published prime Siegel–Walfisz input by actual partial summation. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma LogarithmicWeightFamily.norm_log_bound {γ : Type*}
    {L : γ → ℝ} {W : γ → ℝ → ℂ} (h : LogarithmicWeightFamily L W) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ i x, ‖W i x‖ ≤ C*(1+Real.log (L i))^A := by
  obtain ⟨C,A,hC,hbound⟩ := h.derivative_bound 0
  refine ⟨C,A,hC,?_⟩
  intro i x
  by_cases hx : 0 < x
  · have he : Real.exp (-(-Real.log x)) = x := by simp [Real.exp_log hx]
    simpa only [norm_iteratedFDeriv_zero,he] using hbound i (-Real.log x)
  · have hz : W i x = 0 := by
      by_contra hn
      exact hx (h.positive i (subset_closure hn))
    rw [hz,norm_zero]
    exact mul_nonneg hC (pow_nonneg (by linarith [Real.log_nonneg (h.length_one i)]) _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeExclusionSavingPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomially bounded exclusion remains negligible compared with
a rough prime coordinate, with every prescribed logarithmic saving. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma exclusion_log_absorption {c d ε : ℝ} (hε : 0 < ε) (hgap : d*ε < c)
    {C : ℝ} (hC : 0 ≤ C) (m k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Y E : ℝ, 0 ≤ E → E ≤ L^d → L^c ≤ Y →
      C*E^ε*(1+Real.log L)^m ≤ Y/(1+Real.log L)^k := by
  let s := (c-d*ε)/2
  have hs : 0 < s := by dsimp [s]; linarith
  have hexp : d*ε+s < c := by dsimp [s]; linarith
  obtain ⟨K,hK,hlog⟩ := log_power_normalization_bound (m+k) hs
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_const_mul_rpow_le hexp (C*K)]
    with L hL hbound
  intro Y E hE hEd hY
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log L := by linarith [Real.log_nonneg hL]
  have hlog' : (1+Real.log L)^(m+k) ≤ K*L^s := by
    calc
      _ = L^s*(L^(-s)*(1+Real.log L)^(m+k)) := by
        rw [← mul_assoc,← Real.rpow_add hLp]
        simp
      _ ≤ L^s*K := mul_le_mul_of_nonneg_left (hlog L hL) (Real.rpow_nonneg hLp.le _)
      _ = _ := mul_comm _ _
  apply (le_div_iff₀ (pow_pos hz k)).mpr
  calc
    _ = C*E^ε*(1+Real.log L)^(m+k) := by rw [pow_add]; ring
    _ ≤ C*(L^d)^ε*(K*L^s) := mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hE hEd hε.le) hC) hlog'
      (pow_nonneg hz.le _) (mul_nonneg hC (Real.rpow_nonneg (Real.rpow_nonneg hLp.le _) _))
    _ = (C*K)*L^(d*ε+s) := by
      rw [← Real.rpow_mul hLp.le,Real.rpow_add hLp]
      ring
    _ ≤ L^c := hbound
    _ ≤ Y := hY

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite realization of the literal prime convolution: each coordinate
contains every primary prime on which its independent weight is nonzero. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_mem_iff {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hhi : ∀ i x, R < x → W i x = 0) (i : ι) (p : Eisenstein) :
    p ∈ fullPrimeSupport R W X i ↔ primaryPrime p ∧ W i (norm p/X i) ≠ 0 := by
  simp only [fullPrimeSupport,Finset.mem_filter,mem_primaryElementBall]
  constructor
  · rintro ⟨⟨⟨hp,_⟩,hw⟩,hq⟩
    exact ⟨⟨hp,hq⟩,hw⟩
  · rintro ⟨⟨hp,hq⟩,hw⟩
    have hn : norm p/X i ≤ R := le_of_not_gt (fun h => hw (hhi i _ h))
    exact ⟨⟨⟨hp,(div_le_iff₀ (hX i)).mp hn⟩,hw⟩,hq⟩

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_eq_coordinate {R Z : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hhi : ∀ i x, R < x → W i x = 0)
    (hZ : ∀ i, R*X i ≤ 2*Z) : fullPrimeSupport R W X = coordinatePrimeSupport W X Z := by
  funext i
  ext p
  rw [fullPrimeSupport_mem_iff W X hX hhi]
  simp only [coordinatePrimeSupport,coordinateSupport,Finset.mem_filter,mem_primaryElementBall]
  constructor
  · rintro ⟨⟨hp,hq⟩,hw⟩
    have hn : norm p/X i ≤ R := le_of_not_gt (fun h => hw (hhi i _ h))
    exact ⟨⟨⟨hp,((div_le_iff₀ (hX i)).mp hn).trans (hZ i)⟩,hw⟩,hq⟩
  · rintro ⟨⟨⟨hp,_⟩,hw⟩,hq⟩
    exact ⟨⟨hp,hq⟩,hw⟩

lemma fullStructuredPrimeSum_eq {R Z : ℝ} (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hhi : ∀ i x, R < x → W i x = 0) (hZ : ∀ i, R*X i ≤ 2*Z) :
    fullStructuredPrimeSum R a b v e u W X = structuredPrimeSum a b v e u W X Z := by
  unfold fullStructuredPrimeSum fullPrimeCoefficient structuredPrimeSum primeMomentCoefficient
  rw [fullPrimeSupport_eq_coordinate W X hX hhi hZ]

lemma coordinate_le_product (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i) (i : ι) :
    X i ≤ ∏ j, X j := by
  rw [← Finset.mul_prod_erase _ X (Finset.mem_univ i)]
  exact le_mul_of_one_le_right (by linarith [hX i]) (Finset.one_le_prod (fun j _ => hX j))

lemma fullStructuredPrimeSum_partition_cutoff {R : ℝ} (hR : 1 ≤ R)
    (J : ℕ) (hJ : 2*R^(Fintype.card ι) ≤ (4/3:ℝ)^J)
    (a b v e : Eisenstein) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 1 ≤ X i) (hhi : ∀ i x, R < x → W i x = 0) :
    fullStructuredPrimeSum R a b v e u W X =
      structuredPrimeSum a b v e u W X (((4/3:ℝ)^J/2)*(∏ i, X i)) := by
  apply fullStructuredPrimeSum_eq a b v e u W X (fun i => by linarith [hX i]) hhi
  intro i
  have hi := coordinate_le_product X hX i
  have hprod : 0 ≤ ∏ i, X i := Finset.prod_nonneg (fun i _ => by linarith [hX i])
  have hk : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hRk : R ≤ R^(Fintype.card ι) := by
    exact le_self_pow₀ hR (Nat.ne_of_gt hk)
  have hRR : R ≤ (4/3:ℝ)^J := by linarith [hRk,show (0:ℝ) ≤ R^Fintype.card ι by positivity]
  nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ R by linarith),
    mul_le_mul_of_nonneg_right hRR hprod]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeExponents
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict exponent gaps away from the two exceptional conductor shapes.
These are the normalized exponents of the two cubic-sieve bounds and
of the ordinary character large sieve, respectively. -/

noncomputable section

namespace CubicFirstMoment

lemma pSieveExponent_neg {p q : ℝ} (hpq : q < p) (hq : 0 ≤ q)
    (hsize : p+2*q ≤ 1) (hex : p ≠ 1 ∨ q ≠ 0) :
    pSieveExponent p q < 0 := by
  have hsum : p+q < 1 := by
    by_contra! hn
    have hq0 : q = 0 := by linarith
    have hp1 : p = 1 := by linarith
    rcases hex with h | h
    · exact h hp1
    · exact h hq0
  unfold pSieveExponent
  exact max_lt (by linarith) (max_lt (by linarith) (by linarith))

lemma qSieveExponent_neg {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q)
    (hsize : p+2*q ≤ 1) : qSieveExponent p q < 0 := by
  unfold qSieveExponent
  exact max_lt (by linarith) (max_lt (by linarith) (by linarith))

lemma ordinarySieveExponent_diag_neg {v : ℝ} (hv : 0 < v) (hv1 : v < 1/3) :
    ordinarySieveExponent v v < 0 := by
  unfold ordinarySieveExponent
  exact max_lt (by linarith) (by linarith)

/-- The only nonnegative-gap possibilities in the large-conductor region
are precisely the two shapes treated by the structured moment argument. -/
theorem noncubeSieveExponent_neg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsize : p+2*q ≤ 1) (hlarge : 0 < p+2*q)
    (hfirst : p ≠ 1 ∨ q ≠ 0) (hbalanced : p ≠ 1/3 ∨ q ≠ 1/3) :
    noncubeSieveExponent p q < 0 := by
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · exact lt_of_le_of_lt (min_le_right _ _)
      (lt_of_le_of_lt (min_le_left _ _) (qSieveExponent_neg hp hpq hsize))
  · subst q
    have hp0 : 0 < p := by linarith
    have hp1 : p < 1/3 := by
      rcases hbalanced with h | h <;> exact lt_of_le_of_ne (by linarith) h
    exact lt_of_le_of_lt (min_le_right _ _)
      (lt_of_le_of_lt (min_le_right _ _) (ordinarySieveExponent_diag_neg hp0 hp1))
  · exact lt_of_le_of_lt (min_le_left _ _) (pSieveExponent_neg hpq hq hsize hfirst)

lemma continuous_noncubeSieveExponent :
    Continuous (fun x : ℝ × ℝ => noncubeSieveExponent x.1 x.2) := by
  unfold noncubeSieveExponent pSieveExponent qSieveExponent ordinarySieveExponent
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformNoncubeGap
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness makes the nonexceptional conductor saving uniform. -/

noncomputable section
open Set
namespace CubicFirstMoment

/-- With a positive conductor threshold and fixed neighborhoods of the two
exceptional shapes removed, one of the three sieve bounds saves a single
uniform positive power. -/
theorem uniform_noncube_exponent_gap {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → p+2*q ≤ 1 →
      κ ≤ p+2*q → δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| →
      noncubeSieveExponent p q ≤ -γ := by
  let K : Set (ℝ × ℝ) := (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ∩
    {x | x.1+2*x.2 ≤ 1 ∧ κ ≤ x.1+2*x.2 ∧
      δ ≤ |x.1-1|+|x.2| ∧ δ ≤ |x.1-1/3|+|x.2-1/3|}
  have h₁ : IsClosed {x : ℝ × ℝ | x.1+2*x.2 ≤ 1} :=
    isClosed_le (by fun_prop) continuous_const
  have h₂ : IsClosed {x : ℝ × ℝ | κ ≤ x.1+2*x.2} :=
    isClosed_le continuous_const (by fun_prop)
  have h₃ : IsClosed {x : ℝ × ℝ | δ ≤ |x.1-1|+|x.2|} :=
    isClosed_le continuous_const (by fun_prop)
  have h₄ : IsClosed {x : ℝ × ℝ | δ ≤ |x.1-1/3|+|x.2-1/3|} :=
    isClosed_le continuous_const (by fun_prop)
  have hclosed := h₁.inter (h₂.inter (h₃.inter h₄))
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right hclosed
  have hneg : ∀ x ∈ K, noncubeSieveExponent x.1 x.2 < 0 := by
    rintro ⟨p,q⟩ ⟨⟨⟨hp,_⟩,⟨hq,_⟩⟩,hsize,hlarge,hfirst,hbalanced⟩
    apply noncubeSieveExponent_neg hp hq hsize (hκ.trans_le hlarge)
    · by_contra! h
      rcases h with ⟨rfl,rfl⟩
      norm_num at hfirst
      linarith
    · by_contra! h
      rcases h with ⟨rfl,rfl⟩
      norm_num at hbalanced
      linarith
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn hne continuous_noncubeSieveExponent.continuousOn
    refine ⟨-noncubeSieveExponent x.1 x.2/2,by linarith [hneg x hx],?_⟩
    intro p q hp hq hsize hlarge hfirst hbalanced
    have hp1 : p ≤ 1 := by linarith
    have hq1 : q ≤ 1 := by linarith
    have hmem : (p,q) ∈ K := ⟨⟨⟨hp,hp1⟩,⟨hq,hq1⟩⟩,hsize,hlarge,hfirst,hbalanced⟩
    have hm := hmax hmem
    have hn := hneg x hx
    change noncubeSieveExponent p q ≤ noncubeSieveExponent x.1 x.2 at hm
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro p q hp hq hsize hlarge hfirst hbalanced
    apply False.elim
    apply hne
    exact ⟨(p,q),⟨⟨⟨hp,by linarith⟩,⟨hq,by linarith⟩⟩,hsize,hlarge,hfirst,hbalanced⟩⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubePowerBounds
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalization of the three numerical sieve bounds, and a quantitative
uniform power saving away from the exceptional configurations. -/

noncomputable section
namespace CubicFirstMoment

private lemma sieve_power_mul_div {B : ℝ} (hB : 0 < B) (a b c : ℝ) :
    B^a*B^b/B^c = B^(a+b-c) := by
  rw [← Real.rpow_add hB,← Real.rpow_sub hB]

private lemma sieve_power_denominator {B : ℝ} (hB : 0 < B) (p q : ℝ) :
    B*(B^p*(B^q)^2)^(1/3:ℝ) = B^(1+(p+2*q)/3) := by
  have hq : (B^q)^2 = B^(2*q) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hB.le]
    congr 1
    ring
  rw [hq,← Real.rpow_add hB,← Real.rpow_mul hB.le]
  calc
    _ = B^(1:ℝ)*B^((p+2*q)/3) := by rw [Real.rpow_one]; congr 2; ring
    _ = _ := by rw [← Real.rpow_add hB]

lemma pSieveRatio_eq_powers {B : ℝ} (hB : 0 < B) (p q : ℝ) :
    pSieveRatio B (B^p) (B^q) =
      B^((2*p+q)/3-1)+B^((q-p)/3)+B^((p+q-1)/3) := by
  have hpb : (B^p*B)^(2/3:ℝ) = B^((p+1)*(2/3)) := by
    conv_lhs => arg 1; rhs; rw [← Real.rpow_one B]
    rw [← Real.rpow_add hB,← Real.rpow_mul hB.le]
  unfold pSieveRatio
  rw [sieve_power_denominator hB,hpb]
  have h₁ : B^q*B^p/B^(1+(p+2*q)/3) = B^((2*p+q)/3-1) := by
    rw [sieve_power_mul_div hB]
    congr 1
    ring
  have h₂ : B^q*B/B^(1+(p+2*q)/3) = B^((q-p)/3) := by
    calc
      _ = B^q*B^(1:ℝ)/B^(1+(p+2*q)/3) := by rw [Real.rpow_one]
      _ = _ := by rw [sieve_power_mul_div hB]; congr 1; ring
  have h₃ : B^q*B^((p+1)*(2/3))/B^(1+(p+2*q)/3) = B^((p+q-1)/3) := by
    rw [sieve_power_mul_div hB]
    congr 1
    ring
  calc
    _ = B^q*B^p/B^(1+(p+2*q)/3)+B^q*B/B^(1+(p+2*q)/3)+
        B^q*B^((p+1)*(2/3))/B^(1+(p+2*q)/3) := by ring
    _ = _ := by rw [h₁,h₂,h₃]

lemma qSieveRatio_eq_powers {B : ℝ} (hB : 0 < B) (p q : ℝ) :
    qSieveRatio B (B^p) (B^q) =
      B^((2*p+q)/3-1)+B^(2*(p-q)/3)+B^((2*p-1)/3) := by
  have hqb : (B^q*B)^(2/3:ℝ) = B^((q+1)*(2/3)) := by
    conv_lhs => arg 1; rhs; rw [← Real.rpow_one B]
    rw [← Real.rpow_add hB,← Real.rpow_mul hB.le]
  unfold qSieveRatio
  rw [sieve_power_denominator hB,hqb]
  have h₁ : B^p*B^q/B^(1+(p+2*q)/3) = B^((2*p+q)/3-1) := by
    rw [sieve_power_mul_div hB]
    congr 1
    ring
  have h₂ : B^p*B/B^(1+(p+2*q)/3) = B^(2*(p-q)/3) := by
    calc
      _ = B^p*B^(1:ℝ)/B^(1+(p+2*q)/3) := by rw [Real.rpow_one]
      _ = _ := by rw [sieve_power_mul_div hB]; congr 1; ring
  have h₃ : B^p*B^((q+1)*(2/3))/B^(1+(p+2*q)/3) = B^((2*p-1)/3) := by
    rw [sieve_power_mul_div hB]
    congr 1
    ring
  calc
    _ = B^p*B^q/B^(1+(p+2*q)/3)+B^p*B/B^(1+(p+2*q)/3)+
        B^p*B^((q+1)*(2/3))/B^(1+(p+2*q)/3) := by ring
    _ = _ := by rw [h₁,h₂,h₃]

lemma ordinarySieveRatio_eq_powers {B : ℝ} (hB : 0 < B) (p q : ℝ) :
    ordinarySieveRatio B (B^p) (B^q) =
      B^(-(p+2*q)/3)+B^((5*p+4*q)/3-1) := by
  have hpq : (B^p*B^q)^2 = B^(2*(p+q)) := by
    rw [← Real.rpow_add hB,← Real.rpow_natCast,← Real.rpow_mul hB.le]
    congr 1
    ring
  unfold ordinarySieveRatio
  rw [sieve_power_denominator hB,hpq,add_div]
  congr 1
  · calc
      _ = B^(1-(1+(p+2*q)/3)) := by rw [Real.rpow_sub hB,Real.rpow_one]
      _ = _ := by congr 1; ring
  · rw [← Real.rpow_sub hB]
    congr 1
    ring

private lemma sieve_three_power_le {B : ℝ} (hB : 1 ≤ B) (a b c : ℝ) :
    B^a+B^b+B^c ≤ 3*B^(max a (max b c)) := by
  have ha := Real.rpow_le_rpow_of_exponent_le hB (le_max_left a (max b c))
  have hb := Real.rpow_le_rpow_of_exponent_le hB
    ((le_max_left b c).trans (le_max_right a (max b c)))
  have hc := Real.rpow_le_rpow_of_exponent_le hB
    ((le_max_right b c).trans (le_max_right a (max b c)))
  linarith

lemma pSieveRatio_le {B : ℝ} (hB : 1 ≤ B) (p q : ℝ) :
    pSieveRatio B (B^p) (B^q) ≤ 3*B^(pSieveExponent p q) := by
  rw [pSieveRatio_eq_powers (by linarith)]
  exact sieve_three_power_le hB _ _ _

lemma qSieveRatio_le {B : ℝ} (hB : 1 ≤ B) (p q : ℝ) :
    qSieveRatio B (B^p) (B^q) ≤ 3*B^(qSieveExponent p q) := by
  rw [qSieveRatio_eq_powers (by linarith)]
  exact sieve_three_power_le hB _ _ _

lemma ordinarySieveRatio_le {B : ℝ} (hB : 1 ≤ B) (p q : ℝ) :
    ordinarySieveRatio B (B^p) (B^q) ≤ 3*B^(ordinarySieveExponent p q) := by
  rw [ordinarySieveRatio_eq_powers (by linarith)]
  have h₁ := Real.rpow_le_rpow_of_exponent_le hB
    (le_max_left (-(p+2*q)/3) ((5*p+4*q)/3-1))
  have h₂ := Real.rpow_le_rpow_of_exponent_le hB
    (le_max_right (-(p+2*q)/3) ((5*p+4*q)/3-1))
  have hp := Real.rpow_nonneg (by linarith : 0 ≤ B) (ordinarySieveExponent p q)
  change _ ≤ 3*B^(max (-(p+2*q)/3) ((5*p+4*q)/3-1))
  unfold ordinarySieveExponent at hp
  linarith

/-- This is the numerical bound used after normalizing the concrete sieve
estimates; the exponent is the limiting exponent. -/
theorem noncubeSieveRatio_le {B : ℝ} (hB : 1 ≤ B) (p q : ℝ) :
    min (pSieveRatio B (B^p) (B^q))
      (min (qSieveRatio B (B^p) (B^q)) (ordinarySieveRatio B (B^p) (B^q))) ≤
      3*B^(noncubeSieveExponent p q) := by
  unfold noncubeSieveExponent
  by_cases h : pSieveExponent p q ≤ min (qSieveExponent p q) (ordinarySieveExponent p q)
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (pSieveRatio_le hB p q)
  · rw [min_eq_right (le_of_not_ge h)]
    by_cases hq : qSieveExponent p q ≤ ordinarySieveExponent p q
    · rw [min_eq_left hq]
      exact ((min_le_right _ _).trans (min_le_left _ _)).trans (qSieveRatio_le hB p q)
    · rw [min_eq_right (le_of_not_ge hq)]
      exact ((min_le_right _ _).trans (min_le_right _ _)).trans (ordinarySieveRatio_le hB p q)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform exponent saving applied to the actual finite frequency mass. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma primary_support_card_le (S : Finset Eisenstein) {U : ℝ} (hU : 0 ≤ U)
    (hS : ∀ s ∈ S, primary s ∧ norm s ≤ U) : (S.card:ℝ) ≤ 18*U := by
  have hsub : S ⊆ nonzeroNormBall U := fun s hs =>
    mem_nonzeroNormBall.mpr ⟨(hS s hs).2,primary_ne_zero (hS s hs).1⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hU)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredCoefficientEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coefficient energy needed by the noncube sieve follows from the
actual independent prime weights, including logarithmic weight families. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeMomentCoefficient_norm_le (W : ι → ℝ → ℂ) (X M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (Z : ℝ) (z : Eisenstein) :
    ‖primeMomentCoefficient W X Z z‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  by_cases hz : Squarefree z
  · simpa only [primeMomentCoefficient,squarefreeConvolution,ite_eq_left hz] using
      orderedConvolution_norm_bound (coordinatePrimeSupport W X Z)
        (fun i n => W i (norm n/X i)) M (coordinatePrimeSupport_primary W X Z) hM
        (fun i p _ => hW i _) z
  · simpa only [primeMomentCoefficient,squarefreeConvolution,ite_eq_right hz,norm_zero] using
      mul_nonneg (Nat.cast_nonneg ((Fintype.card ι)^(Fintype.card ι)))
        (Finset.prod_nonneg (fun i _ => hM i))

lemma structuredCoefficient_energy_le (W : ι → ℝ → ℂ) (X M : ι → ℝ)
    (hX : ∀ i, 0 < X i) {R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (Z : ℝ) :
    (∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
      ‖primeMomentCoefficient W X Z z‖^2) ≤
      18*(R^(Fintype.card ι)*(∏ i, X i))*
        (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  let S := orderedConvolutionSupport (coordinatePrimeSupport W X Z)
  have hcard : (S.card:ℝ) ≤ 18*(R^(Fintype.card ι)*(∏ i, X i)) :=
    primary_support_card_le S (mul_nonneg (pow_nonneg hR _)
      (Finset.prod_nonneg (fun i _ => (hX i).le))) (fun z hz =>
      ⟨orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
        (fun i p hp => (coordinatePrimeSupport_primary W X Z i p hp).1) hz,
        (coordinatePrimeProduct_norm_bounds W X hX hR hlo hhi Z z hz).2⟩)
  calc
    _ ≤ ∑ _z ∈ S, (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 :=
      Finset.sum_le_sum (fun z _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
        (primeMomentCoefficient_norm_le W X M hM hW Z z) 2)
    _ = (S.card:ℝ)*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

lemma LogarithmicWeightFamily.subpower_norm {L : γ → ℝ} {W : γ → ℝ → ℂ}
    (h : LogarithmicWeightFamily L W) {s : ℝ} (hs : 0 < s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r x, ‖W r x‖ ≤ M*(L r)^s := by
  obtain ⟨M,hM,hbound⟩ := (h.normalize hs).norm_bound
  refine ⟨M,hM,?_⟩
  intro r x
  have hL : 0 < L r := zero_lt_one.trans_le (h.length_one r)
  have hb : (L r)^(-s)*‖W r x‖ ≤ M := by
    simpa only [normalizedLogWeight,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hL.le _)] using hbound r x
  calc
    _ = (L r)^s*((L r)^(-s)*‖W r x‖) := by
      rw [← mul_assoc,← Real.rpow_add hL]; simp
    _ ≤ (L r)^s*M := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hL.le _)
    _ = _ := mul_comm _ _

/-- Every specified logarithmic family has the actual subpower coefficient
energy required in the nonexceptional character sieve. -/
theorem logarithmic_structured_coefficient_energy {L : γ → ℝ}
    {W : γ → ι → ℝ → ℂ} (hW : LogarithmicWeightFamily
      (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ T : ℝ, ∀ (r : γ) (X : ι → ℝ) (Z : ℝ), 1 ≤ L r → T ≤ L r →
      (∀ i, 0 < X i) → (∏ i, X i) = L r →
      (∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport (W r) X Z),
        ‖primeMomentCoefficient (W r) X Z z‖^2) ≤ (L r)^(1+ε) := by
  let k : ℕ := Fintype.card ι
  let s := ε/(4*((k:ℝ)+1))
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨M,hM,hbound⟩ := hW.subpower_norm hs
  let C := 18*R^k*((k^k:ℕ)*M^k)^2
  have he : 1+2*s*(k:ℝ) < 1+ε := by
    dsimp [s]
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
    have hd : (0:ℝ) < 4*((k:ℝ)+1) := by positivity
    have hh : s*(4*((k:ℝ)+1)) = ε := div_mul_cancel₀ _ hd.ne'
    nlinarith [mul_nonneg hs.le hk]
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_const_mul_rpow_le he C)
  refine ⟨T,?_⟩
  intro r X Z hL hT' hX hprod
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hb := structuredCoefficient_energy_le (W r) X (fun _ => M*(L r)^s) hX hR
    (hlo r) (hhi r) (fun _ => mul_nonneg hM (Real.rpow_nonneg hLp.le _))
    (fun i x => hbound (r,i) x) Z
  rw [hprod] at hb
  apply hb.trans
  calc
    _ = C*(L r)^(1+2*s*(k:ℝ)) := by
      simp only [Finset.prod_const,Finset.card_univ,mul_pow]
      rw [← Real.rpow_natCast ((L r)^s) k,← Real.rpow_mul hLp.le]
      dsimp [C,k]
      rw [mul_pow,← Real.rpow_natCast ((L r)^(s*(Fintype.card ι:ℝ))) 2,
        ← Real.rpow_mul hLp.le]
      rw [Real.rpow_add hLp,Real.rpow_one]
      have hexp : s*(Fintype.card ι:ℝ)*(2:ℝ) = 2*s*(Fintype.card ι:ℝ) := by ring
      norm_num only [Nat.cast_ofNat]
      rw [hexp]
      ring
    _ ≤ _ := hT (L r) hT'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullStructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary published mean-value theorem applied to the literal
prime convolution, with every numerator and excluded-prime factor retained. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeSupport_eq_product_cutoff {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i)
    (hhi : ∀ i x, R < x → W i x = 0) :
    fullPrimeSupport R W X = coordinatePrimeSupport W X (R/2*(∏ i, X i)) := by
  apply fullPrimeSupport_eq_coordinate W X (fun i => zero_lt_one.trans_le (hX i)) hhi
  intro i
  have h := mul_le_mul_of_nonneg_left (coordinate_le_product X hX i) hR
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredResidualFrequencies
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact passage from ramified/cube frequencies to the structured pair
moments. A cube factor becomes an arithmetic exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_primary (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    ∀ i, ∀ z ∈ fullPrimeSupport R W X i, primary z := by
  intro i z hz
  exact (mem_primaryElementBall.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1

lemma cubicSymbol_cube_indicator {z : Eisenstein} (hz : primary z) (j : Eisenstein) :
    cubicSymbol z (j^3) = if IsCoprime z j then 1 else 0 := by
  rw [cubicSymbol_pow_upper hz]
  by_cases hj : IsCoprime z j
  · rw [ite_eq_left hj,cubicSymbol_cube_of_isCoprime hz j hj]
  · rw [ite_eq_right hj,cubicSymbol_eq_zero_of_not_isCoprime hz hj,zero_pow (by norm_num : (3:ℕ) ≠ 0)]

lemma fullStructuredPrimeSum_residual (R : ℝ) (r j p q v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    fullStructuredPrimeSum R (r*p*q^2*j^3) 1 v e u W X =
      fullStructuredPrimeSum R p q (v*r) (e*j) u W X := by
  unfold fullStructuredPrimeSum
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have hp := orderedPrimarySupport_primary (fullPrimeSupport R W X)
    (fullPrimeSupport_primary R W X) hz
  have hcop : IsCoprime z (e*j) ↔ IsCoprime z e ∧ IsCoprime z j :=
    ⟨fun h => ⟨h.of_mul_right_left,h.of_mul_right_right⟩,fun h => h.1.mul_right h.2⟩
  have hnum : v*(r*p*q^2*j^3)*1^2 = ((v*r)*p*q^2)*j^3 := by ring
  rw [hnum,cubicSymbol_mul_upper hp,cubicSymbol_cube_indicator hp j]
  by_cases he : IsCoprime z e <;> by_cases hj : IsCoprime z j <;>
    simp only [hcop,he,hj,and_self,and_false,false_and,ite_true, if_true,ite_false, if_false,mul_one,mul_zero]

lemma fullStructured_residual_mass_le (R : ℝ) (Ram J H : Finset Eisenstein)
    (P : Finset (Eisenstein × Eisenstein))
    (hH : H ⊆ coprimeResidualSupport Ram J P) (v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u W X‖^2) ≤
      ∑ r ∈ Ram, ∑ j ∈ J, ∑ z ∈ P,
        ‖fullStructuredPrimeSum R z.1 z.2 (v*r) (e*j) u W X‖^2 := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg hH (fun _ _ _ => sq_nonneg _)).trans
  unfold coprimeResidualSupport
  apply (Finset.sum_image_le_of_nonneg (fun _ _ => sq_nonneg _)).trans_eq
  calc
    _ = ∑ r ∈ Ram, ∑ j ∈ J, ∑ z ∈ P,
        ‖fullStructuredPrimeSum R (r*z.1*z.2^2*j^3) 1 v e u W X‖^2 :=
      (Finset.sum_product (Ram.product J) P
        (fun t : (Eisenstein × Eisenstein) × (Eisenstein × Eisenstein) =>
          ‖fullStructuredPrimeSum R (t.1.1*t.2.1*t.2.2^2*t.1.2^3) 1 v e u W X‖^2)).trans
        (Finset.sum_product Ram J (fun t : Eisenstein × Eisenstein =>
          ∑ z ∈ P, ‖fullStructuredPrimeSum R (t.1*z.1*z.2^2*t.2^3) 1 v e u W X‖^2))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro z hz
      rw [fullStructuredPrimeSum_residual]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicDyadicCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite cover of all noncube frequencies outside the small-core set
by the actual coprime ramified/squarefree blocks used in the moment bounds. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coreDyadicConductor_pos (i j : ℕ) : 0 < coreDyadicConductor i j := by
  unfold coreDyadicConductor
  positivity

lemma squarefreePrimaryDyad_gramDyad {i : ℕ} {s : Eisenstein}
    (hs : s ∈ squarefreePrimaryDyad i) : gramDyad ((2:ℝ)^i) s := by
  obtain ⟨hf,hp,hq⟩ := mem_squarefreePrimaryDyad.mp hs
  have hlog := (mem_frequencyDyad.mp hf).2
  refine ⟨hp,hq,(frequencyDyad_norm hf).1,?_⟩
  have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (normNat s)
  rw [hlog] at hlt
  have hcast : norm s < (2:ℝ)^(i+1) := by
    rw [← normNat_cast]
    exact_mod_cast hlt
  simpa only [pow_succ,mul_comm] using hcast

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicFrequencyMassSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete small-core / dyadic-core partition of a finite noncube
mass. Multiple arithmetic decompositions cost no frequency multiplicity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coreDyadicCubeFactors_card_weight {B : ℝ} (hB : 0 ≤ B) (i j : ℕ) :
    ((coreDyadicCubeFactors B i j).card:ℝ)*(coreDyadicConductor i j)^(1/3:ℝ) ≤
      18*B^(1/3:ℝ) := by
  have hD := coreDyadicConductor_pos i j
  calc
    _ ≤ (18*(B/coreDyadicConductor i j)^(1/3:ℝ))*
        (coreDyadicConductor i j)^(1/3:ℝ) :=
      mul_le_mul_of_nonneg_right (nonzeroNormBall_card_le (Real.rpow_nonneg (div_nonneg hB hD.le) _))
        (Real.rpow_nonneg hD.le _)
    _ = _ := by
      rw [Real.div_rpow hB hD.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hD (1/3:ℝ))]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoreBlockGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric cube cutoff in each actual core block has precisely
the mass scale needed by the noncube moment estimates. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma coreDyadicCubeFactors_spec {B : ℝ} (hB : 0 ≤ B) {i j : ℕ} {c : Eisenstein}
    (hc : c ∈ coreDyadicCubeFactors B i j) :
    c ≠ 0 ∧ norm c^3*coreDyadicConductor i j ≤ B := by
  obtain ⟨hcN,hc0⟩ := mem_nonzeroNormBall.mp hc
  have hD := coreDyadicConductor_pos i j
  refine ⟨hc0,?_⟩
  have hp := pow_le_pow_left₀ (norm_nonneg c) hcN 3
  rw [rpow_third_cube (div_nonneg hB hD.le)] at hp
  exact (le_div_iff₀ hD).mp hp

lemma rpow_eight_third : (8:ℝ)^(1/3:ℝ) = 2 := by
  rw [show (8:ℝ) = (2:ℝ)^3 by norm_num,← Real.rpow_natCast (2:ℝ) 3,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

lemma coreDyadicCubeFactors_card_eight_weight {B : ℝ} (hB : 0 ≤ B) (i j : ℕ) :
    ((coreDyadicCubeFactors B i j).card:ℝ)*(8*coreDyadicConductor i j)^(1/3:ℝ) ≤
      36*B^(1/3:ℝ) := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) (coreDyadicConductor_pos i j).le,
    rpow_eight_third]
  nlinarith [coreDyadicCubeFactors_card_weight hB i j]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_EnlargedNoncubeGap
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonexceptional sieve gap persists under the small enlargement of
`P Q² ≤ B` required by the dispersion localization. -/
noncomputable section
open Set
namespace CubicFirstMoment

theorem enlarged_noncube_exponent_gap {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ η γ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < γ ∧
      ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → p+2*q ≤ 1+η →
      κ ≤ p+2*q → δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| →
      noncubeSieveExponent p q ≤ -γ := by
  obtain ⟨γ,hγ,hgap⟩ := uniform_noncube_exponent_gap hκ hδ
  let K : Set (ℝ × ℝ) := (Icc (0:ℝ) 2 ×ˢ Icc (0:ℝ) 2) ∩
    {x | κ ≤ x.1+2*x.2 ∧ δ ≤ |x.1-1|+|x.2| ∧
      δ ≤ |x.1-1/3|+|x.2-1/3| ∧ -γ/2 ≤ noncubeSieveExponent x.1 x.2}
  have h₁ : IsClosed {x : ℝ × ℝ | κ ≤ x.1+2*x.2} :=
    isClosed_le continuous_const (by fun_prop)
  have h₂ : IsClosed {x : ℝ × ℝ | δ ≤ |x.1-1|+|x.2|} :=
    isClosed_le continuous_const (by fun_prop)
  have h₃ : IsClosed {x : ℝ × ℝ | δ ≤ |x.1-1/3|+|x.2-1/3|} :=
    isClosed_le continuous_const (by fun_prop)
  have h₄ : IsClosed {x : ℝ × ℝ | -γ/2 ≤ noncubeSieveExponent x.1 x.2} :=
    isClosed_le continuous_const continuous_noncubeSieveExponent
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    (h₁.inter (h₂.inter (h₃.inter h₄)))
  have hpositive : ∀ x ∈ K, 0 < x.1+2*x.2-1 := by
    rintro ⟨p,q⟩ ⟨⟨⟨hp,_⟩,⟨hq,_⟩⟩,hlarge,hfirst,hbalanced,hbad⟩
    by_contra! h
    have hg := hgap p q hp hq (by linarith) hlarge hfirst hbalanced
    linarith
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hne (show
        Continuous (fun x : ℝ × ℝ => x.1+2*x.2-1) by fun_prop).continuousOn
    let η : ℝ := min 1 ((x.1+2*x.2-1)/2)
    have hη : 0 < η := lt_min (by norm_num) (by linarith [hpositive x hx])
    refine ⟨η,γ/2,hη,min_le_left _ _,by positivity,?_⟩
    intro p q hp hq hsize hlarge hfirst hbalanced
    by_contra! hbad
    have hmem : (p,q) ∈ K := ⟨⟨⟨hp,by
      have := min_le_left (1:ℝ) ((x.1+2*x.2-1)/2)
      change η ≤ 1 at this
      linarith⟩,⟨hq,by
      have := min_le_left (1:ℝ) ((x.1+2*x.2-1)/2)
      change η ≤ 1 at this
      linarith⟩⟩,hlarge,hfirst,hbalanced,by linarith⟩
    have hm := hmin hmem
    change x.1+2*x.2-1 ≤ p+2*q-1 at hm
    have he : η ≤ (x.1+2*x.2-1)/2 := min_le_right _ _
    linarith [hpositive x hx]
  · refine ⟨1,γ/2,by norm_num,le_rfl,by positivity,?_⟩
    intro p q hp hq hsize hlarge hfirst hbalanced
    by_contra! hbad
    apply hne
    exact ⟨(p,q),⟨⟨⟨hp,by linarith⟩,⟨hq,by linarith⟩⟩,
      hlarge,hfirst,hbalanced,by linarith⟩⟩

/-- The same enlargement allows all sieve epsilon losses to be absorbed. -/
theorem enlarged_noncube_ratio_saving {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ η γ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < γ ∧
      ∀ (B p q e : ℝ), 1 ≤ B → 0 ≤ p → 0 ≤ q → p+2*q ≤ 1+η →
      κ ≤ p+2*q → δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| → e ≤ γ/2 →
      B^e * min (pSieveRatio B (B^p) (B^q))
        (min (qSieveRatio B (B^p) (B^q)) (ordinarySieveRatio B (B^p) (B^q))) ≤
          3*B^(-γ/2) := by
  obtain ⟨η,γ,hη,hηhi,hγ,hgap⟩ := enlarged_noncube_exponent_gap hκ hδ
  refine ⟨η,γ,hη,hηhi,hγ,?_⟩
  intro B p q e hB hp hq hsize hlarge hfirst hbalanced he
  have hg := hgap p q hp hq hsize hlarge hfirst hbalanced
  calc
    _ ≤ B^e*(3*B^(noncubeSieveExponent p q)) :=
      mul_le_mul_of_nonneg_left (noncubeSieveRatio_le hB p q)
        (Real.rpow_nonneg (by linarith) _)
    _ = 3*B^(e+noncubeSieveExponent p q) := by
      rw [Real.rpow_add (by linarith : 0 < B)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB (by linarith)) (by norm_num)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DilatedNoncubeMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite noncube character mass in the enlarged conductor region
used by dispersion, with the fixed coefficient-support dilation absorbed
into the constants. The small enlargement is derived from the sieve gap. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

private lemma sieve_epsilon_loss_p0 {B p q ε : ℝ} (hB : 1 ≤ B)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hsize : p+2*q ≤ 2) (hε : 0 ≤ ε) :
    (B^p*B)^ε ≤ B^(3*ε) ∧ (B^q*B)^ε ≤ B^(3*ε) ∧
      (B^p*B^q)^ε ≤ B^(3*ε) := by
  have hB0 : 0 < B := by linarith
  have hh (a : ℝ) (ha : a ≤ 2) : (B^a*B)^ε ≤ B^(3*ε) := by
    have he : B^a*B = B^(a+1) := by rw [Real.rpow_add hB0,Real.rpow_one]
    rw [he,← Real.rpow_mul hB0.le]
    exact Real.rpow_le_rpow_of_exponent_le hB (mul_le_mul_of_nonneg_right (by linarith) hε)
  refine ⟨hh p (by linarith),hh q (by linarith),?_⟩
  rw [← Real.rpow_add hB0,← Real.rpow_mul hB0.le]
  exact Real.rpow_le_rpow_of_exponent_le hB (mul_le_mul_of_nonneg_right (by linarith) hε)

private lemma pSieveRatio_cancel_p0 {B P Q : ℝ} (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) :
    (B*(P*Q^2)^(1/3:ℝ))*pSieveRatio B P Q = Q*(P+B+(P*B)^(2/3:ℝ)) := by
  unfold pSieveRatio
  have hD : B*(P*Q^2)^(1/3:ℝ) ≠ 0 := ne_of_gt (by positivity)
  exact mul_div_cancel₀ _ hD

private lemma qSieveRatio_cancel_p0 {B P Q : ℝ} (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) :
    (B*(P*Q^2)^(1/3:ℝ))*qSieveRatio B P Q = P*(Q+B+(Q*B)^(2/3:ℝ)) := by
  unfold qSieveRatio
  have hD : B*(P*Q^2)^(1/3:ℝ) ≠ 0 := ne_of_gt (by positivity)
  exact mul_div_cancel₀ _ hD

private lemma ordinarySieveRatio_cancel_p0 {B P Q : ℝ} (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) :
    (B*(P*Q^2)^(1/3:ℝ))*ordinarySieveRatio B P Q = B+(P*Q)^2 := by
  unfold ordinarySieveRatio
  have hD : B*(P*Q^2)^(1/3:ℝ) ≠ 0 := ne_of_gt (by positivity)
  exact mul_div_cancel₀ _ hD

private lemma scale_sieve_row_p0 {r j C T loss term E L W M D ratio : ℝ}
    (hr : 0 ≤ r) (hj : 0 ≤ j) (hE : 0 ≤ E) (hloss0 : 0 ≤ loss)
    (hterm : 0 ≤ term) (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hCT : C*T ≤ L*W) (hloss : loss ≤ M) (hcancel : D*ratio = W*term) :
    r*j*C*(T*loss*term)*E ≤ (r*j*L*D*E)*M*ratio := by
  calc
    _ = r*j*(C*T)*loss*term*E := by ring
    _ ≤ r*j*(L*W)*M*term*E := by gcongr
    _ = (r*j*L*M*E)*(W*term) := by ring
    _ = (r*j*L*M*E)*(D*ratio) := by rw [hcancel]
    _ = _ := by ring

/-- Away from the two exceptional shapes, the actual quadratic character mass
saves a uniform power over `B*(P*Q²)^(1/3)` times coefficient energy. -/
theorem quantitative_dilated_noncube_mass (hHuxley : HuxleyAdditiveLargeSieve)
    {K : ℝ} (hK : 1 ≤ K)
    {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ η C γ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < C ∧ 0 < γ ∧
      ∀ (B p q : ℝ), 1 ≤ B → 0 ≤ p → 0 ≤ q → p+2*q ≤ 1+η →
        κ ≤ p+2*q → δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| →
      ∀ (A R S T J H : Finset Eisenstein),
        (∀ a ∈ A, primary a ∧ Squarefree a ∧ norm a ≤ K*B) →
        (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ B^p) →
        (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ B^q) →
        H ⊆ coprimeResidualSupport R J (coprimePairs S T) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
        C*(R.card:ℝ)*J.card*B*(B^p*(B^q)^2)^(1/3:ℝ)*B^(-γ)*
          ∑ a ∈ A, ‖β a‖^2 := by
  obtain ⟨η,γ,hη,hηhi,hγ,hgap⟩ := enlarged_noncube_ratio_saving hκ hδ
  let ε := γ/8
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C₁,C₂,hC₁,hC₂,hraw⟩ := dilated_noncube_three_sieve_bounds hHuxley hK hε
  let L := 18*max C₁ C₂
  have hL : 0 < L := mul_pos (by norm_num) (lt_max_iff.mpr (Or.inl hC₁))
  refine ⟨η,3*L,γ/2,hη,hηhi,mul_pos (by norm_num) hL,by positivity,?_⟩
  intro B p q hB hp hq hsize hlarge hfirst hbalanced A R S T J H hA hS hT hH β
  let E := ∑ a ∈ A, ‖β a‖^2
  let D := B*(B^p*(B^q)^2)^(1/3:ℝ)
  let F := (R.card:ℝ)*J.card*L*D*E
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB0 : 0 < B := by linarith
  have hU : 1 ≤ B^p := Real.one_le_rpow hB hp
  have hV : 1 ≤ B^q := Real.one_le_rpow hB hq
  have hU0 : 0 < B^p := by positivity
  have hV0 : 0 < B^q := by positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hSc := primary_support_card_le S hU0.le (fun s hs => ⟨(hS s hs).1,(hS s hs).2.2⟩)
  have hTc := primary_support_card_le T hV0.le (fun t ht => ⟨(hT t ht).1,(hT t ht).2.2⟩)
  have hloss := sieve_epsilon_loss_p0 hB hp hq (by linarith : p+2*q ≤ 2) hε.le
  have hCp : C₁*(T.card:ℝ) ≤ L*B^q := by
    calc
      _ ≤ max C₁ C₂*(18*B^q) := mul_le_mul (le_max_left _ _) hTc (by positivity) (by positivity)
      _ = _ := by dsimp [L]; ring
  have hCq : C₁*(S.card:ℝ) ≤ L*B^p := by
    calc
      _ ≤ max C₁ C₂*(18*B^p) := mul_le_mul (le_max_left _ _) hSc (by positivity) (by positivity)
      _ = _ := by dsimp [L]; ring
  have hCo : C₂ ≤ L := by
    apply (le_max_right C₁ C₂).trans
    dsimp [L]
    nlinarith [hC₁.le.trans (le_max_left C₁ C₂)]
  have hm := hraw A R S T J H B (B^p) (B^q) hB hU hV hA hS hT hH β
  have hcp : 0 ≤ (R.card:ℝ)*J.card*C₁ := by positivity
  have hmP : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      (R.card:ℝ)*J.card*C₁*((T.card:ℝ)*(B^p*B)^ε*(B^p+B+(B^p*B)^(2/3:ℝ)))*E :=
    hm.trans (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hcp)) hE)
  have hmQ : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      (R.card:ℝ)*J.card*C₁*((S.card:ℝ)*(B^q*B)^ε*(B^q+B+(B^q*B)^(2/3:ℝ)))*E :=
    hm.trans (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hcp)) hE)
  have hmO : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      (R.card:ℝ)*J.card*C₂*(B^p*B^q)^ε*((B^p*B^q)^2+B)*E :=
    hm.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hE)
  have hP : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      F*B^(3*ε)*pSieveRatio B (B^p) (B^q) := by
    exact hmP.trans (scale_sieve_row_p0 (by positivity) (by positivity) hE
      (by positivity) (by positivity) hL.le hV0.le hCp hloss.1
      (pSieveRatio_cancel_p0 hB0 hU0 hV0))
  have hQ : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      F*B^(3*ε)*qSieveRatio B (B^p) (B^q) := by
    exact hmQ.trans (scale_sieve_row_p0 (by positivity) (by positivity) hE
      (by positivity) (by positivity) hL.le hU0.le hCq hloss.2.1
      (qSieveRatio_cancel_p0 hB0 hU0 hV0))
  have hO : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      F*B^(3*ε)*ordinarySieveRatio B (B^p) (B^q) := by
    have hh := scale_sieve_row_p0 (r := (R.card:ℝ)) (j := (J.card:ℝ))
      (C := C₂) (T := 1) (loss := (B^p*B^q)^ε) (term := B+(B^p*B^q)^2)
      (E := E) (L := L) (W := 1) (M := B^(3*ε)) (D := D)
      (ratio := ordinarySieveRatio B (B^p) (B^q))
      (by positivity) (by positivity) hE (by positivity) (by positivity) hL.le
      (by norm_num) (by simpa using hCo) hloss.2.2
      (by change (B*(B^p*(B^q)^2)^(1/3:ℝ))*ordinarySieveRatio B (B^p) (B^q) = _
          simpa only [one_mul] using ordinarySieveRatio_cancel_p0 hB0 hU0 hV0)
    apply hmO.trans
    convert hh using 1 <;> first | rfl | ring
  have hmin : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      F*(B^(3*ε)*min (pSieveRatio B (B^p) (B^q))
        (min (qSieveRatio B (B^p) (B^q)) (ordinarySieveRatio B (B^p) (B^q)))) := by
    rw [← mul_assoc,mul_min_of_nonneg _ _ (mul_nonneg hF (by positivity)),
      mul_min_of_nonneg _ _ (mul_nonneg hF (by positivity))]
    exact le_min hP (le_min hQ hO)
  apply hmin.trans
  have hsave := hgap B p q (3*ε) hB hp hq hsize hlarge hfirst hbalanced
    (by dsimp [ε]; linarith)
  have hh := mul_le_mul_of_nonneg_left hsave hF
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [F,D,E]; ring_nf)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExceptionalBenchmark
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the exceptional moments by the actual local dispersion
benchmark B²(PQ²)^(1/3), retaining a positive power saving. -/
noncomputable section
namespace CubicFirstMoment

lemma exceptional_conductor_lower {p q ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcase : (|p-1| ≤ ρ ∧ 0 ≤ q ∧ q ≤ ρ) ∨
      (|p-1/3| ≤ ρ ∧ |q-1/3| ≤ ρ)) : 1-3*ρ ≤ p+2*q := by
  rcases hcase with ⟨hp,hq,_⟩ | ⟨hp,hq⟩
  · linarith [(abs_le.mp hp).1]
  · linarith [(abs_le.mp hp).1,(abs_le.mp hq).1]

lemma conductor_rpow_identity {B : ℝ} (hB : 0 < B) (p q : ℝ) :
    (B^p*(B^q)^2)^(1/3:ℝ) = B^((p+2*q)/3) := by
  rw [← Real.rpow_natCast (B^q) 2,← Real.rpow_mul hB.le]
  norm_num only [Nat.cast_ofNat]
  rw [← Real.rpow_add hB,← Real.rpow_mul hB.le]
  congr 1
  ring

theorem exceptional_moment_benchmark {B p q ρ ε E : ℝ}
    (hB : 1 ≤ B) (hρ : 0 ≤ ρ) (hρε : ρ ≤ ε/2)
    (hcase : (|p-1| ≤ ρ ∧ 0 ≤ q ∧ q ≤ ρ) ∨
      (|p-1/3| ≤ ρ ∧ |q-1/3| ≤ ρ))
    (hE : E ≤ B^(7/3-ε)) :
    E ≤ B^2*(B^p*(B^q)^2)^(1/3:ℝ)*B^(-ε/2) := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hlo := exceptional_conductor_lower hρ hcase
  apply hE.trans
  rw [conductor_rpow_identity hBp,← Real.rpow_two,← Real.rpow_add hBp,← Real.rpow_add hBp]
  exact Real.rpow_le_rpow_of_exponent_le hB (by linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredFrequencyPolynomial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact squarefree frequency polynomial with the numerator, height and
excluded-prime factors retained in its actual coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma structuredPrimeSum_eq_frequency (h v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) :
    structuredPrimeSum h 1 v e u W X Z =
      ∑ z ∈ structuredFrequencySupport W X Z,
        structuredFrequencyCoefficient v e u W X Z z*cubicSymbol z h := by
  unfold structuredPrimeSum structuredFrequencySupport
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have hp := orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
    (fun i p hp => (coordinatePrimeSupport_primary W X Z i p hp).1) hz
  by_cases hsf : Squarefree z
  · rw [ite_eq_left hsf]
    by_cases hc : IsCoprime z e
    · simp only [ite_eq_left hc,structuredFrequencyCoefficient,one_pow,mul_one,
        cubicSymbol_mul_upper hp]
      ring
    · simp only [ite_eq_right hc,structuredFrequencyCoefficient,zero_mul]
  · have he : primeMomentCoefficient W X Z z = 0 := by
      simp only [primeMomentCoefficient,squarefreeConvolution,ite_eq_right hsf]
    simp only [he,zero_mul,ite_eq_right hsf,ite_self]

lemma structuredFrequencySupport_bounds (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) {R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (Z : ℝ) : ∀ z ∈ structuredFrequencySupport W X Z,
      primary z ∧ Squarefree z ∧ norm z ≤ R^(Fintype.card ι)*(∏ i, X i) := by
  intro z hz
  obtain ⟨hz,hsf⟩ := Finset.mem_filter.mp hz
  exact ⟨orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
    (fun i p hp => (coordinatePrimeSupport_primary W X Z i p hp).1) hz,
    hsf,(coordinatePrimeProduct_norm_bounds W X hX hR hlo hhi Z z hz).2⟩

lemma structuredFrequencyCoefficient_energy_le (v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) :
    (∑ z ∈ structuredFrequencySupport W X Z,
      ‖structuredFrequencyCoefficient v e u W X Z z‖^2) ≤
    ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
      ‖primeMomentCoefficient W X Z z‖^2 := by
  have hsub : structuredFrequencySupport W X Z ⊆
      orderedConvolutionSupport (coordinatePrimeSupport W X Z) := Finset.filter_subset _ _
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun z _ _ => sq_nonneg ‖primeMomentCoefficient W X Z z‖))
  apply Finset.sum_le_sum
  intro z hz
  have hp := orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
    (fun i p hp => (coordinatePrimeSupport_primary W X Z i p hp).1) (Finset.mem_filter.mp hz).1
  apply pow_le_pow_left₀ (_root_.norm_nonneg _)
  unfold structuredFrequencyCoefficient
  split_ifs
  · rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hp v)
  · simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogarithmicNoncube
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonexceptional frequency savings for the actual logarithmically varying
prime convolutions. Coefficient energy is proved, not supplied as an input. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma noncube_energy_absorption {C r j B D ν E A : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hj : 0 ≤ j) (hB : 0 < B) (hD : 0 ≤ D)
    (hE : E ≤ B^(1+ν/2)) (hA : A ≤ C*r*j*B*D*B^(-ν)*E) :
    A ≤ C*r*j*B^2*D*B^(-ν/2) := by
  have hm : 0 ≤ C*r*j*B*D*B^(-ν) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hr) hj) hB.le) hD)
      (Real.rpow_nonneg hB.le _)
  have hid : B^(-ν)*B^(1+ν/2) = B*B^(-ν/2) := by
    calc
      _ = B^(1-ν/2) := by rw [← Real.rpow_add hB]; congr 1; ring
      _ = B^(1:ℝ)*B^(-ν/2) := by rw [← Real.rpow_add hB]; congr 1; ring
      _ = _ := by rw [Real.rpow_one]
  calc
    A ≤ C*r*j*B*D*B^(-ν)*B^(1+ν/2) :=
      hA.trans (mul_le_mul_of_nonneg_left hE hm)
    _ = (C*r*j*B*D)*(B^(-ν)*B^(1+ν/2)) := by ring
    _ = _ := by rw [hid]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullNoncubeMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonexceptional frequency mass for the literal untruncated prime
convolution, at the same length scale as the exceptional moment bounds. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem full_logarithmic_noncube (hHuxley : HuxleyAdditiveLargeSieve)
    {κ δ R : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hR : 1 ≤ R) :
    ∃ η C ν : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < C ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ) (p q : ℝ) (v e : Eisenstein) (u : ℝ)
      (Ram S T J H : Finset Eisenstein), T₀ ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      0 ≤ p → 0 ≤ q → p+2*q ≤ 1+η → κ ≤ p+2*q →
      δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ (L r)^p) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ (L r)^q) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by
  have hK : 1 ≤ R^(Fintype.card ι) := one_le_pow₀ hR
  obtain ⟨η,C,ν,hη,hηhi,hC,hν,hraw⟩ := quantitative_dilated_noncube_mass hHuxley hK hκ hδ
  refine ⟨η,C,ν/2,hη,hηhi,hC,by positivity,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T₀,henergy⟩ := logarithmic_structured_coefficient_energy hW
    (show 0 ≤ R by linarith) (show 0 < ν/2 by positivity) hlo hhi
  refine ⟨T₀,?_⟩
  intro r X p q v e u Ram S T J H hT₀ hX hprod hp hq hsize hlarge hfirst hbalanced hS hT hH
  let Z := R/2*L r
  let A := structuredFrequencySupport (W r) X Z
  let β := structuredFrequencyCoefficient v e u (W r) X Z
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hXp : ∀ i, 0 < X i := fun i => zero_lt_one.trans_le (hX i)
  have hA : ∀ a ∈ A, primary a ∧ Squarefree a ∧ norm a ≤ R^(Fintype.card ι)*L r := by
    intro a ha
    simpa only [hprod] using structuredFrequencySupport_bounds (W r) X hXp
      (show 0 ≤ R by linarith) (hlo r) (hhi r) Z a ha
  have hE : (∑ a ∈ A, ‖β a‖^2) ≤ (L r)^(1+ν/2) :=
    (structuredFrequencyCoefficient_energy_le v e u (W r) X Z).trans
      (henergy r X Z (hL r) hT₀ hXp hprod)
  have hm := hraw (L r) p q (hL r) hp hq hsize hlarge hfirst hbalanced
    A Ram S T J H hA hS hT hH β
  have hfull (h : Eisenstein) : fullStructuredPrimeSum R h 1 v e u (W r) X =
      structuredPrimeSum h 1 v e u (W r) X Z := by
    apply fullStructuredPrimeSum_eq h 1 v e u (W r) X hXp (hhi r)
    intro i
    have hi : X i ≤ L r := by simpa only [hprod] using coordinate_le_product X hX i
    dsimp [Z]
    nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ R by linarith)]
  have heq : (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) =
      ∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2 := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [hfull h,structuredPrimeSum_eq_frequency]
  rw [heq]
  simpa only [neg_div] using noncube_energy_absorption hC.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hLp (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hLp.le _) (sq_nonneg _)) _)
    hE hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicNoncubeMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed norm dyads in the actual noncube estimate. Their factor of two
is absorbed by a strictly smaller exponent neighborhood. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma shifted_distance_bound (p q b c : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    |p-b|+|q-c| ≤ |p+a-b|+|q+a-c|+2*a := by
  have hb : |p-b| ≤ |p+a-b|+a := by
    calc
      _ = |(p+a-b)+(-a)| := by congr 1; ring
      _ ≤ |p+a-b|+|-a| := abs_add_le _ _
      _ = _ := by rw [abs_neg,abs_of_nonneg ha]
  have hc : |q-c| ≤ |q+a-c|+a := by
    calc
      _ = |(q+a-c)+(-a)| := by congr 1; ring
      _ ≤ |q+a-c|+|-a| := abs_add_le _ _
      _ = _ := by rw [abs_neg,abs_of_nonneg ha]
  linarith

lemma noncube_dyadic_shift_absorption {B C ν a : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (p q : ℝ) (ha : a ≤ ν/2) :
    C*B^2*(B^(p+a)*(B^(q+a))^2)^(1/3:ℝ)*B^(-ν) ≤
      C*B^2*(B^p*(B^q)^2)^(1/3:ℝ)*B^(-ν/2) := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have heq : (B^(p+a)*(B^(q+a))^2)^(1/3:ℝ) = (B^p*(B^q)^2)^(1/3:ℝ)*B^a := by
    rw [conductor_rpow_identity hBp,conductor_rpow_identity hBp,← Real.rpow_add hBp]
    congr 1
    ring
  rw [heq]
  calc
    _ = (C*B^2*(B^p*(B^q)^2)^(1/3:ℝ))*(B^a*B^(-ν)) := by ring
    _ = (C*B^2*(B^p*(B^q)^2)^(1/3:ℝ))*B^(a-ν) := by
      rw [← Real.rpow_add hBp]
      congr 2
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB (by linarith)) (by positivity)

theorem dyadic_full_noncube (hHuxley : HuxleyAdditiveLargeSieve)
    {κ δ R : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hR : 1 ≤ R) :
    ∃ η C ν : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < C ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ) (p q : ℝ) (v e : Eisenstein) (u : ℝ)
      (Ram S T J H : Finset Eisenstein), T₀ ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      0 ≤ p → 0 ≤ q → p+2*q ≤ 1+η → κ ≤ p+2*q →
      δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| →
      (∀ s ∈ S, gramDyad ((L r)^p) s) → (∀ t ∈ T, gramDyad ((L r)^q) t) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨η,C,ν,hη,hηhi,hC,hν,hraw⟩ := full_logarithmic_noncube (γ := γ) (ι := ι)
    hHuxley hκ (show 0 < δ/2 by positivity) hR
  let a := min η (min ν δ)/12
  have ha : 0 < a := div_pos (lt_min hη (lt_min hν hδ)) (by norm_num)
  have haη : 3*a ≤ η/2 := by dsimp [a]; linarith [min_le_left η (min ν δ)]
  have haν : a ≤ ν/2 := by dsimp [a]; linarith [(min_le_right η (min ν δ)).trans (min_le_left ν δ)]
  have haδ : 2*a ≤ δ/2 := by dsimp [a]; linarith [(min_le_right η (min ν δ)).trans (min_le_right ν δ)]
  refine ⟨η/2,C,ν/2,by positivity,by linarith,hC,by positivity,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T₁,hbound⟩ := hraw L W hL hW hlo hhi
  obtain ⟨T₂,htwo⟩ := eventually_atTop.mp ((tendsto_rpow_atTop ha).eventually_ge_atTop (2:ℝ))
  refine ⟨max T₁ T₂,?_⟩
  intro r X p q v e u Ram S T J H hT₀ hX hprod hp hq hsize hlarge hfirst hbalanced hS hT hH
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have h2 : 2 ≤ (L r)^a := htwo (L r) ((le_max_right _ _).trans hT₀)
  have hn (z t : ℝ) (hz : z < 2*(L r)^t) : z ≤ (L r)^(t+a) := by
    apply hz.le.trans
    rw [Real.rpow_add hLp]
    nlinarith [mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hLp.le t)]
  have hS' : ∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ (L r)^(p+a) :=
    fun s hs => ⟨(hS s hs).1,(hS s hs).2.1,hn _ _ (hS s hs).2.2.2⟩
  have hT' : ∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ (L r)^(q+a) :=
    fun t ht => ⟨(hT t ht).1,(hT t ht).2.1,hn _ _ (hT t ht).2.2.2⟩
  have hf : δ/2 ≤ |p+a-1|+|q+a| := by
    have hh := shifted_distance_bound p q 1 0 ha.le
    simp only [sub_zero] at hh
    linarith
  have hb : δ/2 ≤ |p+a-1/3|+|q+a-1/3| := by
    have hh := shifted_distance_bound p q (1/3) (1/3) ha.le
    linarith
  have hm := hbound r X (p+a) (q+a) v e u Ram S T J H ((le_max_left _ _).trans hT₀)
    hX hprod (by linarith) (by linarith) (by linarith) (by linarith) hf hb hS' hT' hH
  apply hm.trans
  have hh := noncube_dyadic_shift_absorption (hL r)
    (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg Ram.card)) (Nat.cast_nonneg J.card)) p q haν
  simpa only [mul_assoc,neg_div] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExceptionalCubeBound
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An exceptional conductor forces the actual cube factor to be small
when the full frequency has norm at most Y^(1+η). -/
noncomputable section
namespace CubicFirstMoment

lemma cube_factor_exceptional_bound {Y p q δ η σ x : ℝ}
    (hY : 1 ≤ Y) (hx : 0 ≤ x) (hsize : η+3*δ ≤ 3*σ)
    (hconductor : 1-3*δ ≤ p+2*q)
    (hfrequency : x^3*(Y^p*(Y^q)^2) ≤ Y^(1+η)) : x ≤ Y^σ := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hσ : (Y^σ)^3 = Y^(3*σ) := by
    rw [← Real.rpow_natCast (Y^σ) 3,← Real.rpow_mul hYp.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hq : (Y^q)^2 = Y^(2*q) := by
    rw [← Real.rpow_natCast (Y^q) 2,← Real.rpow_mul hYp.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have heq : (Y^σ)^3*(Y^p*(Y^q)^2) = Y^(3*σ+p+2*q) := by
    rw [hσ,hq,← Real.rpow_add hYp,← Real.rpow_add hYp]
    congr 1
    ring
  have hbound : Y^(1+η) ≤ (Y^σ)^3*(Y^p*(Y^q)^2) := by
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  have hprod : 0 < Y^p*(Y^q)^2 := mul_pos (Real.rpow_pos_of_pos hYp _)
    (sq_pos_of_pos (Real.rpow_pos_of_pos hYp _))
  have hcube : x^3 ≤ (Y^σ)^3 := (mul_le_mul_iff_left₀ hprod).mp
    (by simpa only [mul_comm] using hfrequency.trans hbound)
  exact (pow_le_pow_iff_left₀ hx (Real.rpow_nonneg hYp.le _) (by norm_num : (3:ℕ) ≠ 0)).mp hcube

lemma moment_constant_saving_mono {A B C D ν μ : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hCD : C ≤ D) (hB : 1 ≤ B) (hμν : μ ≤ ν) :
    C*A*B^(-ν) ≤ D*A*B^(-μ) := by
  exact mul_le_mul (mul_le_mul_of_nonneg_right hCD hA)
    (Real.rpow_le_rpow_of_exponent_le hB (by linarith))
    (Real.rpow_nonneg (by linarith) _) (mul_nonneg (hC.trans hCD) hA)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExceptionalStructuredMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both exceptional conductor neighborhoods for the original structured
prime sum, with common constants and the actual finite pair set. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exceptional_structured_moment (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (J : ℕ) (hJ : 2*R^(Fintype.card ι) ≤ (4/3:ℝ)^J)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T : ℝ, ∀ (r : γ) (X : ι → ℝ) (v e : Eisenstein) (u p q : ℝ)
      (P : Finset (Eisenstein × Eisenstein)), T ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) → (∀ i, X i ≤ L r) →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^ρ → norm e ≤ (L r)^ρ → |u| ≤ (L r)^(9/25:ℝ) →
      (∀ z ∈ P, gramDyad ((L r)^p) z.1 ∧ gramDyad ((L r)^q) z.2 ∧ IsCoprime z.1 z.2) →
      ((|p-1| ≤ ρ ∧ 0 ≤ q ∧ q ≤ ρ) ∨ (|p-1/3| ≤ ρ ∧ |q-1/3| ≤ ρ)) →
      (∑ z ∈ P, ‖structuredPrimeSum z.1 z.2 v e u (W r) X (((4/3:ℝ)^J/2)*L r)‖^2) ≤
        (L r)^(7/3-ε) := by
  obtain ⟨d₁,hd₁,_,e₁,he₁,hfirst⟩ := first_unweighted_structured_moment
    (γ := γ) (ι := ι) hpub hperiod hc hc₁ hR J hJ hGI hGQ
  obtain ⟨d₂,hd₂,_,e₂,he₂,hbalanced⟩ := balanced_unweighted_structured_moment
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR J hJ hGI hGQ
  let ρ := min d₁ d₂/4
  have hρ : 0 < ρ := div_pos (lt_min hd₁ hd₂) (by norm_num)
  have hρ₁ : ρ < d₁ := by dsimp [ρ]; linarith [min_le_left d₁ d₂]
  have hρ₂ : ρ < d₂ := by dsimp [ρ]; linarith [min_le_right d₁ d₂]
  refine ⟨ρ,min e₁ e₂,hρ,lt_min he₁ he₂,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T₁,hF⟩ := hfirst L W hL hW hlo hhi
  obtain ⟨T₂,hB⟩ := hbalanced L W hL hW hlo hhi
  obtain ⟨T₃,hsmall⟩ := eventually_atTop.mp (eventually_const_mul_rpow_le hρ₁ 2)
  obtain ⟨T₄,hupper⟩ := eventually_atTop.mp (eventually_const_mul_rpow_le
    (by linarith : 1/3+ρ < 1/3+d₂) 2)
  refine ⟨max (max T₁ T₂) (max T₃ T₄),?_⟩
  intro r X v e u p q P hT hprod hXlo hXhi hv he hvY heY hu hP hcase
  have hT₁ : T₁ ≤ L r := (le_max_left T₁ T₂).trans ((le_max_left _ _).trans hT)
  have hT₂ : T₂ ≤ L r := (le_max_right T₁ T₂).trans ((le_max_left _ _).trans hT)
  have hT₃ : T₃ ≤ L r := (le_max_left T₃ T₄).trans ((le_max_right _ _).trans hT)
  have hT₄ : T₄ ≤ L r := (le_max_right T₃ T₄).trans ((le_max_right _ _).trans hT)
  have hv₁ := hvY.trans (Real.rpow_le_rpow_of_exponent_le (hL r) hρ₁.le)
  have he₁' := heY.trans (Real.rpow_le_rpow_of_exponent_le (hL r) hρ₁.le)
  have hv₂ := hvY.trans (Real.rpow_le_rpow_of_exponent_le (hL r) hρ₂.le)
  have he₂' := heY.trans (Real.rpow_le_rpow_of_exponent_le (hL r) hρ₂.le)
  rcases hcase with ⟨hp,hqlo,hqhi⟩ | ⟨hp,hq⟩
  · let A := P.image Prod.fst
    let B := P.image Prod.snd
    have hNlo : (L r)^(1-d₁) ≤ (L r)^p :=
      Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [(abs_le.mp hp).1])
    have hNhi : (L r)^p ≤ (L r)^(1+d₁) :=
      Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [(abs_le.mp hp).2])
    have hA : ∀ a ∈ A, gramDyad ((L r)^p) a := by
      intro a ha
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
      exact (hP z hz).1
    have hB' : ∀ b ∈ B, primary b ∧ norm b ≤ (L r)^d₁ := by
      intro b hb
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
      have hz' := (hP z hz).2.1
      refine ⟨hz'.1,?_⟩
      apply hz'.2.2.2.le.trans
      exact (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hL r) hqhi) (by norm_num)).trans (hsmall (L r) hT₃)
    have hb := hF r ((L r)^p) X v e u A B hT₁ hNlo hNhi hprod hXlo hXhi
      hv he hv₁ he₁' hu hA hB'
    have hsub : P ⊆ A ×ˢ B := fun z hz => Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hz,Finset.mem_image_of_mem _ hz⟩
    calc
      _ ≤ ∑ z ∈ A ×ˢ B,
          ‖structuredPrimeSum z.1 z.2 v e u (W r) X (((4/3:ℝ)^J/2)*L r)‖^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ = ∑ b ∈ B, ∑ a ∈ A,
          ‖structuredPrimeSum a b v e u (W r) X (((4/3:ℝ)^J/2)*L r)‖^2 := by
        rw [Finset.sum_product,Finset.sum_comm]
      _ ≤ (L r)^(7/3-e₁) := hb
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [min_le_left e₁ e₂])
  · have hrows : ∀ z ∈ P, PrimarySquarefreePair z ∧
        norm z.1 ≤ (L r)^(1/3+d₂) ∧ norm z.2 ≤ (L r)^(1/3+d₂) ∧
        (L r)^(1/3-d₂) ≤ norm z.1 := by
      intro z hz
      obtain ⟨hzp,hzq,hcop⟩ := hP z hz
      refine ⟨⟨hzp.1,hzq.1,hzp.2.1,hzq.2.1,hcop⟩,?_,?_,?_⟩
      · apply hzp.2.2.2.le.trans
        exact (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [(abs_le.mp hp).2]))
          (by norm_num)).trans (hupper (L r) hT₄)
      · apply hzq.2.2.2.le.trans
        exact (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [(abs_le.mp hq).2]))
          (by norm_num)).trans (hupper (L r) hT₄)
      · exact (Real.rpow_le_rpow_of_exponent_le (hL r)
          (by linarith [(abs_le.mp hp).1])).trans hzp.2.2.1
    exact (hB r X v e u P hT₂ hprod hXlo hXhi hv he hv₂ he₂' hu hrows).trans
      (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [min_le_right e₁ e₂]))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullExceptionalMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional moment estimate for the literal, untruncated ordered
prime convolution. The finite output partition is chosen inside the proof. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem full_exceptional_structured_moment (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T : ℝ, ∀ (r : γ) (X : ι → ℝ) (v e : Eisenstein) (u p q : ℝ)
      (P : Finset (Eisenstein × Eisenstein)), T ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^ρ → norm e ≤ (L r)^ρ →
      1+|u| ≤ (L r)^(9/25:ℝ) →
      (∀ z ∈ P, gramDyad ((L r)^p) z.1 ∧ gramDyad ((L r)^q) z.2 ∧ IsCoprime z.1 z.2) →
      ((|p-1| ≤ ρ ∧ 0 ≤ q ∧ q ≤ ρ) ∨ (|p-1/3| ≤ ρ ∧ |q-1/3| ≤ ρ)) →
      (∑ z ∈ P, ‖fullStructuredPrimeSum R z.1 z.2 v e u (W r) X‖^2) ≤
        (L r)^(7/3-ε) := by
  obtain ⟨J,hJ⟩ := pow_unbounded_of_one_lt (2*R^(Fintype.card ι))
    (by norm_num : (1:ℝ) < 4/3)
  obtain ⟨ρ,ε,hρ,hε,hraw⟩ := exceptional_structured_moment (γ := γ) (ι := ι)
    hpub hHuxley hperiod hc hc₁ hR J hJ.le hGI hGQ
  refine ⟨ρ,ε,hρ,hε,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T,hbound⟩ := hraw L W hL hW hlo hhi
  refine ⟨T,?_⟩
  intro r X v e u p q P hT hprod hXlo hv he hvL heL hu hP hcase
  have hXone : ∀ i, 1 ≤ X i := fun i => (Real.one_le_rpow
    (show 1 ≤ 2*L r by linarith [hL r]) hc.le).trans (hXlo i).le
  have hXhi : ∀ i, X i ≤ L r := fun i => by
    simpa only [hprod] using coordinate_le_product X hXone i
  have hb := hbound r X v e u p q P hT hprod hXlo hXhi hv he hvL heL
    (by linarith : |u| ≤ (L r)^(9/25:ℝ)) hP hcase
  have heq : (∑ z ∈ P, ‖fullStructuredPrimeSum R z.1 z.2 v e u (W r) X‖^2) =
      ∑ z ∈ P, ‖structuredPrimeSum z.1 z.2 v e u (W r) X (((4/3:ℝ)^J/2)*L r)‖^2 := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [fullStructuredPrimeSum_partition_cutoff hR J hJ.le z.1 z.2 v e u (W r) X hXone (hhi r),hprod]
  exact heq.trans_le hb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExceptionalResidualMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional structured estimate on the actual ramified/cube
frequency block, including its local dispersion normalization. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma double_sum_real_const (S T : Finset Eisenstein) (x : ℝ) :
    (∑ _s ∈ S, ∑ _t ∈ T, x) = (S.card:ℝ)*T.card*x := by
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

lemma norm_mul_small_power {Y δ ρ : ℝ} (hY : 1 ≤ Y) (hδ : 2*δ ≤ ρ)
    {v r : Eisenstein} (hv : norm v ≤ Y^δ) (hr : norm r ≤ Y^δ) : norm (v*r) ≤ Y^ρ := by
  rw [norm_mul_eq]
  calc
    _ ≤ Y^δ*Y^δ := mul_le_mul hv hr (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
    _ = Y^(2*δ) := by rw [← Real.rpow_add (by linarith : 0 < Y)]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY hδ

theorem exceptional_residual_moment (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ δ ν : ℝ, 0 < δ ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T : ℝ, ∀ (r : γ) (X : ι → ℝ) (v e : Eisenstein) (u p q : ℝ)
      (Ram J H : Finset Eisenstein) (P : Finset (Eisenstein × Eisenstein)), T ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^δ → norm e ≤ (L r)^δ →
      1+|u| ≤ (L r)^(9/25:ℝ) →
      (∀ a ∈ Ram, a ≠ 0 ∧ norm a ≤ (L r)^δ) →
      (∀ j ∈ J, j ≠ 0 ∧ norm j ≤ (L r)^δ) →
      (∀ z ∈ P, gramDyad ((L r)^p) z.1 ∧ gramDyad ((L r)^q) z.2 ∧ IsCoprime z.1 z.2) →
      ((|p-1| ≤ δ ∧ 0 ≤ q ∧ q ≤ δ) ∨ (|p-1/3| ≤ δ ∧ |q-1/3| ≤ δ)) →
      H ⊆ coprimeResidualSupport Ram J P →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        (Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨ρ,ε,hρ,hε,hraw⟩ := full_exceptional_structured_moment (γ := γ) (ι := ι)
    hpub hHuxley hperiod hc hc₁ hR hGI hGQ
  let δ := min ρ ε/4
  have hδ : 0 < δ := div_pos (lt_min hρ hε) (by norm_num)
  have hδρ : 2*δ ≤ ρ := by dsimp [δ]; linarith [min_le_left ρ ε]
  have hδρ' : δ ≤ ρ := by linarith
  have hδε : δ ≤ ε/2 := by dsimp [δ]; linarith [min_le_right ρ ε]
  refine ⟨δ,ε/2,hδ,by positivity,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T,hbound⟩ := hraw L W hL hW hlo hhi
  refine ⟨T,?_⟩
  intro r X v e u p q Ram J H P hT hprod hX hv he hvL heL hu hRam hJ hP hcase hH
  have hcase' : (|p-1| ≤ ρ ∧ 0 ≤ q ∧ q ≤ ρ) ∨ (|p-1/3| ≤ ρ ∧ |q-1/3| ≤ ρ) := by
    rcases hcase with ⟨hp,hq,hq'⟩ | ⟨hp,hq⟩
    · exact Or.inl ⟨hp.trans hδρ',hq,hq'.trans hδρ'⟩
    · exact Or.inr ⟨hp.trans hδρ',hq.trans hδρ'⟩
  have hb (a : Eisenstein) (ha : a ∈ Ram) (j : Eisenstein) (hj : j ∈ J) :
      (∑ z ∈ P, ‖fullStructuredPrimeSum R z.1 z.2 (v*a) (e*j) u (W r) X‖^2) ≤
        (L r)^(7/3-ε) := hbound r X (v*a) (e*j) u p q P hT hprod hX
      (mul_ne_zero hv (hRam a ha).1) (mul_ne_zero he (hJ j hj).1)
      (norm_mul_small_power (hL r) hδρ hvL (hRam a ha).2)
      (norm_mul_small_power (hL r) hδρ heL (hJ j hj).2) hu hP hcase'
  have hbenchmark := exceptional_moment_benchmark (hL r) hδ.le hδε hcase
    (le_rfl : (L r)^(7/3-ε) ≤ (L r)^(7/3-ε))
  calc
    _ ≤ ∑ a ∈ Ram, ∑ j ∈ J, ∑ z ∈ P,
        ‖fullStructuredPrimeSum R z.1 z.2 (v*a) (e*j) u (W r) X‖^2 :=
      fullStructured_residual_mass_le R Ram J H P hH v e u (W r) X
    _ ≤ ∑ _a ∈ Ram, ∑ _j ∈ J, (L r)^(7/3-ε) :=
      Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun j hj => hb a ha j hj))
    _ = (Ram.card:ℝ)*J.card*(L r)^(7/3-ε) := double_sum_real_const Ram J _
    _ ≤ (Ram.card:ℝ)*J.card*((L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ε/2)) :=
      mul_le_mul_of_nonneg_left hbenchmark (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by rw [neg_div]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogCoefficientEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit logarithmic, rather than subpower, energy of the actual
full prime convolution. This is used in the small-conductor sieve range. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem logarithmic_full_coefficient_energy {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ (r : γ) (X : ι → ℝ),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      (∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R (W r) X),
        ‖fullPrimeCoefficient R (W r) X z‖^2) ≤
        C*L r*(1+Real.log (L r))^A := by
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  let n := Fintype.card ι
  let C := 18*R^n*((n^n:ℕ)*M^n)^2
  refine ⟨C,2*m*n,?_,?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans hR) _)) (sq_nonneg _)
  intro r X hL hX hprod
  let Z := R/2*L r
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have heq : fullPrimeSupport R (W r) X = coordinatePrimeSupport (W r) X Z := by
    simpa only [Z,hprod] using fullPrimeSupport_eq_product_cutoff (zero_le_one.trans hR)
      (W r) X hX (hhi r)
  have hb := structuredCoefficient_energy_le (W r) X
    (fun _ => M*(1+Real.log (L r))^m) (fun i => zero_lt_one.trans_le (hX i))
    (zero_le_one.trans hR) (hlo r) (hhi r)
    (fun _ => mul_nonneg hM (pow_nonneg hz _)) (fun i x => hMb (r,i) x) Z
  have hcoeff : fullPrimeCoefficient R (W r) X = fun z => primeMomentCoefficient (W r) X Z z := by
    funext z
    unfold fullPrimeCoefficient primeMomentCoefficient
    rw [heq]
  rw [heq,hcoeff]
  apply hb.trans_eq
  rw [hprod,Finset.prod_const,Finset.card_univ,mul_pow,← pow_mul]
  dsimp only [C,n]
  rw [mul_pow,mul_pow,← pow_mul]
  have hm : m*(Fintype.card ι*2) = 2*m*Fintype.card ι := by ring
  rw [hm,pow_mul M (Fintype.card ι) 2]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullOrdinaryMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary sieve on the actual full convolution, retaining precise
logarithmic weight costs. It applies also below every fixed conductor power. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem full_ordinary_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε)
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (C : ℝ) (a : ℕ), 0 < C ∧ ∀ (r : γ) (X : ι → ℝ) (U V : ℝ)
      (v e : Eisenstein) (u : ℝ) (Ram S T J H : Finset Eisenstein),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → 1 ≤ U → 1 ≤ V →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(U*V)^ε*((U*V)^2+L r)*L r*(1+Real.log (L r))^a := by
  obtain ⟨C₀,a,hC₀,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  obtain ⟨C₁,C₂,_,hC₂,hsieve⟩ := dilated_noncube_three_sieve_bounds hHuxley
    (one_le_pow₀ hR : 1 ≤ R^(Fintype.card ι)) hε
  refine ⟨C₂*(C₀+1),a,mul_pos hC₂ (by linarith),?_⟩
  intro r X U V v e u Ram S T J H hL hX hprod hU hV hS hT hH
  let Z := R/2*L r
  let B := structuredFrequencySupport (W r) X Z
  let β := structuredFrequencyCoefficient v e u (W r) X Z
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hXp : ∀ i, 0 < X i := fun i => zero_lt_one.trans_le (hX i)
  have hB : ∀ b ∈ B, primary b ∧ Squarefree b ∧ norm b ≤ R^(Fintype.card ι)*L r := by
    intro b hb
    simpa only [hprod] using structuredFrequencySupport_bounds (W r) X hXp
      (zero_le_one.trans hR) (hlo r) (hhi r) Z b hb
  have heq : fullPrimeSupport R (W r) X = coordinatePrimeSupport (W r) X Z := by
    simpa only [Z,hprod] using fullPrimeSupport_eq_product_cutoff (zero_le_one.trans hR)
      (W r) X hX (hhi r)
  have hE : (∑ b ∈ B, ‖β b‖^2) ≤ (C₀+1)*L r*(1+Real.log (L r))^a := by
    apply (structuredFrequencyCoefficient_energy_le v e u (W r) X Z).trans
    have hb := henergy r X hL hX hprod
    change (∑ b ∈ orderedConvolutionSupport (coordinatePrimeSupport (W r) X Z),
      ‖primeMomentCoefficient (W r) X Z b‖^2) ≤ _
    have hb' : (∑ b ∈ orderedConvolutionSupport (coordinatePrimeSupport (W r) X Z),
        ‖primeMomentCoefficient (W r) X Z b‖^2) ≤ C₀*L r*(1+Real.log (L r))^a := by
      simpa only [fullPrimeCoefficient,primeMomentCoefficient,heq] using hb
    exact hb'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : C₀ ≤ C₀+1) hLp.le) (pow_nonneg hz _))
  have hm := hsieve B Ram S T J H (L r) U V hL hU hV hB hS hT hH β
  have hbound := hm.trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hfull (h : Eisenstein) : fullStructuredPrimeSum R h 1 v e u (W r) X =
      structuredPrimeSum h 1 v e u (W r) X Z := by
    apply fullStructuredPrimeSum_eq h 1 v e u (W r) X hXp (hhi r)
    intro i
    have hi : X i ≤ L r := by simpa only [hprod] using coordinate_le_product X hX i
    dsimp [Z]
    nlinarith [mul_le_mul_of_nonneg_left hi (zero_le_one.trans hR)]
  have hsum : (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) =
      ∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2 := by
    apply Finset.sum_congr rfl
    intro h _
    rw [hfull,structuredPrimeSum_eq_frequency]
  rw [hsum]
  apply hbound.trans
  calc
    _ ≤ ((Ram.card:ℝ)*J.card*C₂*(U*V)^ε*((U*V)^2+L r))*
        ((C₀+1)*L r*(1+Real.log (L r))^a) :=
      mul_le_mul_of_nonneg_left hE
        (mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hC₂.le)
          (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans hU) (zero_le_one.trans hV)) _))
          (add_nonneg (sq_nonneg _) hLp.le))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeConductorMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single saving across the entire large-conductor region. The cube
factor is proved small where the exceptional moment is needed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem large_conductor_structured_moment (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R κ : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R) (hκ : 0 < κ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ η σ C ν : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < C ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ) (p q : ℝ) (v e : Eisenstein) (u : ℝ)
      (Ram S T J H : Finset Eisenstein), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      0 ≤ p → 0 ≤ q → p+2*q ≤ 1+η → κ ≤ p+2*q →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^σ → norm e ≤ (L r)^σ →
      1+|u| ≤ (L r)^(9/25:ℝ) →
      (∀ a ∈ Ram, a ≠ 0 ∧ norm a ≤ (L r)^σ) →
      (∀ j ∈ J, j ≠ 0 ∧ norm j^3*((L r)^p*((L r)^q)^2) ≤ (L r)^(1+η)) →
      (∀ s ∈ S, gramDyad ((L r)^p) s) → (∀ t ∈ T, gramDyad ((L r)^q) t) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨σ,νE,hσ,hνE,hE⟩ := exceptional_residual_moment (γ := γ) (ι := ι)
    hpub hHuxley hperiod hc hc₁ hR hGI hGQ
  let δ := σ/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ηN,CN,νN,hηN,hηNhi,hCN,hνN,hN⟩ := dyadic_full_noncube (γ := γ) (ι := ι)
    hHuxley hκ hδ hR
  let η := min ηN (σ/8)
  let C := max 1 CN
  let ν := min νE νN
  have hη : 0 < η := lt_min hηN (by positivity)
  have hηhi : η ≤ 1 := (min_le_left _ _).trans hηNhi
  have hδσ : δ ≤ σ := by dsimp [δ]; linarith
  have hηδ : η+3*δ ≤ 3*σ := by dsimp [η,δ]; linarith [min_le_right ηN (σ/8)]
  refine ⟨η,σ,C,ν,hη,hηhi,hσ,lt_of_lt_of_le zero_lt_one (le_max_left _ _),lt_min hνE hνN,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨TE,hBE⟩ := hE L W hL hW hlo hhi
  obtain ⟨TN,hBN⟩ := hN L W hL hW hlo hhi
  refine ⟨max TE TN,?_⟩
  intro r X p q v e u Ram S T J H hT₀ hprod hX hp hq hsize hlarge hv he hvL heL hu hRam hJ hS hT hH
  let A := (Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)
  have hA : 0 ≤ A :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (sq_nonneg _)) (Real.rpow_nonneg
        (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hL r)) _) (sq_nonneg _)) _)
  have hXone : ∀ i, 1 ≤ X i := fun i => (Real.one_le_rpow
    (show 1 ≤ 2*L r by linarith [hL r]) hc.le).trans (hX i).le
  have hPE : ∀ z ∈ coprimePairs S T,
      gramDyad ((L r)^p) z.1 ∧ gramDyad ((L r)^q) z.2 ∧ IsCoprime z.1 z.2 := by
    intro z hz
    have hh := Finset.mem_filter.mp hz
    have hz' := Finset.mem_product.mp hh.1
    exact ⟨hS z.1 hz'.1,hT z.2 hz'.2,hh.2⟩
  have exceptional (hcase : (|p-1| ≤ δ ∧ 0 ≤ q ∧ q ≤ δ) ∨
      (|p-1/3| ≤ δ ∧ |q-1/3| ≤ δ)) :
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤ C*A*(L r)^(-ν) := by
    have hcE : (|p-1| ≤ σ ∧ 0 ≤ q ∧ q ≤ σ) ∨ (|p-1/3| ≤ σ ∧ |q-1/3| ≤ σ) := by
      rcases hcase with ⟨hp,hq,hq'⟩ | ⟨hp,hq⟩
      · exact Or.inl ⟨hp.trans hδσ,hq,hq'.trans hδσ⟩
      · exact Or.inr ⟨hp.trans hδσ,hq.trans hδσ⟩
    have hjE : ∀ j ∈ J, j ≠ 0 ∧ norm j ≤ (L r)^σ := by
      intro j hj
      exact ⟨(hJ j hj).1,cube_factor_exceptional_bound (hL r) (norm_nonneg j) hηδ
        (exceptional_conductor_lower hδ.le hcase) (hJ j hj).2⟩
    have hh := hBE r X v e u p q Ram J H (coprimePairs S T) ((le_max_left _ _).trans hT₀)
      hprod hX hv he hvL heL hu hRam hjE hPE hcE hH
    have hs := moment_constant_saving_mono hA (show (0:ℝ) ≤ 1 by norm_num)
      (show (1:ℝ) ≤ C from le_max_left _ _) (hL r) (min_le_left νE νN)
    apply hh.trans
    simpa only [one_mul,A,mul_assoc] using hs
  have goal_eq : C*A*(L r)^(-ν) =
      C*(Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by dsimp [A]; ring
  rw [← goal_eq]
  by_cases hf : δ ≤ |p-1|+|q|
  · by_cases hb : δ ≤ |p-1/3|+|q-1/3|
    · have hh := hBN r X p q v e u Ram S T J H ((le_max_right _ _).trans hT₀)
        hXone hprod hp hq (hsize.trans (by dsimp [η]; linarith [min_le_left ηN (σ/8)]))
        hlarge hf hb hS hT hH
      have hs := moment_constant_saving_mono hA hCN.le (show CN ≤ C from le_max_right _ _)
        (hL r) (min_le_right νE νN)
      apply hh.trans
      simpa only [A,mul_assoc] using hs
    · apply exceptional (Or.inr ?_)
      constructor <;> linarith [lt_of_not_ge hb,abs_nonneg (p-1/3),abs_nonneg (q-1/3)]
  · apply exceptional (Or.inl ?_)
    have hh : |p-1|+q < δ := by simpa only [abs_of_nonneg hq] using lt_of_not_ge hf
    exact ⟨by linarith, hq, by linarith [abs_nonneg (p-1)]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RealScaleLargeMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The large-conductor estimate in the actual real dyadic scales.
The exponents are constructed from logarithms, not supplied as extra data. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma momentScaleExponent_nonneg {L U : ℝ} (hL : 1 < L) (hU : 1 ≤ U) :
    0 ≤ momentScaleExponent L U := div_nonneg (Real.log_nonneg hU) (Real.log_pos hL).le

lemma rpow_momentScaleExponent {L U : ℝ} (hL : 1 < L) (hU : 0 < U) :
    L^(momentScaleExponent L U) = U := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hL)]
  unfold momentScaleExponent
  rw [show Real.log L*(Real.log U/Real.log L) = Real.log U by
    field_simp [(Real.log_pos hL).ne'],Real.exp_log hU]

lemma rpow_conductor_exponent {L : ℝ} (hL : 0 < L) (p q : ℝ) :
    L^(p+2*q) = L^p*(L^q)^2 := by
  rw [Real.rpow_add hL]
  congr 1
  rw [← Real.rpow_natCast (L^q) 2,← Real.rpow_mul hL.le]
  congr 1
  push_cast
  ring

theorem large_conductor_real_scales (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R κ : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R) (hκ : 0 < κ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ η σ C ν : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < C ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ) (U V : ℝ) (v e : Eisenstein) (u : ℝ)
      (Ram S T J H : Finset Eisenstein), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ U → 1 ≤ V → U*V^2 ≤ (L r)^(1+η) → (L r)^κ ≤ U*V^2 →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^σ → norm e ≤ (L r)^σ →
      1+|u| ≤ (L r)^(9/25:ℝ) →
      (∀ a ∈ Ram, a ≠ 0 ∧ norm a ≤ (L r)^σ) →
      (∀ j ∈ J, j ≠ 0 ∧ norm j^3*(U*V^2) ≤ (L r)^(1+η)) →
      (∀ s ∈ S, gramDyad U s) → (∀ t ∈ T, gramDyad V t) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*(U*V^2)^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨η,σ,C,ν,hη,hη₁,hσ,hC,hν,hbound⟩ :=
    large_conductor_structured_moment (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hκ hGI hGQ
  refine ⟨η,σ,C,ν,hη,hη₁,hσ,hC,hν,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T₀,hbound⟩ := hbound L W hL hW hlo hhi
  refine ⟨max T₀ 2,?_⟩
  intro r X U V v e u Ram S T J H hT₀ hprod hX hU hV hsize hlarge hv he hvN heN hu hRam hJ hS hT hH
  have hLgt : 1 < L r := by linarith [le_trans (le_max_right T₀ 2) hT₀]
  let p := momentScaleExponent (L r) U
  let q := momentScaleExponent (L r) V
  have hp : (L r)^p = U := rpow_momentScaleExponent hLgt (zero_lt_one.trans_le hU)
  have hq : (L r)^q = V := rpow_momentScaleExponent hLgt (zero_lt_one.trans_le hV)
  have hD : (L r)^(p+2*q) = U*V^2 := by
    rw [rpow_conductor_exponent (zero_lt_one.trans hLgt),hp,hq]
  have hsize' : p+2*q ≤ 1+η := (Real.rpow_le_rpow_left_iff hLgt).mp (by simpa only [hD] using hsize)
  have hlarge' : κ ≤ p+2*q := (Real.rpow_le_rpow_left_iff hLgt).mp (by simpa only [hD] using hlarge)
  have hh := hbound r X p q v e u Ram S T J H ((le_max_left _ _).trans hT₀)
    hprod hX (momentScaleExponent_nonneg hLgt hU) (momentScaleExponent_nonneg hLgt hV)
    hsize' hlarge' hv he hvN heN hu hRam
    (by simpa only [hp,hq] using hJ) (by simpa only [hp] using hS)
    (by simpa only [hq] using hT) hH
  simpa only [hp,hq] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeCoreBlockMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved large-conductor estimate on the concrete frequency cover;
the cube-factor count cancels its conductor weight. -/
noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem large_core_block_moment (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R κ : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R) (hκ : 0 < κ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ η σ C ν : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < C ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (i j : ℕ)
      (v e : Eisenstein) (u : ℝ) (H : Finset Eisenstein), T₀ ≤ L r →
      (∏ a, X a) = L r → (∀ a, (2*L r)^c < X a) →
      0 ≤ B → B ≤ (L r)^(1+η) → coreDyadicConductor i j ≤ B →
      (L r)^κ ≤ coreDyadicConductor i j →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^σ → norm e ≤ (L r)^σ →
      1+|u| ≤ (L r)^(9/25:ℝ) → H ⊆ coreDyadicBlock B i j →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨η,σ,C,ν,hη,hη₁,hσ,hC,hν,hbound⟩ :=
    large_conductor_real_scales (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hκ hGI hGQ
  let K : ℝ := (nonzeroNormBall 729).card
  have hK : 0 < K := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    exact ⟨1,mem_nonzeroNormBall.mpr ⟨by norm_num [norm_one_eq],one_ne_zero⟩⟩
  refine ⟨η,σ,18*C*K,ν,hη,hη₁,hσ,by positivity,hν,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T₁,hbound⟩ := hbound L W hL hW hlo hhi
  obtain ⟨T₂,h729⟩ := eventually_atTop.mp ((tendsto_rpow_atTop hσ).eventually_ge_atTop (729:ℝ))
  refine ⟨max T₁ T₂,?_⟩
  intro r X B i j v e u H hT₀ hprod hX hB hBL hDB hlarge hv he hvN heN hu hH
  have h729' : 729 ≤ (L r)^σ := h729 _ ((le_max_right _ _).trans hT₀)
  have hRam : ∀ a ∈ nonzeroNormBall 729, a ≠ 0 ∧ norm a ≤ (L r)^σ := by
    intro a ha
    have hm := mem_nonzeroNormBall.mp ha
    exact ⟨hm.2,hm.1.trans h729'⟩
  have hJ : ∀ a ∈ coreDyadicCubeFactors B i j, a ≠ 0 ∧
      norm a^3*((2:ℝ)^i*((2:ℝ)^j)^2) ≤ (L r)^(1+η) := by
    intro a ha
    have hm := coreDyadicCubeFactors_spec hB ha
    exact ⟨hm.1,hm.2.trans hBL⟩
  have hh := hbound r X ((2:ℝ)^i) ((2:ℝ)^j) v e u
    (nonzeroNormBall 729) (squarefreePrimaryDyad i) (squarefreePrimaryDyad j)
    (coreDyadicCubeFactors B i j) H ((le_max_left _ _).trans hT₀)
    hprod hX (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
    (hDB.trans hBL) hlarge hv he hvN heN hu hRam hJ
    (fun _ ha => squarefreePrimaryDyad_gramDyad ha)
    (fun _ ha => squarefreePrimaryDyad_gramDyad ha) hH
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left (coreDyadicCubeFactors_card_weight hB i j)
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le hK.le) (sq_nonneg (L r)))
      (Real.rpow_nonneg (zero_le_one.trans (hL r)) (-ν)))
  convert hm using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [K,coreDyadicConductor] <;> ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeCutoffPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical margins for the three actual noncube conductor regions. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma small_core_ordinary_window {L U V : ℝ} (hL : 0 ≤ L) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hsmall : U*V^2 ≤ L^(1/4:ℝ)) (hmargin : 16*L^(1/2:ℝ) ≤ L) :
    (4*U*V)^2 ≤ L := by
  have hUV : U*V ≤ U*V^2 := by
    have hvv : V ≤ V^2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hvv (by linarith)
  have he : (L^(1/4:ℝ))^2 = L^(1/2:ℝ) := by
    rw [← Real.rpow_natCast _ 2,← Real.rpow_mul hL]
    norm_num
  calc
    _ = 16*(U*V)^2 := by ring
    _ ≤ 16*(L^(1/4:ℝ))^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (hUV.trans hsmall) 2) (by norm_num)
    _ = 16*L^(1/2:ℝ) := by rw [he]
    _ ≤ L := hmargin

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallConductorLogPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary small-conductor bound becomes an arbitrary logarithmic
saving above an explicit logarithmic conductor threshold. -/
noncomputable section
namespace CubicFirstMoment

lemma ordinary_small_conductor_power {U V L : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hL : 0 ≤ L) (hsize : (U*V)^2 ≤ L) :
    (U*V)^(1/12:ℝ)*((U*V)^2+L)*L ≤
      2*L^2*(U*V^2)^(1/3:ℝ)*(U*V^2)^(-(1/4:ℝ)) := by
  have hUV : 0 < U*V := mul_pos (zero_lt_one.trans_le hU) (zero_lt_one.trans_le hV)
  have hD : 0 < U*V^2 := mul_pos (zero_lt_one.trans_le hU) (pow_pos (zero_lt_one.trans_le hV) _)
  have hcomp : U*V ≤ U*V^2 := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  have he : (U*V^2)^(1/3:ℝ)*(U*V^2)^(-(1/4:ℝ)) = (U*V^2)^(1/12:ℝ) := by
    rw [← Real.rpow_add hD]
    norm_num
  rw [mul_assoc (2*L^2),he]
  calc
    _ ≤ (U*V^2)^(1/12:ℝ)*(2*L)*L := mul_le_mul_of_nonneg_right
      (mul_le_mul (Real.rpow_le_rpow hUV.le hcomp (by norm_num)) (by linarith)
        (by positivity) (Real.rpow_nonneg hD.le _)) hL
    _ = _ := by ring

lemma conductor_log_tail {D z : ℝ} (hD : 0 < D) (hz : 1 ≤ z) (a k : ℕ)
    (hlarge : z^(4*(a+k)) ≤ D) :
    D^(-(1/4:ℝ))*z^a ≤ 1/z^k := by
  have hzp : 0 < z := zero_lt_one.trans_le hz
  have hp : z^(a+k) ≤ D^(1/4:ℝ) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hzp.le (4*(a+k))) hlarge (by norm_num : (0:ℝ) ≤ 1/4)
    rw [← Real.rpow_natCast z (4*(a+k)),← Real.rpow_mul hzp.le] at hh
    have he : ((4*(a+k):ℕ):ℝ)*(1/4) = (a+k:ℕ) := by push_cast; ring
    rw [he,Real.rpow_natCast] at hh
    exact hh
  apply (le_div_iff₀ (pow_pos hzp k)).mpr
  rw [mul_assoc,← pow_add,Real.rpow_neg hD.le,inv_mul_eq_div]
  exact (div_le_one (Real.rpow_pos_of_pos hD _)).mpr hp

lemma ordinary_log_tail_bound {H C R J L U V z : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hJ : 0 ≤ J) (hL : 0 ≤ L)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hz : 1 ≤ z) (a k : ℕ)
    (hsize : (U*V)^2 ≤ L) (hlarge : z^(4*(a+k)) ≤ U*V^2)
    (hH : H ≤ C*R*J*(U*V)^(1/12:ℝ)*((U*V)^2+L)*L*z^a) :
    H ≤ (2*C)*R*J*L^2*(U*V^2)^(1/3:ℝ)/z^k := by
  have hD : 0 < U*V^2 := mul_pos (zero_lt_one.trans_le hU) (pow_pos (zero_lt_one.trans_le hV) _)
  have hp := ordinary_small_conductor_power hU hV hL hsize
  have ht := conductor_log_tail hD hz a k hlarge
  calc
    H ≤ (C*R*J)*((U*V)^(1/12:ℝ)*((U*V)^2+L)*L)*z^a := by convert hH using 1; ring
    _ ≤ (C*R*J)*(2*L^2*(U*V^2)^(1/3:ℝ)*(U*V^2)^(-(1/4:ℝ)))*z^a :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (pow_nonneg (by linarith) _)
    _ = ((2*C)*R*J*L^2*(U*V^2)^(1/3:ℝ))*((U*V^2)^(-(1/4:ℝ))*z^a) := by ring
    _ ≤ ((2*C)*R*J*L^2*(U*V^2)^(1/3:ℝ))*(1/z^k) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallConductorLogSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The part of the small-conductor range above a fixed logarithmic
power has arbitrary logarithmic saving, without any roughness or height
restriction. All coefficients remain the actual prime convolution. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem small_conductor_log_saving (hHuxley : HuxleyAdditiveLargeSieve)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (k : ℕ) :
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧ ∀ (r : γ) (X : ι → ℝ) (U V : ℝ)
      (v e : Eisenstein) (u : ℝ) (Ram S T J H : Finset Eisenstein),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → 1 ≤ U → 1 ≤ V →
      (U*V)^2 ≤ L r → (1+Real.log (L r))^A ≤ U*V^2 →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*(U*V^2)^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,a,hC,hbound⟩ := full_ordinary_moment hHuxley hW hR
    (by norm_num : (0:ℝ) < 1/12) hlo hhi
  refine ⟨2*C,4*(a+k),by positivity,?_⟩
  intro r X U V v e u Ram S T J H hL hX hprod hU hV hsize hlarge hS hT hH
  exact ordinary_log_tail_bound hC.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (zero_le_one.trans hL) hU hV (by linarith [Real.log_nonneg hL]) a k hsize hlarge
    (hbound r X U V v e u Ram S T J H hL hX hprod hU hV hS hT hH)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallCoreBlockMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The intermediate small-conductor estimate applied to the actual
finite core blocks, including their ramified and cube multiplicities. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem small_core_block_log_saving (hHuxley : HuxleyAdditiveLargeSieve)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (k : ℕ) :
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (i j : ℕ)
      (v e : Eisenstein) (u : ℝ) (H : Finset Eisenstein),
      1 ≤ L r → (∀ a, 1 ≤ X a) → (∏ a, X a) = L r → 0 ≤ B →
      (4*(2:ℝ)^i*(2:ℝ)^j)^2 ≤ L r →
      (1+Real.log (L r))^A ≤ 8*coreDyadicConductor i j →
      H ⊆ coreDyadicBlock B i j →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,A,hC,hbound⟩ := small_conductor_log_saving hHuxley hW hR hlo hhi k
  let K := (nonzeroNormBall 729).card
  have hK : 0 < K := by
    apply Finset.card_pos.mpr
    refine ⟨1,mem_nonzeroNormBall.mpr ⟨?_,one_ne_zero⟩⟩
    norm_num [norm_one_eq]
  refine ⟨36*C*K,A,by dsimp [K]; positivity,?_⟩
  intro r X B i j v e u H hL hX hprod hB hsize hlarge hH
  have hU : 1 ≤ 2*(2:ℝ)^i := by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := i)]
  have hV : 1 ≤ 2*(2:ℝ)^j := by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j)]
  have hD : (2*(2:ℝ)^i)*(2*(2:ℝ)^j)^2 = 8*coreDyadicConductor i j := by
    unfold coreDyadicConductor
    ring
  have hST (n : ℕ) : ∀ s ∈ squarefreePrimaryDyad n,
      primary s ∧ Squarefree s ∧ norm s ≤ 2*(2:ℝ)^n := by
    intro s hs
    have hg := squarefreePrimaryDyad_gramDyad hs
    exact ⟨hg.1,hg.2.1,hg.2.2.2.le⟩
  have hh := hbound r X (2*(2:ℝ)^i) (2*(2:ℝ)^j) v e u
    (nonzeroNormBall 729) (squarefreePrimaryDyad i) (squarefreePrimaryDyad j)
    (coreDyadicCubeFactors B i j) H hL hX hprod hU hV
    (by convert hsize using 1; ring) (by rwa [hD]) (hST i) (hST j) hH
  rw [hD] at hh
  apply hh.trans
  have hz : 0 ≤ (1+Real.log (L r))^k := pow_nonneg (by linarith [Real.log_nonneg hL]) _
  apply div_le_div_of_nonneg_right _ hz
  have hweight := coreDyadicCubeFactors_card_eight_weight hB i j
  have hm := mul_le_mul_of_nonneg_left hweight
    (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg K)) (sq_nonneg (L r)))
  dsimp [K] at hm ⊢
  nlinarith [hm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformCoreBlockMoment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One logarithmic saving on every actual core dyad above the small
core cutoff, obtained by joining the ordinary and exceptional estimates. -/
noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma negative_power_log_saving {ν : ℝ} (hν : 0 < ν) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, L^(-ν) ≤ 1/(1+Real.log L)^k := by
  have h := exclusion_log_absorption (c := ν) (d := 0) (ε := 1)
    (by norm_num) (by simpa using hν) (C := 1) (by norm_num) k 0
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with L h hL
  have hp := h (L^ν) 1 (by norm_num) (by simp) le_rfl
  simp only [Real.one_rpow,one_mul,pow_zero,div_one] at hp
  have hz : 0 < (1+Real.log L)^k := pow_pos (by linarith [Real.log_nonneg hL]) _
  rw [Real.rpow_neg (zero_le_one.trans hL),← one_div]
  exact one_div_le_one_div_of_le hz hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialHeightCoreBlock
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The large-core bound extends to the fixed polynomial height window
needed before taking the rapidly decreasing Mellin tails. -/
noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem uniform_core_block_polynomial_height_oai (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (C T₀ : ℝ) (A : ℕ), 0 < C ∧
    ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (i j : ℕ) (e : Eisenstein) (u : ℝ)
      (H : Finset Eisenstein), T₀ ≤ L r →
      (∏ a, X a) = L r → (∀ a, (2*L r)^c < X a) →
      0 ≤ B → B ≤ (L r)^(1+η) → coreDyadicConductor i j ≤ B →
      (1+Real.log (L r))^A ≤ 8*coreDyadicConductor i j →
      e ≠ 0 → norm e ≤ (L r)^σ → 1+|u| ≤ (L r)^(9/25:ℝ) →
      H ⊆ coreDyadicBlock B i j →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 1 e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,CL,ν,hη,hη₁,hσ,hCL,hν,hlarge⟩ :=
    large_core_block_moment (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR
      (by norm_num : (0:ℝ) < 1/4) hGI hGQ
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨TS,hlarge⟩ := hlarge L W hL hW hlo hhi
  obtain ⟨CS,A,hCS,hsmall⟩ := small_core_block_log_saving hHuxley hW hR hlo hhi k
  have hev := (eventually_ge_atTop TS).and ((negative_power_log_saving hν k).and
    (eventually_const_mul_rpow_le
      (by norm_num : (1/2:ℝ) < 1) 16))
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp hev
  refine ⟨max CS CL,T₀,A,lt_of_lt_of_le hCS (le_max_left _ _),?_⟩
  intro r X B i j e u H hT₀ hprod hX hB hBL hDB hcut he heN hu hH
  obtain ⟨hTS,hneg,hmargin⟩ := hT (L r) hT₀
  have hXone : ∀ a, 1 ≤ X a := fun a =>
    (Real.one_le_rpow (by linarith [hL r] : 1 ≤ 2*L r) hc.le).trans (hX a).le
  have hz : 0 ≤ (1+Real.log (L r))^k := pow_nonneg (by linarith [Real.log_nonneg (hL r)]) _
  have hbase : 0 ≤ (L r)^2*B^(1/3:ℝ) := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hB _)
  by_cases hD : coreDyadicConductor i j ≤ (L r)^(1/4:ℝ)
  · have hm := hsmall r X B i j 1 e u H (hL r) hXone hprod hB
      (small_core_ordinary_window (zero_le_one.trans (hL r))
        (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) hD
        (by simpa only [Real.rpow_one] using hmargin)) hcut hH
    apply hm.trans
    apply div_le_div_of_nonneg_right _ hz
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left CS CL) hbase]
  · have hm := hlarge r X B i j 1 e u H hTS hprod hX hB hBL hDB
      (le_of_not_ge hD) one_ne_zero he
      (by simpa only [norm_one_eq] using Real.one_le_rpow (hL r) hσ.le) heN
      hu hH
    apply hm.trans
    calc
      _ ≤ CL*(L r)^2*B^(1/3:ℝ)*(1/(1+Real.log (L r))^k) :=
        mul_le_mul_of_nonneg_left hneg (mul_nonneg (mul_nonneg hCL.le (sq_nonneg _))
          (Real.rpow_nonneg hB _))
      _ = CL*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hz
        nlinarith [mul_le_mul_of_nonneg_right (le_max_right CS CL) hbase]

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CubicFirstMoment.uniform_core_block_polynomial_height_oai.{u_1, u_2} := @OAI.CubicFirstMoment.uniform_core_block_polynomial_height_oai.{u_1, u_2}
