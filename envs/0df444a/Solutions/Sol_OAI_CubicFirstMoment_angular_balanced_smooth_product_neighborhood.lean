-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_balanced_smooth_product_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:02:22.948712+00:00
-- url     : https://prove2.me/submissions/134f6082-7406-4b01-aec9-6046a5013d8e

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_full_smooth_angular_twisted_primitive_cubic_bound

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
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_InnerExtension
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full inner cube covers and sharp coefficient extension bounds. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma complex_norm_sum_sq_le {ι : Type*} (I : Finset ι) (v : ι → ℂ) :
    ‖∑ i ∈ I, v i‖^2 ≤ (I.card : ℝ)*∑ i ∈ I, ‖v i‖^2 := by
  have ht := norm_sum_le I v
  have hc := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun i => ‖v i‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
  exact (pow_le_pow_left₀ (_root_.norm_nonneg _) ht 2).trans hc

lemma complex_mass_sum_sq_le {ι κ : Type*} (I : Finset ι) (P : Finset κ)
    (F : κ → ι → ℂ) :
    (∑ a ∈ P, ‖∑ i ∈ I, F a i‖^2) ≤
      (I.card : ℝ)*∑ i ∈ I, ∑ a ∈ P, ‖F a i‖^2 := by
  calc
    _ ≤ ∑ a ∈ P, (I.card : ℝ)*∑ i ∈ I, ‖F a i‖^2 :=
      Finset.sum_le_sum (fun a _ => complex_norm_sum_sq_le I (F a))
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primeSetExponent_le_iff (S : Finset EisensteinIdealPrime) (ν : EisensteinIdealExponent) :
    primeSetExponent S ≤ ν ↔ ∀ p ∈ S, 0 < ν p := by
  constructor
  · intro h p hp
    have h1 := h p
    simpa only [primeSetExponent_apply,ite_eq_left hp,Nat.one_le_iff_ne_zero,
      Nat.pos_iff_ne_zero] using h1
  · intro h p
    by_cases hp : p ∈ S
    · simpa only [primeSetExponent_apply,ite_eq_left hp] using (Nat.succ_le_iff.mpr (h p hp))
    · simp [hp]

/-- Exact finite inclusion--exclusion for the prime-to-`S` condition. -/
lemma ideal_prime_exclusion_indicator (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) :
    (if ∀ p ∈ S, ν p = 0 then (1:ℂ) else 0) =
      ∑ T ∈ S.powerset, if primeSetExponent T ≤ ν then (-1:ℂ)^T.card else 0 := by
  have he : S.powerset.filter (fun T => primeSetExponent T ≤ ν) =
      (S.filter (fun p => 0 < ν p)).powerset := by
    ext T
    simp only [Finset.mem_filter,Finset.mem_powerset,primeSetExponent_le_iff]
    constructor
    · rintro ⟨hTS,hpos⟩ p hp
      exact Finset.mem_filter.mpr ⟨hTS hp,hpos p hp⟩
    · intro h
      exact ⟨fun p hp => (Finset.mem_filter.mp (h hp)).1,
        fun p hp => (Finset.mem_filter.mp (h hp)).2⟩
  rw [← Finset.sum_filter,he]
  have hsum : (∑ T ∈ (S.filter (fun p => 0 < ν p)).powerset, (-1:ℂ)^T.card) =
      if S.filter (fun p => 0 < ν p) = ∅ then 1 else 0 := by
    exact_mod_cast (Finset.sum_powerset_neg_one_pow_card (x := S.filter (fun p => 0 < ν p)))
  rw [hsum]
  have hzero : S.filter (fun p => 0 < ν p) = ∅ ↔ ∀ p ∈ S, ν p = 0 := by
    simp only [Finset.filter_eq_empty_iff,Nat.not_lt,Nat.le_zero]
  simp only [hzero]

lemma idealNorm_shift_mem_iff (δ ν : EisensteinIdealExponent) (Y : ℝ) :
    δ+ν ∈ fullIdealBall Y ↔ ν ∈ fullIdealBall (Y/idealExponentNorm δ) := by
  simp only [mem_fullIdealBall,idealExponentNorm_add]
  rw [le_div_iff₀ (idealExponentNorm_pos δ)]
  rw [mul_comm]

lemma idealNorm_tsub_mem {δ ν : EisensteinIdealExponent} (hδ : δ ≤ ν)
    {Y : ℝ} (hν : ν ∈ fullIdealBall Y) :
    ν-δ ∈ fullIdealBall (Y/idealExponentNorm δ) := by
  apply (idealNorm_shift_mem_iff δ (ν-δ) Y).mp
  simpa only [add_tsub_cancel_of_le hδ] using hν

/-- An exact rescaled complete ideal sum for one divisor. Character
multiplicativity is explicit, and no Euler factor is silently deleted. -/
lemma fullIdealBall_shift_sum (δ : EisensteinIdealExponent) (Y : ℝ)
    (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ) = χ ν*χ κ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) :
    (∑ ν ∈ fullIdealBall Y, if δ ≤ ν then χ ν*W (idealExponentNorm ν/Z) else 0) =
      χ δ * ∑ κ ∈ fullIdealBall (Y/idealExponentNorm δ),
        χ κ*W (idealExponentNorm κ/(Z/idealExponentNorm δ)) := by
  rw [← Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_bij' (fun ν _ => ν-δ) (fun κ _ => δ+κ)
  · intro ν hν
    exact idealNorm_tsub_mem (Finset.mem_filter.mp hν).2 (Finset.mem_filter.mp hν).1
  · intro κ hκ
    exact Finset.mem_filter.mpr ⟨(idealNorm_shift_mem_iff δ κ Y).mpr hκ,
      le_add_of_nonneg_right zero_le⟩
  · intro ν hν
    exact add_tsub_cancel_of_le (Finset.mem_filter.mp hν).2
  · intro κ hκ
    exact add_tsub_cancel_left δ κ
  · intro ν hν
    have hd := (Finset.mem_filter.mp hν).2
    have he : δ+(ν-δ) = ν := add_tsub_cancel_of_le hd
    have hnorm : idealExponentNorm ν/Z =
        idealExponentNorm (ν-δ)/(Z/idealExponentNorm δ) := by
      calc
        _ = (idealExponentNorm δ*idealExponentNorm (ν-δ))/Z := by
          rw [← idealExponentNorm_add,he]
        _ = _ := by field_simp [ne_of_gt hZ,ne_of_gt (idealExponentNorm_pos δ)]
    have hchar : χ ν = χ δ*χ (ν-δ) := (congrArg χ he).symm.trans (hχ _ _)
    rw [hchar,hnorm]
    ring

/-- Removing any finite set of local Euler factors is a finite sum of
complete ideal sums at the exact rescaled lengths. The finite set may
include the ramified prime; its norm and character factor are retained. -/
theorem fullIdealBall_euler_exclusion (S : Finset EisensteinIdealPrime)
    (Y : ℝ) (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ) = χ ν*χ κ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) :
    (∑ ν ∈ fullIdealBall Y, if ∀ p ∈ S, ν p = 0 then χ ν*W (idealExponentNorm ν/Z) else 0) =
      ∑ T ∈ S.powerset, (-1:ℂ)^T.card*χ (primeSetExponent T)*
        ∑ κ ∈ fullIdealBall (Y/idealExponentNorm (primeSetExponent T)),
          χ κ*W (idealExponentNorm κ/(Z/idealExponentNorm (primeSetExponent T))) := by
  calc
    _ = ∑ ν ∈ fullIdealBall Y, ∑ T ∈ S.powerset,
        (if primeSetExponent T ≤ ν then (-1:ℂ)^T.card else 0)*
          (χ ν*W (idealExponentNorm ν/Z)) := by
      apply Finset.sum_congr rfl
      intro ν hν
      rw [← Finset.sum_mul,← ideal_prime_exclusion_indicator]
      split_ifs <;> simp
    _ = ∑ T ∈ S.powerset, ∑ ν ∈ fullIdealBall Y,
        (if primeSetExponent T ≤ ν then (-1:ℂ)^T.card else 0)*
          (χ ν*W (idealExponentNorm ν/Z)) := Finset.sum_comm
    _ = ∑ T ∈ S.powerset, (-1:ℂ)^T.card *
        (∑ ν ∈ fullIdealBall Y,
          if primeSetExponent T ≤ ν then χ ν*W (idealExponentNorm ν/Z) else 0) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν hν
      split_ifs <;> simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [fullIdealBall_shift_sum _ Y χ hχ W hZ]
      ring

lemma compactSupport_upper_cutoff (W : ℝ → ℂ) (hW : HasCompactSupport W) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, B < x → W x = 0 := by
  obtain ⟨R,hR⟩ := hW.isCompact.isBounded.exists_norm_le
  refine ⟨max R 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x hx
  by_contra hne
  have hbound := hR x (subset_tsupport W hne)
  have hRabs : |x| ≤ R := by simpa only [Real.norm_eq_abs] using hbound
  have hle : x ≤ max R 1 := (le_abs_self x).trans (hRabs.trans (le_max_left _ _))
  exact (not_le_of_gt hx) hle

/-- Compact norm support makes the complete ideal sum literally finite;
no analytic convergence hypothesis is required for this reduction. -/
lemma ideal_smooth_tsum_eq_ball (χ : EisensteinIdealExponent → ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) :
    (∑' ν, χ ν*W (idealExponentNorm ν/Z)) =
      ∑ ν ∈ fullIdealBall (B*Z), χ ν*W (idealExponentNorm ν/Z) := by
  apply tsum_eq_sum
  intro ν hν
  have hN : B*Z < idealExponentNorm ν := lt_of_not_ge (fun h => hν (mem_fullIdealBall.mpr h))
  rw [hW _ ((lt_div_iff₀ hZ).mpr hN),mul_zero]

/-- The actual complete smooth ideal sum, with finite Euler exclusions.
In particular, selecting the ramified prime in `S` restores or removes its
local factor through this formula with its exact norm and character value. -/
theorem smooth_ideal_euler_exclusion (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ) = χ ν*χ κ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    {Z : ℝ} (hZ : 0 < Z) :
    (∑' ν, if ∀ p ∈ S, ν p = 0 then χ ν*W (idealExponentNorm ν/Z) else 0) =
      ∑ T ∈ S.powerset, (-1:ℂ)^T.card*χ (primeSetExponent T)*
        ∑' κ, χ κ*W (idealExponentNorm κ/(Z/idealExponentNorm (primeSetExponent T))) := by
  obtain ⟨B,_,hB⟩ := compactSupport_upper_cutoff W hW
  have hleft : (∑' ν, if ∀ p ∈ S, ν p = 0 then χ ν*W (idealExponentNorm ν/Z) else 0) =
      ∑ ν ∈ fullIdealBall (B*Z),
        if ∀ p ∈ S, ν p = 0 then χ ν*W (idealExponentNorm ν/Z) else 0 := by
    simpa only [ite_mul,zero_mul] using ideal_smooth_tsum_eq_ball
      (fun ν => if ∀ p ∈ S, ν p = 0 then χ ν else 0) W hZ hB
  rw [hleft,fullIdealBall_euler_exclusion S (B*Z) χ hχ W hZ]
  apply Finset.sum_congr rfl
  intro T hT
  have h := ideal_smooth_tsum_eq_ball χ W
    (div_pos hZ (idealExponentNorm_pos (primeSetExponent T))) hB
  have he : B*(Z/idealExponentNorm (primeSetExponent T)) =
      B*Z/idealExponentNorm (primeSetExponent T) := by ring
  simpa only [he] using congrArg (fun z : ℂ => (-1:ℂ)^T.card*χ (primeSetExponent T)*z) h.symm

end CubicFirstMoment

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeToThreeIdeals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ramified Euler restriction in primary-element polynomials.
Prime-to-three ideals are identified arithmetically, then the complete
ideal-sum exclusion formula restores their missing local factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealGenerator_coprime_three_iff (ν : EisensteinIdealExponent) :
    IsCoprime (idealExponentGenerator ν) 3 ↔ ∀ p ∈ ramifiedIdealPrimes, ν p = 0 := by
  rw [isCoprime_iff_idealExponent_disjoint (idealExponentGenerator_ne_zero ν) (by norm_num),
    idealExponentOf_generator]
  constructor
  · intro h p hp
    rcases h p with hν | h3
    · exact hν
    · exact False.elim ((Finsupp.mem_support_iff.mp hp) h3)
  · intro h p
    by_cases hp : p ∈ ramifiedIdealPrimes
    · exact Or.inl (h p hp)
    · exact Or.inr (Finsupp.notMem_support_iff.mp hp)

/-- Primary normalization succeeds exactly on the ideals prime to three. -/
theorem idealPrimaryGenerator_primary_iff (ν : EisensteinIdealExponent) :
    primary (idealPrimaryGenerator ν) ↔ ∀ p ∈ ramifiedIdealPrimes, ν p = 0 := by
  rw [← idealGenerator_coprime_three_iff]
  constructor
  · intro h
    exact (primary_coprime_three h).of_isCoprime_of_dvd_left
      (primaryNormalize_associated (idealExponentGenerator ν)).dvd
  · intro h
    exact primaryNormalize_primary (residue_isUnit_of_isCoprime h.symm)

lemma primaryIdealBall_eq_full_filter (Y : ℝ) :
    primaryIdealBall Y = (fullIdealBall Y).filter (fun ν => ∀ p ∈ ramifiedIdealPrimes, ν p = 0) := by
  ext ν
  simp only [mem_primaryIdealBall,Finset.mem_filter,mem_fullIdealBall,
    idealPrimaryGenerator_primary_iff]
  exact and_comm

lemma primaryIdealBall_sum_eq_elements (Y : ℝ) (f : EisensteinIdealExponent → ℂ) :
    (∑ ν ∈ primaryIdealBall Y, f ν) = ∑ a ∈ primaryElementBall Y, f (idealExponentOf a) := by
  unfold primaryIdealBall
  apply Finset.sum_image
  intro a ha b hb he
  exact idealExponentOf_inj_primary (mem_primaryElementBall.mp ha).1
    (mem_primaryElementBall.mp hb).1 he

lemma primary_ideal_smooth_tsum_eq_ball (χ : EisensteinIdealExponent → ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) :
    (∑' ν, if primary (idealPrimaryGenerator ν) then χ ν*W (idealExponentNorm ν/Z) else 0) =
      ∑ ν ∈ primaryIdealBall (B*Z), χ ν*W (idealExponentNorm ν/Z) := by
  have h := ideal_smooth_tsum_eq_ball
    (fun ν => if primary (idealPrimaryGenerator ν) then χ ν else 0) W hZ hW
  simp only [ite_mul,zero_mul] at h
  rw [h,primaryIdealBall_eq_full_filter,Finset.sum_filter]
  simp only [idealPrimaryGenerator_primary_iff]

lemma primary_element_smooth_tsum_eq_ball (χ : EisensteinIdealExponent → ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) :
    (∑' a : Eisenstein, if primary a then χ (idealExponentOf a)*W (norm a/Z) else 0) =
      ∑ a ∈ primaryElementBall (B*Z), χ (idealExponentOf a)*W (norm a/Z) := by
  calc
    _ = ∑ a ∈ primaryElementBall (B*Z),
        if primary a then χ (idealExponentOf a)*W (norm a/Z) else 0 := by
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

/-- The original primary-element smooth polynomial is exactly the smooth
ideal sum with the actual primes above three excluded. -/
theorem primary_element_ideal_smooth_eq (χ : EisensteinIdealExponent → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    (∑' a : Eisenstein, if primary a then χ (idealExponentOf a)*W (norm a/Z) else 0) =
      ∑' ν, if primary (idealPrimaryGenerator ν) then χ ν*W (idealExponentNorm ν/Z) else 0 := by
  obtain ⟨B,_,hB⟩ := compactSupport_upper_cutoff W hW
  rw [primary_element_smooth_tsum_eq_ball χ W hZ hB,
    primary_ideal_smooth_tsum_eq_ball χ W hZ hB,primaryIdealBall_sum_eq_elements]
  apply Finset.sum_congr rfl
  intro a ha
  rw [idealExponentOf_norm (primary_ne_zero (mem_primaryElementBall.mp ha).1)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryHeckeCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primaryMixedLift_unit {a b x : Eisenstein} (ha : primary a) (hb : primary b)
    (hx : IsUnit x) : primaryMixedLift a b x = 1 := by
  rw [primaryMixedLift,ite_eq_left (hx.map (Ideal.Quotient.mk (modulus 3))),
    primaryNormalize_unit hx,mixedCubic_one ha hb]

lemma primaryMixedResidueChar_primary {a b x : Eisenstein}
    (ha : primary a) (hb : primary b) (hx : primary x) :
    primaryMixedResidueChar a b ha hb (Ideal.Quotient.mk (modulus (3*(a*b))) x) =
      mixedCubic a b x := by rw [primaryMixedResidueChar_mk,primaryMixedLift_primary hx]

lemma primaryMixedResidueChar_trivialInfinity {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    ∀ u : Eisensteinˣ, primaryMixedResidueChar a b ha hb
      (Ideal.Quotient.mk (modulus (3*(a*b))) u) = 1 := by
  intro u
  rw [primaryMixedResidueChar_mk,primaryMixedLift_unit ha hb u.isUnit]


lemma primaryMixedLift_associated {a b x y : Eisenstein}
    (ha : primary a) (hb : primary b) (hxy : Associated x y) :
    primaryMixedLift a b x = primaryMixedLift a b y := by
  obtain ⟨u,hu⟩ := hxy
  rw [← hu,primaryMixedLift_mul ha hb,primaryMixedLift_unit ha hb u.isUnit,mul_one]

lemma primaryMixedIdealChar_at_element {a b x : Eisenstein}
    (ha : primary a) (hb : primary b) (hx : primary x) :
    primaryMixedIdealChar a b (idealExponentOf x) = mixedCubic a b x := by
  rw [primaryMixedIdealChar,
    primaryMixedLift_associated ha hb (idealExponentOf_associated (primary_ne_zero hx)),
    primaryMixedLift_primary hx]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveConductor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary conductor reduction for the finite residue characters.
Minimality is measured by the positive ideal norm; the inducing character
and exact deleted Euler factors are not supplied as extra assumptions. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma ResidueCharacterInduces.refl (q : Eisenstein) (χ : MulChar (Residues q) ℂ) :
    ResidueCharacterInduces q q χ χ := ⟨dvd_refl q,fun _ _ => rfl⟩

lemma ResidueCharacterInduces.trans {q d e : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    {ω : MulChar (Residues e) ℂ}
    (hqd : ResidueCharacterInduces q d χ ψ) (hde : ResidueCharacterInduces d e ψ ω) :
    ResidueCharacterInduces q e χ ω := by
  refine ⟨hde.1.trans hqd.1,?_⟩
  intro x hx
  exact (hde.2 x (hx.of_isCoprime_of_dvd_left hqd.1)).trans (hqd.2 x hx)

/-- Every finite character has an actual primitive inducing character,
of modulus dividing the original one and of no larger norm. -/
theorem primitive_residue_conductor_exists {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ ResidueCharacterInduces q d χ ψ ∧
      normNat d ≤ normNat q ∧ PrimitiveResidueCharacter d ψ := by
  let E : ℕ → Prop := fun n => ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
    normNat d = n ∧ ResidueCharacterInduces q d χ ψ
  have hex : ∃ n, E n := ⟨normNat q,q,χ,rfl,ResidueCharacterInduces.refl q χ⟩
  obtain ⟨d,ψ,hdn,hd⟩ := Nat.find_spec hex
  refine ⟨d,ψ,ne_zero_of_dvd_ne_zero hq hd.1,hd,?_,?_⟩
  · rw [hdn]
    exact Nat.find_min' hex ⟨q,χ,rfl,ResidueCharacterInduces.refl q χ⟩
  · intro e ω he
    rw [hdn]
    exact Nat.find_min' hex ⟨e,ω,rfl,hd.trans he⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueIdealCharacters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma residueIdealChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ν : EisensteinIdealExponent) :
    ‖residueIdealChar q χ ν‖ ≤ 1 := residueChar_norm_le_one hq χ _

lemma ideal_coprime_support {q : Eisenstein} (hq : q ≠ 0)
    (ν : EisensteinIdealExponent) :
    IsCoprime q (idealExponentGenerator ν) ↔
      ∀ p ∈ (idealExponentOf q).support, ν p = 0 := by
  rw [isCoprime_comm,isCoprime_iff_idealExponent_disjoint (idealExponentGenerator_ne_zero ν) hq,
    idealExponentOf_generator]
  constructor
  · intro h p hp
    rcases h p with hn | hq
    · exact hn
    · exact False.elim ((Finsupp.mem_support_iff.mp hp) hq)
  · intro h p
    by_cases hp : p ∈ (idealExponentOf q).support
    · exact Or.inl (h p hp)
    · exact Or.inr (Finsupp.notMem_support_iff.mp hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite factor at 3 required by a fixed angular Hecke character.
The archimedean phase is retained separately, including after primitive
conductor reduction. Complete ideal sums therefore include every prime
at which the primitive character is unramified. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma ResidueCharacterInduces.angular_units {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) {ℓ : ℤ}
    (hu : AngularUnitCompatible q χ ℓ) : AngularUnitCompatible d ψ ℓ := by
  intro u
  rw [h.2 u (show IsCoprime q (u:Eisenstein) from ⟨0,(u⁻¹:Eisensteinˣ),by simp⟩)]
  exact hu u

lemma angularResidueIdealChar_add (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (ν κ : EisensteinIdealExponent) :
    angularResidueIdealChar q χ ℓ (ν+κ) =
      angularResidueIdealChar q χ ℓ ν*angularResidueIdealChar q χ ℓ κ := by
  simp only [angularResidueIdealChar, residueIdealChar_add, idealExponentGenerator_add, theta_mul]
  ring

lemma angularResidueIdealChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    ‖angularResidueIdealChar q χ ℓ ν‖ ≤ 1 := by
  rw [angularResidueIdealChar, norm_mul, norm_theta (idealExponentGenerator_ne_zero ν), mul_one]
  exact residueIdealChar_norm_le_one hq χ ν

lemma angular_character_associated {q x y : Eisenstein}
    (χ : MulChar (Residues q) ℂ) {ℓ : ℤ} (hu : AngularUnitCompatible q χ ℓ)
    (hxy : Associated x y) :
    χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x =
      χ (Ideal.Quotient.mk (modulus q) y)*theta ℓ y := by
  obtain ⟨u,rfl⟩ := hxy
  rw [map_mul, map_mul, theta_mul]
  symm
  calc
    _ = (χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x)*
        (χ (Ideal.Quotient.mk (modulus q) u)*theta ℓ u) := by ring
    _ = _ := by rw [hu u, mul_one]

lemma angularResidueIdealChar_at_element {q x : Eisenstein}
    (χ : MulChar (Residues q) ℂ) {ℓ : ℤ} (hu : AngularUnitCompatible q χ ℓ)
    (hx : x ≠ 0) :
    angularResidueIdealChar q χ ℓ (idealExponentOf x) =
      χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x :=
  angular_character_associated χ hu (idealExponentOf_associated hx)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryIdealMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sieve moments of the actual primary-normalized ideal character.
The primary representative and the ramified zero are retained explicitly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryMixedIdealChar_eq (a b : Eisenstein) (ν : EisensteinIdealExponent) :
    primaryMixedIdealChar a b ν =
      if primary (idealPrimaryGenerator ν) then
        mixedCubic a b (idealPrimaryGenerator ν) else 0 := by
  unfold primaryMixedIdealChar primaryMixedLift idealPrimaryGenerator
  by_cases h : IsUnit (Ideal.Quotient.mk (modulus 3) (idealExponentGenerator ν))
  · rw [ite_eq_left h,ite_eq_left (primaryNormalize_primary h)]
  · rw [ite_eq_right h,ite_eq_right]
    intro hp
    exact h (unit_residue_of_dvd_primary hp (primaryNormalize_associated _).dvd)

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

lemma cubicSymbol_eq_one_of_dvd_sub {q x : Eisenstein}
    (hq : primary q) (hx : q ∣ x-1) : cubicSymbol q x = 1 := by
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub hx)]
  exact (cubic_reciprocity hq (by norm_num [primary])).trans (cubicSymbol_one_lower q)

lemma squarefree_primary_dvd_of_prime_dvd {a d : Eisenstein} (ha : primary a)
    (hsa : Squarefree a)
    (hprime : ∀ p : Eisenstein, primaryPrime p → p ∣ a → p ∣ d) : a ∣ d := by
  apply (primary_induction (P := fun a => Squarefree a →
    (∀ p : Eisenstein, primaryPrime p → p ∣ a → p ∣ d) → a ∣ d) ?_ ?_ ha) hsa hprime
  · intro _ _
    exact one_dvd d
  · intro p c hp hc ih hsf hall
    have hpd : p ∣ d := hall p hp (dvd_mul_right p c)
    have hcd : c ∣ d := ih hsf.of_mul_right (fun r hr hrc =>
      hall r hr (hrc.trans (dvd_mul_left c p)))
    exact (IsRelPrime.of_squarefree_mul hsf).mul_dvd hpd hcd

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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimitiveDualMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubic second moments for the actual primitive ideal characters.
The primes above three are separated exactly before applying the cubic sieve. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angularResidueIdealChar_primaryNormalize {d : Eisenstein}
    (ψ : MulChar (Residues d) ℂ) {ℓ : ℤ} (hu : AngularUnitCompatible d ψ ℓ)
    (ν : EisensteinIdealExponent) :
    angularResidueIdealChar d ψ ℓ ν =
      ψ (Ideal.Quotient.mk (modulus d) (idealPrimaryGenerator ν))*
        theta ℓ (idealPrimaryGenerator ν) :=
  angular_character_associated ψ hu
    (primaryNormalize_associated (idealExponentGenerator ν))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallPrimeParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual small-prime partition of squarefree cubic moduli. Its
parts divide the small modulus, so their number has a proved subpower bound. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primarySmallPart_dvd {a v : Eisenstein} (ha : Squarefree a) (hv : v ≠ 0) :
    primarySmallPart v a ∣ v := by
  have hle : supportedIdealPart v (idealExponentOf a) ≤ idealExponentOf v := by
    intro p
    simp only [supportedIdealPart,Finsupp.filter_apply]
    split_ifs with hp
    · exact ((idealExponentOf_squarefree_iff ha.ne_zero).mpr ha p).trans
        (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp))
    · exact Nat.zero_le _
  exact (primaryNormalize_associated _).symm.dvd.trans
    ((idealExponentGenerator_dvd_of_le hle).trans (idealExponentOf_associated hv).dvd)

lemma primaryOutsidePart_squarefree (v : Eisenstein) {a : Eisenstein}
    (ha : primary a) (hsa : Squarefree a) : Squarefree (primaryOutsidePart v a) := by
  have hs : Squarefree (primarySmallPart v a*primaryOutsidePart v a) := by
    rw [primary_small_outside_mul v ha]
    exact hsa
  exact hs.of_mul_right

theorem smallPrimeParts_card {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (v : Eisenstein), v ≠ 0 →
      (∀ a ∈ P, primary a ∧ Squarefree a) →
      ((P.image (primarySmallPart v)).card:ℝ) ≤ C*norm v^ε := by
  obtain ⟨C,hC,hbound⟩ := primary_divisor_card_small_power hε
  refine ⟨C,hC,?_⟩
  intro P v hv hP
  let T := P.image (primarySmallPart v)
  have hprim (x : Eisenstein) (hx : x ∈ T) : primary x := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact primarySmallPart_primary v (hP a ha).1
  have hdiv (x : Eisenstein) (hx : x ∈ T) : x ∣ v := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact primarySmallPart_dvd (hP a ha).2 hv
  have he : T.filter (fun x => x ∣ v) = T := Finset.filter_eq_self.mpr hdiv
  have h := hbound T hprim v hv
  rwa [he] at h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedConductor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variable squarefree conductor survives multiplication by a fixed
character of coprime small modulus. Detection is by explicit local CRT. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem twisted_conductor_left_prime {a b d p r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a)
    (hab : IsCoprime a b) (hsmall : IsCoprime (a*b) r) (hp : primaryPrime p) (hpa : p ∣ a)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) : p ∣ d := by
  by_contra hpd
  obtain ⟨c,rfl⟩ := hpa
  have hc : primary c := primary_of_mul hp.1 ha
  have hpc : IsCoprime p c := (IsRelPrime.of_squarefree_mul hsa).isCoprime
  have hpb : IsCoprime p b := hab.of_mul_left_left
  have hpd' : IsCoprime p d := hp.2.irreducible.coprime_iff_not_dvd.mpr hpd
  have hpr : IsCoprime p r := hsmall.of_mul_left_left.of_mul_left_left
  let Q := 3*c*b*d*r
  have hpQ : IsCoprime p Q :=
    ((((primary_coprime_three hp.1).mul_right hpc).mul_right hpb).mul_right hpd').mul_right hpr
  obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp (cubicResidueChar_ne_one hp)
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective (u : Residues p)
  obtain ⟨x,hxp,hxQ⟩ := residue_crt_one hpQ y
  have hx3 : (3:Eisenstein) ∣ x-1 := (show (3:Eisenstein) ∣ Q from ⟨c*b*d*r,by dsimp [Q]; ring⟩).trans hxQ
  have hxc : c ∣ x-1 := (show c ∣ Q from ⟨3*b*d*r,by dsimp [Q]; ring⟩).trans hxQ
  have hxb : b ∣ x-1 := (show b ∣ Q from ⟨3*c*d*r,by dsimp [Q]; ring⟩).trans hxQ
  have hxd : d ∣ x-1 := (show d ∣ Q from ⟨3*c*b*r,by dsimp [Q]; ring⟩).trans hxQ
  have hxr : r ∣ x-1 := (show r ∣ Q from ⟨3*c*b*d,by dsimp [Q]; ring⟩).trans hxQ
  have hrx := isCoprime_of_dvd_sub_one hxr
  have hη : η (Ideal.Quotient.mk (modulus r) x) = 1 := by
    rw [residue_eq_of_dvd_sub hxr,map_one,map_one]
  have hxp' : Ideal.Quotient.mk (modulus p) x = u :=
    (residue_eq_of_dvd_sub hxp).trans hy
  have hpx : IsCoprime p x := isCoprime_of_residue_isUnit (by rw [hxp']; exact u.isUnit)
  have hcx := isCoprime_of_dvd_sub_one hxc
  have hbx := isCoprime_of_dvd_sub_one hxb
  have hval := hagree x hx3 (((hpx.mul_left hcx).mul_left hbx).mul_left hrx)
  have hψ : ψ (Ideal.Quotient.mk (modulus d) x) = 1 := by
    rw [residue_eq_of_dvd_sub hxd,map_one,map_one]
  rw [hψ,hη,mul_one,mixedCubic,cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hc),
    cubicSymbol_eq_one_of_dvd_sub hc hxc,cubicSymbol_eq_one_of_dvd_sub hb hxb,
    star_one,mul_one,mul_one,cubicSymbol_prime hp,← cubicResidueChar_mk p hp,hxp'] at hval
  exact hu hval.symm


theorem twisted_conductor_contains {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) :
    a*b ∣ d := by
  have had : a ∣ d := squarefree_primary_dvd_of_prime_dvd ha hsa
    (fun p hp hpa => twisted_conductor_left_prime ha hb hsa hab hsmall hp hpa ψ η hagree)
  have hswap : ∀ x : Eisenstein, primary x → IsCoprime (b*a*r) x →
      (star ψ) (Ideal.Quotient.mk (modulus d) x) =
        mixedCubic b a x*(star η) (Ideal.Quotient.mk (modulus r) x) := by
    intro x hx hcop
    rw [MulChar.star_apply,hagree x hx (by simpa only [mul_comm] using hcop)]
    simp only [mixedCubic,star_mul,star_star,MulChar.star_apply]
    ring
  have hbd : b ∣ d := squarefree_primary_dvd_of_prime_dvd hb hsb
    (fun p hp hpb => twisted_conductor_left_prime hb ha hsb hab.symm
      (by simpa only [mul_comm] using hsmall) hp hpb (star ψ) (star η) hswap)
  exact hab.isRelPrime.mul_dvd had hbd

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedIdealMatch
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Agreement with the actual small-twisted mixed coefficients outside
three and the small modulus, including every common zero. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma twisted_character_primary_match {a b d r x : Eisenstein}
    (ha : primary a) (hb : primary b) (ψ : MulChar (Residues d) ℂ)
    (η : MulChar (Residues r) ℂ) (hdiv : a*b ∣ d)
    (hagree : ∀ y : Eisenstein, primary y → IsCoprime (a*b*r) y →
      ψ (Ideal.Quotient.mk (modulus d) y) = mixedCubic a b y*η (Ideal.Quotient.mk (modulus r) y))
    (hx : primary x) (hxr : IsCoprime r x) :
    ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x) := by
  by_cases hcop : IsCoprime (a*b) x
  · exact hagree x hx (hcop.mul_left hxr)
  · have hz : mixedCubic a b x = 0 := mixedCubic_eq_zero_of_nonunit ha hb x
      (fun h => hcop (isCoprime_of_residue_isUnit h))
    rw [hz,zero_mul]
    apply MulChar.map_nonunit
    intro h
    exact hcop ((isCoprime_of_residue_isUnit h).of_isCoprime_of_dvd_left hdiv)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedIdealMatch
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Agreement with the actual small-twisted mixed coefficients outside
three and the small modulus, including every common zero. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma angular_twisted_ideal_mixed_match {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (ℓ : ℤ) (hu : AngularUnitCompatible d ψ ℓ)
    (hη : AngularUnitCompatible r η ℓ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (ν : EisensteinIdealExponent) (hν : primary (idealPrimaryGenerator ν))
    (hνr : IsCoprime r (idealPrimaryGenerator ν)) :
    angularResidueIdealChar d ψ ℓ ν = primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν := by
  rw [angularResidueIdealChar_primaryNormalize ψ hu ν,
    angularResidueIdealChar_primaryNormalize η hη ν,
    twisted_character_primary_match ha hb ψ η
      (twisted_conductor_contains ha hb hsa hsb hab hsmall ψ η hagree) hagree hν hνr,
    primaryMixedIdealChar_eq,ite_eq_left hν]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedEuler
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Euler restoration for the small-twisted primary sum. Only the
primes above three and the fixed small modulus are omitted, with the
angular character and its unit compatibility retained exactly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angular_twisted_residue_restriction {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (ℓ : ℤ) (hu : AngularUnitCompatible d ψ ℓ)
    (hη : AngularUnitCompatible r η ℓ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (ν : EisensteinIdealExponent) :
    primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν =
      if ∀ p ∈ (idealExponentOf (3*r)).support, ν p = 0 then angularResidueIdealChar d ψ ℓ ν else 0 := by
  have h3r : (3:Eisenstein)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  by_cases hlocal : ∀ p ∈ (idealExponentOf (3*r)).support, ν p = 0
  · rw [ite_eq_left hlocal]
    have hcop := (ideal_coprime_support h3r ν).mpr hlocal
    have hprim : primary (idealPrimaryGenerator ν) :=
      (idealPrimaryGenerator_primary_iff ν).mpr
        ((idealGenerator_coprime_three_iff ν).mp hcop.of_mul_left_left.symm)
    have hpr : IsCoprime r (idealPrimaryGenerator ν) :=
      hcop.of_mul_left_right.of_isCoprime_of_dvd_right
        (primaryNormalize_associated (idealExponentGenerator ν)).symm.dvd
    exact (angular_twisted_ideal_mixed_match ha hb hsa hsb hab hsmall ψ η ℓ hu hη hagree ν hprim hpr).symm
  · rw [ite_eq_right hlocal]
    by_cases hprim : primary (idealPrimaryGenerator ν)
    · have hn : ¬ IsCoprime r (idealExponentGenerator ν) := by
        intro hc
        apply hlocal
        apply (ideal_coprime_support h3r ν).mp
        exact ((idealGenerator_coprime_three_iff ν).mpr
          ((idealPrimaryGenerator_primary_iff ν).mp hprim)).symm.mul_left hc
      have hz : angularResidueIdealChar r η ℓ ν = 0 := by
        have hzero : residueIdealChar r η ν = 0 :=
          MulChar.map_nonunit η (fun h => hn (isCoprime_of_residue_isUnit h))
        rw [angularResidueIdealChar,hzero,zero_mul]
      rw [hz,mul_zero]
    · rw [primaryMixedIdealChar_eq,ite_eq_right hprim,zero_mul]

 theorem primary_angular_smalltwist_euler {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (ℓ : ℤ) (hu : AngularUnitCompatible d ψ ℓ)
    (hη : AngularUnitCompatible r η ℓ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    (∑' x : Eisenstein, if primary x then
      mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)*theta ℓ x*
        mellinPhase t (norm x)*W (norm x/Z) else 0) =
      ∑ T ∈ (idealExponentOf (3*r)).support.powerset,
        (-1:ℂ)^T.card*angularResidueIdealChar d ψ ℓ (primeSetExponent T)*
          mellinPhase t (idealExponentNorm (primeSetExponent T))*
          ∑' ν, angularResidueIdealChar d ψ ℓ ν*mellinPhase t (idealExponentNorm ν)*
            W (idealExponentNorm ν/(Z/idealExponentNorm (primeSetExponent T))) := by
  let χ (ν : EisensteinIdealExponent) :=
    primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν*mellinPhase t (idealExponentNorm ν)
  have he : (∑' x : Eisenstein, if primary x then
      mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)*theta ℓ x*
        mellinPhase t (norm x)*W (norm x/Z) else 0) =
      ∑' ν, χ ν*W (idealExponentNorm ν/Z) := by
    have hh := primary_element_ideal_smooth_eq χ W hW hZ
    have hleft : (∑' x : Eisenstein, if primary x then
        mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)*theta ℓ x*
          mellinPhase t (norm x)*W (norm x/Z) else 0) =
        ∑' x : Eisenstein, if primary x then χ (idealExponentOf x)*W (norm x/Z) else 0 := by
      apply tsum_congr
      intro x
      by_cases hx : primary x
      · rw [ite_eq_left hx,ite_eq_left hx]
        dsimp only [χ]
        rw [primaryMixedIdealChar_at_element ha hb hx,
          idealExponentOf_norm (primary_ne_zero hx),
          angularResidueIdealChar_at_element η hη (primary_ne_zero hx)]
        ring
      · rw [ite_eq_right hx,ite_eq_right hx]
    rw [hleft,hh]
    apply tsum_congr
    intro ν
    by_cases hν : primary (idealPrimaryGenerator ν)
    · rw [ite_eq_left hν]
    · rw [ite_eq_right hν]
      simp only [χ,primaryMixedIdealChar_eq,ite_eq_right hν,zero_mul]
  rw [he]
  let ω (ν : EisensteinIdealExponent) := angularResidueIdealChar d ψ ℓ ν*mellinPhase t (idealExponentNorm ν)
  have hω (ν κ : EisensteinIdealExponent) : ω (ν+κ) = ω ν*ω κ := by
    dsimp only [ω]
    rw [angularResidueIdealChar_add,idealExponentNorm_add,
      mellinPhase_mul_pos t (idealExponentNorm_pos ν) (idealExponentNorm_pos κ)]
    ring
  have hf : (∑' ν, χ ν*W (idealExponentNorm ν/Z)) =
      ∑' ν, if ∀ p ∈ (idealExponentOf (3*r)).support, ν p = 0 then
        ω ν*W (idealExponentNorm ν/Z) else 0 := by
    apply tsum_congr
    intro ν
    dsimp only [χ,ω]
    rw [angular_twisted_residue_restriction ha hb hsa hsb hab hr hsmall ψ η ℓ hu hη hagree]
    split <;> simp
  rw [hf]
  simpa only [ω,mul_assoc] using smooth_ideal_euler_exclusion
    (idealExponentOf (3*r)).support ω hω W hW hZ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedPrimitive
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual primitive reduction after a fixed small character twist. The
variable squarefree conductor is detected, rather than postulated. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

 theorem angular_twisted_mixed_primitive_conductor {a b r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (hnu : ¬ IsUnit (a*b)) (η : MulChar (Residues r) ℂ)
    (ℓ : ℤ) (hη : AngularUnitCompatible r η ℓ) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ ψ ≠ 1 ∧
      normNat d ≤ normNat ((3*(a*b))*r) ∧ a*b ∣ d ∧
      AngularUnitCompatible d ψ ℓ ∧
      ResidueCharacterInduces ((3*(a*b))*r) d
        (productResidueChar (primaryMixedResidueChar a b ha hb) η) ψ ∧
      (∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
        ψ (Ideal.Quotient.mk (modulus d) x) =
          mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) := by
  have hq : (3*(a*b))*r ≠ (0:Eisenstein) :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))) hr
  obtain ⟨d,ψ,hd,hind,hN,hprim⟩ := primitive_residue_conductor_exists hq
    (productResidueChar (primaryMixedResidueChar a b ha hb) η)
  have hqx (x : Eisenstein) (hx : primary x) (hcop : IsCoprime (a*b*r) x) :
      IsCoprime ((3*(a*b))*r) x :=
    ((primary_coprime_three hx).symm.mul_left hcop.of_mul_left_left).mul_left
      hcop.of_mul_left_right
  have hagree (x : Eisenstein) (hx : primary x) (hcop : IsCoprime (a*b*r) x) :
      ψ (Ideal.Quotient.mk (modulus d) x) =
        mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x) := by
    rw [hind.2 x (hqx x hx hcop),productResidueChar_mk,
      primaryMixedResidueChar_primary ha hb hx]
  have hdiv := twisted_conductor_contains ha hb hsa hsb hab hsmall ψ η hagree
  have hn : ψ ≠ 1 := by
    intro he
    have h1 (x : Eisenstein) (hx : primary x) (hcop : IsCoprime (a*b*r) x) :
        (1 : MulChar (Residues (1:Eisenstein)) ℂ) (Ideal.Quotient.mk (modulus 1) x) =
          mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x) := by
      have hg := hagree x hx hcop
      rw [he,MulChar.one_apply (residue_isUnit_of_isCoprime
        ((hqx x hx hcop).of_isCoprime_of_dvd_left hind.1))] at hg
      rw [MulChar.one_apply (residue_isUnit_of_isCoprime (isCoprime_one_left))]
      exact hg
    exact hnu (isUnit_of_dvd_one
      (twisted_conductor_contains ha hb hsa hsb hab hsmall 1 η h1))
  refine ⟨d,ψ,hd,hprim,hn,hN,hdiv,?_,hind,hagree⟩
  apply hind.angular_units
  intro u
  rw [productResidueChar_mk, primaryMixedResidueChar_trivialInfinity ha hb u,one_mul]
  exact hη u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MixedPrimitiveData
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chosen arithmetic data for the actual primitive mixed character.
All fields are proved from the original squarefree coprime pair. -/
noncomputable section
namespace CubicFirstMoment

lemma residueHeckeScale_sq {d : Eisenstein} (hd : d ≠ 0) :
    (residueHeckeScale d)^2 = 3*norm d/(2*Real.pi)^2 := by
  unfold residueHeckeScale
  rw [div_pow,Real.sq_sqrt (by positivity [norm_pos_of_ne_zero hd])]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedPrimitiveFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing the actual primitive characters for a finite family, with
uniform arithmetic conductor bounds and the exact angular unit condition. -/
noncomputable section
namespace CubicFirstMoment

 theorem actual_primitive_angular_smalltwist_family (P : Finset Eisenstein) {b r : Eisenstein}
    (hb : primary b) (hsb : Squarefree b) (hr : r ≠ 0) (η : MulChar (Residues r) ℂ)
    (ℓ : ℤ) (hη : AngularUnitCompatible r η ℓ)
    (hP : ∀ a ∈ P, primary a ∧ Squarefree a ∧ IsCoprime a b ∧ ¬ IsUnit (a*b))
    (hsmall : ∀ a ∈ P, IsCoprime (a*b) r) :
    ∃ (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ),
      ∀ a ∈ P, PrimitiveAngularSmallTwistSpecification a b r (d a) η (ψ a) ℓ := by
  have hex (a : Eisenstein) : ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      a ∈ P → PrimitiveAngularSmallTwistSpecification a b r d η ψ ℓ := by
    by_cases ha : a ∈ P
    · obtain ⟨d,ψ,hd,hprim,hn,hN,_,hu,_,hag⟩ := angular_twisted_mixed_primitive_conductor
        (hP a ha).1 hb (hP a ha).2.1 hsb (hP a ha).2.2.1 hr
        (hsmall a ha) (hP a ha).2.2.2 η ℓ hη
      refine ⟨d,ψ,fun _ => ⟨hd,hprim,hn,hu,hag,?_⟩⟩
      have h3 : norm (3:Eisenstein) = 9 := by
        change Complex.normSq (3:ℂ) = 9
        norm_num [Complex.normSq]
      have hN' : norm d ≤ 9*norm a*norm b*norm r := by
        have h : norm d ≤ norm ((3*(a*b))*r) := by
          simpa only [normNat_cast] using (Nat.cast_le (α := ℝ).mpr hN)
        calc
          norm d ≤ norm ((3*(a*b))*r) := h
          _ = _ := by rw [norm_mul_eq,norm_mul_eq,norm_mul_eq,h3]; ring
      rw [residueHeckeScale_sq hd]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith
    · exact ⟨1,1,fun h => False.elim (ha h)⟩
  choose d ψ hspec using hex
  exact ⟨d,ψ,hspec⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallEulerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The count and norm of the exact Euler rescalings at a small modulus. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma euler_part_norm_le {v : Eisenstein} (hv : v ≠ 0)
    {T : Finset EisensteinIdealPrime} (hT : T ∈ (idealExponentOf v).support.powerset) :
    idealExponentNorm (primeSetExponent T) ≤ norm v := by
  have hle : primeSetExponent T ≤ idealExponentOf v := by
    apply (primeSetExponent_le_iff T (idealExponentOf v)).mpr
    intro p hp
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Finset.mem_powerset.mp hT) hp))
  have hnorm := norm_le_of_dvd (idealExponentGenerator_ne_zero (idealExponentOf v))
    (idealExponentGenerator_dvd_of_le hle)
  have hn : idealExponentNorm (primeSetExponent T) ≤ idealExponentNorm (idealExponentOf v) := by
    simpa only [idealExponentNorm,normNat_cast] using hnorm
  rwa [idealExponentOf_norm hv] at hn

 theorem euler_parts_card_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Eisenstein, v ≠ 0 →
      (((idealExponentOf v).support.powerset).card:ℝ) ≤ C*norm v^ε := by
  obtain ⟨C,hC,hbound⟩ := ideal_divisor_product_small_power hε
  refine ⟨C,hC,?_⟩
  intro v hv
  have hpoint : ∀ p ∈ (idealExponentOf v).support,
      (2:ℝ) ≤ (idealExponentOf v p:ℝ)+1 := by
    intro p hp
    have hn : (1:ℝ) ≤ idealExponentOf v p := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp))
    linarith
  calc
    _ = ∏ _p ∈ (idealExponentOf v).support, (2:ℝ) := by
      simp only [Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat,Finset.prod_const]
    _ ≤ ∏ p ∈ (idealExponentOf v).support, ((idealExponentOf v p:ℝ)+1) :=
      Finset.prod_le_prod (fun _ _ => by norm_num) hpoint
    _ ≤ C*idealExponentNorm (idealExponentOf v)^ε := hbound _
    _ = C*norm v^ε := by rw [idealExponentOf_norm hv]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmallTwistSmoothMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original primary mixed smooth sum has the cubic second moment.
Its primitive characters, conductors, and Euler corrections are constructed. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primary_angular_smalltwist_smooth_cubic_moment (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    {ε : ℝ} (hε : 0 < ε) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (P : Finset Eisenstein) (b q : Eisenstein) (η : MulChar (Residues q) ℂ) (N Y Z J t : ℝ),
      primary b → Squarefree b → q ≠ 0 →
      (AngularUnitCompatible q η ℓ) →
      (∀ a ∈ P, IsCoprime (a*b) q) →
      1 ≤ N → 1 ≤ Y → 9*norm q ≤ Z → 1 ≤ J →
      Z ≤ Y^H → J ≤ Y^H →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧
        IsCoprime a b ∧ ¬ IsUnit (a*b)) →
      ((243*N*norm b*norm q^2/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      (∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2) ≤
        C*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*q)^(3*ε) +
          D*P.card*Y^(-2*R)*norm (3*q)^(2*ε) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := full_smooth_angular_twisted_primitive_cubic_bound hpub ℓ hε
    W hW hpos hsm hδ H R hGI hGQ
  obtain ⟨E,hE,hEbound⟩ := euler_parts_card_small_power hε
  refine ⟨C*E^2,D*E^2,by positivity,by positivity,?_⟩
  intro P b q η N Y Z J t hb hsb hq hη hsmall hN hY hZ hJ hZH hJH hP hcut
  let K := (idealExponentOf (3*q)).support.powerset
  have h3q : (3:Eisenstein)*q ≠ 0 := mul_ne_zero (by norm_num) hq
  have h3 : norm (3:Eisenstein) = 9 := by
    change Complex.normSq (3:ℂ) = 9
    norm_num [Complex.normSq]
  have hNq : 0 < norm q := norm_pos_of_ne_zero hq
  have hNpow : 0 ≤ norm (3*q)^ε := Real.rpow_nonneg (norm_nonneg _) _
  have hZ0 : 0 < Z := lt_of_lt_of_le (by positivity) hZ
  obtain ⟨d,ψ,hspec⟩ := actual_primitive_angular_smalltwist_family P hb hsb hq η ℓ hη
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.2.1,(hP a ha).2.2.2.2⟩) hsmall
  let V (a : Eisenstein) (T : Finset EisensteinIdealPrime) : ℂ :=
    ∑' ν, angularResidueIdealChar (d a) (ψ a) ℓ ν*mellinPhase t (idealExponentNorm ν)*
      W (idealExponentNorm ν/(Z/idealExponentNorm (primeSetExponent T)))
  let F (a : Eisenstein) (T : Finset EisensteinIdealPrime) : ℂ :=
    (-1:ℂ)^T.card*angularResidueIdealChar (d a) (ψ a) ℓ (primeSetExponent T)*
      mellinPhase t (idealExponentNorm (primeSetExponent T))*V a T
  let B := C*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*q)^ε + D*P.card*Y^(-2*R)
  have hrow (T : Finset EisensteinIdealPrime) (hT : T ∈ K) :
      (∑ a ∈ P, ‖F a T‖^2) ≤ B := by
    let r := idealExponentNorm (primeSetExponent T)
    have hr : 1 ≤ r := idealExponentNorm_ge_one _
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    have hr9 : r ≤ 9*norm q := by
      simpa only [norm_mul_eq,h3] using euler_part_norm_le h3q hT
    have hZr : 1 ≤ Z/r := (le_div_iff₀ hr0).mpr (by linarith)
    have hZrZ : Z/r ≤ Z := div_le_self hZ0.le hr
    have hlocal (a : Eisenstein) (ha : a ∈ P) :
        ((residueHeckeScale (d a))^2*(1+|t|)^2)/((Z/r)*J) ≤ Y^(-δ) := by
      have hb0 : 0 ≤ norm b := norm_nonneg b
      have hB0 : 0 ≤ 27*N*norm b*norm q/(2*Real.pi)^2 := by positivity
      have haN : (residueHeckeScale (d a))^2 ≤ 27*N*norm b*norm q/(2*Real.pi)^2 :=
        (hspec a ha).2.2.2.2.2.trans (by gcongr; exact (hP a ha).2.2.1)
      have hprod : r*(residueHeckeScale (d a))^2 ≤ (9*norm q)*(27*N*norm b*norm q/(2*Real.pi)^2) :=
        mul_le_mul hr9 haN (sq_nonneg _) (by positivity)
      calc
        _ = (r*(residueHeckeScale (d a))^2*(1+|t|)^2)/(Z*J) := by
          field_simp
        _ ≤ ((9*norm q)*(27*N*norm b*norm q/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hprod (sq_nonneg _)) (by positivity)
        _ = ((243*N*norm b*norm q^2/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) := by ring
        _ ≤ _ := hcut
    have hv := hbound P b d ψ q η N Y (Z/r) J t hb hsb hq hη hsmall hN hY hZr hJ
      (hZrZ.trans hZH) hJH
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.1,(hP a ha).2.2.2.1⟩)
      (fun a ha => (hspec a ha).1) (fun a ha => (hspec a ha).2.1)
      (fun a ha => Or.inr (hspec a ha).2.2.1) (fun a ha => (hspec a ha).2.2.2.1)
      (fun a ha => (hspec a ha).2.2.2.2.1) hlocal
    calc
      _ ≤ ∑ a ∈ P, ‖V a T‖^2 := by
        apply Finset.sum_le_sum
        intro a ha
        have hc : ‖(-1:ℂ)^T.card*angularResidueIdealChar (d a) (ψ a) ℓ (primeSetExponent T)*
            mellinPhase t (idealExponentNorm (primeSetExponent T))‖ ≤ 1 := by
          simpa only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
            mellinPhase_norm,mul_one] using
            angularResidueIdealChar_norm_le_one (hspec a ha).1 (ψ a) ℓ (primeSetExponent T)
        apply pow_le_pow_left₀ (_root_.norm_nonneg _)
        exact (norm_mul _ _).trans_le (mul_le_of_le_one_left (_root_.norm_nonneg _) hc)
      _ ≤ C*(Z/r)*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*q)^ε + D*P.card*Y^(-2*R) := hv
      _ ≤ B := by dsimp [B]; gcongr
  have hsplit (a : Eisenstein) (ha : a ∈ P) :
      primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t = ∑ T ∈ K, F a T :=
    primary_angular_smalltwist_euler (hP a ha).1 hb (hP a ha).2.1 hsb
      (hP a ha).2.2.2.1 hq (hsmall a ha) (ψ a) η ℓ (hspec a ha).2.2.2.1 hη
      (hspec a ha).2.2.2.2.1 W hW hZ0 t
  calc
    _ = ∑ a ∈ P, ‖∑ T ∈ K, F a T‖^2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hsplit a ha]
    _ ≤ (K.card:ℝ)*∑ T ∈ K, ∑ a ∈ P, ‖F a T‖^2 := complex_mass_sum_sq_le K P F
    _ ≤ (K.card:ℝ)*∑ _T ∈ K, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (Nat.cast_nonneg _)
    _ = (K.card:ℝ)^2*B := by simp; ring
    _ ≤ (E*norm (3*q)^ε)^2*B := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (hEbound (3*q) h3q) 2) (by dsimp [B]; positivity)
    _ = _ := by
      have hNp : 0 < norm (3*q) := norm_pos_of_ne_zero h3q
      have h2 : (norm (3*q)^ε)^2 = norm (3*q)^(2*ε) := by
        rw [← Real.rpow_mul_natCast hNp.le]
        congr 1
        norm_num
        ring
      dsimp [B]
      rw [mul_pow,h2]
      rw [show 3*ε = ε+2*ε by ring,Real.rpow_add hNp]
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallTwistPower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit positive saving for dominant smooth factors with a small
extra finite character, including all Euler rescaling costs. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma small_modulus_rpow {q : Eisenstein} {Y s : ℝ} (hY : 1 ≤ Y) (hs : 0 ≤ s)
    (hq : norm q ≤ Y^(1/1000:ℝ)) :
    norm (3*q)^s ≤ (9:ℝ)^s*Y^(s/1000) := by
  have h3 : norm (3:Eisenstein) = 9 := by
    change Complex.normSq (3:ℂ) = 9
    norm_num [Complex.normSq]
  rw [norm_mul_eq,h3,Real.mul_rpow (by norm_num) (norm_nonneg q)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  calc
    _ ≤ (Y^(1/1000:ℝ))^s := Real.rpow_le_rpow (norm_nonneg q) hq hs
    _ = _ := by rw [← Real.rpow_mul (by linarith : 0 ≤ Y)]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic-sieve envelope for balanced conductor variables. -/
noncomputable section
namespace CubicFirstMoment

lemma balanced_cubic_envelope :
    ∃ K : ℝ, 0 < K ∧ ∀ N Z J Y : ℝ, 1 ≤ Y → 1 ≤ N → 1 ≤ Z → 1 ≤ J →
      N ≤ Y^(1/2:ℝ) → Z ≤ Y^(101/100:ℝ) → J ≤ Y^(1/2:ℝ) →
      Z*(N*(2*J))^(1/100:ℝ)*(N+2*J+(N*(2*J))^(2/3:ℝ)) ≤ K*Y^(17/10:ℝ) := by
  let K : ℝ := (2:ℝ)^(1/100:ℝ)*(3+(2:ℝ)^(2/3:ℝ))
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro N Z J Y hY hN hZ hJ hNY hZY hJY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ : N*(2*J) ≤ 2*Y^(1:ℝ) := by
    calc
      _ ≤ Y^(1/2:ℝ)*(2*Y^(1/2:ℝ)) := by gcongr
      _ = 2*(Y^(1/2:ℝ)*Y^(1/2:ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hY0]; norm_num
  have hpow (s : ℝ) (hs : 0 ≤ s) :
      (N*(2*J))^s ≤ (2:ℝ)^s*Y^((1)*s) := by
    calc
      _ ≤ (2*Y^(1:ℝ))^s := Real.rpow_le_rpow (by positivity) hQ hs
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hY0.le _),
        ← Real.rpow_mul hY0.le]
  have hsmall := hpow (1/100) (by norm_num)
  have hlarge := hpow (2/3) (by norm_num)
  norm_num at hsmall hlarge
  have hnF : N ≤ Y^(2/3:ℝ) := hNY.trans
    (Real.rpow_le_rpow_of_exponent_le hY (by norm_num))
  have hjF : J ≤ Y^(2/3:ℝ) := hJY.trans
    (Real.rpow_le_rpow_of_exponent_le hY (by norm_num))
  have hF : N+2*J+(N*(2*J))^(2/3:ℝ) ≤
      (3+(2:ℝ)^(2/3:ℝ))*Y^(2/3:ℝ) := by nlinarith
  calc
    _ ≤ Y^(101/100:ℝ)*((2:ℝ)^(1/100:ℝ)*Y^(1/100:ℝ))*
        ((3+(2:ℝ)^(2/3:ℝ))*Y^(2/3:ℝ)) := by
      exact mul_le_mul (mul_le_mul hZY hsmall (by positivity) (by positivity)) hF
        (by positivity) (by positivity)
    _ = K*Y^((101/100:ℝ)+1/100+2/3) := by
      dsimp [K]
      rw [Real.rpow_add hY0,Real.rpow_add hY0]
      ring
    _ ≤ K*Y^(17/10:ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by dsimp [K]; positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularBalancedSmallTwistPower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Power saving for the full smooth factor with balanced conductor variables. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

 theorem balanced_angular_smalltwist_smooth_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Finset Eisenstein) (b q : Eisenstein)
      (η : MulChar (Residues q) ℂ) (N Y Z J t : ℝ),
      primary b → Squarefree b → q ≠ 0 →
      (AngularUnitCompatible q η ℓ) →
      (∀ a ∈ P, IsCoprime (a*b) q) →
      1 ≤ N → 1 ≤ Y → 9*norm q ≤ Z → 1 ≤ J →
      N ≤ Y^(1/2:ℝ) → Z ≤ Y^(101/100:ℝ) → J ≤ Y^(1/2:ℝ) →
      norm q ≤ Y^(1/1000:ℝ) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b ∧ ¬ IsUnit (a*b)) →
      ((243*N*norm b*norm q^2/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) ≤ Y^(-(1/1000:ℝ)) →
      (∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2) ≤ C*Y^(9/5:ℝ) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := primary_angular_smalltwist_smooth_cubic_moment hpub ℓ
    (show (0:ℝ) < 1/100 by norm_num) W hW hpos hsm
    (show (0:ℝ) < 1/1000 by norm_num) 2 2 hGI hGQ
  obtain ⟨K,hK,henv⟩ := balanced_cubic_envelope
  refine ⟨C*K*(9:ℝ)^(3/100:ℝ)+18*D*(9:ℝ)^(1/50:ℝ),by positivity,?_⟩
  intro P b q η N Y Z J t hb hsb hq hη hsmall hN hY hZ hJ hNY hZY hJY hqY hP hcut
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hZ1 : 1 ≤ Z := (by nlinarith [one_le_norm hq] : (1:ℝ) ≤ 9*norm q).trans hZ
  have hbound' := hbound P b q η N Y Z J t hb hsb hq hη hsmall hN hY hZ hJ
    (hZY.trans (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)))
    (hJY.trans (Real.rpow_le_rpow_of_exponent_le hY (by norm_num))) hP hcut
  have hcard : (P.card:ℝ) ≤ 18*N := by
    have hsub : P ⊆ primaryElementBall N :=
      fun a ha => mem_primaryElementBall.mpr ⟨(hP a ha).1,(hP a ha).2.2.1⟩
    exact (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)).trans
      (primaryElementBall_card_le (by linarith))
  have hq3 := small_modulus_rpow hY (show (0:ℝ) ≤ 3/100 by norm_num) hqY
  have hq2 := small_modulus_rpow hY (show (0:ℝ) ≤ 1/50 by norm_num) hqY
  norm_num only [div_div] at hq3 hq2
  have hm : C*Z*(N*(2*J))^(1/100:ℝ)*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*q)^(3*(1/100:ℝ)) ≤
      (C*K*(9:ℝ)^(3/100:ℝ))*Y^(9/5:ℝ) := by
    calc
      _ ≤ (C*(K*Y^(17/10:ℝ)))*((9:ℝ)^(3/100:ℝ)*Y^((3/100:ℝ)/1000)) := by
        apply mul_le_mul _ (by convert hq3 using 1 <;> first | (with_reducible_and_instances rfl) | norm_num) (Real.rpow_nonneg (norm_nonneg (3*q)) _) (by positivity)
        have h := mul_le_mul_of_nonneg_left (henv N Z J Y hY hN hZ1 hJ hNY hZY hJY) hC
        simpa only [mul_assoc] using h
      _ = (C*K*(9:ℝ)^(3/100:ℝ))*Y^((17/10:ℝ)+(3/100)/1000) := by
        rw [Real.rpow_add hY0]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity)
  have ht : D*P.card*Y^(-(2:ℝ)*2)*norm (3*q)^(2*(1/100:ℝ)) ≤
      (18*D*(9:ℝ)^(1/50:ℝ))*Y^(9/5:ℝ) := by
    have hpow : Y^(-(2:ℝ)*2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY (by norm_num)
    calc
      _ ≤ (D*(18*Y^(101/100:ℝ))*1)*((9:ℝ)^(1/50:ℝ)*Y^((1/50:ℝ)/1000)) := by
        apply mul_le_mul _ (by convert hq2 using 1 <;> first | (with_reducible_and_instances rfl) | norm_num) (Real.rpow_nonneg (norm_nonneg (3*q)) _) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (hcard.trans (mul_le_mul_of_nonneg_left
          (hNY.trans (Real.rpow_le_rpow_of_exponent_le hY (by norm_num))) (by norm_num))) hD) hpow (by positivity) (by positivity)
      _ = (18*D*(9:ℝ)^(1/50:ℝ))*Y^((101/100:ℝ)+(1/50)/1000) := by
        rw [Real.rpow_add hY0]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity)
  exact hbound'.trans (by nlinarith [hm,ht])

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural dual length for balanced conductors at height Y^0.37. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventual_balanced_natural_cutoff :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y N B Z t : ℝ, Y₀ ≤ Y → 0 ≤ N → 0 ≤ B →
      N ≤ Y^(17/50:ℝ) → B ≤ Y^(171/500:ℝ) →
      Y^(999/1000:ℝ) ≤ Z → |t| ≤ Y^(37/100:ℝ) →
      ((243*N*B/(2*Real.pi)^2)*(1+|t|)^2)/(Z*Y^(1/2:ℝ)) ≤ Y^(-(1/1000:ℝ)) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 76/1000 by norm_num)).eventually_ge_atTop (972:ℝ))
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y N B Z t hY hN hB hNY hBY hZY ht
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hscale : 972 ≤ Y^(76/1000:ℝ) := hT Y ((le_max_right _ _).trans hY)
  have hZ0 : 0 < Z := (Real.rpow_pos_of_pos hY0 _).trans_le hZY
  have hπ : (1:ℝ) ≤ (2*Real.pi)^2 := by have := Real.pi_gt_three; nlinarith
  have ht' : 1+|t| ≤ 2*Y^(37/100:ℝ) := by
    have := Real.one_le_rpow hY1 (by norm_num : (0:ℝ) ≤ 37/100)
    linarith
  have htpow : (1+|t|)^2 ≤ 4*Y^(37/50:ℝ) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|t|) ht' 2
    have he : (Y^(37/100:ℝ))^2 = Y^(37/50:ℝ) := by
      rw [← Real.rpow_mul_natCast hY0.le]
      norm_num
    simpa only [mul_pow,he,show (2:ℝ)^2 = 4 by norm_num] using h
  have hNB : N*B ≤ Y^(341/500:ℝ) := by
    calc
      _ ≤ Y^(17/50:ℝ)*Y^(171/500:ℝ) :=
        mul_le_mul hNY hBY hB (Real.rpow_nonneg hY0.le _)
      _ = _ := by rw [← Real.rpow_add hY0]; norm_num
  have hnum : (243*N*B/(2*Real.pi)^2)*(1+|t|)^2 ≤ 972*Y^(711/500:ℝ) := by
    calc
      _ ≤ (243*(N*B))*(4*Y^(37/50:ℝ)) := by
        apply mul_le_mul _ htpow (sq_nonneg _) (by positivity)
        simpa only [mul_assoc] using div_le_self (by positivity : 0 ≤ 243*N*B) hπ
      _ ≤ (243*Y^(341/500:ℝ))*(4*Y^(37/50:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNB (by norm_num)) (by positivity)
      _ = 972*(Y^(341/500:ℝ)*Y^(37/50:ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hY0]; norm_num
  have hden : Y^(1499/1000:ℝ) ≤ Z*Y^(1/2:ℝ) := by
    calc
      _ = Y^(999/1000:ℝ)*Y^(1/2:ℝ) := by rw [← Real.rpow_add hY0]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hZY (Real.rpow_nonneg hY0.le _)
  calc
    _ ≤ (972*Y^(711/500:ℝ))/Y^(1499/1000:ℝ) :=
      div_le_div₀ (by positivity) hnum (Real.rpow_pos_of_pos hY0 _) hden
    _ = 972*Y^(-(77/1000:ℝ)) := by
      rw [mul_div_assoc,← Real.rpow_sub hY0]
      norm_num
    _ ≤ Y^(76/1000:ℝ)*Y^(-(77/1000:ℝ)) :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hY0.le _)
    _ = _ := by rw [← Real.rpow_add hY0]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularBalancedSmallTwistCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The natural cutoff and lower rescaled length for a small-twisted
full sum, uniformly up to the required height Y^0.37. -/
noncomputable section
open Filter Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

 theorem balanced_angular_smalltwist_smooth_power_at_height (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (P : Finset Eisenstein) (b q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (N Y Z t : ℝ), Y₀ ≤ Y → primary b → Squarefree b → q ≠ 0 →
      (AngularUnitCompatible q η ℓ) →
      (∀ a ∈ P, IsCoprime (a*b) q) → 1 ≤ N →
      N ≤ Y^(17/50:ℝ) → Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      norm b ≤ Y^(17/50:ℝ) → norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b ∧ ¬ IsUnit (a*b)) →
      (∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2) ≤ C*Y^(9/5:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := balanced_angular_smalltwist_smooth_power hpub ℓ W hW hpos hsm hGI hGQ
  obtain ⟨A,hA,hcut⟩ := eventual_balanced_natural_cutoff
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 998/1000 by norm_num)).eventually_ge_atTop (9:ℝ))
  refine ⟨C,max A T,hC,hA.trans (le_max_left _ _),?_⟩
  intro P b q η N Y Z t hY hb hsb hq hη hsmall hN hNY hZY hYZ hbY hqY ht hP
  have hYA : A ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := hA.trans hYA
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hB : norm b*norm q^2 ≤ Y^(171/500:ℝ) := by
    calc
      _ ≤ Y^(17/50:ℝ)*(Y^(1/1000:ℝ))^2 :=
        mul_le_mul hbY (pow_le_pow_left₀ (norm_nonneg q) hqY 2)
          (sq_nonneg _) (Real.rpow_nonneg hY0.le _)
      _ = _ := by
        rw [← Real.rpow_mul_natCast hY0.le,← Real.rpow_add hY0]
        norm_num
  have h9 : 9 ≤ Y^(998/1000:ℝ) := hT Y ((le_max_right _ _).trans hY)
  have hZ : 9*norm q ≤ Z := by
    calc
      _ ≤ 9*Y^(1/1000:ℝ) := mul_le_mul_of_nonneg_left hqY (by norm_num)
      _ ≤ Y^(998/1000:ℝ)*Y^(1/1000:ℝ) :=
        mul_le_mul_of_nonneg_right h9 (Real.rpow_nonneg hY0.le _)
      _ = Y^(999/1000:ℝ) := by rw [← Real.rpow_add hY0]; norm_num
      _ ≤ Z := hYZ
  have hJ : 1 ≤ Y^(1/2:ℝ) := Real.one_le_rpow hY1 (by norm_num)
  have hc := hcut Y N (norm b*norm q^2) Z t hYA (by linarith)
    (by positivity [norm_nonneg b]) hNY hB hYZ ht
  apply hbound P b q η N Y Z (Y^(1/2:ℝ)) t hb hsb hq hη hsmall hN hY1 hZ hJ
    (hNY.trans (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)))
    (hZY.trans (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))) le_rfl hqY hP
  simpa only [mul_assoc] using hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogSmoothWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma logSmoothWeight_compact {W : ℝ → ℂ} (hW : HasCompactSupport W) :
    HasCompactSupport (logSmoothWeight W) :=
  hW.mul_left (f := fun x : ℝ => (Real.log x:ℂ))

lemma logSmoothWeight_positive {W : ℝ → ℂ} (hpos : tsupport W ⊆ Ioi 0) :
    tsupport (logSmoothWeight W) ⊆ Ioi 0 := tsupport_mul_subset_right.trans hpos

lemma logSmoothWeight_smooth {W : ℝ → ℂ} (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (logSmoothWeight W) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : (0:ℝ) ∉ tsupport W := fun h => (lt_irrefl (0:ℝ)) (hpos h)
    have he := notMem_tsupport_iff_eventuallyEq.mp hz
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    change W y = 0 at hy
    simp only [logSmoothWeight,hy,mul_zero]
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (Real.contDiffAt_log.mpr hx)).mul hsm.contDiffAt

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

 theorem primary_log_smooth_decomposition (c : Eisenstein → ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    (∑' a : Eisenstein, if primary a then
      (Real.log (norm a):ℂ)*c a*W (norm a/Z) else 0) =
      (Real.log Z:ℂ)*(∑' a : Eisenstein, if primary a then c a*W (norm a/Z) else 0)+
      ∑' a : Eisenstein, if primary a then c a*logSmoothWeight W (norm a/Z) else 0 := by
  obtain ⟨B,_,hB⟩ := compactSupport_upper_cutoff W hW
  have hBlog (x : ℝ) (hx : B < x) : logSmoothWeight W x = 0 := by
    rw [logSmoothWeight,hB x hx,mul_zero]
  rw [primary_weighted_smooth_finite _ W hZ hB,
    primary_weighted_smooth_finite c W hZ hB,
    primary_weighted_smooth_finite c (logSmoothWeight W) hZ hBlog,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hn : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp ha).1)
  have hlog : Real.log (norm a) = Real.log Z+Real.log (norm a/Z) := by
    rw [Real.log_div hn.ne' hZ.ne']
    ring
  rw [hlog,Complex.ofReal_add,logSmoothWeight]
  ring

lemma primary_log_smooth_sq_le (c : Eisenstein → ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    ‖∑' a : Eisenstein, if primary a then
      (Real.log (norm a):ℂ)*c a*W (norm a/Z) else 0‖^2 ≤
      2*(Real.log Z)^2*‖∑' a : Eisenstein, if primary a then c a*W (norm a/Z) else 0‖^2+
      2*‖∑' a : Eisenstein, if primary a then c a*logSmoothWeight W (norm a/Z) else 0‖^2 := by
  rw [primary_log_smooth_decomposition c W hW hZ]
  let u : ℂ := ∑' a : Eisenstein, if primary a then c a*W (norm a/Z) else 0
  let v : ℂ := ∑' a : Eisenstein, if primary a then c a*logSmoothWeight W (norm a/Z) else 0
  change ‖(Real.log Z:ℂ)*u+v‖^2 ≤ 2*(Real.log Z)^2*‖u‖^2+2*‖v‖^2
  have ht := norm_add_le ((Real.log Z:ℂ)*u) v
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs] at ht
  have hs := pow_le_pow_left₀ (_root_.norm_nonneg _) ht 2
  nlinarith [sq_nonneg (|Real.log Z| * ‖u‖-‖v‖),sq_abs (Real.log Z)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedFullRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collection over the second conductor variable, with literal row fibers. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_pairFirstFiber {S : Finset (Eisenstein × Eisenstein)} {a b : Eisenstein} :
    a ∈ pairFirstFiber S b ↔ (a,b) ∈ S := by
  simp only [pairFirstFiber,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨⟨x,y⟩,⟨h,hy⟩,hx⟩
    change x = a at hx
    change y = b at hy
    subst x
    subst y
    exact h
  · intro h
    exact ⟨(a,b),⟨h,rfl⟩,rfl⟩

lemma pair_sum_fibers (S : Finset (Eisenstein × Eisenstein))
    (f : Eisenstein × Eisenstein → ℝ) :
    (∑ p ∈ S, f p) = ∑ b ∈ S.image Prod.snd, ∑ a ∈ pairFirstFiber S b, f (a,b) := by
  have hf (b : Eisenstein) : (∑ a ∈ pairFirstFiber S b, f (a,b)) =
      ∑ p ∈ S.filter (fun p => p.2 = b), f p := by
    unfold pairFirstFiber
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [← (Finset.mem_filter.mp hp).2]
    · intro p hp q hq he
      exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
  simp_rw [hf]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun p hp => Finset.mem_image_of_mem Prod.snd hp) f).symm

lemma balanced_pair_moment_collection (S : Finset (Eisenstein × Eisenstein))
    (f : Eisenstein × Eisenstein → ℝ) {Y C γ : ℝ} (hY : 1 ≤ Y) (hC : 0 ≤ C)
    (hS : ∀ p ∈ S, primary p.2 ∧ norm p.2 ≤ Y^(17/50:ℝ))
    (hf : ∀ b ∈ S.image Prod.snd, (∑ a ∈ pairFirstFiber S b, f (a,b)) ≤ C*Y^γ) :
    (∑ p ∈ S, f p) ≤ (18*C)*Y^(2/5+γ) := by
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hsub : S.image Prod.snd ⊆ primaryElementBall (Y^(17/50:ℝ)) := by
    intro b hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
    exact mem_primaryElementBall.mpr (hS p hp)
  have hcard : ((S.image Prod.snd).card:ℝ) ≤ 18*Y^(2/5:ℝ) := by
    calc
      _ ≤ ((primaryElementBall (Y^(17/50:ℝ))).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ 18*Y^(17/50:ℝ) := primaryElementBall_card_le (Real.rpow_nonneg hY0.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by norm_num)
  calc
    _ = ∑ b ∈ S.image Prod.snd, ∑ a ∈ pairFirstFiber S b, f (a,b) := pair_sum_fibers S f
    _ ≤ ∑ _b ∈ S.image Prod.snd, C*Y^γ := Finset.sum_le_sum hf
    _ = ((S.image Prod.snd).card:ℝ)*(C*Y^γ) := by simp
    _ ≤ (18*Y^(2/5:ℝ))*(C*Y^γ) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hC (Real.rpow_nonneg hY0.le _))
    _ = _ := by rw [Real.rpow_add hY0]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularBalancedFullRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collection over the second conductor variable, with literal row fibers. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem balanced_angular_smalltwist_pair_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (S : Finset (Eisenstein × Eisenstein)) (q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (Y Z t : ℝ), Y₀ ≤ Y → q ≠ 0 →
      (AngularUnitCompatible q η ℓ) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z → norm q ≤ Y^(1/1000:ℝ) →
      |t| ≤ Y^(37/100:ℝ) →
      (∀ p ∈ S, primary p.1 ∧ Squarefree p.1 ∧ primary p.2 ∧ Squarefree p.2 ∧
        norm p.1 ≤ Y^(17/50:ℝ) ∧ norm p.2 ≤ Y^(17/50:ℝ) ∧
        IsCoprime p.1 p.2 ∧ ¬ IsUnit (p.1*p.2) ∧ IsCoprime (p.1*p.2) q) →
      (∑ p ∈ S, ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2) ≤ C*Y^(11/5:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := balanced_angular_smalltwist_smooth_power_at_height hpub ℓ W hW hpos hsm hGI hGQ
  refine ⟨18*C,T,by positivity,hT,?_⟩
  intro S q η Y Z t hY hq hη hZY hYZ hqY ht hS
  have hY1 : 1 ≤ Y := hT.trans hY
  have hrow (b : Eisenstein) (hb : b ∈ S.image Prod.snd) :
      (∑ a ∈ pairFirstFiber S b, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2) ≤ C*Y^(9/5:ℝ) := by
    obtain ⟨p,hp,hpb⟩ := Finset.mem_image.mp hb
    have hbp := hS p hp
    apply hbound (pairFirstFiber S b) b q η (Y^(17/50:ℝ)) Y Z t hY
      (hpb ▸ hbp.2.2.1) (hpb ▸ hbp.2.2.2.1) hq hη
      (fun a ha => (hS (a,b) (mem_pairFirstFiber.mp ha)).2.2.2.2.2.2.2.2)
      (Real.one_le_rpow hY1 (by norm_num)) le_rfl hZY hYZ
      (hpb ▸ hbp.2.2.2.2.2.1) hqY ht
    intro a ha
    have hs := hS (a,b) (mem_pairFirstFiber.mp ha)
    exact ⟨hs.1,hs.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.1⟩
  have hcollect := balanced_pair_moment_collection S
    (fun p => ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2) hY1 hC
    (fun p hp => ⟨(hS p hp).2.2.1,(hS p hp).2.2.2.2.2.1⟩) hrow
  convert hcollect using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallPartCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal finite-character factorization at the small conductor primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mixedCubic_modulus_mul {a₁ a₂ b₁ b₂ : Eisenstein}
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (x : Eisenstein) :
    mixedCubic (a₁*a₂) (b₁*b₂) x = mixedCubic a₁ b₁ x*mixedCubic a₂ b₂ x := by
  simp only [mixedCubic,cubicSymbol_mul_lower ha₁ ha₂,cubicSymbol_mul_lower hb₁ hb₂,star_mul]
  ring

lemma primaryOutsidePart_norm_le (v : Eisenstein) {a : Eisenstein} (ha : primary a) :
    norm (primaryOutsidePart v a) ≤ norm a := by
  apply norm_le_of_dvd (primary_ne_zero ha)
  exact ⟨primarySmallPart v a,by rw [mul_comm,primary_small_outside_mul v ha]⟩

lemma primaryOutsidePart_norm_lower (v : Eisenstein) {a : Eisenstein}
    (ha : primary a) (hsa : Squarefree a) (hv : v ≠ 0) :
    norm a/norm v ≤ norm (primaryOutsidePart v a) := by
  have hs := norm_le_of_dvd hv (primarySmallPart_dvd hsa hv)
  have hp := congrArg norm (primary_small_outside_mul v ha)
  rw [norm_mul_eq] at hp
  apply (div_le_iff₀ (norm_pos_of_ne_zero hv)).mpr
  rw [mul_comm]
  nlinarith [norm_nonneg (primaryOutsidePart v a)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmallPartCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite small-part twist preserves its fixed infinity type. -/
noncomputable section
namespace CubicFirstMoment

lemma productResidueChar_angular_units {q r : Eisenstein}
    (χ : MulChar (Residues q) ℂ) (η : MulChar (Residues r) ℂ)
    (hχ : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    {ℓ : ℤ} (hη : AngularUnitCompatible r η ℓ) :
    AngularUnitCompatible (q*r) (productResidueChar χ η) ℓ := by
  intro u
  rw [productResidueChar_mk,hχ u,one_mul]
  exact hη u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallPartGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conductor size and coprimality after the actual small-prime split. -/
noncomputable section
namespace CubicFirstMoment

lemma primaryOutsidePart_dvd (v : Eisenstein) {a : Eisenstein} (ha : primary a) :
    primaryOutsidePart v a ∣ a :=
  ⟨primarySmallPart v a,by rw [mul_comm,primary_small_outside_mul v ha]⟩

lemma outside_parts_coprime (v : Eisenstein) {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hab : IsCoprime a b) :
    IsCoprime (primaryOutsidePart v a) (primaryOutsidePart v b) :=
  (hab.of_isCoprime_of_dvd_left (primaryOutsidePart_dvd v ha)).of_isCoprime_of_dvd_right
    (primaryOutsidePart_dvd v hb)

lemma outside_parts_coprime_local {v a b q : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hv : v ≠ 0) (h3 : (3:Eisenstein) ∣ v) (hq : q ∣ v) :
    IsCoprime (primaryOutsidePart v a*primaryOutsidePart v b)
      ((3*(primarySmallPart v a*primarySmallPart v b))*q) := by
  have hc := (primaryOutsidePart_coprime ha hv).mul_left (primaryOutsidePart_coprime hb hv)
  exact (hc.of_isCoprime_of_dvd_right h3).mul_right
    ((hc.of_isCoprime_of_dvd_right (primarySmallPart_dvd hsa hv)).mul_right
      (hc.of_isCoprime_of_dvd_right (primarySmallPart_dvd hsb hv))) |>.mul_right
        (hc.of_isCoprime_of_dvd_right hq)

lemma smallPartModulus_norm_le {v a b q : Eisenstein}
    (hsa : Squarefree a) (hsb : Squarefree b) (hv : v ≠ 0) :
    norm ((3*(primarySmallPart v a*primarySmallPart v b))*q) ≤ 9*norm v^2*norm q := by
  have h3 : norm (3:Eisenstein) = 9 := by
    change Complex.normSq (3:ℂ) = 9
    norm_num [Complex.normSq]
  rw [norm_mul_eq,norm_mul_eq,norm_mul_eq,h3]
  have ha := norm_le_of_dvd hv (primarySmallPart_dvd hsa hv)
  have hb := norm_le_of_dvd hv (primarySmallPart_dvd hsb hv)
  have hmul := mul_le_mul ha hb (norm_nonneg _) (norm_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul (by norm_num : (0:ℝ) ≤ 9)) (norm_nonneg q)]

lemma primaryOutsidePart_nonunit {v a : Eisenstein}
    (ha : primary a) (hsa : Squarefree a) (hv : v ≠ 0) (hN : norm v < norm a) :
    ¬ IsUnit (primaryOutsidePart v a) := by
  intro hu
  have h := primaryOutsidePart_norm_lower v ha hsa hv
  rw [norm_of_isUnit hu] at h
  have h' := (div_le_one (norm_pos_of_ne_zero hv)).mp h
  exact (not_le_of_gt hN) h'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmallPartTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transfer from an original row fiber to its coprime outside parts. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryAngularSmallTwistSmoothSum_factor (ℓ : ℤ) {a b s u d w q : Eisenstein}
    (hs : primary s) (hu : primary u) (hd : primary d) (hw : primary w)
    (ha : a = s*u) (hb : b = d*w) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (Z t : ℝ) :
    primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t =
      primaryAngularSmallTwistSmoothSum ℓ u w ((3*(s*d))*q)
        (productResidueChar (primaryMixedResidueChar s d hs hd) η) W Z t := by
  unfold primaryAngularSmallTwistSmoothSum
  apply tsum_congr
  intro x
  by_cases hx : primary x
  · simp only [ite_eq_left hx,productResidueChar_mk,primaryMixedResidueChar_primary hs hd hx]
    rw [ha,hb,mixedCubic_modulus_mul (primary_ne_zero hs) (primary_ne_zero hu)
      (primary_ne_zero hd) (primary_ne_zero hw)]
    ring
  · simp only [ite_eq_right hx]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullSmoothFactor
attribute [-instance] _root_.instMeasurableSpace
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

lemma full_dyad_above_sqrt {F Y Z : ℝ} (hY : 1 < Y)
    (hF : F ≤ Y^(1001/1000:ℝ)) (hZ : Y^(999/1000:ℝ) ≤ Z) : Real.sqrt F < Z := by
  apply lt_of_lt_of_le _ hZ
  have hY0 : 0 < Y := zero_lt_one.trans hY
  have hs : Real.sqrt F ≤ Y^(1001/2000:ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact Real.rpow_nonneg hY0.le _
    · have he : (Y^(1001/2000:ℝ))^2 = Y^(1001/1000:ℝ) := by
        rw [← Real.rpow_mul_natCast hY0.le]
        norm_num
      rwa [he]
  exact hs.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularFullSmoothFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primaryAngularShortSmoothSum_zeta (ℓ : ℤ) (a b q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (Z t : ℝ) :
    primaryAngularShortSmoothSum ℓ idealZeta a b q η W Z t = primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t := by
  simp only [primaryAngularShortSmoothSum,primaryAngularSmallTwistSmoothSum,MvPowerSeries.coeff_apply,
    idealZeta,Complex.ofReal_one,one_mul]

lemma primaryAngularShortSmoothSum_log (ℓ : ℤ) (a b q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (Z t : ℝ) :
    primaryAngularShortSmoothSum ℓ idealLogNorm a b q η W Z t = primaryAngularSmallTwistLogSmoothSum ℓ a b q η W Z t := by
  unfold primaryAngularShortSmoothSum primaryAngularSmallTwistLogSmoothSum
  apply tsum_congr
  intro x
  by_cases hx : primary x
  · simp only [ite_eq_left hx,MvPowerSeries.coeff_apply,idealLogNorm,
      idealExponentOf_norm (primary_ne_zero hx)]
  · simp only [ite_eq_right hx]

lemma primaryAngularShortSmoothSum_moebius (ℓ : ℤ) {F Z : ℝ} (hFZ : Real.sqrt F < Z)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (hWlow : ∀ x : ℝ, x < 1 → W x = 0) (t : ℝ) :
    primaryAngularShortSmoothSum ℓ (shortIdealMoebius F) a b q η W Z t = 0 := by
  have hZ : 0 < Z := (Real.sqrt_nonneg F).trans_lt hFZ
  unfold primaryAngularShortSmoothSum
  trans ∑' _x : Eisenstein, (0:ℂ)
  swap
  · exact tsum_zero
  apply tsum_congr
  intro x
  by_cases hx : primary x
  · rw [ite_eq_left hx]
    by_cases hn : idealExponentNorm (idealExponentOf x) ≤ Real.sqrt F
    · have hxZ : norm x/Z < 1 := (div_lt_one hZ).mpr (by
        rw [idealExponentOf_norm (primary_ne_zero hx)] at hn
        exact hn.trans_lt hFZ)
      rw [hWlow _ hxZ,mul_zero]
    · simp only [MvPowerSeries.coeff_apply,shortIdealMoebius,hn,ite_false, if_false,
        Complex.ofReal_zero,zero_mul]
  · rw [ite_eq_right hx]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallPairParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact two-variable conductor partitions and their arithmetic size. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma pairOutsideParts_fiber_injective (v : Eisenstein) (s : Eisenstein × Eisenstein)
    (S : Finset (Eisenstein × Eisenstein)) (hS : ∀ p ∈ S, primary p.1 ∧ primary p.2) :
    Set.InjOn (pairOutsideParts v) ↑(S.filter (fun p => pairSmallParts v p = s)) := by
  intro p hp r hr he
  have hp' := Finset.mem_filter.mp hp
  have hr' := Finset.mem_filter.mp hr
  have hsmall : pairSmallParts v p = pairSmallParts v r := hp'.2.trans hr'.2.symm
  apply Prod.ext
  · have hs := congrArg Prod.fst hsmall
    have ho := congrArg Prod.fst he
    have ha := primary_small_outside_mul v (hS p hp'.1).1
    have hb := primary_small_outside_mul v (hS r hr'.1).1
    change primarySmallPart v p.1 = primarySmallPart v r.1 at hs
    change primaryOutsidePart v p.1 = primaryOutsidePart v r.1 at ho
    rw [hs,ho] at ha
    exact ha.symm.trans hb
  · have hs := congrArg Prod.snd hsmall
    have ho := congrArg Prod.snd he
    have ha := primary_small_outside_mul v (hS p hp'.1).2
    have hb := primary_small_outside_mul v (hS r hr'.1).2
    change primarySmallPart v p.2 = primarySmallPart v r.2 at hs
    change primaryOutsidePart v p.2 = primaryOutsidePart v r.2 at ho
    rw [hs,ho] at ha
    exact ha.symm.trans hb

lemma pair_small_parts_card {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Eisenstein × Eisenstein)) (v : Eisenstein), v ≠ 0 →
      (∀ p ∈ S, primary p.1 ∧ Squarefree p.1 ∧ primary p.2 ∧ Squarefree p.2) →
      ((S.image (pairSmallParts v)).card:ℝ) ≤ C*norm v^(2*ε) := by
  obtain ⟨D,hD,hbound⟩ := smallPrimeParts_card hε
  refine ⟨D^2,sq_pos_of_pos hD,?_⟩
  intro S v hv hS
  let A := (S.image Prod.fst).image (primarySmallPart v)
  let B := (S.image Prod.snd).image (primarySmallPart v)
  have ha : (A.card:ℝ) ≤ D*norm v^ε := by
    apply hbound (S.image Prod.fst) v hv
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨(hS p hp).1,(hS p hp).2.1⟩
  have hb : (B.card:ℝ) ≤ D*norm v^ε := by
    apply hbound (S.image Prod.snd) v hv
    intro b hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
    exact ⟨(hS p hp).2.2.1,(hS p hp).2.2.2⟩
  have hsub : S.image (pairSmallParts v) ⊆ A.product B := by
    intro p hp
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ (Finset.mem_image_of_mem Prod.fst hr),
        Finset.mem_image_of_mem _ (Finset.mem_image_of_mem Prod.snd hr)⟩
  calc
    _ ≤ ((A.product B).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = (A.card:ℝ)*(B.card:ℝ) := by rw [Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]
    _ ≤ (D*norm v^ε)*(D*norm v^ε) :=
      mul_le_mul ha hb (Nat.cast_nonneg _) (mul_nonneg hD.le (Real.rpow_nonneg (norm_nonneg v) _))
    _ = D^2*norm v^(2*ε) := by
      rw [show 2*ε = ε+ε by ring,Real.rpow_add (norm_pos_of_ne_zero hv)]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmallPairParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact two-variable conductor partitions and their arithmetic size. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angular_small_pair_fiber_smooth_moment (ℓ : ℤ) (v : Eisenstein) (s : Eisenstein × Eisenstein)
    (S : Finset (Eisenstein × Eisenstein))
    (hs : primary s.1 ∧ primary s.2)
    (hS : ∀ p ∈ S, primary p.1 ∧ primary p.2 ∧ pairSmallParts v p = s)
    {q : Eisenstein} (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) :
    (∑ p ∈ S, ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2) =
      ∑ r ∈ S.image (pairOutsideParts v),
        ‖primaryAngularSmallTwistSmoothSum ℓ r.1 r.2 ((3*(s.1*s.2))*q)
          (productResidueChar (primaryMixedResidueChar s.1 s.2 hs.1 hs.2) η) W Z t‖^2 := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    have hpa : primarySmallPart v p.1 = s.1 := congrArg Prod.fst (hS p hp).2.2
    have hpb : primarySmallPart v p.2 = s.2 := congrArg Prod.snd (hS p hp).2.2
    rw [primaryAngularSmallTwistSmoothSum_factor ℓ hs.1 (primaryOutsidePart_primary v (hS p hp).1)
      hs.2 (primaryOutsidePart_primary v (hS p hp).2.1)
      (by rw [← hpa,primary_small_outside_mul v (hS p hp).1])
      (by rw [← hpb,primary_small_outside_mul v (hS p hp).2.1])]
    rfl
  · intro p hp r hr he
    apply pairOutsideParts_fiber_injective v s S (fun p hp => ⟨(hS p hp).1,(hS p hp).2.1⟩)
      (Finset.mem_filter.mpr ⟨hp,(hS p hp).2.2⟩)
      (Finset.mem_filter.mpr ⟨hr,(hS r hr).2.2⟩) he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularBalancedSmallPartTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balanced full-factor estimates on the original, possibly ramified rows. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem balanced_angular_smalltwist_smooth_fiber_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (S : Finset (Eisenstein × Eisenstein)) (k : Eisenstein × Eisenstein)
        (v q : Eisenstein) (η : MulChar (Residues q) ℂ) (Y Z t : ℝ),
      Y₀ ≤ Y → v ≠ 0 → q ≠ 0 → (3:Eisenstein) ∣ v → q ∣ v →
      (AngularUnitCompatible q η ℓ) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      9*norm v^2*norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(17/50:ℝ) ∧
        norm p.2 ≤ Y^(17/50:ℝ) ∧ norm v < norm p.1 ∧ pairSmallParts v p = k) →
      (∑ p ∈ S, ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2) ≤ C*Y^(11/5:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := balanced_angular_smalltwist_pair_power hpub ℓ W hW hpos hsm hGI hGQ
  refine ⟨C,T,hC,hT,?_⟩
  intro S k v q η Y Z t hY hv hq h3 hqv hη hZY hYZ hsize ht hS
  by_cases hne : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hne
    have hk : primary k.1 ∧ primary k.2 := by
      rw [← (hS p₀ hp₀).2.2.2.2]
      exact ⟨primarySmallPart_primary v (hS p₀ hp₀).1.1,
        primarySmallPart_primary v (hS p₀ hp₀).1.2.1⟩
    let r := (3*(k.1*k.2))*q
    let η' := productResidueChar (primaryMixedResidueChar k.1 k.2 hk.1 hk.2) η
    have hr : r ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
      (mul_ne_zero (primary_ne_zero hk.1) (primary_ne_zero hk.2))) hq
    have hrN : norm r ≤ Y^(1/1000:ℝ) := by
      apply le_trans _ hsize
      dsimp [r]
      rw [← (hS p₀ hp₀).2.2.2.2]
      exact smallPartModulus_norm_le (hS p₀ hp₀).1.2.2.1 (hS p₀ hp₀).1.2.2.2.1 hv
    rw [angular_small_pair_fiber_smooth_moment ℓ v k S hk
      (fun p hp => ⟨(hS p hp).1.1,(hS p hp).1.2.1,(hS p hp).2.2.2.2⟩)]
    apply hbound (S.image (pairOutsideParts v)) r η' Y Z t hY hr
      (productResidueChar_angular_units _ _ (primaryMixedResidueChar_trivialInfinity hk.1 hk.2) hη)
      hZY hYZ hrN ht
    intro o ho
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ho
    have hsp := hS p hp
    have hpp := hsp.1
    refine ⟨primaryOutsidePart_primary v hpp.1,primaryOutsidePart_squarefree v hpp.1 hpp.2.2.1,
      primaryOutsidePart_primary v hpp.2.1,primaryOutsidePart_squarefree v hpp.2.1 hpp.2.2.2.1,
      (primaryOutsidePart_norm_le v hpp.1).trans hsp.2.1,
      (primaryOutsidePart_norm_le v hpp.2.1).trans hsp.2.2.1,
      outside_parts_coprime v hpp.1 hpp.2.1 hpp.2.2.2.2,?_,?_⟩
    · intro hu
      exact primaryOutsidePart_nonunit hpp.1 hpp.2.2.1 hv hsp.2.2.2.1
        (isUnit_of_mul_isUnit_left hu)
    · dsimp [r]
      rw [← hsp.2.2.2.2]
      exact outside_parts_coprime_local hpp.1 hpp.2.1 hpp.2.2.1 hpp.2.2.2.1 hv h3 hqv
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    exact mul_nonneg hC (Real.rpow_nonneg (by linarith [hT.trans hY]) _)

theorem balanced_angular_smalltwist_smooth_partition_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (S : Finset (Eisenstein × Eisenstein)) (v q : Eisenstein)
        (η : MulChar (Residues q) ℂ) (Y Z t : ℝ),
      Y₀ ≤ Y → v ≠ 0 → q ≠ 0 → (3:Eisenstein) ∣ v → q ∣ v →
      (AngularUnitCompatible q η ℓ) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      9*norm v^2*norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(17/50:ℝ) ∧
        norm p.2 ≤ Y^(17/50:ℝ) ∧ norm v < norm p.1) →
      (∑ p ∈ S, ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2) ≤ C*Y^(221/100:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := balanced_angular_smalltwist_smooth_fiber_power hpub ℓ W hW hpos hsm hGI hGQ
  obtain ⟨D,hD,hcard⟩ := pair_small_parts_card (show (0:ℝ) < 1 by norm_num)
  refine ⟨D*C,T,mul_nonneg hD.le hC,hT,?_⟩
  intro S v q η Y Z t hY hv hq h3 hqv hη hZY hYZ hsize ht hS
  have hY1 : 1 ≤ Y := hT.trans hY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hv1 := one_le_norm hv
  have hq1 := one_le_norm hq
  have hvY : norm v ≤ Y^(1/1000:ℝ) := by
    have hcoef : norm v ≤ 9*norm v^2*norm q := by
      calc
        _ ≤ norm v^2 := by nlinarith
        _ ≤ norm v^2*norm q := by nlinarith [sq_nonneg (norm v)]
        _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg (norm v)) (norm_nonneg q)]
    exact hcoef.trans hsize
  have hc := hcard S v hv (fun p hp => ⟨(hS p hp).1.1,(hS p hp).1.2.2.1,
    (hS p hp).1.2.1,(hS p hp).1.2.2.2.1⟩)
  norm_num only [mul_one] at hc
  have hp : norm v^(2:ℝ) ≤ Y^(1/500:ℝ) := by
    calc
      _ ≤ (Y^(1/1000:ℝ))^(2:ℝ) := Real.rpow_le_rpow (norm_nonneg v) hvY (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hY0.le]; norm_num
  have hf (k : Eisenstein × Eisenstein) (_hk : k ∈ S.image (pairSmallParts v)) :
      (∑ p ∈ S.filter (fun p => pairSmallParts v p = k),
        ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2) ≤ C*Y^(11/5:ℝ) := by
    apply hbound _ k v q η Y Z t hY hv hq h3 hqv hη hZY hYZ hsize ht
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact ⟨(hS p hm.1).1,(hS p hm.1).2.1,(hS p hm.1).2.2.1,(hS p hm.1).2.2.2,hm.2⟩
  calc
    _ = ∑ k ∈ S.image (pairSmallParts v), ∑ p ∈ S.filter (fun p => pairSmallParts v p = k),
        ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2 :=
      (Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem (pairSmallParts v) hp) _).symm
    _ ≤ ∑ _k ∈ S.image (pairSmallParts v), C*Y^(11/5:ℝ) := Finset.sum_le_sum hf
    _ = ((S.image (pairSmallParts v)).card:ℝ)*(C*Y^(11/5:ℝ)) := by simp
    _ ≤ (D*Y^(1/500:ℝ))*(C*Y^(11/5:ℝ)) :=
      mul_le_mul_of_nonneg_right (hc.trans (mul_le_mul_of_nonneg_left hp hD.le)) (by positivity)
    _ = (D*C)*Y^((1/500:ℝ)+11/5) := by rw [Real.rpow_add hY0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLogBalancedSmallParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic full factors after the exact small-prime row partition. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
 theorem balanced_angular_smalltwist_log_partition_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (P : Finset (Eisenstein × Eisenstein)) (v q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (Y Z t : ℝ), Y₀ ≤ Y → v ≠ 0 → q ≠ 0 →
      (3:Eisenstein) ∣ v → q ∣ v →
      AngularUnitCompatible q η ℓ →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      9*norm v^2*norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(17/50:ℝ) ∧
        norm a.2 ≤ Y^(17/50:ℝ) ∧ norm v < norm a.1) →
      (∑ a ∈ P, ‖primaryAngularSmallTwistLogSmoothSum ℓ a.1 a.2 q η W Z t‖^2) ≤ C*Y^(111/50:ℝ) := by
  obtain ⟨C₁,T₁,hC₁,hT₁,hbound₁⟩ := balanced_angular_smalltwist_smooth_partition_power hpub ℓ
    W hW hpos hsm hGI hGQ
  obtain ⟨C₂,T₂,hC₂,hT₂,hbound₂⟩ := balanced_angular_smalltwist_smooth_partition_power hpub ℓ
    (logSmoothWeight W) (logSmoothWeight_compact hW) (logSmoothWeight_positive hpos)
    (logSmoothWeight_smooth hpos hsm) hGI hGQ
  refine ⟨80802*C₁+2*C₂,max T₁ T₂,by positivity,hT₁.trans (le_max_left _ _),?_⟩
  intro P v q η Y Z t hY hv hq h3 hqv hη hZY hYZ hB ht hP
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans hY
  have hYT₂ : T₂ ≤ Y := (le_max_right _ _).trans hY
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hZ1 : 1 ≤ Z := (Real.one_le_rpow hY1 (by norm_num : (0:ℝ) ≤ 999/1000)).trans hYZ
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  have hb₁ := hbound₁ P v q η Y Z t hYT₁ hv hq h3 hqv hη hZY hYZ hB ht hP
  have hb₂ := hbound₂ P v q η Y Z t hYT₂ hv hq h3 hqv hη hZY hYZ hB ht hP
  have hlog : Real.log Z ≤ 201*Y^(1/200:ℝ) := by
    have hlogZ := Real.log_le_log hZ0 hZY
    rw [Real.log_rpow hY0] at hlogZ
    have hlogY := Real.log_le_rpow_div hY0.le (show (0:ℝ) < 1/200 by norm_num)
    have hpow : 0 ≤ Y^(1/200:ℝ) := Real.rpow_nonneg hY0.le _
    norm_num at hlogY
    nlinarith
  have hlog2 : (Real.log Z)^2 ≤ 40401*Y^(1/100:ℝ) := by
    have h := pow_le_pow_left₀ (Real.log_nonneg hZ1) hlog 2
    have hp : (Y^(1/200:ℝ))^2 = Y^(1/100:ℝ) := by
      rw [← Real.rpow_mul_natCast hY0.le]
      norm_num
    simpa only [mul_pow,hp,show (201:ℝ)^2 = 40401 by norm_num] using h
  have hrow (a : Eisenstein × Eisenstein) :
      ‖primaryAngularSmallTwistLogSmoothSum ℓ a.1 a.2 q η W Z t‖^2 ≤
        2*(Real.log Z)^2*‖primaryAngularSmallTwistSmoothSum ℓ a.1 a.2 q η W Z t‖^2+
        2*‖primaryAngularSmallTwistSmoothSum ℓ a.1 a.2 q η (logSmoothWeight W) Z t‖^2 := by
    exact primary_log_smooth_sq_le
      (fun x => mixedCubic a.1 a.2 x*η (Ideal.Quotient.mk (modulus q) x)*theta ℓ x*mellinPhase t (norm x)) W hW hZ0
  calc
    _ ≤ ∑ a ∈ P, (2*(Real.log Z)^2*‖primaryAngularSmallTwistSmoothSum ℓ a.1 a.2 q η W Z t‖^2+
        2*‖primaryAngularSmallTwistSmoothSum ℓ a.1 a.2 q η (logSmoothWeight W) Z t‖^2) :=
      Finset.sum_le_sum (fun a _ => hrow a)
    _ = 2*(Real.log Z)^2*(∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a.1 a.2 q η W Z t‖^2)+
        2*(∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a.1 a.2 q η (logSmoothWeight W) Z t‖^2) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ ≤ 2*(40401*Y^(1/100:ℝ))*(C₁*Y^(221/100:ℝ))+2*(C₂*Y^(221/100:ℝ)) := by
      apply add_le_add _ (mul_le_mul_of_nonneg_left hb₂ (by norm_num))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hlog2 (by norm_num)) hb₁
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
    _ ≤ (80802*C₁+2*C₂)*Y^(111/50:ℝ) := by
      have hp : Y^(1/100:ℝ)*Y^(221/100:ℝ) = Y^(111/50:ℝ) := by
        rw [← Real.rpow_add hY0]
        norm_num
      have hm : Y^(221/100:ℝ) ≤ Y^(111/50:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*C₂ by positivity)]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularBalancedFullSmoothFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual short-inverse full-factor bound for balanced rows. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
 theorem balanced_angular_short_full_smooth_partition_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (hWlow : ∀ x : ℝ, x < 1 → W x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (P : Finset (Eisenstein × Eisenstein)) (v q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (A : EisensteinArithmeticFunction) (F Y Z t : ℝ),
      Y₀ ≤ Y → ShortArithmeticFactor F A → F ≤ Y^(1001/1000:ℝ) →
      v ≠ 0 → q ≠ 0 → (3:Eisenstein) ∣ v → q ∣ v →
      (AngularUnitCompatible q η ℓ) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      9*norm v^2*norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(17/50:ℝ) ∧
        norm a.2 ≤ Y^(17/50:ℝ) ∧ norm v < norm a.1) →
      (∑ a ∈ P, ‖primaryAngularShortSmoothSum ℓ A a.1 a.2 q η W Z t‖^2) ≤ C*Y^(111/50:ℝ) := by
  obtain ⟨C₁,T₁,hC₁,hT₁,hbound₁⟩ := balanced_angular_smalltwist_smooth_partition_power hpub ℓ W hW hpos hsm hGI hGQ
  obtain ⟨C₂,T₂,hC₂,hT₂,hbound₂⟩ := balanced_angular_smalltwist_log_partition_power hpub ℓ W hW hpos hsm hGI hGQ
  refine ⟨max C₁ C₂,max 2 (max T₁ T₂),hC₁.trans (le_max_left _ _),by have := le_max_left (2:ℝ) (max T₁ T₂); linarith,?_⟩
  intro P v q η A F Y Z t hY hA hF hv hq h3 hqv hη hZY hYZ hsize ht hP
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := by linarith
  have hFZ := full_dyad_above_sqrt (show 1 < Y by linarith) hF hYZ
  rcases hA with rfl | rfl | rfl
  · calc
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        rw [primaryAngularShortSmoothSum_moebius ℓ hFZ a.1 a.2 q η W hWlow t,norm_zero]
        norm_num
      _ ≤ _ := mul_nonneg (hC₁.trans (le_max_left _ _)) (Real.rpow_nonneg (by linarith) _)
  · simp_rw [primaryAngularShortSmoothSum_zeta]
    apply (hbound₁ P v q η Y Z t
      ((le_max_left T₁ T₂).trans ((le_max_right _ _).trans hY))
      hv hq h3 hqv hη hZY hYZ hsize ht hP).trans
    exact mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
      (Real.rpow_nonneg (by linarith) _) (hC₁.trans (le_max_left _ _))
  · simp_rw [primaryAngularShortSmoothSum_log]
    exact (hbound₂ P v q η Y Z t
      ((le_max_right T₁ T₂).trans ((le_max_right _ _).trans hY))
      hv hq h3 hqv hη hZY hYZ hsize ht hP).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _))


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallPartSizes
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subpower local data satisfy the quantitative conductor margins. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventual_small_part_modulus_size :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y V Q : ℝ, Y₀ ≤ Y →
      0 ≤ V → 0 ≤ Q → V ≤ Y^(1/10000:ℝ) → Q ≤ Y^(1/10000:ℝ) →
      9*V^2*Q ≤ Y^(1/1000:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 7/10000 by norm_num)).eventually_ge_atTop (9:ℝ))
  refine ⟨max 2 T,le_max_left _ _,?_⟩
  intro Y V Q hY hV hQ hVY hQY
  have hY0 : 0 < Y := by have := (le_max_left (2:ℝ) T).trans hY; linarith
  have hscale : 9 ≤ Y^(7/10000:ℝ) := hT Y ((le_max_right _ _).trans hY)
  calc
    _ ≤ 9*(Y^(1/10000:ℝ))^2*Y^(1/10000:ℝ) := by gcongr
    _ = 9*Y^(3/10000:ℝ) := by
      rw [← Real.rpow_mul_natCast hY0.le,mul_assoc,← Real.rpow_add hY0]
      norm_num
    _ ≤ Y^(7/10000:ℝ)*Y^(3/10000:ℝ) :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hY0.le _)
    _ = _ := by rw [← Real.rpow_add hY0]; norm_num

lemma small_part_smaller_than_row {Y V A : ℝ} (hY : 1 < Y)
    (hV : V ≤ Y^(1/10000:ℝ)) (hA : Y^(1/1000:ℝ) ≤ A) : V < A :=
  hV.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num)).trans_le hA)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DominantSmoothSizes
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit eventual scale margins for the dominant smooth dyad. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventual_dominant_smooth_scales (C : ℝ) :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      2*Y ≤ Y^(1001/1000:ℝ) ∧ C*Y ≤ Y^(1001/1000:ℝ) ∧
      (∀ X : ℝ, Y^(9999/10000:ℝ) ≤ X → X ≤ C*Y →
        Y^(999/1000:ℝ) ≤ X/2 ∧ X/2 ≤ Y^(1001/1000:ℝ)) ∧
      (∀ Q : ℝ, Q ≤ Y^(1/100000:ℝ) → 9*Q ≤ Y^(1/10000:ℝ)) := by
  obtain ⟨T₁,h₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 1/1000 by norm_num)).eventually_ge_atTop (max 2 C))
  obtain ⟨T₂,h₂⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 9/10000 by norm_num)).eventually_ge_atTop (2:ℝ))
  obtain ⟨T₃,h₃⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 9/100000 by norm_num)).eventually_ge_atTop (9:ℝ))
  refine ⟨max 2 (max T₁ (max T₂ T₃)),le_max_left _ _,?_⟩
  intro Y hY
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 < Y := by linarith
  have hY₁ : T₁ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hY₂ : T₂ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hY₃ : T₃ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hp := h₁ Y hY₁
  have htwo := (le_max_left (2:ℝ) C).trans hp
  have hC := (le_max_right (2:ℝ) C).trans hp
  have hid : Y^(1/1000:ℝ)*Y = Y^(1001/1000:ℝ) := by
    conv_lhs => arg 2; rw [← Real.rpow_one Y]
    rw [← Real.rpow_add hY0]
    norm_num
  have hupper : C*Y ≤ Y^(1001/1000:ℝ) :=
    (mul_le_mul_of_nonneg_right hC hY0.le).trans_eq hid
  refine ⟨(mul_le_mul_of_nonneg_right htwo hY0.le).trans_eq hid,hupper,?_,?_⟩
  · intro X hlo hhi
    constructor
    · apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
      calc
        _ ≤ Y^(999/1000:ℝ)*Y^(9/10000:ℝ) :=
          mul_le_mul_of_nonneg_left (h₂ Y hY₂) (Real.rpow_nonneg hY0.le _)
        _ = Y^(9999/10000:ℝ) := by rw [← Real.rpow_add hY0]; norm_num
        _ ≤ X := hlo
    · have hX0 : 0 ≤ X := (Real.rpow_nonneg hY0.le _).trans hlo
      exact (div_le_self hX0 (by norm_num : (1:ℝ) ≤ 2)).trans (hhi.trans hupper)
  · intro Q hQ
    calc
      _ ≤ 9*Y^(1/100000:ℝ) := mul_le_mul_of_nonneg_left hQ (by norm_num)
      _ ≤ Y^(9/100000:ℝ)*Y^(1/100000:ℝ) :=
        mul_le_mul_of_nonneg_right (h₃ Y hY₃) (Real.rpow_nonneg hY0.le _)
      _ = _ := by rw [← Real.rpow_add hY0]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDominantNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-factor estimates retain room in the conductor exponent.
These are applications of the existing smooth Hecke moments to the actual rows. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem angular_dominant_balanced_full_factor_neighborhood (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (hWlow : ∀ x : ℝ, x < 1 → W x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (D : ℝ) :
    ∃ K Y₀ : ℝ, 0 ≤ K ∧ 2 ≤ Y₀ ∧
      ∀ (P : Finset (Eisenstein × Eisenstein)) (q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (A : EisensteinArithmeticFunction) (F Y X t : ℝ), Y₀ ≤ Y →
      ShortArithmeticFactor F A → F ≤ D*Y → q ≠ 0 →
      (AngularUnitCompatible q η ℓ) →
      norm q ≤ Y^(1/100000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      Y^(9999/10000:ℝ) ≤ X → X ≤ D*Y → (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(17/50:ℝ) ∧
        norm a.2 ≤ Y^(17/50:ℝ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryAngularShortSmoothSum ℓ A a.1 a.2 q η W (X/2) t‖^2) ≤ K*Y^(111/50:ℝ) := by
  classical
  obtain ⟨K,T₁,hK,hT₁,hbound⟩ := balanced_angular_short_full_smooth_partition_power hpub ℓ W hW hpos hsm hWlow hGI hGQ
  obtain ⟨T₂,hT₂,hscale⟩ := eventual_dominant_smooth_scales D
  obtain ⟨T₃,hT₃,hlocal⟩ := eventual_small_part_modulus_size
  refine ⟨K,max T₁ (max T₂ T₃),hK,hT₂.trans ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro P q η A F Y X t hY hA hF hq hη hqY ht hXlo hXhi hP
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans hY
  have hYT₂ : T₂ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₃ : T₃ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hY)
  have hY2 : 2 ≤ Y := hT₂.trans hYT₂
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hs := hscale Y hYT₂
  have hXs := hs.2.2.1 X hXlo hXhi
  have h3 : norm (3:Eisenstein) = 9 := by
    change Complex.normSq (3:ℂ) = 9
    norm_num [Complex.normSq]
  have hvq : norm (3*q) ≤ Y^(1/10000:ℝ) := by
    rw [norm_mul_eq,h3]
    exact hs.2.2.2 (norm q) hqY
  have hqsmall : norm q ≤ Y^(1/10000:ℝ) := hqY.trans
    (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
  have hsize := hlocal Y (norm (3*q)) (norm q) hYT₃
    (norm_nonneg _) (norm_nonneg _) hvq hqsmall
  apply hbound P (3*q) q η A F Y (X/2) t hYT₁ hA (hF.trans hs.2.1)
    (mul_ne_zero (by norm_num) hq) hq (dvd_mul_right _ _) (dvd_mul_left _ _) hη
    hXs.2 hXs.1 hsize ht
  intro a ha
  have hp := hP a ha
  refine ⟨hp.1,?_,?_,?_⟩
  · exact hp.2.1
  · exact hp.2.2.1
  · exact small_part_smaller_than_row (by linarith) hvq hp.2.2.2

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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmoothShortFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmoothShortMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem angular_dominant_smooth_mixed_moment_reduction (ℓ : ℤ) {C δ ε : ℝ}
    (hC : 0 < C) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
      (P : Finset (Eisenstein × Eisenstein)) (i : ι),
      (∀ k, ShortArithmeticFactor F (A k)) → (∀ k, 1 ≤ X k) →
      (∀ k, q k ≠ 0) → (∀ k x, ‖W k x‖ ≤ 1) → (∀ k x, 2 < x → W k x = 0) →
      1 ≤ Y → (∀ p ∈ P, primary p.1 ∧ primary p.2) → (∏ k, X k) ≤ C*Y → Y^(1-δ) ≤ X i →
      (∑ p ∈ P, ‖∏ k, primaryAngularShortSmoothSum ℓ (A k) p.1 p.2 (q k) (η k) (W k) (X k/2) (t k)‖^2) ≤
        (M*Y^(δ+ε))^2*(∑ p ∈ P, ‖primaryAngularShortSmoothSum ℓ (A i) p.1 p.2 (q i) (η i) (W i) (X i/2) (t i)‖^2) := by
  obtain ⟨M,hM,hbound⟩ := dominant_mixed_moment_reduction (ι := ι) hC hδ hε
  refine ⟨M,hM,?_⟩
  intro F Y X A q η W t P i hA hX hq hW hcut hY hP htotal hlong
  let K := angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW
  have h := hbound K 0 Y i P hY hP htotal hlong
  simpa only [K,angularShortFamily_mixedValue ℓ F X A q η W t hA hX hq hW hcut] using h

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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmoothShortNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem angular_all_short_smooth_mixed_neighborhood (ℓ : ℤ) (hHuxley : HuxleyAdditiveLargeSieve)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/3 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (F Y : ℝ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
        (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
        (W : ι → ℝ → ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
      (∀ i, X i ≤ Y^(1-δ)) → Y/C ≤ ∏ i, X i → (∏ i, X i) ≤ C*Y →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3+κ) ∧ norm p.2 ≤ Y^(1/3+κ)) →
      (∑ p ∈ P, ‖∏ i, primaryAngularShortSmoothSum ℓ (A i) p.1 p.2 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := all_short_mixed_neighborhood (ι := ι) hHuxley hδ hC
  refine ⟨κ,hκ,hκhi,ε,hε,T,?_⟩
  intro F Y X A q η W t P hY hA hX hq hW hcut hshort hlo hhi hP
  let K := angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW
  have h := hbound K 0 Y P hY hshort hlo hhi hP
  simpa only [K,angularShortFamily_mixedValue ℓ F X A q η W t hA hX hq hW hcut] using h


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularBalancedSmoothNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem angular_balanced_smooth_product_neighborhood_oai (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (W : ι → ℝ → ℂ) (hW : ∀ i, HasCompactSupport (W i))
    (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0) (hsm : ∀ i, ContDiff ℝ ∞ (W i))
    (hWlow : ∀ i x, x < 1 → W i x = 0) (hWup : ∀ i x, 2 < x → W i x = 0)
    (hWnorm : ∀ i x, ‖W i x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(37/100:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖∏ i, primaryAngularShortSmoothSum ℓ (A i) a.1 a.2 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,_,ε,hε,T₀,hshort⟩ := angular_all_short_smooth_mixed_neighborhood (ι := ι) ℓ hHuxley
    (show (0:ℝ) < 1/10000 by norm_num) hD
  obtain ⟨M,hM,hred⟩ := angular_dominant_smooth_mixed_moment_reduction (ι := ι) ℓ hD
    (show (0:ℝ) ≤ 1/10000 by norm_num) (show (0:ℝ) < 1/10000 by norm_num)
  choose K T hK hT hfull using fun i => angular_dominant_balanced_full_factor_neighborhood hpub ℓ
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

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.angular_balanced_smooth_product_neighborhood_oai.{u_1} := @OAI.CubicFirstMoment.angular_balanced_smooth_product_neighborhood_oai.{u_1}
