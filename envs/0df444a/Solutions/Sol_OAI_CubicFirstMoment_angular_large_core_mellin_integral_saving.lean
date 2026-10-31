-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_large_core_mellin_integral_saving
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:08:57.305563+00:00
-- url     : https://prove2.me/submissions/79fd7b56-4d53-48a6-a3b2-20ed34a3f539

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A020
import Definitions.Def_OAIQ096A023
import Theorems.Thm_OAI_CubicFirstMoment_angular_exceptional_residual_moment
import Theorems.Thm_OAI_CubicFirstMoment_dilated_noncube_three_sieve_bounds

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cube_decomposition (n : Eisenstein) :
    ∃ s t c : Eisenstein, Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧ n = s*t^2*c^3 := by
  refine UniqueFactorizationMonoid.induction_on_prime n ?_ ?_ ?_
  · exact ⟨1,1,0,squarefree_one,squarefree_one,isCoprime_one_left,by simp⟩
  · intro u hu
    exact ⟨u,1,1,hu.squarefree,squarefree_one,isCoprime_one_right,by simp⟩
  · intro b p hb hp ih
    obtain ⟨s,t,c,hss,hst,hcop,rfl⟩ := ih
    by_cases hps : p ∣ s
    · obtain ⟨s',rfl⟩ := hps
      have hps' : IsCoprime p s' := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hss).1
      have hpt : IsCoprime p t := hcop.of_mul_left_left
      refine ⟨s',p*t,c,hss.of_mul_right,
        squarefree_mul_iff.mpr ⟨hpt.isRelPrime,hp.squarefree,hst⟩,
        hps'.symm.mul_right hcop.of_mul_left_right,?_⟩
      ring
    · by_cases hpt : p ∣ t
      · obtain ⟨t',rfl⟩ := hpt
        refine ⟨s,t',p*c,hss,hst.of_mul_right,hcop.of_mul_right_right,?_⟩
        ring
      · have hps' := hp.coprime_iff_not_dvd.mpr hps
        have hpt' := hp.coprime_iff_not_dvd.mpr hpt
        refine ⟨p*s,t,c,squarefree_mul_iff.mpr ⟨hps'.isRelPrime,hp.squarefree,hss⟩,
          hst,hpt'.mul_left hcop,?_⟩
        ring

theorem squarefree_ramified_split (n : Eisenstein) (hs : Squarefree n) :
    ∃ d e : Eisenstein, d ∣ 3 ∧ IsCoprime e 3 ∧ n = d*e := by
  have h : ∀ n : Eisenstein, Squarefree n →
      ∃ d e : Eisenstein, d ∣ 3 ∧ IsCoprime e 3 ∧ n = d*e := by
    intro n
    refine UniqueFactorizationMonoid.induction_on_prime n ?_ ?_ ?_
    · intro hs
      have hh := hs 0 (by simp)
      exact (not_isUnit_zero hh).elim
    · intro u hu hs
      refine ⟨1,u,one_dvd _,?_,by simp⟩
      exact (isCoprime_zero_right.mpr hu).of_isCoprime_of_dvd_right (dvd_zero 3)
    · intro b p hb hp ih hs
      obtain ⟨d,e,hd,he,hbe⟩ := ih hs.of_mul_right
      have hpb : IsCoprime p b := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
      by_cases hp3 : p ∣ 3
      · have hpd : IsCoprime p d := (hbe ▸ hpb).of_mul_right_left
        refine ⟨p*d,e,hpd.mul_dvd hp3 hd,he,?_⟩
        rw [hbe]; ring
      · refine ⟨d,p*e,hd,(hp.coprime_iff_not_dvd.mpr hp3).mul_left he,?_⟩
        rw [hbe]; ring
  exact h n hs

lemma unit_residue_of_isCoprime_three {e : Eisenstein} (he : IsCoprime e 3) :
    IsUnit (Ideal.Quotient.mk (modulus 3) e) := by
  have h := he.map (Ideal.Quotient.mk (modulus 3))
  simpa only [residue_three_eq_zero, isCoprime_zero_right] using h

lemma norm_le_of_dvd {a b : Eisenstein} (hb : b ≠ 0) (hd : a ∣ b) :
    norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := hd
  have hc : c ≠ 0 := by intro h; simp [h] at hb
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg a) (one_le_norm hc)

theorem squarefree_primary_residual (n : Eisenstein) (hs : Squarefree n) :
    ∃ r s : Eisenstein, r ≠ 0 ∧ norm r ≤ 9 ∧ primary s ∧ Squarefree s ∧ n = r*s := by
  obtain ⟨d,e,hd,he,hde⟩ := squarefree_ramified_split n hs
  obtain ⟨u,hu,hprim⟩ := unit_lift_mod_three (unit_residue_of_isCoprime_three he)
  obtain ⟨v,rfl⟩ := hu
  have hd0 : d ≠ 0 := by
    intro hd0
    rw [hd0, zero_dvd_iff] at hd
    norm_num at hd
  have hvi : norm (↑v⁻¹ : Eisenstein) = 1 := by
    rw [← normNat_cast, normNat_of_isUnit (Units.isUnit _), Nat.cast_one]
  refine ⟨d*(↑v⁻¹ : Eisenstein),e*(↑v : Eisenstein),mul_ne_zero hd0 (Units.ne_zero _),?_,hprim,?_,?_⟩
  · rw [norm_mul_eq, hvi, mul_one]
    have h := norm_le_of_dvd (by norm_num : (3 : Eisenstein) ≠ 0) hd
    have h3 : norm (3 : Eisenstein) = 9 := by
      change Complex.normSq (3 : ℂ) = 9
      norm_num
    simpa only [h3] using h
  · have hes : Squarefree e := (hde ▸ hs).of_mul_right
    exact squarefree_mul_iff.mpr ⟨((isCoprime_zero_left.mpr (Units.isUnit v)).of_isCoprime_of_dvd_left (dvd_zero e)).isRelPrime,hes,
      (Units.isUnit v).squarefree⟩
  · rw [hde]
    simp [mul_assoc, mul_left_comm, mul_comm]

end CubicFirstMoment

namespace CubicFirstMoment

theorem full_cube_decomposition {n : Eisenstein} (hn : n ≠ 0) :
    ∃ r s t c : Eisenstein, r ≠ 0 ∧ norm r ≤ 729 ∧
      primary s ∧ primary t ∧ Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧
      c ≠ 0 ∧ n = r*s*t^2*c^3 := by
  obtain ⟨s₀,t₀,c,hs₀,ht₀,hst,hn'⟩ := cube_decomposition n
  obtain ⟨r,s,hr0,hr,hs,hss,hs'⟩ := squarefree_primary_residual s₀ hs₀
  obtain ⟨q,t,hq0,hq,ht,hst',ht'⟩ := squarefree_primary_residual t₀ ht₀
  have hc0 : c ≠ 0 := by intro hc; simp [hc] at hn'; exact hn hn'
  have hcop : IsCoprime s t :=
    hst.of_isCoprime_of_dvd_left (hs' ▸ dvd_mul_left s r) |>.of_isCoprime_of_dvd_right
      (ht' ▸ dvd_mul_left t q)
  refine ⟨r*q^2,s,t,c,mul_ne_zero hr0 (pow_ne_zero _ hq0),?_,hs,ht,hss,hst',hcop,hc0,?_⟩
  · rw [norm_mul_eq]
    have he : norm (q^2) = norm q ^ 2 := by simp [pow_two]
    rw [he]
    have hq2 : norm q ^ 2 ≤ 81 := by nlinarith [norm_nonneg q]
    nlinarith [norm_nonneg r, sq_nonneg (norm q)]
  · rw [hn',hs',ht']; ring

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_primary (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    ∀ i, ∀ p ∈ coordinatePrimeSupport W X Y i, primaryPrime p := by
  intro i p hp
  exact ⟨coordinateSupport_primary W X Y i p (Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2⟩

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

lemma coordinate_le_product (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i) (i : ι) :
    X i ≤ ∏ j, X j := by
  rw [← Finset.mul_prod_erase _ X (Finset.mem_univ i)]
  exact le_mul_of_one_le_right (by linarith [hX i]) (Finset.one_le_prod (fun j _ => hX j))

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_prime (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    ∀ i, ∀ z ∈ fullPrimeSupport R W X i, primaryPrime z := by
  intro i z hz
  exact ⟨(mem_primaryElementBall.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1,
    (Finset.mem_filter.mp hz).2⟩

lemma fullPrimeSupport_eq_product_cutoff {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i)
    (hhi : ∀ i x, R < x → W i x = 0) :
    fullPrimeSupport R W X = coordinatePrimeSupport W X (R/2*(∏ i, X i)) := by
  apply fullPrimeSupport_eq_coordinate W X (fun i => zero_lt_one.trans_le (hX i)) hhi
  intro i
  have h := mul_le_mul_of_nonneg_left (coordinate_le_product X hX i) hR
  nlinarith

lemma fullStructuredAngularSum_eq (R : ℝ) (h v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    fullStructuredAngularSum R h v e ℓ u W X =
      ∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R W X),
        fullStructuredCoefficient R h v e W X z*theta ℓ z*mellinPhase u (norm z) := by
  unfold fullStructuredAngularSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  unfold fullStructuredCoefficient
  split_ifs <;> simp only [zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularFullPrimeConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

lemma fullStructuredAngularPrimeSum_eq {R Z : ℝ} (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hhi : ∀ i x, R < x → W i x = 0) (hZ : ∀ i, R*X i ≤ 2*Z) :
    fullStructuredAngularPrimeSum ℓ R a b v e u W X = structuredAngularPrimeSum ℓ a b v e u W X Z := by
  unfold fullStructuredAngularPrimeSum fullPrimeCoefficient structuredAngularPrimeSum primeMomentCoefficient
  rw [fullPrimeSupport_eq_coordinate W X hX hhi hZ]

lemma fullStructuredAngularPrimeSum_eq_existing (R : ℝ) (h v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    fullStructuredAngularPrimeSum ℓ R h 1 v e u W X =
      fullStructuredAngularSum R h v e ℓ u W X := by
  unfold fullStructuredAngularPrimeSum fullStructuredAngularSum
  apply Finset.sum_congr rfl
  intro z _
  simp only [one_pow,mul_one]
  ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStructuredFrequencyPolynomial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact angular frequency coefficients; their energy is unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma structuredAngularPrimeSum_eq_frequency (ℓ : ℤ) (h v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) :
    structuredAngularPrimeSum ℓ h 1 v e u W X Z =
      ∑ z ∈ structuredFrequencySupport W X Z,
        structuredAngularFrequencyCoefficient ℓ v e u W X Z z*cubicSymbol z h := by
  unfold structuredAngularPrimeSum structuredFrequencySupport
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have hp := orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
    (fun i p h => (coordinatePrimeSupport_primary W X Z i p h).1) hz
  by_cases hsf : Squarefree z
  · rw [ite_eq_left hsf]
    by_cases hc : IsCoprime z e
    · simp only [ite_eq_left hc,structuredAngularFrequencyCoefficient,
        structuredFrequencyCoefficient,one_pow,mul_one,cubicSymbol_mul_upper hp]
      ring
    · simp only [ite_eq_right hc,structuredAngularFrequencyCoefficient,
        structuredFrequencyCoefficient,mul_zero,zero_mul]
  · have he : primeMomentCoefficient W X Z z = 0 := by
      simp only [primeMomentCoefficient,squarefreeConvolution,ite_eq_right hsf]
    simp only [he,zero_mul,ite_eq_right hsf,ite_self]

lemma structuredAngularFrequencyCoefficient_energy_le (ℓ : ℤ) (v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) :
    (∑ z ∈ structuredFrequencySupport W X Z,
      ‖structuredAngularFrequencyCoefficient ℓ v e u W X Z z‖^2) ≤
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
        ‖primeMomentCoefficient W X Z z‖^2 := by
  have he : (∑ z ∈ structuredFrequencySupport W X Z,
      ‖structuredAngularFrequencyCoefficient ℓ v e u W X Z z‖^2) =
      ∑ z ∈ structuredFrequencySupport W X Z,
        ‖structuredFrequencyCoefficient v e u W X Z z‖^2 := by
    apply Finset.sum_congr rfl
    intro z hz
    have hp := orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
      (fun i p h => (coordinatePrimeSupport_primary W X Z i p h).1) (Finset.mem_filter.mp hz).1
    rw [structuredAngularFrequencyCoefficient,norm_mul,norm_theta (primary_ne_zero hp) ℓ,one_mul]
  rw [he]
  exact structuredFrequencyCoefficient_energy_le v e u W X Z

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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularFullNoncubeMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_full_logarithmic_noncube (hHuxley : HuxleyAdditiveLargeSieve)
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
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
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
  let β := structuredAngularFrequencyCoefficient ℓ v e u (W r) X Z
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hXp : ∀ i, 0 < X i := fun i => zero_lt_one.trans_le (hX i)
  have hA : ∀ a ∈ A, primary a ∧ Squarefree a ∧ norm a ≤ R^(Fintype.card ι)*L r := by
    intro a ha
    simpa only [hprod] using structuredFrequencySupport_bounds (W r) X hXp
      (show 0 ≤ R by linarith) (hlo r) (hhi r) Z a ha
  have hE : (∑ a ∈ A, ‖β a‖^2) ≤ (L r)^(1+ν/2) :=
    (structuredAngularFrequencyCoefficient_energy_le ℓ v e u (W r) X Z).trans
      (henergy r X Z (hL r) hT₀ hXp hprod)
  have hm := hraw (L r) p q (hL r) hp hq hsize hlarge hfirst hbalanced
    A Ram S T J H hA hS hT hH β
  have hfull (h : Eisenstein) : fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X =
      structuredAngularPrimeSum ℓ h 1 v e u (W r) X Z := by
    apply fullStructuredAngularPrimeSum_eq ℓ h 1 v e u (W r) X hXp (hhi r)
    intro i
    have hi : X i ≤ L r := by simpa only [hprod] using coordinate_le_product X hX i
    dsimp [Z]
    nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ R by linarith)]
  have heq : (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) =
      ∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2 := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [hfull h,structuredAngularPrimeSum_eq_frequency ℓ]
  rw [heq]
  simpa only [neg_div] using noncube_energy_absorption hC.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hLp (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hLp.le _) (sq_nonneg _)) _)
    hE hm

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicNoncubeMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDyadicNoncubeMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_dyadic_full_noncube (hHuxley : HuxleyAdditiveLargeSieve)
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
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨η,C,ν,hη,hηhi,hC,hν,hraw⟩ := angular_full_logarithmic_noncube ℓ (γ := γ) (ι := ι)
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularFullOrdinaryMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_full_ordinary_moment (hHuxley : HuxleyAdditiveLargeSieve)
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
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(U*V)^ε*((U*V)^2+L r)*L r*(1+Real.log (L r))^a := by
  obtain ⟨C₀,a,hC₀,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  obtain ⟨C₁,C₂,_,hC₂,hsieve⟩ := dilated_noncube_three_sieve_bounds hHuxley
    (one_le_pow₀ hR : 1 ≤ R^(Fintype.card ι)) hε
  refine ⟨C₂*(C₀+1),a,mul_pos hC₂ (by linarith),?_⟩
  intro r X U V v e u Ram S T J H hL hX hprod hU hV hS hT hH
  let Z := R/2*L r
  let B := structuredFrequencySupport (W r) X Z
  let β := structuredAngularFrequencyCoefficient ℓ v e u (W r) X Z
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
    apply (structuredAngularFrequencyCoefficient_energy_le ℓ v e u (W r) X Z).trans
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
  have hfull (h : Eisenstein) : fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X =
      structuredAngularPrimeSum ℓ h 1 v e u (W r) X Z := by
    apply fullStructuredAngularPrimeSum_eq ℓ h 1 v e u (W r) X hXp (hhi r)
    intro i
    have hi : X i ≤ L r := by simpa only [hprod] using coordinate_le_product X hX i
    dsimp [Z]
    nlinarith [mul_le_mul_of_nonneg_left hi (zero_le_one.trans hR)]
  have hsum : (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) =
      ∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2 := by
    apply Finset.sum_congr rfl
    intro h _
    rw [hfull,structuredAngularPrimeSum_eq_frequency ℓ]
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLargeConductorMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_large_conductor_structured_moment (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R κ : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R) (hκ : 0 < κ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
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
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨σ,νE,hσ,hνE,hE⟩ := angular_exceptional_residual_moment ℓ (γ := γ) (ι := ι)
    hpub hHuxley hperiod hc hc₁ hR hGI hGQ
  let δ := σ/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ηN,CN,νN,hηN,hηNhi,hCN,hνN,hN⟩ := angular_dyadic_full_noncube ℓ (γ := γ) (ι := ι)
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
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤ C*A*(L r)^(-ν) := by
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
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularRealScaleLargeMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_large_conductor_real_scales (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R κ : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R) (hκ : 0 < κ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
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
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*(U*V^2)^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨η,σ,C,ν,hη,hη₁,hσ,hC,hν,hbound⟩ :=
    angular_large_conductor_structured_moment ℓ (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hκ hGI hGQ
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicCoreCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coverage of a noncube frequency by either the low-core set or
a ramified/squarefree pair of large conductor. No decomposition is assumed. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_cube (j : Eisenstein) : norm (j^3) = norm j^3 := by
  simp only [pow_succ,norm_mul_eq,pow_zero,norm_one_eq]

lemma cube_part_norm_bound {h v j : Eisenstein} {H : ℝ}
    (hv : v ≠ 0) (heq : h = v*j^3) (hh : norm h ≤ H) :
    norm j ≤ H^(1/3:ℝ) := by
  have hcube : norm j^3 ≤ H := by
    calc
      _ ≤ norm v*norm j^3 := le_mul_of_one_le_left (pow_nonneg (norm_nonneg j) _) (one_le_norm hv)
      _ = norm h := by rw [heq,norm_mul_eq,norm_cube]
      _ ≤ H := hh
  have hp := Real.rpow_le_rpow (pow_nonneg (norm_nonneg j) 3) hcube (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (norm j^3)^(1/3:ℝ) = norm j := by
    rw [← Real.rpow_natCast (norm j) 3,← Real.rpow_mul (norm_nonneg j)]
    norm_num
  rwa [he] at hp

lemma mem_lowNoncubeSupport_of_core {h v j : Eisenstein} {V H : ℝ}
    (hv : v ≠ 0) (hj : j ≠ 0) (heq : h = v*j^3) (hh : norm h ≤ H)
    (hsmall : norm v ≤ V) (hn : ¬∃ a : Eisenstein, a^3 = h) :
    h ∈ lowNoncubeSupport V (H^(1/3:ℝ)) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(v,j),?_,heq.symm⟩,hn⟩
  exact Finset.mem_product.mpr ⟨mem_nonzeroNormBall.mpr ⟨hsmall,hv⟩,
    mem_nonzeroNormBall.mpr ⟨cube_part_norm_bound hv heq hh,hj⟩⟩

theorem noncube_large_core_decomposition {h : Eisenstein} {V H : ℝ}
    (hh0 : h ≠ 0) (hh : norm h ≤ H) (hn : ¬∃ a : Eisenstein, a^3 = h)
    (hnot : h ∉ lowNoncubeSupport V (H^(1/3:ℝ))) :
    ∃ r s t j : Eisenstein, r ≠ 0 ∧ norm r ≤ 729 ∧
      primary s ∧ primary t ∧ Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧
      j ≠ 0 ∧ h = r*s*t^2*j^3 ∧
      V/729 < norm s*norm t^2 ∧ norm s*norm t^2 ≤ H ∧ norm j ≤ H^(1/3:ℝ) := by
  obtain ⟨r,s,t,j,hr,hrN,hs,ht,hss,hst,hcop,hj,heq⟩ := full_cube_decomposition hh0
  have hv : r*s*t^2 ≠ 0 := mul_ne_zero (mul_ne_zero hr (primary_ne_zero hs))
    (pow_ne_zero _ (primary_ne_zero ht))
  have hcore : h = (r*s*t^2)*j^3 := heq
  have hlarge : V < norm (r*s*t^2) := lt_of_not_ge (fun hsmall => hnot
    (mem_lowNoncubeSupport_of_core hv hj hcore hh hsmall hn))
  have hc : norm (r*s*t^2) = norm r*(norm s*norm t^2) := by
    rw [norm_mul_eq,norm_mul_eq]
    have ht2 : norm (t^2) = norm t^2 := by simp only [pow_two,norm_mul_eq]
    rw [ht2]
    ring
  have hD0 : 0 ≤ norm s*norm t^2 := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hsmall : norm (r*s*t^2) ≤ norm h := by
    calc
      _ ≤ norm (r*s*t^2)*norm (j^3) :=
        le_mul_of_one_le_right (norm_nonneg _) (one_le_norm (pow_ne_zero _ hj))
      _ = norm h := by simp only [hcore,norm_mul_eq]
  refine ⟨r,s,t,j,hr,hrN,hs,ht,hss,hst,hcop,hj,heq,?_,?_,cube_part_norm_bound hv hcore hh⟩
  · apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 729)).mpr
    rw [hc] at hlarge
    nlinarith [mul_le_mul_of_nonneg_right hrN hD0]
  · apply le_trans _ (hsmall.trans hh)
    rw [hc]
    exact le_mul_of_one_le_left hD0 (one_le_norm hr)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicDyadicCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma real_cube_scale_bound {x B D : ℝ} (hx : 0 ≤ x) (hD : 0 < D)
    (h : x^3*D ≤ B) : x ≤ (B/D)^(1/3:ℝ) := by
  have hc : x^3 ≤ B/D := (le_div_iff₀ hD).mpr h
  have hp := Real.rpow_le_rpow (pow_nonneg hx 3) hc (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (x^3)^(1/3:ℝ) = x := by
    rw [← Real.rpow_natCast x 3,← Real.rpow_mul hx]
    norm_num
  rwa [he] at hp

theorem noncube_mem_coreDyadicBlock {h : Eisenstein} {V B : ℝ}
    (hh0 : h ≠ 0) (hh : norm h ≤ B) (hn : ¬∃ a : Eisenstein, a^3 = h)
    (hnot : h ∉ lowNoncubeSupport V (B^(1/3:ℝ))) :
    ∃ z ∈ largeCoreDyadicIndices V B, h ∈ coreDyadicBlock B z.1 z.2 := by
  obtain ⟨r,s,t,c,hr,hrN,hs,ht,hss,hst,hcop,hc,heq,hlarge,hcore,hcN⟩ :=
    noncube_large_core_decomposition hh0 hh hn hnot
  let i := Nat.log 2 (normNat s)
  let j := Nat.log 2 (normNat t)
  have hsD : s ∈ squarefreePrimaryDyad i := mem_squarefreePrimaryDyad.mpr
    ⟨mem_frequencyDyad.mpr ⟨primary_ne_zero hs,rfl⟩,hs,hss⟩
  have htD : t ∈ squarefreePrimaryDyad j := mem_squarefreePrimaryDyad.mpr
    ⟨mem_frequencyDyad.mpr ⟨primary_ne_zero ht,rfl⟩,ht,hst⟩
  have hsG := squarefreePrimaryDyad_gramDyad hsD
  have htG := squarefreePrimaryDyad_gramDyad htD
  have hDlo : coreDyadicConductor i j ≤ norm s*norm t^2 := by
    exact mul_le_mul hsG.2.2.1 (pow_le_pow_left₀ (by positivity) htG.2.2.1 2)
      (by positivity) (norm_nonneg s)
  have hDhi : norm s*norm t^2 < 8*coreDyadicConductor i j := by
    have ht2 : norm t^2 < (2*(2:ℝ)^j)^2 :=
      (pow_lt_pow_left₀ htG.2.2.2 (norm_nonneg t) (by norm_num : (2:ℕ) ≠ 0))
    calc
      _ < (2*(2:ℝ)^i)*((2*(2:ℝ)^j)^2) := mul_lt_mul hsG.2.2.2 ht2.le
        (sq_pos_of_pos (zero_lt_one.trans_le (one_le_norm (primary_ne_zero ht)))) (by positivity)
      _ = _ := by unfold coreDyadicConductor; ring
  have hDb : coreDyadicConductor i j ≤ B := hDlo.trans hcore
  have hidx : ∀ (a : Eisenstein), primary a → norm a ≤ B →
      Nat.log 2 (normNat a) < Nat.log 2 ⌊B⌋₊+1 := by
    intro a ha haB
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    apply Nat.le_floor
    rwa [normNat_cast]
  have hsB : norm s ≤ B := (le_mul_of_one_le_right (norm_nonneg s)
    (one_le_pow₀ (one_le_norm (primary_ne_zero ht)))).trans hcore
  have htB : norm t ≤ B := by
    have htt : norm t ≤ norm t^2 := by
      nlinarith [one_le_norm (primary_ne_zero ht)]
    exact htt.trans ((le_mul_of_one_le_left (sq_nonneg _) (one_le_norm (primary_ne_zero hs))).trans hcore)
  have hcube : norm c^3*coreDyadicConductor i j ≤ B := by
    have hn : norm h = norm r*(norm s*norm t^2)*norm c^3 := by
      simp only [heq,norm_mul_eq,norm_cube,pow_two]
      ring
    calc
      _ ≤ norm c^3*(norm s*norm t^2) := mul_le_mul_of_nonneg_left hDlo (pow_nonneg (norm_nonneg c) _)
      _ ≤ norm r*(norm s*norm t^2)*norm c^3 := by
        nlinarith [mul_le_mul_of_nonneg_right
          (one_le_norm hr) (mul_nonneg (mul_nonneg (norm_nonneg s) (sq_nonneg (norm t)))
            (pow_nonneg (norm_nonneg c) 3))]
      _ = norm h := hn.symm
      _ ≤ B := hh
  refine ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (hidx s hs hsB),Finset.mem_range.mpr (hidx t ht htB)⟩,
    ⟨by dsimp only; linarith,hDb⟩⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨((r,c),(s,t)),Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨mem_nonzeroNormBall.mpr ⟨hrN,hr⟩,mem_nonzeroNormBall.mpr
      ⟨real_cube_scale_bound (norm_nonneg c) (coreDyadicConductor_pos i j) hcube,hc⟩⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsD,htD⟩,hcop⟩⟩,heq.symm⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicFrequencyMassSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem noncube_frequency_mass_split (H : Finset Eisenstein) {V B : ℝ}
    (hH : ∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h)
    (f : Eisenstein → ℝ) (hf : ∀ h, 0 ≤ f h) :
    (∑ h ∈ H, f h) ≤
      (∑ h ∈ H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))), f h)+
      ∑ z ∈ largeCoreDyadicIndices V B, ∑ h ∈ coreDyadicBlock B z.1 z.2, f h := by
  let I := (largeCoreDyadicIndices V B).sigma (fun z => coreDyadicBlock B z.1 z.2)
  let F : Sigma (fun _ : ℕ × ℕ => Eisenstein) → Eisenstein := Sigma.snd
  have hcover : H.filter (fun h => h ∉ lowNoncubeSupport V (B^(1/3:ℝ))) ⊆ I.image F := by
    intro h hh
    obtain ⟨hm,hn⟩ := Finset.mem_filter.mp hh
    obtain ⟨z,hz,hb⟩ := noncube_mem_coreDyadicBlock (hH h hm).1
      (hH h hm).2.1 (hH h hm).2.2 hn
    exact Finset.mem_image.mpr ⟨⟨z,h⟩,Finset.mem_sigma.mpr ⟨hz,hb⟩,rfl⟩
  have hsum : (∑ h ∈ H.filter (fun h => h ∉ lowNoncubeSupport V (B^(1/3:ℝ))), f h) ≤
      ∑ z ∈ largeCoreDyadicIndices V B, ∑ h ∈ coreDyadicBlock B z.1 z.2, f h := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun h _ _ => hf h)).trans
    apply (Finset.sum_image_le_of_nonneg (s := I) (g := F) (f := f) (fun h _ => hf h)).trans_eq
    exact Finset.sum_sigma _ _ _
  rw [← Finset.sum_filter_add_sum_filter_not H
    (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))) f]
  exact add_le_add le_rfl hsum

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

lemma largeCoreDyadicIndices_card (V B : ℝ) :
    (largeCoreDyadicIndices V B).card ≤ (Nat.log 2 ⌊B⌋₊+1)^2 := by
  unfold largeCoreDyadicIndices
  apply (Finset.card_filter_le _ _).trans
  exact le_of_eq ((Finset.card_product _ _).trans (by simp only [Finset.card_range,pow_two]))

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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLargeCoreBlockMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_large_core_block_moment (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R κ : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R) (hκ : 0 < κ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
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
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨η,σ,C,ν,hη,hη₁,hσ,hC,hν,hbound⟩ :=
    angular_large_conductor_real_scales ℓ (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hκ hGI hGQ
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmallConductorLogSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_small_conductor_log_saving (hHuxley : HuxleyAdditiveLargeSieve)
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
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*(U*V^2)^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,a,hC,hbound⟩ := angular_full_ordinary_moment ℓ hHuxley hW hR
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmallCoreBlockMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_small_core_block_log_saving (hHuxley : HuxleyAdditiveLargeSieve)
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
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,A,hC,hbound⟩ := angular_small_conductor_log_saving ℓ hHuxley hW hR hlo hhi k
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

lemma low_core_log_threshold (A : ℕ) :
    ∀ᶠ L : ℝ in atTop, 5832*(1+Real.log L)^A ≤ (Real.log L)^(A+1) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop
    (max 1 (5832*(2:ℝ)^A))] with L hL
  have hlog : 1 ≤ Real.log L := (le_max_left _ _).trans hL
  have hlarge : 5832*(2:ℝ)^A ≤ Real.log L := (le_max_right _ _).trans hL
  calc
    _ ≤ 5832*(2*Real.log L)^A := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (by linarith) _) (by norm_num)
    _ = (5832*(2:ℝ)^A)*(Real.log L)^A := by rw [mul_pow]; ring
    _ ≤ Real.log L*(Real.log L)^A := mul_le_mul_of_nonneg_right hlarge (pow_nonneg (by linarith) _)
    _ = _ := by rw [pow_succ]; ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPolynomialHeightCoreBlock
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_uniform_core_block_polynomial_height (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (k : ℕ) :
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
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 1 e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,CL,ν,hη,hη₁,hσ,hCL,hν,hlarge⟩ :=
    angular_large_core_block_moment ℓ (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR
      (by norm_num : (0:ℝ) < 1/4) hGI hGQ
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨TS,hlarge⟩ := hlarge L W hL hW hlo hhi
  obtain ⟨CS,A,hCS,hsmall⟩ := angular_small_core_block_log_saving ℓ hHuxley hW hR hlo hhi k
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

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit absorption of the retained norm-dyad count and arbitrarily
small arithmetic losses in a fixed polynomial scale range. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_dyad_count_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℝ, 1 ≤ J →
      ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ) ≤ C*(1+Real.log J) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C := 1+Real.log 3/Real.log 2+1/Real.log 2
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro J hJ
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hfloor : (1:ℕ) ≤ ⌊3*J⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    norm_num
    linarith
  have hfloorpos : (0:ℝ) < (⌊3*J⌋₊:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hfloor)
  have hlog := Real.log_le_log hfloorpos (Nat.floor_le (by positivity : 0 ≤ 3*J))
  have hn := Real.natLog_le_logb ⌊3*J⌋₊ 2
  simp only [Real.logb,Nat.cast_ofNat] at hn
  have hjlog := Real.log_nonneg hJ
  have hh : ((Nat.log 2 ⌊3*J⌋₊:ℕ):ℝ) ≤
      (Real.log 3+Real.log J)/Real.log 2 := by
    apply hn.trans
    apply (div_le_div_iff_of_pos_right h2).mpr
    simpa only [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hJp.ne'] using hlog
  rw [Nat.cast_add,Nat.cast_one]
  have hhp : ((Nat.log 2 ⌊3*J⌋₊:ℕ):ℝ)+1 ≤
      (Real.log 3+Real.log J)/Real.log 2+1 := by linarith only [hh]
  apply hhp.trans
  dsimp [C]
  have hx := mul_nonneg (show 0 ≤ 1+Real.log 3/Real.log 2 by positivity) hjlog
  simp only [div_eq_mul_inv] at *
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoreIndexLogCount
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete two-dimensional core partition costs only two powers
of the logarithm, uniformly throughout the required frequency range. -/
noncomputable section
namespace CubicFirstMoment

theorem core_dyadic_index_log_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (V B L : ℝ), 1 ≤ B → 1 ≤ L → B ≤ L^2 →
      ((largeCoreDyadicIndices V B).card:ℝ) ≤ C*(1+Real.log L)^2 := by
  obtain ⟨C,hC,hcount⟩ := metaplectic_dyad_count_log_bound
  refine ⟨4*C^2,by positivity,?_⟩
  intro V B L hB hL hBL
  have hmono : Nat.log 2 ⌊B⌋₊+1 ≤ Nat.log 2 ⌊3*B⌋₊+1 :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono (by linarith))) 1
  have hn : ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ) ≤ C*(1+Real.log B) :=
    (Nat.cast_le.mpr hmono).trans (hcount B hB)
  have hlog : Real.log B ≤ 2*Real.log L := by
    have h := Real.log_le_log (zero_lt_one.trans_le hB) hBL
    rw [← Real.rpow_natCast L 2,Real.log_rpow (zero_lt_one.trans_le hL)] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hn' : ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ) ≤ 2*C*(1+Real.log L) :=
    hn.trans (by nlinarith)
  calc
    _ ≤ ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ)^2 := by
      exact_mod_cast largeCoreDyadicIndices_card V B
    _ ≤ (2*C*(1+Real.log L))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hn' 2
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLargeCorePolynomialHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite large-core contribution has every logarithmic saving
throughout the fixed polynomial height window required by Mellin truncation. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_large_core_cutoff_polynomial_height (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (C T₀ : ℝ) (a : ℕ), 0 < C ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (H : Finset Eisenstein) (e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ (¬∃ z : Eisenstein, z^3 = h) ∧
        h ∉ lowNoncubeSupport ((Real.log (L r))^a) (B^(1/3:ℝ))) →
      e ≠ 0 → norm e ≤ (L r)^σ → 1+|u| ≤ (L r)^(9/25:ℝ) →
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 1 e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hblock⟩ := angular_uniform_core_block_polynomial_height ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hGI hGQ (k+2)
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨CB,TB,A,hCB,hblock⟩ := hblock L W hL hW hlo hhi
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp ((eventually_ge_atTop TB).and (low_core_log_threshold A))
  refine ⟨CI*CB,T₀,A+1,by positivity,?_⟩
  intro r X B H e u hT₀ hprod hX hB hBL hH he heN hu
  obtain ⟨hTB,hcut⟩ := hT (L r) hT₀
  have hB₂ : B ≤ (L r)^2 := by
    apply hBL.trans
    rw [← Real.rpow_natCast (L r) 2]
    exact Real.rpow_le_rpow_of_exponent_le (hL r) (by norm_num; linarith)
  let V := (Real.log (L r))^(A+1)
  let F (h : Eisenstein) := ‖fullStructuredAngularPrimeSum ℓ R h 1 1 e u (W r) X‖^2
  have hlarge : (∑ z ∈ largeCoreDyadicIndices V B,
      ∑ h ∈ coreDyadicBlock B z.1 z.2, F h) ≤
      CI*CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
    have hrow : ∀ z ∈ largeCoreDyadicIndices V B,
        (∑ h ∈ coreDyadicBlock B z.1 z.2, F h) ≤
        CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2) := by
      intro z hz
      have hm := (Finset.mem_filter.mp hz).2
      have hD := coreDyadicConductor_pos z.1 z.2
      have hthreshold : (1+Real.log (L r))^A ≤ 8*coreDyadicConductor z.1 z.2 := by
        dsimp [V] at hm
        nlinarith [hcut]
      exact hblock r X B z.1 z.2 e u _ hTB hprod hX (zero_le_one.trans hB) hBL hm.2
        hthreshold he heN hu (Finset.Subset.refl _)
    have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
    have hbase : 0 ≤ CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2) :=
      div_nonneg (mul_nonneg (mul_nonneg hCB.le (sq_nonneg _)) (Real.rpow_nonneg (zero_le_one.trans hB) _))
        (pow_nonneg hz.le _)
    calc
      _ ≤ ∑ _z ∈ largeCoreDyadicIndices V B,
          CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2) := Finset.sum_le_sum hrow
      _ = ((largeCoreDyadicIndices V B).card:ℝ)*
          (CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2)) := by simp
      _ ≤ (CI*(1+Real.log (L r))^2)*
          (CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2)) :=
        mul_le_mul_of_nonneg_right (hcount V B (L r) hB (hL r) hB₂) hbase
      _ = _ := by rw [pow_add]; field_simp [hz.ne']
  have hsplit := noncube_frequency_mass_split H (V := V)
    (fun h hh => ⟨(hH h hh).1,(hH h hh).2.1,(hH h hh).2.2.1⟩) F (fun _ => sq_nonneg _)
  have hempty : H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro h hh
    exact (hH h hh).2.2.2
  rw [hempty,Finset.sum_empty,zero_add] at hsplit
  exact hsplit.trans hlarge

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramStructuredRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rows in the Poisson kernel are exactly the full structured prime
sums, including the squarefree restriction and the reversal of Mellin height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullSquarefreePrimeSupport_primary (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) {b : Eisenstein} (hb : b ∈ fullSquarefreePrimeSupport R W X e) :
    primary b ∧ Squarefree b := by
  have hm := Finset.mem_filter.mp hb
  exact ⟨orderedPrimarySupport_primary _ (fun i b hb => (fullPrimeSupport_prime R W X i b hb).1) hm.1,hm.2.1⟩

lemma fullPrimeCoefficient_sum_squarefree (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (f : Eisenstein → ℂ) :
    (∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter
      (fun b => IsCoprime b e), fullPrimeCoefficient R W X b*f b) =
    ∑ b ∈ fullSquarefreePrimeSupport R W X e, fullPrimeCoefficient R W X b*f b := by
  simp only [fullSquarefreePrimeSupport,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hsf : Squarefree b
  · simp only [hsf,true_and]
  · simp [hsf,fullPrimeCoefficient,squarefreeConvolution]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeNormRange
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed log-norm range for an unchanged prime convolution is derived
from its coordinate supports. -/
noncomputable section
open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeProduct_norm_bounds (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport (fullPrimeSupport R W X)) :
    (∏ i, X i) ≤ norm b ∧ norm b ≤ R^(Fintype.card ι)*(∏ i, X i) := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  have hbound (i : ι) : X i ≤ norm (f i) ∧ norm (f i) ≤ R*X i := by
    have hmem := Fintype.mem_piFinset.mp hf i
    have hw := ((fullPrimeSupport_mem_iff W X hX hhi i (f i)).mp hmem).2
    constructor
    · have hn : 1 ≤ norm (f i)/X i := le_of_not_gt (fun h => hw (hlo i _ h))
      simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hn
    · have hn : norm (f i)/X i ≤ R := le_of_not_gt (fun h => hw (hhi i _ h))
      exact (div_le_iff₀ (hX i)).mp hn
  rw [norm_finset_prod]
  constructor
  · exact Finset.prod_le_prod (fun i _ => (hX i).le) (fun i _ => (hbound i).1)
  · calc
      _ ≤ ∏ i, R*X i := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (hbound i).2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Fourier decay for the fixed wider log-norm cutoff used by the
actual prime convolution. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma wideGramExp_deriv_bound (M : ℝ) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (i : ℕ), i ≤ n → ∀ u : ℝ, |u| ≤ 2*M →
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D := by
  have hb (i : ℕ) : ∃ D : ℝ, ∀ u ∈ Set.Icc (-2*M) (2*M),
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D :=
    isCompact_Icc.exists_bound_of_continuousOn
      (gramExp_contDiff.continuous_iteratedFDeriv (mod_cast le_top)).continuousOn
  choose B hB using hb
  let D := 1 + ∑ i ∈ Finset.range (n+1), |B i|
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n+1), |B i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨D, by dsimp [D]; linarith, ?_⟩
  intro i hi u hu
  have hbi : |B i| ≤ ∑ j ∈ Finset.range (n+1), |B j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_range.mpr (by omega))
  exact (hB i u ⟨by linarith [(abs_le.mp hu).1], (abs_le.mp hu).2⟩).trans
    ((le_abs_self (B i)).trans (hbi.trans (by dsimp [D]; linarith)))

lemma wideGramExp_scale_growth {M c u : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hu : |u| ≤ 2*M) :
    1+c ≤ Real.exp M * (1+‖c • gramExp u‖) := by
  have hE : 1 ≤ Real.exp M := Real.one_le_exp hM
  have hEu : 1 ≤ Real.exp M * Real.exp (u/2) := by
    rw [← Real.exp_add]
    simpa using Real.exp_le_exp.mpr (show (0:ℝ) ≤ M + u/2 by
      linarith [(abs_le.mp hu).1])
  have hEc := mul_le_mul_of_nonneg_left hEu hc
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, gramExp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  nlinarith

theorem schwartz_wideGramExp_comp_uniform (M : ℝ) (hM : 0 ≤ M) (F : 𝓢(ℂ, ℂ)) (n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c → ∀ u : ℝ, |u| ≤ 2*M →
      (1+c)^K * ‖iteratedFDeriv ℝ n (fun v => F (c • gramExp v)) u‖ ≤ C := by
  obtain ⟨D, hD, hderiv⟩ := wideGramExp_deriv_bound M n
  let L := n+K
  let S := (Finset.Iic (L,n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  let H := (Real.exp M)^L * 2^L * S
  have hS : 0 ≤ S := by positivity
  have hH : 0 ≤ H := by positivity
  refine ⟨(n.factorial : ℝ)*H*D^n, by positivity, ?_⟩
  intro c hc u hu
  have hc1 : 0 < 1+c := by positivity
  have hC (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ ≤ H / (1+c)^L := by
    rw [le_div_iff₀' (pow_pos hc1 L)]
    have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (L,n)) (k := L) (n := i) (le_refl L) hi F (c • gramExp u)
    calc
      _ ≤ (Real.exp M * (1+‖c • gramExp u‖))^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ := by
        gcongr
        exact wideGramExp_scale_growth hM hc hu
      _ = (Real.exp M)^L * ((1+‖c • gramExp u‖)^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖) := by rw [mul_pow]; ring
      _ ≤ (Real.exp M)^L * (2^L*S) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = H := by dsimp [H]; ring
  have hDb (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun v => c • gramExp v) u‖ ≤ ((1+c)*D)^i := by
    rw [iteratedFDeriv_const_smul_apply' (gramExp_contDiff.of_le (mod_cast le_top)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      _ ≤ c*D := mul_le_mul_of_nonneg_left (hderiv i hin u hu) hc
      _ ≤ (1+c)*D := by nlinarith
      _ ≤ ((1+c)*D)^i := le_self_pow₀ (by nlinarith) (by omega)
  have hb := norm_iteratedFDeriv_comp_le (F.smooth ⊤) (gramExp_contDiff.const_smul c)
    (n := n) (mod_cast le_top) u hC hDb
  calc
    _ ≤ (1+c)^K * ((n.factorial : ℝ)*(H/(1+c)^L)*((1+c)*D)^n) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (n.factorial : ℝ)*H*D^n := by
      dsimp [L]
      rw [pow_add, mul_pow]
      field_simp


lemma wideAnnularLogSchwartz_deriv_zero (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (c u : ℝ) (n : ℕ)
    (hu : ¬ |u| ≤ 2*M) : iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u = 0 := by
  by_contra hn
  have hs := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := wideAnnularLogSchwartz M hM F c) n hn
  have hb := tsupport_smul_subset_left ((wideGramLogBump M hM) : ℝ → ℝ)
    (fun v => F (c • gramExp v)) hs
  rw [(wideGramLogBump M hM).tsupport_eq] at hb
  exact hu (by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, wideGramLogBump] using hb)

theorem wideAnnularLogSchwartz_seminorm_uniform (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * SchwartzMap.seminorm ℝ k n (wideAnnularLogSchwartz M hM F c) ≤ C := by
  choose C hC hbound using fun i => schwartz_wideGramExp_comp_uniform M hM.le F i K
  let B : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) * C (n-i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => mul_nonneg (by positivity) (hC (n-i)))
  refine ⟨(2*M)^k * B, by positivity, ?_⟩
  intro c hc
  have hp : 0 < (1+c)^K := pow_pos (by positivity) _
  rw [← le_div_iff₀' hp]
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ 2*M
  · rw [le_div_iff₀' hp]
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (wideGramLogBump M hM).contDiff
      ((F.smooth ⊤).comp (gramExp_contDiff.const_smul c)) u (n := n) (mod_cast le_top)
    have hd' : (1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖ ≤ B := by
      calc
        _ ≤ (1+c)^K * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ *
              ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖ :=
          mul_le_mul_of_nonneg_left hd hp.le
        _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ *
              ((1+c)^K * ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ B := by
          apply Finset.sum_le_sum
          intro i hi
          have hb : ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ ≤
              SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) := by
            have hb := SchwartzMap.le_seminorm ℝ 0 i (wideGramBumpSchwartz M hM) u
            rw [show (wideGramBumpSchwartz M hM : ℝ → ℝ) = ((wideGramLogBump M hM) : ℝ → ℝ) from rfl] at hb
            simpa only [pow_zero, one_mul] using hb
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity))
            (hbound (n-i) c hc u hu) (by positivity) (by positivity)
    calc
      _ = ‖u‖^k * ((1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖) := by ring
      _ ≤ (2*M)^k * B := mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _)
        (by simpa only [Real.norm_eq_abs] using hu) k) hd' (by positivity) (by positivity)
  · rw [wideAnnularLogSchwartz_deriv_zero M hM F c u n hu, norm_zero, mul_zero]
    positivity

lemma wideAnnularLogSchwartz_eq_wideGramLogSchwartz (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    wideAnnularLogSchwartz M hM (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ) =
      wideGramLogSchwartz M hM W hW hW' ρ := by
  ext u
  simp only [wideAnnularLogSchwartz_apply M hM, wideGramLogSchwartz_apply, wideGramLogKernel,
    normProfileFourierSchwartz_apply]
  congr 2
  simp only [gramExp, Complex.real_smul, Complex.ofReal_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormDenominatorMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm denominator in the actual Poisson formula stays in its
Mellin kernel. No real power is inserted into the prime coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma normDenominatorMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    Integrable (normDenominatorMellinCoefficient M hM W hW hW' ρ) :=
  (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integrable


lemma normDenominatorLogSchwartz_eq_annular (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    normDenominatorLogSchwartz M hM W hW hW' ρ =
      SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
        (wideAnnularLogSchwartz M hM (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ)) := by
  rw [wideAnnularLogSchwartz_eq_wideGramLogSchwartz]
  rfl

lemma normDenominatorFourier_seminorm_uniform (M : ℝ) (hM : 0 < M)
    (F : 𝓢(ℂ,ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c → (1+c)^K * SchwartzMap.seminorm ℝ k n
      (𝓕 (SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
        (wideAnnularLogSchwartz M hM F c))) ≤ C := by
  let f : ℝ → 𝓢(ℝ,ℂ) := fun c => (1+c)^K • wideAnnularLogSchwartz M hM F c
  have hb : Bornology.IsVonNBounded ℝ (f '' Ici 0) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C,hC,hc⟩ := wideAnnularLogSchwartz_seminorm_uniform M hM F i.1 i.2 K
    refine ⟨C+1,by linarith,?_⟩
    intro c hc0
    have hc0' : 0 ≤ c := hc0
    change SchwartzMap.seminorm ℝ i.1 i.2 ((1+c)^K • wideAnnularLogSchwartz M hM F c) < _
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (pow_pos (by linarith [hc0']) _)]
    exact (hc c hc0).trans_lt (by linarith)
  let A : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.fourierTransformCLM ℝ (V := ℝ) (E := ℂ)).comp
      ((SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)).restrictScalars ℝ)
  have hA := hb.image A
  obtain ⟨C,hC,hc⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hA (k,n)
  refine ⟨C,hC,?_⟩
  intro c hc0
  have h := hc (A (f c)) ⟨f c,⟨c,hc0,rfl⟩,rfl⟩
  change SchwartzMap.seminorm ℝ k n (A ((1+c)^K • wideAnnularLogSchwartz M hM F c)) < C at h
  rw [map_smul,map_smul_eq_mul,Real.norm_eq_abs,
    abs_of_pos (pow_pos (by linarith) _)] at h
  exact h.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormMellinMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrated decay with polynomial Mellin-height weights. This controls
truncated shifts in the dispersion kernel. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

theorem normDenominatorMellinCoefficient_moment_decay (M : ℝ) (hM : 0 < M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^A * (∫ t : ℝ, ‖t‖^B*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) ≤ C := by
  let k := (volume : Measure ℝ).integrablePower
  let D : ℝ := 2^k * ∫ t : ℝ, (1+‖t‖)^(-(k:ℝ))
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg (fun t => by positivity))
  obtain ⟨C₀,hC₀,hc₀⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') 0 0 (2*A)
  obtain ⟨C₁,hC₁,hc₁⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') (B+k) 0 (2*A)
  refine ⟨D*(C₀+C₁)+1,by positivity,?_⟩
  intro ρ hρ
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_nonneg ρ]
  have h := (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integral_pow_mul_iteratedFDeriv_le ℝ volume B 0
  simp only [norm_iteratedFDeriv_zero] at h
  have h₀ := hc₀ (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  have h₁ := hc₁ (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [← normDenominatorLogSchwartz_eq_annular] at h₀ h₁
  have hb : (1+ρ)^A * (∫ t : ℝ, ‖t‖^B*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) ≤ D*(C₀+C₁) := by
    calc
      _ ≤ (1+Real.sqrt ρ)^(2*A) * (D *
          (SchwartzMap.seminorm ℝ 0 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
           SchwartzMap.seminorm ℝ (B+k) 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)))) :=
        mul_le_mul hs h (integral_nonneg (fun t => by positivity)) (by positivity)
      _ = D*((1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ 0 0
          (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
        (1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ (B+k) 0
          (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h₀ h₁) hD
  linarith

lemma mellin_window_majorant {g : ℝ → ℝ} {B C T : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT : 0 < T) (k : ℕ) (hg : ∀ t, g t ≤ C) (hsmall : ∀ t, ‖t‖ ≤ T → g t ≤ B) (t : ℝ) :
    g t ≤ B+C/T^k*‖t‖^k := by
  by_cases ht : ‖t‖ ≤ T
  · exact (hsmall t ht).trans (le_add_of_nonneg_right (by positivity))
  · have hp : T^k ≤ ‖t‖^k := pow_le_pow_left₀ hT.le (le_of_not_ge ht) _
    have hratio : 1 ≤ ‖t‖^k/T^k := (le_div_iff₀ (pow_pos hT _)).mpr (by simpa using hp)
    calc
      _ ≤ C := hg t
      _ ≤ C*(‖t‖^k/T^k) := le_mul_of_one_le_right hC hratio
      _ = C/T^k*‖t‖^k := by ring
      _ ≤ B+C/T^k*‖t‖^k := le_add_of_nonneg_left hB


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeMellinEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial coarse envelope for the unchanged full prime rows,
uniform in Mellin height and the ambient set of prime divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeSupport_card_bound {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0) (e : Eisenstein) :
    ((fullSquarefreePrimeSupport R W X e).card:ℝ) ≤ 18*(R^Fintype.card ι*(∏ i, X i)) := by
  apply primary_support_card_le _ (mul_nonneg (pow_nonneg hR _) (Finset.prod_nonneg (fun i _ => (hX i).le)))
  intro b hb
  exact ⟨(fullSquarefreePrimeSupport_primary R W X e hb).1,
    (fullPrimeProduct_norm_bounds R W X hX hlo hhi (Finset.mem_filter.mp hb).1).2⟩

lemma fullPrimeCoefficient_l1_square {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0) (e : Eisenstein) :
    (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖)^2 ≤
      18*(R^Fintype.card ι*(∏ i, X i))*
        ∑ b ∈ orderedConvolutionSupport (fullPrimeSupport R W X), ‖fullPrimeCoefficient R W X b‖^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (fullSquarefreePrimeSupport R W X e)
    (fun _ => (1:ℝ)) (fun b => ‖fullPrimeCoefficient R W X b‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  apply hcs.trans
  apply mul_le_mul (fullPrimeSupport_card_bound hR W X hX hlo hhi e)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg hR _) (Finset.prod_nonneg (fun i _ => (hX i).le))))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredHeightMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite frequency blocks retain the proved height mean, with an explicit
row count for the actual ramified and cube decomposition. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma continuous_fullStructuredAngularSum (R : ℝ) (h v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    Continuous (fun t : ℝ => fullStructuredAngularSum R h v e ℓ (t+u) W X) := by
  simp_rw [fullStructuredAngularSum_eq]
  apply continuous_finsetSum
  intro z _
  apply continuous_const.mul
  unfold mellinPhase
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp
      ((continuous_id.add continuous_const).mul continuous_const)).mul continuous_const)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredHeightContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and boundedness of the actual finite height mass. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullStructuredHeightMass_nonneg (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein)
    (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (t : ℝ) :
    0 ≤ fullStructuredHeightMass R H v e ℓ u W X t :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma continuous_fullStructuredHeightMass (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein)
    (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    Continuous (fullStructuredHeightMass R H v e ℓ u W X) := by
  exact continuous_finsetSum H (fun h _ =>
    ((continuous_fullStructuredAngularSum R h v e ℓ u W X).norm).pow 2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullStructuredHeightEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial envelope for the actual angular height mass, uniform
in height, angular index, numerator and exclusions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullStructuredAngularSum_norm_le_l1 (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (h v e : Eisenstein) (ℓ : ℤ) (u : ℝ) :
    ‖fullStructuredAngularSum R h v e ℓ u W X‖ ≤
      ∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖ := by
  have he : fullStructuredAngularSum R h v e ℓ u W X =
      ∑ b ∈ fullSquarefreePrimeSupport R W X e, fullPrimeCoefficient R W X b*
        (cubicSymbol b (v*h)*theta ℓ b*mellinPhase u (norm b)) := by
    calc
      _ = ∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter (fun b => IsCoprime b e),
          fullPrimeCoefficient R W X b*(cubicSymbol b (v*h)*theta ℓ b*mellinPhase u (norm b)) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := fullPrimeCoefficient_sum_squarefree R W X e _
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  have hp := (fullSquarefreePrimeSupport_primary R W X e hb).1
  rw [norm_mul,norm_mul,norm_mul,norm_theta (primary_ne_zero hp),mellinPhase_norm,mul_one,mul_one]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hp _)

theorem logarithmic_full_height_envelope {R : ℝ} (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (K : ℝ) (A : ℕ), 0 ≤ K ∧ ∀ (r : γ) (X : ι → ℝ), 1 ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ∀ (H : Finset Eisenstein) (v e : Eisenstein) (ℓ : ℤ) (u t : ℝ),
      fullStructuredHeightMass R H v e ℓ u (W r) X t ≤
        K*(H.card:ℝ)*(L r)^2*(1+Real.log (L r))^A := by
  obtain ⟨C,A,hC,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  refine ⟨18*R^Fintype.card ι*C,A,by positivity,?_⟩
  intro r X hL hX hprod H v e ℓ u t
  have hl := fullPrimeCoefficient_l1_square (zero_le_one.trans hR) (W r) X
    (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) e
  rw [hprod] at hl
  have hl' := hl.trans (mul_le_mul_of_nonneg_left (henergy r X hL hX hprod) (by positivity))
  calc
    _ ≤ ∑ _h ∈ H, (∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
        ‖fullPrimeCoefficient R (W r) X b‖)^2 := by
      apply Finset.sum_le_sum
      intro h _
      exact pow_le_pow_left₀ (_root_.norm_nonneg _)
        (fullStructuredAngularSum_norm_le_l1 R (W r) X h v e ℓ (t+u)) 2
    _ = (H.card:ℝ)*(∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
        ‖fullPrimeCoefficient R (W r) X b‖)^2 := by simp
    _ ≤ (H.card:ℝ)*(18*(R^Fintype.card ι*L r)*(C*L r*(1+Real.log (L r))^A)) :=
      mul_le_mul_of_nonneg_left hl' (Nat.cast_nonneg _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArithmeticMellinKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the Fourier-transform frequency to the arithmetic height in
N(n)^(it). The fixed factor 2π stays in the actual kernel. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open Set MeasureTheory
namespace CubicFirstMoment

lemma arithmeticMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) :
    Integrable (arithmeticMellinCoefficient M hM V hV hV' ρ) :=
  (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).comp_div
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArithmeticMellinMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial integral moments after the exact 2π rescaling. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace CubicFirstMoment

lemma arithmetic_mellin_moment_scale (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) (k : ℕ) (t : ℝ) :
    ‖t‖^k*‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖ =
      (2*Real.pi)^k*(‖t/(2*Real.pi)‖^k*
        ‖normDenominatorMellinCoefficient M hM V hV hV' ρ (t/(2*Real.pi))‖) := by
  have hc : 2*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  simp only [arithmeticMellinCoefficient,norm_div,Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi),div_pow]
  field_simp

lemma arithmeticMellinCoefficient_moment_integrable (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) (k : ℕ) :
    Integrable (fun t : ℝ => ‖t‖^k*‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖) := by
  have hi := (𝓕 (normDenominatorLogSchwartz M hM V hV hV' ρ)).integrable_pow_mul volume k
  have hscaled := (hi.comp_div (R := 2*Real.pi) (mul_ne_zero (by norm_num) Real.pi_ne_zero)).const_mul ((2*Real.pi)^k)
  exact hscaled.congr (Eventually.of_forall (fun t => (arithmetic_mellin_moment_scale M hM V hV hV' ρ k t).symm))

theorem arithmeticMellinCoefficient_moment_decay (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖t‖^k*‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖) ≤ C := by
  obtain ⟨C,hC,hb⟩ := normDenominatorMellinCoefficient_moment_decay M hM V hV hV' q k
  refine ⟨(2*Real.pi)^(k+1)*C,by positivity,?_⟩
  intro ρ hρ
  simp_rw [arithmetic_mellin_moment_scale]
  have he := Measure.integral_comp_div
    (fun t : ℝ => ‖t‖^k*‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖) (2*Real.pi)
  rw [integral_const_mul,he,abs_of_pos (by positivity : 0 < 2*Real.pi),smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left (hb ρ hρ) (pow_nonneg (by positivity : 0 ≤ 2*Real.pi) (k+1))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [pow_succ]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWindowIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded finite mass is integrated using its local bound and a
polynomial kernel moment. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

theorem integral_bounded_mellin_window {f g : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ t, 0 ≤ f t) (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    {B C T : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hT : 0 < T) (k : ℕ)
    (hfk : Integrable (fun t : ℝ => ‖t‖^k*f t))
    (hgC : ∀ t, g t ≤ C) (hsmall : ∀ t, ‖t‖ ≤ T → g t ≤ B) :
    (∫ t : ℝ, f t*g t) ≤ B*(∫ t : ℝ, f t)+C/T^k*(∫ t : ℝ, ‖t‖^k*f t) := by
  have hi : Integrable (fun t : ℝ => f t*g t) := hf.mul_bdd hg.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hg0 t)]
      exact hgC t))
  have hm := (hf.const_mul B).add (hfk.const_mul (C/T^k))
  calc
    _ ≤ ∫ t : ℝ, B*f t+(C/T^k)*(‖t‖^k*f t) := by
      apply integral_mono hi hm
      intro t
      calc
        _ ≤ f t*(B+C/T^k*‖t‖^k) :=
          mul_le_mul_of_nonneg_left (mellin_window_majorant hB hC hT k hgC hsmall t) (hf0 t)
        _ = _ := by dsimp only [Pi.add_apply]; ring
    _ = _ := by rw [integral_add (hf.const_mul B) (hfk.const_mul (C/T^k)),
      integral_const_mul,integral_const_mul]

theorem arithmeticMellin_bounded_window (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q k : ℕ) :
    ∃ D₀ Dk : ℝ, 0 < D₀ ∧ 0 < Dk ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ (g : ℝ → ℝ), Continuous g → (∀ t, 0 ≤ g t) →
      ∀ B C T : ℝ, 0 ≤ B → 0 ≤ C → 0 < T →
      (∀ t, g t ≤ C) → (∀ t, ‖t‖ ≤ T → g t ≤ B) →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*g t) ≤
        B*D₀+C/T^k*Dk := by
  obtain ⟨D₀,hD₀,hzero⟩ := arithmeticMellinCoefficient_moment_decay M hM V hV hV' q 0
  obtain ⟨Dk,hDk,hk⟩ := arithmeticMellinCoefficient_moment_decay M hM V hV hV' q k
  refine ⟨D₀,Dk,hD₀,hDk,?_⟩
  intro ρ hρ g hg hg0 B C T hB hC hT hgC hsmall
  let F := arithmeticMellinCoefficient M hM V hV hV' ρ
  have hi := integral_bounded_mellin_window
    (arithmeticMellinCoefficient_integrable M hM V hV hV' ρ).norm
    (fun t => _root_.norm_nonneg (F t)) hg hg0 hB hC hT k
    (arithmeticMellinCoefficient_moment_integrable M hM V hV hV' ρ k) hgC hsmall
  have hz : (1+ρ)^q*(∫ t : ℝ, ‖F t‖) ≤ D₀ := by
    simpa only [pow_zero,one_mul] using hzero ρ hρ
  calc
    _ ≤ (1+ρ)^q*(B*(∫ t : ℝ, ‖F t‖)+C/T^k*(∫ t : ℝ, ‖t‖^k*‖F t‖)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = B*((1+ρ)^q*(∫ t : ℝ, ‖F t‖))+
        C/T^k*((1+ρ)^q*(∫ t : ℝ, ‖t‖^k*‖F t‖)) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hz hB)
      (mul_le_mul_of_nonneg_left (hk ρ hρ) (by positivity))

lemma polynomial_mellin_tail_absorb {L z E : ℝ} (hL : 0 < L) (hz : 0 < z)
    (b k : ℕ) (hlog : E*z^(b+k) ≤ L) :
    (E*L^4*z^b)/(L^(1/4:ℝ))^12 ≤ L^2/z^k := by
  have he : (L^(1/4:ℝ))^12 = L^3 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
    norm_num
  rw [he]
  apply (div_le_div_iff₀ (pow_pos hL 3) (pow_pos hz k)).mpr
  have hm := mul_le_mul_of_nonneg_left hlog (le_of_lt (pow_pos hL 4))
  rw [pow_add] at hm
  nlinarith only [hm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLargeCoreMellinIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The large-core mass over all Mellin heights. The polynomial-height
sieve controls the window; the literal coefficient envelope and the
kernel's twelfth moment control the complement. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_large_core_mellin_integral_saving_oai (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (K T₀ : ℝ) (a : ℕ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (H : Finset Eisenstein) (e : Eisenstein) (u ρ : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ (¬∃ z : Eisenstein, z^3 = h) ∧
        h ∉ lowNoncubeSupport ((Real.log (L r))^a) (B^(1/3:ℝ))) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (L r)^(1/4:ℝ) → 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*
        fullStructuredHeightMass R H 1 e ℓ u (W r) X t) ≤
          K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hlarge⟩ := angular_large_core_cutoff_polynomial_height ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hGI hGQ k
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨Cl,Tl,a,hCl,hlarge⟩ := hlarge L W hL hW hlo hhi
  obtain ⟨Ce,b,hCe,henv⟩ := logarithmic_full_height_envelope hR hW hlo hhi
  obtain ⟨D₀,D₁₂,hD₀,hD₁₂,hwindow⟩ := arithmeticMellin_bounded_window M hM V hV hV' q 12
  have hlogevent := exclusion_log_absorption (c := 1) (d := 0) (ε := 1) (C := 18*Ce*D₁₂)
    (by norm_num) (by norm_num) (by positivity) (b+k) 0
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp ((eventually_ge_atTop Tl).and
    ((eventually_const_mul_rpow_le (by norm_num : (1/4:ℝ) < 9/25) 3).and hlogevent))
  refine ⟨Cl*D₀+1,T₀,a,by positivity,?_⟩
  intro r X B H e u ρ hT hprod hX hB hBL hH he heN hu hρ
  obtain ⟨hTl,hheight,hlog⟩ := hT₀ (L r) hT
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  let T := (L r)^(1/4:ℝ)
  let G := fullStructuredHeightMass R H 1 e ℓ u (W r) X
  let Bl := Cl*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k
  let E := 18*Ce*D₁₂
  have hX1 : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le
  have hT1 : 1 ≤ T := Real.one_le_rpow (hL r) (by norm_num)
  have hB2 : B ≤ (L r)^2 := by
    apply hBL.trans
    rw [← Real.rpow_natCast (L r) 2]
    exact Real.rpow_le_rpow_of_exponent_le (hL r) (by norm_num; linarith)
  have hcard : (H.card:ℝ) ≤ 18*(L r)^2 := by
    have hsub : H ⊆ nonzeroNormBall B := fun h hh =>
      mem_nonzeroNormBall.mpr ⟨(hH h hh).2.1,(hH h hh).1⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      ((nonzeroNormBall_card_le (zero_le_one.trans hB)).trans (by gcongr))
  have hgC : ∀ t, G t ≤ 18*Ce*(L r)^4*(1+Real.log (L r))^b := by
    intro t
    apply (henv r X (hL r) hX1 hprod H 1 e ℓ u t).trans
    calc
      _ ≤ Ce*(18*(L r)^2)*(L r)^2*(1+Real.log (L r))^b := by gcongr
      _ = _ := by ring
  have hsmall : ∀ t : ℝ, ‖t‖ ≤ T → G t ≤ Bl := by
    intro t ht
    have hs : 1+|t+u| ≤ (L r)^(9/25:ℝ) := by
      have ha := abs_add_le t u
      rw [Real.norm_eq_abs] at ht
      calc
        _ ≤ 1+(|t|+|u|) := by linarith
        _ ≤ 3*T := by dsimp only [T] at *; linarith
        _ ≤ _ := hheight
    simpa only [G,Bl,fullStructuredHeightMass,←fullStructuredAngularPrimeSum_eq_existing ℓ] using
      hlarge r X B H e (t+u) hTl hprod hX hB hBL hH he heN hs
  have hi := hwindow ρ hρ G (continuous_fullStructuredHeightMass R H 1 e ℓ u (W r) X)
    (fullStructuredHeightMass_nonneg R H 1 e ℓ u (W r) X) Bl
    (18*Ce*(L r)^4*(1+Real.log (L r))^b) T (by dsimp [Bl]; positivity)
    (by positivity) (zero_lt_one.trans_le hT1) hgC hsmall
  have hl : E*(1+Real.log (L r))^(b+k) ≤ L r := by
    have hh := hlog (L r) 1 (by norm_num) (by simp) (by simp)
    simpa only [Real.one_rpow,one_mul,mul_one,pow_zero,div_one,E] using hh
  have htail : (18*Ce*(L r)^4*(1+Real.log (L r))^b)/T^12*D₁₂ ≤
      (L r)^2/(1+Real.log (L r))^k := by
    convert polynomial_mellin_tail_absorb hLp hz b k hl using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [T,E]
    ring
  have hbroot : 1 ≤ B^(1/3:ℝ) := Real.one_le_rpow hB (by norm_num)
  have hbase : (L r)^2/(1+Real.log (L r))^k ≤
      (L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg _) hbroot) (pow_nonneg hz.le k)
  apply hi.trans
  apply (add_le_add le_rfl (htail.trans hbase)).trans_eq
  dsimp only [Bl]
  ring

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CubicFirstMoment.angular_large_core_mellin_integral_saving_oai.{u_1, u_2} := @OAI.CubicFirstMoment.angular_large_core_mellin_integral_saving_oai.{u_1, u_2}
