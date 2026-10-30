-- Prove2me | solution 1 for OAI.CubicFirstMoment.dominant_balanced_full_factor_neighborhood
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:27:51.439398+00:00
-- url     : https://prove2.me/submissions/7858f2f9-9349-4b1b-a9d0-bc9f1586e0aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_full_smooth_twisted_primitive_cubic_bound

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

lemma ResidueCharacterInduces.global_units {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1) :
    ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1 := by
  intro u
  have hc : IsCoprime q (u:Eisenstein) := ⟨0,(u⁻¹:Eisensteinˣ),by simp⟩
  exact (h.2 u hc).trans (hu u)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primaryElementBall_card_le {X : ℝ} (hX : 0 ≤ X) :
    ((primaryElementBall X).card : ℝ) ≤ 18*X :=
  (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (nonzeroNormBall_card_le hX)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueProducts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedPrimitive
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

 theorem twisted_mixed_primitive_conductor {a b r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (hnu : ¬ IsUnit (a*b)) (η : MulChar (Residues r) ℂ)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) u) = 1) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ ψ ≠ 1 ∧
      normNat d ≤ normNat ((3*(a*b))*r) ∧ a*b ∣ d ∧
      (∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1) ∧
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
  exact hind.global_units (productResidueChar_units _ η
    (primaryMixedResidueChar_trivialInfinity ha hb) hη)

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

lemma twisted_ideal_mixed_match {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) u) = 1)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (ν : EisensteinIdealExponent) (hν : primary (idealPrimaryGenerator ν))
    (hνr : IsCoprime r (idealPrimaryGenerator ν)) :
    residueIdealChar d ψ ν = primaryMixedIdealChar a b ν*residueIdealChar r η ν := by
  rw [residueIdealChar_primaryNormalize ψ hu ν,residueIdealChar_primaryNormalize η hη ν,
    twisted_character_primary_match ha hb ψ η
      (twisted_conductor_contains ha hb hsa hsb hab hsmall ψ η hagree) hagree hν hνr,
    primaryMixedIdealChar_eq,ite_eq_left hν]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedEuler
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Euler restoration for the small-twisted primary sum. Only the
primes above three and the fixed small modulus are omitted. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma twisted_residue_restriction {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) u) = 1)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (ν : EisensteinIdealExponent) :
    primaryMixedIdealChar a b ν*residueIdealChar r η ν =
      if ∀ p ∈ (idealExponentOf (3*r)).support, ν p = 0 then residueIdealChar d ψ ν else 0 := by
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
    exact (twisted_ideal_mixed_match ha hb hsa hsb hab hsmall ψ η hu hη hagree ν hprim hpr).symm
  · rw [ite_eq_right hlocal]
    by_cases hprim : primary (idealPrimaryGenerator ν)
    · have hn : ¬ IsCoprime r (idealExponentGenerator ν) := by
        intro hc
        apply hlocal
        apply (ideal_coprime_support h3r ν).mp
        exact ((idealGenerator_coprime_three_iff ν).mpr
          ((idealPrimaryGenerator_primary_iff ν).mp hprim)).symm.mul_left hc
      have hz : residueIdealChar r η ν = 0 :=
        MulChar.map_nonunit η (fun h => hn (isCoprime_of_residue_isUnit h))
      rw [hz,mul_zero]
    · rw [primaryMixedIdealChar_eq,ite_eq_right hprim,zero_mul]

 theorem primary_smalltwist_euler {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) u) = 1)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    (∑' x : Eisenstein, if primary x then
      mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)*
        mellinPhase t (norm x)*W (norm x/Z) else 0) =
      ∑ T ∈ (idealExponentOf (3*r)).support.powerset,
        (-1:ℂ)^T.card*residueIdealChar d ψ (primeSetExponent T)*
          mellinPhase t (idealExponentNorm (primeSetExponent T))*
          ∑' ν, residueIdealChar d ψ ν*mellinPhase t (idealExponentNorm ν)*
            W (idealExponentNorm ν/(Z/idealExponentNorm (primeSetExponent T))) := by
  let χ (ν : EisensteinIdealExponent) :=
    primaryMixedIdealChar a b ν*residueIdealChar r η ν*mellinPhase t (idealExponentNorm ν)
  have he : (∑' x : Eisenstein, if primary x then
      mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)*
        mellinPhase t (norm x)*W (norm x/Z) else 0) =
      ∑' ν, χ ν*W (idealExponentNorm ν/Z) := by
    have hh := primary_element_ideal_smooth_eq χ W hW hZ
    have hleft : (∑' x : Eisenstein, if primary x then
        mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)*
          mellinPhase t (norm x)*W (norm x/Z) else 0) =
        ∑' x : Eisenstein, if primary x then χ (idealExponentOf x)*W (norm x/Z) else 0 := by
      apply tsum_congr
      intro x
      by_cases hx : primary x
      · rw [ite_eq_left hx,ite_eq_left hx]
        dsimp only [χ]
        rw [primaryMixedIdealChar_at_element ha hb hx,
          idealExponentOf_norm (primary_ne_zero hx),
          residueIdealChar_primaryNormalize η hη,idealPrimaryGenerator_at_element hx]
      · rw [ite_eq_right hx,ite_eq_right hx]
    rw [hleft,hh]
    apply tsum_congr
    intro ν
    by_cases hν : primary (idealPrimaryGenerator ν)
    · rw [ite_eq_left hν]
    · rw [ite_eq_right hν]
      simp only [χ,primaryMixedIdealChar_eq,ite_eq_right hν,zero_mul]
  rw [he]
  let ω (ν : EisensteinIdealExponent) := residueIdealChar d ψ ν*mellinPhase t (idealExponentNorm ν)
  have hω (ν κ : EisensteinIdealExponent) : ω (ν+κ) = ω ν*ω κ := by
    dsimp only [ω]
    rw [residueIdealChar_add,idealExponentNorm_add,
      mellinPhase_mul_pos t (idealExponentNorm_pos ν) (idealExponentNorm_pos κ)]
    ring
  have hf : (∑' ν, χ ν*W (idealExponentNorm ν/Z)) =
      ∑' ν, if ∀ p ∈ (idealExponentOf (3*r)).support, ν p = 0 then
        ω ν*W (idealExponentNorm ν/Z) else 0 := by
    apply tsum_congr
    intro ν
    dsimp only [χ,ω]
    rw [twisted_residue_restriction ha hb hsa hsb hab hr hsmall ψ η hu hη hagree]
    split <;> simp
  rw [hf]
  simpa only [ω,mul_assoc] using smooth_ideal_euler_exclusion
    (idealExponentOf (3*r)).support ω hω W hW hZ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedPrimitiveFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing the actual primitive characters for a finite family, with
uniform arithmetic conductor bounds. -/
noncomputable section
namespace CubicFirstMoment

 theorem actual_primitive_smalltwist_family (P : Finset Eisenstein) {b r : Eisenstein}
    (hb : primary b) (hsb : Squarefree b) (hr : r ≠ 0) (η : MulChar (Residues r) ℂ)
    (hη : ∀ v : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) v) = 1)
    (hP : ∀ a ∈ P, primary a ∧ Squarefree a ∧ IsCoprime a b ∧ ¬ IsUnit (a*b))
    (hsmall : ∀ a ∈ P, IsCoprime (a*b) r) :
    ∃ (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ),
      ∀ a ∈ P, PrimitiveSmallTwistSpecification a b r (d a) η (ψ a) := by
  have hex (a : Eisenstein) : ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      a ∈ P → PrimitiveSmallTwistSpecification a b r d η ψ := by
    by_cases ha : a ∈ P
    · obtain ⟨d,ψ,hd,hprim,hn,hN,_,hu,_,hag⟩ := twisted_mixed_primitive_conductor
        (hP a ha).1 hb (hP a ha).2.1 hsb (hP a ha).2.2.1 hr
        (hsmall a ha) (hP a ha).2.2.2 η hη
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallTwistSmoothMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem primary_smalltwist_smooth_cubic_moment (hpub : PrimitiveResidueHeckeInput)
    {ε : ℝ} (hε : 0 < ε) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (P : Finset Eisenstein) (b q : Eisenstein) (η : MulChar (Residues q) ℂ) (N Y Z J t : ℝ),
      primary b → Squarefree b → q ≠ 0 →
      (∀ v : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) v) = 1) →
      (∀ a ∈ P, IsCoprime (a*b) q) →
      1 ≤ N → 1 ≤ Y → 9*norm q ≤ Z → 1 ≤ J →
      Z ≤ Y^H → J ≤ Y^H →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧
        IsCoprime a b ∧ ¬ IsUnit (a*b)) →
      ((243*N*norm b*norm q^2/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      (∑ a ∈ P, ‖primarySmallTwistSmoothSum a b q η W Z t‖^2) ≤
        C*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*q)^(3*ε) +
          D*P.card*Y^(-2*R)*norm (3*q)^(2*ε) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := full_smooth_twisted_primitive_cubic_bound hpub hε
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
  obtain ⟨d,ψ,hspec⟩ := actual_primitive_smalltwist_family P hb hsb hq η hη
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.2.1,(hP a ha).2.2.2.2⟩) hsmall
  let V (a : Eisenstein) (T : Finset EisensteinIdealPrime) : ℂ :=
    ∑' ν, residueIdealChar (d a) (ψ a) ν*mellinPhase t (idealExponentNorm ν)*
      W (idealExponentNorm ν/(Z/idealExponentNorm (primeSetExponent T)))
  let F (a : Eisenstein) (T : Finset EisensteinIdealPrime) : ℂ :=
    (-1:ℂ)^T.card*residueIdealChar (d a) (ψ a) (primeSetExponent T)*
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
      (fun a ha => (hspec a ha).2.2.1) (fun a ha => (hspec a ha).2.2.2.1)
      (fun a ha => (hspec a ha).2.2.2.2.1) hlocal
    calc
      _ ≤ ∑ a ∈ P, ‖V a T‖^2 := by
        apply Finset.sum_le_sum
        intro a ha
        have hc : ‖(-1:ℂ)^T.card*residueIdealChar (d a) (ψ a) (primeSetExponent T)*
            mellinPhase t (idealExponentNorm (primeSetExponent T))‖ ≤ 1 := by
          simpa only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
            mellinPhase_norm,mul_one] using
            residueIdealChar_norm_le_one (hspec a ha).1 (ψ a) (primeSetExponent T)
        apply pow_le_pow_left₀ (_root_.norm_nonneg _)
        exact (norm_mul _ _).trans_le (mul_le_of_le_one_left (_root_.norm_nonneg _) hc)
      _ ≤ C*(Z/r)*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*q)^ε + D*P.card*Y^(-2*R) := hv
      _ ≤ B := by dsimp [B]; gcongr
  have hsplit (a : Eisenstein) (ha : a ∈ P) :
      primarySmallTwistSmoothSum a b q η W Z t = ∑ T ∈ K, F a T :=
    primary_smalltwist_euler (hP a ha).1 hb (hP a ha).2.1 hsb
      (hP a ha).2.2.2.1 hq (hsmall a ha) (ψ a) η (hspec a ha).2.2.2.1 hη
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedSmallTwistPower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

 theorem balanced_smalltwist_smooth_power (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Finset Eisenstein) (b q : Eisenstein)
      (η : MulChar (Residues q) ℂ) (N Y Z J t : ℝ),
      primary b → Squarefree b → q ≠ 0 →
      (∀ v : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) v) = 1) →
      (∀ a ∈ P, IsCoprime (a*b) q) →
      1 ≤ N → 1 ≤ Y → 9*norm q ≤ Z → 1 ≤ J →
      N ≤ Y^(1/2:ℝ) → Z ≤ Y^(101/100:ℝ) → J ≤ Y^(1/2:ℝ) →
      norm q ≤ Y^(1/1000:ℝ) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b ∧ ¬ IsUnit (a*b)) →
      ((243*N*norm b*norm q^2/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) ≤ Y^(-(1/1000:ℝ)) →
      (∑ a ∈ P, ‖primarySmallTwistSmoothSum a b q η W Z t‖^2) ≤ C*Y^(9/5:ℝ) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := primary_smalltwist_smooth_cubic_moment hpub
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedSmallTwistCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

 theorem balanced_smalltwist_smooth_power_at_height (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (P : Finset Eisenstein) (b q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (N Y Z t : ℝ), Y₀ ≤ Y → primary b → Squarefree b → q ≠ 0 →
      (∀ v : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) v) = 1) →
      (∀ a ∈ P, IsCoprime (a*b) q) → 1 ≤ N →
      N ≤ Y^(17/50:ℝ) → Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      norm b ≤ Y^(17/50:ℝ) → norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b ∧ ¬ IsUnit (a*b)) →
      (∑ a ∈ P, ‖primarySmallTwistSmoothSum a b q η W Z t‖^2) ≤ C*Y^(9/5:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := balanced_smalltwist_smooth_power hpub W hW hpos hsm hGI hGQ
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem balanced_smalltwist_pair_power (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (S : Finset (Eisenstein × Eisenstein)) (q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (Y Z t : ℝ), Y₀ ≤ Y → q ≠ 0 →
      (∀ v : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) v) = 1) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z → norm q ≤ Y^(1/1000:ℝ) →
      |t| ≤ Y^(37/100:ℝ) →
      (∀ p ∈ S, primary p.1 ∧ Squarefree p.1 ∧ primary p.2 ∧ Squarefree p.2 ∧
        norm p.1 ≤ Y^(17/50:ℝ) ∧ norm p.2 ≤ Y^(17/50:ℝ) ∧
        IsCoprime p.1 p.2 ∧ ¬ IsUnit (p.1*p.2) ∧ IsCoprime (p.1*p.2) q) →
      (∑ p ∈ S, ‖primarySmallTwistSmoothSum p.1 p.2 q η W Z t‖^2) ≤ C*Y^(11/5:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := balanced_smalltwist_smooth_power_at_height hpub W hW hpos hsm hGI hGQ
  refine ⟨18*C,T,by positivity,hT,?_⟩
  intro S q η Y Z t hY hq hη hZY hYZ hqY ht hS
  have hY1 : 1 ≤ Y := hT.trans hY
  have hrow (b : Eisenstein) (hb : b ∈ S.image Prod.snd) :
      (∑ a ∈ pairFirstFiber S b, ‖primarySmallTwistSmoothSum a b q η W Z t‖^2) ≤ C*Y^(9/5:ℝ) := by
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
    (fun p => ‖primarySmallTwistSmoothSum p.1 p.2 q η W Z t‖^2) hY1 hC
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallPartTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primarySmallTwistSmoothSum_factor {a b s u d w q : Eisenstein}
    (hs : primary s) (hu : primary u) (hd : primary d) (hw : primary w)
    (ha : a = s*u) (hb : b = d*w) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (Z t : ℝ) :
    primarySmallTwistSmoothSum a b q η W Z t =
      primarySmallTwistSmoothSum u w ((3*(s*d))*q)
        (productResidueChar (primaryMixedResidueChar s d hs hd) η) W Z t := by
  unfold primarySmallTwistSmoothSum
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

lemma primaryShortSmoothSum_zeta (a b q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (Z t : ℝ) :
    primaryShortSmoothSum idealZeta a b q η W Z t = primarySmallTwistSmoothSum a b q η W Z t := by
  simp only [primaryShortSmoothSum,primarySmallTwistSmoothSum,MvPowerSeries.coeff_apply,
    idealZeta,Complex.ofReal_one,one_mul]

lemma primaryShortSmoothSum_log (a b q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (Z t : ℝ) :
    primaryShortSmoothSum idealLogNorm a b q η W Z t = primarySmallTwistLogSmoothSum a b q η W Z t := by
  unfold primaryShortSmoothSum primarySmallTwistLogSmoothSum
  apply tsum_congr
  intro x
  by_cases hx : primary x
  · simp only [ite_eq_left hx,MvPowerSeries.coeff_apply,idealLogNorm,
      idealExponentOf_norm (primary_ne_zero hx)]
  · simp only [ite_eq_right hx]

lemma primaryShortSmoothSum_moebius {F Z : ℝ} (hFZ : Real.sqrt F < Z)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (hWlow : ∀ x : ℝ, x < 1 → W x = 0) (t : ℝ) :
    primaryShortSmoothSum (shortIdealMoebius F) a b q η W Z t = 0 := by
  have hZ : 0 < Z := (Real.sqrt_nonneg F).trans_lt hFZ
  unfold primaryShortSmoothSum
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallPairParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma small_pair_fiber_smooth_moment (v : Eisenstein) (s : Eisenstein × Eisenstein)
    (S : Finset (Eisenstein × Eisenstein))
    (hs : primary s.1 ∧ primary s.2)
    (hS : ∀ p ∈ S, primary p.1 ∧ primary p.2 ∧ pairSmallParts v p = s)
    {q : Eisenstein} (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) :
    (∑ p ∈ S, ‖primarySmallTwistSmoothSum p.1 p.2 q η W Z t‖^2) =
      ∑ r ∈ S.image (pairOutsideParts v),
        ‖primarySmallTwistSmoothSum r.1 r.2 ((3*(s.1*s.2))*q)
          (productResidueChar (primaryMixedResidueChar s.1 s.2 hs.1 hs.2) η) W Z t‖^2 := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    have hpa : primarySmallPart v p.1 = s.1 := congrArg Prod.fst (hS p hp).2.2
    have hpb : primarySmallPart v p.2 = s.2 := congrArg Prod.snd (hS p hp).2.2
    rw [primarySmallTwistSmoothSum_factor hs.1 (primaryOutsidePart_primary v (hS p hp).1)
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedSmallPartTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem balanced_smalltwist_smooth_fiber_power (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (S : Finset (Eisenstein × Eisenstein)) (k : Eisenstein × Eisenstein)
        (v q : Eisenstein) (η : MulChar (Residues q) ℂ) (Y Z t : ℝ),
      Y₀ ≤ Y → v ≠ 0 → q ≠ 0 → (3:Eisenstein) ∣ v → q ∣ v →
      (∀ e : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) e) = 1) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      9*norm v^2*norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(17/50:ℝ) ∧
        norm p.2 ≤ Y^(17/50:ℝ) ∧ norm v < norm p.1 ∧ pairSmallParts v p = k) →
      (∑ p ∈ S, ‖primarySmallTwistSmoothSum p.1 p.2 q η W Z t‖^2) ≤ C*Y^(11/5:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := balanced_smalltwist_pair_power hpub W hW hpos hsm hGI hGQ
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
    rw [small_pair_fiber_smooth_moment v k S hk
      (fun p hp => ⟨(hS p hp).1.1,(hS p hp).1.2.1,(hS p hp).2.2.2.2⟩)]
    apply hbound (S.image (pairOutsideParts v)) r η' Y Z t hY hr
      (productResidueChar_units _ _ (primaryMixedResidueChar_trivialInfinity hk.1 hk.2) hη)
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

theorem balanced_smalltwist_smooth_partition_power (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (S : Finset (Eisenstein × Eisenstein)) (v q : Eisenstein)
        (η : MulChar (Residues q) ℂ) (Y Z t : ℝ),
      Y₀ ≤ Y → v ≠ 0 → q ≠ 0 → (3:Eisenstein) ∣ v → q ∣ v →
      (∀ e : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) e) = 1) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      9*norm v^2*norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(17/50:ℝ) ∧
        norm p.2 ≤ Y^(17/50:ℝ) ∧ norm v < norm p.1) →
      (∑ p ∈ S, ‖primarySmallTwistSmoothSum p.1 p.2 q η W Z t‖^2) ≤ C*Y^(221/100:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := balanced_smalltwist_smooth_fiber_power hpub W hW hpos hsm hGI hGQ
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
        ‖primarySmallTwistSmoothSum p.1 p.2 q η W Z t‖^2) ≤ C*Y^(11/5:ℝ) := by
    apply hbound _ k v q η Y Z t hY hv hq h3 hqv hη hZY hYZ hsize ht
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact ⟨(hS p hm.1).1,(hS p hm.1).2.1,(hS p hm.1).2.2.1,(hS p hm.1).2.2.2,hm.2⟩
  calc
    _ = ∑ k ∈ S.image (pairSmallParts v), ∑ p ∈ S.filter (fun p => pairSmallParts v p = k),
        ‖primarySmallTwistSmoothSum p.1 p.2 q η W Z t‖^2 :=
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogBalancedSmallParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
 theorem balanced_smalltwist_log_partition_power (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (P : Finset (Eisenstein × Eisenstein)) (v q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (Y Z t : ℝ), Y₀ ≤ Y → v ≠ 0 → q ≠ 0 →
      (3:Eisenstein) ∣ v → q ∣ v →
      (∀ v : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) v) = 1) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      9*norm v^2*norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(17/50:ℝ) ∧
        norm a.2 ≤ Y^(17/50:ℝ) ∧ norm v < norm a.1) →
      (∑ a ∈ P, ‖primarySmallTwistLogSmoothSum a.1 a.2 q η W Z t‖^2) ≤ C*Y^(111/50:ℝ) := by
  obtain ⟨C₁,T₁,hC₁,hT₁,hbound₁⟩ := balanced_smalltwist_smooth_partition_power hpub
    W hW hpos hsm hGI hGQ
  obtain ⟨C₂,T₂,hC₂,hT₂,hbound₂⟩ := balanced_smalltwist_smooth_partition_power hpub
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
      ‖primarySmallTwistLogSmoothSum a.1 a.2 q η W Z t‖^2 ≤
        2*(Real.log Z)^2*‖primarySmallTwistSmoothSum a.1 a.2 q η W Z t‖^2+
        2*‖primarySmallTwistSmoothSum a.1 a.2 q η (logSmoothWeight W) Z t‖^2 := by
    exact primary_log_smooth_sq_le
      (fun x => mixedCubic a.1 a.2 x*η (Ideal.Quotient.mk (modulus q) x)*mellinPhase t (norm x)) W hW hZ0
  calc
    _ ≤ ∑ a ∈ P, (2*(Real.log Z)^2*‖primarySmallTwistSmoothSum a.1 a.2 q η W Z t‖^2+
        2*‖primarySmallTwistSmoothSum a.1 a.2 q η (logSmoothWeight W) Z t‖^2) :=
      Finset.sum_le_sum (fun a _ => hrow a)
    _ = 2*(Real.log Z)^2*(∑ a ∈ P, ‖primarySmallTwistSmoothSum a.1 a.2 q η W Z t‖^2)+
        2*(∑ a ∈ P, ‖primarySmallTwistSmoothSum a.1 a.2 q η (logSmoothWeight W) Z t‖^2) := by
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedFullSmoothFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
 theorem balanced_short_full_smooth_partition_power (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (hWlow : ∀ x : ℝ, x < 1 → W x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (P : Finset (Eisenstein × Eisenstein)) (v q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (A : EisensteinArithmeticFunction) (F Y Z t : ℝ),
      Y₀ ≤ Y → ShortArithmeticFactor F A → F ≤ Y^(1001/1000:ℝ) →
      v ≠ 0 → q ≠ 0 → (3:Eisenstein) ∣ v → q ∣ v →
      (∀ e : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) e) = 1) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      9*norm v^2*norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(17/50:ℝ) ∧
        norm a.2 ≤ Y^(17/50:ℝ) ∧ norm v < norm a.1) →
      (∑ a ∈ P, ‖primaryShortSmoothSum A a.1 a.2 q η W Z t‖^2) ≤ C*Y^(111/50:ℝ) := by
  obtain ⟨C₁,T₁,hC₁,hT₁,hbound₁⟩ := balanced_smalltwist_smooth_partition_power hpub W hW hpos hsm hGI hGQ
  obtain ⟨C₂,T₂,hC₂,hT₂,hbound₂⟩ := balanced_smalltwist_log_partition_power hpub W hW hpos hsm hGI hGQ
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
        rw [primaryShortSmoothSum_moebius hFZ a.1 a.2 q η W hWlow t,norm_zero]
        norm_num
      _ ≤ _ := mul_nonneg (hC₁.trans (le_max_left _ _)) (Real.rpow_nonneg (by linarith) _)
  · simp_rw [primaryShortSmoothSum_zeta]
    apply (hbound₁ P v q η Y Z t
      ((le_max_left T₁ T₂).trans ((le_max_right _ _).trans hY))
      hv hq h3 hqv hη hZY hYZ hsize ht hP).trans
    exact mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
      (Real.rpow_nonneg (by linarith) _) (hC₁.trans (le_max_left _ _))
  · simp_rw [primaryShortSmoothSum_log]
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DominantNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem dominant_balanced_full_factor_neighborhood_oai (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (hWlow : ∀ x : ℝ, x < 1 → W x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (D : ℝ) :
    ∃ K Y₀ : ℝ, 0 ≤ K ∧ 2 ≤ Y₀ ∧
      ∀ (P : Finset (Eisenstein × Eisenstein)) (q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (A : EisensteinArithmeticFunction) (F Y X t : ℝ), Y₀ ≤ Y →
      ShortArithmeticFactor F A → F ≤ D*Y → q ≠ 0 →
      (∀ e : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) e) = 1) →
      norm q ≤ Y^(1/100000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      Y^(9999/10000:ℝ) ≤ X → X ≤ D*Y → (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(17/50:ℝ) ∧
        norm a.2 ≤ Y^(17/50:ℝ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryShortSmoothSum A a.1 a.2 q η W (X/2) t‖^2) ≤ K*Y^(111/50:ℝ) := by
  classical
  obtain ⟨K,T₁,hK,hT₁,hbound⟩ := balanced_short_full_smooth_partition_power hpub W hW hpos hsm hWlow hGI hGQ
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

theorem solution : type_of% @OAI.CubicFirstMoment.dominant_balanced_full_factor_neighborhood_oai := @OAI.CubicFirstMoment.dominant_balanced_full_factor_neighborhood_oai
