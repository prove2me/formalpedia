-- Prove2me | solution 1 for OAI.CubicFirstMoment.patterson_angularCancellation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:42:25.306687+00:00
-- url     : https://prove2.me/submissions/b9839236-3a06-4c16-bbec-0e69026cd6c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_patterson_angularComparison
import Theorems.Thm_OAI_CubicFirstMoment_primitiveAngularHeckeInput_proved
import Theorems.Thm_OAI_CubicFirstMoment_primitive_angular_prime_ideal_estimate

section
-- module Solutions.OAIQ096_CM.CubicGram_Coordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral coordinates and finite norm cutoffs in the Eisenstein subring. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeCutoffSum_eq_sum (f : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum f X = ∑ p ∈ primeCutoff X, f p := by
  unfold primeCutoffSum
  rw [tsum_eq_sum (s := primeCutoff X)]
  · apply Finset.sum_congr rfl
    intro p hp
    simp [mem_primeCutoff.mp hp]
  · intro p hp
    simp only [mem_primeCutoff] at hp
    simp [hp]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Algebra of fixed angular prime moments

The angular weight is the phase of a nonzero Eisenstein integer raised to
an integer power.  These elementary facts ensure that fixed angular
weights preserve absolute values and distribute through finite prime sums.
-/

noncomputable section

open scoped BigOperators

namespace CubicFirstMoment

/-- The scale of the first moment is positive beyond one. -/
theorem firstMomentScale_pos {X : ℝ} (hX : 1 < X) : 0 < firstMomentScale X := by
  unfold firstMomentScale
  exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos hX)

@[simp] theorem primeCutoffSum_add (f g : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => f p + g p) X =
      primeCutoffSum f X + primeCutoffSum g X := by
  simp only [primeCutoffSum_eq_sum, Finset.sum_add_distrib]

@[simp] theorem primeCutoffSum_sub (f g : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => f p - g p) X =
      primeCutoffSum f X - primeCutoffSum g X := by
  simp only [primeCutoffSum_eq_sum, Finset.sum_sub_distrib]

@[simp] theorem primeCutoffSum_const_mul (z : ℂ) (f : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => z * f p) X = z * primeCutoffSum f X := by
  simp only [primeCutoffSum_eq_sum, Finset.mul_sum]

theorem angularPrimeDifference_eq_sub (ℓ : ℤ) (X : ℝ) :
    angularPrimeDifference ℓ X =
      angularPrimeMoment ℓ X - primeCutoffSum (angularPrimeModel ℓ) X := by
  simp only [angularPrimeDifference, angularPrimeMoment, mul_sub, primeCutoffSum_sub]
  rfl

/-- Angular comparison and the model prime-number theorem imply angular
cancellation by subtraction. -/
theorem angularCancellation_of_comparison
    (hcomparison : AngularComparisonStatement)
    (hmodel : ∀ ℓ : ℤ, ℓ ≠ 0 → Asymptotics.IsLittleO Filter.atTop
      (primeCutoffSum (angularPrimeModel ℓ)) firstMomentScale) :
    AngularCancellationStatement := by
  intro ℓ hℓ
  have h := (hcomparison ℓ).add (hmodel ℓ hℓ)
  have heq : (fun X => angularPrimeDifference ℓ X +
      primeCutoffSum (angularPrimeModel ℓ) X) = angularPrimeMoment ℓ := by
    funext X
    rw [angularPrimeDifference_eq_sub, sub_add_cancel]
  change Asymptotics.IsLittleO Filter.atTop (angularPrimeMoment ℓ) firstMomentScale
  change Asymptotics.IsLittleO Filter.atTop
    (fun X => angularPrimeDifference ℓ X + primeCutoffSum (angularPrimeModel ℓ) X)
    firstMomentScale at h
  rwa [heq] at h

end CubicFirstMoment

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

lemma idealExponentNorm_mono {ν κ : EisensteinIdealExponent} (h : ν ≤ κ) :
    idealExponentNorm ν ≤ idealExponentNorm κ := by
  rw [← add_tsub_cancel_of_le h, idealExponentNorm_add]
  exact le_mul_of_one_le_right (idealExponentNorm_pos ν).le (idealExponentNorm_ge_one _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMoebiusBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedPrimeInput
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the published prime input to smooth prime weights

Prime elements of equal norm are collected without identifying conjugate
prime ideals. Complex Abel summation then derives the smooth-weighted
estimate from `CubicPrimeSiegelWalfisz`. The weighted estimate follows by partial summation.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

lemma primeNormCoefficient_cumulative (R t : ℝ) (χ : Eisenstein → ℂ)
    (ht : 0 ≤ t) (htR : t ≤ R) :
    (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, primeNormCoefficient R χ n) = primeCutoffSum χ t := by
  simp only [primeNormCoefficient]
  rw [Finset.sum_comm, primeCutoffSum_eq_sum]
  have he (p : Eisenstein) :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, if n = normNat p then χ p else 0) =
        if norm p ≤ t then χ p else 0 := by
    simp only [Finset.sum_ite_eq', Finset.mem_Icc, Nat.zero_le, true_and]
    simp only [Nat.le_floor_iff ht, normNat_cast]
  simp_rw [he]
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, mem_primeCutoff]
  constructor
  · intro hp
    exact ⟨hp.1.1, hp.2⟩
  · intro hp
    exact ⟨⟨hp.1, hp.2.trans htR⟩, hp.2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeToThreeIdeals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma ResidueCharacterInduces.restriction {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (x : Eisenstein) :
    χ (Ideal.Quotient.mk (modulus q) x) =
      if IsCoprime q x then ψ (Ideal.Quotient.mk (modulus d) x) else 0 := by
  by_cases hx : IsCoprime q x
  · rw [ite_eq_left hx,h.2 x hx]
  · rw [ite_eq_right hx]
    exact MulChar.map_nonunit χ (fun hu => hx (isCoprime_of_residue_isUnit hu))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueIdealCharacters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma induced_residueIdealChar {q d : Eisenstein} (hq : q ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (ν : EisensteinIdealExponent) :
    residueIdealChar q χ ν =
      if ∀ p ∈ (idealExponentOf q).support, ν p = 0 then residueIdealChar d ψ ν else 0 := by
  simpa only [residueIdealChar,ideal_coprime_support hq] using
    h.restriction (idealExponentGenerator ν)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma angularUnitCorrection_primary {x : Eisenstein} (hx : primary x) (ℓ : ℤ) :
    angularUnitCorrection ℓ x = 1 := by
  rw [angularUnitCorrection, ite_eq_left (unit_residue_of_dvd_primary hx (dvd_refl x)),
    primaryNormalize_eq_self hx, div_self (theta_ne_zero (primary_ne_zero hx) ℓ)]

lemma angularUnitCorrection_compensates (ℓ : ℤ) {x : Eisenstein}
    (hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)) :
    angularUnitCorrection ℓ x*theta ℓ x = theta ℓ (primaryNormalize x) := by
  rw [angularUnitCorrection, ite_eq_left hx]
  exact div_mul_cancel₀ _ (theta_ne_zero (ne_zero_of_three_unit hx) ℓ)

lemma ResidueCharacterInduces.angular_units {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) {ℓ : ℤ}
    (hu : AngularUnitCompatible q χ ℓ) : AngularUnitCompatible d ψ ℓ := by
  intro u
  rw [h.2 u (show IsCoprime q (u:Eisenstein) from ⟨0,(u⁻¹:Eisensteinˣ),by simp⟩)]
  exact hu u

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

lemma induced_angularResidueIdealChar {q d : Eisenstein} (hq : q ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    angularResidueIdealChar q χ ℓ ν =
      if ∀ p ∈ (idealExponentOf q).support, ν p = 0 then
        angularResidueIdealChar d ψ ℓ ν else 0 := by
  rw [angularResidueIdealChar, induced_residueIdealChar hq h]
  split <;> simp [angularResidueIdealChar]

lemma primaryAngularMixedChar_primary (ℓ : ℤ) {a b x : Eisenstein}
    (ha : primary a) (hb : primary b) (hx : primary x) :
    primaryAngularMixedChar ℓ a b ha hb (Ideal.Quotient.mk (modulus (3*(a*b))) x) =
      mixedCubic a b x := by
  rw [primaryAngularMixedChar_mk, primaryAngularMixedLift,
    angularUnitCorrection_primary hx, primaryMixedLift_primary hx, one_mul]

lemma primaryAngularMixedChar_compatible (ℓ : ℤ) {a b : Eisenstein}
    (ha : primary a) (hb : primary b) :
    AngularUnitCompatible (3*(a*b)) (primaryAngularMixedChar ℓ a b ha hb) ℓ := by
  intro u
  rw [primaryAngularMixedChar_mk, primaryAngularMixedLift,
    primaryMixedLift_unit ha hb u.isUnit, mul_one]
  exact angularUnitCorrection_compensates ℓ
    (u.isUnit.map (Ideal.Quotient.mk (modulus 3))) |>.trans (by
      rw [primaryNormalize_unit u.isUnit, theta_one])

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelPartialSummation
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The elementary prime model from the ordinary prime ideal theorem

The only number-theoretic hypothesis used here is the ordinary asymptotic
for the number of primary prime elements.  The power-weighted consequence
is derived by Abel summation.
-/

noncomputable section

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace CubicFirstMoment

lemma hasDerivAt_firstMomentScale {X : ℝ} (hX : 1 < X) :
    HasDerivAt firstMomentScale (firstMomentScaleDerivative X) X := by
  have hX₀ : 0 < X := lt_trans zero_lt_one hX
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hp := Real.hasDerivAt_rpow_const (x := X) (p := (5 / 6 : ℝ)) (Or.inl hX₀.ne')
  have hl := Real.hasDerivAt_log hX₀.ne'
  have hm : X ^ (-1 / 6 : ℝ) * X = X ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_add_one hX₀.ne']
    norm_num
  refine (hp.div hl hlog).congr_deriv ?_
  · norm_num only at *
    dsimp [firstMomentScaleDerivative]
    field_simp
    nlinarith [hm]

lemma firstMomentScaleDerivative_continuousOn :
    ContinuousOn firstMomentScaleDerivative (Set.Ioi 1) := by
  intro X hX
  have hX₀ : X ≠ 0 := ne_of_gt (lt_trans zero_lt_one hX)
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  exact (((Real.continuousAt_rpow_const X (-1 / 6) (Or.inl hX₀)).div
    (Real.continuousAt_log hX₀) hlog).mul
      (continuousAt_const.sub (continuousAt_const.div (Real.continuousAt_log hX₀) hlog))).continuousWithinAt

lemma firstMomentScaleDerivative_pos {X : ℝ} (hX₁ : 1 < X) (hX : 2 < Real.log X) :
    0 < firstMomentScaleDerivative X := by
  have hl : 0 < Real.log X := lt_trans (by norm_num) hX
  have hX₀ : 0 < X := lt_trans zero_lt_one hX₁
  have hinv : 1 / Real.log X < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hX
  unfold firstMomentScaleDerivative
  exact mul_pos (div_pos (Real.rpow_pos_of_pos hX₀ _) hl) (by linarith)

lemma tendsto_firstMomentScale : Tendsto firstMomentScale atTop atTop := by
  have h : Tendsto (fun X : ℝ => Real.log X / X ^ (5 / 6 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 6)).tendsto_div_nhds_zero
  have hpos : ∀ᶠ X : ℝ in atTop, 0 < Real.log X / X ^ (5 / 6 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact div_pos (Real.log_pos hX) (Real.rpow_pos_of_pos (lt_trans zero_lt_one hX) _)
  have hright : Tendsto (fun X : ℝ => Real.log X / X ^ (5 / 6 : ℝ))
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨h, hpos⟩
  have hi := hright.inv_tendsto_nhdsGT_zero
  change Tendsto (fun X : ℝ => (Real.log X / X ^ (5 / 6 : ℝ))⁻¹) atTop atTop at hi
  change Tendsto (fun X : ℝ => firstMomentScale X) atTop atTop
  simpa only [inv_div, firstMomentScale] using hi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedAngularHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative fixed-angular Hecke prime estimates

The published input is the degree-two, nonexceptional specialization of
Kaneko--Thorner, *Highly uniform prime number theorems*, Ann. Inst. Fourier
75 (2025), Theorem 1.2, pp. 1904--1905 (restating Iwaniec--Kowalski,
Theorem 5.13), with the zero-free region and completion from Rajan (1998),
Proposition 1 and Section 1. The exponential conductor-dependent error
is retained. Arbitrary logarithmic savings are derived below; they are
not included among the published-input hypotheses.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators

namespace CubicFirstMoment

private lemma eventually_loglog_small (a b ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      a + b * Real.log (Real.log x) ≤ ε * Real.sqrt (Real.log x) := by
  have hlim : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hc : (fun _ : ℝ => a) =o[atTop] (fun x => Real.sqrt (Real.log x)) := by
    apply isLittleO_const_left.mpr
    right
    simpa only [Function.comp_def, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hlim
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
    Real.tendsto_log_atTop
  have hl' : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
      (fun x => Real.sqrt (Real.log x)) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using hl
  have h := (hc.add (hl'.const_mul_left b)).def hε
  filter_upwards [h] with x hx
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hx)

/-- Logarithmic conductor growth makes the published exponential error
smaller than any prescribed logarithmic saving, uniformly in the conductor. -/
lemma heckeExponentialError_logSaving {c K A D : ℝ}
    (hc : 0 < c) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, ∀ Q : ℝ, 1 ≤ Q → Q ≤ K * (Real.log x) ^ A →
      heckeExponentialError c x Q ≤ 16 * x / (Real.log x) ^ D := by
  have hcond := eventually_loglog_small (Real.log K) A 1 zero_lt_one
  have hdecay := eventually_loglog_small 0 (D + 4) (c / 2) (by positivity)
  filter_upwards [hcond, hdecay, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with x hcond hdecay hL hx Q hQ hQmax
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hL₀ : 0 < Real.log x := Real.log_pos hx
  have hQ₀ : 0 < Q := zero_lt_one.trans_le hQ
  have hlogQ₀ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlogQ : Real.log Q ≤ Real.sqrt (Real.log x) := by
    have h := Real.log_le_log hQ₀ hQmax
    rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hL₀ A).ne', Real.log_rpow hL₀] at h
    exact h.trans (by simpa only [one_mul] using hcond)
  have hroot : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hL₀
  have hd : 0 < Real.log Q + Real.sqrt (Real.log x) := by positivity
  have hratio : Real.sqrt (Real.log x) / 2 ≤
      Real.log x / (Real.log Q + Real.sqrt (Real.log x)) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [Real.sq_sqrt hL₀.le]
  have he₁ : Real.exp (-c * Real.log x / (Real.log Q + Real.sqrt (Real.log x))) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = -c * (Real.log x / (Real.log Q + Real.sqrt (Real.log x))) := by ring
      _ ≤ _ := by nlinarith
  have he₂ : Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤
      (Real.log x) ^ (-(D + 4)) := by
    rw [Real.rpow_def_of_pos hL₀]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlogprod : Real.log (x * Q) ≤ 2 * Real.log x := by
    rw [Real.log_mul hx₀.ne' hQ₀.ne']
    have hq := hlogQ.trans (Real.sqrt_le_self_iff.mpr (Or.inr hL))
    linarith
  have hpoly : (Real.log (x * Q)) ^ 4 ≤ 16 * (Real.log x) ^ 4 := by
    calc
      _ ≤ (2 * Real.log x) ^ 4 := by
        gcongr
        exact Real.log_nonneg (by nlinarith)
      _ = _ := by ring
  have hpow : (Real.log x) ^ 4 * (Real.log x) ^ (-(D + 4)) =
      1 / (Real.log x) ^ D := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL₀]
    norm_num
    rw [Real.rpow_neg hL₀.le]
  calc
    heckeExponentialError c x Q ≤
        x * (16 * (Real.log x) ^ 4) * (Real.log x) ^ (-(D + 4)) := by
      unfold heckeExponentialError
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly hx₀.le)
        (he₁.trans he₂) (Real.exp_nonneg _) (by positivity)
    _ = 16 * x / (Real.log x) ^ D := by rw [mul_assoc, mul_assoc, hpow]; ring

/-- The prime-power deletion error is also negligible at every fixed
logarithmic scale. -/
lemma sqrt_logSq_logSaving (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x * (Real.log x) ^ 2 ≤ x / (Real.log x) ^ D := by
  have h := (isLittleO_log_rpow_rpow_atTop (D + 2)
    (by norm_num : (0 : ℝ) < 1 / 2)).def zero_lt_one
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx₁
  have hx₀ : 0 < x := zero_lt_one.trans hx₁
  have hL₀ : 0 < Real.log x := Real.log_pos hx₁
  have hsmall : (Real.log x) ^ (D + 2) ≤ Real.sqrt x := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hL₀.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _), one_mul, Real.sqrt_eq_rpow] using hx
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL₀ D)).mpr
  calc
    _ = Real.sqrt x * (Real.log x) ^ (D + 2) := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hL₀]
      congr 2
      ring
    _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg x)
    _ = x := Real.mul_self_sqrt hx₀.le

lemma angularConductorFactor_ge_one (ℓ : ℤ) : 1 ≤ angularConductorFactor ℓ := by
  unfold angularConductorFactor
  nlinarith [abs_nonneg (ℓ : ℝ)]

lemma angularAnalyticConductor_ge_one (ℓ : ℤ) {q₁ q₂ : Eisenstein}
    (h₁ : Squarefree q₁) (h₂ : Squarefree q₂) :
    1 ≤ angularAnalyticConductor ℓ q₁ q₂ := by
  have hn : 1 ≤ norm (q₁ * q₂) := by
    rw [← normNat_cast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (mul_ne_zero h₁.ne_zero h₂.ne_zero))
  unfold angularAnalyticConductor
  simpa only [one_mul] using mul_le_mul (angularConductorFactor_ge_one ℓ) hn zero_le_one
    (le_trans zero_le_one (angularConductorFactor_ge_one ℓ))

/-- The logarithmic saving is a deduction from the conductor-dependent
published error, uniform in the small-conductor family. -/
theorem fixedAngular_chebyshev_logSaving (hEF : FixedAngularPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (_hA : 0 < A) (_hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ x : ℝ, X₀ ≤ x → ∀ q₁ q₂ : Eisenstein,
        primary q₁ → primary q₂ → Squarefree q₁ → Squarefree q₂ → IsCoprime q₁ q₂ →
        norm (q₁ * q₂) ≤ (Real.log x) ^ A →
        ‖primeChebyshev (angularMixedCubic ℓ q₁ q₂) x‖ ≤ C * x / (Real.log x) ^ D := by
  obtain ⟨B, c, hB, hc, hbound⟩ := hEF ℓ hℓ
  have hK : 0 < angularConductorFactor ℓ := zero_lt_one.trans_le (angularConductorFactor_ge_one ℓ)
  have herr := heckeExponentialError_logSaving (K := angularConductorFactor ℓ)
    (A := A) (D := D) hc hK
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (herr.and (sqrt_logSq_logSaving D))
  refine ⟨17 * B, max X₁ 3, by positivity, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx q₁ q₂ h₁ h₂ hs₁ hs₂ hcop hcon
  have hx₁ : X₁ ≤ x := (le_max_left _ _).trans hx
  have hx₃ : 3 ≤ x := (le_max_right _ _).trans hx
  have he := (hX₁ x hx₁).1 (angularAnalyticConductor ℓ q₁ q₂)
    (angularAnalyticConductor_ge_one ℓ hs₁ hs₂)
    (mul_le_mul_of_nonneg_left hcon hK.le)
  calc
    _ ≤ B * (16 * x / (Real.log x) ^ D + x / (Real.log x) ^ D) :=
      (hbound q₁ q₂ h₁ h₂ hs₁ hs₂ hcop x hx₃).trans
        (mul_le_mul_of_nonneg_left (add_le_add he (hX₁ x hx₁).2) hB.le)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The sharp fixed-angular prime model

The input is the explicit published Hecke prime estimate, not a weighted
prime-model asymptotic.  Partial summation with `x^(-1/6)/log x` derives
the required little-oh at the sharp first-moment scale.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace CubicFirstMoment

lemma fixedAngular_chebyshev_div_tendsto_zero (hEF : FixedAngularPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    Tendsto (fun X => ‖primeChebyshev (theta ℓ) X‖ / X) atTop (𝓝 0) := by
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ :=
    fixedAngular_chebyshev_logSaving hEF ℓ hℓ 1 1 zero_lt_one zero_lt_one
  have hlim : Tendsto (fun X : ℝ => C / Real.log X) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := (tendsto_order.mp hlim).2 ε hε
  filter_upwards [hsmall, eventually_ge_atTop X₀,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with X hsmall hX hlog
  have hX₁ : 1 < X := hX₀.trans_le hX
  have hXpos : 0 < X := zero_lt_one.trans hX₁
  have hc := hbound X hX 1 1 primary_one primary_one
    squarefree_one squarefree_one (isCoprime_one_left)
    (by simpa [norm] using hlog)
  have he : angularMixedCubic ℓ 1 1 = theta ℓ := by
    funext p
    simp [angularMixedCubic, mixedCubic, cubicSymbol_one_lower]
  rw [he] at hc
  have hr : ‖primeChebyshev (theta ℓ) X‖ / X ≤ C / Real.log X := by
    apply (div_le_div_of_nonneg_right hc hXpos.le).trans_eq
    simp only [Real.rpow_one]
    field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (_root_.norm_nonneg _) hXpos.le)]
  exact hr.trans_lt hsmall

lemma hasDerivAt_angularAbelWeight {X : ℝ} (hX : 1 < X) :
    HasDerivAt angularAbelWeight (angularAbelDerivative X) X := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hp := Real.hasDerivAt_rpow_const (x := X) (p := (-1 / 6 : ℝ))
    (Or.inl hXpos.ne')
  have hl := Real.hasDerivAt_log hXpos.ne'
  have hm : X ^ (-1 / 6 : ℝ) = X ^ (-7 / 6 : ℝ) * X := by
    rw [← Real.rpow_add_one hXpos.ne']
    norm_num
  refine (hp.div hl (Real.log_pos hX).ne').congr_deriv ?_
  · norm_num only at *
    dsimp [angularAbelDerivative]
    rw [hm]
    field_simp [(Real.log_pos hX).ne']
    ring

lemma angularAbelDerivative_continuousOn :
    ContinuousOn angularAbelDerivative (Set.Ioi 1) := by
  intro X hX
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  exact (((Real.continuousAt_rpow_const X (-7 / 6) (Or.inl hXpos.ne')).div
    (Real.continuousAt_log hXpos.ne') hlog).neg.mul
    (continuousAt_const.add (continuousAt_const.div
      (Real.continuousAt_log hXpos.ne') hlog))).continuousWithinAt

lemma angularAbel_boundary_ratio (a X : ℝ) (hX : 1 < X) :
    angularAbelWeight X * a / firstMomentScale X = a / X := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hm : X ^ (5 / 6 : ℝ) = X ^ (-1 / 6 : ℝ) * X := by
    rw [← Real.rpow_add_one hXpos.ne']
    norm_num
  unfold angularAbelWeight firstMomentScale
  rw [hm]
  field_simp [(Real.log_pos hX).ne']

lemma angularAbel_integrand_ratio (a X : ℝ) (hX : 1 < X)
    (hlog : 2 < Real.log X) :
    |angularAbelDerivative X| * a / firstMomentScaleDerivative X =
      (a / X) * ((1 / 6 + 1 / Real.log X) / (5 / 6 - 1 / Real.log X)) := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hlogpos : 0 < Real.log X := Real.log_pos hX
  have hderiv : angularAbelDerivative X ≤ 0 := by
    unfold angularAbelDerivative
    have : 0 ≤ 1 / 6 + 1 / Real.log X := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) this
  have hm : X ^ (-1 / 6 : ℝ) = X ^ (-7 / 6 : ℝ) * X := by
    rw [← Real.rpow_add_one hXpos.ne']
    norm_num
  have hi : 1 / Real.log X < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hlog
  have hd : (5 / 6 : ℝ) - 1 / Real.log X ≠ 0 := by linarith
  rw [abs_of_nonpos hderiv]
  unfold angularAbelDerivative firstMomentScaleDerivative
  rw [hm]
  field_simp

/-- The version of scale comparison starting at two, where the logarithmic
Abel weight is regular. Only its limit-zero case is needed. -/
lemma integral_from_two_div_scale_tendsto_zero (f : ℝ → ℝ)
    (hint : ∀ X : ℝ, 2 ≤ X → IntervalIntegrable f volume 2 X)
    (hlim : Tendsto (fun X => f X / firstMomentScaleDerivative X) atTop (𝓝 0)) :
    Tendsto (fun X => (∫ t in 2..X, f t) / firstMomentScale X) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hr := Metric.tendsto_nhds.mp hlim (ε / 2) (by positivity)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_gt_atTop (2 : ℝ))
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    ((hr.and hlog).and (eventually_ge_atTop (2 : ℝ)))
  have hA₂ : 2 ≤ A := (hA A le_rfl).2
  have hA₁ : 1 < A := lt_of_lt_of_le (by norm_num) hA₂
  let C := ∫ t in 2..A, f t
  have hC : Tendsto (fun X => |C| / firstMomentScale X) atTop (𝓝 0) :=
    tendsto_firstMomentScale.const_div_atTop |C|
  have he := (tendsto_order.mp hC).2 (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop A, he] with X hX hsmall
  have hX₂ : 2 ≤ X := hA₂.trans hX
  have hX₁ : 1 < X := hA₁.trans_le hX
  have hsX : 0 < firstMomentScale X := firstMomentScale_pos hX₁
  have hsA : 0 < firstMomentScale A := firstMomentScale_pos hA₁
  have hdint : IntervalIntegrable firstMomentScaleDerivative volume A X := by
    apply ContinuousOn.intervalIntegrable_of_Icc hX
    apply firstMomentScaleDerivative_continuousOn.mono
    intro t ht
    exact hA₁.trans_le ht.1
  have hFTC : (∫ t in A..X, firstMomentScaleDerivative t) =
      firstMomentScale X - firstMomentScale A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hdint
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    exact hasDerivAt_firstMomentScale (hA₁.trans_le ht.1)
  have hfint : IntervalIntegrable f volume A X :=
    (hint A hA₂).symm.trans (hint X hX₂)
  have htail : ‖∫ t in A..X, f t‖ ≤
      ε / 2 * (firstMomentScale X - firstMomentScale A) := by
    have hb : ∀ᵐ t : ℝ, t ∈ Set.Ioc A X →
        ‖f t‖ ≤ ε / 2 * firstMomentScaleDerivative t := by
      apply Filter.Eventually.of_forall
      intro t ht
      have hat := hA t ht.1.le
      have hdt : 0 < firstMomentScaleDerivative t :=
        firstMomentScaleDerivative_pos (lt_of_lt_of_le (by norm_num) hat.2) hat.1.2
      have hclose : |f t / firstMomentScaleDerivative t| < ε / 2 := by
        simpa only [Real.dist_eq, sub_zero] using hat.1.1
      rw [← div_mul_cancel₀ (f t) hdt.ne', norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hdt]
      exact mul_le_mul_of_nonneg_right hclose.le hdt.le
    have hi := intervalIntegral.norm_integral_le_of_norm_le hX hb (hdint.const_mul (ε / 2))
    simpa only [intervalIntegral.integral_const_mul, hFTC] using hi
  have heq : (∫ t in 2..X, f t) = C + ∫ t in A..X, f t := by
    exact (intervalIntegral.integral_add_adjacent_intervals (hint A hA₂) hfint).symm
  have hbound : |∫ t in 2..X, f t| ≤ |C| + ε / 2 * firstMomentScale X := by
    rw [heq]
    calc
      _ ≤ |C| + |∫ t in A..X, f t| := abs_add_le _ _
      _ ≤ |C| + ε / 2 * (firstMomentScale X - firstMomentScale A) := by
        simpa only [Real.norm_eq_abs] using add_le_add (le_refl |C|) htail
      _ ≤ _ := by nlinarith
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hsX]
  calc
    _ ≤ (|C| + ε / 2 * firstMomentScale X) / firstMomentScale X :=
      div_le_div_of_nonneg_right hbound hsX.le
    _ = |C| / firstMomentScale X + ε / 2 := by field_simp
    _ < ε := by linarith

lemma angularChebyshevIntegrand_intervalIntegrable (ℓ : ℤ) {X : ℝ} (hX : 2 ≤ X) :
    IntervalIntegrable (angularChebyshevIntegrand ℓ) volume 2 X := by
  have hd : IntegrableOn (fun t : ℝ => (angularAbelDerivative t : ℂ)) (Set.Icc 2 X) := by
    apply ContinuousOn.integrableOn_Icc
    exact Complex.continuous_ofReal.comp_continuousOn
      (angularAbelDerivative_continuousOn.mono (fun t ht => lt_of_lt_of_le (by norm_num) ht.1))
  have hi := (integrableOn_mul_sum_Icc (m := 0)
    (primeNormCoefficient X (fun p => theta ℓ p * (Real.log (norm p) : ℂ)))
    (by norm_num : (0 : ℝ) ≤ 2) hd).norm
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hX]
  apply IntegrableOn.congr_fun hi _ measurableSet_Icc
  intro t ht
  dsimp only
  rw [primeNormCoefficient_cumulative X t _ (by linarith [ht.1]) ht.2]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, angularChebyshevIntegrand,
    primeChebyshev]

lemma angularChebyshev_integral_div_scale_tendsto_zero
    (hEF : FixedAngularPrimeExplicitEstimate) (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    Tendsto (fun X => (∫ t in 2..X, angularChebyshevIntegrand ℓ t) / firstMomentScale X)
      atTop (𝓝 0) := by
  apply integral_from_two_div_scale_tendsto_zero _
    (fun X hX => angularChebyshevIntegrand_intervalIntegrable ℓ hX)
  have hi : Tendsto (fun X : ℝ => 1 / Real.log X) atTop (𝓝 0) := by
    have h := Real.tendsto_log_atTop.inv_tendsto_atTop
    change Tendsto (fun X : ℝ => (Real.log X)⁻¹) atTop (𝓝 0) at h
    simpa only [one_div] using h
  have hr : Tendsto (fun X => (1 / 6 + 1 / Real.log X) / (5 / 6 - 1 / Real.log X))
      atTop (𝓝 ((1 / 6 + 0 : ℝ) / (5 / 6 - 0))) :=
    (tendsto_const_nhds.add hi).div (tendsto_const_nhds.sub hi)
      (by norm_num : (5 / 6 : ℝ) - 0 ≠ 0)
  have hm := (fixedAngular_chebyshev_div_tendsto_zero hEF ℓ hℓ).mul hr
  norm_num only [zero_mul] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (2 : ℝ))] with X hX hlog
  exact (angularAbel_integrand_ratio _ X hX hlog).symm

private lemma primaryPrime_norm_gt_one {p : Eisenstein} (hp : primaryPrime p) :
    1 < norm p := by
  have hp₀ := normNat_ne_zero hp.2.ne_zero
  have hp₁ : normNat p ≠ 1 := by
    intro h
    apply hp.2.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [← normNat_cast, h, Nat.cast_one]
  rw [← normNat_cast]
  exact_mod_cast (show 1 < normNat p by omega)

private lemma primeNormCoefficient_log (R : ℝ) (χ : Eisenstein → ℂ) (n : ℕ) :
    primeNormCoefficient R (fun p => χ p * (Real.log (norm p) : ℂ)) n =
      primeNormCoefficient R χ n * (Real.log (n : ℝ) : ℂ) := by
  unfold primeNormCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hn : n = normNat p
  · have he : norm p = (n : ℝ) := by rw [← normNat_cast, ← hn]
    simp [hn, he]
  · simp [hn]

private lemma primeNormCoefficient_weighted_prefix (X : ℝ) (f : ℝ → ℂ)
    (χ : Eisenstein → ℂ) (hX : 0 ≤ X) :
    (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, f n * primeNormCoefficient X χ n) =
      ∑ p ∈ primeCutoff X, f (norm p) * χ p := by
  simp only [primeNormCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hpn : normNat p ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX).mpr
    (by rw [normNat_cast]; exact (mem_primeCutoff.mp hp).2)
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_Icc,
    Nat.zero_le, true_and, ite_eq_left hpn, normNat_cast]

lemma angularWeightedPrimeSum_abel (ℓ : ℤ) {X : ℝ} (hX : 2 ≤ X) :
    angularWeightedPrimeSum ℓ X =
      (angularAbelWeight X : ℂ) * primeChebyshev (theta ℓ) X -
        ∫ t in 2..X, (angularAbelDerivative t : ℂ) * primeChebyshev (theta ℓ) t := by
  let χ := fun p => theta ℓ p * (Real.log (norm p) : ℂ)
  let c := primeNormCoefficient X χ
  let f := fun t : ℝ => (angularAbelWeight t : ℂ)
  have hc₀ : c 0 = 0 := by simp [c, χ, primeNormCoefficient_log]
  have hc₁ : c 1 = 0 := by simp [c, χ, primeNormCoefficient_log]
  have hderiv : ∀ t ∈ Set.Icc 2 X, deriv f t = (angularAbelDerivative t : ℂ) := by
    intro t ht
    exact (hasDerivAt_angularAbelWeight (lt_of_lt_of_le (by norm_num) ht.1)).ofReal_comp.deriv
  have hdiff : ∀ t ∈ Set.Icc 2 X, DifferentiableAt ℝ f t := by
    intro t ht
    exact (hasDerivAt_angularAbelWeight
      (lt_of_lt_of_le (by norm_num) ht.1)).ofReal_comp.differentiableAt
  have hint : IntegrableOn (deriv f) (Set.Icc 2 X) := by
    apply IntegrableOn.congr_fun ?_ (fun t ht => (hderiv t ht).symm) measurableSet_Icc
    apply ContinuousOn.integrableOn_Icc
    exact Complex.continuous_ofReal.comp_continuousOn
      (angularAbelDerivative_continuousOn.mono (fun t ht => lt_of_lt_of_le (by norm_num) ht.1))
  have h := sum_mul_eq_sub_integral_mul₁ c hc₀ hc₁ X hdiff hint
  have hleft : (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, f n * c n) = angularWeightedPrimeSum ℓ X := by
    rw [primeNormCoefficient_weighted_prefix X f χ (by linarith)]
    unfold angularWeightedPrimeSum
    rw [primeCutoffSum_eq_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hl : Real.log (norm p) ≠ 0 :=
      (Real.log_pos (primaryPrime_norm_gt_one (mem_primeCutoff.mp hp).1)).ne'
    dsimp [f, χ, angularAbelWeight]
    push_cast
    field_simp [show (Real.log (norm p) : ℂ) ≠ 0 by exact_mod_cast hl]
  rw [hleft, primeNormCoefficient_cumulative X X χ (by linarith) le_rfl,
    ← intervalIntegral.integral_of_le hX] at h
  have hi : (∫ t in 2..X, deriv f t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
      ∫ t in 2..X, (angularAbelDerivative t : ℂ) * primeChebyshev (theta ℓ) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    dsimp only
    rw [hderiv t ht, primeNormCoefficient_cumulative X t χ (by linarith [ht.1]) ht.2]
    rfl
  rw [hi] at h
  exact h

lemma angularWeightedPrimeSum_norm_le (ℓ : ℤ) {X : ℝ} (hX : 2 ≤ X) :
    ‖angularWeightedPrimeSum ℓ X‖ ≤
      angularAbelWeight X * ‖primeChebyshev (theta ℓ) X‖ +
        ∫ t in 2..X, angularChebyshevIntegrand ℓ t := by
  have hW : 0 ≤ angularAbelWeight X := by
    unfold angularAbelWeight
    exact div_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.log_pos (by linarith)).le
  rw [angularWeightedPrimeSum_abel ℓ hX]
  have hi : ‖∫ t in 2..X, (angularAbelDerivative t : ℂ) * primeChebyshev (theta ℓ) t‖ ≤
      ∫ t in 2..X, angularChebyshevIntegrand ℓ t := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, angularChebyshevIntegrand] using
      (intervalIntegral.norm_integral_le_integral_norm
        (f := fun t => (angularAbelDerivative t : ℂ) * primeChebyshev (theta ℓ) t) hX)
  have hb : ‖(angularAbelWeight X : ℂ) * primeChebyshev (theta ℓ) X‖ =
      angularAbelWeight X * ‖primeChebyshev (theta ℓ) X‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW]
  calc
    _ ≤ ‖(angularAbelWeight X : ℂ) * primeChebyshev (theta ℓ) X‖ +
        ‖∫ t in 2..X, (angularAbelDerivative t : ℂ) * primeChebyshev (theta ℓ) t‖ :=
      norm_sub_le _ _
    _ ≤ _ := add_le_add hb.le hi

theorem angularWeightedPrimeSum_isLittleO (hEF : FixedAngularPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    angularWeightedPrimeSum ℓ =o[atTop] firstMomentScale := by
  have hb : Tendsto (fun X => angularAbelWeight X * ‖primeChebyshev (theta ℓ) X‖ /
      firstMomentScale X) atTop (𝓝 0) := by
    apply (fixedAngular_chebyshev_div_tendsto_zero hEF ℓ hℓ).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact (angularAbel_boundary_ratio _ X hX).symm
  have hi := angularChebyshev_integral_div_scale_tendsto_zero hEF ℓ hℓ
  have hsum : Tendsto (fun X =>
      angularAbelWeight X * ‖primeChebyshev (theta ℓ) X‖ / firstMomentScale X +
      (∫ t in 2..X, angularChebyshevIntegrand ℓ t) / firstMomentScale X) atTop (𝓝 0) := by
    simpa only [add_zero] using hb.add hi
  have hratio : Tendsto (fun X => ‖angularWeightedPrimeSum ℓ X‖ / firstMomentScale X)
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall := (tendsto_order.mp hsum).2 ε hε
    filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with X hsmall hX
    have hs : 0 < firstMomentScale X := firstMomentScale_pos (by linarith)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (_root_.norm_nonneg _) hs.le)]
    have hbound := div_le_div_of_nonneg_right (angularWeightedPrimeSum_norm_le ℓ hX) hs.le
    rw [add_div] at hbound
    exact hbound.trans_lt hsmall
  apply IsLittleO.of_norm_left
  apply isLittleO_of_tendsto' _ hratio
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  exact fun hz => False.elim ((firstMomentScale_pos hX).ne' hz)

/-- The sharp nonzero-angular prime model is negligible at the precise
`X^(5/6)/log X` scale, derived from the published explicit Hecke input. -/
theorem angularPrimeModel_isLittleO (hEF : FixedAngularPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    primeCutoffSum (angularPrimeModel ℓ) =o[atTop] firstMomentScale := by
  have h := (angularWeightedPrimeSum_isLittleO hEF ℓ hℓ).const_mul_left (cStar : ℂ)
  refine h.congr' ?_ Filter.EventuallyEq.rfl
  apply Filter.Eventually.of_forall
  intro X
  unfold angularWeightedPrimeSum
  dsimp only
  rw [primeCutoffSum_eq_sum, primeCutoffSum_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [angularPrimeModel, Complex.ofReal_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIdealBall
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite norm ball of prime ideals and the exact reindexing of its
logarithmically weighted sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma mem_primeIdealBall {X : ℝ} {p : EisensteinIdealPrime} :
    p ∈ primeIdealBall X ↔ idealExponentNorm (Finsupp.single p 1) ≤ X := by
  constructor
  · intro hp
    obtain ⟨ν,hν,hpν⟩ := Finset.mem_biUnion.mp hp
    have hle : Finsupp.single p 1 ≤ ν := Finsupp.single_le_iff.mpr
      (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hpν))
    exact (idealExponentNorm_mono hle).trans (mem_fullIdealBall.mp hν)
  · intro hp
    exact Finset.mem_biUnion.mpr ⟨Finsupp.single p 1,mem_fullIdealBall.mpr hp,by simp⟩

lemma primeIdealBall_image (X : ℝ) :
    (primeIdealBall X).image (fun p => Finsupp.single p 1) =
      (fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1) := by
  ext ν
  simp only [Finset.mem_image,mem_primeIdealBall,Finset.mem_filter,mem_fullIdealBall]
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨hp,p,rfl⟩
  · rintro ⟨hν,p,rfl⟩
    exact ⟨p,hν,rfl⟩

lemma idealPrimeChebyshev_eq_sum_primes (χ : EisensteinIdealExponent → ℂ) (X : ℝ) :
    idealPrimeChebyshev χ X = ∑ p ∈ primeIdealBall X,
      (Real.log (idealExponentNorm (Finsupp.single p 1)):ℂ)*χ (Finsupp.single p 1) := by
  unfold idealPrimeChebyshev
  rw [←primeIdealBall_image,Finset.sum_image]
  exact fun _ _ _ _ h => Finsupp.single_left_injective (by norm_num : (1:ℕ) ≠ 0) h

lemma primeIdealLog_nonneg (p : EisensteinIdealPrime) :
    0 ≤ Real.log (idealExponentNorm (Finsupp.single p 1)) :=
  Real.log_nonneg (idealExponentNorm_ge_one _)

lemma idealExponentNorm_primeSet (S : Finset EisensteinIdealPrime) :
    idealExponentNorm (primeSetExponent S) =
      ∏ p ∈ S, idealExponentNorm (Finsupp.single p 1) := by
  induction S using Finset.induction_on with
  | empty => simp [primeSetExponent,idealExponentNorm,idealExponentGenerator]
  | @insert p S hp ih =>
    simp only [primeSetExponent,Finset.sum_insert hp,idealExponentNorm_add,Finset.prod_insert hp] at *
    rw [ih]

lemma primeIdealLog_sum_le (S : Finset EisensteinIdealPrime) (ν : EisensteinIdealExponent)
    (hS : S ⊆ ν.support) :
    (∑ p ∈ S, Real.log (idealExponentNorm (Finsupp.single p 1))) ≤ Real.log (idealExponentNorm ν) := by
  have hle : primeSetExponent S ≤ ν := (primeSetExponent_le_iff S ν).mpr
    (fun p hp => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (hS hp)))
  have hh := Real.log_le_log (idealExponentNorm_pos (primeSetExponent S)) (idealExponentNorm_mono hle)
  rwa [idealExponentNorm_primeSet,Real.log_prod (fun _ _ => (idealExponentNorm_pos _).ne')] at hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact deletion of finitely many Euler factors in prime-ideal sums.
Its logarithmic cost is bounded by the norm of the original modulus. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeIdealRestriction_single (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (p : EisensteinIdealPrime) :
    primeIdealRestriction S χ (Finsupp.single p 1) =
      if p ∈ S then 0 else χ (Finsupp.single p 1) := by
  have he : (∀ q ∈ S, (Finsupp.single p 1 : EisensteinIdealExponent) q=0) ↔ p ∉ S := by
    constructor
    · intro h hp
      have hh := h p hp
      simp at hh
    · intro hp q hq
      have hqp : q ≠ p := fun he => hp (he ▸ hq)
      simp [hqp]
  unfold primeIdealRestriction
  by_cases hp : p ∈ S
  · rw [ite_eq_right (fun h => (he.mp h) hp),ite_eq_left hp]
  · rw [ite_eq_left (he.mpr hp),ite_eq_right hp]

theorem primeIdeal_restriction_error (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (X : ℝ) :
    ‖idealPrimeChebyshev χ X-idealPrimeChebyshev (primeIdealRestriction S χ) X‖ ≤
      ∑ p ∈ S, Real.log (idealExponentNorm (Finsupp.single p 1)) := by
  rw [idealPrimeChebyshev_eq_sum_primes,idealPrimeChebyshev_eq_sum_primes,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ primeIdealBall X, if p ∈ S then
        Real.log (idealExponentNorm (Finsupp.single p 1)) else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p hp
      rw [primeIdealRestriction_single]
      by_cases hmem : p ∈ S
      · simp only [hmem,ite_true, if_true]
        rw [mul_zero,sub_zero,norm_mul,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg (primeIdealLog_nonneg p)]
        exact mul_le_of_le_one_right (primeIdealLog_nonneg p) (hχ _)
      · simp only [hmem,ite_false, if_false,sub_self,norm_zero,le_refl]
    _ = ∑ p ∈ (primeIdealBall X).filter (fun p => p ∈ S),
        Real.log (idealExponentNorm (Finsupp.single p 1)) := by rw [Finset.sum_filter]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (fun p hp => (Finset.mem_filter.mp hp).2) (fun p _ _ => primeIdealLog_nonneg p)

theorem primeIdeal_restriction_norm_cost (ν : EisensteinIdealExponent)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ κ, ‖χ κ‖ ≤ 1) (X : ℝ) :
    ‖idealPrimeChebyshev χ X-idealPrimeChebyshev (primeIdealRestriction ν.support χ) X‖ ≤
      Real.log (idealExponentNorm ν) :=
  (primeIdeal_restriction_error ν.support χ hχ X).trans
    (primeIdealLog_sum_le ν.support ν (Finset.Subset.refl _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIdealPrimaryTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact passage from complete prime ideals to the manuscript's unique
primary prime representatives when the ramified coefficient vanishes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_idealExponent_single {a : Eisenstein} (ha : Prime a) :
    ∃ p : EisensteinIdealPrime, idealExponentOf a=Finsupp.single p 1 := by
  have hcard : (idealExponentOf a).support.card=1 := by
    rw [idealExponentOf_support_card ha.irreducible.squarefree,
      UniqueFactorizationMonoid.card_factors_of_irreducible ha.irreducible]
  obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hcard
  have hone : idealExponentOf a p=1 := by
    have hle := (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha.irreducible.squarefree p
    omega
  exact ⟨p,by rw [he,hone]⟩

lemma prime_idealPrimaryGenerator (p : EisensteinIdealPrime) :
    Prime (idealPrimaryGenerator (Finsupp.single p 1)) := by
  have hp : Prime (idealExponentGenerator (Finsupp.single p 1)) := by
    simpa [idealExponentGenerator,Finsupp.prod_single_index] using
      (idealPrimeRepresentative_irreducible p).prime
  exact (primaryNormalize_associated (idealExponentGenerator (Finsupp.single p 1))).prime_iff.mp hp

lemma primeCutoff_image_idealExponent (X : ℝ) :
    (primeCutoff X).image idealExponentOf =
      ((fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1)).filter
        (fun ν => primary (idealPrimaryGenerator ν)) := by
  ext ν
  simp only [Finset.mem_image,Finset.mem_filter,mem_fullIdealBall]
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨hap,haX⟩ := mem_primeCutoff.mp ha
    refine ⟨⟨?_,prime_idealExponent_single hap.2⟩,?_⟩
    · rwa [idealExponentOf_norm hap.2.ne_zero]
    · rw [idealPrimaryGenerator_at_element hap.1]
      exact hap.1
  · rintro ⟨⟨hN,p,rfl⟩,hp⟩
    refine ⟨idealPrimaryGenerator (Finsupp.single p 1),mem_primeCutoff.mpr ⟨⟨hp,
      prime_idealPrimaryGenerator p⟩,?_⟩,idealExponentOf_primaryGenerator _⟩
    rwa [idealPrimaryGenerator_norm]

theorem idealPrimeChebyshev_primary_sum (χ : EisensteinIdealExponent → ℂ)
    (ψ : Eisenstein → ℂ)
    (hzero : ∀ ν, ¬primary (idealPrimaryGenerator ν) → χ ν=0)
    (hval : ∀ a : Eisenstein, primary a → χ (idealExponentOf a)=ψ a) (X : ℝ) :
    idealPrimeChebyshev χ X=primeChebyshev ψ X := by
  unfold idealPrimeChebyshev
  have he : (∑ ν ∈ (fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1),
      (Real.log (idealExponentNorm ν):ℂ)*χ ν) =
      ∑ ν ∈ ((fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1)).filter
        (fun ν => primary (idealPrimaryGenerator ν)), (Real.log (idealExponentNorm ν):ℂ)*χ ν := by
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ν hν
    by_cases hp : primary (idealPrimaryGenerator ν)
    · rw [ite_eq_left hp]
    · rw [ite_eq_right hp,hzero ν hp,mul_zero]
  rw [he,←primeCutoff_image_idealExponent,Finset.sum_image]
  · unfold primeChebyshev
    rw [primeCutoffSum_eq_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hap := (mem_primeCutoff.mp ha).1
    rw [hval a hap.1,idealExponentOf_norm hap.2.ne_zero]
    ring
  · intro a ha b hb hab
    exact idealExponentOf_inj_primary (mem_primeCutoff.mp ha).1.1
      (mem_primeCutoff.mp hb).1.1 hab

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-ideal Euler-factor restoration and exact primary-prime transfer
for fixed angular characters, retaining the original modulus at three. -/
noncomputable section
namespace CubicFirstMoment

theorem induced_angular_prime_error {q d : Eisenstein} (hq : q ≠ 0) (hd : d ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (ℓ : ℤ) (X : ℝ) :
    ‖idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X-
      idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X‖ ≤ Real.log (norm q) := by
  have he : angularResidueIdealChar q χ ℓ =
      primeIdealRestriction (idealExponentOf q).support (angularResidueIdealChar d ψ ℓ) :=
    funext (induced_angularResidueIdealChar hq h ℓ)
  rw [he,norm_sub_rev]
  have hh := primeIdeal_restriction_norm_cost (idealExponentOf q)
    (angularResidueIdealChar d ψ ℓ) (angularResidueIdealChar_norm_le_one hd ψ ℓ) X
  rwa [idealExponentOf_norm hq] at hh

lemma residueIdealChar_zero_nonprimary {q : Eisenstein} (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ) (ν : EisensteinIdealExponent)
    (hn : ¬primary (idealPrimaryGenerator ν)) : residueIdealChar q χ ν=0 := by
  have hnc : ¬IsCoprime q (idealExponentGenerator ν) := by
    intro hc
    have hcop := (hc.of_isCoprime_of_dvd_left h3).symm
    apply hn
    exact (idealPrimaryGenerator_primary_iff ν).mpr ((idealGenerator_coprime_three_iff ν).mp hcop)
  exact MulChar.map_nonunit χ (fun hu => hnc (isCoprime_of_residue_isUnit hu))

lemma angularResidueIdealChar_zero_nonprimary {q : Eisenstein} (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (ν : EisensteinIdealExponent)
    (hn : ¬primary (idealPrimaryGenerator ν)) : angularResidueIdealChar q χ ℓ ν=0 := by
  rw [angularResidueIdealChar,residueIdealChar_zero_nonprimary h3 χ ν hn,zero_mul]

theorem angular_primeChebyshev_eq_ideal {q : Eisenstein} (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ) (X : ℝ) :
    primeChebyshev (fun p => χ (Ideal.Quotient.mk (modulus q) p)*theta ℓ p) X =
      idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X := by
  symm
  apply idealPrimeChebyshev_primary_sum
  · exact angularResidueIdealChar_zero_nonprimary h3 χ ℓ
  · intro a ha
    exact angularResidueIdealChar_at_element χ hu (primary_ne_zero ha)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckePrimeScales
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete height and conductor scales for the prime contour. -/
noncomputable section
namespace CubicFirstMoment

lemma primeContourDenominator_ge_one {Q X : ℝ} (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    1 ≤ primeContourDenominator Q X := by
  have hroot : 1 ≤ Real.sqrt (Real.log X) := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hX)
  unfold primeContourDenominator
  linarith [Real.log_nonneg hQ]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeSmoothingScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing a cutoff width after its finite derivative order is known.
The same exponential saving absorbs the cutoff cost and the contour tail. -/
noncomputable section
namespace CubicFirstMoment

lemma primeContour_ratio_bounds {Q X : ℝ} (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    0 ≤ Real.log X/primeContourDenominator Q X ∧
    Real.log X/primeContourDenominator Q X ≤ Real.sqrt (Real.log X) ∧
    Real.log X/primeContourDenominator Q X ≤ Real.log X := by
  have hd := primeContourDenominator_ge_one hQ hX
  have hl : 0 ≤ Real.log X := by linarith
  refine ⟨div_nonneg hl (by linarith),?_,div_le_self hl hd⟩
  apply (div_le_iff₀ (by linarith : 0 < primeContourDenominator Q X)).mpr
  have hs := Real.sq_sqrt hl
  have hq := Real.log_nonneg hQ
  unfold primeContourDenominator
  nlinarith [Real.sqrt_nonneg (Real.log X)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeContourOptimization
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary optimization of the actual smoothed prime contour bound.
The cutoff order is fixed before the conductor and the summation length. -/
noncomputable section
namespace CubicFirstMoment

lemma primeLogSize_bounds {Q X : ℝ} (hQ : 1 ≤ Q) (hXp : 0 < X)
    (hX : 1 ≤ Real.log X) :
    1 ≤ Real.log (X*Q) ∧ Real.log X ≤ Real.log (X*Q) ∧
    primeContourDenominator Q X ≤ Real.log (X*Q) := by
  have hq := Real.log_nonneg hQ
  have hs : Real.sqrt (Real.log X) ≤ Real.log X := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by linarith,?_⟩
    nlinarith
  rw [Real.log_mul hXp.ne' (show Q ≠ 0 by linarith)]
  unfold primeContourDenominator
  exact ⟨by linarith,by linarith,by linarith⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDyadicMajorant
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison of the prime contour majorant over the upper half of a
contracting dyadic partition. -/
noncomputable section
namespace CubicFirstMoment

lemma primeDyadic_log_bounds {X t : ℝ} (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (ht : Real.sqrt X ≤ t) (htX : t ≤ X) :
    0 < t ∧ 1 ≤ Real.log t ∧ Real.log X/2 ≤ Real.log t ∧ Real.log t ≤ Real.log X := by
  have htp : 0 < t := (Real.sqrt_pos.mpr hXp).trans_le ht
  have hlo := Real.log_le_log (Real.sqrt_pos.mpr hXp) ht
  rw [Real.log_sqrt hXp.le] at hlo
  exact ⟨htp,by linarith,hlo,Real.log_le_log htp htX⟩

lemma primeDyadic_sqrt_absorption {c Q X t : ℝ} (_hc : 0 ≤ c) (hc1 : c ≤ 1/2)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (ht : Real.sqrt X ≤ t) (htX : t ≤ X) :
    Real.sqrt t ≤ t*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X) := by
  obtain ⟨htp,hlt,hlo,_⟩ := primeDyadic_log_bounds hXp hX ht htX
  have hy := primeContour_ratio_bounds hQ (by linarith : 1 ≤ Real.log X)
  have hh := mul_le_mul_of_nonneg_right hc1 hy.1
  have hs : Real.sqrt t = Real.exp (Real.log t/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos htp]
    congr 1
    ring
  calc
    _ = Real.exp (Real.log t/2) := hs
    _ ≤ Real.exp (Real.log t+-(c/2)*Real.log X/primeContourDenominator Q X) := by
      apply Real.exp_le_exp.mpr
      simp only [div_eq_mul_inv] at *
      nlinarith [hy.2.2]
    _ = _ := by rw [Real.exp_add,Real.exp_log htp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimeEstimateTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite loss in restoring the original modulus is absorbed in
the same explicit prime majorant. No new analytic estimate is needed. -/
noncomputable section
namespace CubicFirstMoment

lemma primeCancellation_log_cost {c Q X : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/4)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X) :
    Real.log Q ≤ primeCancellationWeight c Q X := by
  have hX1 : 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr (show (0:ℝ) ≤ Real.log X by linarith)
    simpa [Real.exp_log hXp] using hh
  have hroot : Real.sqrt X ≤ X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hXp.le,by nlinarith⟩
  have hs := primeDyadic_sqrt_absorption (c := 2*c) (by linarith : 0 ≤ 2*c)
    (by linarith : 2*c ≤ 1/2) hQ hXp hX hroot le_rfl
  rw [show 2*c/2=c by ring] at hs
  have hroot1 : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hXp.le).mpr (by simpa using hX1)
  have hv : 1 ≤ X*Real.exp (-c*Real.log X/primeContourDenominator Q X) := hroot1.trans hs
  have hP := (primeLogSize_bounds hQ hXp (by linarith)).1
  have hq : Real.log Q ≤ Real.log (X*Q) := by
    rw [Real.log_mul hXp.ne' (show Q ≠ 0 by linarith)]
    linarith
  calc
    _ ≤ (Real.log (X*Q))^2 := by nlinarith
    _ ≤ (X*Real.exp (-c*Real.log X/primeContourDenominator Q X))*(Real.log (X*Q))^2 :=
      le_mul_of_one_le_left (sq_nonneg _) hv
    _ = _ := by unfold primeCancellationWeight; ring

theorem primary_angular_prime_bound_of_primitive {q d : Eisenstein}
    (hq : q ≠ 0) (hd : d ≠ 0) (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ) (ψ : MulChar (Residues d) ℂ)
    (hi : ResidueCharacterInduces q d χ ψ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    {B c Q X : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/4) (hQ : 1 ≤ Q)
    (hqQ : norm q ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (hmain : ‖idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X‖ ≤ B*primeCancellationWeight c Q X) :
    ‖primeChebyshev (fun p => χ (Ideal.Quotient.mk (modulus q) p)*theta ℓ p) X‖ ≤
      (B+1)*primeCancellationWeight c Q X := by
  have herr := (induced_angular_prime_error hq hd hi ℓ X).trans
    ((Real.log_le_log (norm_pos_of_ne_zero hq) hqQ).trans (primeCancellation_log_cost hc hc1 hQ hXp hX))
  rw [angular_primeChebyshev_eq_ideal h3 χ ℓ hu]
  calc
    _ = ‖idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X+
        (idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X-
          idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X)‖ := by
      congr 1
      abel
    _ ≤ ‖idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X‖+
        ‖idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X-
          idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X‖ := norm_add_le _ _
    _ ≤ B*primeCancellationWeight c Q X+primeCancellationWeight c Q X := add_le_add hmain herr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConductorComparison
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial conductor cost of a finite Euler correction preserves
the explicit exponential prime error after a fixed change of constants. -/
noncomputable section
namespace CubicFirstMoment

lemma primeCancellation_polynomial_conductor {c Q X : ℝ} (hc : 0 ≤ c)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hL : 1 ≤ Real.log X) :
    primeCancellationWeight c (4*Q^2) X ≤ 25*heckeExponentialError (c/5) X Q := by
  have hQp : 0 < Q := by linarith
  have hR : 1 ≤ 4*Q^2 := by nlinarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlog4 : Real.log (4:ℝ) ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    linarith
  have hlogR : Real.log (4*Q^2) = Real.log 4+2*Real.log Q := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hQp.ne'),Real.log_pow]
    norm_num
  have hd := primeContourDenominator_ge_one hQ hL
  have hdR := primeContourDenominator_ge_one hR hL
  have hden : primeContourDenominator (4*Q^2) X ≤ 5*primeContourDenominator Q X := by
    unfold primeContourDenominator at *
    rw [hlogR]
    nlinarith [Real.sqrt_nonneg (Real.log X)]
  have hratio : Real.log X/(5*primeContourDenominator Q X) ≤
      Real.log X/primeContourDenominator (4*Q^2) X :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) hden
  have he : Real.exp (-c*Real.log X/primeContourDenominator (4*Q^2) X) ≤
      Real.exp (-(c/5)*Real.log X/primeContourDenominator Q X) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hratio hc
    first | (convert neg_le_neg hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((neg_le_neg hh).trans (le_of_eq (by ring)))
  have hP := (primeLogSize_bounds hQ hXp hL).1
  have hPR := (primeLogSize_bounds hR hXp hL).1
  have hlogs : Real.log (X*(4*Q^2)) ≤ 5*Real.log (X*Q) := by
    rw [Real.log_mul hXp.ne' (by positivity),hlogR,Real.log_mul hXp.ne' hQp.ne']
    nlinarith
  have hp2 : (Real.log (X*(4*Q^2)))^2 ≤ 25*(Real.log (X*Q))^4 := by
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log (X*(4*Q^2))) hlogs 2
    have hp : (Real.log (X*Q))^2 ≤ (Real.log (X*Q))^4 := by
      nlinarith [sq_nonneg ((Real.log (X*Q))^2-1)]
    nlinarith only [hh,hp]
  unfold primeCancellationWeight heckeExponentialError primeContourDenominator at *
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hp2 hXp.le) he (Real.exp_pos _).le (by positivity)
  nlinarith only [hh]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeFromPrimitive
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive reduction, finite Euler restoration, and the literal
primary-prime sum with a fixed nonzero angular frequency. -/
noncomputable section
namespace CubicFirstMoment

theorem angular_prime_from_primitive (hpub : PrimitiveAngularHeckeInput) :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ 1 < X0 ∧
    ∀ (q : Eisenstein), q ≠ 0 → (3:Eisenstein) ∣ q →
    ∀ (χ : MulChar (Residues q) ℂ) (ℓ : ℤ), ℓ ≠ 0 → AngularUnitCompatible q χ ℓ →
    ∀ Q : ℝ, 1 ≤ Q → norm q ≤ Q → |(ℓ:ℝ)|+7 ≤ Q →
    ∀ X : ℝ, X0 ≤ X →
      ‖primeChebyshev (fun p => χ (Ideal.Quotient.mk (modulus q) p)*theta ℓ p) X‖ ≤
        B*heckeExponentialError c X Q := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := primitive_angular_prime_ideal_estimate hpub
  let X0 := max Y0 (Real.exp 2)
  refine ⟨25*(B+1),c/5,X0,by positivity,by positivity,hY0.trans_le (le_max_left _ _),?_⟩
  intro q hq h3 χ ℓ hℓ hu Q hQ hqQ hkQ X hX
  obtain ⟨d,ψ,hd,hi,hN,hp⟩ := primitive_residue_conductor_exists hq χ
  have hnd : norm d ≤ norm q := by
    simpa only [normNat_cast] using (Nat.cast_le.mpr hN : (normNat d:ℝ) ≤ (normNat q:ℝ))
  have hdQ : norm d ≤ Q := hnd.trans hqQ
  have hR : 1 ≤ 4*Q^2 := by nlinarith
  have hQR : Q ≤ 4*Q^2 := by nlinarith
  have hNR : 2*norm d*(1+norm d) ≤ 4*Q^2 := by
    calc
      _ ≤ 2*Q*(1+Q) := by gcongr; linarith [norm_nonneg d]
      _ ≤ _ := by nlinarith
  have hm := hbound d hd ψ hp ℓ hℓ (hi.angular_units hu) (4*Q^2) hR hNR
    (hkQ.trans hQR) X ((le_max_left _ _).trans hX)
  have hXe : Real.exp 2 ≤ X := (le_max_right _ _).trans hX
  have hXp : 0 < X := (Real.exp_pos 2).trans_le hXe
  have hL : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) hXe
    rwa [Real.log_exp] at hh
  have hh := primary_angular_prime_bound_of_primitive hq hd h3 χ ψ hi ℓ hu
    hc.le hc1 hR (hqQ.trans hQR) hXp hL hm
  calc
    _ ≤ (B+1)*primeCancellationWeight c (4*Q^2) X := hh
    _ ≤ (B+1)*(25*heckeExponentialError (c/5) X Q) := mul_le_mul_of_nonneg_left
      (primeCancellation_polynomial_conductor hc.le hQ hXp (by linarith)) (by linarith)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeChebyshevTrivial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite-lattice bound covers the bounded initial interval in the
explicit angular prime theorem. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma primeChebyshev_trivial (ψ : Eisenstein → ℂ)
    (hψ : ∀ p, primaryPrime p → ‖ψ p‖ ≤ 1) {X : ℝ} (hX : 1 ≤ X) :
    ‖primeChebyshev ψ X‖ ≤ 18*X*Real.log X := by
  have hsub : primeCutoff X ⊆ nonzeroNormBall X := by
    intro p hp
    exact mem_nonzeroNormBall.mpr ⟨(mem_primeCutoff.mp hp).2,(mem_primeCutoff.mp hp).1.2.ne_zero⟩
  have hcard := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (nonzeroNormBall_card_le (by linarith : 0 ≤ X))
  rw [primeChebyshev,primeCutoffSum_eq_sum]
  calc
    _ ≤ ∑ p ∈ primeCutoff X, ‖ψ p*(Real.log (norm p):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ primeCutoff X, Real.log X := by
      apply Finset.sum_le_sum
      intro p hp
      have hpp := (mem_primeCutoff.mp hp).1
      have hpn : 1 ≤ norm p := one_le_norm hpp.2.ne_zero
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hpn)]
      exact (mul_le_of_le_one_left (Real.log_nonneg hpn) (hψ p hpp)).trans
        (Real.log_le_log (by linarith) (mem_primeCutoff.mp hp).2)
    _ = ((primeCutoff X).card:ℝ)*Real.log X := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.log_nonneg hX)

lemma primeChebyshev_bounded_range (ψ : Eisenstein → ℂ)
    (hψ : ∀ p, primaryPrime p → ‖ψ p‖ ≤ 1) {X Y : ℝ} (hX : 3 ≤ X) (hXY : X ≤ Y) :
    ‖primeChebyshev ψ X‖ ≤ 18*Y*(Real.sqrt X*(Real.log X)^2) := by
  have hXp : 0 < X := by linarith
  have hL : 1 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.le.trans hX)
    simpa only [Real.log_exp] using hh
  have hsqrt : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hXp.le).mpr (by linarith)
  have hlog : Real.log X ≤ Real.sqrt X*(Real.log X)^2 := by
    calc
      _ ≤ (Real.log X)^2 := by nlinarith
      _ ≤ _ := le_mul_of_one_le_left (sq_nonneg _) hsqrt
  calc
    _ ≤ 18*X*Real.log X := primeChebyshev_trivial ψ hψ (by linarith)
    _ ≤ 18*Y*Real.log X := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by nlinarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeExplicit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit angular prime estimate, including the bounded initial
range, derived from primitive Hecke completion. -/
noncomputable section
namespace CubicFirstMoment

theorem angular_prime_explicit_of_primitive (hpub : PrimitiveAngularHeckeInput) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧
    ∀ (q : Eisenstein), q ≠ 0 → (3:Eisenstein) ∣ q →
    ∀ (χ : MulChar (Residues q) ℂ) (ℓ : ℤ), ℓ ≠ 0 → AngularUnitCompatible q χ ℓ →
    ∀ Q : ℝ, 1 ≤ Q → norm q ≤ Q → |(ℓ:ℝ)|+7 ≤ Q →
    ∀ X : ℝ, 3 ≤ X →
      ‖primeChebyshev (fun p => χ (Ideal.Quotient.mk (modulus q) p)*theta ℓ p) X‖ ≤
        B*(heckeExponentialError c X Q+Real.sqrt X*(Real.log X)^2) := by
  obtain ⟨B,c,X0,hB,hc,hX0,hbound⟩ := angular_prime_from_primitive hpub
  refine ⟨B+18*X0,c,by positivity,hc,?_⟩
  intro q hq h3 χ ℓ hℓ hu Q hQ hqQ hkQ X hX
  have hE : 0 ≤ heckeExponentialError c X Q := by unfold heckeExponentialError; positivity
  have hS : 0 ≤ Real.sqrt X*(Real.log X)^2 := by positivity
  by_cases hlarge : X0 ≤ X
  · have hh := hbound q hq h3 χ ℓ hℓ hu Q hQ hqQ hkQ X hlarge
    nlinarith [mul_nonneg (by positivity : 0 ≤ 18*X0) hE,
      mul_nonneg (by positivity : 0 ≤ B+18*X0) hS]
  · have hh := primeChebyshev_bounded_range (fun p => χ (Ideal.Quotient.mk (modulus q) p)*theta ℓ p)
      (fun p hp => by
        rw [norm_mul,norm_theta hp.2.ne_zero ℓ,mul_one]
        exact residueChar_norm_le_one hq χ _) hX (le_of_not_ge hlarge)
    nlinarith [mul_nonneg hB.le hS,mul_nonneg (by positivity : 0 ≤ B+18*X0) hE]

lemma angularConductor_controls (ℓ : ℤ) {v : Eisenstein} (hv : v ≠ 0) :
    norm (3*v) ≤ angularConductorFactor ℓ*norm v ∧
      |(ℓ:ℝ)|+7 ≤ angularConductorFactor ℓ*norm v := by
  have hn := one_le_norm hv
  have hk := abs_nonneg (ℓ:ℝ)
  have hP : 12 ≤ (|(ℓ:ℝ)|/2+3)*(|(ℓ:ℝ)|/2+4) := by nlinarith
  have hheight : |(ℓ:ℝ)|+7 ≤ angularConductorFactor ℓ := by
    unfold angularConductorFactor
    nlinarith
  have hF : 9 ≤ angularConductorFactor ℓ := by unfold angularConductorFactor; nlinarith
  have h3 : norm (3:Eisenstein)=9 := by change Complex.normSq (3:ℂ)=9; norm_num
  constructor
  · rw [norm_mul_eq,h3]
    exact mul_le_mul_of_nonneg_right hF (by linarith)
  · exact hheight.trans (le_mul_of_one_le_right (by linarith) hn)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeInputsProof
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both literal angular prime inputs follow from the published primitive
angular Hecke completion. Their original conductor majorants are preserved. -/
noncomputable section
namespace CubicFirstMoment

theorem fixedAngularPrimeExplicitEstimate_of_primitive (hpub : PrimitiveAngularHeckeInput) :
    FixedAngularPrimeExplicitEstimate := by
  obtain ⟨B,c,hB,hc,hbound⟩ := angular_prime_explicit_of_primitive hpub
  intro ℓ hℓ
  refine ⟨B,c,hB,hc,?_⟩
  intro a b ha hb hsa hsb _hcop X hX
  have hab : a*b ≠ 0 := mul_ne_zero hsa.ne_zero hsb.ne_zero
  have hq : (3:Eisenstein)*(a*b) ≠ 0 := mul_ne_zero (by norm_num) hab
  have hcontrol := angularConductor_controls ℓ hab
  have hh := hbound (3*(a*b)) hq (dvd_mul_right 3 (a*b))
    (primaryAngularMixedChar ℓ a b ha hb) ℓ hℓ (primaryAngularMixedChar_compatible ℓ ha hb)
    (angularAnalyticConductor ℓ a b) (angularAnalyticConductor_ge_one ℓ hsa hsb)
    hcontrol.1 hcontrol.2 X hX
  have he : primeChebyshev (fun p => primaryAngularMixedChar ℓ a b ha hb
      (Ideal.Quotient.mk (modulus (3*(a*b))) p)*theta ℓ p) X =
      primeChebyshev (angularMixedCubic ℓ a b) X := by
    unfold primeChebyshev
    rw [primeCutoffSum_eq_sum,primeCutoffSum_eq_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only
    rw [primaryAngularMixedChar_primary ℓ ha hb (mem_primeCutoff.mp hp).1.1]
    simp only [angularMixedCubic,mul_comm]
  rwa [he] at hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact first moment and both fixed-angular main theorems. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

theorem patterson_angularCancellation_oai : AngularCancellationStatement :=
  angularCancellation_of_comparison patterson_angularComparison
    (angularPrimeModel_isLittleO (fixedAngularPrimeExplicitEstimate_of_primitive primitiveAngularHeckeInput_proved))

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.patterson_angularCancellation_oai := @OAI.CubicFirstMoment.patterson_angularCancellation_oai
