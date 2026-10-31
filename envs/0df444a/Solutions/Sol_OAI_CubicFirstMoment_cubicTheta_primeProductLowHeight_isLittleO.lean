-- Prove2me | solution 1 for OAI.CubicFirstMoment.cubicTheta_primeProductLowHeight_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:31:22.608902+00:00
-- url     : https://prove2.me/submissions/8f040e10-2dff-413a-bb4c-c362c13c9fba

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A022
import Theorems.Thm_OAI_CubicFirstMoment_kummerPrimeSiegelWalfisz_of_primitive
import Theorems.Thm_OAI_CubicFirstMoment_primaryPrimePNT_proved
import Theorems.Thm_OAI_CubicFirstMoment_primeProductLowHeight_angular_isLittleO_actual
import Theorems.Thm_OAI_CubicFirstMoment_primeProductLowHeight_radial_isLittleO_actual
import Theorems.Thm_OAI_CubicFirstMoment_primitiveAngularHeckeInput_proved
import Theorems.Thm_OAI_CubicFirstMoment_primitive_angular_prime_ideal_estimate

section
-- module Solutions.OAIQ096_CM.CubicGram_Coordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveConductor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma angularCorrectionChar_unit (ℓ : ℤ) (u : Eisensteinˣ) :
    angularCorrectionChar ℓ (Ideal.Quotient.mk (modulus 3) u)*theta ℓ u = 1 := by
  rw [angularCorrectionChar_mk,
    angularUnitCorrection_compensates ℓ (u.isUnit.map (Ideal.Quotient.mk (modulus 3))),
    primaryNormalize_unit u.isUnit, theta_one]

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicNumeratorCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularNumeratorCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular numerator character on the original modulus `9*v`.
The finite correction at three is absorbed into this modulus, so its norm
bound remains `81*N(v)`. -/
noncomputable section
namespace CubicFirstMoment

lemma angularNumeratorChar_mk (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (ℓ : ℤ) (x : Eisenstein) :
    angularNumeratorChar hpub v hv ℓ (Ideal.Quotient.mk (modulus (9*v)) x)=
      angularNumeratorLift v ℓ x :=
  angularNumeratorLift_congr hpub hv ℓ (residueRepresentative_spec _ _)

lemma angularNumeratorChar_primary (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (ℓ : ℤ) {x : Eisenstein} (hx : primary x) :
    angularNumeratorChar hpub v hv ℓ (Ideal.Quotient.mk (modulus (9*v)) x)=cubicSymbol x v := by
  rw [angularNumeratorChar_mk,angularNumeratorLift,cubicNumeratorLift_primary v hx,
    angularUnitCorrection_primary hx,mul_one]

lemma angularNumeratorChar_compatible (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (ℓ : ℤ) :
    AngularUnitCompatible (9*v) (angularNumeratorChar hpub v hv ℓ) ℓ := by
  intro u
  rw [angularNumeratorChar_mk,angularNumeratorLift,cubicNumeratorLift_unit v u.isUnit,one_mul]
  simpa only [angularCorrectionChar_mk] using angularCorrectionChar_unit ℓ u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIdealBall
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedAngularHecke
attribute [-instance] _root_.instMeasurableSpace
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

lemma angularConductorFactor_ge_one (ℓ : ℤ) : 1 ≤ angularConductorFactor ℓ := by
  unfold angularConductorFactor
  nlinarith [abs_nonneg (ℓ : ℝ)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIdealPrimaryTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaElementaryGrowth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary bounds used to discharge reciprocal Gamma growth. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma gamma_norm_le_real {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma gamma_norm_le_add_nat {s : ℂ} (hs : 1 ≤ |s.im|) (n : ℕ) :
    ‖Complex.Gamma s‖ ≤ ‖Complex.Gamma (s+n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have him : (s+(n:ℂ)).im = s.im := by simp
    have hn : 1 ≤ ‖s+(n:ℂ)‖ := hs.trans (by simpa using Complex.abs_im_le_norm (s+(n:ℂ)))
    have hne : s+(n:ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hn)
    calc
      _ ≤ ‖Complex.Gamma (s+n)‖ := ih
      _ ≤ ‖s+(n:ℂ)‖*‖Complex.Gamma (s+n)‖ :=
        le_mul_of_one_le_left (_root_.norm_nonneg _) hn
      _ = ‖Complex.Gamma (s+(n+1:ℕ))‖ := by
        rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hne, norm_mul]

lemma complex_sin_norm_le_exp_im (s : ℂ) :
    ‖Complex.sin s‖ ≤ Real.exp |s.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have hp : ‖Complex.exp (-s*Complex.I)‖ ≤ Real.exp |s.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using le_abs_self s.im
  have hm : ‖Complex.exp (s*Complex.I)‖ ≤ Real.exp |s.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using neg_le_abs s.im
  have hd := (norm_sub_le (Complex.exp (-s*Complex.I)) (Complex.exp (s*Complex.I))).trans
    (add_le_add hp hm)
  norm_num
  simp only [neg_mul] at hd
  linarith

lemma gamma_real_interval_bound {a b : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Icc a b, Real.Gamma x ≤ M := by
  have hc : ContinuousOn (fun x : ℝ => Complex.Gamma (x:ℂ)) (Icc a b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply (Complex.continuousAt_Gamma (x:ℂ) ?_).comp Complex.continuous_ofReal.continuousAt
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.ofReal_re,Complex.neg_re,Complex.natCast_re] at hr
    have : (0:ℝ) ≤ n := by positivity
    linarith [hx.1]
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x hx
  exact (Complex.re_le_norm (Complex.Gamma (x:ℂ))).trans ((hM x hx).trans (le_max_left _ _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaInverseGrowth
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal Gamma has the coarse strip growth needed for the completed
Hecke functions. This uses Euler's integral, reflection and recurrence. -/
noncomputable section
open Set
namespace CubicFirstMoment

private lemma gamma_inverse_reflection {s : ℂ} (hs : 1 ≤ |s.im|) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1-s)*Complex.sin (Real.pi*s)/Real.pi := by
  have hi : s.im ≠ 0 := by intro h; simp only [h,abs_zero] at hs; linarith
  have hreg : ∀ n : ℕ, s ≠ -(n:ℂ) := by
    intro n hn
    apply hi
    simpa using congrArg Complex.im hn
  have hreg' : ∀ n : ℕ, 1-s ≠ -(n:ℂ) := by
    intro n hn
    apply hi
    have hh := congrArg Complex.im hn
    simpa using hh
  have hG := Complex.Gamma_ne_zero hreg
  have hG' := Complex.Gamma_ne_zero hreg'
  have hr := Complex.Gamma_mul_Gamma_one_sub s
  have hsin : Complex.sin (Real.pi*s) ≠ 0 := by
    intro hz
    rw [hz,div_zero] at hr
    exact mul_ne_zero hG hG' hr
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr' := (eq_div_iff hsin).mp hr
  apply (eq_div_iff hp).mpr
  calc
    _ = (Complex.Gamma s)⁻¹*(Complex.Gamma s*Complex.Gamma (1-s)*
        Complex.sin (Real.pi*s)) := congrArg (fun z : ℂ => (Complex.Gamma s)⁻¹*z) hr'.symm
    _ = _ := by field_simp [hG]

private lemma gamma_inverse_large_height_bound (a b : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℂ, s.re ∈ Icc a b → 1 ≤ |s.im| →
      ‖(Complex.Gamma s)⁻¹‖ ≤ D*Real.exp (Real.pi*|s.im|) := by
  obtain ⟨n,hn⟩ := exists_nat_gt b
  have hlo : 0 < 1-b+(n:ℝ) := by linarith
  obtain ⟨M,hM,hbound⟩ := gamma_real_interval_bound (b := 1-a+(n:ℝ)) hlo
  refine ⟨M/Real.pi,div_pos hM Real.pi_pos,?_⟩
  intro s hs ht
  have hz : 0 < (1-s+(n:ℂ)).re := by
    simp only [Complex.add_re,Complex.sub_re,Complex.one_re,Complex.natCast_re]
    linarith [hs.2]
  have hΓ : ‖Complex.Gamma (1-s)‖ ≤ M := by
    calc
      _ ≤ ‖Complex.Gamma (1-s+(n:ℂ))‖ := gamma_norm_le_add_nat (by simpa using ht) n
      _ ≤ Real.Gamma (1-s+(n:ℂ)).re := gamma_norm_le_real hz
      _ ≤ M := hbound _ (by
        simp only [mem_Icc,Complex.add_re,Complex.sub_re,Complex.one_re,Complex.natCast_re]
        constructor <;> linarith [hs.1,hs.2])
  have hsin : ‖Complex.sin (Real.pi*s)‖ ≤ Real.exp (Real.pi*|s.im|) := by
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      abs_mul,abs_of_pos Real.pi_pos] using complex_sin_norm_le_exp_im (Real.pi*s)
  rw [gamma_inverse_reflection ht,norm_div,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  exact (div_le_div_of_nonneg_right (mul_le_mul hΓ hsin (_root_.norm_nonneg _) hM.le)
    Real.pi_pos.le).trans_eq (by ring)

/-- The exact reciprocal-Gamma strip input is an elementary theorem. -/
theorem gammaInverseFiniteOrder (a b : ℝ) : GammaInverseFiniteOrder a b := by
  obtain ⟨D,hD,hlarge⟩ := gamma_inverse_large_height_bound a b
  let F : ℝ × ℝ → ℂ := fun p => (Complex.Gamma ((p.1:ℂ)+(p.2:ℂ)*Complex.I))⁻¹
  have hF : Continuous F := by
    simpa only [F,one_div,Function.comp_def] using Complex.differentiable_one_div_Gamma.continuous.comp
      (show Continuous (fun p : ℝ × ℝ => (p.1:ℂ)+(p.2:ℂ)*Complex.I) by fun_prop)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := (Icc a b) ×ˢ (Icc (-1:ℝ) 1)) hF.continuousOn
  let E := max (max C 1) D
  have hE1 : 1 ≤ E := (le_max_right C 1).trans (le_max_left _ _)
  have hE : 0 < E := zero_lt_one.trans_le hE1
  have hlog : 0 ≤ Real.log E := Real.log_nonneg hE1
  refine ⟨Real.log E+Real.pi,add_nonneg hlog Real.pi_pos.le,?_⟩
  intro s hs
  have hb : ‖(Complex.Gamma s)⁻¹‖ ≤ E*Real.exp (Real.pi*|s.im|) := by
    by_cases ht : |s.im| ≤ 1
    · have hc := hC (s.re,s.im) ⟨hs,abs_le.mp ht⟩
      have hc' : ‖(Complex.Gamma s)⁻¹‖ ≤ C := by
        simpa only [F,Complex.re_add_im] using hc
      exact (hc'.trans ((le_max_left C 1).trans (le_max_left _ _))).trans
        (le_mul_of_one_le_right hE.le (Real.one_le_exp (mul_nonneg Real.pi_pos.le (abs_nonneg _))))
    · exact (hlarge s hs (le_of_not_ge ht)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  have hquad1 : 1 ≤ (1+|s.im|)^2 := by nlinarith [abs_nonneg s.im,sq_nonneg |s.im|]
  have hquad2 : |s.im| ≤ (1+|s.im|)^2 := by nlinarith [abs_nonneg s.im,sq_nonneg |s.im|]
  calc
    _ ≤ E*Real.exp (Real.pi*|s.im|) := hb
    _ = Real.exp (Real.log E+Real.pi*|s.im|) := by rw [Real.exp_add,Real.exp_log hE]
    _ ≤ Real.exp ((Real.log E+Real.pi)*(1+|s.im|)^2) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ Real.log E*(1+|s.im|)^2+Real.pi*(1+|s.im|)^2 :=
          add_le_add (by simpa using mul_le_mul_of_nonneg_left hquad1 hlog)
            (mul_le_mul_of_nonneg_left hquad2 Real.pi_pos.le)
        _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeThetaCompletion
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decompletion of the actual theta Mellin transform. These algebraic bridges
will be applied to the primitive residue-character theta series. -/
noncomputable section
namespace CubicFirstMoment

lemma thetaHeckeL_differentiable {A : ℝ} (hA : 0 < A) {Λ : ℂ → ℂ}
    (hΛ : Differentiable ℂ Λ) : Differentiable ℂ (thetaHeckeL A Λ) := by
  let _ : NeZero (A:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hA.ne'⟩
  exact (((differentiable_const_cpow_of_neZero (A:ℂ)).comp differentiable_neg).mul
    Complex.differentiable_one_div_Gamma).mul hΛ

lemma thetaHeckeL_completed {A : ℝ} (hA : 0 < A) (Λ : ℂ → ℂ) (s : ℂ)
    (hs : Complex.Gamma s ≠ 0) :
    heckeCompleted A 0 (thetaHeckeL A Λ) s = Λ s := by
  have hAp : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))
  simp only [heckeCompleted,thetaHeckeL,Complex.ofReal_zero,add_zero,Complex.cpow_neg]
  field_simp

lemma thetaHeckeL_functionalEquation {A : ℝ} (hA : 0 < A)
    (P : WeakFEPair ℂ) (hk : P.k = 1) :
    HeckeFunctionalEquation A 0 P.ε
      (thetaHeckeL A P.Λ) (thetaHeckeL A P.symm.Λ) := by
  intro s hs hdual
  simp only [Complex.ofReal_zero,add_zero] at hs hdual
  rw [thetaHeckeL_completed hA _ _ hs,thetaHeckeL_completed hA _ _ hdual]
  have he := P.functional_equation (1-s)
  simpa only [hk,Complex.ofReal_one,sub_sub_cancel,smul_eq_mul] using he

lemma thetaHeckeL_entire (P : WeakFEPair ℂ) (hP : IsStrongFEPair P)
    {A : ℝ} (hA : 0 < A) :
    Differentiable ℂ (thetaHeckeL A P.Λ) ∧
      Differentiable ℂ (thetaHeckeL A P.symm.Λ) :=
  ⟨thetaHeckeL_differentiable hA hP.differentiable_Λ,
    thetaHeckeL_differentiable hA hP.symm.differentiable_Λ⟩

lemma thetaHeckeL_finiteOrder {A : ℝ} (hA : 0 < A)
    {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : ℂ, ‖Λ s‖ ≤ Real.exp (C*(1+‖s‖)^2)) :
    CompletedHeckeFiniteOrder A (thetaHeckeL A Λ) := by
  exact ⟨Λ,hΛ,(fun s hs => (thetaHeckeL_completed hA Λ s hs).symm),C,hC,hbound⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyLiftedPacking
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local multiplicity of the reduced fractions and all their lattice translates. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxleyLift_actual {q : Eisenstein} (hq : q ≠ 0) {Q : ℝ} (hQ : norm q ≤ Q)
    (x : Residues q) (hx : IsUnit x) (z : Eisenstein) :
    HuxleyLift.reduced Q ⟨q,residueRepresentative q x,z⟩ := by
  refine ⟨hq,hQ,?_,?_⟩
  · exact isCoprime_of_residue_isUnit (by rwa [residueRepresentative_spec])
  · dsimp
    rw [residueRepresentative_spec]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianPacking
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian mass of the separated lifted fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxleyGaussianConstant_pos : 0 < huxleyGaussianConstant := by
  unfold huxleyGaussianConstant
  apply mul_pos (by norm_num)
  have h := huxley_gaussian_weight_summable.le_tsum 0 (fun _ _ => by positivity)
  norm_num at h
  linarith

lemma huxleyLiftGaussian_tsum_bound (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    {t : ℝ} (ht : 0 < t) :
    (∑' i : HuxleyLift, huxleyLiftGaussian Q t z i) ≤
      huxleyGaussianConstant*(1+Q^2/t) := by
  apply Real.tsum_le_of_sum_le
  · intro i
    unfold huxleyLiftGaussian
    split_ifs <;> positivity
  · exact huxleyLiftGaussian_finite_bound Q hQ z ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodized Gaussian rows over the actual finite set of residue fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxleyPeriodizedGaussian_nonneg (t : ℝ) (x : ℂ) :
    0 ≤ huxleyPeriodizedGaussian t x := tsum_nonneg (fun _ => (Real.exp_pos _).le)

lemma huxleyPeriodizedGaussian_neg (t : ℝ) (x : ℂ) :
    huxleyPeriodizedGaussian t (-x) = huxleyPeriodizedGaussian t x := by
  unfold huxleyPeriodizedGaussian
  simp only [sub_neg_eq_add]
  rw [← (Equiv.neg Eisenstein).tsum_eq (fun z : Eisenstein => Real.exp (-t*‖(z:ℂ)+x‖^2))]
  apply tsum_congr
  intro z
  simp only [Equiv.neg_apply]
  have he : ((-z:Eisenstein):ℂ)+x = -((z:ℂ)-x) := by push_cast; ring
  rw [he,norm_neg]

lemma huxleyPeriodizedGaussian_row_bound (Q : ℝ) (hQ : 0 < Q)
    {t : ℝ} (ht : 0 < t) (P : Finset HuxleyLift)
    (hred : ∀ p ∈ P, p.reduced Q) (hzero : ∀ p ∈ P, p.shift = 0) (x : ℂ) :
    (∑ p ∈ P, huxleyPeriodizedGaussian t (x-p.frequency)) ≤
      huxleyGaussianConstant*(1+Q^2/t) := by
  let lift : ({p // p ∈ P} × Eisenstein) → HuxleyLift :=
    fun p => ⟨p.1.val.denominator,p.1.val.numerator,p.2⟩
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Prod.ext
    · apply Subtype.ext
      apply HuxleyLift.ext
      · simpa only [lift] using congrArg HuxleyLift.denominator hab
      · simpa only [lift] using congrArg HuxleyLift.numerator hab
      · exact (hzero _ a.1.property).trans (hzero _ b.1.property).symm
    · exact congrArg HuxleyLift.shift hab
  have hr (p : {p // p ∈ P} × Eisenstein) : (lift p).reduced Q := by
    exact hred p.1.val p.1.property
  have he (p : {p // p ∈ P} × Eisenstein) :
      huxleyLiftGaussian Q t x (lift p) =
        Real.exp (-t*‖(p.2:ℂ)-(x-p.1.val.frequency)‖^2) := by
    rw [huxleyLiftGaussian,ite_eq_left (hr p)]
    have hz : (lift p).frequency-x = (p.2:ℂ)-(x-p.1.val.frequency) := by
      dsimp [lift,HuxleyLift.frequency]
      rw [hzero _ p.1.property]
      push_cast
      ring
    rw [hz]
  have hs := huxleyLiftGaussian_summable Q hQ x ht
  have hc := hs.comp_injective hinj
  change Summable (fun p => huxleyLiftGaussian Q t x (lift p)) at hc
  have hb := hc.tsum_le_tsum_of_inj lift hinj
    (fun i hi => by unfold huxleyLiftGaussian; split_ifs <;> positivity)
    (fun i => le_rfl) hs
  have hex : (∑' p : {p // p ∈ P} × Eisenstein, huxleyLiftGaussian Q t x (lift p)) =
      ∑ p ∈ P, huxleyPeriodizedGaussian t (x-p.frequency) := by
    rw [hc.tsum_prod]
    simp_rw [he]
    rw [tsum_fintype]
    exact Finset.sum_coe_sort P (fun p => huxleyPeriodizedGaussian t (x-p.frequency))
  rw [hex] at hb
  exact hb.trans (huxleyLiftGaussian_tsum_bound Q hQ x ht)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealThetaLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ideal-to-element reindexing for a unit-invariant residue theta series. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma residue_char_unit_mul (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    (x : EisensteinIdealExponent × Eisensteinˣ) :
    χ (Ideal.Quotient.mk (modulus q) (idealElementCoordinates x).val) = residueIdealChar q χ x.1 := by
  change χ (Ideal.Quotient.mk (modulus q) ((x.2:Eisenstein)*idealExponentGenerator x.1)) = _
  rw [map_mul,map_mul,hu,one_mul]
  rfl

lemma idealTheta_lattice {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    (∑' a : {a : Eisenstein // a ≠ 0},
      χ (Ideal.Quotient.mk (modulus q) a.val)*(Real.exp (-norm a.val*t/A):ℝ)) =
      (Nat.card (Eisensteinˣ):ℂ)*idealTheta A (residueIdealChar q χ) t := by
  let : Finite (Eisensteinˣ) := idealTheta_units_finite
  let : Fintype (Eisensteinˣ) := Fintype.ofFinite _
  let f : EisensteinIdealExponent → ℂ := fun ν =>
    residueIdealChar q χ ν*(Real.exp (-idealExponentNorm ν*t/A):ℝ)
  have hf : Summable f := idealTheta_summable hA ht _ (residueIdealChar_norm_le_one hq χ)
  have hprod : Summable (fun x : EisensteinIdealExponent × Eisensteinˣ => f x.1) := by
    simpa only [mul_one] using summable_mul_of_summable_norm
      (g := fun _ : Eisensteinˣ => (1:ℂ)) hf.norm (hasSum_fintype _).summable
  rw [← idealElementCoordinates.tsum_eq]
  have he : (fun x : EisensteinIdealExponent × Eisensteinˣ =>
      χ (Ideal.Quotient.mk (modulus q) (idealElementCoordinates x).val)*
        (Real.exp (-norm (idealElementCoordinates x).val*t/A):ℝ)) = fun x => f x.1 := by
    funext x
    rw [residue_char_unit_mul q χ hu,idealElementCoordinates_norm]
  rw [he,hprod.tsum_prod' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [tsum_mul_left]
  simp only [Nat.card_eq_fintype_card]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueThetaLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete Eisenstein theta sum, including its zero term, equals the
ideal theta sum with its exact unit multiplicity. -/
noncomputable section
namespace CubicFirstMoment

lemma residueLatticeTheta_eq {q : Eisenstein} (hq : q ≠ 0)
    [Nontrivial (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    residueLatticeTheta q χ A t =
      (Nat.card (Eisensteinˣ):ℂ)*idealTheta A (residueIdealChar q χ) t := by
  rw [← idealTheta_lattice hq χ hu hA ht]
  symm
  unfold residueLatticeTheta
  exact tsum_subtype_eq_of_support_subset (s := {a : Eisenstein | a ≠ 0})
    (f := fun a : Eisenstein => χ (Ideal.Quotient.mk (modulus q) a)*(Real.exp (-norm a*t/A):ℝ)) (by
    intro a ha
    by_contra he
    have hz : a = 0 := not_not.mp he
    subst a
    simp only [Function.mem_support,map_zero,MulChar.map_zero,zero_mul,ne_eq,not_true_eq_false] at ha)

lemma residue_nontrivial_of_nonprincipal {q : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (hn : χ ≠ 1) : Nontrivial (Residues q) := by
  obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp hn
  apply nontrivial_of_ne (u : Residues q) 1
  intro he
  apply hu
  rw [he,map_one]

lemma residueTheta_inversion_of_lattice {q : Eisenstein} (hq : q ≠ 0)
    [Nontrivial (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    (hd : ∀ u : Eisensteinˣ, (star χ) (Ideal.Quotient.mk (modulus q) u) = 1)
    {A : ℝ} (hA : 0 < A) {root : ℂ}
    (hFE : ∀ t : ℝ, 0 < t → residueLatticeTheta q χ A (1/t) =
      root*(t:ℂ)*residueLatticeTheta q (star χ) A t) :
    ∀ t : ℝ, 0 < t → idealTheta A (residueIdealChar q χ) (1/t) =
      root*(t:ℂ)*idealTheta A (residueIdealChar q (star χ)) t := by
  intro t ht
  have h := hFE t ht
  rw [residueLatticeTheta_eq hq χ hu hA (one_div_pos.mpr ht),
    residueLatticeTheta_eq hq (star χ) hd hA ht] at h
  apply mul_left_cancel₀ residueTheta_unit_multiplicity_ne_zero
  calc
    _ = root*(t:ℂ)*((Nat.card (Eisensteinˣ):ℂ)*idealTheta A (residueIdealChar q (star χ)) t) := h
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueGaussianPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian specialization of periodic lattice Poisson, retaining the exact
finite Fourier coefficient. Primitivity is only needed when this coefficient
is later evaluated as a Gauss eigenvalue. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma residueGaussian_poisson {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    residueLatticeTheta q χ A t = (2/(Real.sqrt 3*norm q):ℝ) •
      ∑' h : Eisenstein, residueFiniteFourier q χ h *
        ((Real.pi/(t/A):ℝ)*(Real.exp
          (-4*Real.pi^2/(t/A)*Complex.normSq ((h:ℂ)/((q:ℂ)*traceLambda))):ℝ)) := by
  have hp := poisson_eisenstein_periodic q hq (fun v => χ v)
    (radialGaussianSchwartz (t/A) (div_pos ht hA))
  have he : (fun z : Eisenstein => χ (Ideal.Quotient.mk (modulus q) z)*
      radialGaussianSchwartz (t/A) (div_pos ht hA) (z:ℂ)) =
      fun z => χ (Ideal.Quotient.mk (modulus q) z)*(Real.exp (-norm z*t/A):ℝ) := by
    funext z
    rw [radialGaussianSchwartz_apply,eisenstein_norm_eq_sq]
    apply congrArg (fun r : ℝ => χ (Ideal.Quotient.mk (modulus q) z)*(Real.exp r:ℝ))
    change -(t/A)*‖(z:ℂ)‖^2 = -‖(z:ℂ)‖^2*t/A
    ring
  rw [he] at hp
  simpa only [residueLatticeTheta,residueFiniteFourier,radialGaussianSchwartz_traceFourier] using hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueGaussianScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact self-dual normalization of the finite-character Gaussian. -/
noncomputable section
namespace CubicFirstMoment

lemma residueGaussian_selfDual {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) {t : ℝ} (ht : 0 < t) :
    residueLatticeTheta q χ (residueHeckeScale q) t =
      (1/(Real.sqrt (norm q)*t):ℝ) *
        ∑' h : Eisenstein, residueFiniteFourier q χ h *
          (Real.exp (-norm h/(residueHeckeScale q*t)):ℝ) := by
  rw [residueGaussian_poisson hq χ (residueHeckeScale_pos hq) ht]
  simp_rw [residueGaussian_exponent hq ht]
  have he (h : Eisenstein) : residueFiniteFourier q χ h *
      ((Real.pi/(t/residueHeckeScale q):ℝ)*(Real.exp (-norm h/(residueHeckeScale q*t)):ℝ)) =
      (Real.pi/(t/residueHeckeScale q):ℝ)*
        (residueFiniteFourier q χ h*(Real.exp (-norm h/(residueHeckeScale q*t)):ℝ)) := by ring
  simp_rw [he]
  rw [tsum_mul_left,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,
    residueGaussian_prefactor hq ht]

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAngularKummerPrime
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-angular prime estimates for the literal ramified numerator

This is the nonexceptional degree-two specialization of Kaneko--Thorner,
*Highly uniform prime number theorems*, Ann. Inst. Fourier 75 (2025),
Theorem 1.2, pp.1904--1905 (Iwaniec--Kowalski, Theorem 5.13), with the
fixed-type zero-free region of Rajan (1998), Proposition 1 and Section 1.
The finite character is `cubicNumeratorChar` of modulus `9*v`; its
identification on primary elements is proved from
`CubicSupplementaryPeriodicity` in `CubicNumeratorCharacter`.

The analytic conductor majorant is
`3 * N(9*v) * (|ell|/2+3) * (|ell|/2+4)`:
`N(9*v)=81*N(v)`, so its constant is 243. The nonzero angular type
excludes a principal/exceptional-real character. The raw input below
retains the exponential conductor error and the prime-power deletion
term. Logarithmic and weighted estimates are deductions, not inputs.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma angularKummerConductorFactor_ge_one (ℓ : ℤ) :
    1 ≤ angularKummerConductorFactor ℓ := by
  have h := angularConductorFactor_ge_one ℓ
  unfold angularKummerConductorFactor
  linarith

lemma angularKummerAnalyticConductor_ge_one (ℓ : ℤ) {v : Eisenstein}
    (hv : v ≠ 0) : 1 ≤ angularKummerAnalyticConductor ℓ v := by
  have hn : (1:ℝ) ≤ norm v := by
    rw [←normNat_cast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero hv)
  unfold angularKummerAnalyticConductor
  nlinarith [angularKummerConductorFactor_ge_one ℓ]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeInputsProof
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both literal angular prime inputs follow from the published primitive
angular Hecke completion. Their original conductor majorants are preserved. -/
noncomputable section
namespace CubicFirstMoment

theorem angularKummerPrimeExplicitEstimate_of_primitive (hpub : PrimitiveAngularHeckeInput) :
    AngularKummerPrimeExplicitEstimate := by
  obtain ⟨B,c,hB,hc,hbound⟩ := angular_prime_explicit_of_primitive hpub
  intro ℓ hℓ
  refine ⟨B,c,hB,hc,?_⟩
  intro v hv _hnc X hX
  have hq : (9:Eisenstein)*v ≠ 0 := mul_ne_zero (by norm_num) hv
  have hcontrol := angularConductor_controls ℓ (mul_ne_zero (by norm_num : (3:Eisenstein)≠0) hv)
  have heq : angularConductorFactor ℓ*norm ((3:Eisenstein)*v) =
      angularKummerAnalyticConductor ℓ v := by
    have h3 : norm (3:Eisenstein)=9 := by change Complex.normSq (3:ℂ)=9; norm_num
    rw [norm_mul_eq,h3]
    unfold angularKummerAnalyticConductor angularKummerConductorFactor
    ring
  have hmod : (3:Eisenstein)*(3*v)=9*v := by ring
  rw [hmod,heq] at hcontrol
  have hh := hbound (9*v) hq (show (3:Eisenstein) ∣ 9*v from ⟨3*v,by ring⟩)
    (angularNumeratorChar cubicSupplementaryPeriodicity_proved v hv ℓ) ℓ hℓ
    (angularNumeratorChar_compatible cubicSupplementaryPeriodicity_proved v hv ℓ)
    (angularKummerAnalyticConductor ℓ v) (angularKummerAnalyticConductor_ge_one ℓ hv)
    hcontrol.1 hcontrol.2 X hX
  have he : primeChebyshev (fun p => angularNumeratorChar cubicSupplementaryPeriodicity_proved v hv ℓ
      (Ideal.Quotient.mk (modulus (9*v)) p)*theta ℓ p) X =
      primeChebyshev (angularKummerCharacter ℓ v) X := by
    unfold primeChebyshev
    rw [primeCutoffSum_eq_sum,primeCutoffSum_eq_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only
    rw [angularNumeratorChar_primary cubicSupplementaryPeriodicity_proved v hv ℓ (mem_primeCutoff.mp hp).1.1]
    simp only [angularKummerCharacter,mul_comm]
  rwa [he] at hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaBetaComparison
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Beta-integral comparison for the Gamma quotient. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

private lemma beta_real_integral_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ in (0:ℝ)..1, t^(x-1)*(1-t)^(y-1)) =
      Real.Gamma x*Real.Gamma y/Real.Gamma (x+y) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (∫ t : ℝ in (0:ℝ)..1, ((t^(x-1)*(1-t)^(y-1):ℝ):ℂ)) =
      Complex.betaIntegral (x:ℂ) (y:ℂ) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    simp only [Complex.ofReal_mul,Complex.ofReal_cpow ht.1,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2),Complex.ofReal_sub,Complex.ofReal_one]
  rw [he,Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hx) (by simpa using hy)]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,← Complex.ofReal_add,Complex.Gamma_ofReal]

lemma beta_norm_le_real (s : ℂ) {d : ℝ} (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.betaIntegral s (d:ℂ)‖ ≤
      Real.Gamma s.re*Real.Gamma d/Real.Gamma (s.re+d) := by
  rw [← beta_real_integral_eq s.re d hs hd]
  unfold Complex.betaIntegral
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)).trans_eq
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  have hp : 0 < 1-t := sub_pos.mpr ht.2
  rw [show (1:ℂ)-(t:ℂ) = ((1-t:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp

lemma gamma_real_shift_ratio_bound (s : ℂ) {d : ℝ} (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.Gamma s‖/‖Complex.Gamma (s+(d:ℂ))‖ ≤
      Real.Gamma s.re/Real.Gamma (s.re+d) := by
  have h := beta_norm_le_real s hs hd
  have hg : 0 < Real.Gamma d := Real.Gamma_pos_of_pos hd
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hs (by simpa using hd),
    norm_div,norm_mul,Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hg] at h
  apply (mul_le_mul_iff_right₀ hg).mp
  first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

lemma gamma_shift_ratio_bound (x y t : ℝ) (n : ℕ) (hx : 0 < x)
    (hgap : 0 < y+(n:ℝ)-x) :
    ‖Complex.Gamma ((x:ℂ)+(t:ℂ)*Complex.I) /
      Complex.Gamma ((y:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (Real.Gamma x/Real.Gamma (y+n))*
        ‖(ascPochhammer ℂ n).eval ((y:ℂ)+(t:ℂ)*Complex.I)‖ := by
  let z : ℂ := (y:ℂ)+(t:ℂ)*Complex.I
  let w : ℂ := (x:ℂ)+(t:ℂ)*Complex.I
  have hyn : 0 < y+(n:ℝ) := by linarith
  have hGn : Complex.Gamma (z+n) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa [z] using hyn)
  by_cases hG : Complex.Gamma z = 0
  · change ‖Complex.Gamma w/Complex.Gamma z‖ ≤ _
    rw [hG,div_zero,norm_zero]
    exact mul_nonneg (div_nonneg (Real.Gamma_pos_of_pos hx).le
      (Real.Gamma_pos_of_pos hyn).le) (_root_.norm_nonneg _)
  have hreg : ∀ k : ℕ, z ≠ -(k:ℂ) := by
    intro k hk
    exact hG (by rw [hk,Complex.Gamma_neg_nat_eq_zero])
  have hp := congrArg (fun u : ℂ => ‖u‖) (Complex.Gamma_add_nat_div_Gamma_eq (n := n) z hreg)
  rw [norm_div] at hp
  have hshift : w+((y+(n:ℝ)-x:ℝ):ℂ) = z+n := by dsimp [w,z]; push_cast; ring
  have hb := gamma_real_shift_ratio_bound w (by simpa [w] using hx) hgap
  rw [hshift,show w.re=x by simp [w],show x+(y+(n:ℝ)-x)=y+n by ring] at hb
  change ‖Complex.Gamma w/Complex.Gamma z‖ ≤ _
  rw [norm_div]
  calc
    _ = (‖Complex.Gamma w‖/‖Complex.Gamma (z+n)‖)*
        ‖(ascPochhammer ℂ n).eval z‖ := by
      rw [← hp]
      field_simp [norm_ne_zero_iff.mpr hG,norm_ne_zero_iff.mpr hGn]
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (_root_.norm_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaQuotientGrowth
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded-strip Gamma quotient follows from the Beta integral and
integer recurrence, with the fixed angular shift retained. -/
noncomputable section
open Set
namespace CubicFirstMoment

private lemma pochhammer_norm_bound (n : ℕ) (z : ℂ) :
    ‖(ascPochhammer ℂ n).eval z‖ ≤ (‖z‖+(n:ℝ))^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,norm_mul]
    have hn : ‖z+(n:ℂ)‖ ≤ ‖z‖+(n:ℝ) := by simpa using norm_add_le z (n:ℂ)
    calc
      _ ≤ (‖z‖+(n:ℝ))^n*(‖z‖+(n:ℝ)) :=
        mul_le_mul ih hn (_root_.norm_nonneg _) (by positivity)
      _ = (‖z‖+(n:ℝ))^(n+1) := (pow_succ _ _).symm
      _ ≤ (‖z‖+((n+1:ℕ):ℝ))^(n+1) := by
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        linarith

private lemma gamma_positive_ratio_compact {a k : ℝ} (hk : -(1/2:ℝ) < k)
    (n : ℕ) (hn : 1-2*a < (n:ℝ)) :
    ∃ M : ℝ, 0 < M ∧ ∀ σ ∈ Icc a (1/2:ℝ),
      Real.Gamma (1-σ+k)/Real.Gamma (σ+k+n) ≤ M := by
  let F : ℝ → ℂ := fun σ => Complex.Gamma ((1-σ+k:ℝ):ℂ)/
    Complex.Gamma ((σ+k+n:ℝ):ℂ)
  have hx {σ : ℝ} (hσ : σ ∈ Icc a (1/2:ℝ)) : 0 < 1-σ+k := by linarith [hσ.2]
  have hy {σ : ℝ} (hσ : σ ∈ Icc a (1/2:ℝ)) : 0 < σ+k+n := by linarith [hσ.1,hσ.2]
  have hc : ContinuousOn F (Icc a (1/2:ℝ)) := by
    intro σ hσ
    have hreg {x : ℝ} (hp : 0 < x) : ∀ m : ℕ, (x:ℂ) ≠ -(m:ℂ) := by
      intro m hm
      have hr := congrArg Complex.re hm
      simp only [Complex.ofReal_re,Complex.neg_re,Complex.natCast_re] at hr
      have : (0:ℝ) ≤ m := by positivity
      linarith
    apply ContinuousAt.continuousWithinAt
    have ht : ContinuousAt (fun τ : ℝ => Complex.Gamma ((1-τ+k:ℝ):ℂ)) σ :=
      (Complex.continuousAt_Gamma _ (hreg (hx hσ))).comp
        (f := fun τ : ℝ => ((1-τ+k:ℝ):ℂ)) (by fun_prop)
    have hb : ContinuousAt (fun τ : ℝ => Complex.Gamma ((τ+k+n:ℝ):ℂ)) σ :=
      (Complex.continuousAt_Gamma _ (hreg (hy hσ))).comp
        (f := fun τ : ℝ => ((τ+k+n:ℝ):ℂ)) (by fun_prop)
    exact ht.div hb
      (Complex.Gamma_ne_zero_of_re_pos (s := ((σ+k+n:ℝ):ℂ)) (by simpa using hy hσ))
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro σ hσ
  have he : ‖F σ‖ = Real.Gamma (1-σ+k)/Real.Gamma (σ+k+n) := by
    dsimp [F]
    rw [norm_div,Complex.Gamma_ofReal,Complex.Gamma_ofReal,Complex.norm_real,
      Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos (hx hσ)),abs_of_pos (Real.Gamma_pos_of_pos (hy hσ))]
  rw [← he]
  exact (hM σ hσ).trans (le_max_left _ _)

/-- The exact fixed-angular quotient input used by the conditional proof. -/
theorem angularGammaQuotientStripBound_proved (k a : ℝ) (hk : -(1/2:ℝ) < k) :
    AngularGammaQuotientStripBound k a := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1-2*a)
  obtain ⟨M,hM,hbound⟩ := gamma_positive_ratio_compact hk n hn
  let D := |a+k|+|(1/2:ℝ)+k|+(n:ℝ)+1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨M*D^n,n,mul_nonneg hM.le (pow_nonneg hD.le _),?_⟩
  intro σ hσ t
  have hx : 0 < 1-σ+k := by linarith [hσ.2]
  have hgap : 0 < (σ+k)+(n:ℝ)-(1-σ+k) := by linarith [hσ.1]
  have hb := gamma_shift_ratio_bound (1-σ+k) (σ+k) t n hx hgap
  have hnum : 1-((σ:ℂ)+(t:ℂ)*Complex.I)+(k:ℂ) =
      starRingEnd ℂ (((1-σ+k:ℝ):ℂ)+(t:ℂ)*Complex.I) := by
    apply Complex.ext <;> simp
  have hden : (σ:ℂ)+(t:ℂ)*Complex.I+(k:ℂ) =
      ((σ+k:ℝ):ℂ)+(t:ℂ)*Complex.I := by push_cast; ring
  have ha : |σ+k| ≤ |a+k|+|(1/2:ℝ)+k| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (a+k),abs_nonneg ((1/2:ℝ)+k),hσ.1]
    · linarith [le_abs_self ((1/2:ℝ)+k),abs_nonneg (a+k),hσ.2]
  have hz : ‖((σ+k:ℝ):ℂ)+(t:ℂ)*Complex.I‖ ≤ |σ+k|+|t| := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,norm_mul,Complex.norm_I,mul_one]
      using norm_add_le (((σ+k:ℝ):ℂ)) ((t:ℂ)*Complex.I)
  have hpoly : ‖(ascPochhammer ℂ n).eval (((σ+k:ℝ):ℂ)+(t:ℂ)*Complex.I)‖ ≤
      D^n*(1+|t|)^n := by
    apply (pochhammer_norm_bound _ _).trans
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hD1 : 1 ≤ D := by
      dsimp [D]
      linarith [abs_nonneg (a+k),abs_nonneg ((1/2:ℝ)+k),show (0:ℝ) ≤ n by positivity]
    dsimp [D] at *
    nlinarith [abs_nonneg t,abs_nonneg (a+k),abs_nonneg ((1/2:ℝ)+k),
      show (0:ℝ) ≤ n by positivity]
  unfold angularGammaFEQuotient
  rw [hnum,hden,Complex.Gamma_conj,norm_div,Complex.norm_conj]
  rw [norm_div] at hb
  apply hb.trans
  calc
    _ ≤ M*(D^n*(1+|t|)^n) :=
      mul_le_mul (hbound σ hσ) hpoly (_root_.norm_nonneg _) hM.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The additive sieve phase as the standard Fourier character of the trace lattice. -/
noncomputable section
namespace CubicFirstMoment

lemma huxleyPhase_eq_traceFourierChar (q h n : Eisenstein) :
    huxleyPhase q h n = (Real.fourierChar
      (tracePair (n:ℂ) ((h:ℂ)/(traceLambda*(q:ℂ)))):ℂ) := by
  unfold huxleyPhase tracePair
  rw [Real.fourierChar_apply]
  have he : (n:ℂ)*(h:ℂ)/(traceLambda*(q:ℂ)) =
      (n:ℂ)*((h:ℂ)/(traceLambda*(q:ℂ))) := by ring
  rw [he]
  have hc (z : ℂ) : z+star z = ((2*z.re:ℝ):ℂ) := by
    apply Complex.ext <;> simp [two_mul]
  dsimp only
  rw [hc]
  push_cast
  congr 1
  ring

lemma huxleyPhase_eq_frequency (q h n : Eisenstein) :
    huxleyPhase q h n = huxleyFrequencyPhase ((h:ℂ)/(q:ℂ)) n := by
  rw [huxleyPhase_eq_traceFourierChar]
  unfold huxleyFrequencyPhase
  rw [show (h:ℂ)/(traceLambda*(q:ℂ)) = ((h:ℂ)/(q:ℂ))/traceLambda by ring]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyCoordinateGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinates for the Gaussian majorant in the additive large sieve. -/
noncomputable section
namespace CubicFirstMoment

lemma huxley_frequency_coordinates (x : ℂ) (a b : ℤ) :
    tracePair (ofCoords a b : ℂ) (x/traceLambda) =
      (a:ℝ)*huxleyXi₀ x+(b:ℝ)*huxleyXi₁ x := by
  have hs : Real.sqrt (3:ℝ) ≠ 0 := by positivity
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  rw [traceLambda_eq]
  simp only [tracePair,ofCoords_coe,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.intCast_re,Complex.intCast_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    omega_re,omega_im,Complex.div_re,Complex.div_im,Complex.normSq_apply,
    huxleyXi₀,huxleyXi₁]
  field_simp
  nlinarith

lemma huxley_frequency_phase_coordinates (x : ℂ) (a b : ℤ) :
    huxleyFrequencyPhase x (ofCoords a b) =
      Complex.exp (((2*Real.pi*(a:ℝ)*huxleyXi₀ x:ℝ):ℂ)*Complex.I)*
      Complex.exp (((2*Real.pi*(b:ℝ)*huxleyXi₁ x:ℝ):ℂ)*Complex.I) := by
  unfold huxleyFrequencyPhase
  rw [huxley_frequency_coordinates,Real.fourierChar_apply,← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma huxley_dual_coordinate_distance (x : ℂ) (m n : ℤ) :
    ‖(ofCoords (m+n) m : ℂ)-x‖^2 ≤
      (3/2:ℝ)*(((m:ℝ)-huxleyXi₀ x)^2+((n:ℝ)-huxleyXi₁ x)^2) := by
  have hs : Real.sqrt (3:ℝ) ≠ 0 := by positivity
  let u := (m:ℝ)-huxleyXi₀ x
  let v := (n:ℝ)-huxleyXi₁ x
  have hd : (ofCoords (m+n) m : ℂ)-x = ((u+v:ℝ):ℂ)+(u:ℂ)*omega := by
    apply Complex.ext <;>
      simp [ofCoords_coe,u,v,huxleyXi₀,huxleyXi₁,Complex.mul_re,Complex.mul_im] <;>
      field_simp
    all_goals ring
  rw [← Complex.normSq_eq_norm_sq]
  rw [hd,real_coordinates_norm]
  change (u+v)^2-(u+v)*u+u^2 ≤ (3/2:ℝ)*(u^2+v^2)
  nlinarith [sq_nonneg (u-v)]

lemma huxley_coordinate_energy (a b : ℤ) :
    (a:ℝ)^2+(b:ℝ)^2 ≤ 2*norm (ofCoords a b) := by
  rw [norm,ofCoords_coe,coordinates_norm]
  push_cast
  nlinarith [sq_nonneg ((a:ℝ)-(b:ℝ))]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyDuality
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Hilbert-space duality for the two sums in the additive large sieve. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_additive_sieve_duality {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (A : ι → κ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hdual : ∀ b : ι → ℂ,
      (∑ n ∈ N, ‖∑ p ∈ P, b p*A p n‖^2) ≤ B*∑ p ∈ P, ‖b p‖^2)
    (v : κ → ℂ) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n*A p n‖^2) ≤ B*∑ n ∈ N, ‖v n‖^2 := by
  let F := fun p => ∑ n ∈ N, v n*A p n
  let S : ℝ := ∑ p ∈ P, ‖F p‖^2
  let T := fun n => ∑ p ∈ P, star (F p)*A p n
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE : 0 ≤ ∑ n ∈ N, ‖v n‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (S:ℂ) = ∑ n ∈ N, v n*T n := by
    calc
      (S:ℂ) = ∑ p ∈ P, F p*star (F p) := by
        simp only [S,Complex.ofReal_sum,Complex.ofReal_pow]
        apply Finset.sum_congr rfl
        intro p hp
        exact (Complex.mul_conj' (F p)).symm
      _ = ∑ p ∈ P, ∑ n ∈ N, v n*A p n*star (F p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_mul N (fun n => v n*A p n) (star (F p))
      _ = ∑ n ∈ N, v n*T n := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro n hn
        dsimp only [T]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hnorm : S ≤ ∑ n ∈ N, ‖v n‖*‖T n‖ := by
    calc
      S = ‖(S:ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hS]
      _ ≤ _ := by
        rw [he]
        simpa only [norm_mul] using norm_sum_le N (fun n => v n*T n)
  have hc : S^2 ≤ (∑ n ∈ N, ‖v n‖^2)*(∑ n ∈ N, ‖T n‖^2) := by
    exact ((sq_le_sq₀ hS (Finset.sum_nonneg (fun _ _ => mul_nonneg
      (_root_.norm_nonneg _) (_root_.norm_nonneg _)))).mpr hnorm).trans
      (Finset.sum_mul_sq_le_sq_mul_sq N (fun n => ‖v n‖) (fun n => ‖T n‖))
  have hd : (∑ n ∈ N, ‖T n‖^2) ≤ B*S := by
    simpa only [T,S,norm_star] using hdual (fun p => star (F p))
  have hsquare : S*S ≤ (B*(∑ n ∈ N, ‖v n‖^2))*S := by
    calc
      S*S = S^2 := (pow_two _).symm
      _ ≤ _ := hc.trans (mul_le_mul_of_nonneg_left hd hE)
      _ = _ := by ring
  change S ≤ _
  by_cases hzero : S = 0
  · rw [hzero]
    exact mul_nonneg hB hE
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne hS (Ne.symm hzero))).mp hsquare

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianPoisson
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One-dimensional Gaussian Poisson identities for the coordinate majorant. -/
noncomputable section
open Filter Asymptotics MeasureTheory
namespace CubicFirstMoment

lemma summable_integer_quadratic_exp (A B C : ℂ) (hA : A.re < 0) :
    Summable (fun n : ℤ => Complex.exp (A*(n:ℂ)^2+B*(n:ℂ)+C)) := by
  have hdec := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact hA B (-2)).isBigO
  have hs := summable_of_isBigO (Real.summable_abs_int_rpow (show (1:ℝ) < 2 by norm_num))
    (hdec.comp_tendsto Int.tendsto_coe_cofinite)
  have hm := hs.mul_right (Complex.exp C)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  simp only [Function.comp_apply,Complex.ofReal_intCast,← Complex.exp_add]

lemma gaussian_coordinate_poisson {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    (∑' n : ℤ, Complex.exp ((-Real.pi*a*(n:ℝ)^2:ℝ):ℂ)*
      Complex.exp (((2*Real.pi*ξ*(n:ℝ):ℝ):ℂ)*Complex.I)) =
    ((1/Real.sqrt a:ℝ):ℂ)*(∑' m : ℤ,
      Complex.exp ((-Real.pi/a*((m:ℝ)-ξ)^2:ℝ):ℂ)) := by
  have hp : 1/(a:ℂ)^(1/2:ℂ) = ((1/Real.sqrt a:ℝ):ℂ) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,
      ← Complex.ofReal_cpow ha.le,← Real.sqrt_eq_rpow,
      Complex.ofReal_div,Complex.ofReal_one]
  calc
    _ = ∑' n : ℤ, Complex.exp (-(Real.pi:ℂ)*(a:ℂ)*(n:ℂ)^2+
        2*(Real.pi:ℂ)*(Complex.I*(ξ:ℂ))*(n:ℂ)) := by
      apply tsum_congr
      intro n
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = _ := by
      rw [Complex.tsum_exp_neg_quadratic (a := (a:ℂ)) (by simpa using ha),hp]
      congr 1
      apply tsum_congr
      intro m
      congr 1
      push_cast
      ring_nf
      norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianCoordinates
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence and the two-coordinate theta identity. -/
noncomputable section
namespace CubicFirstMoment

lemma summable_real_gaussian_shift {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    Summable (fun n : ℤ => Real.exp (-Real.pi*a*((n:ℝ)-ξ)^2)) := by
  have h := summable_integer_quadratic_exp
    ((-Real.pi*a:ℝ):ℂ) ((2*Real.pi*a*ξ:ℝ):ℂ) ((-Real.pi*a*ξ^2:ℝ):ℂ)
    (by simp only [Complex.ofReal_re]; exact mul_neg_of_neg_of_pos (by linarith [Real.pi_pos]) ha)
  convert (Complex.hasSum_re h.hasSum).summable using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  rw [← Complex.ofReal_intCast]
  norm_cast
  congr 1
  push_cast
  ring

lemma norm_huxleyGaussianFactor (a ξ : ℝ) (n : ℤ) :
    ‖huxleyGaussianFactor a ξ n‖ = Real.exp (-Real.pi*a*(n:ℝ)^2) := by
  simp only [huxleyGaussianFactor,norm_mul,Complex.norm_exp,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,
    sub_zero,Real.exp_zero,mul_one]

lemma summable_norm_huxleyGaussianFactor {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    Summable (fun n => ‖huxleyGaussianFactor a ξ n‖) := by
  simp only [norm_huxleyGaussianFactor]
  simpa using summable_real_gaussian_shift ha 0

lemma huxley_gaussian_two_coordinate_poisson {a : ℝ} (ha : 0 < a) (ξ η : ℝ) :
    (∑' p : ℤ × ℤ, huxleyGaussianFactor a ξ p.1*huxleyGaussianFactor a η p.2) =
      ((1/a:ℝ):ℂ)*∑' p : ℤ × ℤ,
        ((Real.exp (-Real.pi/a*((p.1:ℝ)-ξ)^2)*
          Real.exp (-Real.pi/a*((p.2:ℝ)-η)^2):ℝ):ℂ) := by
  rw [← tsum_mul_tsum_of_summable_norm
    (summable_norm_huxleyGaussianFactor ha ξ) (summable_norm_huxleyGaussianFactor ha η)]
  change (∑' n, huxleyGaussianFactor a ξ n)*(∑' n, huxleyGaussianFactor a η n) = _
  rw [show (∑' n, huxleyGaussianFactor a ξ n) = _ from gaussian_coordinate_poisson ha ξ,
    show (∑' n, huxleyGaussianFactor a η n) = _ from gaussian_coordinate_poisson ha η]
  have hs (x : ℝ) : Summable (fun n : ℤ =>
      ‖Complex.exp ((-Real.pi/a*((n:ℝ)-x)^2:ℝ):ℂ)‖) := by
    simp only [Complex.norm_exp,Complex.ofReal_re]
    simpa only [div_eq_mul_inv,mul_assoc] using summable_real_gaussian_shift (inv_pos.mpr ha) x
  have hprod := tsum_mul_tsum_of_summable_norm (hs ξ) (hs η)
  have hc : ((1/Real.sqrt a:ℝ):ℂ)*((1/Real.sqrt a:ℝ):ℂ) = ((1/a:ℝ):ℂ) := by
    norm_cast
    rw [← pow_two,div_pow,Real.sq_sqrt ha.le]
    norm_num
  calc
    _ = (((1/Real.sqrt a:ℝ):ℂ)*((1/Real.sqrt a:ℝ):ℂ))*
        ((∑' n : ℤ, Complex.exp ((-Real.pi/a*((n:ℝ)-ξ)^2:ℝ):ℂ)) *
        (∑' n : ℤ, Complex.exp ((-Real.pi/a*((n:ℝ)-η)^2:ℝ):ℂ))) := by ring
    _ = _ := by
      rw [hc,hprod]
      congr 1
      apply tsum_congr
      intro p
      simp only [Complex.ofReal_mul,Complex.ofReal_exp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian Fourier kernel and its periodized majorant. -/
noncomputable section
namespace CubicFirstMoment

lemma huxleyCoordinateWeight_phase (a : ℝ) (x : ℂ) (p : ℤ × ℤ) :
    (huxleyCoordinateWeight a p:ℂ)*huxleyFrequencyPhase x (ofCoords p.1 p.2) =
      huxleyGaussianFactor a (huxleyXi₀ x) p.1 *
        huxleyGaussianFactor a (huxleyXi₁ x) p.2 := by
  rw [huxley_frequency_phase_coordinates]
  unfold huxleyCoordinateWeight huxleyGaussianFactor
  rw [show (-Real.pi*a*((p.1:ℝ)^2+(p.2:ℝ)^2)) =
    -Real.pi*a*(p.1:ℝ)^2 + -Real.pi*a*(p.2:ℝ)^2 by ring]
  rw [Real.exp_add,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_exp]
  rw [show 2*Real.pi*(p.1:ℝ)*huxleyXi₀ x = 2*Real.pi*huxleyXi₀ x*(p.1:ℝ) by ring,
    show 2*Real.pi*(p.2:ℝ)*huxleyXi₁ x = 2*Real.pi*huxleyXi₁ x*(p.2:ℝ) by ring]
  ring

lemma huxleyGaussianKernel_norm_bound {a : ℝ} (ha : 0 < a) (x : ℂ) :
    ‖huxleyGaussianKernel a x‖ ≤
      (1/a)*huxleyPeriodizedGaussian ((2/3:ℝ)*(Real.pi/a)) x := by
  let t := (2/3:ℝ)*(Real.pi/a)
  have ht : 0 < t := by dsimp [t]; positivity
  let f : ℤ × ℤ → ℝ := fun p =>
    Real.exp (-Real.pi/a*((p.1:ℝ)-huxleyXi₀ x)^2)*
      Real.exp (-Real.pi/a*((p.2:ℝ)-huxleyXi₁ x)^2)
  let g : ℤ × ℤ → ℝ := fun p =>
    Real.exp (-t*‖(huxleyDualCoordinateEquiv p:ℂ)-x‖^2)
  have hg : Summable g :=
    (huxleyPeriodizedGaussian_summable ht x).comp_injective huxleyDualCoordinateEquiv.injective
  have hfg (p : ℤ × ℤ) : f p ≤ g p := by
    have hd := huxley_dual_coordinate_distance x p.1 p.2
    have hm := mul_le_mul_of_nonneg_left hd ht.le
    dsimp [f,g,huxleyDualCoordinateEquiv]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change -Real.pi/a*((p.1:ℝ)-huxleyXi₀ x)^2 +
      -Real.pi/a*((p.2:ℝ)-huxleyXi₁ x)^2 ≤
      -t*‖(ofCoords (p.1+p.2) p.1:ℂ)-x‖^2
    calc
      _ = -(t*((3/2:ℝ)*(((p.1:ℝ)-huxleyXi₀ x)^2+
          ((p.2:ℝ)-huxleyXi₁ x)^2))) := by dsimp [t]; ring
      _ ≤ _ := by simpa only [neg_mul] using neg_le_neg hm
  have hf : Summable f := hg.of_nonneg_of_le (fun p => by dsimp [f]; positivity) hfg
  have he : huxleyGaussianKernel a x = ((1/a)*∑' p, f p:ℝ) := by
    unfold huxleyGaussianKernel
    rw [huxley_gaussian_two_coordinate_poisson ha]
    rw [← Complex.ofReal_tsum,← Complex.ofReal_mul]
  have hn : ‖huxleyGaussianKernel a x‖ = (1/a)*∑' p, f p := by
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    exact mul_nonneg (by positivity) (tsum_nonneg (fun p => by dsimp [f]; positivity))
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑' p, g p := hf.tsum_le_tsum hfg hg
    _ = huxleyPeriodizedGaussian t x := huxleyDualCoordinateEquiv.tsum_eq
      (fun z : Eisenstein => Real.exp (-t*‖(z:ℂ)-x‖^2))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyPhaseAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Phase multiplication for the Gaussian Gram expansion. -/
noncomputable section
namespace CubicFirstMoment

lemma huxleyFrequencyPhase_sub (x y : ℂ) (n : Eisenstein) :
    huxleyFrequencyPhase (x-y) n =
      huxleyFrequencyPhase x n*star (huxleyFrequencyPhase y n) := by
  have he : tracePair (n:ℂ) ((x-y)/traceLambda) =
      tracePair (n:ℂ) (x/traceLambda)-tracePair (n:ℂ) (y/traceLambda) := by
    simp only [tracePair,sub_div,mul_sub,Complex.sub_re]
  unfold huxleyFrequencyPhase
  rw [he,sub_eq_add_neg,AddChar.map_add_eq_mul,Circle.coe_mul,
    AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleySchur
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Schur estimate used for the Gaussian additive-sieve kernel. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma huxley_finite_schur {ι : Type*} (P : Finset ι) (K : ι → ι → ℝ)
    (hK : ∀ i ∈ P, ∀ j ∈ P, 0 ≤ K i j)
    (hsym : ∀ i ∈ P, ∀ j ∈ P, K i j = K j i)
    {B : ℝ} (hrow : ∀ i ∈ P, ∑ j ∈ P, K i j ≤ B) (v : ι → ℂ) :
    (∑ i ∈ P, ∑ j ∈ P, ‖v i‖*‖v j‖*K i j) ≤ B*∑ i ∈ P, ‖v i‖^2 := by
  have hcol : (∑ i ∈ P, ∑ j ∈ P, ‖v j‖^2*K i j) =
      ∑ i ∈ P, ∑ j ∈ P, ‖v i‖^2*K i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
  have he : (∑ i ∈ P, ∑ j ∈ P, (‖v i‖^2+‖v j‖^2)*K i j) =
      2*∑ i ∈ P, ‖v i‖^2*(∑ j ∈ P, K i j) := by
    simp_rw [add_mul,Finset.sum_add_distrib]
    rw [hcol]
    simp_rw [← Finset.mul_sum]
    ring
  have hpair : 2*(∑ i ∈ P, ∑ j ∈ P, ‖v i‖*‖v j‖*K i j) ≤
      ∑ i ∈ P, ∑ j ∈ P, (‖v i‖^2+‖v j‖^2)*K i j := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hp : 2*‖v i‖*‖v j‖ ≤ ‖v i‖^2+‖v j‖^2 := by
      nlinarith [sq_nonneg (‖v i‖-‖v j‖)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp (hK i hi j hj)
  have htotal : (∑ i ∈ P, ‖v i‖^2*(∑ j ∈ P, K i j)) ≤ B*∑ i ∈ P, ‖v i‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg ‖v i‖)
  rw [he] at hpair
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expansion and Schur bound for the actual Gaussian-weighted dual polynomial. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma huxley_weighted_phase_summable {a : ℝ} (ha : 0 < a) (x : ℂ) :
    Summable (fun n : ℤ × ℤ => (huxleyCoordinateWeight a n:ℂ)*
      huxleyFrequencyPhase x (ofCoords n.1 n.2)) := by
  simp_rw [huxleyCoordinateWeight_phase]
  exact summable_mul_of_summable_norm (summable_norm_huxleyGaussianFactor ha _)
    (summable_norm_huxleyGaussianFactor ha _)

lemma huxleyGaussianEnergy_expansion (a : ℝ) (P : Finset HuxleyLift)
    (v : HuxleyLift → ℂ) (n : ℤ × ℤ) :
    ((huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2:ℝ):ℂ) =
      ∑ p ∈ P, ∑ q ∈ P, (v p*star (v q))*
        ((huxleyCoordinateWeight a n:ℂ)*
          huxleyFrequencyPhase (p.frequency-q.frequency) (ofCoords n.1 n.2)) := by
  rw [Complex.ofReal_mul,Complex.ofReal_pow,← Complex.mul_conj']
  unfold huxleyDualPolynomial
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [huxleyFrequencyPhase_sub]
  simp only [starRingEnd_apply]
  ring

lemma huxleyGaussianEnergy_summable {a : ℝ} (ha : 0 < a) (P : Finset HuxleyLift)
    (v : HuxleyLift → ℂ) :
    Summable (fun n : ℤ × ℤ => huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2) := by
  have hs : Summable (fun n : ℤ × ℤ => ∑ p ∈ P, ∑ q ∈ P,
      (v p*star (v q))*((huxleyCoordinateWeight a n:ℂ)*
        huxleyFrequencyPhase (p.frequency-q.frequency) (ofCoords n.1 n.2))) :=
    summable_sum (fun p hp => summable_sum (fun q hq =>
      (huxley_weighted_phase_summable ha _).mul_left _))
  convert (Complex.hasSum_re hs.hasSum).summable using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  rw [← huxleyGaussianEnergy_expansion]
  rfl

lemma huxleyGaussianEnergy_sum {a : ℝ} (ha : 0 < a) (P : Finset HuxleyLift)
    (v : HuxleyLift → ℂ) :
    Complex.ofReal (∑' n : ℤ × ℤ, huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2) =
      ∑ p ∈ P, ∑ q ∈ P, (v p*star (v q))*
        huxleyGaussianKernel a (p.frequency-q.frequency) := by
  rw [Complex.ofReal_tsum]
  simp_rw [huxleyGaussianEnergy_expansion]
  rw [Summable.tsum_finsetSum (fun p hp => summable_sum (fun q hq =>
    (huxley_weighted_phase_summable ha _).mul_left _))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Summable.tsum_finsetSum (fun q hq =>
    (huxley_weighted_phase_summable ha _).mul_left _)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [tsum_mul_left]
  congr 1
  simp_rw [huxleyCoordinateWeight_phase]
  rfl

lemma huxleyGaussianEnergy_bound {a : ℝ} (ha : 0 < a) (Q : ℝ) (hQ : 0 < Q)
    (P : Finset HuxleyLift) (hred : ∀ p ∈ P, p.reduced Q)
    (hzero : ∀ p ∈ P, p.shift = 0) (v : HuxleyLift → ℂ) :
    (∑' n : ℤ × ℤ, huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2) ≤
      ((1/a)*huxleyGaussianConstant*(1+Q^2/((2/3:ℝ)*(Real.pi/a))))*
        ∑ p ∈ P, ‖v p‖^2 := by
  let t := (2/3:ℝ)*(Real.pi/a)
  have ht : 0 < t := by dsimp [t]; positivity
  have hs : 0 ≤ ∑' n : ℤ × ℤ,
      huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2 :=
    tsum_nonneg (fun n => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  calc
    _ = ‖Complex.ofReal (∑' n : ℤ × ℤ,
        huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs]
    _ ≤ ∑ p ∈ P, ∑ q ∈ P,
        ‖v p‖*‖v q‖*‖huxleyGaussianKernel a (p.frequency-q.frequency)‖ := by
      rw [huxleyGaussianEnergy_sum ha]
      apply (norm_sum_le P (fun p => ∑ q ∈ P,
        (v p*star (v q))*huxleyGaussianKernel a (p.frequency-q.frequency))).trans
      apply Finset.sum_le_sum
      intro p hp
      simpa only [norm_mul,norm_star] using norm_sum_le P (fun q =>
        (v p*star (v q))*huxleyGaussianKernel a (p.frequency-q.frequency))
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, ‖v p‖*‖v q‖*
        ((1/a)*huxleyPeriodizedGaussian t (p.frequency-q.frequency)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (huxleyGaussianKernel_norm_bound ha _)
        (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))
    _ ≤ _ := by
      apply huxley_finite_schur
      · intro p hp q hq
        exact mul_nonneg (by positivity) (huxleyPeriodizedGaussian_nonneg _ _)
      · intro p hp q hq
        rw [show q.frequency-p.frequency = -(p.frequency-q.frequency) by ring,
          huxleyPeriodizedGaussian_neg]
      · intro p hp
        rw [← Finset.mul_sum]
        exact (mul_le_mul_of_nonneg_left
          (huxleyPeriodizedGaussian_row_bound Q hQ ht P hred hzero p.frequency)
          (by positivity)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyFiniteDual
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the Gaussian weight on the finite norm ball and applying duality. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma huxleyAdditiveConstant_pos : 0 < huxleyAdditiveConstant := by
  have hG := huxleyGaussianConstant_pos
  have hπ := Real.pi_pos
  unfold huxleyAdditiveConstant
  positivity

lemma huxley_coordinate_majorant {Z : ℝ} (hZ : 0 < Z) (n : ℤ × ℤ)
    (hn : norm (ofCoords n.1 n.2) ≤ Z) :
    1 ≤ Real.exp 1*huxleyCoordinateWeight (1/(2*Real.pi*Z)) n := by
  have hE := (huxley_coordinate_energy n.1 n.2).trans (mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ) ≤ 2))
  have hm := mul_le_mul_of_nonneg_left hE
    (show 0 ≤ Real.pi*(1/(2*Real.pi*Z)) by positivity)
  have hc : Real.pi*(1/(2*Real.pi*Z))*(2*Z) = 1 := by
    field_simp
  rw [hc] at hm
  unfold huxleyCoordinateWeight
  rw [← Real.exp_add]
  exact Real.one_le_exp_iff.mpr (by nlinarith)

lemma huxley_gaussian_constant_bound {Q Z : ℝ} (hZ : 0 < Z) :
    Real.exp 1*((1/(1/(2*Real.pi*Z)))*huxleyGaussianConstant*
      (1+Q^2/((2/3:ℝ)*(Real.pi/(1/(2*Real.pi*Z)))))) ≤
      huxleyAdditiveConstant*(Q^2+Z) := by
  have hπ := Real.pi_pos
  have hπ0 := Real.pi_ne_zero
  have hZ0 := ne_of_gt hZ
  have he : (1/(1/(2*Real.pi*Z)))*
      (1+Q^2/((2/3:ℝ)*(Real.pi/(1/(2*Real.pi*Z))))) =
      2*Real.pi*Z+(3/(2*Real.pi))*Q^2 := by
    field_simp
  have hscale : 2*Real.pi*Z+(3/(2*Real.pi))*Q^2 ≤
      (2*Real.pi+3/(2*Real.pi))*(Q^2+Z) := by
    have h1 : 0 ≤ (2*Real.pi)*Q^2 := by positivity
    have h2 : 0 ≤ (3/(2*Real.pi))*Z := by positivity
    nlinarith
  calc
    _ = (Real.exp 1*huxleyGaussianConstant)*
        ((1/(1/(2*Real.pi*Z)))*(1+Q^2/((2/3:ℝ)*(Real.pi/(1/(2*Real.pi*Z)))))) := by ring
    _ ≤ (Real.exp 1*huxleyGaussianConstant)*((2*Real.pi+3/(2*Real.pi))*(Q^2+Z)) := by
      rw [he]
      exact mul_le_mul_of_nonneg_left hscale (mul_nonneg (Real.exp_pos _).le huxleyGaussianConstant_pos.le)
    _ = _ := by unfold huxleyAdditiveConstant; ring

lemma huxley_finite_dual_bound (Q Z : ℝ) (hQ : 0 < Q) (hZ : 0 < Z)
    (P : Finset HuxleyLift) (hred : ∀ p ∈ P, p.reduced Q)
    (hzero : ∀ p ∈ P, p.shift = 0)
    (N : Finset Eisenstein) (hN : ∀ n ∈ N, norm n ≤ Z) (v : HuxleyLift → ℂ) :
    (∑ n ∈ N, ‖∑ p ∈ P, v p*huxleyFrequencyPhase p.frequency n‖^2) ≤
      huxleyAdditiveConstant*(Q^2+Z)*∑ p ∈ P, ‖v p‖^2 := by
  classical
  let T := N.image huxleyCoordinateEquiv.symm
  let a := 1/(2*Real.pi*Z)
  have ha : 0 < a := by dsimp [a]; positivity
  have hsum := huxleyGaussianEnergy_summable ha P v
  have hmajor (n : ℤ × ℤ) (hn : n ∈ T) :
      1 ≤ Real.exp 1*huxleyCoordinateWeight a n := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    apply huxley_coordinate_majorant hZ
    exact (show norm (huxleyCoordinateEquiv (huxleyCoordinateEquiv.symm k)) ≤ Z by
      simpa only [Equiv.apply_symm_apply] using hN k hk)
  have hweight : (∑ n ∈ T, ‖huxleyDualPolynomial P v n‖^2) ≤
      Real.exp 1*∑ n ∈ T, huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have h := mul_le_mul_of_nonneg_right (hmajor n hn) (sq_nonneg ‖huxleyDualPolynomial P v n‖)
    simpa only [one_mul,mul_assoc] using h
  have hfinite : (∑ n ∈ T, huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2) ≤
      ∑' n, huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2 :=
    hsum.sum_le_tsum T (fun n hn => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  calc
    _ = ∑ n ∈ T, ‖huxleyDualPolynomial P v n‖^2 := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro n hn
        have he : ofCoords (huxleyCoordinateEquiv.symm n).1 (huxleyCoordinateEquiv.symm n).2 = n :=
          huxleyCoordinateEquiv.apply_symm_apply n
        simp only [huxleyDualPolynomial,he]
      · exact fun _ _ _ _ h => huxleyCoordinateEquiv.symm.injective h
    _ ≤ Real.exp 1*(∑' n, huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2) :=
      hweight.trans (mul_le_mul_of_nonneg_left hfinite (Real.exp_pos _).le)
    _ ≤ Real.exp 1*(((1/a)*huxleyGaussianConstant*(1+Q^2/((2/3:ℝ)*(Real.pi/a))))*
        ∑ p ∈ P, ‖v p‖^2) :=
      mul_le_mul_of_nonneg_left (huxleyGaussianEnergy_bound ha Q hQ P hred hzero v) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (huxley_gaussian_constant_bound hZ)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma huxley_finite_primal_bound (Q Z : ℝ) (hQ : 0 < Q) (hZ : 0 < Z)
    (P : Finset HuxleyLift) (hred : ∀ p ∈ P, p.reduced Q)
    (hzero : ∀ p ∈ P, p.shift = 0)
    (N : Finset Eisenstein) (hN : ∀ n ∈ N, norm n ≤ Z) (v : Eisenstein → ℂ) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n*huxleyFrequencyPhase p.frequency n‖^2) ≤
      huxleyAdditiveConstant*(Q^2+Z)*∑ n ∈ N, ‖v n‖^2 :=
  finite_additive_sieve_duality P N _
    (mul_nonneg huxleyAdditiveConstant_pos.le (by positivity))
    (huxley_finite_dual_bound Q Z hQ hZ P hred hzero N hN) v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyResiduePoints
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal residue sums as a finite set of reduced fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxleyIndexLift_injective (Q : ℝ) : Function.Injective (@huxleyIndexLift Q) := by
  rintro ⟨⟨q,hq⟩,x⟩ ⟨⟨r,hr⟩,y⟩ h
  have hqr : q = r := congrArg HuxleyLift.denominator h
  subst r
  have hxy : x = y := by
    have hn : residueRepresentative q x = residueRepresentative q y :=
      congrArg HuxleyLift.numerator h
    have hm := congrArg (Ideal.Quotient.mk (modulus q)) hn
    simpa only [residueRepresentative_spec] using hm
  subst y
  rfl

lemma huxleyResiduePointSet_reduced (Q : ℝ) :
    ∀ p ∈ huxleyResiduePointSet Q, p.reduced Q := by
  let _ : Fintype (HuxleyResidueIndex Q) := huxleyResidueIndexFintype Q
  intro p hp
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
  have hq := mem_nonzeroNormBall.mp j.1.property
  exact huxleyLift_actual hq.2 hq.1 j.2 (Finset.mem_filter.mp hj).2 0

lemma huxleyResiduePointSet_shift (Q : ℝ) :
    ∀ p ∈ huxleyResiduePointSet Q, p.shift = 0 := by
  let _ : Fintype (HuxleyResidueIndex Q) := huxleyResidueIndexFintype Q
  intro p hp
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
  rfl

lemma huxleyResiduePointSet_sum (Q : ℝ) (f : HuxleyLift → ℝ) :
    (∑ p ∈ huxleyResiduePointSet Q, f p) =
      ∑ q ∈ nonzeroNormBall Q, ∑' x : Residues q,
        if IsUnit x then f ⟨q,residueRepresentative q x,0⟩ else 0 := by
  let _ (q : {q : Eisenstein // q ∈ nonzeroNormBall Q}) : Fintype (Residues q.val) := huxleyResidueFintype q
  let _ : Fintype (HuxleyResidueIndex Q) := huxleyResidueIndexFintype Q
  unfold huxleyResiduePointSet
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    rw [Fintype.sum_sigma]
    rw [← Finset.sum_coe_sort (nonzeroNormBall Q)]
    apply Finset.sum_congr rfl
    intro q hq
    rw [tsum_fintype]
    rfl
  · exact fun _ _ _ _ h => huxleyIndexLift_injective Q h

lemma huxleySieveMass_eq_points (Q Z : ℝ) (v : Eisenstein → ℂ) :
    huxleySieveMass Q Z v = ∑ p ∈ huxleyResiduePointSet Q,
      ‖∑ n ∈ nonzeroNormBall Z, v n*huxleyFrequencyPhase p.frequency n‖^2 := by
  rw [huxleyResiduePointSet_sum]
  unfold huxleySieveMass
  apply Finset.sum_congr rfl
  intro q hq
  unfold huxleyModulusMass
  apply tsum_congr
  intro x
  split_ifs <;> try rfl
  unfold additiveSievePolynomial
  congr 2
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  rw [huxleyPhase_eq_frequency]
  simp [HuxleyLift.frequency]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyProof
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact published additive large-sieve input, proved from Gaussian packing. -/
noncomputable section
namespace CubicFirstMoment

theorem huxleyAdditiveLargeSieve_proved : HuxleyAdditiveLargeSieve := by
  refine ⟨huxleyAdditiveConstant,huxleyAdditiveConstant_pos,?_⟩
  intro Q Z hQ hZ v
  rw [huxleySieveMass_eq_points]
  exact huxley_finite_primal_bound Q Z (by linarith) (by linarith)
    (huxleyResiduePointSet Q) (huxleyResiduePointSet_reduced Q)
    (huxleyResiduePointSet_shift Q) (nonzeroNormBall Z)
    (fun n hn => (mem_nonzeroNormBall.mp hn).1) v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealThetaCompletion
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic continuation from the exact ideal theta transformation. The
hypotheses concern the theta series itself and follow from the
finite-character Poisson formula. -/
noncomputable section
open Filter Asymptotics MeasureTheory
namespace CubicFirstMoment

lemma idealThetaFEPair_strong {A : ℝ} (hA : 0 < A)
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {ε : ℂ} (hε : ε ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealTheta A χ (1/t) = ε*(t:ℂ)*idealTheta A χdual t) :
    IsStrongFEPair (idealThetaFEPair hA χ χdual hχ hχdual hε hFE) := ⟨rfl,rfl⟩

lemma thetaHeckeL_eq_series {A : ℝ} (hA : 0 < A)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    thetaHeckeL A (mellin (idealTheta A χ)) s =
      normDirichletSeries χ idealExponentNorm s := by
  rw [thetaHeckeL,idealTheta_mellin hA χ hχ hs,Complex.cpow_neg]
  have hAp : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))
  have hG := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  field_simp

lemma idealThetaFEPair_hecke {A : ℝ} (hA : 0 < A)
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {ε : ℂ} (hε : ε ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealTheta A χ (1/t) = ε*(t:ℂ)*idealTheta A χdual t) :
    let P := idealThetaFEPair hA χ χdual hχ hχdual hε hFE
    Differentiable ℂ (thetaHeckeL A P.Λ) ∧
    Differentiable ℂ (thetaHeckeL A P.symm.Λ) ∧
    (∀ s : ℂ, 1 < s.re → thetaHeckeL A P.Λ s =
      normDirichletSeries χ idealExponentNorm s) ∧
    (∀ s : ℂ, 1 < s.re → thetaHeckeL A P.symm.Λ s =
      normDirichletSeries χdual idealExponentNorm s) ∧
    HeckeFunctionalEquation A 0 ε (thetaHeckeL A P.Λ) (thetaHeckeL A P.symm.Λ) := by
  dsimp only
  let P := idealThetaFEPair hA χ χdual hχ hχdual hε hFE
  have hP := idealThetaFEPair_strong hA χ χdual hχ hχdual hε hFE
  have he := thetaHeckeL_entire P hP hA
  refine ⟨he.1,he.2,?_,?_,thetaHeckeL_functionalEquation hA P rfl⟩
  · intro s hs
    rw [hP.Λ_eq]
    exact thetaHeckeL_eq_series hA χ hχ hs
  · intro s hs
    rw [hP.symm_Λ_eq]
    exact thetaHeckeL_eq_series hA χdual hχdual hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MeanValueLogSpacing
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic frequency separation for the Dirichlet mean value bound. -/
noncomputable section
namespace CubicFirstMoment

lemma log_frequency_spacing {R x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxR : x ≤ R) (hyR : y ≤ R) :
    |x-y| ≤ R*|Real.log x-Real.log y| := by
  have hordered {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
      (hxy : y ≤ x) (hxR : x ≤ R) :
      x-y ≤ R*(Real.log x-Real.log y) := by
    have hlog : Real.log y-Real.log x ≤ y/x-1 := by
      rw [← Real.log_div hy.ne' hx.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hy hx)
    have hm := mul_le_mul_of_nonneg_left hlog hx.le
    have he : x*(y/x-1) = y-x := by field_simp
    rw [he] at hm
    have hl : 0 ≤ Real.log x-Real.log y :=
      sub_nonneg.mpr (Real.log_le_log hy hxy)
    apply le_trans (b := x*(Real.log x-Real.log y))
    · nlinarith
    · exact mul_le_mul_of_nonneg_right hxR hl
  by_cases hxy : y ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy hxy))]
    exact hordered hx hy hxy hxR
  · have hyx := le_of_not_ge hxy
    rw [abs_sub_comm x y,abs_sub_comm (Real.log x) (Real.log y),
      abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hx hyx))]
    exact hordered hy hx hyx hyR

lemma integer_log_frequency_spacing {Z m n : ℕ} (hm : m ∈ Finset.Icc 1 Z)
    (hn : n ∈ Finset.Icc 1 Z) :
    |(m:ℝ)-(n:ℝ)| ≤ (Z:ℝ)*|Real.log (m:ℝ)-Real.log (n:ℝ)| := by
  obtain ⟨hm1,hmZ⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hn1,hnZ⟩ := Finset.mem_Icc.mp hn
  exact log_frequency_spacing (by exact_mod_cast (zero_lt_one.trans_le hm1))
    (by exact_mod_cast (zero_lt_one.trans_le hn1))
    (by exact_mod_cast hmZ) (by exact_mod_cast hnZ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MeanValueGaussianKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian Fourier kernel for the mean value of the actual integer
norm Dirichlet polynomial. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma meanValueGaussianPhase_scale {L : ℝ} (hL : L ≠ 0) (u t : ℝ) :
    meanValueGaussianPhase L u t = meanValueGaussianPhase 1 (L*u) (t/L) := by
  have he : (L*u)*(t/L) = u*t := by field_simp
  simp only [meanValueGaussianPhase,div_one,he]

lemma meanValueGaussianPhase_one_integrable (u : ℝ) :
    Integrable (meanValueGaussianPhase 1 u) := by
  have he : meanValueGaussianPhase 1 u = fun t : ℝ =>
      Complex.exp (-(1:ℂ)*(t:ℂ)^2+((u:ℂ)*Complex.I)*(t:ℂ)+0) := by
    funext t
    simp only [meanValueGaussianPhase,div_one,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  exact integrable_cexp_quadratic (b := (1:ℂ)) (by norm_num) _ _

lemma meanValueGaussianPhase_integrable {L : ℝ} (hL : 0 < L) (u : ℝ) :
    Integrable (meanValueGaussianPhase L u) := by
  have he : meanValueGaussianPhase L u = fun t => meanValueGaussianPhase 1 (L*u) (t/L) :=
    funext (meanValueGaussianPhase_scale hL.ne' u)
  rw [he]
  exact (meanValueGaussianPhase_one_integrable (L*u)).comp_div hL.ne'

lemma meanValueGaussianPhase_one_integral_norm (u : ℝ) :
    ‖∫ t : ℝ, meanValueGaussianPhase 1 u t‖ =
      Real.sqrt Real.pi*Real.exp (-u^2/4) := by
  have he : (∫ t : ℝ, meanValueGaussianPhase 1 u t) =
      (Real.pi/(1:ℂ))^(1/2:ℂ)*Complex.exp (-(u:ℂ)^2/(4*(1:ℂ))) := by
    convert fourierIntegral_gaussian (b := (1:ℂ)) (by norm_num) (u:ℂ) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext t
    simp only [meanValueGaussianPhase,div_one]
    rw [mul_comm]
    congr 1 <;> push_cast <;> ring_nf
  rw [he,norm_mul]
  have hp : ‖(Real.pi/(1:ℂ))^(1/2:ℂ)‖ = Real.sqrt Real.pi := by
    rw [div_one,show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_real,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
      ← Real.sqrt_eq_rpow]
  have ht : -(u:ℂ)^2/(4*(1:ℂ)) = ((-u^2/4:ℝ):ℂ) := by push_cast; ring
  rw [hp,ht,Complex.norm_exp,Complex.ofReal_re]

lemma meanValueGaussianPhase_integral_norm {L : ℝ} (hL : 0 < L) (u : ℝ) :
    ‖∫ t : ℝ, meanValueGaussianPhase L u t‖ =
      L*Real.sqrt Real.pi*Real.exp (-(L*u)^2/4) := by
  have he : meanValueGaussianPhase L u = fun t => meanValueGaussianPhase 1 (L*u) (t/L) :=
    funext (meanValueGaussianPhase_scale hL.ne' u)
  rw [he,Measure.integral_comp_div,norm_smul,Real.norm_eq_abs,abs_of_pos hL,
    meanValueGaussianPhase_one_integral_norm]
  rw [abs_of_pos hL]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MeanValueGaussianRows
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform row sums for the Gaussian matrix on logarithmic frequencies. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma nat_dist_cast_eq_abs (m n : ℕ) : (Nat.dist m n:ℝ) = |(m:ℝ)-(n:ℝ)| := by
  by_cases h : m ≤ n
  · rw [Nat.dist_eq_sub_of_le h,Nat.cast_sub h,abs_of_nonpos (sub_nonpos.mpr (show (m:ℝ) ≤ n by exact_mod_cast h))]
    ring
  · have h' := le_of_not_ge h
    rw [Nat.dist_eq_sub_of_le_right h',Nat.cast_sub h',abs_of_nonneg (sub_nonneg.mpr (show (n:ℝ) ≤ m by exact_mod_cast h'))]

lemma geometric_nat_distance_sum {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (Z n : ℕ) (hn : n ≤ Z) :
    (∑ m ∈ Finset.Icc 1 Z, q^(Nat.dist n m)) ≤ 2/(1-q) := by
  let S := Finset.Icc 1 Z
  let A := S.filter (fun m => m ≤ n)
  let B := S.filter (fun m => ¬m ≤ n)
  have hgeom : (∑ d ∈ Finset.range (Z+1), q^d) ≤ 1/(1-q) := by
    simpa only [Nat.Ico_zero_eq_range,pow_zero] using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := Z+1) hq hq1)
  have hA : (∑ m ∈ A, q^(Nat.dist n m)) ≤ 1/(1-q) := by
    calc
      _ = ∑ m ∈ A, q^(n-m) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp hm).2]
      _ = ∑ d ∈ A.image (fun m => n-m), q^d := by
        symm
        apply Finset.sum_image
        intro m hm k hk he
        have hm' := (Finset.mem_filter.mp hm).2
        have hk' := (Finset.mem_filter.mp hk).2
        change n-m = n-k at he
        omega
      _ ≤ ∑ d ∈ Finset.range (Z+1), q^d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hd
          exact Finset.mem_range.mpr (by omega)
        · intro d _ _
          exact pow_nonneg hq _
      _ ≤ _ := hgeom
  have hB : (∑ m ∈ B, q^(Nat.dist n m)) ≤ 1/(1-q) := by
    calc
      _ = ∑ m ∈ B, q^(m-n) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Nat.dist_eq_sub_of_le (by have := (Finset.mem_filter.mp hm).2; omega)]
      _ = ∑ d ∈ B.image (fun m => m-n), q^d := by
        symm
        apply Finset.sum_image
        intro m hm k hk he
        have hm' := (Finset.mem_filter.mp hm).2
        have hk' := (Finset.mem_filter.mp hk).2
        change m-n = k-n at he
        omega
      _ ≤ ∑ d ∈ Finset.range (Z+1), q^d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hd
          have hmZ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
          exact Finset.mem_range.mpr (by omega)
        · intro d _ _
          exact pow_nonneg hq _
      _ ≤ _ := hgeom
  have he : (∑ m ∈ S, q^(Nat.dist n m)) =
      (∑ m ∈ A, q^(Nat.dist n m))+(∑ m ∈ B, q^(Nat.dist n m)) := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun m => m ≤ n) _).symm
  change (∑ m ∈ S, q^(Nat.dist n m)) ≤ _
  rw [he]
  calc
    _ ≤ 1/(1-q)+1/(1-q) := add_le_add hA hB
    _ = _ := by ring

lemma gaussian_log_frequency_decay {Z n m : ℕ} (hn : n ∈ Finset.Icc 1 Z)
    (hm : m ∈ Finset.Icc 1 Z) {L : ℝ} (hL : (Z:ℝ) ≤ L) :
    Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4) ≤
      (Real.exp (-(1/4:ℝ)))^(Nat.dist n m) := by
  have hdist : 0 ≤ (Nat.dist n m:ℝ) := by positivity
  have hsep : (Nat.dist n m:ℝ) ≤ L*|Real.log (n:ℝ)-Real.log (m:ℝ)| := by
    rw [nat_dist_cast_eq_abs]
    exact (integer_log_frequency_spacing hn hm).trans
      (mul_le_mul_of_nonneg_right hL (abs_nonneg _))
  have hnat : (Nat.dist n m:ℝ) ≤ (Nat.dist n m:ℝ)^2 := by
    have hn' : Nat.dist n m ≤ Nat.dist n m*Nat.dist n m := by
      generalize Nat.dist n m = d
      by_cases hd : d = 0
      · simp [hd]
      · have : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
        nlinarith
    simpa only [pow_two] using (show (Nat.dist n m:ℝ) ≤ (Nat.dist n m:ℝ)*(Nat.dist n m:ℝ) by exact_mod_cast hn')
  have hL0 : 0 ≤ L := le_trans (Nat.cast_nonneg Z) hL
  have hsquare : (Nat.dist n m:ℝ)^2 ≤ (L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2 := by
    have h := sq_le_sq₀ hdist (mul_nonneg hL0 (abs_nonneg _)) |>.mpr hsep
    simpa only [mul_pow,sq_abs] using h
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma gaussian_log_frequency_row_bound {Z n : ℕ} (hn : n ∈ Finset.Icc 1 Z)
    {L : ℝ} (hL : (Z:ℝ) ≤ L) :
    (∑ m ∈ Finset.Icc 1 Z,
      Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4)) ≤
      2/(1-Real.exp (-(1/4:ℝ))) := by
  apply (Finset.sum_le_sum (fun m hm => gaussian_log_frequency_decay hn hm hL)).trans
  exact geometric_nat_distance_sum (Real.exp_pos _).le
    (by rw [Real.exp_lt_one_iff]; norm_num) Z n (Finset.mem_Icc.mp hn).2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MeanValueGaussianEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian mean square of the actual integer-frequency polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma meanValueGaussian_phase_product (L t x y : ℝ) :
    (meanValueGaussianWeight L t:ℂ)*mellinPhase t x*star (mellinPhase t y) =
      meanValueGaussianPhase L (Real.log x-Real.log y) t := by
  simp only [← starRingEnd_apply]
  simp only [meanValueGaussianWeight,meanValueGaussianPhase,mellinPhase,
    Complex.ofReal_exp,← Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma meanValueGaussian_expansion (Z : ℕ) (v : ℕ → ℂ) (L t : ℝ) :
    ((meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2:ℝ):ℂ) =
      ∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        (v n*star (v m))*meanValueGaussianPhase L
          (Real.log (n:ℝ)-Real.log (m:ℝ)) t := by
  rw [Complex.ofReal_mul,Complex.ofReal_pow,← Complex.mul_conj']
  unfold integerNormPolynomial
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [← meanValueGaussian_phase_product]
  simp only [starRingEnd_apply]
  ring

lemma meanValueGaussian_integrable {L : ℝ} (hL : 0 < L) (Z : ℕ) (v : ℕ → ℂ) :
    Integrable (fun t : ℝ => meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) := by
  have hi : Integrable (fun t : ℝ =>
      ∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        (v n*star (v m))*meanValueGaussianPhase L
          (Real.log (n:ℝ)-Real.log (m:ℝ)) t) := by
    apply integrable_finsetSum
    intro n hn
    apply integrable_finsetSum
    intro m hm
    exact (meanValueGaussianPhase_integrable hL _).const_mul _
  have he : (fun t : ℝ => meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) =
      fun t => (∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        (v n*star (v m))*meanValueGaussianPhase L
          (Real.log (n:ℝ)-Real.log (m:ℝ)) t).re := by
    funext t
    rw [← meanValueGaussian_expansion]
    rfl
  rw [he]
  exact hi.re

lemma meanValueGaussian_integral_bound {L : ℝ} (hL : 0 < L)
    (Z : ℕ) (v : ℕ → ℂ) :
    (∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) ≤
      L*Real.sqrt Real.pi * ∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        ‖v n‖*‖v m‖*Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4) := by
  let S := Finset.Icc 1 Z
  have he : Complex.ofReal (∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) =
      ∑ n ∈ S, ∑ m ∈ S, (v n*star (v m))*
        ∫ t : ℝ, meanValueGaussianPhase L (Real.log (n:ℝ)-Real.log (m:ℝ)) t := by
    rw [← integral_complex_ofReal]
    simp_rw [meanValueGaussian_expansion]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro m hm
        exact integral_const_mul _ _
      · intro m hm
        exact (meanValueGaussianPhase_integrable hL _).const_mul _
    · intro n hn
      apply integrable_finsetSum
      intro m hm
      exact (meanValueGaussianPhase_integrable hL _).const_mul _
  have h0 : 0 ≤ ∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2 :=
    integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  calc
    _ = ‖Complex.ofReal (∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0]
    _ ≤ ∑ n ∈ S, ∑ m ∈ S,
        ‖(v n*star (v m))*∫ t : ℝ,
          meanValueGaussianPhase L (Real.log (n:ℝ)-Real.log (m:ℝ)) t‖ := by
      rw [he]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => norm_sum_le _ _))
    _ = _ := by
      simp only [norm_mul,norm_star,meanValueGaussianPhase_integral_norm hL]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring

lemma gaussian_schur_bound {Z : ℕ} {L : ℝ} (hL : (Z:ℝ) ≤ L) (v : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
      ‖v n‖*‖v m‖*Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4)) ≤
      (2/(1-Real.exp (-(1/4:ℝ))))*∑ n ∈ Finset.Icc 1 Z, ‖v n‖^2 := by
  let S := Finset.Icc 1 Z
  let K := fun n m : ℕ => Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4)
  have hsym : ∀ n m, K n m = K m n := by
    intro n m
    dsimp [K]
    congr 1
    ring
  have hrow : ∀ n ∈ S, ∑ m ∈ S, K n m ≤ 2/(1-Real.exp (-(1/4:ℝ))) :=
    fun n hn => gaussian_log_frequency_row_bound hn hL
  have hcol : (∑ n ∈ S, ∑ m ∈ S, ‖v m‖^2*K n m) =
      ∑ n ∈ S, ∑ m ∈ S, ‖v n‖^2*K n m := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    rw [hsym]
  have he : (∑ n ∈ S, ∑ m ∈ S, (‖v n‖^2+‖v m‖^2)*K n m) =
      2*∑ n ∈ S, ‖v n‖^2*(∑ m ∈ S, K n m) := by
    simp_rw [add_mul,Finset.sum_add_distrib]
    rw [hcol]
    simp_rw [← Finset.mul_sum]
    ring
  have hpair : 2*(∑ n ∈ S, ∑ m ∈ S, ‖v n‖*‖v m‖*K n m) ≤
      ∑ n ∈ S, ∑ m ∈ S, (‖v n‖^2+‖v m‖^2)*K n m := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro m hm
    have hp : 2*‖v n‖*‖v m‖ ≤ ‖v n‖^2+‖v m‖^2 := by nlinarith [sq_nonneg (‖v n‖-‖v m‖)]
    exact (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le)
  have htotal : (∑ n ∈ S, ‖v n‖^2*(∑ m ∈ S, K n m)) ≤
      (2/(1-Real.exp (-(1/4:ℝ))))*∑ n ∈ S, ‖v n‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg ‖v n‖)
  change (∑ n ∈ S, ∑ m ∈ S, ‖v n‖*‖v m‖*K n m) ≤ _
  rw [he] at hpair
  linarith

 theorem integerNormPolynomial_gaussian_meanSquare {Z : ℕ} {L : ℝ}
    (hL : 0 < L) (hZL : (Z:ℝ) ≤ L) (v : ℕ → ℂ) :
    (∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) ≤
      (L*Real.sqrt Real.pi*(2/(1-Real.exp (-(1/4:ℝ)))))*
        ∑ n ∈ Finset.Icc 1 Z, ‖v n‖^2 := by
  exact (meanValueGaussian_integral_bound hL Z v).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (gaussian_schur_bound hZL v)
      (mul_nonneg hL.le (Real.sqrt_nonneg _)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MontgomeryVaughanProof
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The required ordinary mean value bound, proved by a Gaussian majorant. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma integerNormPolynomial_continuous (Z : ℕ) (v : ℕ → ℂ) :
    Continuous (integerNormPolynomial Z v) := by
  unfold integerNormPolynomial mellinPhase
  fun_prop

lemma gaussian_interval_majorant {L a b : ℝ} (hL : 0 < L) (hab : a ≤ b)
    (ha : -L ≤ a) (hb : b ≤ L) (Z : ℕ) (v : ℕ → ℂ) :
    (∫ t in a..b, ‖integerNormPolynomial Z v t‖^2) ≤
      Real.exp 1*(∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) := by
  let f := fun t : ℝ => ‖integerNormPolynomial Z v t‖^2
  let g := fun t : ℝ => meanValueGaussianWeight L t*f t
  have hf : IntervalIntegrable f volume a b :=
    ((integerNormPolynomial_continuous Z v).norm.pow 2).intervalIntegrable _ _
  have hg : Integrable g := meanValueGaussian_integrable hL Z v
  have hgI : IntervalIntegrable g volume a b := hg.intervalIntegrable
  have hbound : ∀ t ∈ Set.Icc a b, f t ≤ Real.exp 1*g t := by
    intro t ht
    have htL : |t| ≤ L := abs_le.mpr ⟨ha.trans ht.1,ht.2.trans hb⟩
    have hratio : |t/L| ≤ 1 := by
      rw [abs_div,abs_of_pos hL]
      exact (div_le_one hL).mpr htL
    have hsq : (t/L)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hratio
    have he : 1 ≤ Real.exp 1*meanValueGaussianWeight L t := by
      rw [meanValueGaussianWeight,← Real.exp_add]
      calc
        1 = Real.exp 0 := Real.exp_zero.symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    calc
      f t = 1*f t := by ring
      _ ≤ (Real.exp 1*meanValueGaussianWeight L t)*f t :=
        mul_le_mul_of_nonneg_right he (sq_nonneg _)
      _ = _ := by dsimp [g]; ring
  calc
    _ ≤ ∫ t in a..b, Real.exp 1*g t :=
      intervalIntegral.integral_mono_on hab hf (hgI.const_mul _) hbound
    _ = Real.exp 1*(∫ t in a..b, g t) := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [intervalIntegral.integral_of_le hab]
      exact setIntegral_le_integral hg (Filter.Eventually.of_forall
        (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))

lemma integerNormPolynomial_translate (Z : ℕ) (v : ℕ → ℂ) (t c : ℝ) :
    integerNormPolynomial Z v (t+c) =
      integerNormPolynomial Z (fun n => v n*mellinPhase c (n:ℝ)) t := by
  unfold integerNormPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [mellinPhase_add]
  ring

lemma ordinaryMeanValueConstant_pos : 0 < ordinaryMeanValueConstant := by
  unfold ordinaryMeanValueConstant
  have he : Real.exp (-(1/4:ℝ)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  positivity

/-- The ordinary Dirichlet-polynomial mean-square bound. -/
theorem montgomeryVaughanBound_proved : MontgomeryVaughanBound ordinaryMeanValueConstant := by
  intro Z v a b hab
  by_cases hZ : Z = 0
  · subst Z
    simp [integerNormPolynomial]
  have hZpos : (0:ℝ) < Z := by exact_mod_cast Nat.pos_of_ne_zero hZ
  let L : ℝ := b-a+Z
  let c : ℝ := (a+b)/2
  let w : ℕ → ℂ := fun n => v n*mellinPhase c (n:ℝ)
  have hL : 0 < L := by dsimp [L]; linarith
  have hZL : (Z:ℝ) ≤ L := by dsimp [L]; linarith
  have he : (∫ t in a..b, ‖integerNormPolynomial Z v t‖^2) =
      ∫ t in a-c..b-c, ‖integerNormPolynomial Z w t‖^2 := by
    have hs := intervalIntegral.integral_comp_add_right
      (a := a-c) (b := b-c) (fun t => ‖integerNormPolynomial Z v t‖^2) c
    simp only [sub_add_cancel] at hs
    rw [← hs]
    apply intervalIntegral.integral_congr
    intro t ht
    change ‖integerNormPolynomial Z v (t+c)‖^2 = ‖integerNormPolynomial Z w t‖^2
    rw [integerNormPolynomial_translate]
  have henergy : (∑ n ∈ Finset.Icc 1 Z, ‖w n‖^2) =
      ∑ n ∈ Finset.Icc 1 Z, ‖v n‖^2 := by
    simp only [w,norm_mul,mellinPhase_norm,mul_one]
  rw [he]
  calc
    _ ≤ Real.exp 1*(∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z w t‖^2) :=
      gaussian_interval_majorant hL (by linarith) (by dsimp [L,c]; linarith)
        (by dsimp [L,c]; linarith) Z w
    _ ≤ Real.exp 1*((L*Real.sqrt Real.pi*(2/(1-Real.exp (-(1/4:ℝ)))))*
        ∑ n ∈ Finset.Icc 1 Z, ‖w n‖^2) :=
      mul_le_mul_of_nonneg_left (integerNormPolynomial_gaussian_meanSquare hL hZL w)
        (Real.exp_pos _).le
    _ = _ := by rw [henergy]; unfold ordinaryMeanValueConstant; dsimp [L]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaUpperMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative Mellin bounds on the exponentially decaying half of theta. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace CubicFirstMoment

lemma theta_mellin_exponent_bound {c t : ℝ} (hc : 0 < c) (ht : 1 ≤ t) (s : ℂ) :
    Real.log t * (s.re-1) - c*t ≤
      2*(1+‖s‖)^2/c - (c/2)*t := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hl0 := Real.log_nonneg ht
  have hl : Real.log t ≤ 2*Real.sqrt t := by
    have hh := Real.log_le_rpow_div ht0.le (show 0 < (1/2:ℝ) by norm_num)
    rw [← Real.sqrt_eq_rpow] at hh
    linarith
  have hr : s.re-1 ≤ 1+‖s‖ := by linarith [Complex.re_le_norm s]
  have h1 := mul_le_mul_of_nonneg_left hr hl0
  have h2 := mul_le_mul_of_nonneg_right hl (show 0 ≤ 1+‖s‖ by positivity)
  have hsq := sq_nonneg (c*Real.sqrt t - 2*(1+‖s‖))
  have hroot := Real.sq_sqrt ht0.le
  have hdiv : c*(2*(1+‖s‖)^2/c) = 2*(1+‖s‖)^2 :=
    mul_div_cancel₀ _ hc.ne'
  have hsq' : 0 ≤ c^2*t-4*c*(1+‖s‖)*Real.sqrt t+4*(1+‖s‖)^2 := by
    calc
      0 ≤ (c*Real.sqrt t - 2*(1+‖s‖))^2 := hsq
      _ = c^2*(Real.sqrt t)^2-4*c*(1+‖s‖)*Real.sqrt t+4*(1+‖s‖)^2 := by ring
      _ = _ := by rw [hroot]
  have hy : 2*(1+‖s‖)*Real.sqrt t ≤ c*t/2 + 2*(1+‖s‖)^2/c := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith only [hsq',hdiv]
  nlinarith

lemma theta_mellin_integrand_bound {f : ℝ → ℂ} {C c : ℝ}
    (hc : 0 < c) (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t))
    (s : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ‖(t:ℂ)^(s-1)*f t‖ ≤
      (C*Real.exp (2*(1+‖s‖)^2/c))*Real.exp (-(c/2)*t) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  calc
    _ ≤ t^((s-1).re)*(C*Real.exp (-c*t)) :=
      mul_le_mul_of_nonneg_left (hf t ht) (Real.rpow_nonneg ht0.le _)
    _ = C*Real.exp (Real.log t*(s.re-1)-c*t) := by
      rw [Real.rpow_def_of_pos ht0,Complex.sub_re,Complex.one_re,
        show Real.log t*(s.re-1)-c*t = Real.log t*(s.re-1)+(-c*t) by ring,Real.exp_add]
      ring
    _ ≤ C*Real.exp (2*(1+‖s‖)^2/c-(c/2)*t) := by
      have hC : 0 ≤ C := by
        have hh := (_root_.norm_nonneg (f 1)).trans (hf 1 le_rfl)
        exact nonneg_of_mul_nonneg_left hh (Real.exp_pos _)
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (theta_mellin_exponent_bound hc ht s)) hC
    _ = _ := by
      rw [show 2*(1+‖s‖)^2/c-(c/2)*t = 2*(1+‖s‖)^2/c+(-(c/2)*t) by ring, Real.exp_add]
      ring

lemma theta_upper_integrable {f : ℝ → ℂ} {C c : ℝ}
    (hc : 0 < c) (hfcont : ContinuousOn f (Ioi 0))
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t)) (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(s-1)*f t) (Ioi 1) := by
  have hg := (integrableOn_exp_mul_Ioi (show -(c/2) < 0 by linarith) 1).const_mul
    (C*Real.exp (2*(1+‖s‖)^2/c))
  apply hg.mono' _
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht =>
      theta_mellin_integrand_bound hc hf s ht.le))
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  apply ContinuousOn.mul _ (hfcont.mono (Ioi_subset_Ioi (by norm_num)))
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht0)).continuousWithinAt

lemma theta_upper_norm_bound {f : ℝ → ℂ} {C c : ℝ}
    (hc : 0 < c) (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t)) (s : ℂ) :
    ‖∫ t : ℝ in Ioi 1, (t:ℂ)^(s-1)*f t‖ ≤
      (2*C/c)*Real.exp (2*(1+‖s‖)^2/c) := by
  have hC : 0 ≤ C := by
    have hh := (_root_.norm_nonneg (f 1)).trans (hf 1 le_rfl)
    exact nonneg_of_mul_nonneg_left hh (Real.exp_pos _)
  calc
    _ ≤ ∫ t : ℝ in Ioi 1,
        (C*Real.exp (2*(1+‖s‖)^2/c))*Real.exp (-(c/2)*t) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_exp_mul_Ioi (show -(c/2) < 0 by linarith) 1).const_mul _)
      exact ae_restrict_of_forall_mem measurableSet_Ioi
        (fun t ht => theta_mellin_integrand_bound hc hf s ht.le)
    _ = (C*Real.exp (2*(1+‖s‖)^2/c))*(2/c)*Real.exp (-(c/2)) := by
      rw [integral_const_mul,integral_exp_mul_Ioi (show -(c/2) < 0 by linarith)]
      field_simp
    _ ≤ (C*Real.exp (2*(1+‖s‖)^2/c))*(2/c)*1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaMellinSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed theta Mellin transform as two rapidly convergent tails. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment

lemma mellin_thetaUpper (f : ℝ → ℂ) (s : ℂ) :
    mellin (thetaUpper f) s = ∫ t : ℝ in Ioi 1, (t:ℂ)^(s-1)*f t := by
  simp only [mellin,thetaUpper,← indicator_smul]
  rw [setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]
  rfl

lemma thetaUpper_mellinConvergent {f : ℝ → ℂ} {C c : ℝ}
    (hc : 0 < c) (hfcont : ContinuousOn f (Ioi 0))
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t)) (s : ℂ) :
    MellinConvergent (thetaUpper f) s := by
  simp only [MellinConvergent,thetaUpper,← indicator_smul]
  rw [IntegrableOn,integrable_indicator_iff measurableSet_Ioi]
  change Integrable _ ((volume.restrict (Ioi 0)).restrict (Ioi 1))
  rw [Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]
  exact theta_upper_integrable hc hfcont hf s

lemma theta_mellin_split {f g : ℝ → ℂ} {ε : ℂ}
    (hFE : ∀ t : ℝ, 0 < t → f (1/t) = ε*(t:ℂ)*g t)
    {s : ℂ} (hf : MellinConvergent (thetaUpper f) s)
    (hg : MellinConvergent (thetaUpper g) (1-s)) :
    mellin f s = mellin (thetaUpper f) s + ε*mellin (thetaUpper g) (1-s) := by
  let v : ℝ → ℂ := fun t => ε • ((t:ℂ)^(-1:ℂ) • thetaUpper g t⁻¹)
  have hginv : MellinConvergent (fun t : ℝ => thetaUpper g t⁻¹) (s-1) := by
    have he : (s-1)/(-1:ℝ) = 1-s := by push_cast; ring
    rw [← he] at hg
    simpa only [Real.rpow_neg_one] using
      (MellinConvergent.comp_rpow (by norm_num : (-1:ℝ) ≠ 0)).mpr hg
  have hv : MellinConvergent v s := by
    exact (MellinConvergent.cpow_smul.mpr (by simpa only [sub_eq_add_neg] using hginv)).const_smul ε
  have hid : f =ᵐ[volume.restrict (Ioi 0)] (fun t => thetaUpper f t + v t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      (volume.restrict (Ioi 0)).ae_ne 1] with t ht ht1
    change 0 < t at ht
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr hlt
      have ht' := hFE t⁻¹ (inv_pos.mpr ht)
      simp only [one_div,inv_inv,Complex.ofReal_inv] at ht'
      rw [thetaUpper,indicator_of_notMem (show t ∉ Ioi (1:ℝ) from not_lt.mpr hlt.le),zero_add]
      dsimp only [v]
      rw [thetaUpper,indicator_of_mem (show t⁻¹ ∈ Ioi (1:ℝ) from hinv),smul_eq_mul,smul_eq_mul,
        Complex.cpow_neg_one]
      simpa only [mul_assoc] using ht'
    · have hinv : t⁻¹ < 1 := (inv_lt_one₀ ht).mpr hgt
      rw [thetaUpper,indicator_of_mem (show t ∈ Ioi (1:ℝ) from hgt)]
      dsimp only [v]
      rw [thetaUpper,indicator_of_notMem (show t⁻¹ ∉ Ioi (1:ℝ) from not_lt.mpr hinv.le)]
      simp
  calc
    mellin f s = mellin (fun t => thetaUpper f t + v t) s := by
      apply integral_congr_ae
      filter_upwards [hid] with t ht
      rw [ht]
    _ = mellin (thetaUpper f) s + mellin v s := (hasMellin_add hf hv).2
    _ = _ := by
      dsimp only [v]
      rw [mellin_const_smul,mellin_cpow_smul,mellin_comp_inv]
      simp only [smul_eq_mul,show -(s+(-1:ℂ)) = 1-s by ring]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaMellinGrowth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic exponential growth bound derived from theta decay and inversion. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma theta_mellin_growth {f g : ℝ → ℂ} {ε : ℂ} {C D c : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfcont : ContinuousOn f (Ioi 0)) (hgcont : ContinuousOn g (Ioi 0))
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t))
    (hg : ∀ t : ℝ, 1 ≤ t → ‖g t‖ ≤ D*Real.exp (-c*t))
    (hFE : ∀ t : ℝ, 0 < t → f (1/t) = ε*(t:ℂ)*g t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ‖mellin f s‖ ≤ Real.exp (B*(1+‖s‖)^2) := by
  let K := 2*C/c+‖ε‖*(2*D/c)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K+8/c,by positivity,?_⟩
  intro s
  have hf' := thetaUpper_mellinConvergent hc hfcont hf s
  have hg' := thetaUpper_mellinConvergent hc hgcont hg (1-s)
  have hsplit := theta_mellin_split hFE hf' hg'
  have hfb := theta_upper_norm_bound hc hf s
  have hgb := theta_upper_norm_bound hc hg (1-s)
  have hn : 1+‖1-s‖ ≤ 2*(1+‖s‖) := by
    have hh := norm_sub_le (1:ℂ) s
    rw [norm_one] at hh
    linarith [_root_.norm_nonneg s]
  have hnsq : (1+‖1-s‖)^2 ≤ 4*(1+‖s‖)^2 := by
    have hh := pow_le_pow_left₀ (show 0 ≤ 1+‖1-s‖ by positivity) hn 2
    nlinarith
  have hexp : Real.exp (2*(1+‖1-s‖)^2/c) ≤ Real.exp ((8/c)*(1+‖s‖)^2) := by
    apply Real.exp_le_exp.mpr
    have hh : 2*(1+‖1-s‖)^2 ≤ 8*(1+‖s‖)^2 := by linarith
    convert div_le_div_of_nonneg_right hh hc.le using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hexp' : Real.exp (2*(1+‖s‖)^2/c) ≤ Real.exp ((8/c)*(1+‖s‖)^2) := by
    apply Real.exp_le_exp.mpr
    have hh : 2*(1+‖s‖)^2 ≤ 8*(1+‖s‖)^2 := by nlinarith [sq_nonneg (1+‖s‖)]
    convert div_le_div_of_nonneg_right hh hc.le using 1
    all_goals try with_reducible_and_instances rfl
    ring
  calc
    ‖mellin f s‖ ≤ ‖mellin (thetaUpper f) s‖+‖ε*mellin (thetaUpper g) (1-s)‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ = ‖mellin (thetaUpper f) s‖+‖ε‖*‖mellin (thetaUpper g) (1-s)‖ := by rw [norm_mul]
    _ ≤ (2*C/c)*Real.exp (2*(1+‖s‖)^2/c)+
        ‖ε‖*((2*D/c)*Real.exp (2*(1+‖1-s‖)^2/c)) := by
      rw [mellin_thetaUpper,mellin_thetaUpper]
      exact add_le_add hfb (mul_le_mul_of_nonneg_left hgb (_root_.norm_nonneg ε))
    _ ≤ K*Real.exp ((8/c)*(1+‖s‖)^2) := by
      calc
        _ ≤ (2*C/c)*Real.exp ((8/c)*(1+‖s‖)^2)+
            ‖ε‖*((2*D/c)*Real.exp ((8/c)*(1+‖s‖)^2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hexp' (by positivity))
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity))
              (_root_.norm_nonneg ε))
        _ = _ := by dsimp [K]; ring
    _ ≤ Real.exp K*Real.exp ((8/c)*(1+‖s‖)^2) :=
      mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp K)) (Real.exp_pos _).le
    _ ≤ Real.exp ((K+8/c)*(1+‖s‖)^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hq : 1 ≤ (1+‖s‖)^2 := one_le_pow₀ (by linarith [_root_.norm_nonneg s])
      nlinarith

lemma idealThetaFEPair_finiteOrder {A : ℝ} (hA : 0 < A)
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {ε : ℂ} (hε : ε ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealTheta A χ (1/t) = ε*(t:ℂ)*idealTheta A χdual t) :
    let P := idealThetaFEPair hA χ χdual hχ hχdual hε hFE
    CompletedHeckeFiniteOrder A (thetaHeckeL A P.Λ) := by
  dsimp only
  let P := idealThetaFEPair hA χ χdual hχ hχdual hε hFE
  have hP := idealThetaFEPair_strong hA χ χdual hχ hχdual hε hFE
  let C := ∑' ν : EisensteinIdealExponent, Real.exp (-idealExponentNorm ν/(2*A))
  have hC : 0 ≤ C := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hbound (ψ : EisensteinIdealExponent → ℂ) (hψ : ∀ ν, ‖ψ ν‖ ≤ 1)
      (t : ℝ) (ht : 1 ≤ t) :
      ‖idealTheta A ψ t‖ ≤ C*Real.exp (-(1/(2*A))*t) := by
    have he : -(1/(2*A))*t = -t/(2*A) := by ring
    simpa only [he] using idealTheta_norm_bound hA ψ hψ ht
  obtain ⟨B,hB,hBbound⟩ := theta_mellin_growth (show 0 < 1/(2*A) by positivity)
    hC hC (idealTheta_continuousOn hA χ hχ) (idealTheta_continuousOn hA χdual hχdual)
    (hbound χ hχ) (hbound χdual hχdual) hFE
  apply thetaHeckeL_finiteOrder hA hP.differentiable_Λ hB
  intro s
  rw [hP.Λ_eq]
  exact hBbound s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveResidueFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The perfect codifferent pairing on every Eisenstein residue ring.
Unlike the trace pairing without the different, this includes ramified moduli. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- Unit frequencies satisfy the exact Gauss eigenrelation for every modulus. -/
lemma residueCharacterFourier_unit (q : Eisenstein) (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ) (a : (Residues q)ˣ) :
    residueCharacterFourier q hq χ a =
      (star χ) a * gaussSum χ (residueFourierChar q hq) := by
  unfold residueCharacterFourier
  rw [gaussSum_mulShift_eq]
  rw [MulChar.star_eq_inv]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveResidueConductorKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitivity detects the kernel of every proper residue reduction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- Triviality on the reduction kernel constructs a genuine lower conductor. -/
lemma residueCharacter_induces_of_kernel {q d : Eisenstein} (hq : q ≠ 0)
    (hd : d ∣ q) (χ : MulChar (Residues q) ℂ)
    (hker : ∀ u : (Residues q)ˣ,
      Units.map (residueReduction hd).toMonoidHom u = 1 → χ u = 1) :
    ∃ ψ : MulChar (Residues d) ℂ, ResidueCharacterInduces q d χ ψ := by
  let f := Units.map (residueReduction hd).toMonoidHom
  have hk : f.ker ≤ χ.toUnitHom.ker := by
    intro u hu
    apply (MonoidHom.mem_ker).mpr
    apply Units.ext
    exact hker u hu
  let E := MonoidHom.liftOfSurjective f (residueReduction_units_surjective hq hd)
    ⟨χ.toUnitHom,hk⟩
  have hE : E.comp f = χ.toUnitHom := MonoidHom.liftOfRightInverse_comp ..
  refine ⟨MulChar.ofUnitHom E,hd,?_⟩
  intro x hx
  let u := (residue_isUnit_of_isCoprime hx).unit
  have hu : (u : Residues q) = Ideal.Quotient.mk (modulus q) x :=
    IsUnit.unit_spec _
  have he := congrArg (fun H => (H u : ℂ)) hE
  change ((E (f u) : ℂˣ) : ℂ) = χ (u : Residues q) at he
  rw [← MulChar.ofUnitHom_coe] at he
  change (MulChar.ofUnitHom E) (residueReduction hd (u : Residues q)) =
    χ (u : Residues q) at he
  rw [hu,residueReduction_mk] at he
  exact he

/-- A primitive character is nontrivial on each proper reduction kernel. -/
theorem primitiveResidue_nontrivial_kernel {q d : Eisenstein} (hq : q ≠ 0)
    (hd : d ∣ q) (hsmall : normNat d < normNat q)
    (χ : MulChar (Residues q) ℂ) (hχ : PrimitiveResidueCharacter q χ) :
    ∃ u : (Residues q)ˣ, Units.map (residueReduction hd).toMonoidHom u = 1 ∧ χ u ≠ 1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨ψ,hψ⟩ := residueCharacter_induces_of_kernel hq hd χ h
  exact (not_le_of_gt hsmall) (hχ d ψ hψ)

/-- A nonunit frequency is fixed by a unit on which a primitive character is
nontrivial. The smaller modulus is the quotient by one common prime factor. -/
lemma primitiveResidue_frequency_stabilizer {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : PrimitiveResidueCharacter q χ)
    (a : Residues q) (ha : ¬ IsUnit a) :
    ∃ u : (Residues q)ˣ, a * (u : Residues q) = a ∧ χ u ≠ 1 := by
  classical
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective a
  have hcop : ¬ IsCoprime q r := fun h => ha (residue_isUnit_of_isCoprime h)
  have hrel : ¬ IsRelPrime q r := fun h => hcop h.isCoprime
  rw [UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hq] at hrel
  push Not at hrel
  obtain ⟨p,hpq,hpr,hp⟩ := hrel
  obtain ⟨d,hd⟩ := hpq
  obtain ⟨k,hk⟩ := hpr
  have hd0 : d ≠ 0 := by intro h; simp [h] at hd; exact hq hd
  have hdp : d ∣ q := ⟨p, hd.trans (mul_comm p d)⟩
  have hpN : 1 < normNat p := by
    have hp0 := normNat_ne_zero hp.ne_zero
    have hp1 : normNat p ≠ 1 := by
      intro he
      apply hp.not_isUnit
      apply isUnit_of_norm_eq_one
      rw [← normNat_cast, he, Nat.cast_one]
    omega
  have hsmall : normNat d < normNat q := by
    rw [hd,normNat_mul]
    nlinarith [Nat.pos_of_ne_zero (normNat_ne_zero hd0)]
  obtain ⟨u,hu,hχu⟩ := primitiveResidue_nontrivial_kernel hq hdp hsmall χ hχ
  refine ⟨u,?_,hχu⟩
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (u : Residues q)
  have hxd : Ideal.Quotient.mk (modulus d) x = 1 := by
    have he := congrArg (fun v : (Residues d)ˣ => (v : Residues d)) hu
    change residueReduction hdp (u : Residues q) = 1 at he
    rw [← hx,residueReduction_mk] at he
    exact he
  have hdx : d ∣ x-1 := by
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change Ideal.Quotient.mk (modulus d) (x-1) = 0
    rw [map_sub,hxd,map_one,sub_self]
  have hdiv : q ∣ r*x-r := by
    obtain ⟨y,hy⟩ := hdx
    refine ⟨k*y,?_⟩
    rw [hd,hk]
    calc
      p*k*x-p*k = p*k*(x-1) := by ring
      _ = p*d*(k*y) := by rw [hy]; ring
  rw [← hx, ← map_mul]
  apply (sub_eq_zero.mp ?_)
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)

/-- The Fourier transform of a primitive residue character vanishes at every
nonunit frequency, including those at ramified factors of the modulus. -/
theorem primitiveResidueFourier_nonunit {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hχ : PrimitiveResidueCharacter q χ) (a : Residues q) (ha : ¬ IsUnit a) :
    residueCharacterFourier q hq χ a = 0 := by
  obtain ⟨u,hu,hχu⟩ := primitiveResidue_frequency_stabilizer hq χ hχ a ha
  have he := gaussSum_mulShift χ ((residueFourierChar q hq).mulShift a) u
  rw [AddChar.mulShift_mulShift, hu] at he
  exact eq_zero_of_mul_eq_self_left hχu he

/-- The complete Gauss eigenrelation holds with the actual zero extension of
the multiplicative character on nonunits. -/
theorem primitiveResidueFourier_eq {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hχ : PrimitiveResidueCharacter q χ) (a : Residues q) :
    residueCharacterFourier q hq χ a =
      (star χ) a * gaussSum χ (residueFourierChar q hq) := by
  by_cases ha : IsUnit a
  · obtain ⟨u,rfl⟩ := ha
    exact residueCharacterFourier_unit q hq χ u
  · rw [primitiveResidueFourier_nonunit hq χ hχ a ha, MulChar.map_nonunit _ ha, zero_mul]

/-- Finite Fourier inversion at the unit element. This identity only needs
the additive pairing to be perfect; the ring need not be a field. -/
lemma finite_gauss_fourier_at_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ∑ a : R, gaussSum χ (ψ.mulShift a) * ψ (-a) = Fintype.card R := by
  classical
  simp only [gaussSum, Finset.sum_mul, AddChar.mulShift_apply]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : R, χ x * ∑ a : R, ψ (a*(x-1)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← ψ.map_add_eq_mul]
      congr 2
      ring
    _ = ∑ x : R, χ x * (if x = 1 then (Fintype.card R : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [AddChar.sum_mulShift (x-1) hψ, sub_eq_zero]
      split_ifs <;> simp_all
    _ = Fintype.card R := by simp

/-- Exact square norm of the primitive residue Gauss sum, for arbitrary
nonzero Eisenstein modulus, including prime powers above three. -/
theorem primitiveResidueGauss_mul_conj {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hχ : PrimitiveResidueCharacter q χ) :
    gaussSum χ (residueFourierChar q hq) *
      star (gaussSum χ (residueFourierChar q hq)) = (normNat q : ℂ) := by
  have hi := finite_gauss_fourier_at_one χ (residueFourierChar q hq)
    (residueFourierChar_isPrimitive q hq)
  change (∑ a : Residues q, residueCharacterFourier q hq χ a *
    residueFourierChar q hq (-a)) = _ at hi
  simp_rw [primitiveResidueFourier_eq hq χ hχ, MulChar.star_apply,
    AddChar.map_neg_eq_conj] at hi
  change (∑ a : Residues q, star (χ a) *
    gaussSum χ (residueFourierChar q hq) * star (residueFourierChar q hq a)) = _ at hi
  have he : (∑ a : Residues q, star (χ a) *
      gaussSum χ (residueFourierChar q hq) * star (residueFourierChar q hq a)) =
      gaussSum χ (residueFourierChar q hq) *
        star (gaussSum χ (residueFourierChar q hq)) := by
    change (∑ a : Residues q, star (χ a) *
      gaussSum χ (residueFourierChar q hq) * star (residueFourierChar q hq a)) =
      gaussSum χ (residueFourierChar q hq) *
        star (∑ a : Residues q, χ a * residueFourierChar q hq a)
    rw [star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [star_mul]
    ring
  rw [he] at hi
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Nat.card_eq_fintype_card, residues_card hq]

/-- Positive real norm of the primitive Gauss sum. -/
theorem primitiveResidueGauss_norm {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hχ : PrimitiveResidueCharacter q χ) :
    ‖gaussSum χ (residueFourierChar q hq)‖ = Real.sqrt (normNat q : ℝ) := by
  have hi := congrArg Complex.re (primitiveResidueGauss_mul_conj hq χ hχ)
  have hs : ‖gaussSum χ (residueFourierChar q hq)‖^2 = (normNat q : ℝ) := by
    have hc := Complex.mul_conj' (gaussSum χ (residueFourierChar q hq))
    change gaussSum χ (residueFourierChar q hq) *
      star (gaussSum χ (residueFourierChar q hq)) = _ at hc
    rw [hc] at hi
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.natCast_re] using hi
  rw [← hs, Real.sqrt_sq (_root_.norm_nonneg _)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueFourierBridge
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Fourier coefficient occurring in lattice Poisson is exactly
the Gauss transform for the primitive inverse-different additive character. -/
noncomputable section
namespace CubicFirstMoment

lemma residueFiniteFourier_eq_characterFourier {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ) (h : Eisenstein) :
    residueFiniteFourier q χ h =
      residueCharacterFourier q hq χ (Ideal.Quotient.mk (modulus q) h) := by
  unfold residueFiniteFourier residueCharacterFourier gaussSum
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro v _
  apply congrArg (fun z : ℂ => χ v*z)
  rw [AddChar.mulShift_apply]
  have hv : v = Ideal.Quotient.mk (modulus q) (residueRepresentative q v) :=
    (residueRepresentative_spec q v).symm
  conv_rhs => rw [hv,←map_mul,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueThetaCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact analytic completion of a residue theta transformation. The
finite-character Poisson identity is the only remaining construction here;
no continuation, growth, or Dirichlet-series identity is assumed. -/
noncomputable section
namespace CubicFirstMoment

lemma residueTheta_completion {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) {root : ℂ} (hroot : root ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealTheta (residueHeckeScale q) (residueIdealChar q χ) (1/t) =
        root*(t:ℂ)*idealTheta (residueHeckeScale q) (residueIdealChar q (star χ)) t) :
    ∃ L Ldual : ℂ → ℂ, Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s = normDirichletSeries (residueIdealChar q χ) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries (residueIdealChar q (star χ)) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale q) 0 root L Ldual ∧
      CompletedHeckeFiniteOrder (residueHeckeScale q) L := by
  have hA := residueHeckeScale_pos hq
  have hχ := residueIdealChar_norm_le_one hq χ
  have hd := residueIdealChar_norm_le_one hq (star χ)
  let P := idealThetaFEPair hA (residueIdealChar q χ) (residueIdealChar q (star χ)) hχ hd hroot hFE
  have he := idealThetaFEPair_hecke hA (residueIdealChar q χ) (residueIdealChar q (star χ)) hχ hd hroot hFE
  exact ⟨thetaHeckeL (residueHeckeScale q) P.Λ,
    thetaHeckeL (residueHeckeScale q) P.symm.Λ,he.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2,
    idealThetaFEPair_finiteOrder hA (residueIdealChar q χ) (residueIdealChar q (star χ)) hχ hd hroot hFE⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueHeckeFromFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The primitive Hecke completion constructed from the finite Gauss Fourier
computation. This bridge assumes no analytic continuation or growth result. -/
noncomputable section
namespace CubicFirstMoment

lemma residueLatticeTheta_inversion_from_fourier {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (G : ℂ)
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h)) :
    ∀ t : ℝ, 0 < t → residueLatticeTheta q χ (residueHeckeScale q) (1/t) =
      (G/(Real.sqrt (norm q):ℝ))*(t:ℂ)*residueLatticeTheta q (star χ) (residueHeckeScale q) t := by
  intro t ht
  rw [residueGaussian_selfDual hq χ (one_div_pos.mpr ht)]
  simp_rw [hFourier]
  have he (h : Eisenstein) : -norm h/(residueHeckeScale q*(1/t)) = -norm h*t/residueHeckeScale q := by
    field_simp
  simp_rw [he,mul_assoc]
  rw [tsum_mul_left]
  change ((1/(Real.sqrt (norm q)*(1/t)):ℝ):ℂ) * (G * residueLatticeTheta q (star χ) (residueHeckeScale q) t) = _
  push_cast
  field_simp

lemma residueHecke_from_finiteFourier {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hn : χ ≠ 1)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    (G : ℂ) (hG : ‖G‖ = Real.sqrt (norm q))
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h)) :
    ∃ (root : ℂ) (L Ldual : ℂ → ℂ), ‖root‖ = 1 ∧ Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s = normDirichletSeries (residueIdealChar q χ) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries (residueIdealChar q (star χ)) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale q) 0 root L Ldual ∧
      CompletedHeckeFiniteOrder (residueHeckeScale q) L := by
  let : Nontrivial (Residues q) := residue_nontrivial_of_nonprincipal χ hn
  let root : ℂ := G/(Real.sqrt (norm q):ℝ)
  have hs : 0 < Real.sqrt (norm q) := Real.sqrt_pos.mpr (norm_pos_of_ne_zero hq)
  have hr : ‖root‖ = 1 := by
    dsimp [root]
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),hG,div_self hs.ne']
  have hr0 : root ≠ 0 := by intro he; rw [he,norm_zero] at hr; norm_num at hr
  have hd (u : Eisensteinˣ) : (star χ) (Ideal.Quotient.mk (modulus q) u) = 1 := by
    rw [MulChar.star_apply,hu,star_one]
  have hFE := residueTheta_inversion_of_lattice hq χ hu hd (residueHeckeScale_pos hq)
    (residueLatticeTheta_inversion_from_fourier hq χ G hFourier)
  obtain ⟨L,Ldual,hL,hseries,hdual,hfunctional,horder⟩ := residueTheta_completion hq χ hr0 hFE
  exact ⟨root,L,Ldual,hr,hL,hseries,hdual,hfunctional,horder⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveHeckeProof
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive finite and fixed-angular Hecke continuation derived from
finite Gauss orthogonality and the actual Gaussian Poisson formula. -/
noncomputable section
namespace CubicFirstMoment

private lemma primitive_poisson_gauss_norm {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hp : PrimitiveResidueCharacter q χ) :
    ‖gaussSum χ (residueFourierChar q hq)‖ = Real.sqrt (norm q) := by
  simpa only [normNat_cast] using primitiveResidueGauss_norm hq χ hp

private lemma primitive_poisson_gauss_fourier {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hp : PrimitiveResidueCharacter q χ) (h : Eisenstein) :
    residueFiniteFourier q χ h =
      gaussSum χ (residueFourierChar q hq)*(star χ) (Ideal.Quotient.mk (modulus q) h) := by
  rw [residueFiniteFourier_eq_characterFourier hq χ h,primitiveResidueFourier_eq hq χ hp,mul_comm]

theorem primitiveResidueHeckeInput_proved : PrimitiveResidueHeckeInput := by
  intro q hq χ hp hn hu
  let : Finite (Residues q) := finite_residues hq
  let : Fintype (Residues q) := Fintype.ofFinite _
  exact residueHecke_from_finiteFourier hq χ hn hu
    (gaussSum χ (residueFourierChar q hq)) (primitive_poisson_gauss_norm hq χ hp)
    (primitive_poisson_gauss_fourier hq χ hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTransformBounds
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the literal angular Voronoi transform. Its Gamma quotient
is a product of two ordinary shifted Hecke quotients, so the only
special-function input is the same precise DLMF bounded-strip estimate. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplecticAngularShift_nonneg (ℓ : ℤ) : 0 ≤ metaplecticAngularShift ℓ := by
  unfold metaplecticAngularShift
  positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered prime comparison from the constructed arithmetic theta
transform, the actual low-height bounds and the actual high-height tails.
No published analytic input is retained as a hypothesis. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

lemma cubicTheta_primeProductLowHeight_isLittleO_oai (ℓ : ℤ) (Ct : ℕ)
    (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop,0<H X) :
    (fun X => primeProductLowHeight ℓ (H X) ((1+Real.log X)^Ct) X)
      =o[atTop] firstMomentScale := by
  have hGI (m : ℕ) : GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2) :=
    gammaInverseFiniteOrder _ _
  have hGQ (m : ℕ) : AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)) := by
    apply angularGammaQuotientStripBound_proved
    have hp : 0≤|(ℓ:ℝ)|/2 := by positivity
    linarith
  have hGamma (k : ℤ) (σ : ℝ) (_hσ : 0<σ) (_hs : σ<1/10000) :
      AngularGammaQuotientStripBound (metaplecticAngularShift k) (-σ-1/6) := by
    apply angularGammaQuotientStripBound_proved
    linarith [metaplecticAngularShift_nonneg k]
  by_cases hℓ : ℓ=0
  · subst ℓ
    have hGI0 (m : ℕ) : GammaInverseFiniteOrder (1/2-(m:ℝ)) 2 := by
      simpa only [Int.cast_zero,abs_zero,zero_div,add_zero] using hGI m
    have hGQ0 (m : ℕ) : GammaQuotientStripBound (1/2-(m:ℝ)) := by
      simpa only [Int.cast_zero,abs_zero,zero_div,AngularGammaQuotientStripBound,
        GammaQuotientStripBound,angularGammaFEQuotient,gammaFEQuotient,
        Complex.ofReal_zero,add_zero] using hGQ m
    exact primeProductLowHeight_radial_isLittleO_actual (ξ:=1/1000)
      primaryPrimePNT_proved (kummerPrimeSiegelWalfisz_of_primitive primitiveResidueHeckeInput_proved)
      primitiveResidueHeckeInput_proved huxleyAdditiveLargeSieve_proved
      cubicSupplementaryPeriodicity_proved montgomeryVaughanBound_proved
      ordinaryMeanValueConstant_pos.le (by norm_num) (by norm_num) hGI0 hGQ0 (hGamma 0) Ct H hH
  · exact primeProductLowHeight_angular_isLittleO_actual ℓ (ξ:=1/1000)
      primaryPrimePNT_proved (angularKummerPrimeExplicitEstimate_of_primitive primitiveAngularHeckeInput_proved)
      hℓ primitiveAngularHeckeInput_proved huxleyAdditiveLargeSieve_proved
      cubicSupplementaryPeriodicity_proved montgomeryVaughanBound_proved
      ordinaryMeanValueConstant_pos.le (by norm_num) (by norm_num) hGI hGQ
      (hGamma 0) (hGamma ℓ) Ct H hH

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.cubicTheta_primeProductLowHeight_isLittleO_oai := @OAI.CubicFirstMoment.cubicTheta_primeProductLowHeight_isLittleO_oai
