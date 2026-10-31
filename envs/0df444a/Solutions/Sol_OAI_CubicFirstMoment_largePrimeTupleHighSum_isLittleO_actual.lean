-- Prove2me | solution 1 for OAI.CubicFirstMoment.largePrimeTupleHighSum_isLittleO_actual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:40:13.067109+00:00
-- url     : https://prove2.me/submissions/f494e457-407c-4dc4-8ed2-cf050839d3bf

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A016
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_full_prime_centered_product_bilinear_actual
import Theorems.Thm_OAI_CubicFirstMoment_full_prime_product_height_bilinear
import Theorems.Thm_OAI_CubicFirstMoment_largePrimeTupleOrdinaryHighSum_isLittleO_actual
import Theorems.Thm_OAI_CubicFirstMoment_largePrimeTupleSelectedFlatHighSum_isLittleO

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composite residue characters, Chinese remainders and squarefree Gauss norms. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

theorem norm_gauss {b : Eisenstein} (hb : primary b) :
    ‖gauss b‖ = if Squarefree b then 1 else 0 := by
  split_ifs with hs
  · exact norm_gauss_of_squarefree hb hs
  · rw [gauss_eq_zero_of_not_squarefree hb hs, norm_zero]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularAlgebra
attribute [-instance] _root_.instMeasurableSpace
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

/-- The bias constant in the manuscript is strictly positive. -/
theorem cStar_pos : 0 < cStar := by
  unfold cStar
  positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem smooth_mellin_vertical_decay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      (1+|t|)^A * ‖mellin W (σ + (t : ℂ)*Complex.I)‖ ≤ C := by
  let F := mellinVerticalSchwartz W hW hpos hsm σ
  let C := 2^A * (Finset.Iic (A,0)).sup
    (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  refine ⟨C+1,by dsimp [C]; positivity,?_⟩
  intro t
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (A,0)) (k := A) (n := 0) le_rfl le_rfl F t
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb
  rw [← mellinVerticalSchwartz_apply W hW hpos hsm σ t]
  exact hb.trans (by dsimp [C]; linarith)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem norm_gauss_le_one {a : Eisenstein} (ha : primary a) : ‖gauss a‖ ≤ 1 := by
  rw [norm_gauss ha]
  split_ifs <;> norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticUniformWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform support, size and far-left transform bounds from the actual
logarithmic derivative hypotheses on the weight family. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma UniformLogWeights.upper_support {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∀ i x, Real.exp h.radius < x → W i x = 0 := by
  intro i x hx
  by_contra hn
  have hxp : 0 < x := (Real.exp_pos _).trans hx
  have hu : -Real.log x ∈ tsupport (fun u : ℝ => W i (Real.exp (-u))) := by
    apply subset_tsupport
    change W i (Real.exp (-(-Real.log x))) ≠ 0
    simpa only [neg_neg,Real.exp_log hxp] using hn
  have hb := h.support_bound i (-Real.log x) hu
  have hl : Real.log x ≤ h.radius := by
    rw [abs_neg] at hb
    exact (le_abs_self _).trans hb
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log hxp] at he
  exact (not_lt_of_ge he) hx

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLatticeModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual squarefree angular model in the low Type-I argument.
Its norm factor is absorbed into the test function, and its cancellation
is obtained from the proved primary-lattice estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealMoebius_sq_complex (u : Eisenstein) :
    (idealMoebius u:ℂ)^2 = if Squarefree u then 1 else 0 := by
  exact_mod_cast idealMoebius_sq u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_KernelScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scaling a cutoff kernel

The normalization and weighted L¹ moment are preserved under `T k(Tx)`.
Thus a single Schwartz kernel gives a uniform family of interval
approximations at all positive truncation heights.
-/

noncomputable section
open MeasureTheory

namespace CubicFirstMoment

theorem integrable_scaledKernel {k : ℝ → ℂ} (hk : Integrable k)
    {T : ℝ} (hT : 0 < T) : Integrable (scaledKernel k T) :=
  (hk.comp_mul_left' hT.ne').const_mul (T : ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FourierCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A concrete Fourier cutoff kernel

The fixed cutoff is a smooth bump, one near zero and supported in [-1,1].
Its inverse Fourier transform is a normalized Schwartz kernel. Mathlib
uses exp(2π i x ξ); this frequency variable differs by 2π from the
height variable in the manuscript.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform

namespace CubicFirstMoment

theorem frequencyCutoff_apply (x : ℝ) : frequencyCutoff x = (frequencyBump x : ℂ) := rfl

theorem frequencyCutoff_zero {x : ℝ} (hx : 1 ≤ |x|) : frequencyCutoff x = 0 := by
  rw [frequencyCutoff_apply, frequencyBump.zero_of_le_dist]
  · rfl
  · simpa only [Real.dist_eq, sub_zero, frequencyBump] using hx

/-- Inversion identifies the Fourier transform with the actual compact cutoff. -/
theorem fourier_truncationKernel : 𝓕 truncationKernel = frequencyCutoff :=
  fourier_fourierInv_eq frequencyCutoff

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FourierSmoothing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Frequency support of the concrete interval smoothing

The convolution has Fourier transform equal to the interval transform
times the actual compactly supported cutoff. This connects the physical
endpoint bounds with truncation in the height variable.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform Convolution

namespace CubicFirstMoment

/-- Dilation of the kernel dilates its Fourier support by exactly the same factor. -/
theorem fourier_scaledKernel (k : ℝ → ℂ) {T : ℝ} (hT : 0 < T) (ξ : ℝ) :
    𝓕 (scaledKernel k T) ξ = 𝓕 k (ξ/T) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  let f : ℝ → ℂ := fun y => Complex.exp ((-2 * Real.pi * y * (ξ/T) : ℝ) * Complex.I) * k y
  have he : (fun y => Complex.exp ((-2 * Real.pi * y * ξ : ℝ) * Complex.I) *
      scaledKernel k T y) = (fun y => (T : ℂ) * f (T*y)) := by
    funext y
    have he : -2 * Real.pi * (T*y) * (ξ/T) = -2 * Real.pi * y * ξ := by field_simp
    simp only [f, scaledKernel, he]
    ring
  rw [he, integral_const_mul, Measure.integral_comp_mul_left]
  simp only [abs_of_pos (inv_pos.mpr hT), Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, mul_inv_cancel₀ hT.ne', Complex.ofReal_one, one_mul, f]

theorem integrable_intervalStep (a b : ℝ) :
    Integrable (fun x => (intervalStep a b x : ℂ)) := by
  have h : Integrable ((Set.Icc a b).indicator (fun _ : ℝ => (1 : ℂ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const isCompact_Icc.measure_ne_top)
  have he : (fun x => (intervalStep a b x : ℂ)) =
      (Set.Icc a b).indicator (fun _ : ℝ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b <;>
      simp only [intervalStep, Set.indicator_apply, hx, ite_true, if_true, ite_false, if_false,
        Complex.ofReal_one, Complex.ofReal_zero]
  rwa [he]

theorem intervalSmoothing_eq_convolution (k : ℝ → ℂ) (a b : ℝ) :
    intervalSmoothing k a b = k ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (fun x => (intervalStep a b x : ℂ)) := by
  funext s
  simp only [intervalSmoothing, convolution_def, ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

/-- The exact Fourier multiplier of the interval approximation. -/
theorem fourier_intervalSmoothing {T : ℝ} (hT : 0 < T) (a b ξ : ℝ) :
    𝓕 (intervalSmoothing (scaledKernel truncationKernel T) a b) ξ =
      frequencyCutoff (ξ/T) * 𝓕 (fun x => (intervalStep a b x : ℂ)) ξ := by
  rw [intervalSmoothing_eq_convolution,
    Real.fourier_mul_convolution_eq (integrable_scaledKernel truncationKernel.integrable hT)
      (integrable_intervalStep a b), fourier_scaledKernel _ hT]
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => f (ξ/T)) fourier_truncationKernel
  rw [SchwartzMap.fourier_coe] at h
  rw [h]

/-- No frequencies beyond the prescribed truncation height survive. -/
theorem fourier_intervalSmoothing_zero {T : ℝ} (hT : 0 < T) (a b ξ : ℝ)
    (hξ : T ≤ |ξ|) :
    𝓕 (intervalSmoothing (scaledKernel truncationKernel T) a b) ξ = 0 := by
  rw [fourier_intervalSmoothing hT, frequencyCutoff_zero, zero_mul]
  rw [abs_div, abs_of_pos hT]
  exact (le_div_iff₀ hT).mpr (by simpa using hξ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CutoffInversion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral representation of the interval cutoff

The same concrete smoothing used for the proved endpoint error is the
inverse Fourier integral of its compactly supported frequency multiplier.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform Convolution

namespace CubicFirstMoment

private theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) hf

theorem integrable_concrete_intervalSmoothing {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    Integrable (intervalSmoothing (scaledKernel truncationKernel T) a b) := by
  rw [intervalSmoothing_eq_convolution]
  exact (integrable_scaledKernel truncationKernel.integrable hT).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_intervalStep a b)

theorem integrable_fourier_intervalSmoothing {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    Integrable (𝓕 (intervalSmoothing (scaledKernel truncationKernel T) a b)) := by
  have hc := continuous_fourier_of_integrable (integrable_concrete_intervalSmoothing hT a b)
  have hs : HasCompactSupport (𝓕 (intervalSmoothing (scaledKernel truncationKernel T) a b)) := by
    apply HasCompactSupport.intro' (K := Set.Icc (-T) T) isCompact_Icc isClosed_Icc
    intro ξ hξ
    apply fourier_intervalSmoothing_zero hT
    simp only [Set.mem_Icc, not_and_or, not_le] at hξ
    rcases hξ with hξ | hξ
    · linarith [neg_abs_le ξ]
    · exact hξ.le.trans (le_abs_self ξ)
  exact hc.integrable_of_hasCompactSupport hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IntervalTransform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The interval Fourier multiplier

Evaluation of the interval transform gives the two endpoint terms divided
by frequency. The value at zero is the interval length, so there is no
singularity in the original multiplier.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform

namespace CubicFirstMoment

theorem fourier_intervalStep_eq_integral {a b : ℝ} (hab : a ≤ b) (ξ : ℝ) :
    𝓕 (fun x => (intervalStep a b x : ℂ)) ξ =
      ∫ x in a..b, Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun x : ℝ => Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I) •
      (intervalStep a b x : ℂ)) = (Set.Icc a b).indicator
        (fun x => Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I)) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b <;>
      simp only [intervalStep, Set.indicator_apply, hx, ite_true, if_true, ite_false, if_false,
        Complex.ofReal_one, Complex.ofReal_zero, smul_eq_mul, mul_one, mul_zero]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeightBounds
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The height weight in the truncated Mellin integral

The interval transform has the expected `1/(1+|ξ|)` bound, including
at frequency zero. The cutoff and the scaling phase have norm at most one.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace CubicFirstMoment

lemma norm_dyadicFourierMultiplier_le_log (ξ : ℝ) :
    ‖dyadicFourierMultiplier ξ‖ ≤ Real.log 2 := by
  unfold dyadicFourierMultiplier
  rw [fourier_intervalStep_eq_integral (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := Real.log 2) (C := (1 : ℝ))
    (f := fun x => Complex.exp ((-2*Real.pi*x*ξ : ℝ)*Complex.I))
    (fun x _ => (Complex.norm_exp_ofReal_mul_I _).le)
  simpa only [sub_zero, abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)),
    one_mul] using h

lemma norm_frequencyCutoff_le_one (ξ : ℝ) : ‖frequencyCutoff ξ‖ ≤ 1 := by
  rw [frequencyCutoff_apply,Complex.norm_real,Real.norm_of_nonneg frequencyBump.nonneg]
  exact frequencyBump.le_one

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CenteredPrimeKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the decomposition kernel with the paper's prime
comparison, including the actual common-height Mellin polynomial. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma centeredGauss_vanishes {n : Eisenstein} (hn : primary n) (hs : ¬Squarefree n) :
    centeredGauss n = 0 := by
  have hg : gauss n = 0 := norm_eq_zero.mp (by rw [norm_gauss hn,ite_eq_right hs])
  rw [centeredGauss,hg,idealMoebius_sq_complex,ite_eq_right hs]
  simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma normPartitionWeight_scale (k : ℕ) (x : ℝ) :
    normPartitionWeight (2*x/(4/3:ℝ)^k) =
      normPartitionWeight (x/((4/3:ℝ)^k/2)) := by
  congr 1
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteMellinProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothShortContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothTuplePartition
attribute [-instance] _root_.instMeasurableSpace
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

lemma normPartitionWeight_nonzero_scale {x : ℝ} {k : ℕ}
    (h : normPartitionWeight (2*x/(4/3:ℝ)^k) ≠ 0) :
    x ≤ (4/3:ℝ)^k ∧ (4/3:ℝ)^k ≤ 2*x := by
  have hp : 0 < (4/3:ℝ)^k := pow_pos (by norm_num) _
  have hlo : 1 ≤ 2*x/(4/3:ℝ)^k := by
    by_contra hn
    exact h (normPartitionWeight_low (lt_of_not_ge hn))
  have hhi : 2*x/(4/3:ℝ)^k ≤ 2 := by
    by_contra hn
    exact h (normPartitionWeight_high (lt_of_not_ge hn))
  constructor
  · have := (div_le_iff₀ hp).mp hhi
    linarith
  · have := (le_div_iff₀ hp).mp hlo
    linarith

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullStructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramMellinTwist
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion of the existing Poisson/Mellin kernel's Fourier
frequency to the norm heights used by the proved structured moments. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellinPhase_add_height (u v x : ℝ) :
    mellinPhase (u+v) x = mellinPhase u x*mellinPhase v x := by
  unfold mellinPhase
  rw [show (((u+v)*Real.log x:ℝ):ℂ)*Complex.I =
    ((u*Real.log x:ℝ):ℂ)*Complex.I+((v*Real.log x:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticBilinearMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation of the actual varying outer weights in a
finite bilinear Gauss sum. All integrability follows from smooth support. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma metaplectic_mellin_term_integrable (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {V x : ℝ} (hV : 0 < V) (_hx : 0 < x) (a : ℂ) :
    Integrable (fun t : ℝ => zeroLineMellinWeight W V t*(a*mellinPhase (-t) x)) := by
  apply (zeroLineMellinWeight_integrable W hW hpos hsm hV).mul_bdd
    (c := ‖a‖)
  · have hc : Continuous (fun t : ℝ => a*mellinPhase (-t) x) := by
      unfold mellinPhase
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards with t
    simp [mellinPhase,Complex.norm_exp]

lemma metaplectic_mellin_term (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {V x : ℝ} (hV : 0 < V) (hx : 0 < x) (a : ℂ) :
    a*W (x/V) = ∫ t : ℝ, zeroLineMellinWeight W V t*(a*mellinPhase (-t) x) := by
  have h := smooth_mellin_finite (fun _ : Unit => a) (fun _ : Unit => x)
    (fun _ => hx) W hW hpos hsm 0 hV
  simp only [Fintype.sum_unique,Complex.ofReal_zero,zero_add] at h
  rw [h,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [mellinPhase_eq_cpow hx]
  have he : ((-t:ℝ):ℂ)*Complex.I = -((t:ℂ)*Complex.I) := by push_cast; ring
  rw [he]
  unfold zeroLineMellinWeight
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CenteredProductMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation of the smooth total-product factor in a
centered bilinear Gauss sum. The norm height is shifted by the true Mellin
frequency, and absolute integrability follows from the smooth weight. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem centered_product_mellin (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (hA : ∀ a ∈ A, primary a) (hB : ∀ b ∈ B, primary b)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (u : ℝ) :
    centeredProductSmoothed A B α β ℓ W X u =
      ∫ τ : ℝ, zeroLineMellinWeight W X τ*centeredProductPolynomial A B α β ℓ (u-τ) := by
  let c := fun a b => α a*β b*theta ℓ (a*b)*centeredGauss (a*b)*normTwist u (a*b)
  let f := fun a b τ => zeroLineMellinWeight W X τ*(c a b*mellinPhase (-τ) (norm (a*b)))
  have hp (a : Eisenstein) (ha : a ∈ A) (b : Eisenstein) (hb : b ∈ B) :
      0 < norm (a*b) := norm_pos_of_ne_zero
        (mul_ne_zero (primary_ne_zero (hA a ha)) (primary_ne_zero (hB b hb)))
  have hi (a : Eisenstein) (ha : a ∈ A) (b : Eisenstein) (hb : b ∈ B) :
      Integrable (f a b) := metaplectic_mellin_term_integrable W hW hpos hsm hX (hp a ha b hb) (c a b)
  calc
    _ = ∑ a ∈ A, ∑ b ∈ B, ∫ τ : ℝ, f a b τ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact metaplectic_mellin_term W hW hpos hsm hX (hp a ha b hb) (c a b)
    _ = ∫ τ : ℝ, ∑ a ∈ A, ∑ b ∈ B, f a b τ := by
      rw [integral_finsetSum A (fun a ha => integrable_finsetSum B (hi a ha))]
      apply Finset.sum_congr rfl
      intro a ha
      exact (integral_finsetSum B (hi a ha)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with τ
      simp only [centeredProductPolynomial,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [f,c]
      rw [sub_eq_add_neg,normTwist_eq_mellinPhase,normTwist_eq_mellinPhase,mellinPhase_add_height]
      ring

theorem centered_product_mellin_integrable (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X : ℝ} (hX : 0 < X) (u : ℝ) :
    Integrable (fun τ : ℝ => zeroLineMellinWeight W X τ*
      centeredProductPolynomial A B α β ℓ (u-τ)) := by
  apply (zeroLineMellinWeight_integrable W hW hpos hsm hX).mul_bdd
    (c := ∑ a ∈ A, ∑ b ∈ B, ‖α a*β b*theta ℓ (a*b)*centeredGauss (a*b)‖)
  · have hc : Continuous (fun τ : ℝ => centeredProductPolynomial A B α β ℓ (u-τ)) := by
      unfold centeredProductPolynomial normTwist
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards with τ
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro b _
    rw [norm_mul,norm_normTwist,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramStructuredRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeNormRange
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeMellinEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeSlice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact quotient support for divisor-restricted prime coefficients.
No independent-prime condition is asserted for the shortened coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeCoefficient_norm_bound (R : ℝ) (W : ι → ℝ → ℂ) (X M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (b : Eisenstein) :
    ‖fullPrimeCoefficient R W X b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  by_cases hs : Squarefree b
  · simpa only [fullPrimeCoefficient,squarefreeConvolution,ite_eq_left hs] using
      orderedConvolution_norm_bound (fullPrimeSupport R W X)
        (fun i n => W i (norm n/X i)) M
        (fun i p hp => fullPrimeSupport_prime R W X i p hp) hM
        (fun i p _ => hW i _) b
  · simp only [fullPrimeCoefficient,squarefreeConvolution,ite_eq_right hs,norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductPolynomialBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Height-independent bounds for the actual two full prime convolutions.
These are used only beyond the power range of the published height mean. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma fullPrimeCoefficient_l1_unit {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hW : ∀ i x, ‖W i x‖ ≤ 1) (e : Eisenstein) :
    (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖) ≤
      primeCoefficientMassConstant R (Fintype.card ι)*(∏ i, X i) := by
  have hb (b : Eisenstein) : ‖fullPrimeCoefficient R W X b‖ ≤ ((Fintype.card ι)^(Fintype.card ι):ℕ) := by
    simpa using fullPrimeCoefficient_norm_bound R W X (fun _ => 1)
      (fun _ => by norm_num) hW b
  calc
    _ ≤ ∑ _b ∈ fullSquarefreePrimeSupport R W X e,
        (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ) := Finset.sum_le_sum (fun b _ => hb b)
    _ = ((fullSquarefreePrimeSupport R W X e).card:ℝ)*
        (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ) := by simp
    _ ≤ (18*(R^Fintype.card ι*(∏ i, X i)))*
        (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ) :=
      mul_le_mul_of_nonneg_right (fullPrimeSupport_card_bound hR W X hX hlo hhi e) (by positivity)
    _ = _ := by unfold primeCoefficientMassConstant; ring

lemma fullPrimeProduct_centered (R : ℝ) (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ)
    (XA : κ → ℝ) (XB : ι → ℝ) (u : ℝ) :
    centeredProductPolynomial (fullSquarefreePrimeSupport R WA XA 1)
      (fullSquarefreePrimeSupport R WB XB 1)
      (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) 0 u =
      fullPrimeProductGauss R WA WB XA XB u-fullPrimeProductModel R WA WB XA XB u := by
  unfold centeredProductPolynomial fullPrimeProductGauss fullPrimeProductModel
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  simp only [theta_zero, mul_one,centeredGauss]
  ring

lemma fullPrimeProduct_weighted_bound (R : ℝ) (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ)
    (XA : κ → ℝ) (XB : ι → ℝ) {M : ℝ}
    (F : Eisenstein → Eisenstein → ℂ)
    (hF : ∀ a ∈ fullSquarefreePrimeSupport R WA XA 1,
      ∀ b ∈ fullSquarefreePrimeSupport R WB XB 1, ‖F a b‖ ≤ M) :
    ‖∑ a ∈ fullSquarefreePrimeSupport R WA XA 1,
      ∑ b ∈ fullSquarefreePrimeSupport R WB XB 1,
        fullPrimeCoefficient R WA XA a*fullPrimeCoefficient R WB XB b*F a b‖ ≤
      (∑ a ∈ fullSquarefreePrimeSupport R WA XA 1, ‖fullPrimeCoefficient R WA XA a‖)*
        (∑ b ∈ fullSquarefreePrimeSupport R WB XB 1, ‖fullPrimeCoefficient R WB XB b‖)*M := by
  calc
    _ ≤ ∑ a ∈ fullSquarefreePrimeSupport R WA XA 1,
        ∑ b ∈ fullSquarefreePrimeSupport R WB XB 1,
          ‖fullPrimeCoefficient R WA XA a‖*‖fullPrimeCoefficient R WB XB b‖*M := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul,norm_mul]
      exact mul_le_mul_of_nonneg_left (hF a ha b hb) (by positivity)
    _ = _ := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]

lemma fullPrimeProductGauss_bound {R : ℝ} (hR : 0 ≤ R)
    (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
    (hXA : ∀ i, 0 < XA i) (hXB : ∀ i, 0 < XB i)
    (hAlo : ∀ i x, x < 1 → WA i x = 0) (hAhi : ∀ i x, R < x → WA i x = 0)
    (hBlo : ∀ i x, x < 1 → WB i x = 0) (hBhi : ∀ i x, R < x → WB i x = 0)
    (hWA : ∀ i x, ‖WA i x‖ ≤ 1) (hWB : ∀ i x, ‖WB i x‖ ≤ 1) (u : ℝ) :
    ‖fullPrimeProductGauss R WA WB XA XB u‖ ≤
      (primeCoefficientMassConstant R (Fintype.card κ)*
        primeCoefficientMassConstant R (Fintype.card ι))*((∏ i, XA i)*(∏ i, XB i)) := by
  have hF (a : Eisenstein) (ha : a ∈ fullSquarefreePrimeSupport R WA XA 1)
      (b : Eisenstein) (hb : b ∈ fullSquarefreePrimeSupport R WB XB 1) :
      ‖gauss (a*b)*normTwist u (a*b)‖ ≤ 1 := by
    rw [norm_mul,norm_normTwist,mul_one]
    exact norm_gauss_le_one (primary_mul (fullSquarefreePrimeSupport_primary R WA XA 1 ha).1
      (fullSquarefreePrimeSupport_primary R WB XB 1 hb).1)
  have h := fullPrimeProduct_weighted_bound R WA WB XA XB
    (fun a b => gauss (a*b)*normTwist u (a*b)) hF
  have hsame : (∑ a ∈ fullSquarefreePrimeSupport R WA XA 1,
      ∑ b ∈ fullSquarefreePrimeSupport R WB XB 1,
        fullPrimeCoefficient R WA XA a*fullPrimeCoefficient R WB XB b*
          (gauss (a*b)*normTwist u (a*b))) = fullPrimeProductGauss R WA WB XA XB u := by
    simp only [fullPrimeProductGauss,mul_assoc]
  rw [hsame,mul_one] at h
  apply h.trans
  apply (mul_le_mul (fullPrimeCoefficient_l1_unit hR WA XA hXA hAlo hAhi hWA 1)
    (fullPrimeCoefficient_l1_unit hR WB XB hXB hBlo hBhi hWB 1)
    (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))
    (by
      unfold primeCoefficientMassConstant
      exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => (hXA i).le)))).trans_eq
  ring

lemma fullPrimeProductModel_bound {R : ℝ} (hR : 0 ≤ R)
    (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
    (hXA : ∀ i, 0 < XA i) (hXB : ∀ i, 0 < XB i)
    (hAlo : ∀ i x, x < 1 → WA i x = 0) (hAhi : ∀ i x, R < x → WA i x = 0)
    (hBlo : ∀ i x, x < 1 → WB i x = 0) (hBhi : ∀ i x, R < x → WB i x = 0)
    (hWA : ∀ i x, ‖WA i x‖ ≤ 1) (hWB : ∀ i x, ‖WB i x‖ ≤ 1) (u : ℝ) :
    ‖fullPrimeProductModel R WA WB XA XB u‖ ≤
      (primeCoefficientMassConstant R (Fintype.card κ)*
        primeCoefficientMassConstant R (Fintype.card ι))*cStar*
          ((∏ i, XA i)*(∏ i, XB i))^(5/6:ℝ) := by
  let D := (∏ i, XA i)*(∏ i, XB i)
  have hD : 0 < D := mul_pos (Finset.prod_pos (fun i _ => hXA i))
    (Finset.prod_pos (fun i _ => hXB i))
  let F := fun a b : Eisenstein =>
    ((cStar:ℂ)*(idealMoebius (a*b):ℂ)^2*((norm (a*b)^(-1/6:ℝ):ℝ):ℂ))*normTwist u (a*b)
  have hF (a : Eisenstein) (ha : a ∈ fullSquarefreePrimeSupport R WA XA 1)
      (b : Eisenstein) (hb : b ∈ fullSquarefreePrimeSupport R WB XB 1) :
      ‖F a b‖ ≤ cStar*D^(-1/6:ℝ) := by
    have hn : D ≤ norm (a*b) := by
      rw [norm_mul_eq]
      exact mul_le_mul (fullPrimeProduct_norm_bounds R WA XA hXA hAlo hAhi
        (Finset.mem_filter.mp ha).1).1
        (fullPrimeProduct_norm_bounds R WB XB hXB hBlo hBhi
          (Finset.mem_filter.mp hb).1).1
        (Finset.prod_nonneg (fun i _ => (hXB i).le)) (norm_nonneg a)
    have hm : ‖(idealMoebius (a*b):ℂ)^2‖ ≤ 1 := by
      rw [norm_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (_root_.norm_nonneg _)
        (norm_idealMoebius_le_one (a*b)) 2
    simp only [F,norm_mul,norm_normTwist,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos cStar_pos,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (a*b)) (-1/6:ℝ))]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm cStar_pos.le)
      (Real.rpow_nonneg (norm_nonneg (a*b)) (-1/6:ℝ))).trans
      (by
        have hr := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hD hn (by norm_num : (-1/6:ℝ) ≤ 0)) cStar_pos.le
        simpa only [mul_one] using hr)
  have h := fullPrimeProduct_weighted_bound R WA WB XA XB F hF
  have hsame : (∑ a ∈ fullSquarefreePrimeSupport R WA XA 1,
      ∑ b ∈ fullSquarefreePrimeSupport R WB XB 1,
        fullPrimeCoefficient R WA XA a*fullPrimeCoefficient R WB XB b*F a b) =
          fullPrimeProductModel R WA WB XA XB u := by
    simp only [F,fullPrimeProductModel,mul_assoc]
  rw [hsame] at h
  apply h.trans
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul (fullPrimeCoefficient_l1_unit hR WA XA hXA hAlo hAhi hWA 1)
      (fullPrimeCoefficient_l1_unit hR WB XB hXB hBlo hBhi hWB 1)
      (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))
      (by
      unfold primeCoefficientMassConstant
      exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => (hXA i).le))))
    (mul_nonneg cStar_pos.le (Real.rpow_nonneg hD.le (-1/6:ℝ)))
  apply hm.trans_eq
  have he : D*D^(-1/6:ℝ) = D^(5/6:ℝ) := by
    calc
      _ = D^(1:ℝ)*D^(-1/6:ℝ) := by rw [Real.rpow_one]
      _ = D^((1:ℝ)+(-1/6:ℝ)) := (Real.rpow_add hD _ _).symm
      _ = _ := by norm_num
  calc
    _ = (primeCoefficientMassConstant R (Fintype.card κ)*
        primeCoefficientMassConstant R (Fintype.card ι))*cStar*(D*D^(-1/6:ℝ)) := by
      dsimp [D]; ring
    _ = _ := by rw [he]

lemma continuous_fullPrimeProductGauss (R : ℝ) (WA : κ → ℝ → ℂ)
    (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ) :
    Continuous (fullPrimeProductGauss R WA WB XA XB) := by
  unfold fullPrimeProductGauss normTwist
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightAveraging
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive, normalized two-sided height averaging. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma dyadicHeightMean_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {T : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Icc (-2*T) (2*T), f t ≤ g t) :
    dyadicHeightMean f T ≤ dyadicHeightMean g T := by
  apply div_le_div_of_nonneg_right _ hT.le
  apply add_le_add
  · apply intervalIntegral.integral_mono_on (by linarith : T ≤ 2*T)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    intro t ht
    exact h t ⟨by linarith [ht.1],ht.2⟩
  · apply intervalIntegral.integral_mono_on (by linarith : -2*T ≤ -T)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    intro t ht
    exact h t ⟨ht.1,by linarith [ht.2]⟩

lemma dyadicHeightMean_const (C : ℝ) {T : ℝ} (hT : T ≠ 0) :
    dyadicHeightMean (fun _ => C) T = 2*C := by
  simp only [dyadicHeightMean,intervalIntegral.integral_const,smul_eq_mul]
  field_simp
  ring

lemma dyadicHeightMean_le_const {f : ℝ → ℝ} (hf : Continuous f)
    {T C : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Icc (-2*T) (2*T), f t ≤ C) :
    dyadicHeightMean f T ≤ 2*C :=
  (dyadicHeightMean_mono hf continuous_const hT h).trans_eq
    (dyadicHeightMean_const C hT.ne')

lemma dyadicHeightMean_neg (f : ℝ → ℝ) (T : ℝ) :
    dyadicHeightMean (fun t => f (-t)) T = dyadicHeightMean f T := by
  have h₁ : -(-2*T) = 2*T := by ring
  have h₂ : -(2*T) = -2*T := by ring
  simp only [dyadicHeightMean,intervalIntegral.integral_comp_neg,neg_neg,h₁,h₂]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicMellinTail
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A weighted Mellin tail from actual dyadic height means. -/
noncomputable section
open Set Filter MeasureTheory
namespace CubicFirstMoment

lemma mellinHeightDyad_union {T : ℝ} (hT : 0 < T) :
    (⋃ n : ℕ, mellinHeightDyad T n) = Ici T := by
  ext x
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact (le_mul_of_one_le_left hT.le (one_le_pow₀ (by norm_num))).trans hn.1
  · intro hx
    obtain ⟨n,hn,hnext⟩ := exists_nat_pow_near ((le_div_iff₀ hT).mpr (by simpa using hx))
      (by norm_num : (1:ℝ) < 2)
    exact mem_iUnion.mpr ⟨n,⟨(le_div_iff₀ hT).mp hn,(div_lt_iff₀ hT).mp hnext⟩⟩

lemma mellinHeightDyad_disjoint {T : ℝ} (hT : 0 < T) :
    Pairwise (fun i j => Disjoint (mellinHeightDyad T i) (mellinHeightDyad T j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : i+1 ≤ j)) hT.le
    exact (not_lt_of_ge (hp.trans hj.1)) hi.2
  · have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : j+1 ≤ i)) hT.le
    exact (not_lt_of_ge (hp.trans hi.1)) hj.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SignedMellinTail
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both signs of the height variable in the low-core Mellin integral. -/
noncomputable section
open Set Filter MeasureTheory
namespace CubicFirstMoment

theorem signed_height_mean_positive {g : ℝ → ℝ} (_hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    {T B : ℝ} (hT : 0 < T)
    (hmean : ∀ S : ℝ, T ≤ S →
      ((∫ t in S..2*S, g t)+(∫ t in -2*S..-S, g t))/S ≤ B) :
    ∀ S : ℝ, T ≤ S → (∫ t in S..2*S, g t) ≤ B*S := by
  intro S hTS
  have hS : 0 < S := hT.trans_le hTS
  have hn : 0 ≤ ∫ t in -2*S..-S, g t :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => hg0 t)
  have hm := (div_le_iff₀ hS).mp (hmean S hTS)
  linarith

theorem signed_height_mean_negative {g : ℝ → ℝ} (_hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    {T B : ℝ} (hT : 0 < T)
    (hmean : ∀ S : ℝ, T ≤ S →
      ((∫ t in S..2*S, g t)+(∫ t in -2*S..-S, g t))/S ≤ B) :
    ∀ S : ℝ, T ≤ S → (∫ t in S..2*S, g (-t)) ≤ B*S := by
  intro S hTS
  have hS : 0 < S := hT.trans_le hTS
  have hn : 0 ≤ ∫ t in S..2*S, g t :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => hg0 t)
  have hm := (div_le_iff₀ hS).mp (hmean S hTS)
  rw [intervalIntegral.integral_comp_neg]
  have he : -(2*S) = -2*S := by ring
  rw [he]
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinMassIntegration
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble a local Mellin estimate and the two signed tails as a bound
for the full integral. -/
noncomputable section
open Set MeasureTheory Filter
namespace CubicFirstMoment

lemma integral_height_split {F : ℝ → ℝ} (hF : Integrable F) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, F t) = (∫ t in Ioo (-T) T, F t)+
      (∫ t in Ici T, F t)+(∫ t in Ici T, F (-t)) := by
  have hc : (Ioo (-T) T)ᶜ = Ici T ∪ Iic (-T) := by
    ext t
    simp only [mem_compl_iff,mem_Ioo,not_and_or,not_lt,mem_union,mem_Ici,mem_Iic]
    tauto
  have hd : Disjoint (Ici T) (Iic (-T)) := by
    apply disjoint_left.mpr
    intro t ht hs
    have ht' : T ≤ t := ht
    have hs' : t ≤ -T := hs
    linarith
  rw [← integral_add_compl measurableSet_Ioo hF,hc,
    setIntegral_union hd measurableSet_Iic hF.integrableOn hF.integrableOn]
  have hn : (∫ t in Ici T, F (-t)) = ∫ t in Iic (-T), F t := by
    rw [integral_Ici_eq_integral_Ioi,integral_comp_neg_Ioi]
  rw [hn]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwoRangeMellinTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Mellin tail with a proved mean up to a power cutoff and a coarse
mean afterwards. Rapid decay suppresses the coarse part by the cutoff
power; the good mean is not silently extended to every height. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem weighted_positive_mellin_tail_two_ranges {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    (hfg : Integrable (fun t => f t*g t))
    {T R B D C : ℝ} (hT : 0 < T) (hR : 0 < R)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hC : 0 ≤ C) (p : ℕ)
    (hmean : ∀ S : ℝ, T ≤ S → S ≤ R → (∫ t in S..2*S, g t) ≤ B*S)
    (hcoarse : ∀ S : ℝ, T ≤ S → (∫ t in S..2*S, g t) ≤ D*S)
    (hdecay : ∀ t : ℝ, T ≤ t → f t ≤ C/t^2)
    (hrapid : ∀ t : ℝ, T ≤ t → f t ≤ C/(t^p*t^2)) :
    (∫ t in Ici T, f t*g t) ≤ 2*(B*C+D*C/R^p)/T := by
  have hdyad (n : ℕ) : (∫ t in mellinHeightDyad T n, f t*g t) ≤
      ((B*C+D*C/R^p)/T)*((1/2:ℝ)^n) := by
    let S := (2:ℝ)^n*T
    have hS : 0 < S := mul_pos (pow_pos (by norm_num) _) hT
    have hTS : T ≤ S := le_mul_of_one_le_left hT.le (one_le_pow₀ (by norm_num))
    have hS2 : S ≤ 2*S := by linarith
    have he : (2:ℝ)^(n+1)*T = 2*S := by dsimp [S]; rw [pow_succ]; ring
    have hgeom : 1/S = (1/T)*((1/2:ℝ)^n) := by
      dsimp [S]
      rw [div_pow,one_pow]
      field_simp
    change (∫ t in Ico S ((2:ℝ)^(n+1)*T), f t*g t) ≤ _
    rw [he,integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le hS2]
    by_cases hSR : S ≤ R
    · have hi := intervalIntegral.integral_mono_on (μ := volume) hS2
        ((hf.mul hg).intervalIntegrable _ _)
        ((continuous_const.mul hg).intervalIntegrable S (2*S))
        (show ∀ t ∈ Icc S (2*S), f t*g t ≤ (C/S^2)*g t from fun t ht => by
          apply mul_le_mul_of_nonneg_right _ (hg0 t)
          exact (hdecay t (hTS.trans ht.1)).trans
            (div_le_div_of_nonneg_left hC (sq_pos_of_pos hS)
              (pow_le_pow_left₀ hS.le ht.1 2)))
      calc
        _ ≤ (C/S^2)*(∫ t in S..2*S, g t) := by
          change (∫ t in S..2*S, f t*g t) ≤ ∫ t in S..2*S, (C/S^2)*g t at hi
          rw [intervalIntegral.integral_const_mul] at hi
          exact hi
        _ ≤ (C/S^2)*(B*S) := mul_le_mul_of_nonneg_left (hmean S hTS hSR) (by positivity)
        _ = (B*C)*(1/S) := by field_simp
        _ ≤ (B*C+D*C/R^p)*(1/S) := by
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
        _ = _ := by rw [hgeom]; ring
    · have hRS : R ≤ S := (lt_of_not_ge hSR).le
      have hi := intervalIntegral.integral_mono_on (μ := volume) hS2
        ((hf.mul hg).intervalIntegrable _ _)
        ((continuous_const.mul hg).intervalIntegrable S (2*S))
        (show ∀ t ∈ Icc S (2*S), f t*g t ≤ (C/(R^p*S^2))*g t from fun t ht => by
          apply mul_le_mul_of_nonneg_right _ (hg0 t)
          have htp : 0 < t := hS.trans_le ht.1
          apply (hrapid t (hTS.trans ht.1)).trans
          apply div_le_div_of_nonneg_left hC (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ hR.le (hRS.trans ht.1) p)
            (pow_le_pow_left₀ hS.le ht.1 2) (by positivity) (by positivity))
      calc
        _ ≤ (C/(R^p*S^2))*(∫ t in S..2*S, g t) := by
          change (∫ t in S..2*S, f t*g t) ≤ ∫ t in S..2*S, (C/(R^p*S^2))*g t at hi
          rw [intervalIntegral.integral_const_mul] at hi
          exact hi
        _ ≤ (C/(R^p*S^2))*(D*S) :=
          mul_le_mul_of_nonneg_left (hcoarse S hTS) (by positivity)
        _ = (D*C/R^p)*(1/S) := by field_simp
        _ ≤ (B*C+D*C/R^p)*(1/S) := by
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hB hC)) (by positivity)
        _ = _ := by rw [hgeom]; ring
  have hsum := hasSum_integral_iUnion (μ := volume)
    (s := mellinHeightDyad T) (f := fun t => f t*g t)
    (fun n : ℕ => (measurableSet_Ico : MeasurableSet (mellinHeightDyad T n)))
    (mellinHeightDyad_disjoint hT) hfg.integrableOn
  rw [mellinHeightDyad_union hT] at hsum
  calc
    _ = ∑' n : ℕ, ∫ t in mellinHeightDyad T n, f t*g t := hsum.tsum_eq.symm
    _ ≤ ∑' n : ℕ, ((B*C+D*C/R^p)/T)*((1/2:ℝ)^n) :=
      Summable.tsum_le_tsum hdyad hsum.summable (summable_geometric_two.mul_left _)
    _ = ((B*C+D*C/R^p)/T)*2 := (hasSum_geometric_two.mul_left _).tsum_eq
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwoRangeSignedTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both signs of the two-range Mellin estimate. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem weighted_signed_mellin_tail_two_ranges {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    (hfg : Integrable (fun t => f t*g t))
    {T R B D C : ℝ} (hT : 0 < T) (hR : 0 < R)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hC : 0 ≤ C) (p : ℕ)
    (hmean : ∀ S : ℝ, T ≤ S → S ≤ R →
      ((∫ t in S..2*S, g t)+(∫ t in -2*S..-S, g t))/S ≤ B)
    (hcoarse : ∀ S : ℝ, T ≤ S →
      ((∫ t in S..2*S, g t)+(∫ t in -2*S..-S, g t))/S ≤ D)
    (hdecay : ∀ t : ℝ, T ≤ |t| → f t ≤ C/t^2)
    (hrapid : ∀ t : ℝ, T ≤ |t| → f t ≤ C/(|t|^p*t^2)) :
    ((∫ t in Ici T, f t*g t)+(∫ t in Ici T, f (-t)*g (-t))) ≤
      4*(B*C+D*C/R^p)/T := by
  have hpos (S : ℝ) (hTS : T ≤ S) (hSR : S ≤ R) :
      (∫ t in S..2*S, g t) ≤ B*S := by
    have hS := hT.trans_le hTS
    have hm := (div_le_iff₀ hS).mp (hmean S hTS hSR)
    have hn : 0 ≤ ∫ t in -2*S..-S, g t :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => hg0 t)
    linarith
  have hneg (S : ℝ) (hTS : T ≤ S) (hSR : S ≤ R) :
      (∫ t in S..2*S, g (-t)) ≤ B*S := by
    have hS := hT.trans_le hTS
    have hm := (div_le_iff₀ hS).mp (hmean S hTS hSR)
    have hn : 0 ≤ ∫ t in S..2*S, g t :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => hg0 t)
    rw [intervalIntegral.integral_comp_neg]
    have he : -(2*S) = -2*S := by ring
    rw [he]
    linarith
  have hp := weighted_positive_mellin_tail_two_ranges hf hg hg0 hfg hT hR hB hD hC p
    hpos (signed_height_mean_positive hg hg0 hT hcoarse)
    (fun t ht => hdecay t (by rwa [abs_of_pos (hT.trans_le ht)]))
    (fun t ht => by
      have hh := hrapid t (by rwa [abs_of_pos (hT.trans_le ht)])
      simpa only [abs_of_pos (hT.trans_le ht)] using hh)
  have hi : Integrable (fun t : ℝ => f (-t)*g (-t)) := hfg.comp_neg
  have hn := weighted_positive_mellin_tail_two_ranges (hf.comp continuous_neg)
    (hg.comp continuous_neg) (fun t => hg0 (-t)) hi hT hR hB hD hC p
    hneg (signed_height_mean_negative hg hg0 hT hcoarse)
    (fun t ht => by
      have hh := hdecay (-t) (by rw [abs_neg,abs_of_pos (hT.trans_le ht)]; exact ht)
      simpa only [Function.comp_apply,neg_sq] using hh)
    (fun t ht => by
      have hh := hrapid (-t) (by rw [abs_neg,abs_of_pos (hT.trans_le ht)]; exact ht)
      simpa only [Function.comp_apply,abs_neg,abs_of_pos (hT.trans_le ht),neg_sq] using hh)
  exact (add_le_add hp hn).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ZeroMellinDecay
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform decay in the total-product scale on the zero Mellin line. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma continuous_norm_zeroLineMellinWeight (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) {X : ℝ} (hX : 0 < X) :
    Continuous (fun t => ‖zeroLineMellinWeight W X t‖) := by
  have he : (fun t => ‖zeroLineMellinWeight W X t‖) =
      fun t => (1/(2*Real.pi))*‖mellinVerticalSchwartz W hW hpos hsm 0 t‖ := by
    funext t
    rw [zeroLineMellinWeight_norm W hX,mellinVerticalSchwartz_apply]
    simp only [Complex.ofReal_zero,zero_add]
  rw [he]
  exact continuous_const.mul (mellinVerticalSchwartz W hW hpos hsm 0).continuous.norm

theorem zeroLineMellinWeight_decay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 < X → ∀ t : ℝ, t ≠ 0 →
      ‖zeroLineMellinWeight W X t‖ ≤ C/|t|^n := by
  obtain ⟨C,hC,hb⟩ := smooth_mellin_vertical_decay W hW hpos hsm 0 n
  refine ⟨C/(2*Real.pi),by positivity,?_⟩
  intro X hX t ht
  have hat : 0 < |t| := abs_pos.mpr ht
  apply (le_div_iff₀ (pow_pos hat n)).mpr
  rw [zeroLineMellinWeight_norm W hX]
  have hp : |t|^n*‖mellin W ((t:ℂ)*Complex.I)‖ ≤ C := by
    apply le_trans _ (by simpa only [Complex.ofReal_zero,zero_add] using hb t)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg t) (by linarith : |t| ≤ 1+|t|) n) (_root_.norm_nonneg _)
  first | (convert mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 1/(2*Real.pi)) using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 1/(2*Real.pi))).trans (le_of_eq (by ring)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductMellinTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete signed Mellin tail for two full prime convolutions.
A height mean up to B^.35 suffices; the remaining frequencies use the
literal coarse convolution bound. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma primeProduct_far_mellin_scale {A B : ℝ} (hA : 0 < A) (hB : 1 ≤ B)
    (hAB : A ≤ B^2) : A*B/(B^(7/20:ℝ))^2 ≤ (A*B)^(5/6:ℝ) := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hV : 0 < A*B := mul_pos hA hBp
  have hvhi : A*B ≤ B^3 := by nlinarith [mul_le_mul_of_nonneg_right hAB hBp.le]
  have hroot : (A*B)^(1/6:ℝ) ≤ (B^(7/20:ℝ))^2 := by
    calc
      _ ≤ (B^3)^(1/6:ℝ) := Real.rpow_le_rpow hV.le hvhi (by norm_num)
      _ = B^(1/2:ℝ) := by rw [←Real.rpow_natCast,←Real.rpow_mul hBp.le]; norm_num
      _ ≤ B^(7/10:ℝ) := Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
      _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hBp.le]; norm_num
  apply (div_le_iff₀ (sq_pos_of_pos (Real.rpow_pos_of_pos hBp _))).mpr
  calc
    _ = (A*B)^(5/6:ℝ)*(A*B)^(1/6:ℝ) := by rw [←Real.rpow_add hV]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hV.le _)

theorem fullPrimeProductGauss_mellin_tail {R : ℝ} (hR : 0 ≤ R)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ D : ℝ, 0 < D ∧ ∀ (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ)
      (XA : κ → ℝ) (XB : ι → ℝ),
      (∀ i, 0 < XA i) → (∀ i, 0 < XB i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, R < x → WA i x = 0) →
      (∀ i x, x < 1 → WB i x = 0) → (∀ i x, R < x → WB i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) → (∀ i x, ‖WB i x‖ ≤ 1) →
      1 ≤ (∏ i, XB i) → (∏ i, XA i) ≤ (∏ i, XB i)^2 →
      ∀ (X u S K : ℝ), 0 < X → 0 < S → 0 ≤ K →
      (∀ T : ℝ, S ≤ T → T ≤ (∏ i, XB i)^(7/20:ℝ) →
        dyadicHeightMean (fun t => ‖fullPrimeProductGauss R WA WB XA XB (u+t)‖) T ≤
          K*((∏ i, XA i)*(∏ i, XB i))^(5/6:ℝ)) →
      ((∫ τ in Ici S, ‖zeroLineMellinWeight W X τ‖*
          ‖fullPrimeProductGauss R WA WB XA XB (u-τ)‖)+
       (∫ τ in Ici S, ‖zeroLineMellinWeight W X (-τ)‖*
          ‖fullPrimeProductGauss R WA WB XA XB (u+τ)‖)) ≤
        D*(K+1)*((∏ i, XA i)*(∏ i, XB i))^(5/6:ℝ)/S := by
  obtain ⟨C₂,hC₂,hdecay₂⟩ := zeroLineMellinWeight_decay W hW hpos hsm 2
  obtain ⟨C₄,hC₄,hdecay₄⟩ := zeroLineMellinWeight_decay W hW hpos hsm 4
  let C := C₂+C₄
  let M := primeCoefficientMassConstant R (Fintype.card κ)*
    primeCoefficientMassConstant R (Fintype.card ι)
  have hM : 0 ≤ M := by dsimp [M,primeCoefficientMassConstant]; positivity
  refine ⟨4*C*(1+2*M),by dsimp [C]; positivity,?_⟩
  intro WA WB XA XB hXA hXB hAlo hAhi hBlo hBhi hWA hWB hB hAB
    X u S K hX hS hK hmean
  let V := (∏ i, XA i)*(∏ i, XB i)
  have hV : 0 < V := mul_pos (Finset.prod_pos (fun i _ => hXA i))
    (Finset.prod_pos (fun i _ => hXB i))
  let f := fun τ => ‖zeroLineMellinWeight W X τ‖
  let g := fun τ => ‖fullPrimeProductGauss R WA WB XA XB (u-τ)‖
  have hf : Continuous f := continuous_norm_zeroLineMellinWeight W hW hpos hsm hX
  have hg : Continuous g := ((continuous_fullPrimeProductGauss R WA WB XA XB).comp
    (continuous_const.sub continuous_id)).norm
  have hg0 : ∀ τ, 0 ≤ g τ := fun _ => _root_.norm_nonneg _
  have hgb : ∀ τ, g τ ≤ M*V := fun τ => fullPrimeProductGauss_bound hR WA WB XA XB
    hXA hXB hAlo hAhi hBlo hBhi hWA hWB (u-τ)
  have hfi : Integrable f := (zeroLineMellinWeight_integrable W hW hpos hsm hX).norm
  have hfg : Integrable (fun τ => f τ*g τ) := hfi.mul_bdd hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun τ => by rw [Real.norm_of_nonneg (hg0 τ)]; exact hgb τ))
  have hgood (T : ℝ) (hST : S ≤ T) (hT : T ≤ (∏ i, XB i)^(7/20:ℝ)) :
      dyadicHeightMean g T ≤ K*V^(5/6:ℝ) := by
    have he : g = fun τ => ‖fullPrimeProductGauss R WA WB XA XB (u+ -τ)‖ := by
      funext τ
      simp only [g,sub_eq_add_neg]
    rw [he,dyadicHeightMean_neg (fun τ => ‖fullPrimeProductGauss R WA WB XA XB (u+τ)‖) T]
    exact hmean T hST hT
  have hcoarse (T : ℝ) (hST : S ≤ T) : dyadicHeightMean g T ≤ 2*M*V := by
    exact (dyadicHeightMean_le_const hg (hS.trans_le hST) (fun τ _ => hgb τ)).trans_eq (by ring)
  have hd₂ (τ : ℝ) (hτ : S ≤ |τ|) : f τ ≤ C/τ^2 := by
    have hn : τ ≠ 0 := abs_pos.mp (hS.trans_le hτ)
    have hh := hdecay₂ X hX τ hn
    rw [sq_abs] at hh
    exact hh.trans (div_le_div_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg τ))
  have hd₄ (τ : ℝ) (hτ : S ≤ |τ|) : f τ ≤ C/(|τ|^2*τ^2) := by
    have hn : τ ≠ 0 := abs_pos.mp (hS.trans_le hτ)
    have hh := hdecay₄ X hX τ hn
    have he : |τ|^4 = |τ|^2*τ^2 := by nlinarith [sq_abs τ]
    rw [he] at hh
    exact hh.trans (div_le_div_of_nonneg_right (by dsimp [C]; linarith) (by positivity))
  have hb := weighted_signed_mellin_tail_two_ranges hf hg hg0 hfg hS
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hB) _) (by positivity : 0 ≤ K*V^(5/6:ℝ))
    (by positivity : 0 ≤ 2*M*V) (by dsimp [C]; positivity : 0 ≤ C) 2
    hgood hcoarse hd₂ hd₄
  have hs : (2*M*V)*C/((∏ i, XB i)^(7/20:ℝ))^2 ≤ 2*M*C*V^(5/6:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left
      (primeProduct_far_mellin_scale (Finset.prod_pos (fun i _ => hXA i)) hB hAB)
      (by dsimp [C]; positivity : 0 ≤ 2*M*C)
    convert hh using 1 <;> first | rfl | ring
  have hb' : ((∫ τ in Ici S, f τ*g τ)+(∫ τ in Ici S, f (-τ)*g (-τ))) ≤
      (4*C*(1+2*M))*(K+1)*V^(5/6:ℝ)/S := by
    apply hb.trans
    apply div_le_div_of_nonneg_right _ hS.le
    have hpow : 0 ≤ V^(5/6:ℝ) := Real.rpow_nonneg hV.le _
    have hc : 0 ≤ C := by dsimp [C]; positivity
    have hnon : 0 ≤ 2*M*K*C*V^(5/6:ℝ) := by positivity
    nlinarith
  simpa only [f,g,V,sub_neg_eq_add] using hb'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightIntegrationByParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact twofold integration by parts for the actual height exponential. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace CubicFirstMoment

lemma heightFourierIntegral_eq (h : ℝ → ℂ) (ℓ : ℝ) :
    heightFourierIntegral h ℓ = ∫ t : ℝ, h t*Complex.exp ((ℓ*t:ℝ)*Complex.I) := by
  rw [heightFourierIntegral,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  have he : -2*Real.pi*t*(-ℓ/(2*Real.pi)) = ℓ*t := by
    field_simp
  rw [he,smul_eq_mul,mul_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightPolynomialIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact interchange between finite height Fourier coefficients and the
actual norm polynomial. No frequency truncation is used. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma height_norm_phase (a : Eisenstein) (x₀ t : ℝ) :
    Complex.exp (((Real.log (norm a)-x₀)*t:ℝ)*Complex.I) =
      Complex.exp ((-x₀*t:ℝ)*Complex.I)*normTwist t a := by
  unfold normTwist
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

lemma integrable_height_phase (h : ℝ → ℂ) (hi : Integrable h) (ℓ : ℝ) :
    Integrable (fun t : ℝ => h t*Complex.exp ((ℓ*t:ℝ)*Complex.I)) := by
  apply hi.mul_bdd (c := 1)
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp ((ℓ*t:ℝ)*Complex.I))).aestronglyMeasurable
  · exact Eventually.of_forall (fun _ => by simp [Complex.norm_exp])

theorem height_norm_polynomial_integral {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (n : ι → Eisenstein) (h : ℝ → ℂ) (hi : Integrable h) (x₀ : ℝ) :
    (∑ a ∈ S, c a*heightFourierIntegral h (Real.log (norm (n a))-x₀)) =
      ∫ t : ℝ, (h t*Complex.exp ((-x₀*t:ℝ)*Complex.I))*
        ∑ a ∈ S, c a*normTwist t (n a) := by
  calc
    _ = ∑ a ∈ S, ∫ t : ℝ, c a*(h t*
        Complex.exp (((Real.log (norm (n a))-x₀)*t:ℝ)*Complex.I)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [heightFourierIntegral_eq,integral_const_mul]
    _ = ∫ t : ℝ, ∑ a ∈ S, c a*(h t*
        Complex.exp (((Real.log (norm (n a))-x₀)*t:ℝ)*Complex.I)) :=
      (integral_finsetSum S (fun a _ =>
        (integrable_height_phase h hi (Real.log (norm (n a))-x₀)).const_mul (c a))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [height_norm_phase]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete sharp-cutoff smoothing in the manuscript's height variable.
The Fourier convention contributes the explicit Jacobian `1 / (2π)`.
All finite sums below retain their original coefficients and support. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

lemma cutoffHeightMultiplier_integrable {T : ℝ} (hT : 0 < T) :
    Integrable (cutoffHeightMultiplier T) := by
  have h := (integrable_fourier_intervalSmoothing hT 0 (Real.log 2)).comp_div
    (show 2*Real.pi ≠ 0 by positivity)
  change Integrable (fun t => frequencyCutoff ((t/(2*Real.pi))/T) *
    𝓕 (fun x => (intervalStep 0 (Real.log 2) x : ℂ)) (t/(2*Real.pi)))
  simpa only [fourier_intervalSmoothing hT] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowHeightIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The low-height weight has a direct polynomial-logarithmic cost.
This transfers the uniform corrected Type-I/II estimates to its integral. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cutoffHeightMultiplier_norm_le_log (H t : ℝ) :
    ‖cutoffHeightMultiplier H t‖ ≤ Real.log 2 := by
  change ‖frequencyCutoff ((t/(2*Real.pi))/H)*
    dyadicFourierMultiplier (t/(2*Real.pi))‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (_root_.norm_nonneg _)
    (norm_frequencyCutoff_le_one _)).trans (norm_dyadicFourierMultiplier_le_log _)

lemma lowHeightWeight_norm_le (H T t : ℝ) :
    ‖lowHeightWeight H T t‖ ≤ Real.log 2 := by
  rw [lowHeightWeight,norm_mul]
  apply (mul_le_of_le_one_right (_root_.norm_nonneg _) ?_).trans
    (cutoffHeightMultiplier_norm_le_log H t)
  simpa only [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg heightPartitionBump.nonneg] using
    (heightPartitionBump.le_one (x := t/T))

lemma lowHeightWeight_zero (H : ℝ) {T t : ℝ} (hT : 0 < T)
    (ht : t ∉ Icc (-(4/3)*T) ((4/3)*T)) : lowHeightWeight H T t = 0 := by
  have hh : 4/3 ≤ |t/T| := by
    rw [abs_div,abs_of_pos hT]
    apply (le_div_iff₀ hT).mpr
    have hn : ¬(-(4/3)*T ≤ t ∧ t ≤ (4/3)*T) := ht
    rw [le_abs]
    by_cases hp : t ≤ (4/3)*T
    · have hl : t < -(4/3)*T := lt_of_not_ge (fun hl => hn ⟨hl,hp⟩)
      exact Or.inr (by linarith)
    · exact Or.inl (le_of_lt (lt_of_not_ge hp))
  rw [lowHeightWeight,heightPartitionBump_zero hh,Complex.ofReal_zero,mul_zero]

theorem lowHeightWeight_integral_bound (H : ℝ) {T B : ℝ}
    (hT : 0 < T) (_hB : 0 ≤ B) (f : ℝ → ℂ)
    (hf : ∀ t ∈ Icc (-(4/3)*T) ((4/3)*T), ‖f t‖ ≤ B) :
    ‖∫ t : ℝ, lowHeightWeight H T t*f t‖ ≤ (8/3)*Real.log 2*T*B := by
  let S : Set ℝ := Icc (-(4/3)*T) ((4/3)*T)
  let b : ℝ := Real.log 2*B
  have hi : Integrable (S.indicator (fun _ => b)) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  have hb : ‖∫ t : ℝ, lowHeightWeight H T t*f t‖ ≤
      ∫ t : ℝ, S.indicator (fun _ => b) t := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards with t
    by_cases ht : t ∈ S
    · rw [indicator_of_mem ht,norm_mul]
      exact mul_le_mul (lowHeightWeight_norm_le H T t) (hf t ht)
        (_root_.norm_nonneg _) (Real.log_nonneg (by norm_num))
    · rw [indicator_of_notMem ht,lowHeightWeight_zero H hT ht,zero_mul,norm_zero]
  apply hb.trans_eq
  rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),intervalIntegral.integral_const]
  dsimp [b]
  ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLowHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer a uniform low-height arithmetic bound to the actual
low-height term of the sharp prime comparison. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma lowHeightWeight_integrable {H : ℝ} (hH : 0 < H) (T : ℝ) :
    Integrable (lowHeightWeight H T) := by
  apply (cutoffHeightMultiplier_integrable hH).mul_bdd (c := 1)
  · exact (Complex.continuous_ofReal.comp
      (heightPartitionBump.continuous.comp (continuous_id.div_const T))).aestronglyMeasurable
  · filter_upwards with t
    simpa only [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg heightPartitionBump.nonneg] using
      (heightPartitionBump.le_one (x := t/T))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove only the proved zero terms when the detector's finite
squarefree envelope is put into a Type-I row. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma centeredGauss_zero_of_not_squarefree {n : Eisenstein} (hn : primary n)
    (hs : ¬Squarefree n) : centeredGauss n = 0 := by
  rw [centeredGauss,gauss_eq_zero_of_not_squarefree hn hs,
    idealMoebius_sq_complex,ite_eq_right hs]
  ring

lemma productCenteredKernel_envelope (ℓ : ℤ) (W : ℝ → ℂ) {B X : ℝ}
    (hX : 0 < X) (hW : ∀ x : ℝ, B < x → W x = 0)
    (t : ℝ) {n : Eisenstein} (hn : primary n) :
    (if n ∈ squarefreeProductEnvelope (B*X) then productCenteredKernel ℓ W X t n else 0) =
      productCenteredKernel ℓ W X t n := by
  by_cases hs : Squarefree n
  · by_cases hsize : norm n ≤ B*X
    · have hm : n ∈ squarefreeProductEnvelope (B*X) :=
        Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hn,hsize⟩,hs⟩
      rw [ite_eq_left hm]
    · have hx : B < norm n/X := (lt_div_iff₀ hX).mpr (lt_of_not_ge hsize)
      simp only [productCenteredKernel,hW _ hx,mul_zero,ite_self]
  · simp only [productCenteredKernel,centeredGauss_zero_of_not_squarefree hn hs,
      mul_zero,zero_mul,ite_self]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The product-envelope Type-I integral equals the literal finite
height-Fourier kernel used in the detector decomposition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma centeredHeightKernel_envelope (ℓ : ℤ) (W : ℝ → ℂ) {B X : ℝ}
    (hX : 0 < X) (hW : ∀ x : ℝ, B < x → W x = 0)
    (H T X₀ : ℝ) {n : Eisenstein} (hn : primary n) :
    (if n ∈ squarefreeProductEnvelope (B*X) then centeredHeightKernel ℓ W H T X X₀ n else 0) =
      centeredHeightKernel ℓ W H T X X₀ n := by
  have he := congrArg (fun z : ℂ => z*heightFourierIntegral (lowHeightWeight H T)
    (Real.log (norm n)-Real.log X₀)) (productCenteredKernel_envelope ℓ W hX hW 0 hn)
  simpa only [ite_mul,zero_mul,productCenteredKernel,normTwist,zero_mul,
    Complex.ofReal_zero,Complex.exp_zero,mul_one,centeredHeightKernel] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CenteredProductHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The low-height integral of a literal centered product polynomial.
The product envelope is separated at its actual Mellin frequency. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem centered_product_low_integral (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (ℓ : ℤ) (W : ℝ → ℂ)
    (X X₀ T : ℝ) {H : ℝ} (hH : 0 < H) :
    (∑ a ∈ A, ∑ b ∈ B, α a*β b*centeredHeightKernel ℓ W H T X X₀ (a*b)) =
      ∫ t : ℝ, (lowHeightWeight H T t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        centeredProductSmoothed A B α β ℓ W X t := by
  let c : Eisenstein × Eisenstein → ℂ := fun q =>
    α q.1*β q.2*theta ℓ (q.1*q.2)*centeredGauss (q.1*q.2)*W (norm (q.1*q.2)/X)
  have hb := height_norm_polynomial_integral (A.product B) c (fun q => q.1*q.2)
    (lowHeightWeight H T) (lowHeightWeight_integrable hH T) (Real.log X₀)
  simp only [Finset.product_eq_sprod,Finset.sum_product] at hb
  calc
    _ = ∑ a ∈ A, ∑ b ∈ B, c (a,b)*heightFourierIntegral (lowHeightWeight H T)
        (Real.log (norm (a*b))-Real.log X₀) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp [c,centeredHeightKernel]
      ring
    _ = _ := by
      rw [hb]
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      unfold centeredProductSmoothed
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp [c]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CenteredMellinWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer a centered polynomial bound through the actual finite
Mellin window and the original low-height weight. The complementary
Mellin tail is kept separate and is not bounded by this lemma. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem centeredMellinWindow_bound (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X M : ℝ} (hX : 0 < X) (hM : 0 ≤ M) (S u : ℝ)
    (hb : ∀ τ ∈ Icc (-S) S, ‖centeredProductPolynomial A B α β ℓ (u-τ)‖ ≤ M) :
    ‖centeredMellinWindow A B α β ℓ W X S u‖ ≤ zeroLineMellinMass W*M := by
  have hw := zeroLineMellinWeight_integrable W hW hpos hsm hX
  have hnorm : ‖centeredMellinWindow A B α β ℓ W X S u‖ ≤
      ∫ τ in Icc (-S) S, ‖zeroLineMellinWeight W X τ‖*M := by
    apply norm_integral_le_of_norm_le (hw.norm.mul_const M).restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb τ hτ) (_root_.norm_nonneg _)
  apply hnorm.trans
  rw [integral_mul_const]
  have hi : (∫ τ in Icc (-S) S, ‖zeroLineMellinWeight W X τ‖) ≤
      ∫ τ : ℝ, ‖zeroLineMellinWeight W X τ‖ :=
    setIntegral_le_integral hw.norm (Filter.Eventually.of_forall (fun _ => _root_.norm_nonneg _))
  rw [zeroLineMellinWeight_mass W hX] at hi
  exact mul_le_mul_of_nonneg_right hi hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinComplement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the Mellin complement, retaining both signs. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma integral_mellin_complement {F : ℝ → ℝ} (hF : Integrable F)
    {S : ℝ} (hS : 0 < S) :
    (∫ t in (Icc (-S) S)ᶜ, F t) =
      (∫ t in Ici S, F t)+(∫ t in Ici S, F (-t)) := by
  have h₁ := integral_height_split hF hS
  have h₂ := integral_add_compl (s := Icc (-S) S) measurableSet_Icc hF
  rw [integral_Icc_eq_integral_Ioo] at h₂
  linarith

lemma centered_product_mellin_complement (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (hA : ∀ a ∈ A, primary a) (hB : ∀ b ∈ B, primary b)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (S u : ℝ) :
    centeredProductSmoothed A B α β ℓ W X u =
      centeredMellinWindow A B α β ℓ W X S u+
      ∫ τ in (Icc (-S) S)ᶜ, zeroLineMellinWeight W X τ*
        centeredProductPolynomial A B α β ℓ (u-τ) := by
  rw [centered_product_mellin A B α β hA hB ℓ W hW hpos hsm hX u]
  exact (integral_add_compl measurableSet_Icc
    (centered_product_mellin_integrable A B α β ℓ W hW hpos hsm hX u)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductCenteredTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restore the model term in the full complementary Mellin integral.
The constants are uniform over all admissible coordinate weights and scales. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem fullPrimeProduct_centered_mellin_tail {R : ℝ} (hR : 0 ≤ R)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ D : ℝ, 0 < D ∧ ∀ (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ)
      (XA : κ → ℝ) (XB : ι → ℝ),
      (∀ i, 0 < XA i) → (∀ i, 0 < XB i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, R < x → WA i x = 0) →
      (∀ i x, x < 1 → WB i x = 0) → (∀ i x, R < x → WB i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) → (∀ i x, ‖WB i x‖ ≤ 1) →
      1 ≤ (∏ i, XB i) → (∏ i, XA i) ≤ (∏ i, XB i)^2 →
      ∀ (X u S K : ℝ), 0 < X → 0 < S → 0 ≤ K →
      (∀ T : ℝ, S ≤ T → T ≤ (∏ i, XB i)^(7/20:ℝ) →
        dyadicHeightMean (fun t => ‖fullPrimeProductGauss R WA WB XA XB (u+t)‖) T ≤
          K*((∏ i, XA i)*(∏ i, XB i))^(5/6:ℝ)) →
      ‖∫ τ in (Icc (-S) S)ᶜ, zeroLineMellinWeight W X τ*
        centeredProductPolynomial (fullSquarefreePrimeSupport R WA XA 1)
          (fullSquarefreePrimeSupport R WB XB 1)
          (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) 0 (u-τ)‖ ≤
        D*(K+1)*((∏ i, XA i)*(∏ i, XB i))^(5/6:ℝ)/S := by
  obtain ⟨Dg,hDg,hgauss⟩ := fullPrimeProductGauss_mellin_tail (ι := ι) (κ := κ) hR W hW hpos hsm
  let M := primeCoefficientMassConstant R (Fintype.card κ)*
    primeCoefficientMassConstant R (Fintype.card ι)*cStar
  let M₁ := ∫ τ : ℝ, |τ| *‖zeroLineMellinWeight W 1 τ‖
  have hM : 0 ≤ M := by dsimp [M,primeCoefficientMassConstant]; have := cStar_pos; positivity
  have hM₁ : 0 ≤ M₁ := integral_nonneg (fun _ => by positivity)
  refine ⟨Dg+M*M₁,by positivity,?_⟩
  intro WA WB XA XB hXA hXB hAlo hAhi hBlo hBhi hWA hWB hB hAB X u S K hX hS hK hmean
  let V := (∏ i, XA i)*(∏ i, XB i)
  have hV : 0 < V := mul_pos (Finset.prod_pos (fun i _ => hXA i))
    (Finset.prod_pos (fun i _ => hXB i))
  let f := fun τ => ‖zeroLineMellinWeight W X τ‖
  let g := fun τ => ‖fullPrimeProductGauss R WA WB XA XB (u-τ)‖
  let P := centeredProductPolynomial (fullSquarefreePrimeSupport R WA XA 1)
    (fullSquarefreePrimeSupport R WB XB 1)
    (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB)
  have hwi := zeroLineMellinWeight_integrable W hW hpos hsm hX
  have hfi : Integrable f := hwi.norm
  have hfg : Integrable (fun τ => f τ*g τ) := hfi.mul_bdd
    (((continuous_fullPrimeProductGauss R WA WB XA XB).comp
      (continuous_const.sub continuous_id)).norm.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun τ => by
      rw [Real.norm_of_nonneg (_root_.norm_nonneg _)]
      exact fullPrimeProductGauss_bound hR WA WB XA XB hXA hXB hAlo hAhi hBlo hBhi hWA hWB (u-τ)))
  have hcenter := centered_product_mellin_integrable (fullSquarefreePrimeSupport R WA XA 1)
    (fullSquarefreePrimeSupport R WB XB 1) (fullPrimeCoefficient R WA XA)
    (fullPrimeCoefficient R WB XB) 0 W hW hpos hsm hX u
  have hcn : Integrable (fun τ => f τ*‖P 0 (u-τ)‖) := by
    simpa only [norm_mul] using hcenter.norm
  have hn : ‖∫ τ in (Icc (-S) S)ᶜ, zeroLineMellinWeight W X τ*P 0 (u-τ)‖ ≤
      ∫ τ in (Icc (-S) S)ᶜ, f τ*g τ+f τ*(M*V^(5/6:ℝ)) := by
    apply (norm_integral_le_integral_norm _).trans
    have hi := integral_mono_ae hcn.restrict
      ((hfg.add (hfi.mul_const (M*V^(5/6:ℝ)))).restrict (s := (Icc (-S) S)ᶜ))
      (Filter.Eventually.of_forall (fun τ => by
        have hc : ‖P 0 (u-τ)‖ ≤ g τ+M*V^(5/6:ℝ) := by
          rw [show P 0 (u-τ) = fullPrimeProductGauss R WA WB XA XB (u-τ)-
              fullPrimeProductModel R WA WB XA XB (u-τ) from
            fullPrimeProduct_centered R WA WB XA XB (u-τ)]
          exact (norm_sub_le _ _).trans (add_le_add le_rfl
            (fullPrimeProductModel_bound hR WA WB XA XB hXA hXB hAlo hAhi hBlo hBhi hWA hWB (u-τ)))
        simpa only [mul_add,Pi.add_apply,f] using mul_le_mul_of_nonneg_left hc (_root_.norm_nonneg _)))
    simpa only [Pi.add_apply,f,norm_mul] using hi
  have hg := hgauss WA WB XA XB hXA hXB hAlo hAhi hBlo hBhi hWA hWB hB hAB X u S K hX hS hK hmean
  have hg' : (∫ τ in (Icc (-S) S)ᶜ, f τ*g τ) ≤ Dg*(K+1)*V^(5/6:ℝ)/S := by
    rw [integral_mellin_complement hfg hS]
    simpa only [f,g,V,sub_neg_eq_add] using hg
  have hmoment := zeroLineMellinWeight_moment_integrable W hW hpos hsm hX 1
  have hmom : (∫ τ : ℝ, |τ|^1*‖zeroLineMellinWeight W X τ‖) = M₁ := by
    apply integral_congr_ae
    filter_upwards with τ
    simp only [pow_one,zeroLineMellinWeight_norm W hX,
      zeroLineMellinWeight_norm W (by norm_num : (0:ℝ) < 1)]
  have ht := weighted_height_tail _ hwi 1 hmoment hS
  rw [hmom,pow_one] at ht
  apply hn.trans
  rw [integral_add hfg.restrict (hfi.mul_const (M*V^(5/6:ℝ))).restrict,integral_mul_const]
  apply (add_le_add hg' (mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ M*V^(5/6:ℝ)))).trans
  have hinc : M₁/S*(M*V^(5/6:ℝ)) ≤ (M₁/S*(M*V^(5/6:ℝ)))*(K+1) :=
    le_mul_of_one_le_right (by positivity) (by linarith : 1 ≤ K+1)
  calc
    _ ≤ Dg*(K+1)*V^(5/6:ℝ)/S+(M₁/S*(M*V^(5/6:ℝ)))*(K+1) :=
      add_le_add le_rfl hinc
    _ = _ := by dsimp only [V]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeModelLogTail
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The model is already negligible above a sufficiently large power
of the logarithm. This leaves the genuinely low-height corrected sum. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma cubic_log_saving_isLittleO :
    (fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) =o[atTop] firstMomentScale := by
  have hL : Tendsto (fun X : ℝ => 1+Real.log X) atTop atTop :=
    tendsto_const_nhds.add_atTop Real.tendsto_log_atTop
  have hi := tendsto_inv_atTop_zero.comp hL
  have hconst : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hh := (hconst.sub hi).mul (hi.pow 2)
  simp only [sub_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero] at hh
  apply Asymptotics.isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    have hp : 0 < firstMomentScale X := div_pos
      (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _) (Real.log_pos hX)
    exact fun hz => (hp.ne' hz).elim
  · apply hh.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    have hp : 0 < X := zero_lt_one.trans hX
    have hl : 0 < Real.log X := Real.log_pos hX
    unfold firstMomentScale
    simp only [Function.comp_apply]
    field_simp [(Real.rpow_pos_of_pos hp (5/6:ℝ)).ne',hl.ne',
      show 1+Real.log X ≠ 0 by positivity]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductEnvelope
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed smooth product envelope equals one on the full sharp dyadic
interval. Thus the exact prime cutoff can be retained in the height integral
while every factorized row has a smooth product weight. -/
noncomputable section
open Set Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma primeProductEnvelope_zero {x : ℝ} (hx : 3 ≤ x) : primeProductEnvelope x = 0 := by
  have h : primeProductBump x = 0 := by
    apply primeProductBump.zero_of_le_dist
    change 1 ≤ |x-3/2|
    exact (by linarith : (1:ℝ) ≤ x-3/2).trans (le_abs_self _)
  simp only [primeProductEnvelope,h,Complex.ofReal_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDetectorCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit smooth cutoff for the exact prime detector. -/
noncomputable section
open Filter
open scoped ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeDetectorCutoff_nonneg (x : ℝ) : 0 ≤ primeDetectorCutoff x :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

lemma primeDetectorCutoff_le_one (x : ℝ) : primeDetectorCutoff x ≤ 1 := by
  unfold primeDetectorCutoff
  linarith [Real.smoothTransition.nonneg (x-1)]

lemma primeDetectorCutoff_one {x : ℝ} (hx : x ≤ 1) : primeDetectorCutoff x = 1 := by
  rw [primeDetectorCutoff,Real.smoothTransition.zero_of_nonpos (by linarith),sub_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductDetector
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the manuscript's exact prime detector to the actual central
integral kernel. The support is a concrete subset of the primary lattice,
with both norm endpoints enforced before the detector is invoked. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeProductEnvelope_zero_lower {x : ℝ} (hx : x ≤ 1/2) :
    primeProductEnvelope x = 0 := by
  have h : primeProductBump x = 0 := by
    apply primeProductBump.zero_of_le_dist
    change 1 ≤ |x-3/2|
    exact (by linarith : (1:ℝ) ≤ -(x-3/2)).trans (neg_le_abs _)
  simp only [primeProductEnvelope,h,Complex.ofReal_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual primary factor tuples in the distinguished-prime expansion.
Ordering a subset contributes its factorial; the remaining primary factor
is the literal complementary product, not an abstract coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguishedPrimeWeight_support {ψ : ℝ → ℝ}
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 0 < w) (hwz : w ≤ z) {p : Eisenstein}
    (hp : 0 < norm p) (hne : distinguishedPrimeWeight ψ w z p ≠ 0) :
    w < norm p ∧ norm p < 2*z := by
  have hz : 0 < z := hw.trans_le hwz
  constructor
  · by_contra h
    have hpw : norm p ≤ w := not_lt.mp h
    apply hne
    rw [distinguishedPrimeWeight,hψone _ (div_pos hp hw) ((div_le_one hw).mpr hpw),
      hψone _ (div_pos hp hz) ((div_le_one hz).mpr (hpw.trans hwz)),sub_self]
    rfl
  · by_contra h
    have hpz : 2*z ≤ norm p := not_lt.mp h
    apply hne
    rw [distinguishedPrimeWeight,hψzero _ ((le_div_iff₀ hw).mpr (by linarith)),
      hψzero _ ((le_div_iff₀ hz).mpr hpz),sub_self]
    rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingProductSlice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact product slices for the original finite support. Divisibility
supplies the norm bound needed by the stopping construction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_primaryProductSlice_iff (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (a : Eisenstein) {m : Eisenstein} (hm : primary m) :
    m ∈ primaryProductSlice S X a ↔ a*m ∈ S := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨mem_primaryElementBall.mpr ⟨hm,?_⟩,h⟩
    exact (norm_le_of_dvd (primary_ne_zero (hS _ h).1)
      (dvd_mul_left m a)).trans (hS _ h).2.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CenteredProductSymmetry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma centeredProductSmoothed_swap (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (ℓ : ℤ) (W : ℝ → ℂ) (X u : ℝ) :
    centeredProductSmoothed A B α β ℓ W X u = centeredProductSmoothed B A β α ℓ W X u := by
  unfold centeredProductSmoothed
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm b a]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CentralProductSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth product kernel permits the exact detector support to be
replaced by its full squarefree envelope. No nonzero term is removed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma centralProductEnvelope_spec {X : ℝ} {n : Eisenstein}
    (hn : n ∈ centralProductEnvelope X) :
    primary n ∧ Squarefree n ∧ norm n ≤ Real.exp primeProductWeights.radius*X := by
  obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
  exact ⟨(mem_primaryElementBall.mp hn).1,hs,(mem_primaryElementBall.mp hn).2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTuplePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite smooth norm partition of the literal large-row prime tuples.
Every original support condition stays inside each summand. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largePrimeTupleNorm_bounds {i j : ℕ} {X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X) (a : Fin i ⊕ Fin j) :
    1 ≤ largePrimeTupleNorm q a ∧
      largePrimeTupleNorm q a ≤ Real.exp primeProductWeights.radius*X := by
  obtain ⟨hf,hg⟩ := Finset.mem_product.mp hq
  rcases a with a | b
  · have hp := mem_primeCutoff.mp (Fintype.mem_piFinset.mp hf a)
    exact ⟨one_le_norm hp.1.2.ne_zero,hp.2⟩
  · have hp := mem_primeCutoff.mp (Fintype.mem_piFinset.mp hg b)
    exact ⟨one_le_norm hp.1.2.ne_zero,hp.2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OverlapScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary powers and logarithmic absorption for model overlap. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma overlap_power_log_saving {c : ℝ} (hc : 0 < c) (a k : ℕ) :
    ∀ᶠ L : ℝ in atTop, (1+Real.log L)^a/L^c ≤ 1/(1+Real.log L)^(2*k) := by
  filter_upwards [negative_power_log_saving hc (a+2*k),eventually_ge_atTop (1:ℝ)] with L h hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log L := by linarith [Real.log_nonneg hL]
  calc
    _ = (1+Real.log L)^a*L^(-c) := by rw [Real.rpow_neg hLp.le]; ring
    _ ≤ (1+Real.log L)^a*(1/(1+Real.log L)^(a+2*k)) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hz.le _)
    _ = _ := by rw [pow_add]; field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeSmoothWeights
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The roughness transition in each actual semiprime norm piece belongs
to a single uniform smooth family. Capping its scale ratio at two is an
identity on the fixed norm support, so all logarithmic derivatives are
uniform even when the original ratio is unbounded. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma semiprimeSmoothWeight_high (r : ℝ) {x : ℝ} (hx : 2 < x) :
    semiprimeSmoothWeight r x = 0 := by
  rw [semiprimeSmoothWeight,normPartitionWeight_high hx,zero_mul]

lemma semiprimeSmoothWeight_norm (r x : ℝ) : ‖semiprimeSmoothWeight r x‖ ≤ 1 := by
  have hc : ‖1-(primeDetectorCutoff (r*x):ℂ)‖ ≤ 1 := by
    have he : (1-(primeDetectorCutoff (r*x):ℂ)) =
        ((1-primeDetectorCutoff (r*x):ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      (sub_nonneg.mpr (primeDetectorCutoff_le_one _))]
    linarith [primeDetectorCutoff_nonneg (r*x)]
  rw [semiprimeSmoothWeight,norm_mul]
  exact (mul_le_mul (normPartitionWeight_norm x) hc (_root_.norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeRange
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual nonzero semiprime pieces lie in the balanced prime range.
The upper bilinear constraint follows from a strict power gap, uniformly
for every fixed logarithmic exponent required by the published inputs. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma semiprime_kernel_product_range (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) {p q : Eisenstein}
    (hk : centeredHeightKernel ℓ primeProductEnvelope H T X X (p*q) ≠ 0) :
    X/2 ≤ norm (p*q) ∧ norm (p*q) ≤ 3*X := by
  have hw : primeProductEnvelope (norm (p*q)/X) ≠ 0 := by
    intro hz
    apply hk
    simp only [centeredHeightKernel,hz,mul_zero,zero_mul]
  constructor
  · apply le_of_not_gt
    intro hh
    apply hw
    exact primeProductEnvelope_zero_lower ((div_le_iff₀ hX).mpr (by linarith))
  · apply le_of_not_gt
    intro hh
    apply hw
    exact primeProductEnvelope_zero ((le_div_iff₀ hX).mpr hh.le)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual support geometry of the large distinguished rows. Every prime
is rough, and the complementary primes inherit the X^(31/50) bound from
the original large distinguished product. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largePrimeTupleTerm_membership {i j : ℕ} {ℓ : ℤ} {ξ : ℝ} {Ct : ℕ} {H X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) :
    (∏ a, q.1 a) ∈ (centralPrimaryFactors X).filter
        (fun r => ¬norm r < X^(38/100:ℝ)) ∧
      (∏ b, q.2 b) ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) (∏ a, q.1 a) := by
  unfold largePrimeTupleTerm at hne
  split_ifs at hne with hr hu
  · exact ⟨hr,hu⟩
  · exact (hne rfl).elim
  · exact (hne rfl).elim

lemma largePrimeTupleTerm_factors_ne_zero {i j : ℕ} {ℓ : ℤ} {ξ : ℝ} {Ct : ℕ} {H X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) :
    (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a)) ≠ 0 ∧
    (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ))) ≠ 0 ∧
      centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
        X X ((∏ a, q.1 a)*(∏ b, q.2 b)) ≠ 0 := by
  obtain ⟨hr,hu⟩ := largePrimeTupleTerm_membership hne
  simp only [largePrimeTupleTerm,hr,hu,ite_true, if_true] at hne
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2,(mul_ne_zero_iff.mp hne).2⟩

lemma largePrimeTupleTerm_product_range {i j : ℕ} {ℓ : ℤ} {ξ : ℝ} {Ct : ℕ} {H X : ℝ}
    (hX : 0 < X) {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) :
    X/2 ≤ norm ((∏ a, q.1 a)*(∏ b, q.2 b)) ∧
      norm ((∏ a, q.1 a)*(∏ b, q.2 b)) ≤ 3*X :=
  semiprime_kernel_product_range ℓ H _ hX (largePrimeTupleTerm_factors_ne_zero hne).2.2

lemma largePrimeTupleNorm_rough_bound {i j : ℕ} {ℓ : ℤ} {ξ : ℝ} {Ct : ℕ} {H X : ℝ}
    (hX : 1 ≤ X) (hξ : ξ ≤ 2/5)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) (a : Fin i ⊕ Fin j) :
    X^ξ < largePrimeTupleNorm q a := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hw := Real.rpow_pos_of_pos hXp ξ
  obtain ⟨hf,hg,_hk⟩ := largePrimeTupleTerm_factors_ne_zero hne
  rcases a with a | b
  · have hn := Finset.prod_ne_zero_iff.mp hf a (Finset.mem_univ a)
    exact (distinguishedPrimeWeight_support (fun _ _ hh => primeDetectorCutoff_one hh)
      (fun _ hh => primeDetectorCutoff_zero hh) hw
      (Real.rpow_le_rpow_of_exponent_le hX hξ)
      (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq (.inl a)).1) hn).1
  · have hn := Finset.prod_ne_zero_iff.mp hg b (Finset.mem_univ b)
    change X^ξ < norm (q.2 b)
    by_contra hh
    apply hn
    rw [primeDetectorCutoff_one ((div_le_one hw).mpr (not_lt.mp hh))]
    simp

lemma largePrimeTupleNorm_upper_bound {i j : ℕ} {ℓ : ℤ} {ξ : ℝ} {Ct : ℕ} {H X : ℝ}
    (hX : 1 ≤ X) (hξ : ξ ≤ 2/5)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) (a : Fin i ⊕ Fin j) :
    largePrimeTupleNorm q a ≤ 3*X^(31/50:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨hf,_hg,_hk⟩ := largePrimeTupleTerm_factors_ne_zero hne
  obtain ⟨hr,hu⟩ := largePrimeTupleTerm_membership hne
  rcases a with a | b
  · have hn := Finset.prod_ne_zero_iff.mp hf a (Finset.mem_univ a)
    have hh := (distinguishedPrimeWeight_support (fun _ _ hh => primeDetectorCutoff_one hh)
      (fun _ hh => primeDetectorCutoff_zero hh) (Real.rpow_pos_of_pos hXp ξ)
      (Real.rpow_le_rpow_of_exponent_le hX hξ)
      (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq (.inl a)).1) hn).2
    change norm (q.1 a) ≤ _
    have hp := Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (2/5:ℝ) ≤ 31/50)
    nlinarith [Real.rpow_pos_of_pos hXp (31/50:ℝ)]
  · have hup := (mem_primaryElementBall.mp (Finset.mem_filter.mp hu).1).1
    have hdiv : q.2 b ∣ ∏ b, q.2 b := Finset.dvd_prod_of_mem q.2 (Finset.mem_univ b)
    have hnb := norm_le_of_dvd (primary_ne_zero hup) hdiv
    have hnr : X^(38/100:ℝ) ≤ norm (∏ a, q.1 a) :=
      le_of_not_gt (Finset.mem_filter.mp hr).2
    have hprod := (largePrimeTupleTerm_product_range hXp hne).2
    rw [norm_mul_eq] at hprod
    have hm : X^(38/100:ℝ)*norm (q.2 b) ≤ 3*X :=
      (mul_le_mul_of_nonneg_right hnr (norm_nonneg _)).trans
        ((mul_le_mul_of_nonneg_left hnb (norm_nonneg _)).trans hprod)
    have he : X^(38/100:ℝ)*(3*X^(31/50:ℝ)) = 3*X := by
      rw [mul_left_comm,←Real.rpow_add hXp]
      norm_num
    change norm (q.2 b) ≤ _
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp (38/100:ℝ))).mp
    simpa only [mul_comm] using hm.trans_eq he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized logarithmic prime sizes in the actual large-row support.
They form a positive partition of one uniformly away from two thirds. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma largePrimeTupleNorm_prod {i j : ℕ}
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) :
    (∏ a, largePrimeTupleNorm q a) = norm (largePrimeTupleProduct q) := by
  rw [Fintype.prod_sum_type]
  simp only [largePrimeTupleNorm,Sum.elim_inl,Sum.elim_inr,largePrimeTupleProduct,
    norm_mul_eq,norm_finset_prod]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single uniform smooth family for the actual distinguished-prime
weights in each large-row norm piece. Both scale ratios are capped only
after proving that the cap leaves the weight unchanged. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma distinguishedSmoothWeight_low (r : ℝ × ℝ) {x : ℝ} (hx : x < 1) :
    distinguishedSmoothWeight r x = 0 := by
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight_low _ hx,sub_self]

lemma distinguishedSmoothWeight_high (r : ℝ × ℝ) {x : ℝ} (hx : 2 < x) :
    distinguishedSmoothWeight r x = 0 := by
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight_high _ hx,sub_self]

lemma distinguishedSmoothWeight_norm (r : ℝ × ℝ) (x : ℝ) :
    ‖distinguishedSmoothWeight r x‖ ≤ 1 := by
  have he : distinguishedSmoothWeight r x = normPartitionWeight x*
      ((primeDetectorCutoff (r.1*x)-primeDetectorCutoff (r.2*x):ℝ):ℂ) := by
    simp only [distinguishedSmoothWeight,semiprimeSmoothWeight,Complex.ofReal_sub]
    ring
  have hb : |primeDetectorCutoff (r.1*x)-primeDetectorCutoff (r.2*x)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [primeDetectorCutoff_nonneg (r.1*x),
      primeDetectorCutoff_nonneg (r.2*x),primeDetectorCutoff_le_one (r.1*x),
      primeDetectorCutoff_le_one (r.2*x)]
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul (normPartitionWeight_norm x) hb (abs_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

lemma distinguishedSmoothWeight_at_prime {A : ℝ} (hA : 0 < A)
    (w z : ℝ) (p : Eisenstein) :
    distinguishedSmoothWeight (A/w,A/z) (norm p/A) =
      normPartitionWeight (norm p/A)*distinguishedPrimeWeight primeDetectorCutoff w z p := by
  have he (r : ℝ) : (A/r)*(norm p/A) = norm p/r := by
    simp only [div_eq_mul_inv]
    calc
      A*r⁻¹*(norm p*A⁻¹) = (A*A⁻¹)*(norm p*r⁻¹) := by ring
      _ = norm p*r⁻¹ := by rw [mul_inv_cancel₀ hA.ne',one_mul]
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight,he,distinguishedPrimeWeight]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleCoordinateWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual independently smoothed prime coordinates of a large row
belong to one uniform family, for every norm partition and roughness scale. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

lemma roughSmoothWeight_at_prime {A : ℝ} (hA : 0 < A) (w : ℝ) (p : Eisenstein) :
    semiprimeSmoothWeight (A/w) (norm p/A) =
      normPartitionWeight (norm p/A)*(1-(primeDetectorCutoff (norm p/w):ℂ)) := by
  have he : (A/w)*(norm p/A) = norm p/w := by
    simp only [div_eq_mul_inv]
    calc
      A*w⁻¹*(norm p*A⁻¹) = (A*A⁻¹)*(norm p*w⁻¹) := by ring
      _ = norm p*w⁻¹ := by rw [mul_inv_cancel₀ hA.ne',one_mul]
  rw [semiprimeSmoothWeight,he]

lemma largeTupleCoordinateWeight_distinguished {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i) (p : Eisenstein) :
    largeTupleCoordinateWeight ξ X k (.inl a)
        (norm p/largeTupleNormScale k (.inl a)) =
      normPartitionWeight (2*norm p/(4/3:ℝ)^(k (.inl a)))*
        distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) p := by
  rw [largeTupleCoordinateWeight,distinguishedSmoothWeight_at_prime (largeTupleNormScale_pos _ _)]
  rw [normPartitionWeight_scale]
  rfl

lemma largeTupleCoordinateWeight_rough {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (b : Fin j) (p : Eisenstein) :
    largeTupleCoordinateWeight ξ X k (.inr b)
        (norm p/largeTupleNormScale k (.inr b)) =
      normPartitionWeight (2*norm p/(4/3:ℝ)^(k (.inr b)))*
        (1-(primeDetectorCutoff (norm p/(X^ξ)):ℂ)) := by
  rw [largeTupleCoordinateWeight,roughSmoothWeight_at_prime (largeTupleNormScale_pos _ _)]
  rw [normPartitionWeight_scale]
  rfl

lemma largeTupleCoordinateWeight_norm {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i ⊕ Fin j) (x : ℝ) :
    ‖largeTupleCoordinateWeight ξ X k a x‖ ≤ 1 := by
  rcases a with a | b
  · exact distinguishedSmoothWeight_norm _ x
  · exact semiprimeSmoothWeight_norm _ x

lemma largeTupleCoordinateWeight_low {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i ⊕ Fin j) {x : ℝ} (hx : x < 1) :
    largeTupleCoordinateWeight ξ X k a x = 0 := by
  rcases a with a | b
  · exact distinguishedSmoothWeight_low _ hx
  · exact semiprimeSmoothWeight_low _ hx

lemma largeTupleCoordinateWeight_high {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i ⊕ Fin j) {x : ℝ} (hx : 2 < x) :
    largeTupleCoordinateWeight ξ X k a x = 0 := by
  rcases a with a | b
  · exact distinguishedSmoothWeight_high _ hx
  · exact semiprimeSmoothWeight_high _ hx

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered kernel itself enforces the original squarefree product
envelope. The independent tuple representation therefore keeps only the
large-distinguished-product inequality as an explicit restriction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largePrimeTupleTerm_envelope {i j : ℕ} (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H : ℝ) {X : ℝ} (hX : 0 < X)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X) :
    largePrimeTupleTerm i j ℓ ξ Ct H X q =
      if ¬norm (∏ a, q.1 a) < X^(38/100:ℝ) then
        (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a))*
          (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ)))*
          centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
            X X ((∏ a, q.1 a)*(∏ b, q.2 b))
      else 0 := by
  obtain ⟨hf,hg⟩ := Finset.mem_product.mp hq
  have hr : primary (∏ a, q.1 a) := primary_finset_prod _ _
    (fun a _ => (mem_primeCutoff.mp (Fintype.mem_piFinset.mp hf a)).1.1)
  have hu : primary (∏ b, q.2 b) := primary_finset_prod _ _
    (fun b _ => (mem_primeCutoff.mp (Fintype.mem_piFinset.mp hg b)).1.1)
  have hn := primary_mul hr hu
  by_cases hp : (∏ a, q.1 a)*(∏ b, q.2 b) ∈ centralProductEnvelope X
  · have hrB : (∏ a, q.1 a) ∈ centralPrimaryFactors X := by
      apply mem_primaryElementBall.mpr
      exact ⟨hr,(norm_le_of_dvd (primary_ne_zero hn) (dvd_mul_right _ _)).trans
        (centralProductEnvelope_spec hp).2.2⟩
    have huS : (∏ b, q.2 b) ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) (∏ a, q.1 a) :=
      (mem_primaryProductSlice_iff _ _ (fun _ hn => centralProductEnvelope_spec hn) _ hu).mpr hp
    simp only [largePrimeTupleTerm,Finset.mem_filter,hrB,true_and,huS,ite_true, if_true]
  · have he := centeredHeightKernel_envelope ℓ primeProductEnvelope hX
      (fun x hx => primeProductWeights.upper_support () x hx) H ((1+Real.log X)^Ct) X hn
    change (if (∏ a, q.1 a)*(∏ b, q.2 b) ∈ centralProductEnvelope X then
      centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
        X X ((∏ a, q.1 a)*(∏ b, q.2 b)) else 0) = _ at he
    rw [ite_eq_right hp] at he
    have huS : (∏ b, q.2 b) ∉ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) (∏ a, q.1 a) := by
      intro huS
      exact hp (Finset.mem_filter.mp huS).2
    simp only [largePrimeTupleTerm,huS,he.symm,mul_zero,ite_self]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleSmoothIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each actual large-row norm piece is a product of the independently
smooth coordinate weights. Its only remaining sharp restriction is the
original lower bound for the distinguished product. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largeTupleCoordinateWeight_product {i j N : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) :
    (∏ a, largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
      (largePrimeTupleNorm q a/largeTupleNormScale (fun a => (k a).val) a)) =
      ((∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a))*
        (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ))))*
        normTupleWeight k (largePrimeTupleNorm q) := by
  rw [Fintype.prod_sum_type]
  simp only [largePrimeTupleNorm,Sum.elim_inl,Sum.elim_inr,
    largeTupleCoordinateWeight_distinguished,largeTupleCoordinateWeight_rough]
  unfold normTupleWeight
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  ring

lemma largePrimeTupleTerm_smoothed {i j N : ℕ} (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H : ℝ) {X : ℝ} (hX : 0 < X)
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X) :
    largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) =
      if ¬norm (∏ a, q.1 a) < X^(38/100:ℝ) then
        (∏ a, largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
          (largePrimeTupleNorm q a/largeTupleNormScale (fun a => (k a).val) a))*
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
          X X ((∏ a, q.1 a)*(∏ b, q.2 b))
      else 0 := by
  rw [largePrimeTupleTerm_envelope ℓ ξ Ct H hX hq,largeTupleCoordinateWeight_product]
  split_ifs <;> ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleScaleGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonzero smooth box fixes independent coordinate lengths. The
same lengths work for every tuple in the box, so a grouping chosen at
one surviving tuple does not introduce a new coupled coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largePrimeTuplePiece_coordinate_range {i j N : ℕ}
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hw : normTupleWeight k (largePrimeTupleNorm q) ≠ 0) (a : Fin i ⊕ Fin j) :
    largeTupleNormScale (fun a => (k a).val) a ≤ largePrimeTupleNorm q a ∧
      largePrimeTupleNorm q a ≤ 2*largeTupleNormScale (fun a => (k a).val) a := by
  have hi := Finset.prod_ne_zero_iff.mp hw a (Finset.mem_univ a)
  obtain ⟨hu,hl⟩ := normPartitionWeight_nonzero_scale hi
  change (4/3:ℝ)^(k a).val/2 ≤ largePrimeTupleNorm q a ∧
    largePrimeTupleNorm q a ≤ 2*((4/3:ℝ)^(k a).val/2)
  constructor <;> linarith

lemma largePrimeTuplePiece_subset_range {i j N : ℕ}
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hw : normTupleWeight k (largePrimeTupleNorm q) ≠ 0)
    (s : Finset (Fin i ⊕ Fin j)) :
    largeTupleSubsetScale (fun a => (k a).val) s ≤ ∏ a ∈ s, largePrimeTupleNorm q a ∧
      (∏ a ∈ s, largePrimeTupleNorm q a) ≤
        2^s.card*largeTupleSubsetScale (fun a => (k a).val) s := by
  constructor
  · exact Finset.prod_le_prod (fun a _ => (largeTupleNormScale_pos _ a).le)
      (fun a _ => (largePrimeTuplePiece_coordinate_range k hw a).1)
  · calc
      _ ≤ ∏ a ∈ s, 2*largeTupleNormScale (fun a => (k a).val) a :=
        Finset.prod_le_prod (fun a _ =>
          (largeTupleNormScale_pos _ a).le.trans (largePrimeTuplePiece_coordinate_range k hw a).1)
          (fun a _ => (largePrimeTuplePiece_coordinate_range k hw a).2)
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]; rfl

lemma largePrimeTuplePiece_scale_product {i j N : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {Ct : ℕ} {H X : ℝ} (hX : 0 < X)
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0) :
    X/(2*2^(i+j)) ≤ largeTupleSubsetScale (fun a => (k a).val) Finset.univ ∧
      largeTupleSubsetScale (fun a => (k a).val) Finset.univ ≤ 3*X := by
  obtain ⟨ht,hw⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨hlo,hhi⟩ := largePrimeTupleTerm_product_range hX ht
  change X/2 ≤ norm (largePrimeTupleProduct q) at hlo
  obtain ⟨hl,hu⟩ := largePrimeTuplePiece_subset_range k hw Finset.univ
  rw [largePrimeTupleNorm_prod] at hl hu
  simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] at hu
  refine ⟨?_,hl.trans hhi⟩
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*2^(i+j))).mpr
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleCutoffBoxes
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp distinguished-product condition is automatic on high
boxes and kills low boxes. The remaining boxes are explicitly confined
to a fixed-ratio neighborhood of the original cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largePrimeTuplePiece_distinguished_range {i j N : ℕ}
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hw : normTupleWeight k (largePrimeTupleNorm q) ≠ 0) :
    largeTupleDistinguishedScale (fun a => (k a).val) ≤ norm (∏ a, q.1 a) ∧
      norm (∏ a, q.1 a) ≤ 2^i*largeTupleDistinguishedScale (fun a => (k a).val) := by
  rw [norm_finset_prod]
  constructor
  · exact Finset.prod_le_prod (fun a _ => (largeTupleNormScale_pos _ _).le)
      (fun a _ => (largePrimeTuplePiece_coordinate_range k hw (.inl a)).1)
  · calc
      _ ≤ ∏ a : Fin i, 2*largeTupleNormScale (fun a => (k a).val) (.inl a) :=
        Finset.prod_le_prod (fun a _ => norm_nonneg _)
          (fun a _ => (largePrimeTuplePiece_coordinate_range k hw (.inl a)).2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp [largeTupleDistinguishedScale]

lemma largePrimeTupleTerm_high_box {i j N : ℕ} (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ)
    (H : ℝ) {X : ℝ} (hX : 0 < X) (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X) :
    largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) =
      (∏ a, largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
        (largePrimeTupleNorm q a/largeTupleNormScale (fun a => (k a).val) a))*
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
          X X (largePrimeTupleProduct q) := by
  by_cases hw : normTupleWeight k (largePrimeTupleNorm q) = 0
  · rw [hw,mul_zero,largeTupleCoordinateWeight_product,hw,mul_zero,zero_mul]
  · have hh : ¬norm (∏ a, q.1 a) < X^(38/100:ℝ) :=
      not_lt.mpr (hhigh.trans (largePrimeTuplePiece_distinguished_range k hw).1)
    rw [largePrimeTupleTerm_smoothed ℓ ξ Ct H hX k hq,ite_eq_left hh]
    rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleOrdinaryScales
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compactness grouping is converted to fixed smooth-box lengths.
All constant support ratios are retained before the eventual power gap
is used. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma largePrimeTuplePiece_log_pos {i j N : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {Ct : ℕ} {H X : ℝ} (hX : 1 ≤ X) (hlog : 200 ≤ Real.log X)
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0) :
    0 < norm (largePrimeTupleProduct q) ∧ 0 < Real.log (norm (largePrimeTupleProduct q)) := by
  have hXp := zero_lt_one.trans_le hX
  have hn := (largePrimeTupleTerm_product_range hXp (mul_ne_zero_iff.mp hne).1).1
  change X/2 ≤ norm (largePrimeTupleProduct q) at hn
  have hnp := (by positivity : (0:ℝ) < X/2).trans_le hn
  have hl := Real.log_le_log (by positivity : (0:ℝ) < X/2) hn
  rw [Real.log_div hXp.ne' (by norm_num)] at hl
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  exact ⟨hnp,by linarith⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleRoughScales
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual roughness survives the fixed-ratio smooth partition and
implies precisely the coordinate threshold used in the prime bilinear
theorem. No roughness is assumed for a box that vanishes. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

theorem largePrimeTuplePiece_rough_scales (i j : ℕ) {ξ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (Ct : ℕ) (H : ℝ) {N : ℕ}
      (k : (Fin i ⊕ Fin j) → Fin N),
      ∀ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
        (∀ a, 1 ≤ largeTupleNormScale (fun a => (k a).val) a) ∧
        ∀ B : ℝ, 0 ≤ B → B ≤ 3*X → ∀ a,
          (2*B)^(ξ/2) < largeTupleNormScale (fun a => (k a).val) a := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hξ).eventually_ge_atTop 2,
    eventually_const_mul_rpow_le (by linarith : ξ/2 < ξ) (2*6^(ξ/2))]
    with X hX hXtwo hgap
  intro ℓ Ct H N k q hq hne
  obtain ⟨ht,hw⟩ := mul_ne_zero_iff.mp hne
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hscale (a : Fin i ⊕ Fin j) :
      X^ξ/2 < largeTupleNormScale (fun a => (k a).val) a := by
    have hrough := largePrimeTupleNorm_rough_bound hX hξz hq ht a
    have hup := (largePrimeTuplePiece_coordinate_range k hw a).2
    linarith
  refine ⟨fun a => (by linarith [hscale a]),?_⟩
  intro B hB hBX a
  calc
    (2*B)^(ξ/2) ≤ (6*X)^(ξ/2) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    _ = 6^(ξ/2)*X^(ξ/2) := Real.mul_rpow (by norm_num) hXp.le
    _ ≤ X^ξ/2 := by linarith
    _ < largeTupleNormScale (fun a => (k a).val) a := hscale a


theorem largePrimeTuplePiece_coordinate_envelope (i j : ℕ) {ξ : ℝ}
    (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (Ct : ℕ) (H : ℝ) {N : ℕ}
      (k : (Fin i ⊕ Fin j) → Fin N),
      ∀ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
        ∀ a, 2*largeTupleNormScale (fun a => (k a).val) a ≤ Real.exp primeProductWeights.radius*X := by
  have hC : 0 < Real.exp primeProductWeights.radius/6 := by positivity
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_rpow_le_const_mul (by norm_num : (31/50:ℝ) < 1) hC]
    with X hX hgap
  intro ℓ Ct H N k q hq hne a
  obtain ⟨ht,hw⟩ := mul_ne_zero_iff.mp hne
  have hlo := (largePrimeTuplePiece_coordinate_range k hw a).1
  have hhi := largePrimeTupleNorm_upper_bound hX hξz hq ht a
  rw [Real.rpow_one] at hgap
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleRegrouping
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact regrouping of independently weighted prime coordinates into
two product variables. The grouping is fixed for the whole box. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma independent_tuple_sum_split (s : Finset ι) (S : ι → Finset Eisenstein)
    (F : ((s → Eisenstein) × ({a : ι // a ∉ s} → Eisenstein)) → ℂ) :
    (∑ f ∈ Fintype.piFinset S, F (fun a => f a,fun a => f a)) =
      ∑ f ∈ Fintype.piFinset (fun a : s => S a),
        ∑ g ∈ Fintype.piFinset (fun a : {a : ι // a ∉ s} => S a), F (f,g) := by
  rw [←Finset.sum_product]
  let e := Equiv.piEquivPiSubtypeProd (fun a => a ∈ s) (fun _ => Eisenstein)
  apply Finset.sum_equiv e
  · intro f
    change (f ∈ Fintype.piFinset S) ↔
      (fun a : s => f a,fun a : {a : ι // a ∉ s} => f a) ∈ _
    simp only [Finset.mem_product,Fintype.mem_piFinset]
    constructor
    · intro hf
      exact ⟨fun a => hf a,fun a => hf a⟩
    · rintro ⟨hf,hg⟩ a
      by_cases ha : a ∈ s
      · exact hf ⟨a,ha⟩
      · exact hg ⟨a,ha⟩
  · intro f _hf
    rfl

lemma independent_prime_tuple_bilinear (s : Finset ι) (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (K : Eisenstein → Eisenstein → ℂ) :
    (∑ f ∈ Fintype.piFinset S,
      (∏ a, w a (f a))*K (∏ a : s, f a) (∏ a : {a : ι // a ∉ s}, f a)) =
      ∑ b ∈ orderedConvolutionSupport (fun a : s => S a),
        ∑ a ∈ orderedConvolutionSupport (fun a : {a : ι // a ∉ s} => S a),
          orderedConvolution (fun a : s => S a) (fun a p => w a p) b*
          orderedConvolution (fun a : {a : ι // a ∉ s} => S a) (fun a p => w a p) a*K b a := by
  have hsplit := independent_tuple_sum_split s S (fun q =>
    (∏ a : s, w a (q.1 a))*(∏ a : {a : ι // a ∉ s}, w a (q.2 a))*
      K (∏ a : s, q.1 a) (∏ a : {a : ι // a ∉ s}, q.2 a))
  have hp (f : ι → Eisenstein) :
      (∏ a : s, w a (f a))*(∏ a : {a : ι // a ∉ s}, w a (f a)) = ∏ a, w a (f a) :=
    by
      rw [←Finset.prod_subtype s (fun _ => Iff.rfl) (fun a => w a (f a)),
        ←Finset.prod_subtype (Finset.univ\s) (by simp) (fun a => w a (f a))]
      exact Finset.prod_mul_prod_compl s (fun a => w a (f a))
  dsimp only at hsplit
  simp_rw [hp] at hsplit
  rw [hsplit]
  symm
  calc
    _ = ∑ b ∈ orderedConvolutionSupport (fun a : s => S a),
        orderedConvolution (fun a : s => S a) (fun a p => w a p) b*
          ∑ a ∈ orderedConvolutionSupport (fun a : {a : ι // a ∉ s} => S a),
            orderedConvolution (fun a : {a : ι // a ∉ s} => S a) (fun a p => w a p) a*K b a := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Finset.mul_sum]
      simp only [mul_assoc]
    _ = _ := by
      rw [orderedConvolution_sum]
      apply Finset.sum_congr rfl
      intro f _hf
      rw [orderedConvolution_sum,Finset.mul_sum]
      simp only [mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleSupportChange
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Changing the finite coordinate envelope leaves a weighted tuple sum
unchanged when the nonzero coordinate weights have the same support. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma independent_tuple_sum_support (S T : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (K : (ι → Eisenstein) → ℂ)
    (hST : ∀ i p, w i p ≠ 0 → (p ∈ S i ↔ p ∈ T i)) :
    (∑ f ∈ Fintype.piFinset S, (∏ i, w i (f i))*K f) =
      ∑ f ∈ Fintype.piFinset T, (∏ i, w i (f i))*K f := by
  have hmem (f : ι → Eisenstein) (hw : (∏ i, w i (f i)) ≠ 0) :
      f ∈ Fintype.piFinset S ↔ f ∈ Fintype.piFinset T := by
    simp only [Fintype.mem_piFinset]
    exact forall_congr' (fun i => hST i (f i) (Finset.prod_ne_zero_iff.mp hw i (Finset.mem_univ i)))
  apply Finset.sum_congr_of_eq_on_inter
  · intro f hf hnot
    by_cases hw : (∏ i, w i (f i)) = 0
    · rw [hw,zero_mul]
    · exact (hnot ((hmem f hw).mp hf)).elim
  · intro f hf hnot
    by_cases hw : (∏ i, w i (f i)) = 0
    · rw [hw,zero_mul]
    · exact (hnot ((hmem f hw).mpr hf)).elim
  · intro _ _ _
    rfl

lemma independent_tuple_sum_sum_type {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : (ι ⊕ κ) → Finset Eisenstein) (F : ((ι → Eisenstein) × (κ → Eisenstein)) → ℂ) :
    (∑ f ∈ Fintype.piFinset S, F (fun a => f (.inl a),fun a => f (.inr a))) =
      ∑ q ∈ (Fintype.piFinset (fun a => S (.inl a))).product
          (Fintype.piFinset (fun a => S (.inr a))), F q := by
  apply Finset.sum_equiv (Equiv.sumArrowEquivProdArrow ι κ Eisenstein)
  · intro f
    change (f ∈ Fintype.piFinset S) ↔
      (fun a => f (.inl a),fun a => f (.inr a)) ∈ _
    simp only [Finset.product_eq_sprod,Finset.mem_product,Fintype.mem_piFinset]
    constructor
    · intro hf
      exact ⟨fun a => hf (.inl a),fun a => hf (.inr a)⟩
    · rintro ⟨hf,hg⟩ (a | a)
      · exact hf a
      · exact hg a
  · intro f _
    rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleFullSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High boxes are literal full independent prime sums. The original
finite prime cutoff is removed only after the coordinate support bounds
show that all nonzero weights fit inside it. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largeTupleVector_prod {i j : ℕ} (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) :
    (∏ a, largeTupleVector q a) = largePrimeTupleProduct q := by
  rw [Fintype.prod_sum_type]
  rfl

lemma largeTupleVector_norm {i j : ℕ} (q : (Fin i → Eisenstein) × (Fin j → Eisenstein))
    (a : Fin i ⊕ Fin j) : norm (largeTupleVector q a) = largePrimeTupleNorm q a := by
  cases a <;> rfl

lemma largeTupleVector_split {i j : ℕ} (f : (Fin i ⊕ Fin j) → Eisenstein) :
    largeTupleVector (fun a => f (.inl a),fun a => f (.inr a)) = f := by
  funext a
  cases a <;> rfl

lemma largeTuple_coordinate_support {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ)
    (hb : ∀ a, 2*largeTupleNormScale k a ≤ Real.exp primeProductWeights.radius*X)
    (a : Fin i ⊕ Fin j) (p : Eisenstein)
    (hw : largeTupleCoordinateWeight ξ X k a (norm p/largeTupleNormScale k a) ≠ 0) :
    p ∈ primeCutoff (Real.exp primeProductWeights.radius*X) ↔
      p ∈ fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X k) (largeTupleNormScale k) a := by
  rw [mem_primeCutoff,fullPrimeSupport_mem_iff _ _ (largeTupleNormScale_pos k)
    (fun a _x hx => largeTupleCoordinateWeight_high ξ X k a hx)]
  constructor
  · intro hp
    exact ⟨hp.1,hw⟩
  · rintro ⟨hp,_⟩
    have hn : norm p/largeTupleNormScale k a ≤ 2 :=
      le_of_not_gt (fun hx => hw (largeTupleCoordinateWeight_high ξ X k a hx))
    exact ⟨hp,((div_le_iff₀ (largeTupleNormScale_pos k a)).mp hn).trans (hb a)⟩

theorem largePrimeTuplePiece_high_full (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H : ℝ) {X : ℝ} (hX : 0 < X)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hhigh : X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    (hb : ∀ a, 2*largeTupleNormScale (fun a => (k a).val) a ≤ Real.exp primeProductWeights.radius*X) :
    largePrimeTuplePiece i j ℓ ξ Ct H X k =
      ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
        largeTupleIndependentSum i j ℓ ξ Ct H X (fun a => (k a).val) := by
  unfold largePrimeTuplePiece largeTupleIndependentSum
  congr 1
  have he := independent_tuple_sum_sum_type
    (fun _ : Fin i ⊕ Fin j => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fun q => (∏ a, largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
      (norm (largeTupleVector q a)/largeTupleNormScale (fun a => (k a).val) a))*
      centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (∏ a, largeTupleVector q a))
  simp_rw [largeTupleVector_split] at he
  rw [independent_tuple_sum_support
    (fun _ : Fin i ⊕ Fin j => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X (fun a => (k a).val))
      (largeTupleNormScale (fun a => (k a).val)))
    (fun a p => largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
      (norm p/largeTupleNormScale (fun a => (k a).val) a))
    (fun f => centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (∏ a, f a))
    (largeTuple_coordinate_support ξ X (fun a => (k a).val) hb)] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro q hq
  rw [largePrimeTupleTerm_high_box ℓ ξ Ct H hX k hhigh hq]
  simp only [largeTupleVector_norm,largeTupleVector_prod]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTuplePieceWitness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonzero actual pieces provide all coordinate-envelope hypotheses.
Thus no envelope admissibility is left as an extra analytic assumption. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largePrimeTuplePiece_witness {i j : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {Ct : ℕ} {H X : ℝ}
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hne : largePrimeTuplePiece i j ℓ ξ Ct H X k ≠ 0) :
    ∃ q ∈ largePrimeTupleBox i j X,
      largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  unfold largePrimeTuplePiece
  rw [Finset.sum_eq_zero h,mul_zero]

theorem eventually_largePrimeTuplePiece_high_full (i j : ℕ) {ξ : ℝ} (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (Ct : ℕ) (H : ℝ)
      (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val) →
      largePrimeTuplePiece i j ℓ ξ Ct H X k ≠ 0 →
      largePrimeTuplePiece i j ℓ ξ Ct H X k =
        ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
          largeTupleIndependentSum i j ℓ ξ Ct H X (fun a => (k a).val) := by
  filter_upwards [largePrimeTuplePiece_coordinate_envelope i j hξz,
    eventually_gt_atTop (0:ℝ)] with X hcoord hX
  intro ℓ Ct H k hhigh hne
  obtain ⟨q,hq,hqne⟩ := largePrimeTuplePiece_witness k hne
  exact largePrimeTuplePiece_high_full i j ℓ ξ Ct H hX k hhigh (hcoord ℓ Ct H k q hq hqne)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FlatTripleGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The largest coordinate of a flat triple gives a genuine transition
range. All lower bounds come from the original nonzero box. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largeTuple_singleton_product {i j : ℕ} (z : largeTupleBoxIndex i j)
    (a : Fin i ⊕ Fin j) :
    largeTupleGroupLength (Finset.univ\{a}) z*largeTupleNormScale z.1.2 a =
      ∏ b, largeTupleNormScale z.1.2 b := by
  have hh := Finset.prod_mul_prod_compl ({a} : Finset (Fin i ⊕ Fin j))
    (largeTupleNormScale z.1.2)
  simpa only [Finset.prod_singleton,mul_comm,largeTupleGroupLength,Finset.compl_eq_univ_sdiff] using hh

lemma largeTuple_product_le_cube {i j : ℕ} (hij : i+j = 3)
    (z : largeTupleBoxIndex i j) (a : Fin i ⊕ Fin j)
    (hmax : ∀ b, largeTupleNormScale z.1.2 b ≤ largeTupleNormScale z.1.2 a) :
    (∏ b, largeTupleNormScale z.1.2 b) ≤ (largeTupleNormScale z.1.2 a)^3 := by
  calc
    _ ≤ ∏ _b : Fin i ⊕ Fin j, largeTupleNormScale z.1.2 a :=
      Finset.prod_le_prod (fun b _ => (largeTupleNormScale_pos _ b).le) (fun b _ => hmax b)
    _ = _ := by simp [hij]

lemma eventually_maximum_triple_scale :
    ∀ᶠ X : ℝ in atTop, ∀ B P : ℝ, 0 ≤ B → X/16 ≤ P → P ≤ B^3 →
      X^(1/4:ℝ) ≤ B := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    eventually_const_mul_rpow_le (by norm_num : (3/4:ℝ) < 1) 16] with X hX hpow
  intro B P hB hlo hhi
  rw [Real.rpow_one] at hpow
  apply le_of_pow_le_pow_left₀ (by norm_num : (3:ℕ) ≠ 0) hB
  have he : (X^(1/4:ℝ))^3 = X^(3/4:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hX.le]
    norm_num
  rw [he]
  exact (le_div_iff₀ (by norm_num : (0:ℝ) < 16)).mpr (by simpa only [mul_comm] using hpow) |>.trans (hlo.trans hhi)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExceptionalTripleScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A surviving tuple in the specified exceptional neighborhood is
balanced enough that the product of the other two scales exceeds each
single scale. This supplies the lower transition range also off the
flat locus. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma exceptionalTriple_coordinate_exponent {i j : ℕ} {δ : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : largePrimeTupleExceptional δ q) (a : Fin i ⊕ Fin j) :
    |largePrimeTupleExponent q a-1/3| < δ := by
  exact (Finset.single_le_sum (fun b _ => abs_nonneg (largePrimeTupleExponent q b-1/3))
    (Finset.mem_univ a)).trans_lt hq.2

lemma exceptionalTriple_coordinate_norm {i j : ℕ} {δ X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hδ : δ ≤ 1/12) (hq : q ∈ largePrimeTupleBox i j X)
    (hex : largePrimeTupleExceptional δ q)
    (hln : 0 < Real.log (norm (largePrimeTupleProduct q))) (a : Fin i ⊕ Fin j) :
    largePrimeTupleNorm q a ≤ norm (largePrimeTupleProduct q)^(5/12:ℝ) := by
  have hn : 0 < norm (largePrimeTupleProduct q) := by
    rw [← largePrimeTupleNorm_prod]
    exact Finset.prod_pos (fun b _ => zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq b).1)
  have hp : 0 < largePrimeTupleNorm q a := zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1
  have hb := exceptionalTriple_coordinate_exponent hex a
  have he : largePrimeTupleExponent q a ≤ 5/12 := by
    linarith [le_abs_self (largePrimeTupleExponent q a-1/3)]
  apply (Real.log_le_log_iff hp (Real.rpow_pos_of_pos hn _)).mp
  rw [Real.log_rpow hn]
  exact (div_le_iff₀ hln).mp he

theorem exceptionalTriple_scale_square (i j : ℕ) {δ : ℝ} (hδ : δ ≤ 1/12) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H : ℝ) {N : ℕ}
      (k : (Fin i ⊕ Fin j) → Fin N),
      ∀ q ∈ largePrimeTupleBox i j X,
      largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
      largePrimeTupleExceptional δ q → ∀ a,
      (largeTupleNormScale (fun a => (k a).val) a)^2 ≤
        ∏ b, largeTupleNormScale (fun a => (k a).val) b := by
  filter_upwards [eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 200,
    eventually_const_mul_rpow_le (by norm_num : (5/6:ℝ) < 1) (16*3^(5/6:ℝ))]
    with X hX hlog hgap
  intro ℓ ξ Ct H N k q hq hne hex a
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨hn,hln⟩ := largePrimeTuplePiece_log_pos hX hlog k hne
  have hupper := exceptionalTriple_coordinate_norm hδ hq hex hln a
  have hcoord := (largePrimeTuplePiece_coordinate_range k (mul_ne_zero_iff.mp hne).2 a).1
  have hpow := pow_le_pow_left₀ (largeTupleNormScale_pos _ _).le (hcoord.trans hupper) 2
  have he : (norm (largePrimeTupleProduct q)^(5/12:ℝ))^2 =
      norm (largePrimeTupleProduct q)^(5/6:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hn.le]
    norm_num
  rw [he] at hpow
  have hprod := largePrimeTuplePiece_scale_product hXp k hne
  rw [hex.1] at hprod
  have hP : X/16 ≤ (∏ b, largeTupleNormScale (fun a => (k a).val) b) := by
    simpa only [largeTupleSubsetScale,show (2:ℝ)*2^3=16 by norm_num] using hprod.1
  have hu := (largePrimeTupleTerm_product_range hXp (mul_ne_zero_iff.mp hne).1).2
  change norm (largePrimeTupleProduct q) ≤ 3*X at hu
  calc
    _ ≤ norm (largePrimeTupleProduct q)^(5/6:ℝ) := hpow
    _ ≤ (3*X)^(5/6:ℝ) := Real.rpow_le_rpow hn.le hu (by norm_num)
    _ ≤ X/16 := by
      rw [Real.mul_rpow (by norm_num) hXp.le]
      rw [Real.rpow_one] at hgap
      apply (le_div_iff₀ (by norm_num : (0:ℝ) < 16)).mpr
      nlinarith
    _ ≤ _ := hP

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite tuple norm partition has only a fixed power of the
logarithm many pieces, uniformly in the growing prime envelope. -/
noncomputable section
namespace CubicFirstMoment

theorem largePrimeTuplePartition_count (i j : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℝ, 1 ≤ X →
      (Fintype.card ((Fin i ⊕ Fin j) → Fin
        (normPartitionCount (Real.exp primeProductWeights.radius*X))):ℝ) ≤
        D*(1+Real.log X)^(i+j) := by
  obtain ⟨K,hK,hcount⟩ := normPartitionCount_log_bound
  let R := primeProductWeights.radius
  have hR : 0 ≤ R := primeProductWeights.radius_nonneg
  refine ⟨(K*(1+R))^(i+j),by positivity,?_⟩
  intro X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hBX : 1 ≤ Real.exp R*X := one_le_mul_of_one_le_of_one_le (Real.one_le_exp hR) hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hb := hcount (Real.exp R*X) hBX
  rw [Real.log_mul (Real.exp_pos R).ne' hXp.ne',Real.log_exp] at hb
  have hN : (normPartitionCount (Real.exp R*X):ℝ) ≤ K*(1+R)*(1+Real.log X) := by
    apply hb.trans
    nlinarith [mul_nonneg hR hlogX]
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_sum,Nat.cast_pow]
  change (normPartitionCount (Real.exp R*X):ℝ)^(i+j) ≤ _
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hN (i+j)).trans_eq
  rw [mul_pow]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeLowWindow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual semiprime kernel in low height and a finite Mellin window.
All coordinate cutoffs have been reconstructed before cancellation is used. -/
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma semiprime_low_mellin_height {L : ℝ} (hL : 2 ≤ L) (Ct Cs : ℕ)
    {t τ : ℝ} (ht : t ∈ Icc (-(4/3)*L^Ct) ((4/3)*L^Ct))
    (hτ : τ ∈ Icc (-(L^Cs)) (L^Cs)) : |t-τ| ≤ L^(Ct+Cs+2) := by
  have hL1 : 1 ≤ L := by linarith
  have ht' : |t| ≤ (4/3)*L^Ct := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
  have hτ' : |τ| ≤ L^Cs := abs_le.mpr hτ
  have hCt : L^Ct ≤ L^(Ct+Cs) := pow_le_pow_right₀ hL1 (Nat.le_add_right _ _)
  have hCs : L^Cs ≤ L^(Ct+Cs) := pow_le_pow_right₀ hL1 (Nat.le_add_left _ _)
  calc
    _ ≤ |t|+|τ| := abs_sub t τ
    _ ≤ (4/3)*L^Ct+L^Cs := add_le_add ht' hτ'
    _ ≤ (7/3)*L^(Ct+Cs) := by linarith
    _ ≤ L^(Ct+Cs)*L^2 := by
      have hsq : (7/3:ℝ) ≤ L^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (pow_nonneg (by linarith : 0 ≤ L) (Ct+Cs))]
    _ = _ := (pow_add _ _ _).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleKernelCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The regrouping identity with the actual squarefree product kernel,
including arbitrary smooth envelopes and height integrals. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma ordered_product_kernel_squarefree (S : ι → Finset Eisenstein)
    (T : κ → Finset Eisenstein) (w : ι → Eisenstein → ℂ) (v : κ → Eisenstein → ℂ)
    (hS : ∀ i a, a ∈ S i → primary a) (hT : ∀ i a, a ∈ T i → primary a)
    (K : Eisenstein → ℂ) (hK : ∀ n, primary n → ¬Squarefree n → K n = 0) :
    (∑ a ∈ orderedConvolutionSupport S, ∑ b ∈ orderedConvolutionSupport T,
      orderedConvolution S w a*orderedConvolution T v b*K (a*b)) =
      ∑ a ∈ (orderedConvolutionSupport S).filter Squarefree,
        ∑ b ∈ (orderedConvolutionSupport T).filter Squarefree,
          squarefreeConvolution S w a*squarefreeConvolution T v b*K (a*b) := by
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  have hpa := orderedPrimarySupport_primary S hS ha
  by_cases hsa : Squarefree a
  · simp only [hsa,ite_true, if_true]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hsb : Squarefree b
    · simp only [hsb,ite_true, if_true,squarefreeConvolution,hsa]
    · have hn : ¬Squarefree (a*b) := fun h => hsb (h.squarefree_of_dvd (dvd_mul_left b a))
      rw [hK (a*b) (primary_mul hpa (orderedPrimarySupport_primary T hT hb)) hn]
      simp only [hsb,ite_false, if_false,mul_zero]
  · simp only [hsa,ite_false, if_false]
    apply Finset.sum_eq_zero
    intro b hb
    have hn : ¬Squarefree (a*b) := fun h => hsa (h.squarefree_of_dvd (dvd_mul_right a b))
    rw [hK (a*b) (primary_mul hpa (orderedPrimarySupport_primary T hT hb)) hn,mul_zero]

lemma independent_prime_tuple_kernel (s : Finset ι) (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (hS : ∀ i a, a ∈ S i → primary a)
    (K : Eisenstein → ℂ) (hK : ∀ n, primary n → ¬Squarefree n → K n = 0) :
    (∑ f ∈ Fintype.piFinset S, (∏ i, w i (f i))*K (∏ i, f i)) =
      ∑ a ∈ (orderedConvolutionSupport (fun a : s => S a)).filter Squarefree,
        ∑ b ∈ (orderedConvolutionSupport (fun a : {a : ι // a ∉ s} => S a)).filter Squarefree,
          squarefreeConvolution (fun a : s => S a) (fun a p => w a p) a*
          squarefreeConvolution (fun a : {a : ι // a ∉ s} => S a) (fun a p => w a p) b*K (a*b) := by
  have hp (f : ι → Eisenstein) :
      (∏ a : s, f a)*(∏ a : {a : ι // a ∉ s}, f a) = ∏ a, f a := by
    rw [←Finset.prod_subtype s (fun _ => Iff.rfl) f,
      ←Finset.prod_subtype (Finset.univ\s) (by simp) f]
    exact Finset.prod_mul_prod_compl s f
  have he := independent_prime_tuple_bilinear s S w (fun a b => K (a*b))
  simp only [hp] at he
  rw [he]
  exact ordered_product_kernel_squarefree
    (fun a : s => S a) (fun a : {a : ι // a ∉ s} => S a)
    (fun a : s => w a) (fun a : {a : ι // a ∉ s} => w a)
    (fun i a ha => hS i a ha) (fun i a ha => hS i a ha) K hK

lemma centeredHeightKernel_squarefree_zero (ℓ : ℤ) (W : ℝ → ℂ)
    (H T X X₀ : ℝ) (n : Eisenstein) (hn : primary n) (hs : ¬Squarefree n) :
    centeredHeightKernel ℓ W H T X X₀ n = 0 := by
  simp only [centeredHeightKernel,centeredGauss_vanishes hn hs,mul_zero,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleKernelRegroup
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact regrouping of the actual high-box kernel. Squarefreeness is
retained through the centered kernel and full prime convolutions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem largeTupleIndependentSum_regroup (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H X : ℝ) (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :
    largeTupleIndependentSum i j ℓ ξ Ct H X k =
      largeTupleRegroupedKernel i j ℓ ξ Ct H X k s := by
  have he := independent_prime_tuple_kernel s
    (fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X k) (largeTupleNormScale k))
    (fun a p => largeTupleCoordinateWeight ξ X k a (norm p/largeTupleNormScale k a))
    (fun a p hp => (fullPrimeSupport_prime 2 (largeTupleCoordinateWeight ξ X k)
      (largeTupleNormScale k) a p hp).1)
    (centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X)
    (centeredHeightKernel_squarefree_zero ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X)
  have hS : (fun a : s => fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X k)
      (largeTupleNormScale k) a) =
      fullPrimeSupport 2 (fun a : s => largeTupleCoordinateWeight ξ X k a)
        (fun a : s => largeTupleNormScale k a) := rfl
  have hT : (fun a : {a : Fin i ⊕ Fin j // a ∉ s} =>
      fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X k) (largeTupleNormScale k) a) =
      fullPrimeSupport 2
        (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleCoordinateWeight ξ X k a)
        (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale k a) := rfl
  rw [hS,hT] at he
  simpa only [largeTupleIndependentSum,largeTupleRegroupedKernel,
    fullSquarefreePrimeSupport,fullPrimeCoefficient,isCoprime_one_right,and_true] using he


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleKernelIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual regrouped kernel on the full Mellin line. No product
cutoff or Mellin-frequency remainder is discarded by these identities. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem largeTupleRegroupedKernel_low_integral {i j : ℕ} (ℓ : ℤ) (ξ X : ℝ)
    (Ct : ℕ) {H : ℝ} (hH : 0 < H) (k : (Fin i ⊕ Fin j) → ℕ)
    (s : Finset (Fin i ⊕ Fin j)) :
    largeTupleRegroupedKernel i j ℓ ξ Ct H X k s =
      ∫ t : ℝ, (lowHeightWeight H ((1+Real.log X)^Ct) t*
        Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*
          largeTupleSmoothedPolynomial ℓ ξ X k s t := by
  exact centered_product_low_integral (largeTupleSelectedSupport ξ X k s)
    (largeTupleOtherSupport ξ X k s) (largeTupleSelectedCoefficient ξ X k s)
    (largeTupleOtherCoefficient ξ X k s) ℓ primeProductEnvelope X X
    ((1+Real.log X)^Ct) hH


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleRestrictedWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate weights restricted to either predicate in a fixed
partition of the tuple indices. This preserves the predicate-subtype
indexing in the exact finite convolution identity. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {i j : ℕ} (P : (Fin i ⊕ Fin j) → Prop) [DecidablePred P]

lemma largeTupleRestrictedLength_notMem (s : Finset (Fin i ⊕ Fin j))
    (z : largeTupleBoxIndex i j) :
    largeTupleRestrictedLength (fun a => a ∉ s) z =
      largeTupleGroupLength (Finset.univ\s) z := by
  exact (Finset.prod_subtype (Finset.univ\s) (by simp)
    (fun a => largeTupleNormScale z.1.2 a)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TripleKernelScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The largest coordinate of a triple has a fixed power lower bound.
These normalizations preserve the fractional logarithmic saving. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma triple_log_comparison {X B : ℝ} (hX : 1 ≤ X)
    (hB : X^(1/4:ℝ) ≤ B) :
    (1/4:ℝ)*(1+Real.log X) ≤ 1+Real.log B := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hh := Real.log_le_log (Real.rpow_pos_of_pos hXp (1/4:ℝ)) hB
  rw [Real.log_rpow hXp] at hh
  linarith

lemma eventually_triple_height_comparison (U : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, X^(1/4:ℝ) ≤ B →
      (1+Real.log X)^U ≤ (1+Real.log B)^(U+1) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop ((4:ℝ)^(U+1))] with X hX hlarge
  intro B hB
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 1/4)).trans hB
  have hL := triple_log_comparison hX hB
  have hLX : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hLB : 0 ≤ 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hinv : 1+Real.log X ≤ (4:ℝ)*(1+Real.log B) := by linarith
  have hbig : (4:ℝ)^U ≤ 1+Real.log B := by
    have he : (4:ℝ)^U = (1/4:ℝ)*(4:ℝ)^(U+1) := by rw [pow_succ]; ring
    rw [he]
    nlinarith
  calc
    _ ≤ ((4:ℝ)*(1+Real.log B))^U := pow_le_pow_left₀ hLX hinv U
    _ = (4:ℝ)^U*(1+Real.log B)^U := mul_pow _ _ _
    _ ≤ (1+Real.log B)*(1+Real.log B)^U :=
      mul_le_mul_of_nonneg_right hbig (pow_nonneg hLB _)
    _ = _ := by rw [pow_succ]; ring

lemma triple_bilinear_nat_scale {X A B K : ℝ} (hX : 1 ≤ X)
    (hA : 0 ≤ A) (hB : X^(1/4:ℝ) ≤ B) (hK : 0 ≤ K)
    (hAB : A*B ≤ 3*X) (k : ℕ) :
    K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k ≤
      (K*3^(5/6:ℝ)/(1/4:ℝ)^k)*X^(5/6:ℝ)/(1+Real.log X)^k := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 1/4)).trans hB
  have hL := triple_log_comparison hX hB
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hLB : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hp := Real.rpow_le_rpow (mul_nonneg hA (zero_le_one.trans hB1)) hAB
    (by norm_num : (0:ℝ) ≤ 5/6)
  rw [Real.mul_rpow hA (zero_le_one.trans hB1),Real.mul_rpow (by norm_num) hXp.le] at hp
  calc
    _ ≤ K*(3^(5/6:ℝ)*X^(5/6:ℝ))/(1+Real.log B)^k := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hLB.le _)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hK
    _ ≤ K*(3^(5/6:ℝ)*X^(5/6:ℝ))/((1/4:ℝ)*(1+Real.log X))^k :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity) _)
        (pow_le_pow_left₀ (by positivity) hL k)
    _ = _ := by rw [mul_pow]; field_simp


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NearFlatGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complement of the explicitly counted flat boxes supplies the
logarithmic length gap required by the ordinary bilinear estimate. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma nonflat_singleton_length_gap {i j : ℕ} (z : largeTupleBoxIndex i j)
    (a : Fin i ⊕ Fin j) {Z : ℝ} (hZ : 0 < Z) (G : ℕ)
    (hmax : ∀ b, largeTupleNormScale z.1.2 b ≤ largeTupleNormScale z.1.2 a)
    (hn : ¬∃ B : ℝ, (∀ b, largeTupleNormScale z.1.2 b ≤ B) ∧
      B^3 ≤ (∏ b, largeTupleNormScale z.1.2 b)*Z^G) :
    largeTupleGroupLength (Finset.univ\{a}) z ≤ (largeTupleNormScale z.1.2 a)^2/Z^G := by
  have hB := largeTupleNormScale_pos z.1.2 a
  have hh : (∏ b, largeTupleNormScale z.1.2 b)*Z^G < (largeTupleNormScale z.1.2 a)^3 :=
    lt_of_not_ge (fun h => hn ⟨_,hmax,h⟩)
  rw [← largeTuple_singleton_product z a] at hh
  apply (le_div_iff₀ (pow_pos hZ G)).mpr
  apply le_of_lt
  apply (mul_lt_mul_iff_right₀ hB).mp
  calc
    _ = (largeTupleGroupLength (Finset.univ\{a}) z*largeTupleNormScale z.1.2 a)*Z^G := by ring
    _ < (largeTupleNormScale z.1.2 a)^3 := hh
    _ = _ := by ring

lemma nearFlat_log_denominator {X B : ℝ} (hX : 1 ≤ X) (hB : 1 ≤ B)
    (hBX : B ≤ 3*X) {g G : ℕ} (hg : g+1 ≤ G)
    (hlarge : max 2 ((2:ℝ)^g) ≤ 1+Real.log X) :
    (1+Real.log B)^g ≤ (1+Real.log X)^G := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hlog := Real.log_le_log (zero_lt_one.trans_le hB) hBX
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hXp.ne'] at hlog
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
  have hZX : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hZB : 0 ≤ 1+Real.log B := by linarith [Real.log_nonneg hB]
  calc
    _ ≤ (2*(1+Real.log X))^g := pow_le_pow_left₀ hZB (by linarith [le_max_left 2 ((2:ℝ)^g)]) g
    _ = (2:ℝ)^g*(1+Real.log X)^g := mul_pow _ _ _
    _ ≤ (1+Real.log X)*(1+Real.log X)^g :=
      mul_le_mul_of_nonneg_right ((le_max_right 2 ((2:ℝ)^g)).trans hlarge) (by positivity)
    _ = (1+Real.log X)^(g+1) := by rw [pow_succ]; ring
    _ ≤ _ := pow_le_pow_right₀ hZX hg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleExceptionalHigh
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining high exceptional boxes split exactly into the flat
subfamily and its complement. Both are negligible on the stated scale. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largePrimeTupleExceptionalHigh_split (i j : ℕ) (ξ δ : ℝ) (Ct G : ℕ) (H X : ℝ) :
    largePrimeTupleExceptionalHighSum i j ξ δ Ct H X =
      largePrimeTupleSelectedFlatHighSum i j ξ Ct G H X
        (largeTupleExceptionalSelector i j ξ δ Ct H X) +
      largePrimeTupleExceptionalNonflatSum i j ξ δ Ct G H X := by
  let S := largePrimeTupleFlatBoxSet i j 0 ξ Ct G H X
  let f := fun d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)) =>
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      largeTupleExceptionalSelector i j ξ δ Ct H X d then
      largePrimeTuplePiece i j 0 ξ Ct H X d else 0
  have hs : Finset.univ.filter (fun d => d ∈ S) = S := by ext d; simp
  have he : (∑ d ∈ S, f d) = ∑ d, if d ∈ S then f d else 0 := by
    calc
      _ = ∑ d ∈ Finset.univ.filter (fun d => d ∈ S), f d := by rw [hs]
      _ = _ := by rw [Finset.sum_filter]
  unfold largePrimeTupleExceptionalHighSum largePrimeTupleSelectedFlatHighSum
    largePrimeTupleExceptionalNonflatSum
  dsimp only [f,S] at he
  rw [he,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simp only [largeTupleExceptionalSelector]
  by_cases hp : X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      largeTupleExceptionalSelector i j ξ δ Ct H X d
  · dsimp only [largeTupleExceptionalSelector] at hp
    by_cases hd : d ∈ S
    · dsimp only [S] at hd
      simp only [hp,hd,true_and,not_true_eq_false,and_false,ite_true, if_true,ite_false, if_false,add_zero]
    · dsimp only [S] at hd
      simp only [hp,hd,not_false_eq_true,and_true,ite_true, if_true,ite_false, if_false,zero_add]
  · dsimp only [largeTupleExceptionalSelector] at hp
    simp only [hp,false_and,ite_false, if_false,ite_self,add_zero]

lemma largePrimeTupleExceptionalHighSum_zero (i j : ℕ) (hij : i+j ≠ 3)
    (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ) :
    largePrimeTupleExceptionalHighSum i j ξ δ Ct H X = 0 := by
  unfold largePrimeTupleExceptionalHighSum
  apply Finset.sum_eq_zero
  intro d _
  split_ifs with hd
  · by_contra hne
    obtain ⟨q,hq,hqne⟩ := largePrimeTuplePiece_witness d hne
    have hex : largePrimeTupleExceptional δ q := by
      by_contra hh
      exact hd.2 ⟨q,hq,hqne,hh⟩
    exact hij hex.1
  · rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleHighSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All high boxes of each actual large-row arity are negligible. The
separate sharp-cutoff boundary contribution is retained explicitly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largePrimeTupleHighSum_split (i j : ℕ) (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ) :
    largePrimeTupleHighSum i j ξ Ct H X = largePrimeTupleOrdinaryHighSum i j ξ δ Ct H X +
      largePrimeTupleExceptionalHighSum i j ξ δ Ct H X := by
  unfold largePrimeTupleHighSum largePrimeTupleOrdinaryHighSum largePrimeTupleExceptionalHighSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hh : X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val)
  · by_cases ho : ∃ q ∈ largePrimeTupleBox i j X,
      largePrimeTupleTerm i j 0 ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
        ¬largePrimeTupleExceptional δ q <;> simp only [hh,ho,true_and,not_true_eq_false,not_false_eq_true,ite_true, if_true,ite_false, if_false,add_zero,zero_add]
  · simp only [hh,false_and,ite_false, if_false,zero_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralPrimeProductSmoothedBilinear
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full Mellin transfer of the published-input prime-product estimate.
Both the finite window and its complete complement are controlled, with
constants uniform in the independent weights, scales and envelope length. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ]


theorem full_prime_centered_smoothed_bilinear_actual
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
    (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
    (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
    (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
    (hAlo : ∀ r i x, x < 1 → WA r i x = 0) (hAhi : ∀ r i x, R < x → WA r i x = 0)
    (hBlo : ∀ r i x, x < 1 → WB r i x = 0) (hBhi : ∀ r i x, R < x → WB r i x = 0)
    (hWA1 : ∀ r i x, ‖WA r i x‖ ≤ 1) (hWB1 : ∀ r i x, ‖WB r i x‖ ≤ 1) (k U : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (X u : ℝ),
      B₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
      (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
      (LB r)^(1-η/16) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
      0 < X → |u| ≤ (1+Real.log (LB r))^U →
      ‖centeredProductSmoothed (fullSquarefreePrimeSupport R (WA r) XA 1)
        (fullSquarefreePrimeSupport R (WB r) XB 1)
        (fullPrimeCoefficient R (WA r) XA) (fullPrimeCoefficient R (WB r) XB)
        0 primeProductEnvelope X u‖ ≤ K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
  obtain ⟨ηh,σh,Gh,Kh,Th,m,hηh,hηh1,hσh,hKh,hheight⟩ := full_prime_product_height_bilinear
    hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ LA LB WA WB hLA hLB hWA hWB
    hAlo hAhi hBlo hBhi 0
  obtain ⟨ηp,σp,Gp,Kp,Tp,hηp,hηp1,hσp,hKp,hpoint⟩ := full_prime_centered_product_bilinear_actual
    hSW hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ  hGamma
    LA LB WA WB hLA hLB hWA hWB hAlo hAhi hBlo hBhi k (U+(m+k)+2)
  obtain ⟨D,hD,htail⟩ := fullPrimeProduct_centered_mellin_tail (ι := ι) (κ := κ)
    (zero_le_one.trans hR) primeProductEnvelope primeProductEnvelope_compact
    primeProductEnvelope_positive primeProductEnvelope_smooth
  let M := zeroLineMellinMass primeProductEnvelope
  have hM : 0 ≤ M := by
    rw [show M = ∫ t : ℝ, ‖zeroLineMellinWeight primeProductEnvelope 1 t‖ from
      (zeroLineMellinWeight_mass primeProductEnvelope (by norm_num)).symm]
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  obtain ⟨Tg,hTg⟩ := eventually_atTop.mp
    (overlap_power_log_saving (by norm_num : (0:ℝ) < 7/20) U 0)
  refine ⟨min ηp ηh,max Gp Gh,M*Kp+D*(Kh+1),max (max Tp Th) (max Tg (Real.exp 1)),
    lt_min hηp hηh,(min_le_left _ _).trans hηp1,by positivity,?_⟩
  intro r XA XB X u hT hprodA hprodB hXA hXB hAlow hAhigh hX hu
  have hTp : Tp ≤ LB r := (le_max_left Tp Th).trans ((le_max_left _ _).trans hT)
  have hTh : Th ≤ LB r := (le_max_right Tp Th).trans ((le_max_left _ _).trans hT)
  have hTg' : Tg ≤ LB r := (le_max_left Tg (Real.exp 1)).trans ((le_max_right _ _).trans hT)
  have hB1 := hLB r
  have hBp : 0 < LB r := zero_lt_one.trans_le hB1
  have hAp : 0 < LA r := zero_lt_one.trans_le (hLA r)
  have hlog : 1 ≤ Real.log (LB r) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      ((le_max_right Tg (Real.exp 1)).trans ((le_max_right _ _).trans hT))
    simpa only [Real.log_exp] using h
  have hL : 0 < 1+Real.log (LB r) := by linarith
  have hL1 : 1 ≤ 1+Real.log (LB r) := by linarith
  have hXA' : ∀ i, 0 < XA i := fun i => zero_lt_one.trans_le (hXA i)
  have hXB' : ∀ i, 0 < XB i := fun i =>
    (Real.rpow_pos_of_pos (by positivity : 0 < 2*LB r) c).trans (hXB i)
  have hupper (g : ℕ) (hg : g ≤ max Gp Gh) : LA r ≤ (LB r)^2/(1+Real.log (LB r))^g :=
    hAhigh.trans (div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hL g)
      (pow_le_pow_right₀ hL1 hg))
  have hAraw : LA r ≤ (LB r)^2 :=
    (hupper 0 (Nat.zero_le _)).trans_eq (by simp)
  have hApoint : (LB r)^(1-ηp/16) ≤ LA r :=
    (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith [min_le_left ηp ηh])).trans hAlow
  have hAheight : (LB r)^(1-ηh/4) ≤ LA r :=
    (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith [min_le_right ηp ηh])).trans hAlow
  let S := (1+Real.log (LB r))^(m+k)
  have hS : 0 < S := pow_pos hL _
  have huB : |u| ≤ (LB r)^(7/20:ℝ) := by
    apply hu.trans
    apply (div_le_one (Real.rpow_pos_of_pos hBp _)).mp
    simpa only [Nat.mul_zero,pow_zero,div_one] using hTg (LB r) hTg'
  have htail' := htail (WA r) (WB r) XA XB hXA' hXB' (hAlo r) (hAhi r) (hBlo r) (hBhi r)
    (hWA1 r) (hWB1 r) (by simpa only [hprodB] using hB1)
    (by simpa only [hprodA,hprodB] using hAraw) X u S Kh hX hS hKh.le (by
      intro T hST hThi
      have hh := hheight r XA XB 1 1 u T hTh hprodA hprodB hXA hXB hAheight
        (hupper Gh (le_max_right _ _)) one_ne_zero
        (by rw [norm_one_eq]; exact Real.one_le_rpow hB1 hσh.le)
        ((pow_le_pow_right₀ hL1 (Nat.le_add_right m k)).trans hST)
        (by simpa only [hprodB] using hThi) huB
      simpa only [pow_zero,div_one,fullPrimeProductGauss,hprodA,hprodB,
        Real.mul_rpow hAp.le hBp.le,mul_assoc] using hh)
  have hlocal := centeredMellinWindow_bound (fullSquarefreePrimeSupport R (WA r) XA 1)
    (fullSquarefreePrimeSupport R (WB r) XB 1) (fullPrimeCoefficient R (WA r) XA)
    (fullPrimeCoefficient R (WB r) XB) 0 primeProductEnvelope primeProductEnvelope_compact
    primeProductEnvelope_positive primeProductEnvelope_smooth hX
    (by positivity : 0 ≤ Kp*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) S u (by
      intro τ hτ
      have hh := hpoint r XA XB 1 1 (u-τ) hTp hprodA hprodB hXA hXB hApoint
        (hupper Gp (le_max_left _ _)) one_ne_zero
        (by rw [norm_one_eq]; exact Real.one_le_rpow hB1 hσp.le)
        (semiprime_low_mellin_height (by linarith) U (m+k)
          (show u ∈ Icc (-(4/3)*(1+Real.log (LB r))^U)
              ((4/3)*(1+Real.log (LB r))^U) from
            ⟨by nlinarith [neg_abs_le u, pow_nonneg hL.le U],
              by nlinarith [le_abs_self u, pow_nonneg hL.le U]⟩) hτ)
      simpa only [centeredProductPolynomial,theta_zero,mul_one] using hh)
  have he := centered_product_mellin_complement (fullSquarefreePrimeSupport R (WA r) XA 1)
    (fullSquarefreePrimeSupport R (WB r) XB 1) (fullPrimeCoefficient R (WA r) XA)
    (fullPrimeCoefficient R (WB r) XB)
    (fun p hp => (fullSquarefreePrimeSupport_primary _ _ _ _ hp).1)
    (fun p hp => (fullSquarefreePrimeSupport_primary _ _ _ _ hp).1)
    0 primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth hX S u
  have ht : D*(Kh+1)*((∏ i, XA i)*(∏ i, XB i))^(5/6:ℝ)/S ≤
      D*(Kh+1)*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
    rw [hprodA,hprodB,Real.mul_rpow hAp.le hBp.le]
    exact (div_le_div_of_nonneg_left (by positivity) (pow_pos hL k)
      (pow_le_pow_right₀ hL1 (Nat.le_add_left k m))).trans_eq (by ring)
  rw [he]
  apply (norm_add_le _ _).trans
  exact (add_le_add hlocal (htail'.trans ht)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralLargeTupleRestrictedSmoothed
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full Mellin smoothing for the precise predicate-indexed coefficients
in the actual regrouping identity. The two independent coordinate products have
exactly their original smooth weights. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem large_tuple_restricted_smoothed_actual {i j : ℕ}
    (s : Finset (Fin i ⊕ Fin j)) (hs : s.Nonempty)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k U : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K T₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (z : largeTupleBoxIndex i j) (u : ℝ),
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      T₀ ≤ B → (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      B^(1-η/16) ≤ A → A ≤ B^2/(1+Real.log B)^G → |u| ≤ (1+Real.log B)^U →
      ‖largeTupleSmoothedPolynomial 0 ξ z.1.1 z.1.2 s u‖ ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  let : Nonempty s := hs.to_subtype
  obtain ⟨η,G,K,T₀,hη,hη1,hK,hbound⟩ := full_prime_centered_smoothed_bilinear_actual
    hSW hpub hHuxley hperiod hMV hC (by positivity : (0:ℝ) < ξ/2)
    (by linarith : ξ/2 ≤ 1) (by norm_num : (1:ℝ) ≤ 2) hGI hGQ  hGamma
    (largeTupleRestrictedLength (fun a => a ∉ s)) (largeTupleGroupLength s)
    (largeTupleRestrictedWeight (fun a => a ∉ s) ξ) (largeTupleGroupWeight ξ s)
    (largeTupleRestrictedLength_one (fun a => a ∉ s))
    (largeTupleGroupLength_one s)
    (largeTupleRestrictedLogWeights (fun a => a ∉ s) ξ)
    (largeTupleGroupLogWeights ξ s)
    (fun z a _x hx => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 a hx)
    (fun z a x => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 a x)
    (fun z a x => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 a x) k U
  refine ⟨η,G,K,T₀,hη,hη1,hK,?_⟩
  intro z u
  dsimp only
  intro hT hrough hAlow hAhigh hu
  have hb := hbound z
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale z.1.2 a)
    (fun a : s => largeTupleNormScale z.1.2 a) z.1.1 u
  simp only [largeTupleRestrictedLength_notMem] at hb
  have hh := hb hT (largeTupleRestrictedLength_notMem s z)
    (Finset.prod_coe_sort s (fun a => largeTupleNormScale z.1.2 a))
    (fun a => z.property a) hrough hAlow hAhigh z.1.1.property hu
  have hWA : largeTupleRestrictedWeight (fun a => a ∉ s) ξ z =
      (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleCoordinateWeight ξ z.1.1 z.1.2 a) := rfl
  have hWB : largeTupleGroupWeight ξ s z =
      (fun a : s => largeTupleCoordinateWeight ξ z.1.1 z.1.2 a) := rfl
  rw [hWA,hWB] at hh
  unfold largeTupleSmoothedPolynomial
  rw [centeredProductSmoothed_swap]
  exact hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralLargeTupleNearFlatKernel
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete low-height kernel with a quarter-power lower bound on
the selected group. This covers near-flat exceptional triples. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem large_tuple_quarter_group_low_kernel_actual {i j : ℕ}
    (s : Finset (Fin i ⊕ Fin j)) (hs : s.Nonempty)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k Ct : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ᶠ X : ℝ in atTop, ∀ (z : largeTupleBoxIndex i j) (H : ℝ), z.1.1 = X → 0 < H →
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      X^(1/4:ℝ) ≤ B → A*B ≤ 3*X → B₀ ≤ B →
      (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      B^(1-η/16) ≤ A → A ≤ B^2/(1+Real.log B)^G →
      ‖largeTupleRegroupedKernel i j 0 ξ Ct H X z.1.2 s‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨η,G,K₀,B₀,hη,hη1,hK₀,hbound⟩ := large_tuple_restricted_smoothed_actual s hs hSW hpub
    hHuxley hperiod hMV hC hξ hξz hGI hGQ  hGamma (k+Ct) (Ct+2)
  let K₁ := K₀*3^(5/6:ℝ)/(1/4:ℝ)^(k+Ct)
  refine ⟨η,G,(8/3)*Real.log 2*K₁,B₀,hη,hη1,by dsimp [K₁]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_triple_height_comparison (Ct+1)] with X hX hlog hheight
  intro z H hz hH
  dsimp only
  intro hBX hAB hB₀ hrough hAlow hAhigh
  have hL : 0 < 1+Real.log X := by linarith
  have hLp : 2 ≤ 1+Real.log X := by linarith
  have hnorm (t : ℝ) (ht : t ∈ Icc (-(4/3)*(1+Real.log X)^Ct) ((4/3)*(1+Real.log X)^Ct)) :
      ‖largeTupleSmoothedPolynomial 0 ξ z.1.1 z.1.2 s t‖ ≤ K₁*X^(5/6:ℝ)/(1+Real.log X)^(k+Ct) := by
    have ht' : |t| ≤ (4/3)*(1+Real.log X)^Ct := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
    have hu : |t| ≤ (1+Real.log (largeTupleGroupLength s z))^(Ct+2) := by
      apply (ht'.trans _).trans (hheight _ hBX)
      rw [pow_succ]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        ((by norm_num : (4/3:ℝ) ≤ 2).trans hLp) (pow_nonneg hL.le Ct)
    have hb := hbound z t hB₀ hrough hAlow hAhigh hu
    exact hb.trans (triple_bilinear_nat_scale hX (zero_le_one.trans (largeTupleGroupLength_one _ z))
      hBX hK₀.le hAB (k+Ct))
  have he := largeTupleRegroupedKernel_low_integral 0 ξ X Ct hH z.1.2 s
  have hsame (t : ℝ) : largeTupleSmoothedPolynomial 0 ξ X z.1.2 s t =
      largeTupleSmoothedPolynomial 0 ξ z.1.1 z.1.2 s t := by rw [hz]
  rw [he]
  simp_rw [hsame]
  have he' : (∫ t : ℝ, (lowHeightWeight H ((1+Real.log X)^Ct) t*
      Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*largeTupleSmoothedPolynomial 0 ξ z.1.1 z.1.2 s t) =
      ∫ t : ℝ, lowHeightWeight H ((1+Real.log X)^Ct) t*
        (Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*largeTupleSmoothedPolynomial 0 ξ z.1.1 z.1.2 s t) := by
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [he']
  have hh := lowHeightWeight_integral_bound H (pow_pos hL Ct)
    (by dsimp [K₁]; positivity : 0 ≤ K₁*X^(5/6:ℝ)/(1+Real.log X)^(k+Ct))
    (fun t => Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*
      largeTupleSmoothedPolynomial 0 ξ z.1.1 z.1.2 s t) (by
        intro t ht
        rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
        exact hnorm t ht)
  apply hh.trans_eq
  rw [pow_add]
  field_simp [hL.ne']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralLargeTupleNonflatHigh
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high exceptional triples outside the counted flat set have a
logarithmic bilinear gap. Their actual smooth boxes therefore have
arbitrary logarithmic saving. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem largePrimeTuplePiece_nonflat_high_bound_actual (i j : ℕ) (hij : i+j = 3)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : δ ≤ 1/12)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k Ct : ℕ) :
    ∃ (G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ H : ℝ, 0 < H →
      ∀ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) →
      d ∉ largePrimeTupleFlatBoxSet i j 0 ξ Ct G H X →
      (∃ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j 0 ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
          largePrimeTupleExceptional δ q) →
      ‖largePrimeTuplePiece i j 0 ξ Ct H X d‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  have hdata (a : Fin i ⊕ Fin j) := large_tuple_quarter_group_low_kernel_actual {a} (by simp)
    hSW hpub hHuxley hperiod hMV hC hξ hξz hGI hGQ  hGamma k Ct
  choose η G K B₀ hη hη1 hK hbound using hdata
  let G₀ : ℕ := 1+∑ a, G a
  have hGle (a : Fin i ⊕ Fin j) : G a+1 ≤ G₀ := by
    have hh := Finset.single_le_sum (fun b _ => Nat.zero_le (G b)) (Finset.mem_univ a)
    dsimp [G₀]
    omega
  let K₀ : ℝ := 1+∑ a, K a
  have hK₀ : 0 < K₀ := by
    have hh := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin i ⊕ Fin j)))
      (fun a _ => (hK a).le)
    dsimp [K₀]
    linarith
  have hKle (a : Fin i ⊕ Fin j) : K a ≤ K₀ := by
    have hh := Finset.single_le_sum (fun b _ => (hK b).le) (Finset.mem_univ a)
    dsimp [K₀]
    linarith
  have hB₀ := (Filter.eventually_all).mpr (fun a =>
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).eventually_ge_atTop (B₀ a))
  have hloglimit : Tendsto (fun X : ℝ => 1+Real.log X) atTop atTop :=
    tendsto_const_nhds.add_atTop Real.tendsto_log_atTop
  have hloglarge := (Filter.eventually_all).mpr (fun a =>
    hloglimit.eventually_ge_atTop
      (max 2 ((2:ℝ)^(G a))))
  let c : ℂ := (i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹
  refine ⟨G₀,(‖c‖+1)*K₀,by positivity,?_⟩
  filter_upwards [(Filter.eventually_all).mpr hbound,hB₀,hloglarge,
    exceptionalTriple_scale_square i j hδ,eventually_maximum_triple_scale,
    largePrimeTuplePiece_rough_scales i j hξ hξz,
    eventually_largePrimeTuplePiece_high_full i j hξz,eventually_ge_atTop (1:ℝ)]
    with X hb hB₀ hloglarge hsquare hquarter hrough hfull hX
  intro H hH d hhigh hnot hex
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  by_cases hne : largePrimeTuplePiece i j 0 ξ Ct H X d = 0
  · rw [hne,norm_zero]
    positivity
  obtain ⟨q,hq,hqne,hqex⟩ := hex
  obtain ⟨hcoord,hrough⟩ := hrough 0 Ct H d q hq hqne
  let z : largeTupleBoxIndex i j := ⟨(⟨X,hXp⟩,fun a => (d a).val),hcoord⟩
  let : Nonempty (Fin i ⊕ Fin j) := Fintype.card_pos_iff.mp (by simp [hij])
  obtain ⟨a,_ha,hmax⟩ := Finset.exists_max_image Finset.univ
    (largeTupleNormScale z.1.2) Finset.univ_nonempty
  have hmax' : ∀ b, largeTupleNormScale z.1.2 b ≤ largeTupleNormScale z.1.2 a :=
    fun b => hmax b (Finset.mem_univ b)
  have hrange := largePrimeTuplePiece_scale_product hXp d hqne
  change X/(2*2^(i+j)) ≤ (∏ b, largeTupleNormScale z.1.2 b) ∧
    (∏ b, largeTupleNormScale z.1.2 b) ≤ 3*X at hrange
  rw [hij] at hrange
  norm_num only [pow_succ,pow_zero,mul_one] at hrange
  have hBpos := largeTupleNormScale_pos z.1.2 a
  have hBX := hquarter _ _ hBpos.le (by simpa using hrange.1)
    (largeTuple_product_le_cube hij z a hmax')
  have hp : largeTupleGroupLength (Finset.univ\{a}) z*largeTupleNormScale z.1.2 a ≤ 3*X := by
    rw [largeTuple_singleton_product]
    exact hrange.2
  have hBupper : largeTupleNormScale z.1.2 a ≤ 3*X := by
    have hAone := largeTupleGroupLength_one (Finset.univ\{a}) z
    nlinarith
  have hBA : largeTupleNormScale z.1.2 a ≤ largeTupleGroupLength (Finset.univ\{a}) z := by
    have hh := hsquare 0 ξ Ct H d q hq hqne hqex a
    change (largeTupleNormScale z.1.2 a)^2 ≤ (∏ b, largeTupleNormScale z.1.2 b) at hh
    rw [← largeTuple_singleton_product z a,pow_two] at hh
    exact (mul_le_mul_iff_right₀ hBpos).mp (by simpa only [mul_comm] using hh)
  have hgap := nonflat_singleton_length_gap z a hLX G₀ hmax' (by
    intro h
    apply hnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,h⟩)
  have hden := nearFlat_log_denominator hX (z.property a) hBupper (hGle a) (hloglarge a)
  have hLB : 0 < 1+Real.log (largeTupleNormScale z.1.2 a) := by
    linarith [Real.log_nonneg (z.property a)]
  have hAhi := hgap.trans (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden)
  have hAlow : (largeTupleNormScale z.1.2 a)^(1-η a/16) ≤
      largeTupleGroupLength (Finset.univ\{a}) z := (Real.rpow_le_self_of_one_le (z.property a) (by linarith [hη a])).trans hBA
  have hk := hb a z H rfl hH
  simp only [largeTupleGroupLength,Finset.prod_singleton] at hk
  have hh := hk hBX hp ((hB₀ a).trans hBX)
    (fun b => hrough _ hBpos.le hBupper b) hAlow hAhi
  rw [hfull 0 Ct H d hhigh hne,largeTupleIndependentSum_regroup i j 0 ξ Ct H X z.1.2 {a},norm_mul]
  change ‖c‖*‖largeTupleRegroupedKernel i j 0 ξ Ct H X z.1.2 {a}‖ ≤ _
  apply (mul_le_mul_of_nonneg_left hh (_root_.norm_nonneg c)).trans
  have hconst : ‖c‖*K a ≤ (‖c‖+1)*K₀ := by
    nlinarith [mul_le_mul_of_nonneg_left (hKle a) (_root_.norm_nonneg c)]
  calc
    _ = (‖c‖*K a)*(X^(5/6:ℝ)/(1+Real.log X)^k) := by ring
    _ ≤ ((‖c‖+1)*K₀)*(X^(5/6:ℝ)/(1+Real.log X)^k) :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralLargeTupleExceptionalHigh
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining high exceptional boxes split exactly into the flat
subfamily and its complement. Both are negligible on the stated scale. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem largePrimeTupleExceptionalHighSum_isLittleO_actual (i j : ℕ) (hij : i+j = 3)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : δ ≤ 1/12)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X) =o[atTop] firstMomentScale := by
  obtain ⟨G,K,hK,hbound⟩ := largePrimeTuplePiece_nonflat_high_bound_actual i j hij hSW hpub
    hHuxley hperiod hMV hC hξ hξz hδ hGI hGQ  hGamma (3+(i+j)) Ct
  obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i j
  have hn : (fun X => largePrimeTupleExceptionalNonflatSum i j ξ δ Ct G (H X) X)
      =o[atTop] firstMomentScale := by
    apply Asymptotics.IsBigO.trans_isLittleO
      (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
    apply Asymptotics.IsBigO.of_bound (D*K)
    filter_upwards [hbound,hH,eventually_ge_atTop (1:ℝ)] with X hb hH hX
    have hXp : 0 < X := zero_lt_one.trans_le hX
    have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
    let B := K*X^(5/6:ℝ)/(1+Real.log X)^(3+(i+j))
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hp (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
        ‖if (X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
          largeTupleExceptionalSelector i j ξ δ Ct (H X) X d) ∧
          d ∉ largePrimeTupleFlatBoxSet i j 0 ξ Ct G (H X) X then
          largePrimeTuplePiece i j 0 ξ Ct (H X) X d else 0‖ ≤ B := by
      split_ifs with hd
      · by_cases hz : largePrimeTuplePiece i j 0 ξ Ct (H X) X d = 0
        · rw [hz,norm_zero]; exact hB
        obtain ⟨q,hq,hqne⟩ := largePrimeTuplePiece_witness d hz
        have hex : largePrimeTupleExceptional δ q := by
          by_contra hh
          exact hd.1.2 ⟨q,hq,hqne,hh⟩
        exact hb (H X) hH d hd.1.1 hd.2 ⟨q,hq,hqne,hex⟩
      · simpa only [norm_zero] using hB
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
    unfold largePrimeTupleExceptionalNonflatSum
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun d _ => hp d)).trans
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right (hcount X hX) hB).trans_eq
    dsimp [B]
    rw [pow_add]
    field_simp
    ring
  have hf := largePrimeTupleSelectedFlatHighSum_isLittleO i j hij hpnt hSW hpub hHuxley
    hperiod hMV hC hξ hξz hGI hGQ Ct G
    (fun X => largeTupleExceptionalSelector i j ξ δ Ct (H X) X) H hH
  have he : (fun X => largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X) =
      (fun X => largePrimeTupleSelectedFlatHighSum i j ξ Ct G (H X) X
        (largeTupleExceptionalSelector i j ξ δ Ct (H X) X) +
        largePrimeTupleExceptionalNonflatSum i j ξ δ Ct G (H X) X) := by
    funext X
    exact largePrimeTupleExceptionalHigh_split i j ξ δ Ct G (H X) X
  rw [he]
  exact hf.add hn

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralLargeTupleHighSum
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All high boxes of each actual large-row arity are negligible. The
separate sharp-cutoff boundary contribution is retained explicitly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem largePrimeTupleHighSum_isLittleO_actual_oai (i j : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδ1 : δ ≤ 1/12)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => largePrimeTupleHighSum i j ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  have ho := largePrimeTupleOrdinaryHighSum_isLittleO_actual i j hSW hpub hHuxley hperiod
    hMV hC hξ hξz hδ hGI hGQ  hGamma Ct H hH
  have he : (fun X => largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X)
      =o[atTop] firstMomentScale := by
    by_cases hij : i+j = 3
    · exact largePrimeTupleExceptionalHighSum_isLittleO_actual i j hij hpnt hSW hpub hHuxley
        hperiod hMV hC hξ hξz hδ1 hGI hGQ  hGamma Ct H hH
    · have hz : (fun X => largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X) =
          fun _ : ℝ => (0:ℂ) := by
        funext X
        exact largePrimeTupleExceptionalHighSum_zero i j hij ξ δ Ct (H X) X
      rw [hz]
      exact Asymptotics.isLittleO_zero _ _
  have hs : (fun X => largePrimeTupleHighSum i j ξ Ct (H X) X) =
      fun X => largePrimeTupleOrdinaryHighSum i j ξ δ Ct (H X) X +
        largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X := by
    funext X
    exact largePrimeTupleHighSum_split i j ξ δ Ct (H X) X
  rw [hs]
  exact ho.add he

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.largePrimeTupleHighSum_isLittleO_actual_oai := @OAI.CubicFirstMoment.largePrimeTupleHighSum_isLittleO_actual_oai
