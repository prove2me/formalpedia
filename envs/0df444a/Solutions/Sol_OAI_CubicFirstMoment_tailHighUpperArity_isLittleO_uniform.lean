-- Prove2me | solution 1 for OAI.CubicFirstMoment.tailHighUpperArity_isLittleO_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:02:23.442614+00:00
-- url     : https://prove2.me/submissions/c4b3c5cf-ff74-4fb8-83e0-49d0516f1078

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A020
import Definitions.Def_OAIQ096A023
import Theorems.Thm_OAI_CubicFirstMoment_tailPrime_upper_group_bound_uniform

section
-- module Solutions.OAIQ096_CM.CubicGram_PrimaryNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique primary associates and canonical prime factorization. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma primaryPrimeFactors_norm_prod {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    ∏ p ∈ primaryPrimeFactors n, normNat p = normNat n := by
  calc
    _ = normNat (∏ p ∈ primaryPrimeFactors n, p) := (map_prod normNatHom _ _).symm
    _ = normNat n := congrArg normNat (primaryPrimeFactors_prod hn hs)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma norm_primaryNormalize (p : Eisenstein) : norm (primaryNormalize p) = norm p := by
  simpa only [normNat_cast] using congrArg (fun m : ℕ => (m : ℝ))
    (associated_normNat (primaryNormalize_associated p)).symm

lemma roughProduct_primary_factors (ψ : ℝ → ℝ) (y : ℝ) (n : Eisenstein) :
    roughProduct ψ y n = ∏ p ∈ primaryPrimeFactors n, (1 - ψ (norm p / y)) := by
  rw [primaryPrimeFactors, Finset.prod_image (primaryNormalize_injOn_primeFactors n)]
  simp only [norm_primaryNormalize, roughProduct]

end CubicFirstMoment
end
end

end OAI
end

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma ordered_subset_product (s : Finset Eisenstein) (v : Eisenstein → ℂ) :
    ((s.card.factorial:ℂ)⁻¹)*
      (∑ e : Fin s.card ≃ s, ∏ i : Fin s.card, v (e i)) = ∏ p ∈ s, v p := by
  have he : Fin s.card ≃ s :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card s = s.card)).symm
  have hcard : Fintype.card (Fin s.card ≃ s) = s.card.factorial := by
    simpa using Fintype.card_equiv he
  have hprod (e : Fin s.card ≃ s) : (∏ i : Fin s.card, v (e i)) = ∏ p ∈ s, v p := by
    exact (e.prod_comp (fun p : s => v p)).trans (Finset.prod_coe_sort s v)
  simp_rw [hprod]
  rw [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul,←mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero s.card)),one_mul]

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

/-- Every chosen prime is large; the product bound therefore bounds the
number of chosen factors, uniformly in the original squarefree element. -/
lemma primary_factor_subset_card_lt {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n)
    {w : ℝ} (hw : 1 ≤ w) (hlarge : ∀ p ∈ s, w ≤ norm p)
    {k : ℕ} (hsize : norm n < w^k) : s.card < k := by
  have hprod : w^s.card ≤ norm n := by
    calc
      _ = ∏ _p ∈ s, w := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ s, norm p := Finset.prod_le_prod (fun _ _ => zero_le_one.trans hw) hlarge
      _ ≤ (∏ p ∈ s, norm p)*(∏ p ∈ primaryPrimeFactors n \ s, norm p) :=
        le_mul_of_one_le_right (Finset.prod_nonneg (fun p _ => norm_nonneg p))
          (Finset.one_le_prod (fun p hp => one_le_norm
            (primaryPrimeFactor_spec hn (Finset.mem_sdiff.mp hp).1).1.2.ne_zero))
      _ = ∏ p ∈ primaryPrimeFactors n, norm p := by
        rw [mul_comm,Finset.prod_sdiff hsub]
      _ = norm n := by
        simpa only [Nat.cast_prod,normNat_cast] using
          congrArg (fun m : ℕ => (m:ℝ)) (primaryPrimeFactors_norm_prod hn hs)
  by_contra h
  exact (not_lt_of_ge ((pow_le_pow_right₀ hw (not_lt.mp h)).trans hprod)) hsize

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BoundedPrimeTuples
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformly bounded tuple lengths in the manuscript's actual
prime detector. The bound depends on xi, not on the envelope scale. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eventually_prime_tuple_norm_bound {ξ C : ℝ} (hC : 0 < C)
    {k : ℕ} (hk : 1 < ξ*(k:ℝ)) :
    ∀ᶠ X : ℝ in atTop, C*X < (X^ξ)^k := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    eventually_const_mul_rpow_le hk (2*C)] with X hX h
  rw [Real.rpow_one] at h
  rw [←Real.rpow_natCast,←Real.rpow_mul (zero_lt_one.trans hX).le]
  nlinarith [mul_pos hC (zero_lt_one.trans hX)]

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

lemma primeDetectorCutoff_one {x : ℝ} (hx : x ≤ 1) : primeDetectorCutoff x = 1 := by
  rw [primeDetectorCutoff,Real.smoothTransition.zero_of_nonpos (by linarith),sub_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingProductSlice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primaryProductSlice_support (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (a : Eisenstein) :
    ∀ m ∈ primaryProductSlice S X a, primary m ∧ Squarefree m ∧ norm m ≤ X := by
  intro m hm
  obtain ⟨hmb,hprod⟩ := Finset.mem_filter.mp hm
  obtain ⟨hmp,hmX⟩ := mem_primaryElementBall.mp hmb
  exact ⟨hmp,(hS _ hprod).2.1.of_mul_right,hmX⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleFiber
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal independent prime-tuple fibre over a squarefree primary
product is exactly its set of orderings. This connects the subset detector
to the fixed-arity coefficients used in the analytic estimates. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma squarefreePrimeTuple_card {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (f : ι → Eisenstein) (hf : ∀ i, primaryPrime (f i)) (hprod : (∏ i, f i) = n) :
    Fintype.card ι = (primaryPrimeFactors n).card := by
  simpa using Fintype.card_congr (squarefreePrimeTupleEquiv hn hs f hf hprod)

theorem orderedConvolution_prime_fiber {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {B : ℝ} (hB : norm n ≤ B) (v : Eisenstein → ℂ) :
    orderedConvolution (fun _ : ι => primeCutoff B) (fun _ => v) n =
      ∑ e : ι ≃ primaryPrimeFactors n, ∏ i, v (e i) := by
  unfold orderedConvolution
  symm
  apply Finset.sum_bij (fun (e : ι ≃ primaryPrimeFactors n) _ i => (e i:Eisenstein))
  · intro e _
    have he : (∏ i, (e i:Eisenstein)) = n := by
      calc
        _ = ∏ p ∈ primaryPrimeFactors n, p :=
          (e.prod_comp (fun p : primaryPrimeFactors n => (p:Eisenstein))).trans
            (Finset.prod_coe_sort (primaryPrimeFactors n) (fun p : Eisenstein => p))
        _ = n := primaryPrimeFactors_prod hn hs
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => ?_),he⟩
    have hp := primaryPrimeFactor_spec hn (e i).property
    exact mem_primeCutoff.mpr ⟨hp.1,(norm_le_of_dvd (primary_ne_zero hn) hp.2).trans hB⟩
  · intro e _ d _ hed
    apply Equiv.ext
    intro i
    exact Subtype.ext (congrFun hed i)
  · intro f hfin
    obtain ⟨hfin,hprod⟩ := Finset.mem_filter.mp hfin
    have hp (i : ι) : primaryPrime (f i) :=
      (mem_primeCutoff.mp (Fintype.mem_piFinset.mp hfin i)).1
    exact ⟨squarefreePrimeTupleEquiv hn hs f hp hprod,Finset.mem_univ _,rfl⟩
  · intro e _
    rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothNormPartition
attribute [-instance] _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CentralProductSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughPrimeTuples
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded ordered prime-factor expansion of the rough remainder in
the large-R branch. Every tuple has its literal primary product. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma roughProduct_ordered_primary_factors (ψ : ℝ → ℝ) (w : ℝ) (n : Eisenstein) :
    (roughProduct ψ w n:ℂ) = ((primaryPrimeFactors n).card.factorial:ℂ)⁻¹*
      ∑ e : Fin (primaryPrimeFactors n).card ≃ primaryPrimeFactors n,
        ∏ i, (1-(ψ (norm (e i)/w):ℂ)) := by
  rw [ordered_subset_product (primaryPrimeFactors n)
    (fun p : Eisenstein => 1-(ψ (norm p/w):ℂ)),roughProduct_primary_factors]
  push_cast
  rfl

lemma roughProduct_nonzero_prime_bound {ψ : ℝ → ℝ}
    (hψ : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    {w : ℝ} (hw : 0 < w) {n : Eisenstein} (hn : primary n)
    (hne : roughProduct ψ w n ≠ 0) {p : Eisenstein} (hp : p ∈ primaryPrimeFactors n) :
    w < norm p := by
  rw [roughProduct_primary_factors] at hne
  have hpne := (Finset.prod_ne_zero_iff.mp hne) p hp
  by_contra h
  apply hpne
  rw [hψ _ (div_pos (zero_lt_one.trans_le
    (one_le_norm (primaryPrimeFactor_spec hn hp).1.2.ne_zero)) hw)
      ((div_le_one hw).mpr (not_lt.mp h)),sub_self]

/-- The rough remainder also has uniformly bounded prime-factor count;
this is needed before replacing it by independent prime dyads. -/
theorem bounded_rough_primary_factors {ξ C : ℝ} (hξ : 0 < ξ) (hC : 0 < C)
    {ψ : ℝ → ℝ} (hψ : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1) :
    ∃ k : ℕ, ∀ᶠ X : ℝ in atTop, ∀ n : Eisenstein,
      primary n → Squarefree n → norm n ≤ C*X → roughProduct ψ (X^ξ) n ≠ 0 →
        (primaryPrimeFactors n).card < k := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ξ)
  have hk' : 1 < ξ*(k:ℝ) := by
    have hh := (div_lt_iff₀ hξ).mp hk
    nlinarith
  refine ⟨k,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_prime_tuple_norm_bound hC hk']
    with X hX hbound
  intro n hn hs hnX hne
  apply primary_factor_subset_card_lt hn hs (subset_refl _)
    (Real.one_le_rpow hX.le hξ.le) _ (hnX.trans_lt hbound)
  intro p hp
  exact (roughProduct_nonzero_prime_bound hψ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _) hn hne hp).le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughRemainderArity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rough remainder is a finite sum of independent prime
convolutions. The factorial weight, literal product and roughness cutoff
are retained. This is the second arity expansion needed for the large rows. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma roughProduct_as_tuple {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {B : ℝ} (hB : norm n ≤ B) (ψ : ℝ → ℝ) (w : ℝ) :
    (roughProduct ψ w n:ℂ) =
      roughTupleCoefficient (primaryPrimeFactors n).card B ψ w n := by
  unfold roughTupleCoefficient
  rw [orderedConvolution_prime_fiber hn hs hB]
  exact roughProduct_ordered_primary_factors ψ w n

lemma roughTupleCoefficient_zero_of_card_ne {n : Eisenstein}
    (hn : primary n) (hs : Squarefree n) {B : ℝ} {k : ℕ}
    (hcard : k ≠ (primaryPrimeFactors n).card) (ψ : ℝ → ℝ) (w : ℝ) :
    roughTupleCoefficient k B ψ w n = 0 := by
  unfold roughTupleCoefficient orderedConvolution
  suffices hempty : (Fintype.piFinset (fun _ : Fin k => primeCutoff B)).filter
      (fun f => (∏ i, f i) = n) = ∅ by rw [hempty,Finset.sum_empty,mul_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨hf,hprod⟩ := Finset.mem_filter.mp hf
  apply hcard
  simpa only [Fintype.card_fin] using squarefreePrimeTuple_card hn hs f
    (fun i => (mem_primeCutoff.mp (Fintype.mem_piFinset.mp hf i)).1) hprod

lemma roughProduct_eq_sum_tuples {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {B : ℝ} (hB : norm n ≤ B) (ψ : ℝ → ℝ)
    (w : ℝ) {k : ℕ}
    (hsize : roughProduct ψ w n ≠ 0 → (primaryPrimeFactors n).card < k) :
    (roughProduct ψ w n:ℂ) =
      ∑ i ∈ Finset.range k, roughTupleCoefficient i B ψ w n := by
  let m := (primaryPrimeFactors n).card
  have hother (i : ℕ) (hi : i ≠ m) : roughTupleCoefficient i B ψ w n = 0 :=
    roughTupleCoefficient_zero_of_card_ne hn hs hi ψ w
  by_cases hm : m < k
  · rw [Finset.sum_eq_single m]
    · exact roughProduct_as_tuple hn hs hB ψ w
    · intro i _hi him
      exact hother i him
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hm)).elim
  · have hz : roughProduct ψ w n = 0 := by
      by_contra hne
      exact hm (hsize hne)
    rw [hz,Complex.ofReal_zero]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    exact hother i (fun he => hm (he ▸ Finset.mem_range.mp hi))

theorem eventually_rough_coefficient_tuples {ξ C : ℝ}
    (hξ : 0 < ξ) (hC : 0 < C) {ψ : ℝ → ℝ}
    (hψ : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1) :
    ∃ k : ℕ, ∀ᶠ X : ℝ in atTop, ∀ n : Eisenstein,
      primary n → Squarefree n → norm n ≤ C*X →
      (roughProduct ψ (X^ξ) n:ℂ) =
        ∑ i ∈ Finset.range k, roughTupleCoefficient i (C*X) ψ (X^ξ) n := by
  obtain ⟨k,hbound⟩ := bounded_rough_primary_factors hξ hC hψ
  refine ⟨k,?_⟩
  filter_upwards [hbound] with X hX
  intro n hn hs hnX
  exact roughProduct_eq_sum_tuples hn hs hnX ψ (X^ξ) (hX n hn hs hnX)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedDoubleArity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both sets of prime factors in the large distinguished rows are
of fixed, bounded arity. Original squarefreeness and product support are
kept inside the sum; no independent-tuple approximation is used. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem rough_slice_by_arity {ξ C : ℝ} (hξ : 0 < ξ) (hC : 0 < C)
    {ψ : ℝ → ℝ} (hψ : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1) :
    ∃ k : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (S : Finset Eisenstein)
      (r : Eisenstein) (K : Eisenstein → ℂ),
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ C*X) →
      (∑ u ∈ primaryProductSlice S (C*X) r, (roughProduct ψ (X^ξ) u:ℂ)*K (r*u)) =
        ∑ j ∈ Finset.range k, ∑ u ∈ primaryProductSlice S (C*X) r,
          roughTupleCoefficient j (C*X) ψ (X^ξ) u*K (r*u) := by
  obtain ⟨k,hbound⟩ := eventually_rough_coefficient_tuples hξ hC hψ
  refine ⟨k,?_⟩
  filter_upwards [hbound] with X hX
  intro S r K hS
  calc
    _ = ∑ u ∈ primaryProductSlice S (C*X) r,
        (∑ j ∈ Finset.range k, roughTupleCoefficient j (C*X) ψ (X^ξ) u)*K (r*u) := by
      apply Finset.sum_congr rfl
      intro u hu
      obtain ⟨hp,hs,hn⟩ := primaryProductSlice_support S (C*X) hS r u hu
      rw [hX u hp hs hn]
    _ = _ := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RestrictedPrimeTuples
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact tuple collection with an arbitrary original product restriction.
This allows the large distinguished rows to retain their sharp support
when both convolutions are expanded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma orderedConvolution_sum_restrict (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (R : Finset Eisenstein) (χ : Eisenstein → ℂ) :
    (∑ b ∈ R, orderedConvolution S w b*χ b) =
      ∑ f ∈ Fintype.piFinset S,
        if (∏ i, f i) ∈ R then (∏ i, w i (f i))*χ (∏ i, f i) else 0 := by
  have he : (∑ b ∈ R, orderedConvolution S w b*χ b) =
      ∑ b ∈ orderedConvolutionSupport S,
        orderedConvolution S w b*(if b ∈ R then χ b else 0) := by
    apply Finset.sum_congr_of_eq_on_inter
    · intro b _hb hout
      rw [orderedConvolution_eq_zero_of_not_mem S w hout,zero_mul]
    · intro b _hb hout
      simp only [hout,ite_false, if_false,mul_zero]
    · intro b hb _hbS
      rw [ite_eq_left hb]
  rw [he,orderedConvolution_sum]
  apply Finset.sum_congr rfl
  intro f _hf
  split_ifs <;> simp only [mul_zero]

lemma orderedConvolution_double_restrict (S : ι → Finset Eisenstein)
    (T : κ → Finset Eisenstein) (v : ι → Eisenstein → ℂ)
    (w : κ → Eisenstein → ℂ) (R : Finset Eisenstein)
    (U : Eisenstein → Finset Eisenstein) (K : Eisenstein → Eisenstein → ℂ) :
    (∑ r ∈ R, orderedConvolution S v r*
      ∑ u ∈ U r, orderedConvolution T w u*K r u) =
      ∑ f ∈ Fintype.piFinset S, ∑ g ∈ Fintype.piFinset T,
        if (∏ i, f i) ∈ R then
          if (∏ j, g j) ∈ U (∏ i, f i) then
            (∏ i, v i (f i))*(∏ j, w j (g j))*K (∏ i, f i) (∏ j, g j)
          else 0
        else 0 := by
  rw [orderedConvolution_sum_restrict]
  apply Finset.sum_congr rfl
  intro f _hf
  by_cases hr : (∏ i, f i) ∈ R
  · simp only [hr,ite_true, if_true]
    rw [orderedConvolution_sum_restrict,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _hg
    split_ifs <;> simp only [mul_zero,mul_assoc]
  · simp only [hr,ite_false, if_false,Finset.sum_const_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTuplePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeSmoothWeights
attribute [-instance] _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma distinguishedSmoothWeight_high (r : ℝ × ℝ) {x : ℝ} (hx : 2 < x) :
    distinguishedSmoothWeight r x = 0 := by
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight_high _ hx,sub_self]

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGrouping
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact partition alternative behind the large-distinguished-
factor branch of the manuscript's prime decomposition. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- A partition of one with each part below two thirds either has a
strictly interior subset sum or consists of exactly three equal thirds. -/
theorem prime_exponent_partition {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i ∧ a i < 2/3)
    (hsum : ∑ i ∈ s, a i = 1) :
    (∃ t ⊆ s, 1/3 < ∑ i ∈ t, a i ∧ ∑ i ∈ t, a i < 2/3) ∨
      (s.card = 3 ∧ ∀ i ∈ s, a i = 1/3) := by
  classical
  by_cases hex : ∃ t ⊆ s, 1/3 < ∑ i ∈ t, a i ∧ ∑ i ∈ t, a i < 2/3
  · exact Or.inl hex
  right
  have hno (t : Finset ι) (ht : t ⊆ s) (hlo : 1/3 < ∑ i ∈ t, a i) :
      2/3 ≤ ∑ i ∈ t, a i :=
    le_of_not_gt (fun hhi => hex ⟨t,ht,hlo,hhi⟩)
  have hthird (i : ι) (hi : i ∈ s) : a i ≤ 1/3 := by
    by_contra h
    have hh := hno {i} (Finset.singleton_subset_iff.mpr hi) (by simpa using not_le.mp h)
    have hh' : 2/3 ≤ a i := by simpa using hh
    exact (not_le_of_gt (ha i hi).2) hh'
  have hall (i : ι) (hi : i ∈ s) : a i = 1/3 := by
    by_contra heq
    have hai : a i < 1/3 := lt_of_le_of_ne (hthird i hi) heq
    let T := s.powerset.filter (fun t => i ∈ t ∧ 1/3 < ∑ j ∈ t, a j)
    have hT : T.Nonempty := by
      refine ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (subset_refl s),hi,?_⟩⟩
      rw [hsum]
      norm_num
    obtain ⟨t,ht,htmin⟩ := T.exists_min_image Finset.card hT
    have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    have hit : i ∈ t := (Finset.mem_filter.mp ht).2.1
    have htlarge : 1/3 < ∑ j ∈ t, a j := (Finset.mem_filter.mp ht).2.2
    obtain ⟨j,hjt,hji⟩ : ∃ j ∈ t, j ≠ i := by
      by_contra! h
      have he : t = {i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hit,h⟩
      rw [he,Finset.sum_singleton] at htlarge
      linarith
    have hjs : j ∈ s := hts hjt
    have herase : ∑ k ∈ t.erase j, a k ≤ 1/3 := by
      by_contra h
      have hmem : t.erase j ∈ T := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((Finset.erase_subset j t).trans hts),
          Finset.mem_erase.mpr ⟨hji.symm,hit⟩,not_le.mp h⟩
      have hle := htmin _ hmem
      have hlt := Finset.card_erase_lt_of_mem hjt
      omega
    have hsplit := Finset.sum_erase_add t a hjt
    have htupper : ∑ k ∈ t, a k ≤ 2/3 := by linarith [hthird j hjs]
    have hteq : ∑ k ∈ t, a k = 2/3 := le_antisymm htupper (hno t hts htlarge)
    have haj : a j = 1/3 := by linarith [hthird j hjs]
    have hpairs : ({i,j}:Finset ι) ⊆ s := by simp [Finset.insert_subset_iff,hi,hjs]
    have hpairsum : (∑ k ∈ ({i,j}:Finset ι), a k) = a i+a j := by
      simp [hji.symm]
    have hpair := hno {i,j} hpairs (by rw [hpairsum,haj]; linarith [(ha i hi).1])
    rw [hpairsum,haj] at hpair
    linarith
  refine ⟨?_,hall⟩
  have hconst : (∑ i ∈ s, a i) = ∑ _i ∈ s, (1/3:ℝ) :=
    Finset.sum_congr rfl hall
  have hcard : (s.card:ℝ)*(1/3) = 1 := by simpa only [Finset.sum_const,nsmul_eq_mul] using hconst.symm.trans hsum
  have hc : (s.card:ℝ) = 3 := by linarith
  exact_mod_cast hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma largePrimeTupleExponent_sum {i j : ℕ} {X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hn : Real.log (norm (largePrimeTupleProduct q)) ≠ 0) :
    (∑ a, largePrimeTupleExponent q a) = 1 := by
  unfold largePrimeTupleExponent
  rw [←Finset.sum_div,←Real.log_prod]
  · rw [largePrimeTupleNorm_prod,div_self hn]
  · intro a _ha
    exact ne_of_gt (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleGrouping
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform grouping for the actual large-row prime tuples, outside the
specified neighborhood of the exceptional three-prime configuration. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma largePrimeTuple_subset_norm_bounds {i j : ℕ} {X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hn : 0 < norm (largePrimeTupleProduct q))
    (hln : 0 < Real.log (norm (largePrimeTupleProduct q)))
    (s : Finset (Fin i ⊕ Fin j)) {l u : ℝ}
    (hl : l ≤ ∑ a ∈ s, largePrimeTupleExponent q a)
    (hu : (∑ a ∈ s, largePrimeTupleExponent q a) ≤ u) :
    norm (largePrimeTupleProduct q)^l ≤ ∏ a ∈ s, largePrimeTupleNorm q a ∧
      (∏ a ∈ s, largePrimeTupleNorm q a) ≤ norm (largePrimeTupleProduct q)^u := by
  have hp : 0 < ∏ a ∈ s, largePrimeTupleNorm q a :=
    Finset.prod_pos (fun a _ha => zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1)
  have he : Real.log (∏ a ∈ s, largePrimeTupleNorm q a) =
      (∑ a ∈ s, largePrimeTupleExponent q a)*Real.log (norm (largePrimeTupleProduct q)) := by
    rw [Real.log_prod (fun a _ha =>
      (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1).ne')]
    simp only [largePrimeTupleExponent]
    rw [←Finset.sum_div,div_mul_cancel₀ _ hln.ne']
  constructor
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hn l) hp).mp
    rw [Real.log_rpow hn,he]
    nlinarith [mul_le_mul_of_nonneg_right hl hln.le]
  · apply (Real.log_le_log_iff hp (Real.rpow_pos_of_pos hn u)).mp
    rw [Real.log_rpow hn,he]
    nlinarith [mul_le_mul_of_nonneg_right hu hln.le]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleSmoothIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleScaleGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma largeTupleSubsetScale_pos {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ)
    (s : Finset (Fin i ⊕ Fin j)) : 0 < largeTupleSubsetScale k s :=
  Finset.prod_pos (fun a _ => largeTupleNormScale_pos k a)

lemma largeTupleSubsetScale_complement {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ)
    (s : Finset (Fin i ⊕ Fin j)) :
    largeTupleSubsetScale k s*largeTupleSubsetScale k (Finset.univ\s) =
      largeTupleSubsetScale k Finset.univ := by
  exact Finset.prod_mul_prod_compl s (largeTupleNormScale k)

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

lemma largePrimeTuplePiece_group_scale {i j N : ℕ} {X : ℝ}
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hw : normTupleWeight k (largePrimeTupleNorm q) ≠ 0)
    (hn : 0 < norm (largePrimeTupleProduct q))
    (hln : 0 < Real.log (norm (largePrimeTupleProduct q)))
    (s : Finset (Fin i ⊕ Fin j)) {l u : ℝ}
    (hl : l ≤ ∑ a ∈ s, largePrimeTupleExponent q a)
    (hu : (∑ a ∈ s, largePrimeTupleExponent q a) ≤ u) :
    norm (largePrimeTupleProduct q)^l/2^s.card ≤ largeTupleSubsetScale (fun a => (k a).val) s ∧
      largeTupleSubsetScale (fun a => (k a).val) s ≤ norm (largePrimeTupleProduct q)^u := by
  obtain ⟨hpl,hpu⟩ := largePrimeTuple_subset_norm_bounds hq hn hln s hl hu
  obtain ⟨hsl,hsu⟩ := largePrimeTuplePiece_subset_range k hw s
  refine ⟨(div_le_iff₀ (by positivity : (0:ℝ) < 2^s.card)).mpr ?_,hsl.trans hpu⟩
  simpa only [mul_comm] using hpl.trans hsu

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleCutoffBoxes
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleRegrouping
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupingBounds
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short-side exponent bounds obtained by actual subset grouping.
The upper-height case permits one prime longer than two thirds. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma prime_exponent_closed_group {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i ∧ a i ≤ 2/3)
    (hsum : ∑ i ∈ s, a i = 1) :
    ∃ t ⊆ s, 1/3 ≤ ∑ i ∈ t, a i ∧ ∑ i ∈ t, a i ≤ 2/3 := by
  classical
  by_cases heq : ∃ i ∈ s, a i = 2/3
  · obtain ⟨i,hi,hai⟩ := heq
    refine ⟨{i},Finset.singleton_subset_iff.mpr hi,?_,?_⟩ <;> norm_num [hai]
  have hlt : ∀ i ∈ s, 0 < a i ∧ a i < 2/3 := by
    intro i hi
    exact ⟨(ha i hi).1,lt_of_le_of_ne (ha i hi).2 (fun h => heq ⟨i,hi,h⟩)⟩
  rcases prime_exponent_partition s a hlt hsum with ⟨t,ht,hlo,hhi⟩ | ⟨hcard,hthird⟩
  · exact ⟨t,ht,hlo.le,hhi.le⟩
  · obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    refine ⟨{i},Finset.singleton_subset_iff.mpr hi,?_,?_⟩ <;> norm_num [hthird i hi]

/-- For the upper-height branch, a prime may exceed two thirds. The
known complementary exponent lower bound still supplies a short side. -/
theorem prime_exponent_short_group {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) {σ : ℝ} (_hσ : 0 < σ) (hσ₁ : σ ≤ 1/3)
    (ha : ∀ i ∈ s, 0 < a i ∧ a i ≤ 1-σ)
    (hsum : ∑ i ∈ s, a i = 1) :
    ∃ t ⊆ s, σ ≤ ∑ i ∈ t, a i ∧ ∑ i ∈ t, a i ≤ 1/2 := by
  classical
  by_cases hbig : ∃ i ∈ s, 2/3 < a i
  · obtain ⟨i,hi,hai⟩ := hbig
    refine ⟨s.erase i,Finset.erase_subset _ _,?_,?_⟩
    all_goals have he := Finset.sum_erase_add s a hi
    · linarith [(ha i hi).2]
    · linarith
  · have hsmall : ∀ i ∈ s, 0 < a i ∧ a i ≤ 2/3 := by
      intro i hi
      exact ⟨(ha i hi).1,le_of_not_gt (fun h => hbig ⟨i,hi,h⟩)⟩
    obtain ⟨t,ht,hlo,hhi⟩ := prime_exponent_closed_group s a hsmall hsum
    by_cases hhalf : (∑ i ∈ t, a i) ≤ 1/2
    · exact ⟨t,ht,hσ₁.trans hlo,hhalf⟩
    · refine ⟨s\t,Finset.sdiff_subset,?_,?_⟩
      all_goals have he := Finset.sum_sdiff ht (f := a)
      · rw [hsum] at he
        linarith
      · rw [hsum] at he
        linarith [not_le.mp hhalf]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleKernelCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstArity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expand the rough remainder only after fixing the distinguished
smooth scales. All tuple and product supports remain exact. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma normTupleWeight_sum_elim {i j N : ℕ} (k : Fin i → Fin N) (l : Fin j → Fin N)
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) :
    normTupleWeight (Sum.elim k l) (largePrimeTupleNorm q) =
      normTupleWeight k (fun a => norm (q.1 a)) *
        normTupleWeight l (fun b => norm (q.2 b)) := by
  unfold normTupleWeight
  rw [Fintype.prod_sum_type]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstRowCollection
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the independently partitioned high-scale rows.
This connects the scale-first identity to the proved high-box estimates. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma sum_partition_sum_type {i j N : ℕ}
    (F : ((Fin i ⊕ Fin j) → Fin N) → ℂ) :
    (∑ k : Fin i → Fin N, ∑ l : Fin j → Fin N, F (Sum.elim k l)) =
      ∑ d : (Fin i ⊕ Fin j) → Fin N, F d := by
  rw [←Fintype.sum_prod_type']
  apply Finset.sum_equiv (Equiv.sumArrowEquivProdArrow (Fin i) (Fin j) (Fin N)).symm
  · intro _
    simp only [Finset.mem_univ]
  · intro _ _
    rfl

lemma distinguishedScaleLength_sum_type {i j N : ℕ}
    (k : Fin i → Fin N) (l : Fin j → Fin N) :
    largeTupleDistinguishedScale (fun a => (Sum.elim k l a).val) =
      distinguishedScaleLength k := by
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstTailHeightPrefix
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An initial segment of the geometric height windows is exactly the
difference of two aligned full tails. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma heightWindowCount_shift {H T : ℝ} (hH : 0 < H) (hT : 0 < T) (j : ℕ) :
    heightWindowCount H (T*(3/2:ℝ)^j) = heightWindowCount H T-j := by
  have hr : 0 < Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  have hB : 0 < 2*Real.pi*H := by positivity
  have hp : 0 < (3/2:ℝ)^j := by positivity
  have he : Real.log ((2*Real.pi*H)/(T*(3/2:ℝ)^j))/Real.log (3/2:ℝ) =
      Real.log ((2*Real.pi*H)/T)/Real.log (3/2:ℝ)-(j:ℝ) := by
    rw [Real.log_div hB.ne' (mul_pos hT hp).ne', Real.log_mul hT.ne' hp.ne',
      Real.log_pow,Real.log_div hB.ne' hT.ne']
    field_simp
    ring
  unfold heightWindowCount
  rw [he,Nat.ceil_sub_natCast]

lemma geometricHeight_prefix (f : ℝ → ℂ) {H T : ℝ} (hH : 0 < H) (hT : 0 < T)
    {j : ℕ} (hj : j ≤ heightWindowCount H T) :
    (∑ s ∈ Finset.range j, f (T*(3/2:ℝ)^s)) =
      (∑ s ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^s))-
        ∑ s ∈ Finset.range (heightWindowCount H (T*(3/2:ℝ)^j)),
          f ((T*(3/2:ℝ)^j)*(3/2:ℝ)^s) := by
  rw [heightWindowCount_shift hH hT j]
  apply (eq_sub_iff_add_eq).mpr
  calc
    _ = (∑ s ∈ Finset.range j, f (T*(3/2:ℝ)^s))+
        ∑ s ∈ Finset.range (heightWindowCount H T-j), f (T*(3/2:ℝ)^(j+s)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      rw [pow_add]
      ring
    _ = _ := by
      simpa only [Nat.add_sub_of_le hj] using
        (Finset.sum_range_add (fun s => f (T*(3/2:ℝ)^s)) j
          (heightWindowCount H T-j)).symm

lemma initial_filter_range {p : ℕ → Prop} [DecidablePred p]
    (hp : ∀ {i j}, i ≤ j → p j → p i) (N : ℕ) :
    ∃ j ≤ N, (Finset.range N).filter p = Finset.range j := by
  induction N with
  | zero => exact ⟨0,le_rfl,by simp⟩
  | succ N ih =>
    by_cases hN : p N
    · refine ⟨N+1,le_rfl,Finset.filter_eq_self.mpr ?_⟩
      intro i hi
      exact hp (by have := Finset.mem_range.mp hi; omega) hN
    · obtain ⟨j,hj,he⟩ := ih
      refine ⟨j,hj.trans (Nat.le_succ N),?_⟩
      rw [Finset.range_add_one,Finset.filter_insert]
      simp only [hN,ite_false, if_false,he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Type I for the actual Gauss product envelope at a height window.
The inner smooth weight is the bounded dilation forced by the outer norm. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma productGaussHeightWindowKernel_envelope (ℓ : ℤ) (W : ℝ → ℂ) {B X : ℝ}
    (hX : 0 < X) (hW : ∀ x : ℝ, B < x → W x = 0)
    (H T X₀ : ℝ) {n : Eisenstein} (hn : primary n) :
    (if n ∈ squarefreeProductEnvelope (B*X) then productGaussHeightWindowKernel ℓ W H T X X₀ n else 0) =
      productGaussHeightWindowKernel ℓ W H T X X₀ n := by
  by_cases hs : Squarefree n
  · by_cases hsize : norm n ≤ B*X
    · have hm : n ∈ squarefreeProductEnvelope (B*X) :=
        Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hn,hsize⟩,hs⟩
      rw [ite_eq_left hm]
    · have hx : B < norm n/X := (lt_div_iff₀ hX).mpr (lt_of_not_ge hsize)
      simp only [productGaussHeightWindowKernel,hW _ hx,mul_zero,zero_mul,ite_self]
  · simp only [productGaussHeightWindowKernel,gauss_eq_zero_of_not_squarefree hn hs,
      mul_zero,zero_mul,ite_self]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UpperTailTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual prime-tuple Gauss kernel for upper height windows.
The high branch begins at X^(1/3-2κ), in the prime decomposition. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma tailPrimeTupleTerm_factors_ne_zero {i j : ℕ} {ℓ : ℤ} {ξ H U X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q ≠ 0) :
    (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a)) ≠ 0 ∧
    (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ))) ≠ 0 ∧
      productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (largePrimeTupleProduct q) ≠ 0 := by
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2,(mul_ne_zero_iff.mp hne).2⟩

lemma tailPrimeTupleTerm_product_range {i j : ℕ} {ℓ : ℤ} {ξ H U X : ℝ}
    (hX : 0 < X) {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q ≠ 0) :
    X/2 ≤ norm (largePrimeTupleProduct q) ∧ norm (largePrimeTupleProduct q) ≤ 3*X := by
  have hk := (tailPrimeTupleTerm_factors_ne_zero hne).2.2
  have hw : primeProductEnvelope (norm (largePrimeTupleProduct q)/X) ≠ 0 := by
    intro hz
    apply hk
    simp only [productGaussHeightWindowKernel,hz,mul_zero,zero_mul]
  constructor
  · by_contra hn
    exact hw (primeProductEnvelope_zero_lower ((div_le_iff₀ hX).mpr (by linarith)))
  · by_contra hn
    exact hw (primeProductEnvelope_zero ((le_div_iff₀ hX).mpr (by linarith)))

lemma tailPrimeTupleNorm_rough {i j : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {H U X : ℝ} (hX : 1 ≤ X) (hξz : ξ ≤ 2/5)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q ≠ 0) (a : Fin i ⊕ Fin j) :
    X^ξ < largePrimeTupleNorm q a := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hw := Real.rpow_pos_of_pos hXp ξ
  obtain ⟨hf,hg,_⟩ := tailPrimeTupleTerm_factors_ne_zero hne
  rcases a with a | b
  · have hn := Finset.prod_ne_zero_iff.mp hf a (Finset.mem_univ a)
    exact (distinguishedPrimeWeight_support (fun _ _ hh => primeDetectorCutoff_one hh)
      (fun _ hh => primeDetectorCutoff_zero hh) hw
      (Real.rpow_le_rpow_of_exponent_le hX hξz)
      (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq (.inl a)).1) hn).1
  · have hn := Finset.prod_ne_zero_iff.mp hg b (Finset.mem_univ b)
    change X^ξ < norm (q.2 b)
    by_contra hh
    apply hn
    rw [primeDetectorCutoff_one ((div_le_one hw).mpr (not_lt.mp hh))]
    simp

lemma tailPrimeTupleNorm_upper {i j N : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {H U X κ : ℝ} (hX : 1 ≤ X) (hκ : 0 ≤ κ) (hξz : ξ ≤ 2/5)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(1/3-2*κ:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0)
    (a : Fin i ⊕ Fin j) : largePrimeTupleNorm q a ≤ 3*X^(2/3+2*κ:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨ht,hw⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨hf,_,_⟩ := tailPrimeTupleTerm_factors_ne_zero ht
  rcases a with a | b
  · have hn := Finset.prod_ne_zero_iff.mp hf a (Finset.mem_univ a)
    have hh := (distinguishedPrimeWeight_support (fun _ _ hh => primeDetectorCutoff_one hh)
      (fun _ hh => primeDetectorCutoff_zero hh) (Real.rpow_pos_of_pos hXp ξ)
      (Real.rpow_le_rpow_of_exponent_le hX hξz)
      (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq (.inl a)).1) hn).2
    change norm (q.1 a) ≤ _
    have hp := Real.rpow_le_rpow_of_exponent_le hX
      (show (2/5:ℝ) ≤ 2/3+2*κ by linarith)
    nlinarith [Real.rpow_pos_of_pos hXp (2/3+2*κ:ℝ)]
  · have hprim : primary (∏ b, q.2 b) := primary_finset_prod _ _
      (fun b _ => (mem_primeCutoff.mp
        (Fintype.mem_piFinset.mp (Finset.mem_product.mp hq).2 b)).1.1)
    have hnb := norm_le_of_dvd (primary_ne_zero hprim)
      (Finset.dvd_prod_of_mem q.2 (Finset.mem_univ b))
    have hnr := hhigh.trans (largePrimeTuplePiece_distinguished_range k hw).1
    have hprod := (tailPrimeTupleTerm_product_range hXp ht).2
    rw [largePrimeTupleProduct,norm_mul_eq] at hprod
    have hm : X^(1/3-2*κ:ℝ)*norm (q.2 b) ≤ 3*X :=
      (mul_le_mul_of_nonneg_right hnr (norm_nonneg _)).trans
        ((mul_le_mul_of_nonneg_left hnb (norm_nonneg _)).trans hprod)
    have he : X^(1/3-2*κ:ℝ)*(3*X^(2/3+2*κ:ℝ)) = 3*X := by
      rw [mul_left_comm,←Real.rpow_add hXp]
      rw [show (1/3-2*κ:ℝ)+(2/3+2*κ)=1 by ring,Real.rpow_one]
    change norm (q.2 b) ≤ _
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp (1/3-2*κ:ℝ))).mp
    simpa only [mul_comm] using hm.trans_eq he.symm


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeRegroup
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prime-tuple regrouping for the Gauss height tail. The original
product envelope and finite weights survive both support changes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem tailPrimeTuplePiece_full (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (H U X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hb : ∀ a, 2*largeTupleNormScale (fun a => (k a).val) a ≤ Real.exp primeProductWeights.radius*X) :
    tailPrimeTuplePiece i j ℓ ξ H U X k =
      ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
        tailPrimeTupleIndependentSum i j ℓ ξ H U X (fun a => (k a).val) := by
  unfold tailPrimeTuplePiece tailPrimeTupleIndependentSum
  congr 1
  have he := independent_tuple_sum_sum_type
    (fun _ : Fin i ⊕ Fin j => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fun q => (∏ a, largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
      (norm (largeTupleVector q a)/largeTupleNormScale (fun a => (k a).val) a))*
      productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (∏ a, largeTupleVector q a))
  simp_rw [largeTupleVector_split] at he
  rw [independent_tuple_sum_support
    (fun _ : Fin i ⊕ Fin j => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X (fun a => (k a).val))
      (largeTupleNormScale (fun a => (k a).val)))
    (fun a p => largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
      (norm p/largeTupleNormScale (fun a => (k a).val) a))
    (fun f => productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (∏ a, f a))
    (largeTuple_coordinate_support ξ X (fun a => (k a).val) hb)] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro q _hq
  simp only [largeTupleVector_norm,largeTupleVector_prod,largeTupleCoordinateWeight_product]
  unfold tailPrimeTupleTerm
  ring


theorem tailPrimeTupleIndependent_regroup (i j : ℕ) (ℓ : ℤ) (ξ H U X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :
    tailPrimeTupleIndependentSum i j ℓ ξ H U X k =
      tailPrimeTupleRegrouped i j ℓ ξ H U X k s := by
  have he := independent_prime_tuple_kernel s
    (fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X k) (largeTupleNormScale k))
    (fun a p => largeTupleCoordinateWeight ξ X k a (norm p/largeTupleNormScale k a))
    (fun a p hp => (fullPrimeSupport_prime 2 (largeTupleCoordinateWeight ξ X k)
      (largeTupleNormScale k) a p hp).1)
    (productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X) (by
      intro n hn hns
      have hz : gauss n = 0 := norm_eq_zero.mp (by rw [norm_gauss hn,ite_eq_right hns])
      simp only [productGaussHeightWindowKernel,hz,mul_zero,zero_mul])
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
  simpa only [tailPrimeTupleIndependentSum,tailPrimeTupleRegrouped,
    largeTupleSelectedSupport,largeTupleOtherSupport,largeTupleSelectedCoefficient,
    largeTupleOtherCoefficient,fullSquarefreePrimeSupport,fullPrimeCoefficient,
    isCoprime_one_right,and_true] using he

theorem tailPrimeTupleRegrouped_tail (i j : ℕ) (ξ H T X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :
    (∑ v ∈ Finset.range (heightWindowCount H T),
      tailPrimeTupleRegrouped i j 0 ξ H (T*(3/2:ℝ)^v) X k s) =
      envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ X k s)
        (largeTupleOtherSupport ξ X k s) (largeTupleSelectedCoefficient ξ X k s)
        (largeTupleOtherCoefficient ξ X k s) primeProductEnvelope H T X := by
  unfold tailPrimeTupleRegrouped envelopeCutoffBilinearTail
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  simp only [productGaussHeightWindowKernel,theta_zero,one_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeExpansion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact bounded-arity expansion of the remaining Gauss height rows.
The original total-product envelope is retained before independent regrouping. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma tailPrimeTupleTerm_envelope {i j : ℕ} (ℓ : ℤ) (ξ H U : ℝ)
    {X : ℝ} (hX : 0 < X)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X) :
    (if (∏ a, q.1 a) ∈ centralPrimaryFactors X then
      if (∏ b, q.2 b) ∈ primaryProductSlice (centralProductEnvelope X)
          (Real.exp primeProductWeights.radius*X) (∏ a, q.1 a) then
        tailPrimeTupleTerm i j ℓ ξ H U X q else 0 else 0) =
      tailPrimeTupleTerm i j ℓ ξ H U X q := by
  obtain ⟨hf,hg⟩ := Finset.mem_product.mp hq
  have hr : primary (∏ a, q.1 a) := primary_finset_prod _ _
    (fun a _ => (mem_primeCutoff.mp (Fintype.mem_piFinset.mp hf a)).1.1)
  have hu : primary (∏ b, q.2 b) := primary_finset_prod _ _
    (fun b _ => (mem_primeCutoff.mp (Fintype.mem_piFinset.mp hg b)).1.1)
  have hn := primary_mul hr hu
  by_cases hp : largePrimeTupleProduct q ∈ centralProductEnvelope X
  · have hrB : (∏ a, q.1 a) ∈ centralPrimaryFactors X := by
      apply mem_primaryElementBall.mpr
      exact ⟨hr,(norm_le_of_dvd (primary_ne_zero hn) (dvd_mul_right _ _)).trans
        (centralProductEnvelope_spec hp).2.2⟩
    have huS : (∏ b, q.2 b) ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) (∏ a, q.1 a) :=
      (mem_primaryProductSlice_iff _ _ (fun _ hn => centralProductEnvelope_spec hn) _ hu).mpr hp
    rw [ite_eq_left hrB,ite_eq_left huS]
  · have he := productGaussHeightWindowKernel_envelope ℓ primeProductEnvelope hX
      (fun x hx => primeProductWeights.upper_support () x hx) H U X hn
    change (if largePrimeTupleProduct q ∈ centralProductEnvelope X then
      productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X
        (largePrimeTupleProduct q) else 0) = _ at he
    rw [ite_eq_right hp] at he
    have hz : tailPrimeTupleTerm i j ℓ ξ H U X q = 0 := by
      simp only [tailPrimeTupleTerm,largePrimeTupleProduct,he.symm,mul_zero]
    simp only [hz,ite_self]

theorem tailScaleRow_remainder_arity {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (ℓ : ℤ) (H U : ℝ)
      (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      scaleFirstTailScaleRow i ℓ ξ H U X k =
        ∑ j ∈ Finset.range m, tailScaleDoubleRow i j ℓ ξ H U X k := by
  obtain ⟨m,hm⟩ := rough_slice_by_arity hξ (Real.exp_pos primeProductWeights.radius)
    (fun _ _ hx => primeDetectorCutoff_one hx)
  refine ⟨m,?_⟩
  filter_upwards [hm] with X hm
  intro i ℓ H U k
  unfold scaleFirstTailScaleRow tailScaleDoubleRow
  change (∑ r ∈ centralPrimaryFactors X, distinguishedScaleCoefficient i ξ X k r *
    ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) r,
      (roughProduct primeDetectorCutoff (X^ξ) u:ℂ)*
        productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (r*u)) = _
  simp_rw [hm (centralProductEnvelope X) _ _ (fun _ hn => centralProductEnvelope_spec hn),
    Finset.mul_sum]
  rw [Finset.sum_comm]

lemma tailScaleDoubleRow_eq_tuples (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (H U : ℝ) {X : ℝ} (hX : 0 < X)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    tailScaleDoubleRow i j ℓ ξ H U X k =
      ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹) *
        ∑ q ∈ largePrimeTupleBox i j X,
          tailPrimeTupleTerm i j ℓ ξ H U X q * normTupleWeight k (fun a => norm (q.1 a)) := by
  let S := fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X)
  let T := fun _ : Fin j => primeCutoff (Real.exp primeProductWeights.radius*X)
  let v := fun a p => normPartitionWeight (2*norm p/(4/3:ℝ)^(k a).val) *
    distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) p
  let w := fun _ : Fin j => fun p => 1-(primeDetectorCutoff (norm p/(X^ξ)):ℂ)
  let Q := primaryProductSlice (centralProductEnvelope X) (Real.exp primeProductWeights.radius*X)
  let K := fun r u => productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (r*u)
  let c := (i.factorial:ℂ)⁻¹
  let d := (j.factorial:ℂ)⁻¹
  have he : tailScaleDoubleRow i j ℓ ξ H U X k =
      (c*d)*∑ r ∈ centralPrimaryFactors X, orderedConvolution S v r *
        ∑ u ∈ Q r, orderedConvolution T w u*K r u := by
    unfold tailScaleDoubleRow distinguishedScaleCoefficient
      distinguishedTupleCoefficient roughTupleCoefficient
    simp only [Fintype.card_fin]
    change (∑ r ∈ centralPrimaryFactors X, (c*orderedConvolution S v r)*
      ∑ u ∈ Q r, (d*orderedConvolution T w u)*K r u) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    have hu : (∑ u ∈ Q r, (d*orderedConvolution T w u)*K r u) =
        d*∑ u ∈ Q r, orderedConvolution T w u*K r u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    rw [hu]
    ring
  rw [he,orderedConvolution_double_restrict]
  congr 1
  rw [show largePrimeTupleBox i j X = (Fintype.piFinset S).product (Fintype.piFinset T) from rfl,
    Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro g hg
  have hq : (f,g) ∈ largePrimeTupleBox i j X := Finset.mem_product.mpr ⟨hf,hg⟩
  have henv := tailPrimeTupleTerm_envelope ℓ ξ H U hX hq
  have hwprod : (∏ a, v a (f a))*(∏ b, w b (g b))*K (∏ a, f a) (∏ b, g b) =
      tailPrimeTupleTerm i j ℓ ξ H U X (f,g)*normTupleWeight k (fun a => norm (f a)) := by
    simp only [v,w,K,tailPrimeTupleTerm,largePrimeTupleProduct,normTupleWeight,
      Finset.prod_mul_distrib]
    ring
  by_cases hr : (∏ a, f a) ∈ centralPrimaryFactors X
  · by_cases hu : (∏ b, g b) ∈ Q (∏ a, f a)
    · simp only [hr,hu,ite_true, if_true]
      exact hwprod
    · dsimp only [Q] at hu
      have hz : tailPrimeTupleTerm i j ℓ ξ H U X (f,g) = 0 := by
        simpa only [hr,hu,ite_true, if_true,ite_false, if_false] using henv.symm
      simp only [Q,hr,hu,ite_true, if_true,ite_false, if_false,hz,zero_mul]
  · have hz : tailPrimeTupleTerm i j ℓ ξ H U X (f,g) = 0 := by
      simpa only [hr,ite_false, if_false] using henv.symm
    simp only [hr,ite_false, if_false,hz,zero_mul]

lemma tailScaleDoubleRow_partition (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (H U : ℝ) {X : ℝ} (hX : 1 ≤ Real.exp primeProductWeights.radius*X)
    (hXp : 0 < X)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    tailScaleDoubleRow i j ℓ ξ H U X k =
      ∑ l : Fin j → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        tailPrimeTuplePiece i j ℓ ξ H U X (Sum.elim k l) := by
  rw [tailScaleDoubleRow_eq_tuples i j ℓ ξ H U hXp]
  rw [finite_sum_normTupleWeight (largePrimeTupleBox i j X)
    (fun q => tailPrimeTupleTerm i j ℓ ξ H U X q * normTupleWeight k (fun a => norm (q.1 a)))
    (fun q b => norm (q.2 b))
    (fun q hq b => (largePrimeTupleNorm_bounds hq (.inr b)).1)
    (fun q hq b => (largePrimeTupleNorm_bounds hq (.inr b)).2)
    (normPartitionCount_covers hX),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  unfold tailPrimeTuplePiece
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [normTupleWeight_sum_elim]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UpperTailGrouping
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual upper-height prime boxes have a shorter group of size at least
X^(1/3-3κ). The grouping uses one surviving tuple and fixed box scales. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma tailPrimeTuple_upper_exponents {i j N : ℕ} {ℓ : ℤ} {ξ H U X κ : ℝ}
    (hX : 1 ≤ X) (hκ : 0 < κ) (hκsmall : κ < 1/12)
    (hlog : 100/κ ≤ Real.log X) (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0) :
    ∀ a, 0 < largePrimeTupleExponent q a ∧ largePrimeTupleExponent q a ≤ 2/3+5*κ/2 := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 < Real.log X := (div_pos (by norm_num) hκ).trans_le hlog
  have hκL : 100 ≤ κ*Real.log X := by
    have hh := (div_le_iff₀ hκ).mp hlog
    nlinarith
  have hL100 : 100 ≤ Real.log X := by nlinarith
  have ht := (mul_ne_zero_iff.mp hne).1
  have hnrange := tailPrimeTupleTerm_product_range hXp ht
  have hnp : 0 < norm (largePrimeTupleProduct q) := (by positivity : (0:ℝ) < X/2).trans_le hnrange.1
  have hlog2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)).trans (by norm_num)
  have hlog3 : Real.log 3 ≤ 3 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)).trans (by norm_num)
  have hln := Real.log_le_log (by positivity : (0:ℝ) < X/2) hnrange.1
  rw [Real.log_div hXp.ne' (by norm_num)] at hln
  have hlnpos : 0 < Real.log (norm (largePrimeTupleProduct q)) := by linarith
  intro a
  have hlo := Real.log_le_log (Real.rpow_pos_of_pos hXp ξ)
    (tailPrimeTupleNorm_rough hX hξz hq ht a).le
  rw [Real.log_rpow hXp] at hlo
  have hhi := Real.log_le_log (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1)
    (tailPrimeTupleNorm_upper hX hκ.le hξz k hhigh hq hne a)
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hXp (2/3+2*κ)).ne',Real.log_rpow hXp] at hhi
  unfold largePrimeTupleExponent
  refine ⟨div_pos (lt_of_lt_of_le (mul_pos hξ hL) hlo) hlnpos,?_⟩
  apply (div_le_iff₀ hlnpos).mpr
  have hfac : 0 ≤ 2/3+5*κ/2 := by positivity
  have hh := mul_le_mul_of_nonneg_left (show Real.log X-2 ≤
    Real.log (norm (largePrimeTupleProduct q)) by linarith) hfac
  nlinarith

theorem eventually_tailPrimeTuple_upper_grouping (i j : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκsmall : κ < 1/12) {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (H U : ℝ) {N : ℕ}
      (k : (Fin i ⊕ Fin j) → Fin N),
      X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (k a).val) →
      ∀ q ∈ largePrimeTupleBox i j X,
        tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
        ∃ s : Finset (Fin i ⊕ Fin j),
          X^(1/3-3*κ) ≤ largeTupleSubsetScale (fun a => (k a).val) s ∧
          (largeTupleSubsetScale (fun a => (k a).val) s)^2 ≤ 3*X := by
  let σ : ℝ := 1/3-5*κ/2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσ1 : σ ≤ 1/3 := by dsimp [σ]; linarith
  have hgap : 1/3-3*κ < σ := by dsimp [σ]; linarith
  have hconst : 0 < (1/2:ℝ)^σ/2^(i+j) := by positivity
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (100/κ),
    eventually_rpow_le_const_mul hgap hconst]
    with X hX hlog hscale
  intro ℓ H U N k hhigh q hq hne
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have ht := (mul_ne_zero_iff.mp hne).1
  have hw := (mul_ne_zero_iff.mp hne).2
  have hnrange := tailPrimeTupleTerm_product_range hXp ht
  have hnp : 0 < norm (largePrimeTupleProduct q) := (by positivity : (0:ℝ) < X/2).trans_le hnrange.1
  have hln : 0 < Real.log (norm (largePrimeTupleProduct q)) := by
    have hκL : 100 ≤ κ*Real.log X := by
      have hh := (div_le_iff₀ hκ).mp hlog
      nlinarith
    have hL100 : 100 ≤ Real.log X := by nlinarith
    have hh := Real.log_le_log (by positivity : (0:ℝ) < X/2) hnrange.1
    rw [Real.log_div hXp.ne' (by norm_num)] at hh
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have ha := tailPrimeTuple_upper_exponents hX hκ hκsmall hlog hξ hξz k hhigh hq hne
  obtain ⟨s,_hs,hlo,hhi⟩ := prime_exponent_short_group Finset.univ
    (largePrimeTupleExponent q) hσ hσ1 (fun a _ => ⟨(ha a).1,by dsimp [σ]; linarith [(ha a).2]⟩)
    (largePrimeTupleExponent_sum hq hln.ne')
  obtain ⟨hgs,hgu⟩ := largePrimeTuplePiece_group_scale k hq hw hnp hln s hlo hhi
  refine ⟨s,?_,?_⟩
  · have hcard : s.card ≤ i+j := by
      simpa only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] using s.card_le_univ
    have hpow : (2:ℝ)^s.card ≤ 2^(i+j) := pow_le_pow_right₀ (by norm_num) hcard
    calc
      X^(1/3-3*κ) ≤ ((1/2:ℝ)^σ/2^(i+j))*X^σ := hscale
      _ = (X/2)^σ/2^(i+j) := by
        rw [div_eq_mul_inv X 2,Real.mul_rpow hXp.le (by positivity)]
        simp only [one_div]
        ring
      _ ≤ norm (largePrimeTupleProduct q)^σ/2^(i+j) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hnrange.1 hσ.le) (by positivity)
      _ ≤ norm (largePrimeTupleProduct q)^σ/2^s.card :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hnp.le _) (by positivity) hpow
      _ ≤ _ := hgs
  · have hp := pow_le_pow_left₀ (largeTupleSubsetScale_pos _ s).le hgu 2
    have he : (norm (largePrimeTupleProduct q)^(1/2:ℝ))^2 = norm (largePrimeTupleProduct q) := by
      rw [←Real.rpow_mul_natCast hnp.le]
      norm_num
    exact hp.trans (by rw [he]; exact hnrange.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All coordinate assumptions for the independent Gauss-tail prime box
follow from one surviving original tuple. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

theorem tailPrimeTuplePiece_rough_scales (i j : ℕ) {ξ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (H U : ℝ) {N : ℕ}
      (k : (Fin i ⊕ Fin j) → Fin N),
      ∀ q ∈ largePrimeTupleBox i j X,
        tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
        (∀ a, 1 ≤ largeTupleNormScale (fun a => (k a).val) a) ∧
        ∀ B : ℝ, 0 ≤ B → B ≤ 3*X → ∀ a,
          (2*B)^(ξ/2) < largeTupleNormScale (fun a => (k a).val) a := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hξ).eventually_ge_atTop 2,
    eventually_const_mul_rpow_le (by linarith : ξ/2 < ξ) (2*6^(ξ/2))]
    with X hX hXtwo hgap
  intro ℓ H U N k q hq hne
  obtain ⟨ht,hw⟩ := mul_ne_zero_iff.mp hne
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hscale (a : Fin i ⊕ Fin j) :
      X^ξ/2 < largeTupleNormScale (fun a => (k a).val) a := by
    have hrough := tailPrimeTupleNorm_rough hX hξz hq ht a
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


lemma tailPrimeTuplePiece_witness {i j : ℕ} {ℓ : ℤ} {ξ H U X : ℝ}
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hne : tailPrimeTuplePiece i j ℓ ξ H U X k ≠ 0) :
    ∃ q ∈ largePrimeTupleBox i j X,
      tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  unfold tailPrimeTuplePiece
  rw [Finset.sum_eq_zero h,mul_zero]

theorem eventually_tailPrimeTuple_coordinate_envelope {i j : ℕ} {κ ξ : ℝ}
    (hκ : 0 ≤ κ) (hκsmall : κ < 1/12) (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (H U : ℝ) {N : ℕ}
      (k : (Fin i ⊕ Fin j) → Fin N),
      X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (k a).val) →
      ∀ q ∈ largePrimeTupleBox i j X,
        tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
        ∀ a, 2*largeTupleNormScale (fun a => (k a).val) a ≤ Real.exp primeProductWeights.radius*X := by
  have hC : 0 < Real.exp primeProductWeights.radius/6 := by positivity
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_rpow_le_const_mul (show (2/3+2*κ:ℝ) < 1 by linarith) hC]
    with X hX hgap
  intro ℓ H U N k hhigh q hq hne a
  have hw := (mul_ne_zero_iff.mp hne).2
  have hlo := (largePrimeTuplePiece_coordinate_range k hw a).1
  have hhi := tailPrimeTupleNorm_upper hX hκ hξz k hhigh hq hne a
  rw [Real.rpow_one] at hgap
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailHighCollection
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of Gauss height-tail rows above any fixed scale threshold.
This retains the independent smooth norm partitions and product envelope. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem tailHighScaleRows_arity {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (ℓ : ℤ) (H U V : ℝ),
      tailHighScaleRows i ℓ ξ H U X V =
        ∑ j ∈ Finset.range m,
          ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
            if V ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
              tailPrimeTuplePiece i j ℓ ξ H U X d else 0 := by
  obtain ⟨m,hm⟩ := tailScaleRow_remainder_arity hξ
  refine ⟨m,?_⟩
  filter_upwards [hm,eventually_ge_atTop (1:ℝ)] with X hm hX
  intro i ℓ H U V
  have hF : 1 ≤ Real.exp primeProductWeights.radius*X :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  unfold tailHighScaleRows
  calc
    _ = ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        ∑ j ∈ Finset.range m,
          if V ≤ distinguishedScaleLength k then
            ∑ l : Fin j → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
              tailPrimeTuplePiece i j ℓ ξ H U X (Sum.elim k l) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hm i ℓ H U k]
      simp_rw [tailScaleDoubleRow_partition i _ ℓ ξ H U hF (zero_lt_one.trans_le hX) k]
      split_ifs <;> simp only [Finset.sum_const_zero]
    _ = ∑ j ∈ Finset.range m,
        ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
          ∑ l : Fin j → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
            if V ≤ distinguishedScaleLength k then
              tailPrimeTuplePiece i j ℓ ξ H U X (Sum.elim k l) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp only [Finset.sum_const_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [distinguishedScaleLength_sum_type] using
        sum_partition_sum_type (fun d : (Fin i ⊕ Fin j) →
          Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)) =>
          if V ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
            tailPrimeTuplePiece i j ℓ ξ H U X d else 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UpperHeightSuffix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper height segment is one aligned full tail, starting strictly
above its cutoff unless the segment is empty. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma geometricHeight_filtered_suffix (f : ℝ → ℂ) {H T : ℝ}
    (hH : 0 < H) (hT : 0 < T) (V : ℝ) :
    ∃ j ≤ heightWindowCount H T,
      (j < heightWindowCount H T → V < T*(3/2:ℝ)^j) ∧
      (∑ s ∈ Finset.range (heightWindowCount H T),
        if V < T*(3/2:ℝ)^s then f (T*(3/2:ℝ)^s) else 0) =
        ∑ s ∈ Finset.range (heightWindowCount H (T*(3/2:ℝ)^j)),
          f ((T*(3/2:ℝ)^j)*(3/2:ℝ)^s) := by
  obtain ⟨j,hj,he⟩ := initial_filter_range (p := fun s => T*(3/2:ℝ)^s ≤ V)
    (fun {i j} hij hV => (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3/2) hij) hT.le).trans hV)
    (heightWindowCount H T)
  refine ⟨j,hj,?_,?_⟩
  · intro hjN
    by_contra hn
    have hm : j ∈ (Finset.range (heightWindowCount H T)).filter
        (fun s => T*(3/2:ℝ)^s ≤ V) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN,le_of_not_gt hn⟩
    rw [he] at hm
    exact (lt_irrefl j) (Finset.mem_range.mp hm)
  · have hprefix : (∑ s ∈ Finset.range (heightWindowCount H T),
        if T*(3/2:ℝ)^s ≤ V then f (T*(3/2:ℝ)^s) else 0) =
        (∑ s ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^s))-
          ∑ s ∈ Finset.range (heightWindowCount H (T*(3/2:ℝ)^j)),
            f ((T*(3/2:ℝ)^j)*(3/2:ℝ)^s) := by
      rw [←Finset.sum_filter,he]
      exact geometricHeight_prefix f hH hT hj
    have hsum : (∑ s ∈ Finset.range (heightWindowCount H T),
        if T*(3/2:ℝ)^s ≤ V then f (T*(3/2:ℝ)^s) else 0)+
        (∑ s ∈ Finset.range (heightWindowCount H T),
          if V < T*(3/2:ℝ)^s then f (T*(3/2:ℝ)^s) else 0) =
        ∑ s ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^s) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : T*(3/2:ℝ)^s ≤ V
      · simp only [hs,not_lt.mpr hs,ite_true, if_true,ite_false, if_false,add_zero]
      · simp only [hs,lt_of_not_ge hs,ite_true, if_true,ite_false, if_false,zero_add]
    rw [hprefix] at hsum
    linear_combination hsum

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeTailGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One surviving height window fixes independent prime groups for the
entire signed tail. Their choice therefore does not depend on frequency. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma tailPrimeTupleTail_witness {i j : ℕ} {ξ H T X : ℝ}
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hne : tailPrimeTupleTail i j ξ H T X k ≠ 0) :
    ∃ v ∈ Finset.range (heightWindowCount H T), ∃ q ∈ largePrimeTupleBox i j X,
      tailPrimeTupleTerm i j 0 ξ H (T*(3/2:ℝ)^v) X q*
        normTupleWeight k (largePrimeTupleNorm q) ≠ 0 := by
  have hv : ∃ v ∈ Finset.range (heightWindowCount H T),
      tailPrimeTuplePiece i j 0 ξ H (T*(3/2:ℝ)^v) X k ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Finset.sum_eq_zero h)
  obtain ⟨v,hv,hvn⟩ := hv
  obtain ⟨q,hq,hqn⟩ := tailPrimeTuplePiece_witness k hvn
  exact ⟨v,hv,q,hq,hqn⟩

lemma tailPrimeTuple_scale_product {i j N : ℕ} {ℓ : ℤ} {ξ H U X : ℝ}
    (hX : 0 < X) (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0) :
    X/(2*2^(i+j)) ≤ largeTupleSubsetScale (fun a => (k a).val) Finset.univ ∧
      largeTupleSubsetScale (fun a => (k a).val) Finset.univ ≤ 3*X := by
  obtain ⟨ht,hw⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨hlo,hhi⟩ := tailPrimeTupleTerm_product_range hX ht
  obtain ⟨hl,hu⟩ := largePrimeTuplePiece_subset_range k hw Finset.univ
  rw [largePrimeTupleNorm_prod] at hl hu
  simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] at hu
  refine ⟨?_,hl.trans hhi⟩
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*2^(i+j))).mpr
  nlinarith

theorem eventually_tailPrimeTupleTail_groups (i j : ℕ) {κ ξ : ℝ}
    (hκ : 0 < κ) (hκsmall : κ < 1/12) (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ H T : ℝ,
      ∀ k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (k a).val) →
      tailPrimeTupleTail i j ξ H T X k ≠ 0 →
      ∃ s : Finset (Fin i ⊕ Fin j),
        let B := largeTupleSubsetScale (fun a => (k a).val) s
        let A := largeTupleSubsetScale (fun a => (k a).val) (Finset.univ\s)
        X^(1/3-3*κ) ≤ B ∧ B^2 ≤ 3*X ∧ X/(2*2^(i+j)) ≤ A*B ∧ A*B ≤ 3*X ∧
        (∀ a, 1 ≤ largeTupleNormScale (fun a => (k a).val) a) ∧
        (∀ a, (2*B)^(ξ/2) < largeTupleNormScale (fun a => (k a).val) a) ∧
        ∀ H' T' : ℝ, tailPrimeTupleTail i j ξ H' T' X k =
          ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
            envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ X (fun a => (k a).val) s)
              (largeTupleOtherSupport ξ X (fun a => (k a).val) s)
              (largeTupleSelectedCoefficient ξ X (fun a => (k a).val) s)
              (largeTupleOtherCoefficient ξ X (fun a => (k a).val) s)
              primeProductEnvelope H' T' X := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_tailPrimeTuple_upper_grouping i j hκ hκsmall hξ hξz,
    eventually_tailPrimeTuple_coordinate_envelope (i := i) (j := j) hκ.le hκsmall hξz,
    tailPrimeTuplePiece_rough_scales i j hξ hξz] with X hX hgroup hcoord hrough
  intro H T k hhigh hne
  obtain ⟨v,_hv,q,hq,hqn⟩ := tailPrimeTupleTail_witness k hne
  obtain ⟨s,hB,hBsq⟩ := hgroup 0 H (T*(3/2:ℝ)^v) k hhigh q hq hqn
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hprod := tailPrimeTuple_scale_product hXp k hqn
  have hp : largeTupleSubsetScale (fun a => (k a).val) (Finset.univ\s)*
      largeTupleSubsetScale (fun a => (k a).val) s =
      largeTupleSubsetScale (fun a => (k a).val) Finset.univ := by
    rw [mul_comm,largeTupleSubsetScale_complement]
  have hr := hrough 0 H (T*(3/2:ℝ)^v) k q hq hqn
  have hB3 : largeTupleSubsetScale (fun a => (k a).val) s ≤ 3*X := by
    have hBp := largeTupleSubsetScale_pos (fun a => (k a).val) s
    nlinarith
  refine ⟨s,hB,hBsq,by simpa only [hp] using hprod.1,
    by simpa only [hp] using hprod.2,hr.1,
    hr.2 _ (largeTupleSubsetScale_pos _ _).le hB3,?_⟩
  intro H' T'
  unfold tailPrimeTupleTail
  simp_rw [tailPrimeTuplePiece_full i j 0 ξ H' _ X k
    (hcoord 0 H (T*(3/2:ℝ)^v) k hhigh q hq hqn),
    tailPrimeTupleIndependent_regroup i j 0 ξ H' _ X _ s]
  rw [←Finset.mul_sum,tailPrimeTupleRegrouped_tail]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeUpperTuple
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each upper-height tuple is one aligned suffix. A surviving term chooses
one group for the whole suffix, before applying any norm estimate. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma tailPrimeUpperTuple_suffix (i j : ℕ) (ξ H T X : ℝ)
    (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hH : 0 < H) (hT : 0 < T) :
    ∃ v ≤ heightWindowCount H T,
      (v < heightWindowCount H T → X^(1/100:ℝ) < T*(3/2:ℝ)^v) ∧
      tailPrimeUpperTuple i j ξ H T X d =
        tailPrimeTupleTail i j ξ H (T*(3/2:ℝ)^v) X d := by
  exact geometricHeight_filtered_suffix
    (fun U => tailPrimeTuplePiece i j 0 ξ H U X d) hH hT _

theorem tailPrime_upper_tuple_bound_uniform
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/36 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ξ : ℝ, 0 < ξ → ξ ≤ 2/5 →
      ∀ i j n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ H T : ℝ, Real.log X ≤ T → 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      ∀ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) →
      ‖tailPrimeUpperTuple i j ξ H T X d‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨κ₀,hκ₀,hκ₀small,hgroup⟩ :=
    tailPrime_upper_group_bound_uniform hpub hHuxley hperiod hMV hC hGI hGQ
  refine ⟨κ₀,hκ₀,hκ₀small,?_⟩
  intro κ hκ hκle ξ hξ hξz i j n
  have hκsmall : κ < 1/12 := by linarith
  have hdata (s : Finset (Fin i ⊕ Fin j)) := hgroup κ hκ hκle ξ hξ hξz i j s n
  choose K hK hb using hdata
  have hall := (Filter.eventually_all).mpr hb
  let M : ℝ := 1+∑ s, |K s|
  let c : ℂ := (i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨(‖c‖+1)*M,by positivity,?_⟩
  filter_upwards [hall,eventually_tailPrimeTupleTail_groups i j hκ hκsmall hξ hξz,
    eventually_gt_atTop (1:ℝ)] with X hbound hgeom hX
  intro H T hT hH hHX d hd
  have hXp : 0 < X := zero_lt_one.trans hX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_pos hX]
  have hTp : 0 < T := (Real.log_pos hX).trans_le hT
  obtain ⟨v,_hv,hstart,he⟩ := tailPrimeUpperTuple_suffix i j ξ H T X d
    (zero_lt_one.trans_le hH) hTp
  rw [he]
  by_cases hz : tailPrimeTupleTail i j ξ H (T*(3/2:ℝ)^v) X d = 0
  · rw [hz,norm_zero]
    positivity
  have hv : v < heightWindowCount H T := by
    by_contra hn
    have hc : heightWindowCount H (T*(3/2:ℝ)^v) = 0 := by
      rw [heightWindowCount_shift (zero_lt_one.trans_le hH) hTp]
      omega
    apply hz
    simp only [tailPrimeTupleTail,hc,Finset.range_zero,Finset.sum_empty]
  obtain ⟨s,hBlo,hBsq,hABlo,hABhi,hcoord,hrough,hid⟩ :=
    hgeom H (T*(3/2:ℝ)^v) d hd hz
  let z : largeTupleBoxIndex i j := ⟨(⟨X,hXp⟩,fun a => (d a).val),hcoord⟩
  have hb := hbound s z H (T*(3/2:ℝ)^v) rfl hBlo hBsq hABlo hABhi
    (fun a => hrough a) (hstart hv).le hH hHX
  rw [hid H (T*(3/2:ℝ)^v),norm_mul]
  change ‖c‖ * ‖envelopeCutoffBilinearTail _ _ _ _ _ H _ X‖ ≤ _
  apply (mul_le_mul_of_nonneg_left hb (_root_.norm_nonneg c)).trans
  have hKM : K s ≤ M := by
    have hh := Finset.single_le_sum (fun t _ => abs_nonneg (K t)) (Finset.mem_univ s)
    dsimp [M]
    linarith [le_abs_self (K s)]
  have hconst : ‖c‖*K s ≤ (‖c‖+1)*M := by
    have hm := mul_le_mul_of_nonneg_left hKM (_root_.norm_nonneg c)
    nlinarith
  calc
    _ = (‖c‖*K s)*(X^(5/6:ℝ)/(1+Real.log X)^n) := by ring
    _ ≤ ((‖c‖+1)*M)*(X^(5/6:ℝ)/(1+Real.log X)^n) :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailHighUpperNegligible
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete upper high-scale prime contribution, including all norm
partitions and the finite arity expansion. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem tailHighUpperArity_collection {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (κ H T : ℝ),
      tailHighUpperArity i κ ξ H T X =
        ∑ j ∈ Finset.range m, tailPrimeUpperTupleSum i j κ ξ H T X := by
  obtain ⟨m,hm⟩ := tailHighScaleRows_arity hξ
  refine ⟨m,?_⟩
  filter_upwards [hm] with X hr
  intro i κ H T
  unfold tailHighUpperArity
  simp_rw [hr i 0 H]
  calc
    _ = ∑ v ∈ Finset.range (heightWindowCount H T), ∑ j ∈ Finset.range m,
        ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
          if X^(1/100:ℝ) < T*(3/2:ℝ)^v then
            if X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
              tailPrimeTuplePiece i j 0 ξ H (T*(3/2:ℝ)^v) X d else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp only [Finset.sum_const_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      unfold tailPrimeUpperTupleSum
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (d a).val)
      · simp only [hd,ite_true, if_true,tailPrimeUpperTuple]
      · simp only [hd,ite_false, if_false,ite_self,Finset.sum_const_zero]

theorem tailHighUpperArity_isLittleO_uniform_oai
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/36 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ξ : ℝ, 0 < ξ → ξ ≤ 2/5 →
      ∀ (i : ℕ) (H T : ℝ → ℝ),
      (∀ᶠ X : ℝ in atTop, Real.log X ≤ T X) →
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
      (∀ᶠ X : ℝ in atTop, H X ≤ X^(1/6+1/3000:ℝ)) →
      (fun X => tailHighUpperArity i κ ξ (H X) (T X) X) =o[atTop] firstMomentScale := by
  obtain ⟨κ₀,hκ₀,hκ₀small,hbound⟩ :=
    tailPrime_upper_tuple_bound_uniform hpub hHuxley hperiod hMV hC hGI hGQ
  refine ⟨κ₀,hκ₀,hκ₀small,?_⟩
  intro κ hκ hκle ξ hξ hξz i H T hT hH hHX
  obtain ⟨m,hm⟩ := tailHighUpperArity_collection hξ
  have hpart (j : ℕ) :
      (fun X => tailPrimeUpperTupleSum i j κ ξ (H X) (T X) X) =o[atTop] firstMomentScale := by
    obtain ⟨K,hK,hb⟩ := hbound κ hκ hκle ξ hξ hξz i j (3+(i+j))
    obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i j
    apply Asymptotics.IsBigO.trans_isLittleO
      (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
    apply Asymptotics.IsBigO.of_bound (D*K)
    filter_upwards [hb,hT,hH,hHX,eventually_ge_atTop (1:ℝ)] with X hb ht hh hx hX
    have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
    have hB : 0 ≤ K*X^(5/6:ℝ)/(1+Real.log X)^(3+(i+j)) := by positivity
    have hp (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
        ‖if X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
          tailPrimeUpperTuple i j ξ (H X) (T X) X d else 0‖ ≤
          K*X^(5/6:ℝ)/(1+Real.log X)^(3+(i+j)) := by
      split_ifs with hd
      · exact hb (H X) (T X) ht hh hx d hd
      · simpa only [norm_zero] using hB
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
    unfold tailPrimeUpperTupleSum
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun d _ => hp d)).trans
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right (hcount X hX) hB).trans_eq
    rw [pow_add]
    field_simp [hL.ne']
    ring
  have hs := Asymptotics.IsLittleO.fun_sum (s := Finset.range m) (fun j _ => hpart j)
  apply hs.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hm] with X hx
  exact (hx i κ (H X) (T X)).symm

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.tailHighUpperArity_isLittleO_uniform_oai := @OAI.CubicFirstMoment.tailHighUpperArity_isLittleO_uniform_oai
