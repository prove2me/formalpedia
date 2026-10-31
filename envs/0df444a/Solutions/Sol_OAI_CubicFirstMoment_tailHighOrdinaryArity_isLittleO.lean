-- Prove2me | solution 1 for OAI.CubicFirstMoment.tailHighOrdinaryArity_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:59:35.832111+00:00
-- url     : https://prove2.me/submissions/bcbbf18c-ad53-4690-b979-7b935ca0f0c6

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A020
import Definitions.Def_OAIQ096A023
import Theorems.Thm_OAI_CubicFirstMoment_full_prime_product_height_bilinear
import Theorems.Thm_OAI_CubicFirstMoment_tailPrime_low_group

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteMellinProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.W21.instNorm _root_.instMeasurableSpace
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

theorem norm_gauss_le_one {a : Eisenstein} (ha : primary a) : ‖gauss a‖ ≤ 1 := by
  rw [norm_gauss ha]
  split_ifs <;> norm_num

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormMellinMoments
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem fourier_intervalStep_nonzero {a b ξ : ℝ} (hab : a ≤ b) (hξ : ξ ≠ 0) :
    𝓕 (fun x => (intervalStep a b x : ℂ)) ξ =
      (Complex.exp ((-2 * Real.pi * b * ξ : ℝ) * Complex.I) -
        Complex.exp ((-2 * Real.pi * a * ξ : ℝ) * Complex.I)) /
          ((-2 * Real.pi * ξ : ℝ) * Complex.I) := by
  rw [fourier_intervalStep_eq_integral hab]
  have hc : ((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero _ Complex.I_ne_zero
    exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) Real.pi_ne_zero) hξ
  have he : (fun x : ℝ => Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I)) =
      (fun x : ℝ => Complex.exp (((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I * x)) := by
    funext x
    congr 1
    push_cast
    ring
  rw [he, integral_exp_mul_complex hc]
  congr 2 <;> congr 1 <;> push_cast <;> ring

/-- The multiplier for the dyadic interval [1,2], at every nonzero frequency. -/
theorem dyadic_interval_multiplier {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 (fun x => (intervalStep 0 (Real.log 2) x : ℂ)) ξ =
      (1 - Complex.exp ((-2 * Real.pi * Real.log 2 * ξ : ℝ) * Complex.I)) /
        ((2 * Real.pi * ξ : ℝ) * Complex.I) := by
  rw [fourier_intervalStep_nonzero (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hξ]
  simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero]
  have hneg : ((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I =
      -(((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by push_cast; ring
  rw [hneg]
  ring

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicWeightIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported height weight is controlled by the actual two-sided
dyadic mean. The normalization includes both height intervals. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma dyadicWeightIntegral_bound (f h : ℝ → ℂ) (hf : Continuous f)
    {T M : ℝ} (hT : 0 < T) (_hM : 0 ≤ M) (hh : ∀ t, ‖h t‖ ≤ M)
    (hs : ∀ t, t ∉ dyadicHeightSupport T → h t = 0) :
    ‖∫ t : ℝ, h t*f t‖ ≤ M*T*dyadicHeightMean (fun t => ‖f t‖) T := by
  let g := fun t : ℝ => M*‖f t‖
  have hg : Continuous g := continuous_const.mul hf.norm
  have hU : MeasurableSet (dyadicHeightSupport T) := measurableSet_Icc.union measurableSet_Icc
  have hgi : Integrable ((dyadicHeightSupport T).indicator g) :=
    (hg.continuousOn.integrableOn_compact (isCompact_Icc.union isCompact_Icc)).integrable_indicator hU
  have hb : ‖∫ t : ℝ, h t*f t‖ ≤ ∫ t : ℝ, (dyadicHeightSupport T).indicator g t := by
    apply norm_integral_le_of_norm_le hgi
    filter_upwards with t
    by_cases ht : t ∈ dyadicHeightSupport T
    · rw [indicator_of_mem ht,norm_mul]
      exact mul_le_mul_of_nonneg_right (hh t) (_root_.norm_nonneg _)
    · rw [indicator_of_notMem ht,hs t ht,zero_mul,norm_zero]
  have hd : Disjoint (Icc T (2*T)) (Icc (-2*T) (-T)) := by
    apply Set.disjoint_left.mpr
    intro t hp hn
    linarith [hp.1,hn.2]
  rw [integral_indicator hU] at hb
  change ‖∫ t : ℝ, h t*f t‖ ≤ ∫ t in Icc T (2*T) ∪ Icc (-2*T) (-T), g t at hb
  rw [setIntegral_union hd measurableSet_Icc hg.integrableOn_Icc hg.integrableOn_Icc,
    integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by linarith : T ≤ 2*T),
    ←intervalIntegral.integral_of_le (by linarith : -2*T ≤ -T)] at hb
  apply hb.trans_eq
  dsimp [g,dyadicHeightMean]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  field_simp

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth height windows with ratio 3/2. Their support lies in [T,2T]
in absolute value, exactly the range of the proved bilinear estimates.
The finite telescoping identity keeps the actual truncation multiplier. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma heightWindow_norm_le (T t : ℝ) : ‖heightWindow T t‖ ≤ 1 := by
  rw [heightWindow, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [heightPartitionBump.nonneg (x := t/((3/2)*T)),
    heightPartitionBump.le_one (x := t/((3/2)*T)),
    heightPartitionBump.nonneg (x := t/T), heightPartitionBump.le_one (x := t/T)]

lemma integrable_cutoffHeightMultiplier_window {S : ℝ} (hS : 0 < S) (T : ℝ) :
    Integrable (fun t => cutoffHeightMultiplier S t*heightWindow T t) :=
  (cutoffHeightMultiplier_integrable hS).mul_bdd
    (heightWindow_smooth T).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (heightWindow_norm_le T))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightWindowCount
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite height partition. Every nonzero window lies below
the Fourier cap, and the number of windows costs only one logarithm. -/
noncomputable section
namespace CubicFirstMoment

theorem heightWindowCount_log_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ S T : ℝ, 1 ≤ S → 1 ≤ T →
      (heightWindowCount S T:ℝ) ≤ K*(1+Real.log S) := by
  let r := Real.log (3/2:ℝ)
  let a := 1+Real.log (2*Real.pi)/r
  let b := 1/r
  have hr : 0 < r := Real.log_pos (by norm_num)
  have hc : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have ha : 0 ≤ a := by
    have hc' := Real.log_nonneg hc
    dsimp [a]
    positivity
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨a+b, by linarith, ?_⟩
  intro S T hS hT
  have hSp : 0 < S := zero_lt_one.trans_le hS
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg hS
  have hcap : 1 ≤ 2*Real.pi*S := by nlinarith
  have hmono : heightWindowCount S T ≤ ⌈Real.log (2*Real.pi*S)/r⌉₊ := by
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ hr.le
    rw [Real.log_div (by positivity : 2*Real.pi*S ≠ 0) hTp.ne']
    linarith [Real.log_nonneg hT]
  have hceil := (Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hcap) hr.le)).le
  have hstart := (Nat.cast_le.mpr hmono).trans hceil
  rw [Real.log_mul (by positivity : 2*Real.pi ≠ 0) hSp.ne', add_div] at hstart
  have he : Real.log (2*Real.pi)/r+Real.log S/r+1 = a+b*Real.log S := by
    dsimp [a,b]
    ring
  apply hstart.trans
  rw [he]
  nlinarith [mul_nonneg ha hlogS]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightMultiplier
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two endpoint phases of the actual cutoff. On each smooth height
window the normalized reciprocal factor is uniformly bounded. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma frequencyCutoff_norm_le (x : ℝ) : ‖frequencyCutoff x‖ ≤ 1 := by
  rw [frequencyCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg frequencyBump.nonneg]
  exact frequencyBump.le_one

lemma cutoffHeightMultiplier_eq_endpoints (S : ℝ) {t : ℝ} (ht : t ≠ 0) :
    cutoffHeightMultiplier S t = frequencyCutoff ((t/(2*Real.pi))/S) *
      ((1-Complex.exp ((-Real.log 2*t : ℝ)*Complex.I))/((t:ℂ)*Complex.I)) := by
  rw [cutoffHeightMultiplier, dyadic_interval_multiplier
    (div_ne_zero ht (by positivity))]
  have he : -2*Real.pi*Real.log 2*(t/(2*Real.pi)) = -Real.log 2*t := by field_simp
  have hd : 2*Real.pi*(t/(2*Real.pi)) = t := by field_simp
  rw [he,hd]

lemma cutoffHeightMultiplier_norm_le (S : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ‖cutoffHeightMultiplier S t‖ ≤ 2/|t| := by
  rw [cutoffHeightMultiplier_eq_endpoints S ht, norm_mul]
  have hnum : ‖1-Complex.exp ((-Real.log 2*t : ℝ)*Complex.I)‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    simp only [norm_one, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_self, Real.exp_zero]
    norm_num
  calc
    _ ≤ 1*(2/|t|) := mul_le_mul (frequencyCutoff_norm_le _) (by
      simpa only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one] using div_le_div_of_nonneg_right hnum (abs_nonneg t))
      (by positivity) (by norm_num)
    _ = _ := one_mul _

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformCoordinateWeights
attribute [-instance] _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Fubini for a bounded height polynomial and an integrable
Mellin weight. No mean estimate or interchange is assumed. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma continuous_height_convolution {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) :
    Continuous (fun t => ∫ s : ℝ, f s*G (t+u+s)) := by
  apply continuous_of_dominated (bound := fun s => ‖f s‖*M)
  · intro t
    exact (hf.mul (hG.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · intro t
    filter_upwards with s
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound _) (_root_.norm_nonneg _)
  · exact hfi.norm.mul_const M
  · filter_upwards with s
    exact continuous_const.mul (hG.comp ((continuous_id.add continuous_const).add continuous_const))

lemma integrable_height_convolution_kernel {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun p : ℝ × ℝ => f p.1*G (p.2+u+p.1))
      (volume.prod (volume.restrict (Icc a b))) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let K : ℝ × ℝ → ℝ := fun p => f p.1*G (p.2+u+p.1)
  have hc : Continuous K :=
    (hf.comp continuous_fst).mul (hG.comp ((continuous_snd.add continuous_const).add continuous_fst))
  have hm : AEStronglyMeasurable K (volume.prod μ) := hc.aestronglyMeasurable
  have hb (s : ℝ) : (∫ t, ‖K (s,t)‖ ∂μ) ≤ (b-a)*M*‖f s‖ := by
    have hki : IntervalIntegrable (fun t => ‖K (s,t)‖) volume a b :=
      ((hc.comp (continuous_const.prodMk continuous_id)).norm).intervalIntegrable a b
    have hi := intervalIntegral.integral_mono_on hab hki
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ‖f s‖*M) volume a b)
      (fun t _ => by
        dsimp [K]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg (f s)))
    rw [intervalIntegral.integral_const,smul_eq_mul] at hi
    simpa only [μ,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,
      mul_comm,mul_left_comm,mul_assoc] using hi
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall (fun s =>
    (hc.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc),?_⟩
  apply (hfi.norm.const_mul ((b-a)*M)).mono' hm.norm.integral_prod_right'
  exact Filter.Eventually.of_forall (fun s => by
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => _root_.norm_nonneg _))]
    exact hb s)

lemma height_convolution_interval_swap {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ∫ s : ℝ, f s*G (t+u+s)) =
      ∫ s : ℝ, f s*(∫ t in a..b, G (t+u+s)) := by
  have hi := integrable_height_convolution_kernel hf hfi hG hbound u hab
  have hs := (integral_integral_swap (f := fun s t : ℝ => f s*G (t+u+s)) hi).symm
  simp only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab] at hs
  rw [hs]
  apply integral_congr_ae
  filter_upwards with s
  exact intervalIntegral.integral_const_mul _ _

lemma integrable_height_convolution_interval {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun s : ℝ => f s*(∫ t in a..b, G (t+u+s))) := by
  have hi := (integrable_height_convolution_kernel hf hfi hG hbound u hab).integral_prod_left
  simp only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_const_mul] at hi
  exact hi

theorem dyadicHeightMean_convolution {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    dyadicHeightMean (fun t => ∫ s : ℝ, f s*G (t+u+s)) T =
      ∫ s : ℝ, f s*dyadicHeightMean (fun t => G (t+u+s)) T := by
  have hp : T ≤ 2*T := by linarith
  have hn : -2*T ≤ -T := by linarith
  have hip := integrable_height_convolution_interval hf hfi hG hbound u hp
  have hin := integrable_height_convolution_interval hf hfi hG hbound u hn
  rw [dyadicHeightMean,height_convolution_interval_swap hf hfi hG hbound u hp,
    height_convolution_interval_swap hf hfi hG hbound u hn,← integral_add hip hin,← integral_div]
  apply integral_congr_ae
  filter_upwards with s
  dsimp [dyadicHeightMean]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightConvolutionBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A height bound on the central Mellin window and the actual moment
tail of the Mellin weight suffice for the averaged convolution. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma integrable_height_convolution_mean {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (fun s => f s*dyadicHeightMean (fun t => G (t+u+s)) T) := by
  have hp := integrable_height_convolution_interval hf hfi hG hbound u
    (by linarith : T ≤ 2*T)
  have hn := integrable_height_convolution_interval hf hfi hG hbound u
    (by linarith : -2*T ≤ -T)
  convert (hp.add hn).div_const T using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  dsimp [dyadicHeightMean]
  ring

theorem dyadicHeightMean_convolution_window {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hf0 : ∀ s, 0 ≤ f s)
    (hG : Continuous G) {M B S T : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hS : 0 < S) (hT : 0 < T) (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) (n : ℕ)
    (hfm : Integrable (fun s => ‖s‖^n*f s))
    (hsmall : ∀ s, ‖s‖ ≤ S →
      dyadicHeightMean (fun t => G (t+u+s)) T ≤ B) :
    dyadicHeightMean (fun t => ∫ s : ℝ, f s*G (t+u+s)) T ≤
      B*(∫ s : ℝ, f s)+(2*M)/S^n*(∫ s : ℝ, ‖s‖^n*f s) := by
  let H := fun s => dyadicHeightMean (fun t => G (t+u+s)) T
  have hglobal (s : ℝ) : H s ≤ 2*M := by
    apply dyadicHeightMean_le_const (hG.comp (by fun_prop)) hT
    intro t _
    exact (le_abs_self _).trans (hbound (t+u+s))
  rw [dyadicHeightMean_convolution hf hfi hG hbound u hT]
  calc
    _ ≤ ∫ s : ℝ, B*f s+((2*M)/S^n)*(‖s‖^n*f s) := by
      apply integral_mono (integrable_height_convolution_mean hf hfi hG hbound u hT)
        ((hfi.const_mul B).add (hfm.const_mul ((2*M)/S^n)))
      intro s
      have hh := mellin_window_majorant hB (by positivity : 0 ≤ 2*M) hS n hglobal hsmall s
      calc
        _ ≤ f s*(B+(2*M)/S^n*‖s‖^n) := mul_le_mul_of_nonneg_left hh (hf0 s)
        _ = _ := by dsimp only [Pi.add_apply]; ring
    _ = _ := by rw [integral_add (hfi.const_mul B) (hfm.const_mul ((2*M)/S^n)),
      integral_const_mul,integral_const_mul]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductPolynomialBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OrdinaryGroupRange
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A strict grouping gap above one third implies the actual logarithmic
upper-length condition in the published-input bilinear theorem. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem ordinary_group_upper_range {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      X^(1/3+δ:ℝ) ≤ B → A*B ≤ C*X → A ≤ B^2/(1+Real.log B)^G := by
  let α : ℝ := 1/3+δ
  let ε : ℝ := δ/α
  have hα : 0 < α := by dsimp [α]; linarith
  have hε : 0 < ε := div_pos hδ hα
  have hε1 : ε < 1 := (div_lt_one hα).mpr (by dsimp [α]; linarith)
  have hpower : α*(3-ε) = 1+2*δ := by
    dsimp [ε]
    field_simp [hα.ne']
    dsimp [α]
    ring
  obtain ⟨B₀,hB₀⟩ := eventually_atTop.mp (overlap_power_log_saving hε G 0)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hα).eventually_ge_atTop B₀,
    eventually_const_mul_rpow_le (by linarith : (1:ℝ) < 1+2*δ) C]
    with X hX hXB hgap
  intro A B hB hAB
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX hα.le).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have hL : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hlog : (1+Real.log B)^G ≤ B^ε := by
    have hh := hB₀ B (hXB.trans hB)
    simpa only [Nat.mul_zero,pow_zero,div_one,one_mul] using
      (div_le_iff₀ (Real.rpow_pos_of_pos hBp ε)).mp hh
  have hp : X^(1+2*δ) ≤ B^(3-ε) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le α) hB (by linarith : 0 ≤ 3-ε)
    rw [←Real.rpow_mul hXp.le,hpower] at hh
    exact hh
  have hCX : C*X ≤ B^(3-ε) := by
    have hh : C*X ≤ X^(1+2*δ) := by simpa only [Real.rpow_one] using hgap
    exact hh.trans hp
  have hm : (A*B)*(1+Real.log B)^G ≤ B^3 := by
    calc
      _ ≤ (C*X)*(1+Real.log B)^G := mul_le_mul_of_nonneg_right hAB (pow_nonneg hL.le _)
      _ ≤ (C*X)*B^ε := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC.le hXp.le)
      _ ≤ B^(3-ε)*B^ε := mul_le_mul_of_nonneg_right hCX (Real.rpow_nonneg hBp.le _)
      _ = B^3 := by rw [←Real.rpow_add hBp]; norm_num
  apply (le_div_iff₀ (pow_pos hL G)).mpr
  apply (mul_le_mul_iff_right₀ hBp).mp
  first | (convert hm using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hm.trans (le_of_eq (by ring)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeBoxRange
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both length inequalities in the bilinear theorem follow from a
shorter grouped side and a strict gap above one third. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_prime_box_range {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (n G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      X/(2*2^n) ≤ A*B → A*B ≤ 3*X → B^2 ≤ 3*X → X^(1/3+δ:ℝ) ≤ B →
      B^(1-η/16) ≤ A ∧ A ≤ B^2/(1+Real.log B)^G := by
  let D : ℝ := 2*2^n
  let K : ℝ := 3*D
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := mul_pos (by norm_num) hD
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (eventually_const_mul_rpow_le (by linarith : (1-η/16:ℝ) < 1) K)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by linarith : (0:ℝ) < 1/3+δ)).eventually_ge_atTop T,
    ordinary_group_upper_range hδ (by norm_num : (0:ℝ) < 3) G]
    with X hX hXT hupper
  intro A B hABlow hABhi hBsq hBlow
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by linarith : (0:ℝ) ≤ 1/3+δ)).trans hBlow
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have hAX : X ≤ D*(A*B) := by
    have hh := (div_le_iff₀ hD).mp hABlow
    simpa only [mul_comm] using hh
  have hBA : B ≤ K*A := by
    apply (mul_le_mul_iff_right₀ hBp).mp
    have hm := hBsq.trans (mul_le_mul_of_nonneg_left hAX (by norm_num : (0:ℝ) ≤ 3))
    dsimp only [K]
    nlinarith
  have hpower : K*B^(1-η/16) ≤ B := by
    simpa only [Real.rpow_one] using hT B (hXT.trans hBlow)
  refine ⟨(mul_le_mul_iff_right₀ hK).mp ?_,hupper A B hBlow hABhi⟩
  simpa only [mul_comm] using hpower.trans hBA

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ZeroMellinDecay
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailMellinMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full Mellin envelope preserves a translated height mean.
Only a bounded shift range is needed; the complement uses an actual moment
of the smooth Mellin weight and the coarse polynomial bound. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

theorem complex_mellin_height_mean {P F w : ℝ → ℂ}
    (hP : Continuous P) (hF : Continuous F) (hw : Integrable w)
    (hwn : Continuous (fun s => ‖w s‖))
    (he : ∀ t, F t = ∫ s : ℝ, w s*P (t-s))
    {M B S T : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hS : 0 < S) (hT : 0 < T)
    (hbound : ∀ t, ‖P t‖ ≤ M) (n : ℕ)
    (hmoment : Integrable (fun s : ℝ => |s|^n*‖w s‖))
    (hsmall : ∀ s, |s| ≤ S → dyadicHeightMean (fun t => ‖P (t+s)‖) T ≤ B) :
    dyadicHeightMean (fun t => ‖F t‖) T ≤
      B*(∫ s : ℝ, ‖w s‖)+(2*M)/S^n*(∫ s : ℝ, |s|^n*‖w s‖) := by
  let f := fun s => ‖w (-s)‖
  let G := fun t => ‖P t‖
  have hf : Continuous f := hwn.comp continuous_neg
  have hfi : Integrable f := hw.norm.comp_neg
  have hG : Continuous G := hP.norm
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by
    rw [Real.norm_of_nonneg (_root_.norm_nonneg _)]
    exact hbound t
  have hconv : Continuous (fun t => ∫ s : ℝ, f s*G (t+0+s)) :=
    continuous_height_convolution hf hfi hG hGb 0
  have hm : Integrable (fun s : ℝ => ‖s‖^n*f s) := by
    simpa only [f,Real.norm_eq_abs,abs_neg] using hmoment.comp_neg
  have hmajor (t : ℝ) : ‖F t‖ ≤ ∫ s : ℝ, f s*G (t+0+s) := by
    rw [he t]
    calc
      _ ≤ ∫ s : ℝ, ‖w s*P (t-s)‖ := norm_integral_le_integral_norm _
      _ = ∫ s : ℝ, f s*G (t+0+s) := by
        rw [←integral_neg_eq_self (fun s : ℝ => ‖w s*P (t-s)‖) volume]
        simp only [f,G,norm_mul,sub_neg_eq_add,add_zero]
  have hc := dyadicHeightMean_convolution_window hf hfi (fun _ => _root_.norm_nonneg _)
    hG hM hB hS hT hGb 0 n hm (fun s hs => by
      simpa only [G,add_zero] using hsmall s (by simpa only [Real.norm_eq_abs] using hs))
  have hzero : (∫ s : ℝ, f s) = ∫ s : ℝ, ‖w s‖ := by
    simpa only [f] using integral_neg_eq_self (fun s : ℝ => ‖w s‖) volume
  have hn : (∫ s : ℝ, ‖s‖^n*f s) = ∫ s : ℝ, |s|^n*‖w s‖ := by
    simpa only [f,Real.norm_eq_abs,abs_neg] using
      integral_neg_eq_self (fun s : ℝ => |s|^n*‖w s‖) volume
  exact (dyadicHeightMean_mono hF.norm hconv hT (fun t _ => hmajor t)).trans
    (by simpa only [hzero,hn] using hc)

theorem zeroLineMellin_height_mean (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) {P F : ℝ → ℂ} (hP : Continuous P) (hF : Continuous F)
    (he : ∀ t, F t = ∫ s : ℝ, zeroLineMellinWeight W X s*P (t-s))
    {M B S T : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hS : 0 < S) (hT : 0 < T)
    (hbound : ∀ t, ‖P t‖ ≤ M) (n : ℕ)
    (hsmall : ∀ s, |s| ≤ S → dyadicHeightMean (fun t => ‖P (t+s)‖) T ≤ B) :
    dyadicHeightMean (fun t => ‖F t‖) T ≤
      B*zeroLineMellinMass W+(2*M)/S^n*zeroLineMellinMoment W n := by
  have hb := complex_mellin_height_mean hP hF
    (zeroLineMellinWeight_integrable W hW hpos hsm hX)
    (continuous_norm_zeroLineMellinWeight W hW hpos hsm hX) he hM hB hS hT hbound n
    (zeroLineMellinWeight_moment_integrable W hW hpos hsm hX n) hsmall
  rw [zeroLineMellinWeight_mass W hX,zeroLineMellinWeight_moment W hX n] at hb
  exact hb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailProductMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-line Mellin separation for the original Gauss polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem product_gauss_mellin (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (hA : ∀ a ∈ A, primary a) (hB : ∀ b ∈ B, primary b)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (u : ℝ) :
    productGaussSmoothed A B α β ℓ W X u =
      ∫ τ : ℝ, zeroLineMellinWeight W X τ*productGaussPolynomial A B α β ℓ (u-τ) := by
  let c := fun a b => α a*β b*theta ℓ (a*b)*gauss (a*b)*normTwist u (a*b)
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
      simp only [productGaussPolynomial,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [f,c]
      rw [sub_eq_add_neg,normTwist_eq_mellinPhase,normTwist_eq_mellinPhase,mellinPhase_add_height]
      ring

lemma productGaussPolynomial_continuous (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) : Continuous (productGaussPolynomial A B α β ℓ) := by
  unfold productGaussPolynomial normTwist
  fun_prop

lemma productGaussSmoothed_continuous (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) :
    Continuous (productGaussSmoothed A B α β ℓ W X) := by
  unfold productGaussSmoothed normTwist
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailProductMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded-shift mean for the unsmoothed Gauss polynomial suffices
for its actual product envelope. All complementary Mellin frequencies are
paid for by an integrable moment, with no frequency discarded. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellinMoment_nonneg (W : ℝ → ℂ) (n : ℕ) :
    0 ≤ zeroLineMellinMoment W n := by
  unfold zeroLineMellinMoment
  positivity

theorem productGaussSmoothed_height_mean (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X M B V T : ℝ} (hX : 0 < X) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hV : 0 < V) (hT : 0 < T)
    (hbound : ∀ u, ‖productGaussPolynomial P S α β ℓ u‖ ≤ M) (n : ℕ)
    (hsmall : ∀ u, |u| ≤ V →
      dyadicHeightMean (fun t => ‖productGaussPolynomial P S α β ℓ (t+u)‖) T ≤ B) :
    dyadicHeightMean (fun t => ‖productGaussSmoothed P S α β ℓ W X t‖) T ≤
      B*zeroLineMellinMass W+(2*M)/V^n*zeroLineMellinMoment W n := by
  exact zeroLineMellin_height_mean W hW hpos hsm hX
    (productGaussPolynomial_continuous P S α β ℓ)
    (productGaussSmoothed_continuous P S α β ℓ W X)
    (fun t => product_gauss_mellin P S α β hP hS ℓ W hW hpos hsm hX t)
    hM hB hV hT hbound n hsmall

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem fullPrimeProductSmoothed_height_mean {R : ℝ} (hR : 0 ≤ R)
    (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
    (hXA : ∀ i, 0 < XA i) (hXB : ∀ i, 0 < XB i)
    (hAlo : ∀ i x, x < 1 → WA i x = 0) (hAhi : ∀ i x, R < x → WA i x = 0)
    (hBlo : ∀ i x, x < 1 → WB i x = 0) (hBhi : ∀ i x, R < x → WB i x = 0)
    (hWA : ∀ i x, ‖WA i x‖ ≤ 1) (hWB : ∀ i x, ‖WB i x‖ ≤ 1)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X E V T : ℝ} (hX : 0 < X) (hE : 0 ≤ E)
    (hV : 0 < V) (hT : 0 < T) (n : ℕ)
    (hsmall : ∀ u, |u| ≤ V →
      dyadicHeightMean (fun t => ‖fullPrimeProductGauss R WA WB XA XB (u+t)‖) T ≤ E) :
    dyadicHeightMean (fun t => ‖productGaussSmoothed
      (fullSquarefreePrimeSupport R WA XA 1) (fullSquarefreePrimeSupport R WB XB 1)
      (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) 0 W X t‖) T ≤
      E*zeroLineMellinMass W+
        (2*(primeCoefficientMassConstant R (Fintype.card κ)*
          primeCoefficientMassConstant R (Fintype.card ι)*(∏ i, XA i)*(∏ i, XB i)))/V^n*
            zeroLineMellinMoment W n := by
  have he (u : ℝ) : productGaussPolynomial
      (fullSquarefreePrimeSupport R WA XA 1) (fullSquarefreePrimeSupport R WB XB 1)
      (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) 0 u =
      fullPrimeProductGauss R WA WB XA XB u := by
    simp only [productGaussPolynomial,fullPrimeProductGauss,theta_zero,mul_one]
  have hpA : 0 ≤ ∏ i, XA i := (Finset.prod_pos (fun i _ => hXA i)).le
  have hpB : 0 ≤ ∏ i, XB i := (Finset.prod_pos (fun i _ => hXB i)).le
  apply productGaussSmoothed_height_mean _ _ _ _
    (fun a ha => (fullSquarefreePrimeSupport_primary R WA XA 1 ha).1)
    (fun b hb => (fullSquarefreePrimeSupport_primary R WB XB 1 hb).1)
    0 W hW hpos hsm hX (by unfold primeCoefficientMassConstant; positivity) hE hV hT _ n _
  · intro u
    rw [he]
    simpa only [mul_assoc] using fullPrimeProductGauss_bound hR WA WB XA XB hXA hXB hAlo hAhi hBlo hBhi hWA hWB u
  · intro u hu
    simp_rw [he]
    simpa only [add_comm] using hsmall u hu

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailMellinScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eight Mellin moments at B^(1/4) absorb the coarse product mass
throughout A <= B². The remaining factor B^(-1) pays for any fixed log. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma primeTail_mellin_error_scale {A B : ℝ} (hA : 0 < A) (hB : 1 ≤ B)
    (hAB : A ≤ B^2) :
    A*B/(B^(1/4:ℝ))^8 ≤ A^(5/6:ℝ)*B^(5/6:ℝ)/B := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hVp : 0 < A*B := mul_pos hA hBp
  have hV : A*B ≤ B^3 := by nlinarith [mul_le_mul_of_nonneg_right hAB hBp.le]
  have hroot : (A*B)^(1/6:ℝ) ≤ B := by
    calc
      _ ≤ (B^3)^(1/6:ℝ) := Real.rpow_le_rpow hVp.le hV (by norm_num)
      _ = B^(1/2:ℝ) := by rw [←Real.rpow_natCast,←Real.rpow_mul hBp.le]; norm_num
      _ ≤ B^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
      _ = B := Real.rpow_one B
  have hs : (B^(1/4:ℝ))^8 = B^2 := by
    rw [←Real.rpow_mul_natCast hBp.le]
    norm_num
  rw [hs]
  apply (div_le_div_iff₀ (sq_pos_of_pos hBp) hBp).mpr
  have he : A*B = (A*B)^(5/6:ℝ)*(A*B)^(1/6:ℝ) := by
    rw [←Real.rpow_add hVp]
    norm_num
  have hh := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ (A*B)^(5/6:ℝ)*B by positivity)
  rw [Real.mul_rpow hA.le hBp.le] at hh
  calc
    A*B*B = ((A*B)^(5/6:ℝ)*(A*B)^(1/6:ℝ))*B := by rw [←he]
    _ = (A^(5/6:ℝ)*B^(5/6:ℝ)*B)*(A*B)^(1/6:ℝ) := by
      rw [Real.mul_rpow hA.le hBp.le]
      ring
    _ ≤ (A^(5/6:ℝ)*B^(5/6:ℝ)*B)*B := hh
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailHeckeMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The published Hecke height mean applied through the full original
product envelope. The bounded shift condition is discharged using eight
Mellin moments and the actual coarse prime-convolution bound. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem full_prime_product_smoothed_height
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
    (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
    (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
    (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
    (hAlo : ∀ r i x, x < 1 → WA r i x = 0)
    (hAhi : ∀ r i x, R < x → WA r i x = 0)
    (hBlo : ∀ r i x, x < 1 → WB r i x = 0)
    (hBhi : ∀ r i x, R < x → WB r i x = 0)
    (hWAone : ∀ r i x, ‖WA r i x‖ ≤ 1) (hWBone : ∀ r i x, ‖WB r i x‖ ≤ 1)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (k : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (X T : ℝ),
      B₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
      (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
      (LB r)^(1-η/4) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
      0 < X →
      (1+Real.log (LB r))^m ≤ T → T ≤ (LB r)^(7/20:ℝ) →
      dyadicHeightMean (fun t => ‖productGaussSmoothed
        (fullSquarefreePrimeSupport R (WA r) XA 1)
        (fullSquarefreePrimeSupport R (WB r) XB 1)
        (fullPrimeCoefficient R (WA r) XA) (fullPrimeCoefficient R (WB r) XB)
        0 W X t‖) T ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
  obtain ⟨η,σ,G,K,B₀,m,hη,hηone,hσ,hK,hmean⟩ := full_prime_product_height_bilinear
    hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ LA LB WA WB hLA hLB hWA hWB
    hAlo hAhi hBlo hBhi k
  obtain ⟨B₁,hB₁⟩ := eventually_atTop.mp
    (overlap_power_log_saving (by norm_num : (0:ℝ) < 1) k 0)
  let M := primeCoefficientMassConstant R (Fintype.card κ)*
    primeCoefficientMassConstant R (Fintype.card ι)
  have hM : 0 ≤ M := by dsimp [M,primeCoefficientMassConstant]; positivity
  let K' := K*zeroLineMellinMass W+2*M*zeroLineMellinMoment W 8+1
  have hmass := zeroLineMellinMass_nonneg W
  have hmom := zeroLineMellinMoment_nonneg W 8
  refine ⟨η,G,K',max B₀ B₁,m,hη,hηone,by dsimp [K']; positivity,?_⟩
  intro r XA XB X T hB hprodA hprodB hXA hXB hAlow hAhigh hX hT hThi
  have hAp : 0 < LA r := zero_lt_one.trans_le (hLA r)
  have hBp : 0 < LB r := zero_lt_one.trans_le (hLB r)
  have hL : 0 < 1+Real.log (LB r) := by linarith [Real.log_nonneg (hLB r)]
  have hLone : 1 ≤ 1+Real.log (LB r) := by linarith [Real.log_nonneg (hLB r)]
  have hAB : LA r ≤ (LB r)^2 :=
    hAhigh.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hLone))
  have hTpos : 0 < T := (pow_pos hL m).trans_le hT
  have hsmall (u : ℝ) (hu : |u| ≤ (LB r)^(1/4:ℝ)) :
      dyadicHeightMean (fun t => ‖fullPrimeProductGauss R (WA r) (WB r) XA XB (u+t)‖) T ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
    exact hmean r XA XB 1 1 u T ((le_max_left _ _).trans hB) hprodA hprodB hXA hXB
      hAlow hAhigh one_ne_zero (by simp; exact Real.one_le_rpow (hLB r) hσ.le) hT hThi
      (hu.trans (Real.rpow_le_rpow_of_exponent_le (hLB r) (by norm_num)))
  have hb := fullPrimeProductSmoothed_height_mean (zero_le_one.trans hR) (WA r) (WB r) XA XB
    (fun i => zero_lt_one.trans_le (hXA i))
    (fun i => lt_trans (Real.rpow_pos_of_pos (by linarith [hLB r] : 0 < 2*LB r) c) (hXB i))
    (hAlo r) (hAhi r) (hBlo r) (hBhi r) (hWAone r) (hWBone r)
    W hW hpos hsm hX (by positivity) (Real.rpow_pos_of_pos hBp _) hTpos 8 hsmall
  rw [hprodA,hprodB] at hb
  have hlog : (1+Real.log (LB r))^k ≤ LB r := by
    have hh := hB₁ (LB r) ((le_max_right _ _).trans hB)
    simp only [Real.rpow_one,Nat.mul_zero,pow_zero,div_one] at hh
    exact (div_le_one hBp).mp hh
  have he := primeTail_mellin_error_scale hAp (hLB r) hAB
  have he' : LA r*LB r/((LB r)^(1/4:ℝ))^8 ≤
      (LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k :=
    he.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hL k) hlog)
  have herr : (2*(M*LA r*LB r))/((LB r)^(1/4:ℝ))^8*zeroLineMellinMoment W 8 ≤
      (2*M*zeroLineMellinMoment W 8)*
        ((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) := by
    calc
      _ = (2*M*zeroLineMellinMoment W 8)*
          (LA r*LB r/((LB r)^(1/4:ℝ))^8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he' (by positivity)
  apply hb.trans
  change (K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k)*zeroLineMellinMass W+
    (2*(M*LA r*LB r))/((LB r)^(1/4:ℝ))^8*zeroLineMellinMoment W 8 ≤ _
  calc
    _ ≤ (K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k)*zeroLineMellinMass W+
        (2*M*zeroLineMellinMoment W 8)*
          ((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) :=
      add_le_add le_rfl herr
    _ = (K*zeroLineMellinMass W+2*M*zeroLineMellinMoment W 8)*
        ((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) := by ring
    _ ≤ K'*((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) :=
      mul_le_mul_of_nonneg_right (by dsimp [K']; linarith) (by positivity)
    _ = _ := by ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Fourier height window is bounded by its two-sided mean,
including the reciprocal height normalization and both endpoint phases. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cutoffHeightWindow_integral_bound (f : ℝ → ℂ) (hf : Continuous f)
    (H X : ℝ) {T : ℝ} (hT : 0 < T) :
    ‖∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow T t*
      Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*f t‖ ≤
      2*dyadicHeightMean (fun t => ‖f t‖) T := by
  let w := fun t => cutoffHeightMultiplier H t*heightWindow T t*
    Complex.exp ((-Real.log X*t:ℝ)*Complex.I)
  have hs (t : ℝ) (ht : t ∉ dyadicHeightSupport T) : w t = 0 := by
    simp only [w,heightWindow_zero hT ht,mul_zero,zero_mul]
  have hb (t : ℝ) : ‖w t‖ ≤ 2/T := by
    by_cases ht : t ∈ dyadicHeightSupport T
    · have ha : T ≤ |t| := by
        rcases ht with ht | ht
        · exact ht.1.trans (le_abs_self t)
        · exact (by linarith [ht.2] : T ≤ -t).trans (neg_le_abs t)
      have hp : 0 < |t| := hT.trans_le ha
      simp only [w,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
      calc
        _ ≤ ‖cutoffHeightMultiplier H t‖*1 :=
          mul_le_mul_of_nonneg_left (heightWindow_norm_le T t) (_root_.norm_nonneg _)
        _ ≤ 2/|t| := by simpa only [mul_one] using cutoffHeightMultiplier_norm_le H (abs_pos.mp hp)
        _ ≤ 2/T := div_le_div_of_nonneg_left (by norm_num) hT ha
    · rw [hs t ht,norm_zero]
      positivity
  have he := dyadicWeightIntegral_bound f w hf hT (by positivity : 0 ≤ 2/T) hb hs
  change ‖∫ t : ℝ, w t*f t‖ ≤ _
  exact he.trans_eq (by field_simp)

lemma productGaussWindow_integral (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) {H : ℝ} (hH : 0 < H) (U X : ℝ) :
    productGaussWindow P S α β ℓ W H U X =
      ∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow U t*
        Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*
          productGaussSmoothed P S α β ℓ W X t := by
  let c := fun q : Eisenstein × Eisenstein =>
    α q.1*β q.2*theta ℓ (q.1*q.2)*gauss (q.1*q.2)*W (norm (q.1*q.2)/X)
  have he := height_norm_polynomial_integral (P.product S) c (fun q => q.1*q.2)
    (fun t => cutoffHeightMultiplier H t*heightWindow U t)
    (integrable_cutoffHeightMultiplier_window hH U) (Real.log X)
  simp only [Finset.product_eq_sprod,Finset.sum_product] at he
  calc
    _ = ∑ a ∈ P, ∑ b ∈ S, c (a,b)*
        heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow U t)
          (Real.log (norm (a*b))-Real.log X) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp [productGaussWindow,productGaussHeightWindowKernel,c]
      ring
    _ = _ := by
      rw [he]
      congr 1
      funext t
      simp only [productGaussSmoothed,Finset.mul_sum,c]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

lemma productGaussWindow_bound (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) {H U : ℝ} (hH : 0 < H) (hU : 0 < U) (X : ℝ) :
    ‖productGaussWindow P S α β ℓ W H U X‖ ≤
      2*dyadicHeightMean (fun t => ‖productGaussSmoothed P S α β ℓ W X t‖) U := by
  rw [productGaussWindow_integral P S α β ℓ W hH U X]
  exact cutoffHeightWindow_integral_bound _
    (productGaussSmoothed_continuous P S α β ℓ W X) H X hU

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

lemma geometricHeight_filtered_prefix (f : ℝ → ℂ) {H T : ℝ}
    (hH : 0 < H) (hT : 0 < T) (V : ℝ) :
    ∃ j ≤ heightWindowCount H T,
      (∑ s ∈ Finset.range (heightWindowCount H T),
        if T*(3/2:ℝ)^s ≤ V then f (T*(3/2:ℝ)^s) else 0) =
        (∑ s ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^s))-
          ∑ s ∈ Finset.range (heightWindowCount H (T*(3/2:ℝ)^j)),
            f ((T*(3/2:ℝ)^j)*(3/2:ℝ)^s) := by
  obtain ⟨j,hj,he⟩ := initial_filter_range (p := fun s => T*(3/2:ℝ)^s ≤ V)
    (fun {i j} hij hV =>
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3/2) hij) hT.le).trans hV)
    (heightWindowCount H T)
  refine ⟨j,hj,?_⟩
  calc
    _ = ∑ s ∈ (Finset.range (heightWindowCount H T)).filter
        (fun s => T*(3/2:ℝ)^s ≤ V), f (T*(3/2:ℝ)^s) := (Finset.sum_filter _ _).symm
    _ = ∑ s ∈ Finset.range j, f (T*(3/2:ℝ)^s) := by rw [he]
    _ = _ := geometricHeight_prefix f hH hT hj

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeHeckeWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Specialization of the full-envelope Hecke tail to the literal
independent coordinates supplied by a surviving prime tuple. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma productGaussWindow_swap (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) (H T X : ℝ) :
    productGaussWindow P S α β ℓ W H T X = productGaussWindow S P β α ℓ W H T X := by
  unfold productGaussWindow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm b a]
  ring

theorem tailPrime_hecke_window {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (k : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ),
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      B₀ ≤ B → (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      B^(1-η/16) ≤ A → A ≤ B^2/(1+Real.log B)^G →
      (1+Real.log B)^m ≤ T → 0 < H → T ≤ B^(7/20:ℝ) →
      ‖productGaussWindow (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
        (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s)
        0 primeProductEnvelope H T z.1.1‖ ≤
          K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  obtain ⟨η,G,K,B₀,m,hη,hηone,hK,hbound⟩ := full_prime_product_smoothed_height
    hpub hHuxley hperiod hMV hC (by positivity : (0:ℝ) < ξ/2)
    (by linarith : ξ/2 ≤ 1) (by norm_num : (1:ℝ) ≤ 2) hGI hGQ
    (largeTupleRestrictedLength (fun a => a ∉ s)) (largeTupleGroupLength s)
    (largeTupleRestrictedWeight (fun a => a ∉ s) ξ) (largeTupleGroupWeight ξ s)
    (largeTupleRestrictedLength_one (fun a => a ∉ s)) (largeTupleGroupLength_one s)
    (largeTupleRestrictedLogWeights (fun a => a ∉ s) ξ) (largeTupleGroupLogWeights ξ s)
    (fun z a _x hx => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 a hx)
    (fun z a x => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 a x)
    (fun z a x => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 a x)
    primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth k
  refine ⟨η,G,2*K,B₀,m,hη,hηone,by positivity,?_⟩
  intro z H T
  dsimp only
  intro hB hrough hAlow hAhigh hT hH hTtop
  have hb := hbound z
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale z.1.2 a)
    (fun a : s => largeTupleNormScale z.1.2 a) z.1.1 T
  simp only [largeTupleRestrictedLength_notMem] at hb
  have hh := hb hB (largeTupleRestrictedLength_notMem s z)
    (Finset.prod_coe_sort s (fun a => largeTupleNormScale z.1.2 a))
    (fun a => z.property a) hrough
    ((Real.rpow_le_rpow_of_exponent_le (largeTupleGroupLength_one s z)
      (by linarith : 1-η/4 ≤ 1-η/16)).trans hAlow)
    hAhigh z.1.1.property hT hTtop
  have hTp : 0 < T := (pow_pos (by
    linarith [Real.log_nonneg (largeTupleGroupLength_one s z)] :
      0 < 1+Real.log (largeTupleGroupLength s z)) m).trans_le hT
  rw [productGaussWindow_swap]
  apply (productGaussWindow_bound _ _ _ _ 0 primeProductEnvelope hH hTp z.1.1).trans
  exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeSmallRange
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual small prime groups meet the localized length range. Constants
from their fixed support widths are retained until a genuine exponent or
logarithmic margin absorbs them. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_tailPrime_small_localized_length {D K : ℝ} (hD : 0 < D) (hK : 0 < K) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ, 0 < B → X/D ≤ A*B →
      B ≤ X^(39/100:ℝ) → K*B^(3/2:ℝ) ≤ A := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (39/40:ℝ) < 1 by norm_num) (D*K)]
    with X hX hgap
  intro A B hB hAB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hpow : B^(5/2:ℝ) ≤ X^(39/40:ℝ) := by
    calc
      _ ≤ (X^(39/100:ℝ))^(5/2:ℝ) :=
        Real.rpow_le_rpow hB.le hBX (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hXp.le]; norm_num
  have hprod : D*(B*(K*B^(3/2:ℝ))) ≤ D*(A*B) := by
    calc
      _ = (D*K)*B^(5/2:ℝ) := by
        have he : B*B^(3/2:ℝ) = B^(5/2:ℝ) := by
          calc
            _ = B^(1:ℝ)*B^(3/2:ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [←Real.rpow_add hB]; norm_num
        calc
          _ = (D*K)*(B*B^(3/2:ℝ)) := by ring
          _ = _ := by rw [he]
      _ ≤ (D*K)*X^(39/40:ℝ) := mul_le_mul_of_nonneg_left hpow (mul_pos hD hK).le
      _ ≤ X := by simpa only [Real.rpow_one] using hgap
      _ ≤ D*(A*B) := by
        have hh := (div_le_iff₀ hD).mp hAB
        nlinarith
  have he : D*B*(K*B^(3/2:ℝ)) ≤ D*B*A := by nlinarith [hprod]
  exact (mul_le_mul_iff_right₀ (mul_pos hD hB)).mp he


lemma tailPrime_low_upper_of_constant {X A B c Q L : ℝ}
    (hX : 0 < X) (hB : 0 < B) (hc : 0 < c)
    (hAB : A*B ≤ 3*X) (hBlo : c*X^(1/3:ℝ) ≤ B)
    (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hmargin : 3*Q ≤ c^3*L^3) :
    Q*A ≤ B^2*L^3 := by
  have hcX := pow_le_pow_left₀ (by positivity : 0 ≤ c*X^(1/3:ℝ)) hBlo 3
  rw [mul_pow,←Real.rpow_mul_natCast hX.le] at hcX
  norm_num at hcX
  apply (mul_le_mul_iff_left₀ hB).mp
  calc
    Q*A*B ≤ (3*Q)*X := by nlinarith only [mul_le_mul_of_nonneg_left hAB hQ]
    _ ≤ (c^3*L^3)*X := mul_le_mul_of_nonneg_right hmargin hX.le
    _ = (c^3*X)*L^3 := by ring
    _ ≤ B^3*L^3 := mul_le_mul_of_nonneg_right hcX (by positivity)
    _ = B^2*L^3*B := by ring

theorem eventually_tailPrime_small_low_upper {c Q : ℝ} (hc : 0 < c) (hQ : 0 ≤ Q) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      c*X^(1/3:ℝ) ≤ B → A*B ≤ 3*X → Q*A ≤ B^2*(1+Real.log B)^3 := by
  have hnorm : Tendsto (fun X : ℝ => c*X^(1/3:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul_atTop hc
  filter_upwards [eventually_gt_atTop (0:ℝ),
    hnorm.eventually_ge_atTop (Real.exp (max 1 (3*Q/c^3)))] with X hX hlarge
  intro A B hBlo hAB
  have hBexp := hlarge.trans hBlo
  have hB : 0 < B := (Real.exp_pos _).trans_le hBexp
  have hlog : max 1 (3*Q/c^3) ≤ Real.log B := by
    simpa using Real.log_le_log (Real.exp_pos _) hBexp
  have hL : 1 ≤ 1+Real.log B := by linarith [le_max_left (1:ℝ) (3*Q/c^3)]
  have hpow : 1+Real.log B ≤ (1+Real.log B)^3 := le_self_pow₀ hL (by norm_num : 3 ≠ 0)
  have hmargin : 3*Q ≤ c^3*(1+Real.log B)^3 := by
    have ht : 3*Q/c^3 ≤ (1+Real.log B)^3 := by
      linarith [le_max_right (1:ℝ) (3*Q/c^3)]
    have hh := (div_le_iff₀ (pow_pos hc 3)).mp ht
    nlinarith only [hh]
  exact tailPrime_low_upper_of_constant hX hB hc hAB hBlo (zero_le_one.trans hL) hQ hmargin

theorem eventually_tailPrime_small_high_upper {κ γ Q : ℝ} (hκ : 0 < κ)
    (hκsmall : κ < 1/12) (hQ : 0 < Q)
    (hmargin : 1 < (1/3-3*κ)*(3+γ)) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      X^(1/3-3*κ) ≤ B → A*B ≤ 3*X → Q*A ≤ B^(2+γ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le hmargin (3*Q)] with X hX hgap
  intro A B hBlo hAB
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hBp : 0 < B := (Real.rpow_pos_of_pos hXp _).trans_le hBlo
  have hexp : 0 ≤ 3+γ := by
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1/3-3*κ) (le_of_not_ge hh)
    linarith
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hBlo hexp
  rw [←Real.rpow_mul hXp.le] at hp
  have htop : 3*Q*X ≤ B^(3+γ) := by
    simpa only [Real.rpow_one] using hgap.trans hp
  apply (mul_le_mul_iff_left₀ hBp).mp
  calc
    Q*A*B ≤ 3*Q*X := by nlinarith only [mul_le_mul_of_nonneg_left hAB hQ.le]
    _ ≤ B^(3+γ) := htop
    _ = B^(2+γ)*B := by
      calc
        _ = B^((2+γ)+1) := by congr 1; ring
        _ = B^(2+γ)*B^((1:ℝ)) := Real.rpow_add hBp _ _
        _ = _ := by rw [Real.rpow_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeHeightRanges
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original logarithmic and power height thresholds meet the group
estimates, with every fixed support constant retained. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma tailPrime_height_cube {X B η : ℝ} (hX : 1 ≤ X) (hη : η ≤ 1/1500)
    (hB : X^(1/4:ℝ) ≤ B) : X^(1/6+η) ≤ B^3 := by
  calc
    _ ≤ X^((1/4:ℝ)*3) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    _ = (X^(1/4:ℝ))^3 := (Real.rpow_mul_natCast (zero_le_one.trans hX) _ _)
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hB 3

theorem eventually_tailPrime_fixed_width_log {C : ℝ} (hC : 1 ≤ C) (m : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, 1 ≤ B → B ≤ 3*X →
      (1+Real.log (C*B))^m ≤ (1+Real.log X)^(m+1) := by
  let D : ℝ := 2+|Real.log (3*C)|
  have hD : 1 ≤ D := by dsimp [D]; linarith [abs_nonneg (Real.log (3*C))]
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (D^m)] with X hX hlarge
  intro B hB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hCB : 1 ≤ C*B := one_le_mul_of_one_le_of_one_le hC hB
  have hL : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hb := Real.log_le_log (zero_lt_one.trans_le hCB)
    (mul_le_mul_of_nonneg_left hBX hCp.le)
  rw [show C*(3*X) = (3*C)*X by ring,
    Real.log_mul (by positivity : (3*C) ≠ 0) hXp.ne'] at hb
  have hmajor : 1+Real.log (C*B) ≤ D*(1+Real.log X) := by
    have hd := le_abs_self (Real.log (3*C))
    have hn := abs_nonneg (Real.log (3*C))
    have hm := mul_nonneg hn (Real.log_nonneg hX)
    dsimp [D]
    nlinarith
  calc
    _ ≤ (D*(1+Real.log X))^m :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg hCB]) hmajor m
    _ = D^m*(1+Real.log X)^m := mul_pow _ _ _
    _ ≤ (1+Real.log X)*(1+Real.log X)^m :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by rw [pow_succ]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeOrdinaryGroup
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary high rows have a closed one-third grouping even at the
exceptional triple. Only support geometry is used here. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma tailPrimeTupleOrdinary_upper {i j N : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {H U X : ℝ} (hX : 1 ≤ X) (hξz : ξ ≤ 2/5)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0)
    (a : Fin i ⊕ Fin j) : largePrimeTupleNorm q a ≤ 3*X^(131/200:ℝ) := by
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
      (show (2/5:ℝ) ≤ 131/200 by norm_num)
    nlinarith [Real.rpow_pos_of_pos hXp (131/200:ℝ)]
  · have hprim : primary (∏ b, q.2 b) := primary_finset_prod _ _
      (fun b _ => (mem_primeCutoff.mp
        (Fintype.mem_piFinset.mp (Finset.mem_product.mp hq).2 b)).1.1)
    have hnb := norm_le_of_dvd (primary_ne_zero hprim)
      (Finset.dvd_prod_of_mem q.2 (Finset.mem_univ b))
    have hnr := hhigh.trans (largePrimeTuplePiece_distinguished_range k hw).1
    have hprod := (tailPrimeTupleTerm_product_range hXp ht).2
    rw [largePrimeTupleProduct,norm_mul_eq] at hprod
    have hm : X^(69/200:ℝ)*norm (q.2 b) ≤ 3*X :=
      (mul_le_mul_of_nonneg_right hnr (norm_nonneg _)).trans
        ((mul_le_mul_of_nonneg_left hnb (norm_nonneg _)).trans hprod)
    have he : X^(69/200:ℝ)*(3*X^(131/200:ℝ)) = 3*X := by
      rw [mul_left_comm,←Real.rpow_add hXp]
      rw [show (69/200:ℝ)+(131/200)=1 by ring,Real.rpow_one]
    change norm (q.2 b) ≤ _
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp (69/200:ℝ))).mp
    simpa only [mul_comm] using hm.trans_eq he.symm


lemma tailPrimeTupleOrdinary_exponents {i j N : ℕ} {ℓ : ℤ} {ξ H U X : ℝ}
    (hX : 1 ≤ X) (hlog : 1000 ≤ Real.log X) (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0)
    (a : Fin i ⊕ Fin j) :
    0 < largePrimeTupleExponent q a ∧ largePrimeTupleExponent q a ≤ 2/3 := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have ht := (mul_ne_zero_iff.mp hne).1
  have hn := tailPrimeTupleTerm_product_range hXp ht
  have hnp : 0 < norm (largePrimeTupleProduct q) := (by positivity : (0:ℝ) < X/2).trans_le hn.1
  have hlo := Real.log_le_log (by positivity : (0:ℝ) < X/2) hn.1
  rw [Real.log_div hXp.ne' (by norm_num)] at hlo
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have hl3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
  have hln : 0 < Real.log (norm (largePrimeTupleProduct q)) := by linarith
  have hr := Real.log_le_log (Real.rpow_pos_of_pos hXp ξ)
    (tailPrimeTupleNorm_rough hX hξz hq ht a).le
  rw [Real.log_rpow hXp] at hr
  have hu := Real.log_le_log (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1)
    (tailPrimeTupleOrdinary_upper hX hξz k hhigh hq hne a)
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hXp (131/200:ℝ)).ne',Real.log_rpow hXp] at hu
  unfold largePrimeTupleExponent
  exact ⟨div_pos (lt_of_lt_of_le (mul_pos hξ (by linarith)) hr) hln,
    (div_le_iff₀ hln).mpr (by linarith)⟩

theorem tailPrimeTupleOrdinary_group {i j N : ℕ} {ℓ : ℤ} {ξ H U X : ℝ}
    (hX : 1 ≤ X) (hlog : 1000 ≤ Real.log X) (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0) :
    ∃ s : Finset (Fin i ⊕ Fin j),
      ((1/2:ℝ)^(1/3:ℝ)/2^(i+j))*X^(1/3:ℝ) ≤
        largeTupleSubsetScale (fun a => (k a).val) s ∧
      (largeTupleSubsetScale (fun a => (k a).val) s)^2 ≤ 3*X := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hn := tailPrimeTupleTerm_product_range hXp (mul_ne_zero_iff.mp hne).1
  have hnp : 0 < norm (largePrimeTupleProduct q) := (by positivity : (0:ℝ) < X/2).trans_le hn.1
  have hln : 0 < Real.log (norm (largePrimeTupleProduct q)) := by
    have hh := Real.log_le_log (by positivity : (0:ℝ) < X/2) hn.1
    rw [Real.log_div hXp.ne' (by norm_num)] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  obtain ⟨s,_hs,hlo,hhi⟩ := prime_exponent_short_group Finset.univ
    (largePrimeTupleExponent q) (by norm_num : (0:ℝ) < 1/3) le_rfl
    (fun a _ => by
      have hh := tailPrimeTupleOrdinary_exponents hX hlog hξ hξz k hhigh hq hne a
      exact ⟨hh.1,by linarith [hh.2]⟩)
    (largePrimeTupleExponent_sum hq hln.ne')
  obtain ⟨hl,hu⟩ := largePrimeTuplePiece_group_scale k hq (mul_ne_zero_iff.mp hne).2 hnp hln s hlo hhi
  refine ⟨s,?_,?_⟩
  · have hcard : s.card ≤ i+j := by
      simpa only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] using s.card_le_univ
    calc
      _ = (X/2)^(1/3:ℝ)/2^(i+j) := by
        rw [show X/2 = (1/2:ℝ)*X by ring,Real.mul_rpow (by norm_num) hXp.le]
        ring
      _ ≤ norm (largePrimeTupleProduct q)^(1/3:ℝ)/2^(i+j) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hn.1 (by norm_num)) (by positivity)
      _ ≤ norm (largePrimeTupleProduct q)^(1/3:ℝ)/2^s.card :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_right₀ (by norm_num) hcard)
      _ ≤ _ := hl
  · have hh := pow_le_pow_left₀ (largeTupleSubsetScale_pos _ _).le hu 2
    have he : (norm (largePrimeTupleProduct q)^(1/2:ℝ))^2 = norm (largePrimeTupleProduct q) := by
      rw [←Real.rpow_mul_natCast hnp.le]
      norm_num
    exact hh.trans (by rw [he]; exact hn.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeOrdinaryBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary-height prefix on an actual group. Small groups use the
logarithmic localization bound on two aligned full tails. Larger groups
use the published Hecke estimate on each retained window. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem tailPrime_ordinary_group_prefix {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (hpnt : PrimaryPrimePNT) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (n : ℕ) :
    ∃ (Ct : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ), z.1.1 = X →
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      ((1/2:ℝ)^(1/3:ℝ)/2^(i+j))*X^(1/3:ℝ) ≤ B → B^2 ≤ 3*X →
      X/(2*2^(i+j)) ≤ A*B → A*B ≤ 3*X →
      (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      (1+Real.log X)^Ct ≤ T → 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      ‖∑ v ∈ Finset.range (heightWindowCount H T),
        if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then
          productGaussWindow (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
            (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
            (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
            (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s)
            0 primeProductEnvelope H (T*(3/2:ℝ)^v) z.1.1 else 0‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨K₁,m₁,hK₁,hb₁⟩ := tailPrime_low_group s hHuxley hMV hC hpnt n 1
  obtain ⟨η,G,K₂,B₂,m₂,hη,_hηone,hK₂,hb₂⟩ :=
    tailPrime_hecke_window s hpub hHuxley hperiod hMV hC hξ hξz hGI hGQ (n+1)
  obtain ⟨D₀,hD₀,hcount⟩ := heightWindowCount_log_bound
  let c : ℝ := (1/2:ℝ)^(1/3:ℝ)/2^(i+j)
  let D : ℝ := 2*2^(i+j)
  let W : ℝ := 2*(2:ℝ)^s.card
  let Q : ℝ := (2:ℝ)^(Fintype.card {x : Fin i ⊕ Fin j // x ∉ s})
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hW : 1 ≤ W := by dsimp [W]; have := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := s.card); linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let Ct := max (m₁+1) (m₂+1)
  let L₁ := K₁*3^(5/6:ℝ)/(1/4:ℝ)^n
  let L₂ := K₂*3^(5/6:ℝ)/(1/4:ℝ)^(n+1)
  refine ⟨Ct,2*L₁+D₀*L₂,by dsimp [L₁,L₂]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (Real.tendsto_log_atTop.eventually_ge_atTop 0),
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul_atTop hc).eventually_ge_atTop
      (max ((65536:ℝ)^2) B₂),
    eventually_rpow_le_const_mul (show (1/3-3*(1/1000):ℝ) < 1/3 by norm_num) hc,
    eventually_tailPrime_small_localized_length hD (show 0 < 4*W^(3/2:ℝ) by positivity),
    eventually_tailPrime_small_low_upper hc hQ,
    eventually_tailPrime_small_high_upper (by norm_num : (0:ℝ) < 1/1000)
      (by norm_num : (1/1000:ℝ) < 1/12) (by norm_num : (0:ℝ) < 1)
      (by norm_num : (1:ℝ) < (1/3-3*(1/1000))*(3+1)),
    eventually_tailPrime_fixed_width_log hW m₁,
    eventually_tailPrime_fixed_width_log (by norm_num : (1:ℝ) ≤ 1) m₂,
    eventually_prime_box_range (show (0:ℝ) < 39/100-1/3 by norm_num) hη (i+j) G]
    with X hX hlog hlarge hpower hlocal hlow hcube hlog₁ hlog₂ hbox
  intro z H T hz
  dsimp only
  intro hBlo hBsq hABlo hABhi hrough hT hH hHX
  let B := largeTupleGroupLength s z
  let A := largeTupleGroupLength (Finset.univ\s) z
  have hBp : 0 < B := zero_lt_one.trans_le (largeTupleGroupLength_one s z)
  have hAp : 0 < A := zero_lt_one.trans_le (largeTupleGroupLength_one _ z)
  have hLX : 1 ≤ 1+Real.log X := by linarith
  have hBpower : X^(1/3-3*(1/1000):ℝ) ≤ B := hpower.trans hBlo
  have hquarter : X^(1/4:ℝ) ≤ B :=
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1/4:ℝ) ≤ 1/3-3*(1/1000))).trans hBpower
  have hBsmall : (65536:ℝ)^2 ≤ B := (le_max_left _ _).trans (hlarge.trans hBlo)
  have hB₂ : B₂ ≤ B := (le_max_right _ _).trans (hlarge.trans hBlo)
  have hBX : B ≤ 3*X := by nlinarith [largeTupleGroupLength_one s z]
  have hA3 : A ≤ B^3 := by
    have hh := hcube A B hBpower hABhi
    rw [one_mul,show (2+(1:ℝ)) = ((3:ℕ):ℝ) by norm_num,Real.rpow_natCast] at hh
    exact hh
  have hHcube : H ≤ B^3 := hHX.trans (tailPrime_height_cube hX (by norm_num) hquarter)
  have hTp : 0 < T := (pow_pos (by linarith : 0 < 1+Real.log X) Ct).trans_le hT
  have hT1 : 1 ≤ T := (one_le_pow₀ hLX).trans hT
  have hTlow : (1+Real.log (W*B))^m₁ ≤ T :=
    (hlog₁ B (largeTupleGroupLength_one s z) hBX).trans
      ((pow_le_pow_right₀ hLX (le_max_left _ _)).trans hT)
  have hThecke : (1+Real.log B)^m₂ ≤ T := by
    have ht := hlog₂ B (largeTupleGroupLength_one s z) hBX
    simp only [one_mul] at ht
    exact ht.trans ((pow_le_pow_right₀ hLX (le_max_right _ _)).trans hT)
  let f := fun U => productGaussWindow (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
    (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
    (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
    (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s) 0 primeProductEnvelope H U z.1.1
  have htail (U : ℝ) : (∑ v ∈ Finset.range (heightWindowCount H U), f (U*(3/2:ℝ)^v)) =
      envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
        (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s) primeProductEnvelope H U z.1.1 := by
    unfold f productGaussWindow envelopeCutoffBilinearTail
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [productGaussHeightWindowKernel,theta_zero,one_mul]
    ring
  by_cases hs : B ≤ X^(39/100:ℝ)
  · have hAlow : 4*(W*B)^(3/2:ℝ) ≤ A := by
      rw [Real.mul_rpow (zero_le_one.trans hW) hBp.le]
      simpa only [mul_assoc] using hlocal A B hBp hABlo hs
    have hAupper : Q*A ≤ B^2*(1+Real.log B)^(3*1) := by
      simpa only [Nat.mul_one] using hlow A B hBlo hABhi
    have hb (U : ℝ) (hU : T ≤ U) :
        ‖∑ v ∈ Finset.range (heightWindowCount H U), f (U*(3/2:ℝ)^v)‖ ≤
          L₁*X^(5/6:ℝ)/(1+Real.log X)^n := by
      rw [htail]
      exact (hb₁ z H U hBsmall hAlow hAupper hA3 (hTlow.trans hU) hH hHcube).trans
        (triple_bilinear_nat_scale hX hAp.le hquarter hK₁.le hABhi n)
    obtain ⟨v,_hv,he⟩ := geometricHeight_filtered_prefix f
      (zero_lt_one.trans_le hH) hTp (X^(1/100:ℝ))
    change ‖∑ v ∈ Finset.range (heightWindowCount H T), if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then f (T*(3/2:ℝ)^v) else 0‖ ≤ _
    rw [he]
    have hshift : T ≤ T*(3/2:ℝ)^v := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3/2)) hTp.le
    apply (norm_sub_le _ _).trans
    apply (add_le_add (hb T le_rfl) (hb _ hshift)).trans
    have hpos : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^n := by positivity
    have hc : 2*L₁ ≤ 2*L₁+D₀*L₂ := by
      have hh : 0 ≤ D₀*L₂ := by dsimp [L₂]; positivity
      linarith
    first | (convert mul_le_mul_of_nonneg_right hc hpos using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_right hc hpos).trans (le_of_eq (by ring)))
  · have hbig : X^(39/100:ℝ) ≤ B := le_of_lt (lt_of_not_ge hs)
    have hrange := hbox A B hABlo hABhi hBsq (by
      simpa only [show (1/3+(39/100-1/3):ℝ) = 39/100 by ring] using hbig)
    have hwin (v : ℕ) :
        ‖if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then f (T*(3/2:ℝ)^v) else 0‖ ≤
          L₂*X^(5/6:ℝ)/(1+Real.log X)^(n+1) := by
      split_ifs with hu
      · have ht : T ≤ T*(3/2:ℝ)^v := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3/2)) hTp.le
        have hub : T*(3/2:ℝ)^v ≤ B^(7/20:ℝ) := hu.trans
          ((Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1/100:ℝ) ≤ (39/100)*(7/20))).trans (by
            rw [Real.rpow_mul (zero_le_one.trans hX)]
            exact Real.rpow_le_rpow (by positivity) hbig (by norm_num)))
        exact (hb₂ z H _ hB₂ hrough hrange.1 hrange.2 (hThecke.trans ht)
          (zero_lt_one.trans_le hH) hub).trans
          (triple_bilinear_nat_scale hX hAp.le hquarter hK₂.le hABhi (n+1))
      · rw [norm_zero]
        dsimp [L₂]
        positivity
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun v _ => hwin v)).trans
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    have hHX1 : H ≤ X := hHX.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
        (show (1/6+1/3000:ℝ) ≤ 1 by norm_num))
    have hN : (heightWindowCount H T:ℝ) ≤ D₀*(1+Real.log X) :=
      (hcount H T hH hT1).trans (mul_le_mul_of_nonneg_left
        (by linarith [Real.log_le_log (zero_lt_one.trans_le hH) hHX1]) hD₀.le)
    apply (mul_le_mul_of_nonneg_right hN (by dsimp [L₂]; positivity)).trans
    have he : D₀*(1+Real.log X)*(L₂*X^(5/6:ℝ)/(1+Real.log X)^(n+1)) =
        (D₀*L₂)*X^(5/6:ℝ)/(1+Real.log X)^n := by
      rw [pow_succ]
      field_simp
    rw [he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hh : 0 ≤ L₁ := by dsimp [L₁]; positivity
    linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeOrdinaryTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A surviving ordinary prefix fixes independent prime groups. Constants
and logarithmic thresholds are uniform over the finite choices of group. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma tailPrimeTupleRegrouped_window (i j : ℕ) (ℓ : ℤ) (ξ H U X : ℝ)
    (d : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :
    tailPrimeTupleRegrouped i j ℓ ξ H U X d s =
      productGaussWindow (largeTupleSelectedSupport ξ X d s)
        (largeTupleOtherSupport ξ X d s) (largeTupleSelectedCoefficient ξ X d s)
        (largeTupleOtherCoefficient ξ X d s) ℓ primeProductEnvelope H U X := rfl

theorem tailPrime_ordinary_tuple_bound (i j : ℕ)
    (hpnt : PrimaryPrimePNT) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (n : ℕ) :
    ∃ (Ct : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ H T : ℝ, (1+Real.log X)^Ct ≤ T → 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      ∀ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) →
      ‖tailPrimeOrdinaryTuple i j ξ H T X d‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  have hdata (s : Finset (Fin i ⊕ Fin j)) := tailPrime_ordinary_group_prefix s hpnt hpub
    hHuxley hperiod hMV hC hξ hξz hGI hGQ n
  choose Ct K hK hb using hdata
  have hall := (Filter.eventually_all).mpr hb
  let Ct₀ := Finset.univ.sup Ct
  let M : ℝ := 1+∑ s, |K s|
  let c : ℂ := (i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨Ct₀,(‖c‖+1)*M,by positivity,?_⟩
  filter_upwards [hall,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1000,
    eventually_tailPrimeTuple_coordinate_envelope (i := i) (j := j)
      (κ := 0) (by norm_num) (by norm_num) hξz,
    tailPrimeTuplePiece_rough_scales i j hξ hξz] with X hbound hX hlog hcoord hrough
  intro H T hT hH hHX d hhigh
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 < 1+Real.log X := by linarith
  by_cases hz : tailPrimeOrdinaryTuple i j ξ H T X d = 0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨v,_hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hpne : tailPrimeTuplePiece i j 0 ξ H (T*(3/2:ℝ)^v) X d ≠ 0 := by
    intro hn
    apply hvn
    simp only [hn,ite_self]
  obtain ⟨q,hq,hqn⟩ := tailPrimeTuplePiece_witness d hpne
  obtain ⟨s,hBlo,hBsq⟩ := tailPrimeTupleOrdinary_group hX hlog hξ hξz d hhigh hq hqn
  have hp := tailPrimeTuple_scale_product hXp d hqn
  have hr := hrough 0 H (T*(3/2:ℝ)^v) d q hq hqn
  have hprod : largeTupleSubsetScale (fun a => (d a).val) (Finset.univ\s)*
      largeTupleSubsetScale (fun a => (d a).val) s =
      largeTupleSubsetScale (fun a => (d a).val) Finset.univ := by
    rw [mul_comm,largeTupleSubsetScale_complement]
  have hB3 : largeTupleSubsetScale (fun a => (d a).val) s ≤ 3*X := by
    have hpos := largeTupleSubsetScale_pos (fun a => (d a).val) s
    nlinarith
  have hhigh' : X^(1/3-2*(0:ℝ)) ≤ largeTupleDistinguishedScale (fun a => (d a).val) :=
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1/3-2*(0:ℝ)) ≤ 69/200)).trans hhigh
  have hcoords := hcoord 0 H (T*(3/2:ℝ)^v) d hhigh' q hq hqn
  let z : largeTupleBoxIndex i j := ⟨(⟨X,hXp⟩,fun a => (d a).val),hr.1⟩
  have hTs : (1+Real.log X)^(Ct s) ≤ T :=
    (pow_le_pow_right₀ (by linarith : 1 ≤ 1+Real.log X)
      (Finset.le_sup (f := Ct) (Finset.mem_univ s))).trans hT
  have hprefix := hbound s z H T rfl hBlo hBsq
    (by change X/(2*2^(i+j)) ≤ largeTupleSubsetScale (fun a => (d a).val) (Finset.univ\s)*largeTupleSubsetScale (fun a => (d a).val) s
        rw [hprod]; exact hp.1)
    (by change largeTupleSubsetScale (fun a => (d a).val) (Finset.univ\s)*largeTupleSubsetScale (fun a => (d a).val) s ≤ 3*X
        rw [hprod]; exact hp.2)
    (fun a => hr.2 _ (largeTupleSubsetScale_pos _ _).le hB3 a) hTs hH hHX
  have he : tailPrimeOrdinaryTuple i j ξ H T X d =
      c*(∑ v ∈ Finset.range (heightWindowCount H T),
        if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then
          productGaussWindow (largeTupleSelectedSupport ξ X (fun a => (d a).val) s)
            (largeTupleOtherSupport ξ X (fun a => (d a).val) s)
            (largeTupleSelectedCoefficient ξ X (fun a => (d a).val) s)
            (largeTupleOtherCoefficient ξ X (fun a => (d a).val) s)
            0 primeProductEnvelope H (T*(3/2:ℝ)^v) X else 0) := by
    unfold tailPrimeOrdinaryTuple
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : T*(3/2:ℝ)^w ≤ X^(1/100:ℝ)
    · simp only [hw,ite_true, if_true,tailPrimeTuplePiece_full i j 0 ξ H _ X d hcoords,
        tailPrimeTupleIndependent_regroup i j 0 ξ H _ X _ s,tailPrimeTupleRegrouped_window]
      rfl
    · simp only [hw,ite_false, if_false,mul_zero]
  rw [he,norm_mul]
  apply (mul_le_mul_of_nonneg_left hprefix (_root_.norm_nonneg c)).trans
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailHighOrdinaryNegligible
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full ordinary high-scale contribution, including the finite arity
expansion and all smooth norm partitions. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem tailHighOrdinaryArity_collection {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (H T : ℝ),
      tailHighOrdinaryArity i ξ H T X =
        ∑ j ∈ Finset.range m, tailPrimeOrdinaryTupleSum i j ξ H T X := by
  obtain ⟨m,hm⟩ := tailHighScaleRows_arity hξ
  refine ⟨m,?_⟩
  filter_upwards [hm] with X hr
  intro i H T
  unfold tailHighOrdinaryArity
  simp_rw [hr i 0 H]
  calc
    _ = ∑ v ∈ Finset.range (heightWindowCount H T), ∑ j ∈ Finset.range m,
        ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
          if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then
            if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
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
      unfold tailPrimeOrdinaryTupleSum
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val)
      · simp only [hd,ite_true, if_true,tailPrimeOrdinaryTuple]
      · simp only [hd,ite_false, if_false,ite_self,Finset.sum_const_zero]

theorem tailHighOrdinaryArity_isLittleO_oai (i : ℕ)
    (hpnt : PrimaryPrimePNT) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ Ct : ℕ, ∀ H T : ℝ → ℝ,
      (∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X) →
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
      (∀ᶠ X : ℝ in atTop, H X ≤ X^(1/6+1/3000:ℝ)) →
      (fun X => tailHighOrdinaryArity i ξ (H X) (T X) X) =o[atTop] firstMomentScale := by
  obtain ⟨m,hm⟩ := tailHighOrdinaryArity_collection hξ
  have hdata (j : Fin m) := tailPrime_ordinary_tuple_bound i j hpnt hpub hHuxley hperiod
    hMV hC hξ hξz hGI hGQ (3+(i+j))
  choose Ct K hK hb using hdata
  let Ct₀ := Finset.univ.sup Ct
  refine ⟨Ct₀,?_⟩
  intro H T hT hH hHX
  have hpart (j : Fin m) :
      (fun X => tailPrimeOrdinaryTupleSum i j ξ (H X) (T X) X) =o[atTop] firstMomentScale := by
    obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i j
    apply Asymptotics.IsBigO.trans_isLittleO
      (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
    apply Asymptotics.IsBigO.of_bound (D*K j)
    filter_upwards [hb j,hT,hH,hHX,eventually_ge_atTop (1:ℝ)] with X hb ht hh hx hX
    have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
    have ht' : (1+Real.log X)^(Ct j) ≤ T X :=
      (pow_le_pow_right₀ (by linarith [Real.log_nonneg hX])
        (Finset.le_sup (f := Ct) (Finset.mem_univ j))).trans ht
    have hKj : 0 < K j := hK j
    have hB : 0 ≤ K j*X^(5/6:ℝ)/(1+Real.log X)^(3+(i+j)) := by positivity
    have hp (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
        ‖if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
          tailPrimeOrdinaryTuple i j ξ (H X) (T X) X d else 0‖ ≤
          K j*X^(5/6:ℝ)/(1+Real.log X)^(3+(i+j)) := by
      split_ifs with hd
      · exact hb (H X) (T X) ht' hh hx d hd
      · simpa only [norm_zero] using hB
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
    unfold tailPrimeOrdinaryTupleSum
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun d _ => hp d)).trans
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right (hcount X hX) hB).trans_eq
    rw [pow_add]
    field_simp [hL.ne']
    ring
  have hs := Asymptotics.IsLittleO.fun_sum (s := Finset.univ) (fun j _ => hpart j)
  apply hs.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hm] with X hx
  rw [Fin.sum_univ_eq_sum_range (fun j => tailPrimeOrdinaryTupleSum i j ξ (H X) (T X) X)]
  exact (hx i (H X) (T X)).symm

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.tailHighOrdinaryArity_isLittleO_oai := @OAI.CubicFirstMoment.tailHighOrdinaryArity_isLittleO_oai
