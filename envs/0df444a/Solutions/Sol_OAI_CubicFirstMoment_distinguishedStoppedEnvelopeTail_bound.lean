-- Prove2me | solution 1 for OAI.CubicFirstMoment.distinguishedStoppedEnvelopeTail_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:34:40.673225+00:00
-- url     : https://prove2.me/submissions/d4f47651-edbe-462b-badf-91f078822d41

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_low_localized_height_integral_bound

section
-- module Solutions.OAIQ096_CM.Compat
attribute [-instance] _root_.instMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PrimaryNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeJoin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collecting the squarefree majorant by least common multiples

The join is the product of the union of the primary prime factors. Its
square divides an element exactly when both input squares divide it.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_le_of_dvd_nonzero {a b : Eisenstein} (hb : b ≠ 0) (h : a ∣ b) : norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := h
  have hc : c ≠ 0 := by intro h; apply hb; rw [h,mul_zero]
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_norm hc)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveMobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Möbius coefficient below the sieve truncation

The union convolution of the squarefree Möbius weights is the same
Möbius weight. This proves the exact low-divisor coefficient identity,
which is stronger than a divisor bound and is needed in the residue.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_product_squarefree (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) : Squarefree (∏ p ∈ U, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact isRelPrime_iff_isCoprime.mpr (primaryPrimes_isCoprime (hU p hp) (hU q hq) hpq)
  · intro p hp
    exact (hU p hp).2.squarefree

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primaryFactorRemainder_spec {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n) :
    primary (primaryFactorRemainder n s) ∧ Squarefree (primaryFactorRemainder n s) ∧
      (∏ p ∈ s, p)*primaryFactorRemainder n s = n := by
  have hp : ∀ p ∈ primaryPrimeFactors n \ s, primaryPrime p :=
    fun p h => (primaryPrimeFactor_spec hn (Finset.mem_sdiff.mp h).1).1
  refine ⟨primary_finset_prod _ _ (fun p h => (hp p h).1),
    primaryPrime_product_squarefree _ hp,?_⟩
  rw [primaryFactorRemainder,mul_comm,Finset.prod_sdiff hsub,primaryPrimeFactors_prod hn hs]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal independent coefficients from the stopping construction.
The selected-side test may contain the first-stage failure and crossing
conditions; the remaining-side test is a separate condition on its divisor.
No coprimality condition is inserted between the two sides. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPairFiber_card_le (S T : Finset Eisenstein)
    (hS : ∀ r ∈ S, primary r) (b : Eisenstein) :
    (primaryPairFiber S T b).card ≤ (S.filter (fun r => r ∣ b)).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    have hm := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨hm.1,⟨p.2,(Finset.mem_filter.mp hp).2.symm⟩⟩
  · intro p hp q hq he
    apply Prod.ext he
    have hmul : p.1*p.2 = p.1*q.2 := by
      calc
        _ = b := (Finset.mem_filter.mp hp).2
        _ = q.1*q.2 := (Finset.mem_filter.mp hq).2.symm
        _ = _ := by rw [he]
    exact mul_left_cancel₀ (primary_ne_zero
      (hS p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)) hmul

lemma primaryPairCoefficient_norm_le (S T : Finset Eisenstein)
    (hS : ∀ r ∈ S, primary r) (b : Eisenstein)
    (w : Eisenstein × Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ p ∈ primaryPairFiber S T b, ‖w p‖ ≤ M) :
    ‖primaryPairCoefficient S T w b‖ ≤ ((S.filter (fun r => r ∣ b)).card:ℝ)*M := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hw).trans
  rw [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (primaryPairFiber_card_le S T hS b)) hM

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficientBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise bounds for the actual stopped coefficients, before any
analytic sequence estimate. The divisor count is literal and introduces
no dependence on the number or width of prime bins. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_norm_le_one {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w : ℝ) (d : Eisenstein) :
    ‖cutoffMoebius ψ w d‖ ≤ 1 := by
  rw [cutoffMoebius,norm_mul,norm_prod]
  have hp : (∏ p ∈ primaryPrimeFactors d, ‖(ψ (norm p/w):ℂ)‖) ≤ 1 := by
    apply Finset.prod_le_one (fun _ _ => _root_.norm_nonneg _)
    intro p hp
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hψ _).1] using (hψ (norm p/w)).2
  exact (mul_le_mul (norm_idealMoebius_le_one d) hp
    (Finset.prod_nonneg (fun _ _ => _root_.norm_nonneg _)) zero_le_one).trans_eq (one_mul 1)

theorem stoppedAlpha_divisor_bound (E U : Finset Eisenstein)
    (hE : ∀ e ∈ E, primary e) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w : ℝ)
    (remaining : Eisenstein → Prop) (a : Eisenstein) :
    ‖stoppedAlpha E U ψ w remaining a‖ ≤ ((E.filter (fun e => e ∣ a)).card:ℝ) := by
  apply (primaryPairCoefficient_norm_le E U hE a _ zero_le_one _).trans_eq (mul_one _)
  intro p hp
  by_cases he : remaining p.1
  · simpa only [ite_eq_left he] using cutoffMoebius_norm_le_one hψ w p.1
  · simp only [ite_eq_right he,norm_zero,zero_le_one]

theorem stoppedBeta_divisor_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w : ℝ)
    (selected : Eisenstein → Eisenstein → Prop) (v : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ r ∈ R, ‖v r‖ ≤ M) (b : Eisenstein) :
    ‖stoppedBeta R D v ψ w selected b‖ ≤ ((R.filter (fun r => r ∣ b)).card:ℝ)*M := by
  apply primaryPairCoefficient_norm_le R D hR b _ hM
  intro p hp
  by_cases hs : selected p.1 p.2
  · simp only [ite_eq_left hs,norm_mul]
    exact (mul_le_mul_of_nonneg_left (cutoffMoebius_norm_le_one hψ w p.2)
      (_root_.norm_nonneg _)).trans ((mul_one _).le.trans
        (hv p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1))
  · simpa only [ite_eq_right hs,norm_zero] using hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished-tuple weight occurring in stopped coefficients.
Its multiplicity is bounded in terms of the fixed tuple length, so the
literal beta coefficient has one divisor-count loss independently of bins. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma distinguishedPrimeWeight_norm_le_one {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w z : ℝ) (p : Eisenstein) :
    ‖distinguishedPrimeWeight ψ w z p‖ ≤ 1 := by
  rw [distinguishedPrimeWeight,Complex.norm_real,Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [(hψ (norm p/w)).1,(hψ (norm p/w)).2,
    (hψ (norm p/z)).1,(hψ (norm p/z)).2]

theorem distinguishedTupleCoefficient_norm (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (W : ι → Eisenstein → ℂ)
    (hW : ∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w z : ℝ) (r : Eisenstein) :
    ‖distinguishedTupleCoefficient S W ψ w z r‖ ≤
      ‖((Fintype.card ι).factorial:ℂ)⁻¹‖ *
        ((Fintype.card ι)^(Fintype.card ι):ℕ) := by
  unfold distinguishedTupleCoefficient
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
  have hp (i : ι) (p : Eisenstein) (hp : p ∈ S i) :
      ‖W i p*distinguishedPrimeWeight ψ w z p‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hW i p hp) (distinguishedPrimeWeight_norm_le_one hψ w z p)
      (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  simpa only [Finset.prod_const_one,mul_one] using
    orderedConvolution_norm_bound S (fun i p => W i p*distinguishedPrimeWeight ψ w z p)
      (fun _ => 1) hS (fun _ => zero_le_one) hp r

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughDivisorBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished divisor is rough at a fixed power scale. On a
squarefree product this gives a uniform number of possible distinguished
divisors, stronger than the generic divisor bound for stopped beta. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem rough_primary_divisor_card (R : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {b : Eisenstein} (hb : primary b) (hs : Squarefree b)
    {w : ℝ} (hw : 1 ≤ w) (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    {k : ℕ} (hsize : norm b < w^k) :
    (R.filter (fun r => r ∣ b)).card ≤ 2^k := by
  let T := R.filter (fun r => r ∣ b)
  let L := (primaryPrimeFactors b).filter (fun p => w ≤ norm p)
  have hS (r : Eisenstein) (hr : r ∈ T) : Squarefree r :=
    fun x hx => hs x (hx.trans (Finset.mem_filter.mp hr).2)
  have hL : L.card < k := primary_factor_subset_card_lt hb hs
    (Finset.filter_subset _ _) hw (fun p hp => (Finset.mem_filter.mp hp).2) hsize
  have hcard : T.card ≤ L.powerset.card := by
    apply Finset.card_le_card_of_injOn primaryPrimeFactors
    · intro r hr
      apply Finset.mem_powerset.mpr
      intro p hp
      have hp' := primaryPrimeFactor_spec (hR r (Finset.mem_filter.mp hr).1) hp
      exact Finset.mem_filter.mpr ⟨primaryPrime_mem_factors hb hp'.1
        (hp'.2.trans (Finset.mem_filter.mp hr).2),hrough r (Finset.mem_filter.mp hr).1 p hp⟩
    · intro r hr q hq he
      calc
        r = ∏ p ∈ primaryPrimeFactors r, p :=
          (primaryPrimeFactors_prod (hR r (Finset.mem_filter.mp hr).1) (hS r hr)).symm
        _ = ∏ p ∈ primaryPrimeFactors q, p := by rw [he]
        _ = q := primaryPrimeFactors_prod (hR q (Finset.mem_filter.mp hq).1) (hS q hq)
  exact hcard.trans (by rw [Finset.card_powerset]; exact Nat.pow_le_pow_right (by decide) hL.le)

theorem stoppedBeta_rough_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (w : ℝ) (hw : 1 ≤ w) (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    (selected : Eisenstein → Eisenstein → Prop) (v : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ r ∈ R, ‖v r‖ ≤ M)
    {b : Eisenstein} (hb : primary b) (hs : Squarefree b) {k : ℕ} (hsize : norm b < w^k) :
    ‖stoppedBeta R D v ψ w selected b‖ ≤ (2^k:ℕ)*M := by
  apply (stoppedBeta_divisor_bound R D hR hψ w selected v hM hv b).trans
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
    (rough_primary_divisor_card R hR hb hs hw hrough hsize)) hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedRoughness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The roughness of the actual distinguished coefficient, followed by
a uniform bound for the stopped beta. Zero distinguished coefficients
are removed before counting divisors, so no support hypothesis is added. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem distinguishedTupleCoefficient_prime_support
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) {ψ : ℝ → ℝ}
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 0 < w) (hwz : w ≤ z) {r p : Eisenstein}
    (hr : distinguishedTupleCoefficient S W ψ w z r ≠ 0)
    (hp : primaryPrime p) (hpr : p ∣ r) : w < norm p ∧ norm p < 2*z := by
  have ho : orderedConvolution S (fun i q => W i q*distinguishedPrimeWeight ψ w z q) r ≠ 0 :=
    (mul_ne_zero_iff.mp hr).2
  obtain ⟨f,hf,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ho
  obtain ⟨hfs,hfr⟩ := Finset.mem_filter.mp hf
  have hd : p ∣ ∏ i, f i := by rw [hfr]; exact hpr
  obtain ⟨i,_,hpi⟩ := (hp.2.dvd_finsetProd_iff f).mp hd
  have hfi := hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)
  have he : p = f i := primary_associated_eq hp.1 hfi.1
    ((hp.2.dvd_prime_iff_associated hfi.2).mp hpi)
  have hweight := (mul_ne_zero_iff.mp
    ((Finset.prod_ne_zero_iff.mp hterm) i (Finset.mem_univ i))).2
  rw [he]
  exact distinguishedPrimeWeight_support hψone hψzero hw hwz
    (zero_lt_one.trans_le (one_le_norm hfi.2.ne_zero)) hweight

lemma stoppedBeta_filter_nonzero (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected : Eisenstein → Eisenstein → Prop) (b : Eisenstein) :
    stoppedBeta (R.filter (fun r => v r ≠ 0)) D v ψ w selected b =
      stoppedBeta R D v ψ w selected b := by
  unfold stoppedBeta primaryPairCoefficient
  apply Finset.sum_subset
  · intro q hq
    obtain ⟨hq,hprod⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqr,hqd⟩ := Finset.mem_product.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hqr).1,hqd⟩,hprod⟩
  · intro q hq hn
    obtain ⟨hq,hprod⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqr,hqd⟩ := Finset.mem_product.mp hq
    have hz : v q.1 = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hqr,h⟩,hqd⟩,hprod⟩)
    simp [hz]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeBinGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform norm distortion for the multiplicative bin surrogate.
The bin ratio is fixed before the norm parameter; all selected subsets
simultaneously satisfy the manuscript's small-power distortion bound. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_norm_ge_two {p : Eisenstein} (hp : primaryPrime p) : 2 ≤ norm p := by
  have hz := normNat_ne_zero hp.2.ne_zero
  have ho : normNat p ≠ 1 := by
    intro h
    apply hp.2.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [←normNat_cast,h]
    norm_num
  have h : 2 ≤ normNat p := by omega
  rw [←normNat_cast]
  exact_mod_cast h

lemma primary_prime_subset_norm_le {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n) :
    norm (∏ p ∈ s, p) ≤ norm n := by
  have he := (primaryFactorRemainder_spec hn hs hsub).2.2
  exact norm_le_of_dvd_nonzero (primary_ne_zero hn) ⟨primaryFactorRemainder n s,he.symm⟩

lemma primary_prime_subset_two_pow_le {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n) :
    (2:ℝ)^s.card ≤ norm n := by
  calc
    _ = ∏ _p ∈ s, (2:ℝ) := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ s, norm p := Finset.prod_le_prod (fun _ _ => by norm_num)
      (fun p hp => primaryPrime_norm_ge_two (primaryPrimeFactor_spec hn (hsub hp)).1)
    _ = norm (∏ p ∈ s, p) := (norm_finset_prod _ _).symm
    _ ≤ norm n := primary_prime_subset_norm_le hn hs hsub

lemma primeSurrogate_norm_bounds (s : Finset Eisenstein) (b : Eisenstein → ℕ)
    (ell : ℕ → ℝ) {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (hcell : ∀ p ∈ s, 0 ≤ ell (b p) ∧ ell (b p) ≤ norm p ∧ norm p ≤ ρ*ell (b p)) :
    primeSurrogate s b ell ≤ norm (∏ p ∈ s, p) ∧
      norm (∏ p ∈ s, p) ≤ ρ^s.card*primeSurrogate s b ell := by
  rw [norm_finset_prod]
  constructor
  · exact Finset.prod_le_prod (fun p hp => (hcell p hp).1) (fun p hp => (hcell p hp).2.1)
  · calc
      _ ≤ ∏ p ∈ s, ρ*ell (b p) :=
        Finset.prod_le_prod (fun p _ => norm_nonneg p) (fun p hp => (hcell p hp).2.2)
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]; rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GeometricPrimeBins
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete descending geometric binning of the actual prime norms.
The number of bins is logarithmic and all lower endpoints exceed one,
so the exact first-crossing construction applies without empty-bin cases. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma geometricPrimeBin_cell {ρ B : ℝ} (hρ : 1 < ρ) (_hρ₂ : ρ ≤ 2)
    {p : Eisenstein} (hp : primaryPrime p) (hpB : norm p ≤ B) :
    geometricBinLower ρ B (geometricPrimeBin ρ B p) ≤ norm p ∧
      norm p < ρ*geometricBinLower ρ B (geometricPrimeBin ρ B p) := by
  have hr := Real.log_pos hρ
  have hpn : 0 < norm p := by linarith [primaryPrime_norm_ge_two hp]
  have hl : 0 ≤ Real.log (norm p)/Real.log ρ :=
    div_nonneg (Real.log_nonneg (by linarith [primaryPrime_norm_ge_two hp])) hr.le
  have hkM : ⌊Real.log (norm p)/Real.log ρ⌋₊ ≤ geometricBinCount ρ B := by
    exact (Nat.floor_mono (div_le_div_of_nonneg_right
      (Real.log_le_log hpn hpB) hr.le)).trans (Nat.floor_le_ceil _)
  have hidx : geometricBinCount ρ B - geometricPrimeBin ρ B p =
      ⌊Real.log (norm p)/Real.log ρ⌋₊ := by
    unfold geometricPrimeBin
    omega
  change ρ^(geometricBinCount ρ B-geometricPrimeBin ρ B p) ≤ norm p ∧
    norm p < ρ*ρ^(geometricBinCount ρ B-geometricPrimeBin ρ B p)
  rw [hidx]
  constructor
  · apply (Real.pow_le_iff_le_log (zero_lt_one.trans hρ) hpn).mpr
    exact (le_div_iff₀ hr).mp (Nat.floor_le hl)
  · rw [←pow_succ',Real.lt_pow_iff_log_lt hpn (zero_lt_one.trans hρ)]
    have h := (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (Real.log (norm p)/Real.log ρ))
    simpa only [Nat.cast_add,Nat.cast_one] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted finite-sum forms of the exact largest-prime decomposition,
ready for the actual norm twist and cubic character. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPairSupport_primary (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) (hD : ∀ d ∈ D, primary d)
    {n : Eisenstein} (hn : n ∈ primaryPairSupport R D) : primary n := by
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
  exact primary_mul (hR _ hr) (hD _ hd)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FourierCutoff
attribute [-instance] _root_.instMeasurableSpace
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

theorem frequencyCutoff_one {x : ℝ} (hx : |x| ≤ 1/2) : frequencyCutoff x = 1 := by
  rw [frequencyCutoff_apply, frequencyBump.one_of_mem_closedBall]
  · rfl
  · simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, frequencyBump] using hx

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelPartialSummation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

private lemma primaryPrimeFiber_eq (n : ℕ) (X : ℝ) (hn : (n : ℝ) ≤ X) :
    (primeCutoff (n : ℝ)).filter (fun p => normNat p = n) =
      (primeCutoff X).filter (fun p => normNat p = n) := by
  ext p
  simp only [Finset.mem_filter, mem_primeCutoff]
  constructor
  · intro hp
    exact ⟨⟨hp.1.1, hp.1.2.trans hn⟩, hp.2⟩
  · intro hp
    have he : norm p = (n : ℝ) := by rw [← normNat_cast p, hp.2]
    exact ⟨⟨hp.1.1, he.le⟩, hp.2⟩

lemma primaryPrimeMultiplicity_zero : primaryPrimeMultiplicity 0 = 0 := by
  have he : (primeCutoff (0 : ℝ)).filter (fun p => normNat p = 0) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hp' := (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
    have hn : norm p = 0 := by
      rw [← normNat_cast p, (Finset.mem_filter.mp hp).2, Nat.cast_zero]
    have hz : p = 0 := by
      apply Subtype.ext
      exact Complex.normSq_eq_zero.mp hn
    exact hp'.2.ne_zero hz
  simp only [primaryPrimeMultiplicity, Nat.cast_zero, he, Finset.card_empty]

lemma primeNorm_sum_eq (g : ℕ → ℝ) {X : ℝ} (hX : 0 ≤ X) :
    (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, g n * primaryPrimeMultiplicity n) =
      ∑ p ∈ primeCutoff X, g (normNat p) := by
  have hmaps : ∀ p ∈ primeCutoff X, normNat p ∈ Finset.Icc 0 ⌊X⌋₊ := by
    intro p hp
    simp only [Finset.mem_Icc, Nat.zero_le, true_and]
    apply (Nat.le_floor_iff hX).mpr
    rw [normNat_cast]
    exact (mem_primeCutoff.mp hp).2
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps g]
  apply Finset.sum_congr rfl
  intro n hn
  have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff hX).mp (Finset.mem_Icc.mp hn).2
  rw [primaryPrimeMultiplicity, primaryPrimeFiber_eq n X hnX]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

lemma normCountingSum_primaryPrimeMultiplicity {X : ℝ} (hX : 0 ≤ X) :
    normCountingSum primaryPrimeMultiplicity X = primaryPrimeCount X := by
  simpa only [normCountingSum, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one,
    primaryPrimeCount] using primeNorm_sum_eq (fun _ => 1) hX

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma integrable_height_phase (h : ℝ → ℂ) (hi : Integrable h) (ℓ : ℝ) :
    Integrable (fun t : ℝ => h t*Complex.exp ((ℓ*t:ℝ)*Complex.I)) := by
  apply hi.mul_bdd (c := 1)
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp ((ℓ*t:ℝ)*Complex.I))).aestronglyMeasurable
  · exact Eventually.of_forall (fun _ => by simp [Complex.norm_exp])

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightPartition
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma heightWindowCount_scale_bounds {S T : ℝ} (hS : 0 < S) (hT : 0 < T)
    {j : ℕ} (hj : j < heightWindowCount S T) :
    T ≤ T*(3/2:ℝ)^j ∧ T*(3/2:ℝ)^j < 2*Real.pi*S := by
  have hr : 0 < Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  have hj' : (j:ℝ) < Real.log ((2*Real.pi*S)/T)/Real.log (3/2:ℝ) := Nat.lt_ceil.mp hj
  have hlog : Real.log ((3/2:ℝ)^j) < Real.log ((2*Real.pi*S)/T) := by
    rw [Real.log_pow]
    exact (lt_div_iff₀ hr).mp hj'
  have hb := (Real.log_lt_log_iff (by positivity : 0 < (3/2:ℝ)^j)
    (div_pos (by positivity) hT)).mp hlog
  constructor
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3/2)) hT.le
  · simpa only [mul_comm] using (lt_div_iff₀ hT).mp hb

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

lemma localizedEndpointWeight_norm_le {T : ℝ} (S : ℝ) (hT : 0 < T) (t : ℝ) :
    ‖localizedEndpointWeight S T t‖ ≤ 1 := by
  by_cases ht : t ∈ dyadicHeightSupport T
  · have habs : T ≤ |t| := by
      rcases ht with ht | ht
      · exact ht.1.trans (le_abs_self t)
      · exact (by linarith [ht.2] : T ≤ -t).trans (neg_le_abs t)
    have hp : 0 < |t| := hT.trans_le habs
    rw [localizedEndpointWeight, norm_mul, norm_div, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT, Complex.norm_I, mul_one]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (T*1)/|t| * 1 := by
        gcongr
        · exact frequencyCutoff_norm_le _
        · exact heightWindow_norm_le _ _
      _ ≤ 1 := by simpa only [mul_one] using (div_le_one hp).mpr habs
  · rw [localizedEndpointWeight_zero S hT t ht, norm_zero]
    norm_num

lemma cutoffHeightMultiplier_window_endpoints {T : ℝ} (S : ℝ) (hT : 0 < T) (t : ℝ) :
    cutoffHeightMultiplier S t*heightWindow T t =
      (T:ℂ)⁻¹*localizedEndpointWeight S T t*
        (1-Complex.exp ((-Real.log 2*t : ℝ)*Complex.I)) := by
  by_cases ht : t = 0
  · subst t
    have hz : (0:ℝ) ∉ dyadicHeightSupport T := by
      simp only [dyadicHeightSupport, Set.mem_union, Set.mem_Icc, not_or]
      constructor <;> rintro ⟨ha,hb⟩ <;> linarith
    rw [heightWindow_zero hT hz, localizedEndpointWeight_zero S hT 0 hz]
    simp
  · rw [cutoffHeightMultiplier_eq_endpoints S ht, localizedEndpointWeight]
    have hc : (T:ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightEndpointRegularity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness at the removable reciprocal singularity, compact support,
and the exact two-endpoint formula for a localized cutoff. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology
namespace CubicFirstMoment

lemma localizedEndpointWeight_integrable (S : ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (localizedEndpointWeight S T) :=
  (localizedEndpointWeight_smooth S hT).continuous.integrable_of_hasCompactSupport
    (localizedEndpointWeight_compact S hT)

lemma localizedEndpointWeight_derivatives (S : ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (deriv (localizedEndpointWeight S T)) ∧
    Differentiable ℝ (deriv (localizedEndpointWeight S T)) ∧
    Integrable (deriv (deriv (localizedEndpointWeight S T))) := by
  have hd := (contDiff_infty_iff_deriv.mp (localizedEndpointWeight_smooth S hT)).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hc := (localizedEndpointWeight_compact S hT).deriv
  exact ⟨hd.continuous.integrable_of_hasCompactSupport hc,
    hd.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), hdd.continuous.integrable_of_hasCompactSupport hc.deriv⟩

lemma localizedEndpointWeight_second_zero (S : ℝ) {T : ℝ} (hT : 0 < T) (t : ℝ)
    (ht : t ∉ dyadicHeightSupport T) :
    deriv (deriv (localizedEndpointWeight S T)) t = 0 := by
  apply deriv_of_notMem_tsupport
  intro hh
  exact ht (localizedEndpointWeight_tsupport S hT (tsupport_deriv_subset hh))

lemma cutoff_window_fourier_endpoints (S : ℝ) {T : ℝ} (hT : 0 < T) (ℓ : ℝ) :
    heightFourierIntegral (fun t => cutoffHeightMultiplier S t*heightWindow T t) ℓ =
      (T:ℂ)⁻¹*(heightFourierIntegral (localizedEndpointWeight S T) ℓ -
        heightFourierIntegral (localizedEndpointWeight S T) (ℓ-Real.log 2)) := by
  have hi := localizedEndpointWeight_integrable S hT
  simp only [heightFourierIntegral_eq]
  rw [← integral_sub (integrable_height_phase _ hi ℓ)
    (integrable_height_phase _ hi (ℓ-Real.log 2)), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [cutoffHeightMultiplier_window_endpoints S hT t]
  have he : Complex.exp (((ℓ-Real.log 2)*t:ℝ)*Complex.I) =
      Complex.exp ((ℓ*t:ℝ)*Complex.I)*Complex.exp ((-Real.log 2*t:ℝ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

theorem bilinear_cutoff_window_endpoints (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (S : ℝ) {T X : ℝ} (hT : 0 < T) (hX : 0 < X) :
    (∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*
      heightFourierIntegral (fun t => cutoffHeightMultiplier S t*heightWindow T t)
        (Real.log (norm (a*b))-Real.log X)) =
      heightBilinearValue P B α β (localizedEndpointWeight S T) X T -
        heightBilinearValue P B α β (localizedEndpointWeight S T) (2*X) T := by
  simp only [heightBilinearValue, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [cutoff_window_fourier_endpoints S hT,
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hX.ne']
  have he : Real.log (norm (a*b))-Real.log X-Real.log 2 =
      Real.log (norm (a*b))-(Real.log 2+Real.log X) := by ring
  rw [he]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CorrectedBilinearScale
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic saving furnished by corrected Cauchy--Schwarz. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma bilinear_error_log_saving {x : ℂ} {M K A L z E V : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hA : 0 < A) (hL : 0 < L) (hz : 0 < z)
    (k d : ℕ) (_hE : 0 ≤ E) (hV : 0 ≤ V)
    (herror : ‖x‖^2 ≤ E*V) (henergy : E ≤ M*A*z^d)
    (hmass : V ≤ K*A^(2/3:ℝ)*L^(5/3:ℝ)/z^(2*k+d)) :
    ‖x‖ ≤ Real.sqrt (M*K)*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k := by
  have hsqA : (A^(5/6:ℝ))^2 = A^(5/3:ℝ) := by
    rw [←Real.rpow_natCast (A^(5/6:ℝ)) 2,←Real.rpow_mul hA.le]
    norm_num
  have hsqL : (L^(5/6:ℝ))^2 = L^(5/3:ℝ) := by
    rw [←Real.rpow_natCast (L^(5/6:ℝ)) 2,←Real.rpow_mul hL.le]
    norm_num
  have hAadd : A*A^(2/3:ℝ) = A^(5/3:ℝ) := by
    nth_rw 1 [←Real.rpow_one A]
    rw [←Real.rpow_add hA]
    norm_num
  have hid : (Real.sqrt (M*K)*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k)^2 =
      (M*A*z^d)*(K*A^(2/3:ℝ)*L^(5/3:ℝ)/z^(2*k+d)) := by
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hM hK),hsqA,hsqL,
      pow_add,pow_mul]
    field_simp
    simp only [←pow_mul]
    rw [Nat.mul_comm 2 k,←hAadd]
    ring
  have hb := herror.trans (mul_le_mul henergy hmass hV (by positivity))
  rw [←hid] at hb
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mp hb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightWindowSum
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual finite ratio-3/2 height windows costs one logarithm. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem height_window_sum_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (H T E : ℝ) (f : ℝ → ℂ),
      1 ≤ H → 1 ≤ T → 0 ≤ E →
      (∀ t, T ≤ t → t < 2*Real.pi*H → ‖f t‖ ≤ E) →
      ‖∑ j ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^j)‖ ≤
        K*(1+Real.log H)*E := by
  obtain ⟨K,hK,hcount⟩ := heightWindowCount_log_bound
  refine ⟨K,hK,?_⟩
  intro H T E f hH hT hE hf
  calc
    _ ≤ ∑ j ∈ Finset.range (heightWindowCount H T), ‖f (T*(3/2:ℝ)^j)‖ :=
      norm_sum_le _ _
    _ ≤ (heightWindowCount H T:ℝ)*E := by
      have hb (j : ℕ) (hj : j ∈ Finset.range (heightWindowCount H T)) :
          ‖f (T*(3/2:ℝ)^j)‖ ≤ E := by
        have hs := heightWindowCount_scale_bounds (zero_lt_one.trans_le hH)
          (zero_lt_one.trans_le hT) (Finset.mem_range.mp hj)
        exact hf _ hs.1 hs.2
      simpa using Finset.sum_le_sum hb
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcount H T hH hT) hE

theorem height_window_sum_log_saving :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ (H T Z B K : ℝ) (j : ℕ) (f : ℝ → ℂ),
      1 ≤ H → 1 ≤ T → 1 ≤ Z → H ≤ Z^3 → 0 ≤ B → 0 ≤ K →
      (∀ t, T ≤ t → t < 2*Real.pi*H →
        ‖f t‖ ≤ K*B/(1+Real.log Z)^(j+1)) →
      ‖∑ i ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^i)‖ ≤
        K₀*K*B/(1+Real.log Z)^j := by
  obtain ⟨K₀,hK₀,hbound⟩ := height_window_sum_bound
  refine ⟨3*K₀,by positivity,?_⟩
  intro H T Z B K j f hH hT hZ hHZ hB hK hf
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ]
  have hlog : 1+Real.log H ≤ 3*(1+Real.log Z) := by
    have hh := Real.log_le_log (zero_lt_one.trans_le hH) hHZ
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  apply (hbound H T (K*B/(1+Real.log Z)^(j+1)) f hH hT (by positivity) hf).trans
  calc
    _ ≤ K₀*(3*(1+Real.log Z))*(K*B/(1+Real.log Z)^(j+1)) := by gcongr
    _ = (3*K₀)*K*B/(1+Real.log Z)^j := by
      rw [pow_succ]
      field_simp

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormPartitionVariation
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform scaled derivative bounds for the actual distinguished norm
partition. Rescaling the prime norm introduces no growing variation cost. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma normPartitionWeight_deriv_zero {x : ℝ} (hx : x ∉ Icc (1:ℝ) 2) :
    deriv normPartitionWeight x = 0 := by
  by_cases hlo : x < 1
  · have he : EqOn normPartitionWeight (fun _ : ℝ => (0:ℂ)) (Iio 1) :=
      fun _ hy => normPartitionWeight_low hy
    simpa only [deriv_const] using he.deriv isOpen_Iio hlo
  · have hhi : 2 < x := by
      rcases not_and_or.mp hx with h | h
      · exact False.elim (h (le_of_not_gt hlo))
      · exact lt_of_not_ge h
    have he : EqOn normPartitionWeight (fun _ : ℝ => (0:ℂ)) (Ioi 2) :=
      fun _ hy => normPartitionWeight_high hy
    simpa only [deriv_const] using he.deriv isOpen_Ioi hhi

theorem normPartitionWeight_radial_deriv_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 0 < x → ‖deriv normPartitionWeight x‖*x ≤ D := by
  have hd : Continuous (deriv normPartitionWeight) :=
    normPartitionWeight_smooth.continuous_deriv (by norm_num)
  obtain ⟨D,hD⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    ((hd.norm.mul continuous_id).continuousOn)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x hx
  by_cases hmem : x ∈ Icc (1:ℝ) 2
  · have h := hD x hmem
    change ‖‖deriv normPartitionWeight x‖*x‖ ≤ D at h
    rw [Real.norm_of_nonneg (mul_nonneg (_root_.norm_nonneg _) hx.le)] at h
    exact h.trans (le_max_left _ _)
  · rw [normPartitionWeight_deriv_zero hmem,norm_zero,zero_mul]
    exact le_max_right _ _

lemma scaledNormPartitionWeight_smooth (c : ℝ) :
    ContDiff ℝ ∞ (scaledNormPartitionWeight c) :=
  normPartitionWeight_smooth.comp (contDiff_const.mul contDiff_id)

lemma scaledNormPartitionWeight_norm (c x : ℝ) : ‖scaledNormPartitionWeight c x‖ ≤ 1 :=
  normPartitionWeight_norm _

theorem scaledNormPartitionWeight_deriv_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ c : ℝ, 0 < c → ∀ x : ℝ, 0 < x →
      ‖deriv (scaledNormPartitionWeight c) x‖*x ≤ D := by
  obtain ⟨D,hD,hbound⟩ := normPartitionWeight_radial_deriv_bound
  refine ⟨D,hD,?_⟩
  intro c hc x hx
  have hd := ((normPartitionWeight_smooth.differentiable (by norm_num)).differentiableAt
    (x := c*x)).hasDerivAt.scomp x (hasDerivAt_const_mul c)
  have he : deriv (scaledNormPartitionWeight c) x = c • deriv normPartitionWeight (c*x) := hd.deriv
  rw [he,norm_smul,Real.norm_of_nonneg hc.le]
  calc
    _ = ‖deriv normPartitionWeight (c*x)‖*(c*x) := by ring
    _ ≤ D := hbound _ (mul_pos hc hx)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedStoppingWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished scale coefficients use a single bounded-variation
family at every partition scale, exactly as the stopped estimate requires. -/
noncomputable section
open Filter
open scoped ContDiff
namespace CubicFirstMoment

lemma distinguishedStoppingWeights_at {i N : ℕ} (k : Fin i → Fin N)
    (j : Fin i) (p : Eisenstein) :
    distinguishedStoppingWeights k j (norm p) =
      normPartitionWeight (2*norm p/(4/3:ℝ)^(k j).val) := by
  unfold distinguishedStoppingWeights scaledNormPartitionWeight
  congr 1
  ring

theorem distinguishedStoppingWeights_uniform :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (i N : ℕ) (k : Fin i → Fin N),
      (∀ j x, ‖distinguishedStoppingWeights k j x‖ ≤ 1) ∧
      (∀ j, ContDiff ℝ ∞ (distinguishedStoppingWeights k j)) ∧
      (∀ j x, 0 < x → ‖deriv (distinguishedStoppingWeights k j) x‖*x ≤ V) := by
  obtain ⟨V,hV,hbound⟩ := scaledNormPartitionWeight_deriv_bound
  refine ⟨V,hV,?_⟩
  intro i N k
  exact ⟨fun _ _ => scaledNormPartitionWeight_norm _ _,
    fun _ => scaledNormPartitionWeight_smooth _,
    fun j x hx => hbound _ (by positivity) x hx⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedActualRange
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordinary stopped range lies strictly inside the stronger
length range needed for the full Gauss Mellin complement. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_stopped_actual_range (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ A b : ℝ,
      X/16 ≤ A*b → A*b ≤ 16*X →
      X^(7/20:ℝ) ≤ b → b ≤ X^(39/100:ℝ) →
      2*b^(3/2:ℝ) ≤ A ∧ A ≤ b^2/(Real.log X)^G := by
  have hlogsave := (isLittleO_log_rpow_rpow_atTop (G:ℝ)
    (by norm_num : (0:ℝ) < 1/20)).def (by norm_num : (0:ℝ) < 1/16)
  filter_upwards [eventually_gt_atTop (1:ℝ),hlogsave,
    eventually_const_mul_rpow_le (by norm_num : (39/40:ℝ) < 1) 32]
    with X hX hlogsave hpower
  intro A b hlo hhi hblo hbhi
  have hXp : 0 < X := zero_lt_one.trans hX
  have hbp : 0 < b := (Real.rpow_pos_of_pos hXp _).trans_le hblo
  have hL : 0 < Real.log X := Real.log_pos hX
  have hlower : 2*b^(3/2:ℝ) ≤ A := by
    have hbpow := Real.rpow_le_rpow hbp.le hbhi (by norm_num : (0:ℝ) ≤ 5/2)
    rw [←Real.rpow_mul hXp.le] at hbpow
    norm_num at hbpow
    have hbsmall : 32*b^(5/2:ℝ) ≤ X :=
      (mul_le_mul_of_nonneg_left hbpow (by norm_num)).trans (by simpa only [Real.rpow_one] using hpower)
    have he : b^(3/2:ℝ)*b = b^(5/2:ℝ) := by
      calc
        _ = b^(3/2:ℝ)*b^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hbp]; norm_num
    apply (mul_le_mul_iff_left₀ hbp).mp
    rw [mul_assoc,he]
    exact (show 2*b^(5/2:ℝ) ≤ X/16 by linarith only [hbsmall]).trans hlo
  have hlogbound : (Real.log X)^G ≤ (1/16:ℝ)*X^(1/20:ℝ) := by
    simpa only [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg hL.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hXp.le _)] using hlogsave
  have hbcube : X^(21/20:ℝ) ≤ b^3 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hblo 3
    rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le] at hh
    norm_num at hh
    exact hh
  have hmul : (A*b)*(Real.log X)^G ≤ b^3 := by
    calc
      _ ≤ (16*X)*(Real.log X)^G := mul_le_mul_of_nonneg_right hhi (pow_nonneg hL.le _)
      _ ≤ (16*X)*((1/16:ℝ)*X^(1/20:ℝ)) :=
        mul_le_mul_of_nonneg_left hlogbound (by positivity)
      _ = X^(21/20:ℝ) := by
        have he : X*X^(1/20:ℝ) = X^(21/20:ℝ) := by
          nth_rw 1 [←Real.rpow_one X]
          rw [←Real.rpow_add hXp]
          norm_num
        nlinarith [he]
      _ ≤ _ := hbcube
  refine ⟨hlower,(le_div_iff₀ (pow_pos hL G)).mpr ?_⟩
  apply (mul_le_mul_iff_left₀ hbp).mp
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDyadPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp dyads with the strict lower endpoint used by stopped rows.
The partition is finite and its count depends only on the norm envelope. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedNormDyadLength_pos (j : ℕ) : 0 < stoppedNormDyadLength j := by
  unfold stoppedNormDyadLength
  positivity

lemma stoppedNormDyad_bounds {S : Finset Eisenstein} {j : ℕ} {n : Eisenstein}
    (hn : n ∈ stoppedNormDyad S j) (hnorm : 2 ≤ norm n) :
    stoppedNormDyadLength j/2 < norm n ∧ norm n ≤ stoppedNormDyadLength j := by
  have hN : 2 ≤ normNat n := by exact_mod_cast (show (2:ℝ) ≤ (normNat n:ℝ) by
    simpa only [normNat_cast] using hnorm)
  have hne : normNat n-1 ≠ 0 := by omega
  have hlo := Nat.pow_log_le_self 2 hne
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (normNat n-1)
  have hj := (Finset.mem_filter.mp hn).2
  change Nat.log 2 (normNat n-1) = j at hj
  rw [hj] at hlo hhi
  have hl : (2:ℕ)^j < normNat n := by omega
  have hu : normNat n ≤ (2:ℕ)^(j+1) := by omega
  have hlr : (2:ℝ)^j < norm n := by
    rw [←normNat_cast]
    exact_mod_cast hl
  have hur : norm n ≤ (2:ℝ)^(j+1) := by
    rw [←normNat_cast]
    exact_mod_cast hu
  unfold stoppedNormDyadLength
  rw [pow_succ]
  constructor
  · nlinarith
  · simpa only [pow_succ] using hur

lemma stoppedNormDyad_outer_bounds {S : Finset Eisenstein} {j : ℕ} {n : Eisenstein}
    (hn : n ∈ stoppedNormDyad S j) (hp : primary n) :
    stoppedNormDyadLength j/2 ≤ norm n ∧ norm n ≤ stoppedNormDyadLength j := by
  by_cases htwo : 2 ≤ norm n
  · have hh := stoppedNormDyad_bounds hn htwo
    exact ⟨hh.1.le,hh.2⟩
  · have hone : 1 ≤ norm n := one_le_norm (primary_ne_zero hp)
    have hN : normNat n = 1 := by
      have hl : 1 ≤ normNat n := by exact_mod_cast (show (1:ℝ) ≤ (normNat n:ℝ) by
        simpa only [normNat_cast] using hone)
      have hu : normNat n < 2 := by exact_mod_cast (show (normNat n:ℝ) < 2 by
        simpa only [normNat_cast] using lt_of_not_ge htwo)
      omega
    have hj : j = 0 := by
      have he := (Finset.mem_filter.mp hn).2
      simpa only [stoppedNormDyadIndex,hN,Nat.sub_self,Nat.log_zero_right] using he.symm
    subst j
    simp only [stoppedNormDyadLength,zero_add,pow_one,div_self (by norm_num : (2:ℝ) ≠ 0)]
    rw [←normNat_cast,hN]
    norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedKernelRange
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Norm geometry of the actual stopped kernel, before any analytic
estimate. Sharp side dyads imply the strengthened bilinear length range. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma stopped_dyad_product_range {X A B : ℝ} {a b : Eisenstein}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : A ≤ norm a ∧ norm a ≤ 2*A)
    (hb : B/2 ≤ norm b ∧ norm b ≤ B)
    (hprod : X/2 ≤ norm (a*b) ∧ norm (a*b) ≤ 3*X) :
    X/4 ≤ A*B ∧ A*B ≤ 6*X := by
  rw [norm_mul_eq] at hprod
  have hu := mul_le_mul ha.2 hb.2 (norm_nonneg _) (by positivity : 0 ≤ 2*A)
  have hl := mul_le_mul ha.1 hb.1 (by positivity : 0 ≤ B/2) (norm_nonneg _)
  constructor <;> nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingBinShift
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport between geometric bins with two ambient norm cutoffs.
Below the smaller cutoff the bin labels differ by one fixed integer, and
the corresponding lower endpoints and prefix sets agree. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma geometricBinCount_mono {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) :
    geometricBinCount ρ X ≤ geometricBinCount ρ F := by
  exact Nat.ceil_mono (div_le_div_of_nonneg_right
    (Real.log_le_log hX hXF) (Real.log_pos hρ).le)

lemma geometricPrimeBin_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) {p : Eisenstein}
    (hp : primaryPrime p) (hpX : norm p ≤ X) :
    geometricPrimeBin ρ F p = geometricPrimeBin ρ X p +
      (geometricBinCount ρ F-geometricBinCount ρ X) := by
  have hc := geometricBinCount_mono hρ hX hXF
  have hpn : 0 < norm p := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
    (primaryPrime_norm_ge_two hp)
  have hk : ⌊Real.log (norm p)/Real.log ρ⌋₊ ≤ geometricBinCount ρ X :=
    (Nat.floor_mono (div_le_div_of_nonneg_right (Real.log_le_log hpn hpX)
      (Real.log_pos hρ).le)).trans (Nat.floor_le_ceil _)
  unfold geometricPrimeBin
  omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimeUpper
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary counting upper bound needed in the smooth-number
Rankin argument, derived from the existing ordinary prime PNT input. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma primaryPrimeCount_mono {x y : ℝ} (hxy : x ≤ y) :
    primaryPrimeCount x ≤ primaryPrimeCount y := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp,hpx⟩ := mem_primeCutoff.mp hp
  exact mem_primeCutoff.mpr ⟨hp,hpx.trans hxy⟩

theorem primaryPrimeCount_upper (hpnt : PrimaryPrimePNT) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y →
      primaryPrimeCount Y ≤ C*Y/Real.log Y := by
  have hevent : ∀ᶠ Y : ℝ in atTop,
      primaryPrimeCount Y*Real.log Y/Y < 2 :=
    hpnt.eventually (eventually_lt_nhds (by norm_num : (1:ℝ) < 2))
  obtain ⟨Y₀,hY₀⟩ := eventually_atTop.mp hevent
  let Q := max 2 Y₀
  let C := 2+primaryPrimeCount Q
  have hc : 0 ≤ primaryPrimeCount Q := Nat.cast_nonneg _
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro Y hY
  have hY1 : 1 < Y := lt_of_lt_of_le (by norm_num) hY
  have hY0 : 0 < Y := zero_lt_one.trans hY1
  have hl : 0 < Real.log Y := Real.log_pos hY1
  apply (le_div_iff₀ hl).mpr
  by_cases hQ : Q ≤ Y
  · have h := (div_lt_iff₀ hY0).mp (hY₀ Y ((le_max_right 2 Y₀).trans hQ))
    apply h.le.trans
    apply mul_le_mul_of_nonneg_right _ hY0.le
    dsimp [C]
    linarith
  · have hcount := primaryPrimeCount_mono (le_of_not_ge hQ)
    have hCQ : primaryPrimeCount Q ≤ C := by dsimp [C]; linarith
    calc
      primaryPrimeCount Y*Real.log Y ≤ C*Real.log Y :=
        mul_le_mul_of_nonneg_right (hcount.trans hCQ) hl.le
      _ ≤ C*Y := mul_le_mul_of_nonneg_left (Real.log_le_self hY0.le) hC.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeReciprocal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime reciprocal estimate used in the smooth-number discard,
derived from ordinary prime counting by literal Abel summation. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma primaryPrimeMultiplicity_one : primaryPrimeMultiplicity 1 = 0 := by
  have he : (primeCutoff (1:ℝ)).filter (fun p => normNat p = 1) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hpp := (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
    have hn : norm p = 1 := by
      rw [←normNat_cast p,(Finset.mem_filter.mp hp).2,Nat.cast_one]
    exact hpp.2.not_isUnit (isUnit_of_norm_eq_one hn)
  simp only [primaryPrimeMultiplicity,Nat.cast_one,he,Finset.card_empty,Nat.cast_zero]

private lemma inverse_square_continuous (X : ℝ) :
    ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc 2 X) := by
  apply (continuousOn_id.pow 2).inv₀
  intro t ht
  exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))

lemma primaryPrime_reciprocal_integrable {X : ℝ} (hX : 2 ≤ X) :
    IntervalIntegrable (fun t => primaryPrimeCount t/t^2) volume 2 X := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr
  have h := integrableOn_mul_sum_Icc (c := primaryPrimeMultiplicity)
    (m := 0) (a := 2) (b := X) (by norm_num)
    (inverse_square_continuous X).integrableOn_Icc
  apply h.congr_fun _ measurableSet_Icc
  intro t ht
  change (t^2)⁻¹*normCountingSum primaryPrimeMultiplicity t = _
  rw [normCountingSum_primaryPrimeMultiplicity (by linarith [ht.1])]
  ring

lemma primaryPrime_reciprocal_identity {X : ℝ} (hX : 2 ≤ X) :
    (∑ p ∈ primeCutoff X, (norm p)⁻¹) = primaryPrimeCount X/X+
      ∫ t in 2..X, primaryPrimeCount t/t^2 := by
  have hdiff : ∀ t ∈ Set.Icc (2:ℝ) X,
      DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc (2:ℝ) X,
      deriv (fun x : ℝ => x⁻¹) t = -(t^2)⁻¹ := by
    intro t ht
    exact (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))).deriv
  have hint : IntegrableOn (deriv (fun x : ℝ => x⁻¹)) (Set.Icc 2 X) := by
    exact ((inverse_square_continuous X).neg.integrableOn_Icc).congr_fun
      (fun t ht => (hderiv t ht).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₁ (c := primaryPrimeMultiplicity)
    primaryPrimeMultiplicity_zero primaryPrimeMultiplicity_one X hdiff hint
  rw [primeNorm_sum_eq (fun n => (n:ℝ)⁻¹) (by linarith)] at h
  change (∑ p ∈ primeCutoff X, (normNat p:ℝ)⁻¹) =
    X⁻¹*normCountingSum primaryPrimeMultiplicity X-
      ∫ t in Set.Ioc 2 X, deriv (fun x : ℝ => x⁻¹) t*
        normCountingSum primaryPrimeMultiplicity t at h
  rw [normCountingSum_primaryPrimeMultiplicity (by linarith),
    ←intervalIntegral.integral_of_le hX] at h
  have hi : (∫ t in 2..X, deriv (fun x : ℝ => x⁻¹) t*
      normCountingSum primaryPrimeMultiplicity t) =
      -(∫ t in 2..X, primaryPrimeCount t/t^2) := by
    rw [←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    dsimp only
    rw [hderiv t ht,normCountingSum_primaryPrimeMultiplicity (by linarith [ht.1])]
    ring
  rw [hi] at h
  simpa only [normNat_cast,sub_neg_eq_add,div_eq_mul_inv,mul_comm] using h

theorem primaryPrime_reciprocal_upper (hpnt : PrimaryPrimePNT) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
      (∑ p ∈ primeCutoff X, (norm p)⁻¹) ≤
        C/Real.log X+C*(Real.log (Real.log X)-Real.log (Real.log 2)) := by
  obtain ⟨C,hC,hcount⟩ := primaryPrimeCount_upper hpnt
  refine ⟨C,hC,?_⟩
  intro X hX
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hlog : 0 < Real.log X := Real.log_pos (lt_of_lt_of_le (by norm_num) hX)
  rw [primaryPrime_reciprocal_identity hX]
  apply add_le_add
  · calc
      _ ≤ (C*X/Real.log X)/X := div_le_div_of_nonneg_right (hcount X hX) hX0.le
      _ = C/Real.log X := by field_simp
  · have hright : IntervalIntegrable (fun t : ℝ => t⁻¹/Real.log t) volume 2 X := by
      have hpos : ∀ t ∈ Set.uIcc (2:ℝ) X, 0 < t := by
        intro t ht
        rw [Set.uIcc_of_le hX] at ht
        exact lt_of_lt_of_le (by norm_num) ht.1
      have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc 2 X) :=
        continuousOn_id.inv₀ (fun t ht => (hpos t ht).ne')
      have hlog : ContinuousOn Real.log (Set.uIcc 2 X) :=
        Real.continuousOn_log.mono (fun t ht => (hpos t ht).ne')
      apply (hinv.div hlog _).intervalIntegrable
      intro t ht
      rw [Set.uIcc_of_le hX] at ht
      exact (Real.log_pos (lt_of_lt_of_le (by norm_num) ht.1)).ne'
    calc
      _ ≤ ∫ t in 2..X, C*(t⁻¹/Real.log t) := by
        apply intervalIntegral.integral_mono_on hX (primaryPrime_reciprocal_integrable hX)
          (hright.const_mul C)
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
        calc
          _ ≤ (C*t/Real.log t)/t^2 :=
            div_le_div_of_nonneg_right (hcount t ht.1) (sq_nonneg t)
          _ = C*(t⁻¹/Real.log t) := by field_simp
      _ = C*(Real.log (Real.log X)-Real.log (Real.log 2)) := by
        rw [intervalIntegral.integral_const_mul,integral_inv_div_log (by norm_num)
          (lt_of_lt_of_le (by norm_num) hX)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothRankinSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth-number discard on the exp(sqrt(log X)) scale.
Only the ordinary prime number theorem is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_reciprocal_exp_bound (hpnt : PrimaryPrimePNT) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∑ p ∈ primeCutoff (Real.exp T), (norm p)⁻¹) ≤ C*(1+Real.log T) := by
  obtain ⟨C,hC,hbound⟩ := primaryPrime_reciprocal_upper hpnt
  let K : ℝ := 1+|Real.log (Real.log 2)|
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg (Real.log (Real.log 2))]
  refine ⟨C*K,mul_pos hC (zero_lt_one.trans_le hK),?_⟩
  intro T hT
  have h2 : (2:ℝ) ≤ Real.exp T := by
    have htwo : (2:ℝ) ≤ Real.exp 1 := by
      convert Real.add_one_le_exp (1:ℝ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
    exact htwo.trans (Real.exp_le_exp.mpr hT)
  have hb := hbound (Real.exp T) h2
  simp only [Real.log_exp] at hb
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  calc
    _ ≤ C/T+C*(Real.log T-Real.log (Real.log 2)) := hb
    _ ≤ C+C*(Real.log T+|Real.log (Real.log 2)|) :=
      add_le_add (div_le_self hC.le hT)
        (mul_le_mul_of_nonneg_left (by linarith [neg_le_abs (Real.log (Real.log 2))]) hC.le)
    _ ≤ C*K*(1+Real.log T) := by
      dsimp [K]
      nlinarith [mul_nonneg (abs_nonneg (Real.log (Real.log 2))) hlog]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingSelectedScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual selected-side size bounds. A nonzero cutoff bounds the final
selected prime, while the stopping inequalities and geometric distortion
bound the complete coefficient scale. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_prime_norm_lt {ψ : ℝ → ℝ}
    (hψ : ∀ x : ℝ, 2 ≤ x → ψ x = 0) {w : ℝ} (hw : 0 < w)
    {d p : Eisenstein} (hp : p ∈ primaryPrimeFactors d)
    (hne : cutoffMoebius ψ w d ≠ 0) : norm p < 2*w := by
  have hprod := (mul_ne_zero_iff.mp hne).2
  change (∏ p ∈ primaryPrimeFactors d, (ψ (norm p/w):ℂ)) ≠ 0 at hprod
  have hterm := (Finset.prod_ne_zero_iff.mp hprod) p hp
  by_contra h
  have hx : 2 ≤ norm p/w := (le_div_iff₀ hw).mpr (by linarith)
  apply hterm
  simp only [hψ (norm p/w) hx,Complex.ofReal_zero]

lemma geometric_selected_norm_distortion {ρ X ε : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    {d : Eisenstein} (hd : primary d) (hs : Squarefree d) (hdX : norm d ≤ X) :
    norm d ≤ X^ε * primeSurrogate (primaryPrimeFactors d)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) := by
  let s := primaryPrimeFactors d
  have hcell (p : Eisenstein) (hp : p ∈ s) :
      0 ≤ geometricBinLower ρ X (geometricPrimeBin ρ X p) ∧
        geometricBinLower ρ X (geometricPrimeBin ρ X p) ≤ norm p ∧
          norm p ≤ ρ*geometricBinLower ρ X (geometricPrimeBin ρ X p) := by
    have hspec := primaryPrimeFactor_spec hd hp
    have hpX := (norm_le_of_dvd (primary_ne_zero hd) hspec.2).trans hdX
    exact ⟨pow_nonneg (zero_lt_one.trans hρ).le _,
      (geometricPrimeBin_cell hρ hρ₂ hspec.1 hpX).1,
      (geometricPrimeBin_cell hρ hρ₂ hspec.1 hpX).2.le⟩
  have hnorm := (primeSurrogate_norm_bounds s (geometricPrimeBin ρ X)
    (geometricBinLower ρ X) (zero_lt_one.trans hρ).le hcell).2
  have hprod : (∏ p ∈ s, p) = d := primaryPrimeFactors_prod hd hs
  rw [hprod] at hnorm
  have hcount : (2:ℝ)^s.card ≤ X :=
    (primary_prime_subset_two_pow_le hd hs (Finset.Subset.refl _)).trans hdX
  have hpower : ρ^s.card ≤ X^ε := by
    calc
      _ ≤ ((2:ℝ)^ε)^s.card := pow_le_pow_left₀ (zero_lt_one.trans hρ).le hsmall _
      _ = ((2:ℝ)^s.card)^ε := by
        rw [←Real.rpow_mul_natCast (by norm_num),←Real.rpow_natCast_mul (by norm_num),mul_comm]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hcount hε
  exact hnorm.trans (mul_le_mul_of_nonneg_right hpower
    (Finset.prod_nonneg (fun p _ => pow_nonneg (zero_lt_one.trans hρ).le _)))

theorem stoppingSideTest_norm_bounds {ρ X Z w ε : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    (hZ : 0 < Z) (hw : 0 < w) {ψ : ℝ → ℝ}
    (hψ : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {r d : Eisenstein} (hd : primary d) (hs : Squarefree d) (hdX : norm d ≤ X)
    {j k : ℕ} (hk : 1 ≤ k)
    (hstop : stoppingSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k Z r d)
    (hne : cutoffMoebius ψ w d ≠ 0) :
    Z ≤ norm (r*d) ∧ norm (r*d) ≤ 2*X^ε*w*Z := by
  have hX : 0 ≤ X := (norm_nonneg d).trans hdX
  have hbin : (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ X) j).Nonempty :=
    Finset.card_pos.mp (by rw [hstop.2.1]; omega)
  obtain ⟨p,hp⟩ := hbin
  obtain ⟨hpd,hpj⟩ := Finset.mem_filter.mp hp
  have hspec := primaryPrimeFactor_spec hd hpd
  have hpX := (norm_le_of_dvd (primary_ne_zero hd) hspec.2).trans hdX
  have hell : geometricBinLower ρ X j < 2*w := by
    have hlower := (geometricPrimeBin_cell hρ hρ₂ hspec.1 hpX).1
    rw [hpj] at hlower
    exact hlower.trans_lt (cutoffMoebius_prime_norm_lt hψ hw hpd hne)
  have hellp : 0 < geometricBinLower ρ X j := pow_pos (zero_lt_one.trans hρ) _
  have hbefore := (div_lt_iff₀ hellp).mp hstop.2.2.1
  have hsur : primeSurrogate (primaryPrimeFactors d)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) ≤ norm d := by
    calc
      _ ≤ ∏ p ∈ primaryPrimeFactors d, norm p := by
        apply Finset.prod_le_prod
        · intro p _hp
          exact pow_nonneg (zero_lt_one.trans hρ).le _
        · intro p hp
          have hpp := primaryPrimeFactor_spec hd hp
          exact (geometricPrimeBin_cell hρ hρ₂ hpp.1
            ((norm_le_of_dvd (primary_ne_zero hd) hpp.2).trans hdX)).1
      _ = norm (∏ p ∈ primaryPrimeFactors d, p) := (norm_finset_prod _ _).symm
      _ = norm d := by rw [primaryPrimeFactors_prod hd hs]
  rw [norm_mul_eq]
  refine ⟨hstop.2.2.2.trans (mul_le_mul_of_nonneg_left hsur (norm_nonneg r)),?_⟩
  calc
    _ ≤ norm r*(X^ε * primeSurrogate (primaryPrimeFactors d)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)) :=
      mul_le_mul_of_nonneg_left (geometric_selected_norm_distortion hρ hρ₂ hε hsmall hd hs hdX)
        (norm_nonneg r)
    _ = X^ε*(norm r*primeSurrogate (primaryPrimeFactors d)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)) := by ring
    _ ≤ X^ε*(Z*geometricBinLower ρ X j) :=
      mul_le_mul_of_nonneg_left hbefore.le (Real.rpow_nonneg hX _)
    _ ≤ X^ε*(Z*(2*w)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hell.le hZ.le) (Real.rpow_nonneg hX _)
    _ = _ := by ring

theorem stoppedBeta_norm_bounds (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    {ψ : ℝ → ℝ} (hψ : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {ρ X Z Q w ε : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hZ : 0 < Z) (hw : 0 < w)
    (hD : ∀ d ∈ D, primary d ∧ norm d ≤ X)
    {j k h : ℕ} (hk : 1 ≤ k) (early : Bool) {b : Eisenstein}
    (hs : Squarefree b)
    (hne : stoppedBeta R D v ψ w
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k h Z Q early) b ≠ 0) :
    Z ≤ norm b ∧ norm b ≤ 2*X^ε*w*Z := by
  unfold stoppedBeta primaryPairCoefficient at hne
  obtain ⟨p,hp,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hp,hprod⟩ := Finset.mem_filter.mp hp
  obtain ⟨_hr,hd⟩ := Finset.mem_product.mp hp
  have hsel : stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h Z Q early p.1 p.2 := by
    by_contra hn
    exact hterm (ite_eq_right hn)
  rw [ite_eq_left hsel] at hterm
  have hcut := (mul_ne_zero_iff.mp hterm).2
  have hsq : Squarefree (p.1*p.2) := by rwa [hprod]
  have hh := stoppingSideTest_norm_bounds hρ hρ₂ hε hsmall hZ hw hψ
    (hD p.2 hd).1 hsq.of_mul_right (hD p.2 hd).2 hk hsel.1 hcut
  rwa [hprod] at hh

/-- A fixed ambient dilation has the same strict selected-scale range.
The cutoff parameter remains X^ξ while the geometric distortion is
measured on the actual ambient envelope C*X. -/
theorem eventually_two_stage_stopped_dyad_range_dilation {ξ ε C : ℝ}
    (hC : 0 < C) (hgap : ξ+ε < 1/100) :
    ∀ᶠ X : ℝ in atTop, ∀ (b Z N : ℝ),
      (Z = X^(36/100:ℝ) ∨ Z = X^(38/100:ℝ)) →
      Z ≤ N → N ≤ 2*(C*X)^ε*X^ξ*Z → b/2 ≤ N → N ≤ b →
      X^(35/100:ℝ) ≤ b ∧ b ≤ X^(39/100:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show ε+ξ+38/100 < (39/100:ℝ) by linarith)
      (4*C^ε)] with X hX hlarge
  intro b Z N hZ hZN hN hbN hNb
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hZlo : X^(35/100:ℝ) ≤ Z := by
    rcases hZ with rfl | rfl
    all_goals exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hZhi : Z ≤ X^(38/100:ℝ) := by
    rcases hZ with rfl | rfl
    · exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    · exact le_rfl
  refine ⟨hZlo.trans (hZN.trans hNb),?_⟩
  have hh : 2*N ≤ X^(39/100:ℝ) := by
    calc
      2*N ≤ 4*(C*X)^ε*X^ξ*Z := by linarith
      _ ≤ 4*(C*X)^ε*X^ξ*X^(38/100:ℝ) :=
        mul_le_mul_of_nonneg_left hZhi (by positivity)
      _ = (4*C^ε)*X^(ε+ξ+38/100:ℝ) := by
        rw [Real.mul_rpow hC.le hXp.le,
          Real.rpow_add hXp,Real.rpow_add hXp]
        ring
      _ ≤ _ := hlarge
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingCoefficientShift
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recovering the smaller-envelope labels on actual nonzero stopped
coefficients, and transporting the independent remaining-side coefficient.
All finite support and both stopping thresholds stay unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppingSideTest_label_shift_bound {ρ X F Z : ℝ}
    (hρ : 1 < ρ) (hX : 0 < X) (hXF : X ≤ F)
    {d r : Eisenstein} (hd : primary d) (hdX : norm d ≤ X)
    {j k : ℕ} (hk : 1 ≤ k)
    (hs : stoppingSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k Z r d) :
    geometricBinCount ρ F-geometricBinCount ρ X ≤ j := by
  have hne : (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ F) j).Nonempty :=
    Finset.card_pos.mp (by rw [hs.2.1]; omega)
  obtain ⟨p,hp⟩ := hne
  obtain ⟨hpd,hpj⟩ := Finset.mem_filter.mp hp
  have hprime := primaryPrimeFactor_spec hd hpd
  have hpX := (norm_le_of_dvd (primary_ne_zero hd) hprime.2).trans hdX
  have hshift := geometricPrimeBin_shift hρ hX hXF hprime.1 hpX
  rw [hpj] at hshift
  omega

lemma stoppedBeta_label_shift_bound (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) {ρ X F Z Q : ℝ}
    (hρ : 1 < ρ) (hX : 0 < X) (hXF : X ≤ F)
    (hD : ∀ d ∈ D, primary d) {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X)
    {j k h : ℕ} (hk : 1 ≤ k) (early : Bool)
    (hne : stoppedBeta R D v ψ w
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
        j k h Z Q early) b ≠ 0) :
    geometricBinCount ρ F-geometricBinCount ρ X ≤ j := by
  unfold stoppedBeta primaryPairCoefficient at hne
  obtain ⟨p,hp,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
  obtain ⟨_hr,hd⟩ := Finset.mem_product.mp hp
  have hs : stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
      j k h Z Q early p.1 p.2 := by
    by_contra hs
    exact hterm (ite_eq_right hs)
  have hdb : p.2 ∣ b := ⟨p.1,by rw [mul_comm,he]⟩
  exact stoppingSideTest_label_shift_bound hρ hX hXF (hD p.2 hd)
    ((norm_le_of_dvd (primary_ne_zero hb) hdb).trans hbX) hk hs.1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightEndpointProfile
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed compact profile removes the reciprocal singularity. Dilating
this profile gives the normalized endpoint weights used in localization. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma endpointProfile_eq (x : ℝ) :
    endpointProfile x = heightWindow 1 x/((x:ℂ)*Complex.I) := by
  change localizedEndpointWeight (2/Real.pi) 1 x = _
  by_cases hx : x ∈ dyadicHeightSupport 1
  · have hnorm : |x| ≤ 2 := by
      rcases hx with hx | hx
      · exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have he : (x/(2*Real.pi))/(2/Real.pi) = x/4 := by field_simp; ring
    have hf : frequencyCutoff ((x/(2*Real.pi))/(2/Real.pi)) = 1 := by
      rw [he]
      apply frequencyCutoff_one
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4)]
      linarith
    simp only [localizedEndpointWeight, hf, Complex.ofReal_one, one_mul]
    ring
  · rw [localizedEndpointWeight_zero _ (by norm_num) _ hx,
      heightWindow_zero (by norm_num) hx, zero_div]

lemma heightWindow_dilation {T : ℝ} (hT : 0 < T) (t : ℝ) :
    heightWindow T t = heightWindow 1 (t/T) := by
  have he : t/((3/2)*T) = (t/T)/((3/2)*1)  := by field_simp [hT.ne']
  simp only [heightWindow, he, mul_one, div_one]

lemma localizedEndpointWeight_dilation {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (t : ℝ) :
    localizedEndpointWeight S T t =
      frequencyCutoff ((T/(2*Real.pi*S))*(t/T))*endpointProfile (t/T) := by
  have hf : (T/(2*Real.pi*S))*(t/T) = (t/(2*Real.pi))/S := by field_simp
  rw [hf, endpointProfile_eq, ← heightWindow_dilation hT]
  unfold localizedEndpointWeight
  by_cases ht : t = 0
  · subst t
    simp
  · have hc : (T:ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have htc : (t:ℂ) ≠ 0 := by exact_mod_cast ht
    push_cast
    field_simp

private lemma secondDerivativeBudget_pos (f : SchwartzMap ℝ ℂ) :
    0 < secondDerivativeBudget f := by
  have hs : 0 ≤ ∑ i ∈ Finset.range 3, SchwartzMap.seminorm ℝ 0 i f :=
    Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  dsimp [secondDerivativeBudget]
  linarith

private lemma norm_iteratedDeriv_le_budget (f : SchwartzMap ℝ ℂ) {i : ℕ}
    (hi : i ≤ 2) (x : ℝ) : ‖iteratedDeriv i f x‖ ≤ secondDerivativeBudget f := by
  have hb := SchwartzMap.le_seminorm' ℝ 0 i f x
  simp only [pow_zero, one_mul] at hb
  have hs : SchwartzMap.seminorm ℝ 0 i f ≤
      ∑ j ∈ Finset.range 3, SchwartzMap.seminorm ℝ 0 j f :=
    Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_range.mpr (by omega))
  exact hb.trans (by dsimp [secondDerivativeBudget]; linarith)

/-- Only two derivatives are needed for the far-cell integration by parts. -/
lemma scaled_schwartz_product_second_bound (f g : SchwartzMap ℝ ℂ) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ x : ℝ,
      ‖deriv (deriv (fun y => f (a*y)*g y)) x‖ ≤ K := by
  let A := secondDerivativeBudget f
  let B := secondDerivativeBudget g
  have hA : 0 < A := secondDerivativeBudget_pos f
  have hB : 0 < B := secondDerivativeBudget_pos g
  refine ⟨4*A*B, by positivity, ?_⟩
  intro a ha ha1 x
  have hf : ContDiff ℝ (2:ℕ) (fun y => f (a*y)) :=
    (f.smooth 2).comp (contDiff_const.mul contDiff_id)
  have he := iteratedDeriv_mul (n := 2) (x := x) hf.contDiffAt (g.smooth 2).contDiffAt
  have hb (i : ℕ) (hi : i ∈ Finset.range 3) :
      ‖((2:ℕ).choose i : ℂ)*iteratedDeriv i (fun y => f (a*y)) x*
          iteratedDeriv (2-i) g x‖ ≤ ((2:ℕ).choose i : ℝ)*A*B := by
    have hi2 : i ≤ 2 := by have := Finset.mem_range.mp hi; omega
    have hfi : ‖iteratedDeriv i (fun y => f (a*y)) x‖ ≤ A := by
      rw [iteratedDeriv_comp_const_smul (f.smooth i), norm_smul, Real.norm_eq_abs,
        abs_pow, abs_of_nonneg ha]
      apply (mul_le_mul (pow_le_one₀ ha ha1) (norm_iteratedDeriv_le_budget f hi2 (a*x))
        (_root_.norm_nonneg _) (by norm_num)).trans_eq
      exact one_mul _
    have hgi : ‖iteratedDeriv (2-i) g x‖ ≤ B :=
      norm_iteratedDeriv_le_budget g (by omega) x
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    gcongr
  have hsum := (norm_sum_le (Finset.range 3) _).trans (Finset.sum_le_sum hb)
  rw [← he] at hsum
  simp only [show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero] at hsum
  norm_num [Finset.sum_range_succ] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem localizedEndpointWeight_second_uniform :
    ∃ K : ℝ, 0 < K ∧ ∀ S T : ℝ, 0 < S → 0 < T → T ≤ 2*Real.pi*S →
      ∀ t : ℝ, ‖(T:ℂ)^2*deriv (deriv (localizedEndpointWeight S T)) t‖ ≤ K := by
  obtain ⟨K,hK,hbound⟩ := scaled_schwartz_product_second_bound frequencyCutoff endpointProfile
  refine ⟨K,hK,?_⟩
  intro S T hS hT hTS t
  let a := T/(2*Real.pi*S)
  let q := fun x => frequencyCutoff (a*x)*endpointProfile x
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := (div_le_one (by positivity)).mpr hTS
  have hq : ContDiff ℝ (2:ℕ) q :=
    ((frequencyCutoff.smooth 2).comp (contDiff_const.mul contDiff_id)).mul
      (endpointProfile.smooth 2)
  have he : localizedEndpointWeight S T = fun x => q (T⁻¹*x) := by
    funext x
    simpa only [q,a,div_eq_mul_inv,mul_comm T⁻¹] using
      localizedEndpointWeight_dilation hS hT x
  have hd := congrFun (iteratedDeriv_comp_const_smul (n := 2) hq T⁻¹) t
  simp only [show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero] at hd
  rw [he,hd,norm_mul,norm_pow,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hT,Real.norm_eq_abs,abs_pow,abs_inv,abs_of_pos hT]
  calc
    T^2*(T⁻¹^2*‖deriv (deriv q) (T⁻¹*t)‖) = ‖deriv (deriv q) (T⁻¹*t)‖ := by field_simp
    _ ≤ K := hbound a ha ha1 (T⁻¹*t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowLogScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer logarithmic exponents for the low-height localization.
These inequalities let the cell width be chosen before the error saving. -/
noncomputable section
namespace CubicFirstMoment

lemma low_large_log {Z : ℝ} (hZ : (65536:ℝ)^2 ≤ Z) : 8 ≤ 1+Real.log Z := by
  have hz : (2:ℝ)^16 ≤ Z := by norm_num at *; linarith
  have hh := Real.log_le_log (by positivity : 0 < (2:ℝ)^16) hz
  rw [Real.log_pow] at hh
  have htwo := Real.log_two_gt_d9
  norm_num only [Nat.cast_ofNat] at hh
  linarith

lemma low_outer_log_root {A Z L : ℝ} (hA : 0 ≤ A) (hZ : 0 < Z) (hL : 0 < L)
    (a : ℕ) (hbound : A ≤ Z^2*L^(3*a)) :
    A^(1/3:ℝ) ≤ Z^(2/3:ℝ)*L^a := by
  have h := Real.rpow_le_rpow hA hbound (show (0:ℝ) ≤ 1/3 by norm_num)
  have hnum : (Z^2)^(1/3:ℝ) = Z^(2/3:ℝ) := by
    rw [←Real.rpow_natCast Z 2,←Real.rpow_mul hZ.le]
    norm_num
  have hden : (L^(3*a))^(1/3:ℝ) = L^a := by
    rw [←Real.rpow_natCast L (3*a),←Real.rpow_mul hL.le]
    push_cast
    rw [show (3*(a:ℝ))*(1/3:ℝ) = (a:ℝ) by ring,Real.rpow_natCast]
  rwa [Real.mul_rpow (sq_nonneg Z) (pow_nonneg hL.le _),hnum,hden] at h

lemma low_diagonal_log_scale {A Z L : ℝ} (hA : 0 < A) (hZ : 0 < Z) (hL : 0 < L)
    (k d a : ℕ) (hbound : A ≤ Z^2*L^(3*a)) :
    A*Z*L^d/L^(a+k+d) ≤ A^(2/3:ℝ)*Z^(5/3:ℝ)/L^k := by
  have hr := low_outer_log_root hA.le hZ hL a hbound
  have ha : A^(2/3:ℝ)*A^(1/3:ℝ) = A := by
    rw [←Real.rpow_add hA]
    norm_num
  have hz : Z*Z^(2/3:ℝ) = Z^(5/3:ℝ) := by
    nth_rw 1 [←Real.rpow_one Z]
    rw [←Real.rpow_add hZ]
    norm_num
  calc
    _ = A^(2/3:ℝ)*Z*A^(1/3:ℝ)*L^d/L^(a+k+d) := by
      rw [mul_right_comm (A^(2/3:ℝ)),ha]
    _ ≤ A^(2/3:ℝ)*Z*(Z^(2/3:ℝ)*L^a)*L^d/L^(a+k+d) := by gcongr
    _ = _ := by
      rw [pow_add,pow_add]
      field_simp
      rw [←hz]

lemma low_remainder_log_scale {L A Z M : ℝ} (hL : L ≠ 0)
    (d D k : ℕ) :
    (L^D)^4*((L^D)^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(D*(d+4)+k)) =
      M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^k := by
  rw [pow_add,←pow_mul,←pow_mul]
  rw [Nat.mul_add,pow_add]
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowLogRoot
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CubicFirstMoment

lemma low_diagonal_root_log_saving {A Z L Mα Mβ Ea Eb : ℝ}
    (hA : 0 < A) (hZ : 0 < Z) (hL : 0 < L)
    (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ) (ha : 0 ≤ Ea) (hb : 0 ≤ Eb)
    (j dα dβ a : ℕ) (hbound : A ≤ Z^2*L^(3*a))
    (hea : Ea ≤ Mα*A*L^dα) (heb : Eb ≤ Mβ*Z*L^dβ) :
    Real.sqrt (A/L^(a+2*j+dα+dβ))*Real.sqrt Ea*Real.sqrt Eb ≤
      Real.sqrt (Mα*Mβ)*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^j := by
  let J := L^(a+2*j+dα+dβ)
  let R := Real.sqrt (A/J)*Real.sqrt Ea*Real.sqrt Eb
  let V := (A/J)*Eb
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hsq : ‖(R:ℂ)‖^2 ≤ Ea*V := by
    rw [Complex.norm_real,Real.norm_of_nonneg hR]
    dsimp [R,V]
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ A/J),Real.sq_sqrt ha,Real.sq_sqrt hb]
    exact le_of_eq (by ring)
  have hmass : V ≤ Mβ*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα) := by
    calc
      V ≤ (A/J)*(Mβ*Z*L^dβ) := mul_le_mul_of_nonneg_left heb (by positivity)
      _ = Mβ*(A*Z*L^dβ/L^(a+(2*j+dα)+dβ)) := by dsimp [J]; ring
      _ ≤ Mβ*(A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα)) :=
        mul_le_mul_of_nonneg_left (low_diagonal_log_scale hA hZ hL (2*j+dα) dβ a hbound) hMβ
      _ = _ := by ring
  have hh := bilinear_error_log_saving hMα hMβ hA hZ hL j dα ha hV hsq hea hmass
  simpa only [Complex.norm_real,Real.norm_of_nonneg hR] using hh

lemma low_remainder_root_log_saving {A Z L Mα M Ea : ℝ}
    (hA : 0 < A) (hZ : 0 < Z) (hL : 0 < L)
    (hMα : 0 ≤ Mα) (ha : 0 ≤ Ea) (j dα d D : ℕ)
    (hea : Ea ≤ Mα*A*L^dα) :
    (L^D)^2*Real.sqrt ((L^D)^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(D*(d+4)+(2*j+dα)))*
      Real.sqrt Ea ≤ Real.sqrt (Mα*M^2)*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^j := by
  let Q := (L^D)^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(D*(d+4)+(2*j+dα))
  let R := (L^D)^2*Real.sqrt Q*Real.sqrt Ea
  let V := (L^D)^4*Q
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hsq : ‖(R:ℂ)‖^2 ≤ Ea*V := by
    rw [Complex.norm_real,Real.norm_of_nonneg hR]
    dsimp [R,V]
    rw [mul_pow,mul_pow,Real.sq_sqrt hQ,Real.sq_sqrt ha]
    exact le_of_eq (by ring)
  have hmass : V ≤ M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα) := by
    exact (low_remainder_log_scale hL.ne' d D (2*j+dα)).le
  have hh := bilinear_error_log_saving hMα (sq_nonneg M) hA hZ hL j dα ha hV hsq hea hmass
  simpa only [Complex.norm_real,Real.norm_of_nonneg hR] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeDivisorMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second divisor moment on primary squarefree elements, from a
finite Euler product and the already specified ordinary prime theorem. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_four_reciprocal_sum (S U : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hU : ∀ b ∈ S, primaryPrimeFactors b ⊆ U) :
    (∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card / norm b) ≤
      ∏ p ∈ U, (1+4/norm p) := by
  rw [Finset.prod_one_add]
  apply OAI.sum_le_sum_of_injOn primaryPrimeFactors
  · intro b hb c hc he
    calc
      b = ∏ p ∈ primaryPrimeFactors b, p :=
        (primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2).symm
      _ = ∏ p ∈ primaryPrimeFactors c, p := by rw [he]
      _ = c := primaryPrimeFactors_prod (hS c hc).1 (hS c hc).2
  · intro s hs
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_powerset.mpr (hU b hb)
  · intro b hb
    have hn : norm b = ∏ p ∈ primaryPrimeFactors b, norm p := by
      rw [←norm_finset_prod,primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2]
    rw [Finset.prod_div_distrib,Finset.prod_const,hn]
  · intro s hs hnot
    exact Finset.prod_nonneg (fun p _ => div_nonneg (by norm_num) (norm_nonneg p))

lemma squarefree_four_sum_le_euler (S : Finset Eisenstein) {X : ℝ}
    (hX : 0 ≤ X) (hS : ∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ X) :
    (∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card) ≤
      X*Real.exp (4*∑ p ∈ primeCutoff X, (norm p)⁻¹) := by
  have hsub : ∀ b ∈ S, primaryPrimeFactors b ⊆ primeCutoff X := by
    intro b hb p hp
    have hprime := primaryPrimeFactor_spec (hS b hb).1 hp
    exact mem_primeCutoff.mpr ⟨hprime.1,
      (norm_le_of_dvd_nonzero (primary_ne_zero (hS b hb).1) hprime.2).trans (hS b hb).2.2⟩
  have hprod : (∏ p ∈ primeCutoff X, (1+4/norm p)) ≤
      Real.exp (4*∑ p ∈ primeCutoff X, (norm p)⁻¹) := by
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      exact add_nonneg zero_le_one (div_nonneg (by norm_num) (norm_nonneg p))
    · intro p hp
      simpa only [div_eq_mul_inv,add_comm] using Real.add_one_le_exp (4*(norm p)⁻¹)
  calc
    _ ≤ ∑ b ∈ S, X*((4:ℝ)^(primaryPrimeFactors b).card/norm b) := by
      apply Finset.sum_le_sum
      intro b hb
      have hb0 := norm_pos_of_ne_zero (primary_ne_zero (hS b hb).1)
      calc
        _ = norm b*((4:ℝ)^(primaryPrimeFactors b).card/norm b) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (hS b hb).2.2 (by positivity)
    _ = X*∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card/norm b := by rw [Finset.mul_sum]
    _ ≤ X*(∏ p ∈ primeCutoff X, (1+4/norm p)) :=
      mul_le_mul_of_nonneg_left (squarefree_four_reciprocal_sum S (primeCutoff X)
        (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) hsub) hX
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod hX

theorem squarefree_divisor_second_moment (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (X : ℝ) (S : Finset Eisenstein),
      Real.exp 1 ≤ X →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ X) →
      (∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card) ≤ K*X*(1+Real.log X)^d := by
  obtain ⟨C,hC,hprime⟩ := primaryPrime_reciprocal_exp_bound hpnt
  obtain ⟨d,hd⟩ := exists_nat_ge (4*C)
  refine ⟨Real.exp (4*C),d,Real.exp_pos _,?_⟩
  intro X S hX hS
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hl : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hl0 : 0 < Real.log X := zero_lt_one.trans_le hl
  have hrec := hprime (Real.log X) hl
  rw [Real.exp_log hX0] at hrec
  have he : Real.exp (4*(C*(1+Real.log (Real.log X)))) =
      Real.exp (4*C)*(Real.log X)^(4*C) := by
    rw [Real.rpow_def_of_pos hl0,←Real.exp_add]
    congr 1
    ring
  have hpow : (Real.log X)^(4*C) ≤ (1+Real.log X)^d := by
    calc
      _ ≤ (Real.log X)^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le hl hd
      _ = (Real.log X)^d := Real.rpow_natCast _ _
      _ ≤ _ := pow_le_pow_left₀ hl0.le (by linarith : Real.log X ≤ 1+Real.log X) d
  calc
    _ ≤ X*Real.exp (4*∑ p ∈ primeCutoff X, (norm p)⁻¹) :=
      squarefree_four_sum_le_euler S hX0.le hS
    _ ≤ X*Real.exp (4*(C*(1+Real.log (Real.log X)))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hrec (by norm_num))) hX0.le
    _ = X*(Real.exp (4*C)*(Real.log X)^(4*C)) := by rw [he]
    _ ≤ X*(Real.exp (4*C)*(1+Real.log X)^d) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)) hX0.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowNormalized
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic cell width and height threshold for the low-height range. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem low_localized_integral_log_saving
    (hpnt : PrimaryPrimePNT)
    {C Mα Mβ M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ)
    (hM : 0 ≤ M) (j dα dβ a : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T H : ℝ),
      (65536:ℝ)^2 ≤ Z →
      2*Z^(3/2:ℝ) ≤ A → A ≤ Z^2*(1+Real.log Z)^(3*a) → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ H →
      (∀ n ∈ P, primary n ∧ 1 ≤ norm n/A ∧ norm n/A ≤ 2) →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ Z/2 ≤ norm n ∧ norm n ≤ Z) →
      (∀ n ∈ S, ‖β n‖ ≤ M) →
      (∑ n ∈ P, ‖α n‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ n ∈ S, ‖β n‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖h t‖ ≤ H) → (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ H) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖heightBilinearValue P S α β h X₀ T‖ ≤
        K*H*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨d,hfamily⟩ := low_localized_height_integral_bound hpnt hMV hC hHuxley
  let D := a+2*(j+1)+dα+dβ
  let q := D*(d+4)+(2*(j+1)+dα)
  obtain ⟨K,Ct,hK,hbound⟩ := hfamily q
  let B := Real.sqrt (Mα*Mβ)+Real.sqrt (Mα*M^2)
  refine ⟨2*K*(B+1),Ct+2*D,by dsimp [B]; positivity,?_⟩
  intro P S α β Z A X₀ T H hZ hA hAu hX hT hH hP hS hβ hea heb h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hL8 := low_large_log hZ
  let L := 1+Real.log Z
  let J := L^D
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hLp : 0 < L := by linarith
  have hZp : 0 < Z := by nlinarith
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  have hD1 : 1 ≤ D := by dsimp [D]; omega
  have hJ : 8 ≤ J := hL8.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 hD1)
  have hJ1 : 1 ≤ J := by linarith
  have hT0 : L^Ct ≤ T := (pow_le_pow_right₀ hL1 (by omega : Ct ≤ Ct+2*D)).trans hT
  have hTJ : J^2 ≤ T := by
    dsimp [J]
    rw [←pow_mul]
    exact (pow_le_pow_right₀ hL1 (by omega : D*2 ≤ Ct+2*D)).trans hT
  have hTp : 0 < T := (pow_pos hLp Ct).trans_le hT0
  have hJle : J ≤ T := (le_self_pow₀ hJ1 (by norm_num : 2 ≠ 0)).trans hTJ
  have hratio : J*(J/T)^2 ≤ 1 := by
    have h1 : J/T ≤ 1 := (div_le_one hTp).mpr hJle
    have h2 : J^2/T ≤ 1 := (div_le_one hTp).mpr hTJ
    have hm : (J/T)*(J^2/T) ≤ 1 := by
      calc
        _ ≤ 1*(J^2/T) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ 1 := by simpa using h2
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hdiag := low_diagonal_root_log_saving hAp hZp hLp hMα hMβ
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (j+1) dα dβ a hAu hea heb
  have herr := low_remainder_root_log_saving (M := M) hAp hZp hLp hMα
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (j+1) dα d D hea
  have hroot : Real.sqrt (A/J)*Real.sqrt (∑ n ∈ P, ‖α n‖^2)*Real.sqrt (∑ n ∈ S, ‖β n‖^2)+
      J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^q)*Real.sqrt (∑ n ∈ P, ‖α n‖^2) ≤
      B*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^j := by
    have hb := add_le_add hdiag herr
    have he : Real.sqrt (A/J)*Real.sqrt (∑ n ∈ P, ‖α n‖^2)*Real.sqrt (∑ n ∈ S, ‖β n‖^2)+
        J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^q)*Real.sqrt (∑ n ∈ P, ‖α n‖^2) ≤
        B*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^(j+1) := by
      convert hb using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [J,D,q,B,L]
      ring
    exact he.trans (div_le_div_of_nonneg_left (by dsimp [B]; positivity)
      (pow_pos hLp j) (pow_le_pow_right₀ hL1 (by omega : j ≤ j+1)))
  have hb := hbound J hJ P S α β Z A X₀ T M H hZ hA hX hT0 hM hH hP hS hβ
    h hi hd hi' hd' hi'' hh hs hh2 hs2
  apply hb.trans
  have hr := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ K*(1+J*(J/T)^2)*H by positivity)
  apply hr.trans
  have hc : K*(1+J*(J/T)^2)*B ≤ 2*K*(B+1) := by
    have hB : 0 ≤ B := by dsimp [B]; positivity
    nlinarith [mul_nonneg hK.le hB,mul_le_mul_of_nonneg_left hratio (mul_nonneg hK.le hB)]
  have hc' := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ H*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^j by positivity)
  first | (convert hc' using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hc'.trans (le_of_eq (by ring)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometry derived from a surviving term of the original stopped dyad. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguishedStoppedSide_spec {X : ℝ} {n : Eisenstein}
    (hn : n ∈ distinguishedStoppedSide X) :
    primary n ∧ Squarefree n ∧ norm n ≤ Real.exp primeProductWeights.radius*X := by
  obtain ⟨hp,hs,hnorm⟩ := Finset.mem_filter.mp hn
  exact ⟨primaryPairSupport_primary _ _
    (fun _ hh => (mem_primaryElementBall.mp hh).1)
    (fun _ hh => (mem_primaryElementBall.mp hh).1) hp,hs,hnorm⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedTailCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal of zero distinguished coefficients before the height-tail
estimate. This proves roughness of the actual remaining support and keeps
the original stopped coefficient unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguishedScaleCoefficient_as_weights (i : ℕ) (ξ X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    distinguishedScaleCoefficient i ξ X d =
      distinguishedTupleCoefficient
        (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
        (fun a p => distinguishedStoppingWeights d a (norm p))
        primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) := by
  have he : (fun a p => normPartitionWeight (2*norm p/(4/3:ℝ)^(d a).val)) =
      (fun a p => distinguishedStoppingWeights d a (norm p)) := by
    funext a p
    exact (distinguishedStoppingWeights_at d a p).symm
  unfold distinguishedScaleCoefficient
  rw [he]

lemma distinguishedScaleCoefficient_norm_le (i : ℕ) (ξ X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (r : Eisenstein) :
    ‖distinguishedScaleCoefficient i ξ X d r‖ ≤
      ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ) := by
  rw [distinguishedScaleCoefficient_as_weights]
  obtain ⟨V,_hV,hw⟩ := distinguishedStoppingWeights_uniform
  simpa only [Fintype.card_fin] using distinguishedTupleCoefficient_norm
    (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fun _ _ hp => (mem_primeCutoff.mp hp).1)
    (fun a p => distinguishedStoppingWeights d a (norm p))
    (fun a p _ => (hw i _ d).1 a (norm p))
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
    (X^ξ) (X^(2/5:ℝ)) r

lemma distinguishedStoppedRoughSupport_spec (i : ℕ) {ξ X : ℝ}
    (hX : 1 ≤ X) (hξz : ξ ≤ 2/5)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    {r : Eisenstein} (hr : r ∈ distinguishedStoppedRoughSupport i ξ X d) :
    primary r ∧ ∀ p ∈ primaryPrimeFactors r, X^ξ ≤ norm p := by
  obtain ⟨hr,hv⟩ := Finset.mem_filter.mp hr
  have hprimary := (mem_primaryElementBall.mp hr).1
  refine ⟨hprimary,?_⟩
  intro p hp
  have hpr := primaryPrimeFactor_spec hprimary hp
  rw [distinguishedScaleCoefficient_as_weights] at hv
  exact (distinguishedTupleCoefficient_prime_support
    (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fun _ _ hp => (mem_primeCutoff.mp hp).1)
    (fun a p => distinguishedStoppingWeights d a (norm p))
    (fun _ _ hx1 => primeDetectorCutoff_one hx1)
    (fun _ hx => primeDetectorCutoff_zero hx)
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hX) ξ)
    (Real.rpow_le_rpow_of_exponent_le hX hξz) hv hpr.1 hpr.2).1.le

lemma distinguishedStoppedBeta_rough_support (i : ℕ) (ρ ξ X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) :
    distinguishedStoppedBeta i ρ ξ X h early d q =
      stoppedBeta (distinguishedStoppedRoughSupport i ξ X d) (centralPrimaryFactors X)
        (distinguishedScaleCoefficient i ξ X d) primeDetectorCutoff (X^ξ)
        (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
          (geometricBinLower ρ (Real.exp primeProductWeights.radius*X))
          q.1 q.2.1 h (if early then X^(9/25:ℝ) else X^(38/100:ℝ))
          (X^(9/25:ℝ)) early) := by
  funext b
  exact (stoppedBeta_filter_nonzero _ _ _ _ _ _ b).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBStoppedAlphaEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic energy of the literal stopped outer coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_squarefree_divisor_card (E : Finset Eisenstein)
    (hE : ∀ e ∈ E, primary e) {a : Eisenstein} (ha : primary a) (hs : Squarefree a) :
    (E.filter (fun e => e ∣ a)).card ≤ 2^(primaryPrimeFactors a).card := by
  let T := E.filter (fun e => e ∣ a)
  have hcard : T.card ≤ (primaryPrimeFactors a).powerset.card := by
    apply Finset.card_le_card_of_injOn primaryPrimeFactors
    · intro e he
      apply Finset.mem_powerset.mpr
      intro p hp
      have hp' := primaryPrimeFactor_spec (hE e (Finset.mem_filter.mp he).1) hp
      exact primaryPrime_mem_factors ha hp'.1 (hp'.2.trans (Finset.mem_filter.mp he).2)
    · intro e he f hf heq
      have hes : Squarefree e := fun x hx => hs x (hx.trans (Finset.mem_filter.mp he).2)
      have hfs : Squarefree f := fun x hx => hs x (hx.trans (Finset.mem_filter.mp hf).2)
      calc
        e = ∏ p ∈ primaryPrimeFactors e, p :=
          (primaryPrimeFactors_prod (hE e (Finset.mem_filter.mp he).1) hes).symm
        _ = ∏ p ∈ primaryPrimeFactors f, p := by rw [heq]
        _ = f := primaryPrimeFactors_prod (hE f (Finset.mem_filter.mp hf).1) hfs
  exact hcard.trans_eq (Finset.card_powerset _)

theorem smallB_stopped_alpha_energy (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (E U S : Finset Eisenstein)
      (ψ : ℝ → ℝ) (w X : ℝ) (remaining : Eisenstein → Prop),
      (∀ e ∈ E, primary e) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → Real.exp 1 ≤ X →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ X) →
      (∑ a ∈ S, ‖stoppedAlpha E U ψ w remaining a‖^2) ≤ K*X*(1+Real.log X)^d := by
  obtain ⟨K,d,hK,hmoment⟩ := squarefree_divisor_second_moment hpnt
  refine ⟨K,d,hK,?_⟩
  intro E U S ψ w X remaining hE hψ hX hS
  apply le_trans _ (hmoment X S hX hS)
  apply Finset.sum_le_sum
  intro a ha
  have hb : ‖stoppedAlpha E U ψ w remaining a‖ ≤
      (2:ℝ)^(primaryPrimeFactors a).card := by
    apply (stoppedAlpha_divisor_bound E U hE hψ w remaining a).trans
    exact_mod_cast primary_squarefree_divisor_card E hE (hS a ha).1 (hS a ha).2.1
  calc
    _ ≤ ((2:ℝ)^(primaryPrimeFactors a).card)^2 :=
      pow_le_pow_left₀ (_root_.norm_nonneg _) hb 2
    _ = (4:ℝ)^(primaryPrimeFactors a).card := by
      rw [←pow_mul, Nat.mul_comm, pow_mul]
      norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBStoppedEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The energy of the actual stopped inner coefficient follows from
rough distinguished divisors and the lattice count, without any
mean-square hypothesis on the collected coefficient. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem smallB_stopped_beta_energy (R D S : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (w : ℝ) (hw : 1 ≤ w)
    (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    (selected : Eisenstein → Eisenstein → Prop) (v : Eisenstein → ℂ)
    {M Z : ℝ} (hM : 0 ≤ M) (hZ : 0 ≤ Z)
    (hv : ∀ r ∈ R, ‖v r‖ ≤ M) (k : ℕ) (hsize : Z < w^k)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ Z) :
    (∑ b ∈ S, ‖stoppedBeta R D v ψ w selected b‖^2) ≤
      18*Z*((2^k:ℕ)*M)^2 := by
  have hc := primary_support_card_le S hZ (fun b hb => ⟨(hS b hb).1,(hS b hb).2.2⟩)
  calc
    _ ≤ ∑ _b ∈ S, ((2^k:ℕ)*M)^2 := by
      apply Finset.sum_le_sum
      intro b hb
      apply pow_le_pow_left₀ (_root_.norm_nonneg _)
      exact stoppedBeta_rough_bound R D hR hψ w hw hrough selected v hM hv
        (hS b hb).1 (hS b hb).2.1 ((hS b hb).2.2.trans_lt hsize)
    _ = (S.card:ℝ)*((2^k:ℕ)*M)^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThinCellStoppedBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The thin-cell estimate for literal stopped coefficients. Their energies
are proved from the divisor moment and roughness, rather than assumed. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma outer_log_energy_conversion_cubic {A Z K : ℝ} (hA : 1 ≤ A) (hZ : 1 ≤ Z)
    (hAZ : A ≤ Z^3) (hK : 0 ≤ K) (d : ℕ) :
    K*(2*A)*(1+Real.log (2*A))^d ≤
      (2*K*(4+Real.log 2)^d)*A*(1+Real.log Z)^d := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hlA : Real.log A ≤ 3*Real.log Z := by
    have hh := Real.log_le_log hA0 hAZ
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hlZ := Real.log_nonneg hZ
  have hl2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hl : 1+Real.log (2*A) ≤ (4+Real.log 2)*(1+Real.log Z) := by
    rw [Real.log_mul (by norm_num) hA0.ne']
    nlinarith [mul_nonneg hl2 hlZ]
  have hp := pow_le_pow_left₀
    (show 0 ≤ 1+Real.log (2*A) by
      have hh := Real.log_nonneg (show 1 ≤ 2*A by linarith)
      linarith) hl d
  calc
    _ ≤ K*(2*A)*((4+Real.log 2)*(1+Real.log Z))^d :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [mul_pow]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedTailEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The height-tail estimate depends only on the actual coefficient
energies and uniform inner bound. This form permits independent norm
twists before restoring the smooth total-product envelope. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem scaleFirst_energy_cutoff_tail (hpnt : PrimaryPrimePNT)
    {C Mα Mβ M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ)
    (hM : 0 ≤ M) (n dα dβ a : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T H : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^2*(1+Real.log Z)^(3*a) → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T → 1 ≤ H → H ≤ Z^3 →
      (∀ b ∈ P, primary b ∧ 1 ≤ norm b/A ∧ norm b/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      (∑ b ∈ P, ‖α b‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ b ∈ S, ‖β b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ‖cutoffBilinearTail P S α β H T X₀‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n := by
  obtain ⟨Kh,hKh,hsecond⟩ := localizedEndpointWeight_second_uniform
  let Mh := 1+Kh
  have hMh : 0 ≤ Mh := by dsimp [Mh]; positivity
  obtain ⟨K,Ct,hK,hbound⟩ := low_localized_integral_log_saving hpnt hMV hC hHuxley
    hMα hMβ hM (n+1) dα dβ a
  obtain ⟨K₀,hK₀,hsum⟩ := height_window_sum_log_saving
  refine ⟨K₀*(2*K*Mh),Ct,by dsimp [Mh]; positivity,?_⟩
  intro P S α β Z A X₀ T H hZ hA hAu hX hT hH hHZ hP hS hβ hea heb
  have hZ1 : 1 ≤ Z := by nlinarith
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  have hT1 : 1 ≤ T := (one_le_pow₀ (by linarith [Real.log_nonneg hZ1])).trans hT
  have hf (t : ℝ) (ht : T ≤ t) (htH : t < 2*Real.pi*H) :
      ‖cutoffBilinearWindow P S α β H t X₀‖ ≤
        (2*K*Mh)*(A^(5/6:ℝ)*Z^(5/6:ℝ))/(1+Real.log Z)^(n+1) := by
    have htp : 0 < t := zero_lt_one.trans_le (hT1.trans ht)
    let w := localizedEndpointWeight H t
    have hi : Integrable w := localizedEndpointWeight_integrable H htp
    have hd : Differentiable ℝ w := (localizedEndpointWeight_smooth H htp).differentiable (by simp)
    have hder := localizedEndpointWeight_derivatives H htp
    have hw (u : ℝ) : ‖w u‖ ≤ Mh := (localizedEndpointWeight_norm_le H htp u).trans
      (by dsimp [Mh]; linarith)
    have hz (u : ℝ) (hu : u ∉ dyadicHeightSupport t) : w u = 0 :=
      localizedEndpointWeight_zero H htp u hu
    have hw2 (u : ℝ) : ‖(t:ℂ)^2*deriv (deriv w) u‖ ≤ Mh :=
      (hsecond H t (zero_lt_one.trans_le hH) htp htH.le u).trans
        (by dsimp [Mh]; linarith)
    have hz2 (u : ℝ) (hu : u ∉ dyadicHeightSupport t) : deriv (deriv w) u = 0 :=
      localizedEndpointWeight_second_zero H htp u hu
    have hb := hbound P S α β Z A X₀ t Mh hZ hA hAu hX (hT.trans ht) hMh
      hP hS hβ hea heb w hi hd hder.1 hder.2.1 hder.2.2 hw hz hw2 hz2
    have hb2 := hbound P S α β Z A (2*X₀) t Mh hZ hA hAu (by positivity)
      (hT.trans ht) hMh hP hS hβ hea heb w hi hd hder.1 hder.2.1 hder.2.2 hw hz hw2 hz2
    unfold cutoffBilinearWindow
    rw [bilinear_cutoff_window_endpoints P S α β H htp hX]
    exact (norm_sub_le _ _).trans ((add_le_add hb hb2).trans_eq (by ring))
  have hb := hsum H T Z (A^(5/6:ℝ)*Z^(5/6:ℝ)) (2*K*Mh) n
    (fun t => cutoffBilinearWindow P S α β H t X₀) hH hT1 hZ1 hHZ
    (by positivity) (by positivity) hf
  simpa only [cutoffBilinearTail,mul_assoc] using hb

theorem scaleFirst_energy_twisted_cutoff_tail (hpnt : PrimaryPrimePNT)
    {C Mα Mβ M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ)
    (hM : 0 ≤ M) (n dα dβ a : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T H : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^2*(1+Real.log Z)^(3*a) → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T → 1 ≤ H → H ≤ Z^3 →
      (∀ b ∈ P, primary b ∧ 1 ≤ norm b/A ∧ norm b/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      (∑ b ∈ P, ‖α b‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ b ∈ S, ‖β b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ → ∀ u : ℝ,
      ‖cutoffBilinearTail P S (fun b => α b*normTwist u b)
        (fun b => β b*normTwist u b) H T X₀‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n := by
  obtain ⟨K,Ct,hK,hbound⟩ := scaleFirst_energy_cutoff_tail hpnt hMV hC hHuxley
    hMα hMβ hM n dα dβ a
  refine ⟨K,Ct,hK,?_⟩
  intro P S α β Z A X₀ T H hZ hA hAu hX hT hH hHZ hP hS hβ hea heb u
  apply hbound P S _ _ Z A X₀ T H hZ hA hAu hX hT hH hHZ hP hS
  · simpa only [norm_mul,norm_normTwist,mul_one] using hβ
  · simpa only [norm_mul,norm_normTwist,mul_one] using hea
  · simpa only [norm_mul,norm_normTwist,mul_one] using heb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedTailEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-line Mellin separation of the total-product envelope in a
finite height tail. No Mellin frequency is discarded. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem envelopeCutoffBilinearTail_mellin (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (H T : ℝ) {X : ℝ} (hX : 0 < X) :
    envelopeCutoffBilinearTail P S α β W H T X =
      ∫ τ : ℝ, zeroLineMellinWeight W X τ*
        cutoffBilinearTail P S (fun a => α a*normTwist (-τ) a)
          (fun b => β b*normTwist (-τ) b) H T X := by
  let c := fun j a b => α a*β b*gauss (a*b)*
    heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow (T*(3/2:ℝ)^j) t)
      (Real.log (norm (a*b))-Real.log X)
  let f := fun j a b τ => zeroLineMellinWeight W X τ*
    (c j a b*mellinPhase (-τ) (norm (a*b)))
  have hn (a : Eisenstein) (ha : a ∈ P) (b : Eisenstein) (hb : b ∈ S) :
      0 < norm (a*b) := norm_pos_of_ne_zero
    (mul_ne_zero (primary_ne_zero (hP a ha)) (primary_ne_zero (hS b hb)))
  have hi (j : ℕ) (a : Eisenstein) (ha : a ∈ P) (b : Eisenstein) (hb : b ∈ S) :
      Integrable (f j a b) :=
    metaplectic_mellin_term_integrable W hW hpos hsm hX (hn a ha b hb) (c j a b)
  calc
    _ = ∑ j ∈ Finset.range (heightWindowCount H T),
        ∑ a ∈ P, ∑ b ∈ S, ∫ τ : ℝ, f j a b τ := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have he := metaplectic_mellin_term W hW hpos hsm hX (hn a ha b hb) (c j a b)
      simpa only [c,f,mul_assoc,mul_left_comm,mul_comm] using he
    _ = ∫ τ : ℝ, ∑ j ∈ Finset.range (heightWindowCount H T),
        ∑ a ∈ P, ∑ b ∈ S, f j a b τ := by
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum P
        (fun a ha => integrable_finsetSum S (hi j a ha)))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum P (fun a ha => integrable_finsetSum S (hi j a ha))]
      apply Finset.sum_congr rfl
      intro a ha
      exact (integral_finsetSum S (hi j a ha)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with τ
      simp only [cutoffBilinearTail,cutoffBilinearWindow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      dsimp only [f,c]
      rw [←normTwist_eq_mellinPhase,normTwist_mul (-τ)
        (primary_ne_zero (hP a ha)) (primary_ne_zero (hS b hb))]
      ring

theorem envelopeCutoffBilinearTail_bound (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (H T : ℝ) {X M : ℝ} (hX : 0 < X) (_hM : 0 ≤ M)
    (hb : ∀ u : ℝ,
      ‖cutoffBilinearTail P S (fun a => α a*normTwist u a)
        (fun b => β b*normTwist u b) H T X‖ ≤ M) :
    ‖envelopeCutoffBilinearTail P S α β W H T X‖ ≤ zeroLineMellinMass W*M := by
  let F := fun τ : ℝ => cutoffBilinearTail P S (fun a => α a*normTwist (-τ) a)
    (fun b => β b*normTwist (-τ) b) H T X
  have hc : Continuous F := by
    unfold F cutoffBilinearTail cutoffBilinearWindow normTwist
    fun_prop
  have hw := zeroLineMellinWeight_integrable W hW hpos hsm hX
  have hi : Integrable (fun τ => zeroLineMellinWeight W X τ*F τ) :=
    hw.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun τ => hb (-τ)))
  rw [envelopeCutoffBilinearTail_mellin P S α β hP hS W hW hpos hsm H T hX]
  change ‖∫ τ : ℝ, zeroLineMellinWeight W X τ*F τ‖ ≤ _
  calc
    _ ≤ ∫ τ : ℝ, ‖zeroLineMellinWeight W X τ*F τ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ τ : ℝ, ‖zeroLineMellinWeight W X τ‖*M := by
      apply integral_mono_ae hi.norm (hw.norm.mul_const M)
      filter_upwards with τ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb (-τ)) (_root_.norm_nonneg _)
    _ = (∫ τ : ℝ, ‖zeroLineMellinWeight W X τ‖)*M := integral_mul_const _ _
    _ = _ := by rw [zeroLineMellinWeight_mass W hX]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedTailTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform common norm twists for the literal stopped coefficients.
Both coefficient energies are derived before restoring the product weight. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem stopped_twisted_cutoff_tail
    (hpnt : PrimaryPrimePNT) {C M : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hM : 0 ≤ M) (n r a : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (R D E U P S : Finset Eisenstein) (ψ : ℝ → ℝ) (w Z A X₀ T H : ℝ)
        (v : Eisenstein → ℂ) (selected : Eisenstein → Eisenstein → Prop)
        (remaining : Eisenstein → Prop),
      (∀ b ∈ R, primary b) → (∀ e ∈ E, primary e) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → 1 ≤ w →
      (∀ b ∈ R, ∀ p ∈ primaryPrimeFactors b, w ≤ norm p) →
      (∀ b ∈ R, ‖v b‖ ≤ M) → Z < w^r →
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^2*(1+Real.log Z)^(3*a) → A ≤ Z^3 →
      0 < X₀ → (1+Real.log Z)^Ct ≤ T → 1 ≤ H → H ≤ Z^3 →
      (∀ e ∈ P, primary e ∧ Squarefree e ∧ 1 ≤ norm e/A ∧ norm e/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) → ∀ u : ℝ,
      ‖cutoffBilinearTail P S
        (fun b => stoppedAlpha E U ψ w remaining b*normTwist u b)
        (fun b => stoppedBeta R D v ψ w selected b*normTwist u b) H T X₀‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n := by
  obtain ⟨Ka,d,hKa,halpha⟩ := smallB_stopped_alpha_energy hpnt
  let Ma := 2*Ka*(4+Real.log 2)^d
  let Mb := 18*((2^r:ℕ)*M)^2
  let Mbeta : ℝ := (2^r:ℕ)*M
  have hMa : 0 ≤ Ma := by dsimp [Ma]; positivity
  have hMb : 0 ≤ Mb := by dsimp [Mb]; positivity
  have hMbeta : 0 ≤ Mbeta := by dsimp [Mbeta]; positivity
  obtain ⟨K,Ct,hK,hbound⟩ := scaleFirst_energy_twisted_cutoff_tail hpnt hMV hC hHuxley
    hMa hMb hMbeta n d 0 a
  refine ⟨K,Ct,hK,?_⟩
  intro R D E U P S ψ w Z A X₀ T H v selected remaining hR hE hψ hw hrough hv hsize
    hZ hA hAupper hAcubic hX hT hH hHZ hP hS u
  have hZbig : 65536 ≤ Z := by nlinarith
  have hZ1 : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have hZA : Z ≤ A := by
    calc
      Z = Z^(1:ℝ) := (Real.rpow_one Z).symm
      _ ≤ Z^(3/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
      _ ≤ A := by linarith [Real.rpow_nonneg hZp.le (3/2:ℝ)]
  have hA1 : 1 ≤ A := hZ1.trans hZA
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  have hpupper (b : Eisenstein) (hb : b ∈ P) : norm b ≤ 2*A :=
    (div_le_iff₀ hAp).mp (hP b hb).2.2.2
  have hexp : Real.exp 1 ≤ 2*A := by
    have he : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
    linarith
  have hea : (∑ b ∈ P, ‖stoppedAlpha E U ψ w remaining b‖^2) ≤
      Ma*A*(1+Real.log Z)^d := by
    apply (halpha E U P ψ w (2*A) remaining hE hψ hexp
      (fun b hb => ⟨(hP b hb).1,(hP b hb).2.1,hpupper b hb⟩)).trans
    exact outer_log_energy_conversion_cubic hA1 hZ1 hAcubic hKa.le d
  have heb : (∑ b ∈ S, ‖stoppedBeta R D v ψ w selected b‖^2) ≤
      Mb*Z*(1+Real.log Z)^0 := by
    have hh := smallB_stopped_beta_energy R D S hR hψ w hw hrough selected v hM
      hZp.le hv r hsize (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1,(hS b hb).2.2.2⟩)
    dsimp only [Mb]
    simpa only [pow_zero,mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using hh
  have hbeta : ∀ b ∈ S, ‖stoppedBeta R D v ψ w selected b‖ ≤ Mbeta := by
    intro b hb
    exact stoppedBeta_rough_bound R D hR hψ w hw hrough selected v hM hv
      (hS b hb).1 (hS b hb).2.1 ((hS b hb).2.2.2.trans_lt hsize)
  exact hbound P S (stoppedAlpha E U ψ w remaining) (stoppedBeta R D v ψ w selected)
    Z A X₀ T H hZ hA hAupper hX hT hH hHZ
    (fun b hb => ⟨(hP b hb).1,(hP b hb).2.2⟩) hS hbeta hea heb u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstTailDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prime detection on each original high-height window. The smooth
total-product envelope and the finite squarefree support are retained. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma scaleFirstTailKernel_envelope_zero (ℓ : ℤ) (H U X : ℝ) (n : Eisenstein)
    (hn : primeProductEnvelope (norm n/X) = 0) : scaleFirstTailKernel ℓ H U X n = 0 := by
  simp only [scaleFirstTailKernel,hn,mul_zero,zero_mul]

lemma scaleFirstTailKernel_norm_range (ℓ : ℤ) (H U : ℝ) {X : ℝ} (hX : 0 < X)
    {n : Eisenstein} (hn : scaleFirstTailKernel ℓ H U X n ≠ 0) :
    X/2 < norm n ∧ norm n < 3*X := by
  have henv : primeProductEnvelope (norm n/X) ≠ 0 := by
    intro hz
    exact hn (scaleFirstTailKernel_envelope_zero ℓ H U X n hz)
  constructor
  · by_contra hn
    exact henv (primeProductEnvelope_zero_lower
      ((div_le_iff₀ hX).mpr (by linarith)))
  · by_contra hn
    exact henv (primeProductEnvelope_zero
      ((le_div_iff₀ hX).mpr (by linarith)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstTailDecompositionEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal squarefree product cutoff can be removed exactly after
retaining the original smooth envelope and Gauss coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma scaleFirstTailKernel_zero_off_envelope (ℓ : ℤ) (H U : ℝ) {X : ℝ} (hX : 0 < X)
    {n : Eisenstein} (hn : primary n) (hout : n ∉ centralProductEnvelope X) :
    scaleFirstTailKernel ℓ H U X n = 0 := by
  by_cases hs : Squarefree n
  · have hsize : Real.exp primeProductWeights.radius*X < norm n := lt_of_not_ge
      (fun hnorm => hout (Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hn,hnorm⟩,hs⟩))
    apply scaleFirstTailKernel_envelope_zero
    exact primeProductWeights.upper_support () (norm n/X) ((lt_div_iff₀ hX).mpr hsize)
  · have hg : gauss n = 0 := norm_eq_zero.mp (by rw [norm_gauss hn,ite_eq_right hs])
    simp only [scaleFirstTailKernel,hg,mul_zero,zero_mul]

lemma scaleFirstTailKernel_indicator (ℓ : ℤ) (H U : ℝ) {X : ℝ} (hX : 0 < X)
    {n : Eisenstein} (hn : primary n) :
    (if n ∈ centralProductEnvelope X then scaleFirstTailKernel ℓ H U X n else 0) =
      scaleFirstTailKernel ℓ H U X n := by
  split_ifs with hm
  · rfl
  · exact (scaleFirstTailKernel_zero_off_envelope ℓ H U hX hn hm).symm

theorem scaleFirstTailStoppedDyads_envelope (i : ℕ) (ρ ξ H T : ℝ) {X : ℝ} (hX : 0 < X)
    (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      scaleFirstTailStoppedDyad i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k) =
      envelopeCutoffBilinearTail (stoppedNormDyad (distinguishedStoppedSide X) j)
        (stoppedNormDyad (distinguishedStoppedSide X) k)
        (distinguishedStoppedAlpha ρ ξ X q)
        (distinguishedStoppedBeta i ρ ξ X h early d q) primeProductEnvelope H T X := by
  unfold envelopeCutoffBilinearTail
  apply Finset.sum_congr rfl
  intro s _
  unfold scaleFirstTailStoppedDyad
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hpa := (distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1).1
  have hpb := (distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1).1
  rw [scaleFirstTailKernel_indicator 0 H _ hX (primary_mul hpa hpb)]
  simp only [scaleFirstTailKernel,theta_zero,one_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstTailDecompositionGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Surviving original height-tail dyads satisfy the true analytic length
range because their retained product envelope is nonzero. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma scaleFirstTailStoppedDyad_witness (i : ℕ) (ℓ : ℤ) (ρ ξ H U X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ)
    (hne : scaleFirstTailStoppedDyad i ℓ ρ ξ H U X h early d q j k ≠ 0) :
    ∃ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
      ∃ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
        distinguishedStoppedBeta i ρ ξ X h early d q b ≠ 0 ∧
        scaleFirstTailKernel ℓ H U X (a*b) ≠ 0 := by
  obtain ⟨a,ha,hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨b,hb,ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  refine ⟨a,ha,b,hb,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ht).1).2,?_⟩
  intro hz
  apply ht
  simp only [hz,ite_self,mul_zero]

theorem eventually_scaleFirstTailStoppedDyad_geometry {ρ ξ ε : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    (hgap : ξ+ε < 1/100) :
    ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (ℓ : ℤ) (H U : ℝ) (h : ℕ) (early : Bool)
      (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (q : ℕ × ℕ × ℕ) (j k : ℕ), 1 ≤ q.2.1 →
      scaleFirstTailStoppedDyad i ℓ ρ ξ H U X h early d q j k ≠ 0 →
      X^(7/20:ℝ) ≤ stoppedNormDyadLength k ∧
      stoppedNormDyadLength k ≤ X^(39/100:ℝ) ∧
      stoppedNormDyadLength k ≤ X ∧
      X/16 ≤ (stoppedNormDyadLength j/2)*stoppedNormDyadLength k ∧
      (stoppedNormDyadLength j/2)*stoppedNormDyadLength k ≤ 16*X ∧
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ q.1 := by
  filter_upwards [eventually_two_stage_stopped_dyad_range_dilation
    (Real.exp_pos primeProductWeights.radius) hgap,eventually_ge_atTop (1:ℝ)] with X hr hX
  intro i ℓ H U h early d q j k hk hne
  obtain ⟨a,ha,b,hb,hβ,hK⟩ := scaleFirstTailStoppedDyad_witness i ℓ ρ ξ H U X h early d q j k hne
  have has := distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1
  have hbs := distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1
  have hab := stoppedNormDyad_outer_bounds ha has.1
  have hbb := stoppedNormDyad_outer_bounds hb hbs.1
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hXF : X ≤ Real.exp primeProductWeights.radius*X :=
    le_mul_of_one_le_left hXp.le (Real.one_le_exp primeProductWeights.radius_nonneg)
  have hsize := stoppedBeta_norm_bounds (centralPrimaryFactors X) (centralPrimaryFactors X)
    (distinguishedScaleCoefficient i ξ X d) (fun x hx => primeDetectorCutoff_zero hx)
    hρ hρ₂ hε hsmall
    (show 0 < (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) by split <;> positivity)
    (Real.rpow_pos_of_pos hXp ξ)
    (fun n hn => mem_primaryElementBall.mp hn) hk early hbs.2.1 hβ
  have hZ : (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) = X^(36/100:ℝ) ∨
      (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) = X^(38/100:ℝ) := by
    cases early <;> norm_num
  have hBr := hr (stoppedNormDyadLength k) _ (norm b) hZ hsize.1 hsize.2 hbb.1 hbb.2
  have hBX : stoppedNormDyadLength k ≤ X := hBr.2.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (show (39/100:ℝ) ≤ 1 by norm_num))
  have hKR := scaleFirstTailKernel_norm_range ℓ H U hXp hK
  have hprod := stopped_dyad_product_range
    (div_nonneg (stoppedNormDyadLength_pos j).le (by norm_num))
    (stoppedNormDyadLength_pos k).le
    (show stoppedNormDyadLength j/2 ≤ norm a ∧ norm a ≤ 2*(stoppedNormDyadLength j/2) by
      constructor
      · exact hab.1
      · nlinarith [hab.2]) hbb ⟨hKR.1.le,hKR.2.le⟩
  refine ⟨by simpa only [show (35/100:ℝ)=7/20 by norm_num] using hBr.1,
    hBr.2,hBX,by linarith [hprod.1],by linarith [hprod.2],?_⟩
  exact stoppedBeta_label_shift_bound _ _ _ _ _ hρ hXp hXF
    (fun n hn => (mem_primaryElementBall.mp hn).1) hbs.1 (hbb.2.trans hBX) hk early hβ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedTailBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original enveloped stopped height tail, including every window
and the entire product Mellin line, has arbitrary logarithmic saving. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem distinguishedStoppedEnvelopeTail_bound_oai (i : ℕ)
    (hpnt : PrimaryPrimePNT) {C ξ ρ ε : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100) (n : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H T : ℝ) (h : ℕ) (early : Bool)
        (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ) (j k : ℕ),
      (1+Real.log X)^Ct ≤ T → 1 ≤ H → H ≤ X → 1 ≤ q.2.1 →
      ‖∑ s ∈ Finset.range (heightWindowCount H T),
        scaleFirstTailStoppedDyad i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨r,hr⟩ := exists_nat_gt (1/ξ)
  have hξr : 1 < ξ*r := by
    have he := (div_lt_iff₀ hξ).mp hr
    simpa only [mul_comm] using he
  let M : ℝ := ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨K,Ct,hK,hbound⟩ := stopped_twisted_cutoff_tail hpnt hMV hC hHuxley hM n r 0
  let c := zeroLineMellinMass primeProductEnvelope
  have hc : 0 ≤ c := by
    dsimp [c,zeroLineMellinMass]
    exact mul_nonneg (by positivity) (integral_nonneg (fun _ => _root_.norm_nonneg _))
  refine ⟨(K*(1+c))*(16:ℝ)^(5/6:ℝ)*(20/7:ℝ)^n,Ct,by positivity,?_⟩
  filter_upwards [eventually_stopped_actual_range 0,
    eventually_scaleFirstTailStoppedDyad_geometry hρ hρ₂ hε hsmall hgap,
    eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 7/20)).eventually_ge_atTop
      ((65536:ℝ)^2)] with X hrange hgeom hX hlarge
  intro H T h early d q j k hT hH hHX hk
  have hXp : 0 < X := zero_lt_one.trans hX
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_pos hX]
  by_cases hz : (∑ s ∈ Finset.range (heightWindowCount H T),
      scaleFirstTailStoppedDyad i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k) = 0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨s,_hs,hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  obtain ⟨hBlo,hBhi,_hBX,hprodlo,hprodhi,_hq⟩ :=
    hgeom i 0 H (T*(3/2:ℝ)^s) h early d q j k hk hs
  let A := stoppedNormDyadLength j/2
  let B := stoppedNormDyadLength k
  have hAp : 0 < A := by dsimp [A]; positivity [stoppedNormDyadLength_pos j]
  have hBp : 0 < B := stoppedNormDyadLength_pos k
  have hB1 : 1 ≤ B :=
    (Real.one_le_rpow hX.le (by norm_num : (0:ℝ) ≤ 7/20)).trans hBlo
  have hBX : B ≤ X := hBhi.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (39/100:ℝ) ≤ 1))
  have hBlarge : (65536:ℝ)^2 ≤ B := hlarge.trans hBlo
  obtain ⟨hAlow,hAhigh⟩ := hrange A B hprodlo hprodhi hBlo hBhi
  have hA2 : A ≤ B^2 := by simpa only [pow_zero,div_one] using hAhigh
  have hA3 : A ≤ B^3 := hA2.trans (pow_le_pow_right₀ hB1 (by omega))
  have hXB3 : X ≤ B^3 := by
    have he := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le (7/20:ℝ)) hBlo 3
    rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le] at he
    norm_num only [show (7/20:ℝ)*(3:ℕ) = 21/20 by norm_num] at he
    apply le_trans _ he
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (1:ℝ) ≤ 21/20)
  have hsize : B < (X^ξ)^r := by
    calc
      B ≤ X := hBX
      _ < X^(ξ*r) := by
        simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hX hξr
      _ = (X^ξ)^r := by rw [←Real.rpow_mul_natCast hXp.le]
  have hT' : (1+Real.log B)^Ct ≤ T := by
    apply le_trans _ hT
    exact pow_le_pow_left₀ (by linarith [Real.log_nonneg hB1])
      (by linarith [Real.log_le_log hBp hBX]) Ct
  have hP (a : Eisenstein) (ha : a ∈ stoppedNormDyad (distinguishedStoppedSide X) j) :
      primary a ∧ Squarefree a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2 := by
    have hp := distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1
    have hn := stoppedNormDyad_outer_bounds ha hp.1
    refine ⟨hp.1,hp.2.1,(one_le_div hAp).mpr hn.1,?_⟩
    apply (div_le_iff₀ hAp).mpr
    dsimp [A]
    nlinarith [hn.2]
  have hQ (b : Eisenstein) (hb : b ∈ stoppedNormDyad (distinguishedStoppedSide X) k) :
      primary b ∧ Squarefree b ∧ B/2 ≤ norm b ∧ norm b ≤ B := by
    have hp := distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1
    have hn := stoppedNormDyad_outer_bounds hb hp.1
    exact ⟨hp.1,hp.2.1,hn.1,hn.2⟩
  have hb := hbound (distinguishedStoppedRoughSupport i ξ X d)
    (centralPrimaryFactors X) (centralPrimaryFactors X) (centralPrimaryFactors X)
    (stoppedNormDyad (distinguishedStoppedSide X) j)
    (stoppedNormDyad (distinguishedStoppedSide X) k)
    primeDetectorCutoff (X^ξ) B A X T H (distinguishedScaleCoefficient i ξ X d)
    (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.1 h
      (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) (X^(9/25:ℝ)) early)
    (stoppingRemainingTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
      q.1 q.2.2)
    (fun a ha => (distinguishedStoppedRoughSupport_spec i hX.le hξz d ha).1)
    (fun a ha => (mem_primaryElementBall.mp ha).1)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
    (Real.one_le_rpow hX.le hξ.le)
    (fun a ha => (distinguishedStoppedRoughSupport_spec i hX.le hξz d ha).2)
    (fun a _ => distinguishedScaleCoefficient_norm_le i ξ X d a)
    hsize hBlarge hAlow (by simpa only [mul_zero,pow_zero,mul_one] using hA2)
    hA3 hXp hT' hH (hHX.trans hXB3) hP hQ
  have hb' : ∀ u : ℝ, ‖cutoffBilinearTail
      (stoppedNormDyad (distinguishedStoppedSide X) j)
      (stoppedNormDyad (distinguishedStoppedSide X) k)
      (fun a => distinguishedStoppedAlpha ρ ξ X q a*normTwist u a)
      (fun b => distinguishedStoppedBeta i ρ ξ X h early d q b*normTwist u b) H T X‖ ≤
      K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^n := by
    rw [distinguishedStoppedBeta_rough_support]
    exact hb
  rw [scaleFirstTailStoppedDyads_envelope i ρ ξ H T hXp h early d q j k]
  have hLB : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  apply (envelopeCutoffBilinearTail_bound _ _ _ _
    (fun a ha => (hP a ha).1) (fun b hb => (hQ b hb).1)
    primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth H T hXp (by positivity) hb').trans
  have hlog : 1+Real.log X ≤ (20/7:ℝ)*(1+Real.log B) := by
    have he := Real.log_le_log (Real.rpow_pos_of_pos hXp (7/20:ℝ)) hBlo
    rw [Real.log_rpow hXp] at he
    nlinarith
  have hden : (1+Real.log X)^n ≤ (20/7:ℝ)^n*(1+Real.log B)^n := by
    simpa only [mul_pow] using pow_le_pow_left₀ hLX.le hlog n
  have hscale : A^(5/6:ℝ)*B^(5/6:ℝ) ≤ (16:ℝ)^(5/6:ℝ)*X^(5/6:ℝ) := by
    rw [←Real.mul_rpow hAp.le hBp.le,←Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16) hXp.le]
    exact Real.rpow_le_rpow (mul_nonneg hAp.le hBp.le) hprodhi (by norm_num)
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos hLB n) (pow_pos hLX n)).mpr
  calc
    c*(K*A^(5/6:ℝ)*B^(5/6:ℝ))*(1+Real.log X)^n ≤
        (1+c)*(K*((16:ℝ)^(5/6:ℝ)*X^(5/6:ℝ)))*
          ((20/7:ℝ)^n*(1+Real.log B)^n) := by
      apply mul_le_mul _ hden (pow_nonneg hLX.le n) (by positivity)
      calc
        c*(K*A^(5/6:ℝ)*B^(5/6:ℝ)) ≤ (1+c)*(K*A^(5/6:ℝ)*B^(5/6:ℝ)) := by
          apply mul_le_mul_of_nonneg_right (by linarith)
          positivity
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale hK.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.distinguishedStoppedEnvelopeTail_bound_oai := @OAI.CubicFirstMoment.distinguishedStoppedEnvelopeTail_bound_oai
