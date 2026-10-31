-- Prove2me | solution 1 for OAI.CubicFirstMoment.cubicTheta_radial_scaleFirstOrdinaryNoStopTail_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:33:43.627845+00:00
-- url     : https://prove2.me/submissions/535f887d-5e5f-418b-8f99-8b515bea3246

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A016
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_UniformLogWeights_cubicTheta_completed_signed_radial_mean

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
-- module Solutions.OAIQ096_CM.CubicGram_CommonFactors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moebius removal of common factors and coprime Gram decomposition. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_subsets_prod_dvd {k : Eisenstein} (hk : primary k)
    {s : Finset Eisenstein} (hs : s ⊆ primaryPrimeFactors k) (n : Eisenstein) :
    (∏ p ∈ s, p) ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  constructor
  · intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp) h
  · intro h
    apply Finset.prod_dvd_of_coprime _ h
    intro p hp q hq hpq
    exact primaryPrimes_isCoprime (primaryPrimeFactor_spec hk (hs hp)).1
      (primaryPrimeFactor_spec hk (hs hq)).1 hpq

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
-- module Solutions.OAIQ096_CM.CubicGram_SieveMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

private lemma finiteIdealMoebius_coeff_repeated (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) {q : EisensteinIdealPrime} (hνq : 2 ≤ ν q) :
    MvPowerSeries.coeff ν (finiteIdealMoebius S) = 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty =>
    have hν : ν ≠ 0 := by
      intro h
      have hq := congrArg (fun f : EisensteinIdealExponent => f q) h
      simp only [Finsupp.zero_apply] at hq
      omega
    simp [finiteIdealMoebius, MvPowerSeries.coeff_one, hν]
  | @insert p S hp ih =>
    have he : finiteIdealMoebius (insert p S) =
        finiteIdealMoebius S * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, coeff_mul_one_sub_X]
    by_cases hqp : q = p
    · subst q
      rw [finiteIdealMoebius_coeff_outside S ν hp (by omega),
        ite_eq_left (by omega), finiteIdealMoebius_coeff_outside S _ hp]
      · simp
      · simpa only [Finsupp.tsub_apply, Finsupp.single_eq_same] using
          (show ν p - 1 ≠ 0 by omega)
    · rw [ih ν hνq]
      by_cases hn : 1 ≤ ν p
      · rw [ite_eq_left hn, ih _]
        · simp
        · simpa [Finsupp.tsub_apply, hqp] using hνq
      · simp [hn]

lemma idealMoebiusSeries_repeated {ν : EisensteinIdealExponent}
    {p : EisensteinIdealPrime} (hν : 2 ≤ ν p) :
    MvPowerSeries.coeff ν idealMoebiusSeries = 0 := by
  rw [coeff_idealMoebiusSeries_eq_finite ν.support ν (Finset.Subset.refl _)]
  exact finiteIdealMoebius_coeff_repeated _ _ hν

private lemma finiteIdealMoebius_coeff_squarefree (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) (hν : ν.support ⊆ S) (h1 : ∀ p, ν p ≤ 1) :
    MvPowerSeries.coeff ν (finiteIdealMoebius S) = (-1 : ℝ) ^ ν.support.card := by
  induction S using Finset.induction_on generalizing ν with
  | empty =>
    have hz : ν = 0 := Finsupp.support_eq_empty.mp (Finset.subset_empty.mp hν)
    simp [hz, finiteIdealMoebius, MvPowerSeries.coeff_one]
  | @insert p S hp ih =>
    have he : finiteIdealMoebius (insert p S) =
        finiteIdealMoebius S * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, coeff_mul_one_sub_X]
    by_cases hz : ν p = 0
    · have hs : ν.support ⊆ S := by
        intro q hq
        rcases Finset.mem_insert.mp (hν hq) with h | h
        · subst q
          exact (Finsupp.mem_support_iff.mp hq hz).elim
        · exact h
      simpa [hz] using ih ν hs h1
    · have ho : ν p = 1 := by have := h1 p; omega
      let κ : EisensteinIdealExponent := ν - Finsupp.single p 1
      have hk : κ.support = ν.support.erase p := by
        ext q
        by_cases hqp : q = p
        · subst q
          simp [κ, Finsupp.mem_support_iff, Finsupp.tsub_apply, ho]
        · simp [κ, Finsupp.mem_support_iff, Finsupp.tsub_apply, hqp]
      have hκ : κ.support ⊆ S := by
        rw [hk]
        intro q hq
        rcases Finset.mem_erase.mp hq with ⟨hqp, hq⟩
        exact (Finset.mem_insert.mp (hν hq)).resolve_left hqp
      have hκ1 : ∀ q, κ q ≤ 1 := fun q =>
        (Nat.sub_le (ν q) _).trans (h1 q)
      have hcard : κ.support.card + 1 = ν.support.card := by
        rw [hk]
        exact Finset.card_erase_add_one (Finsupp.mem_support_iff.mpr hz)
      rw [finiteIdealMoebius_coeff_outside S ν hp hz, ite_eq_left (by omega),
        ih κ hκ hκ1, zero_sub, ← hcard, pow_succ]
      ring

lemma idealMoebiusSeries_squarefree {ν : EisensteinIdealExponent}
    (h1 : ∀ p, ν p ≤ 1) :
    MvPowerSeries.coeff ν idealMoebiusSeries = (-1 : ℝ) ^ ν.support.card := by
  rw [coeff_idealMoebiusSeries_eq_finite ν.support ν (Finset.Subset.refl _)]
  exact finiteIdealMoebius_coeff_squarefree _ _ (Finset.Subset.refl _) h1

lemma idealExponentOf_support_card {a : Eisenstein} (ha : Squarefree a) :
    (idealExponentOf a).support.card = (UniqueFactorizationMonoid.factors a).card := by
  have hnodup : (Associates.factors' a).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    exact (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha
  change (Associates.factors' a).toFinset.card = _
  rw [Multiset.toFinset_card_of_nodup hnodup]
  have h := congrArg Multiset.card (Associates.map_subtype_coe_factors' (a := a))
  simpa only [Multiset.card_map] using h

/-- The Dirichlet-inverse definition agrees with the repository's
arithmetic Möbius function on every nonzero Eisenstein ideal. -/
lemma idealMoebiusSeries_at_element {a : Eisenstein} (ha : a ≠ 0) :
    MvPowerSeries.coeff (idealExponentOf a) idealMoebiusSeries = (idealMoebius a : ℝ) := by
  by_cases hs : Squarefree a
  · rw [idealMoebiusSeries_squarefree ((idealExponentOf_squarefree_iff ha).mpr hs),
      idealExponentOf_support_card hs]
    simp [idealMoebius, hs]
  · have hh : ¬ ∀ p, idealExponentOf a p ≤ 1 :=
      mt (idealExponentOf_squarefree_iff ha).mp hs
    push Not at hh
    obtain ⟨p, hp⟩ := hh
    rw [idealMoebiusSeries_repeated (by omega : 2 ≤ idealExponentOf a p)]
    simp [idealMoebius, hs]

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primary_divisors_eq_subset_products (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) {e : Eisenstein}
    (he : primary e) (hcomplete : ∀ c, primary c → Squarefree c → c ∣ e → c ∈ C) :
    C.filter (· ∣ e) = (primaryPrimeFactors e).powerset.image (fun s => ∏ p ∈ s, p) := by
  ext c
  constructor
  · intro hc
    obtain ⟨hc,hce⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_image.mpr ⟨primaryPrimeFactors c,
      Finset.mem_powerset.mpr (primaryPrimeFactors_subset_of_dvd (hC c hc).1 he hce),
      primaryPrimeFactors_prod (hC c hc).1 (hC c hc).2⟩
  · intro hc
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hc
    have hsub := Finset.mem_powerset.mp hs
    have hsp : ∀ p ∈ s, primaryPrime p := fun p hp => (primaryPrimeFactor_spec he (hsub hp)).1
    have hp := primary_finset_prod s (fun p : Eisenstein => p) (fun p hp => (hsp p hp).1)
    have hd : (∏ p ∈ s, p) ∣ e :=
      (primary_subsets_prod_dvd he hsub e).mpr (fun p hp => (primaryPrimeFactor_spec he (hsub hp)).2)
    exact Finset.mem_filter.mpr ⟨hcomplete _ hp (primaryPrime_product_squarefree s hsp) hd,hd⟩

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal primary-divisor Möbius expansion used in the small-R
branch, and its exact splitting at a prime bin. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_divisors_of_squarefree_eq {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    metaplecticPrimaryDivisors n =
      (primaryPrimeFactors n).powerset.image (fun s => ∏ p ∈ s, p) := by
  let C := metaplecticPrimaryDivisors n
  have hC (c : Eisenstein) (hc : c ∈ C) : primary c ∧ Squarefree c := by
    have hm := Finset.mem_filter.mp hc
    exact ⟨(mem_primaryElementBall.mp hm.1).1,fun x hx => hs x (hx.trans hm.2)⟩
  have hcomplete (c : Eisenstein) (hc : primary c) (_hs : Squarefree c) (hd : c ∣ n) : c ∈ C := by
    apply Finset.mem_filter.mpr
    exact ⟨mem_primaryElementBall.mpr ⟨hc,norm_le_of_dvd_nonzero (primary_ne_zero hn) hd⟩,hd⟩
  have he := primary_divisors_eq_subset_products C hC hn hcomplete
  have hf : C.filter (· ∣ n) = C := by
    apply Finset.filter_true_of_mem
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  rwa [hf] at he

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

lemma primaryPairCoefficient_sum (S T : Finset Eisenstein)
    (w : Eisenstein × Eisenstein → ℂ) (F : Eisenstein → ℂ) :
    (∑ b ∈ primaryPairSupport S T, primaryPairCoefficient S T w b*F b) =
      ∑ p ∈ S ×ˢ T, w p*F (p.1*p.2) := by
  unfold primaryPairCoefficient primaryPairFiber
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ b ∈ primaryPairSupport S T,
        ∑ p ∈ S ×ˢ T with p.1*p.2 = b, w p*F (p.1*p.2) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image_of_mem _ hp) _

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

/-- A fixed ratio larger than one can be chosen so that all selected
subproducts in every squarefree envelope have distortion at most
X^(kappa/4). No bin occupancy vector is enumerated. -/
theorem uniform_prime_bin_distortion {κ C : ℝ} (hκ : 0 < κ) (hC : 0 < C) :
    ∃ ρ : ℝ, 1 < ρ ∧ ∀ᶠ X : ℝ in atTop,
      ∀ n : Eisenstein, primary n → Squarefree n → norm n ≤ C*X →
      ∀ s : Finset Eisenstein, s ⊆ primaryPrimeFactors n →
      ∀ (b : Eisenstein → ℕ) (ell : ℕ → ℝ),
        (∀ p ∈ s, 0 ≤ ell (b p) ∧ ell (b p) ≤ norm p ∧ norm p ≤ ρ*ell (b p)) →
      primeSurrogate s b ell ≤ norm (∏ p ∈ s, p) ∧
        norm (∏ p ∈ s, p) ≤ X^(κ/4)*primeSurrogate s b ell := by
  let δ : ℝ := κ/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let ρ : ℝ := (2:ℝ)^δ
  have hρ : 1 < ρ := Real.one_lt_rpow (by norm_num) hδ
  refine ⟨ρ,hρ,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),
    eventually_const_mul_rpow_le (show δ < κ/4 by dsimp [δ]; linarith) (C^δ)] with X hX hbound
  intro n hn hs hnX s hsub b ell hcell
  have hpow : ρ^s.card ≤ X^(κ/4) := by
    calc
      _ = ((2:ℝ)^s.card)^δ := by
        dsimp [ρ]
        rw [←Real.rpow_mul_natCast (by norm_num),←Real.rpow_natCast_mul (by norm_num),mul_comm]
      _ ≤ (C*X)^δ := Real.rpow_le_rpow (by positivity)
        ((primary_prime_subset_two_pow_le hn hs hsub).trans hnX) hδ.le
      _ = C^δ*X^δ := Real.mul_rpow hC.le hX.le
      _ ≤ _ := hbound
  obtain ⟨hlo,hhi⟩ := primeSurrogate_norm_bounds s b ell (zero_lt_one.trans hρ).le hcell
  exact ⟨hlo,hhi.trans (mul_le_mul_of_nonneg_right hpow
    (Finset.prod_nonneg (fun p hp => (hcell p hp).1)))⟩

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

theorem geometricBinCount_log_bound {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ B : ℝ, 1 ≤ B →
      (geometricBinCount ρ B:ℝ) ≤ K*(1+Real.log B) := by
  let K : ℝ := 1+(Real.log ρ)⁻¹
  have hr : 0 < Real.log ρ := Real.log_pos hρ
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro B hB
  have hl : 0 ≤ Real.log B := Real.log_nonneg hB
  have hi : 0 < (Real.log ρ)⁻¹ := inv_pos.mpr hr
  have h := (Nat.ceil_lt_add_one (div_nonneg hl hr.le)).le
  change (geometricBinCount ρ B:ℝ) ≤ _ at h
  apply h.trans
  dsimp [K]
  rw [div_eq_mul_inv]
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_NoStopSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The no-stop coefficient is genuinely supported on short outer levels.
This follows from the previously proved geometric distortion estimate. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_ne_zero_squarefree {ψ : ℝ → ℝ} {w : ℝ} {m : Eisenstein}
    (hm : cutoffMoebius ψ w m ≠ 0) : Squarefree m := by
  by_contra hs
  exact hm (by simp [cutoffMoebius,idealMoebius,UniqueFactorizationMonoid.moebius,hs])

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryProductCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of ideal convolution coefficients with the finite
fibres of products of primary Eisenstein elements. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealExponentOf_primary_prod {ι : Type*} (S : Finset ι) (n : ι → Eisenstein)
    (hn : ∀ i ∈ S, primary (n i)) :
    idealExponentOf (∏ i ∈ S, n i) = ∑ i ∈ S, idealExponentOf (n i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,Finset.sum_empty]
    simpa [idealExponentGenerator] using idealExponentOf_generator (0 : EisensteinIdealExponent)
  | @insert i S hi ih =>
    have hS : ∀ j ∈ S, primary (n j) := fun j hj => hn j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,Finset.sum_insert hi,
      idealExponentOf_mul (primary_ne_zero (hn i (Finset.mem_insert_self _ _)))
        (primary_ne_zero (primary_finset_prod S n hS)),ih hS]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coeff_product_primary_fiber {R : Type*} [CommSemiring R]
    (A : ι → MvPowerSeries EisensteinIdealPrime R)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i) =
      ∑ n ∈ (Fintype.piFinset (fun _ : ι => primaryElementBall F)).filter
        (fun n => (∏ i, n i) = b), ∏ i, MvPowerSeries.coeff (idealExponentOf (n i)) (A i) := by
  rw [MvPowerSeries.coeff_prod]
  let g : (ι →₀ EisensteinIdealExponent) → ι → Eisenstein :=
    fun l i => idealPrimaryGenerator (l i)
  have hle (l : ι →₀ EisensteinIdealExponent)
      (hl : l ∈ Finset.finsuppAntidiag Finset.univ (idealExponentOf b)) (i : ι) :
      l i ≤ idealExponentOf b := by
    rw [← (Finset.mem_finsuppAntidiag.mp hl).1]
    exact Finset.single_le_sum (fun j _ => (show 0 ≤ l j from zero_le)) (Finset.mem_univ i)
  have hg (l : ι →₀ EisensteinIdealExponent)
      (hl : l ∈ Finset.finsuppAntidiag Finset.univ (idealExponentOf b)) :
      ∀ i, primary (g l i) := fun i => idealPrimaryGenerator_primary hb (hle l hl i)
  apply Finset.sum_bij (fun l _ => g l)
  · intro l hl
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => mem_primaryElementBall.mpr ⟨hg l hl i,?_⟩),?_⟩
    · rw [idealPrimaryGenerator_norm]
      exact ((idealExponentNorm_mono (hle l hl i)).trans_eq
        (idealExponentOf_norm (primary_ne_zero hb))).trans hbF
    · apply primary_eq_of_idealExponentOf_eq (primary_finset_prod _ _ (fun i _ => hg l hl i)) hb
      rw [idealExponentOf_primary_prod _ _ (fun i _ => hg l hl i)]
      simpa only [g,idealExponentOf_primaryGenerator] using (Finset.mem_finsuppAntidiag.mp hl).1
  · intro l _ m _ h
    apply Finsupp.ext
    intro i
    have hi := congrArg idealExponentOf (congrFun h i)
    simpa only [g,idealExponentOf_primaryGenerator] using hi
  · intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hnp (i : ι) : primary (n i) :=
      (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hmem.1) i)).1
    let l : ι →₀ EisensteinIdealExponent :=
      Finsupp.onFinset Finset.univ (fun i => idealExponentOf (n i)) (by simp)
    have hli (i : ι) : l i = idealExponentOf (n i) := rfl
    refine ⟨l,Finset.mem_finsuppAntidiag.mpr ⟨?_,Finset.subset_univ _⟩,?_⟩
    · simp_rw [hli]
      rw [← idealExponentOf_primary_prod _ _ (fun i _ => hnp i),hmem.2]
    · funext i
      exact idealPrimaryGenerator_at_element (hnp i)
  · intro l _
    apply Finset.prod_congr rfl
    intro i _
    simp only [g,idealExponentOf_primaryGenerator]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PowerSavings
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Power savings at the first-moment scale

A fixed power saving is smaller than `X^(5/6) / log X`.  This is the
analytic bookkeeping used for the short-range and truncation errors in
the sharp-cutoff argument.
-/

noncomputable section

open Filter Asymptotics

namespace CubicFirstMoment

/-- Any fixed positive power saving is negligible at the asserted scale. -/
theorem powerSaving_isLittleO {δ : ℝ} (hδ : 0 < δ) :
    (fun X : ℝ => X ^ (5 / 6 - δ : ℝ)) =o[atTop] firstMomentScale := by
  let multiplier : ℝ → ℝ := fun X => X ^ (5 / 6 - δ : ℝ) / Real.log X
  have h := (isLittleO_log_rpow_atTop hδ).mul_isBigO
    (isBigO_refl multiplier atTop)
  apply h.congr'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    dsimp [multiplier]
    field_simp [(Real.log_pos hX).ne']
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    dsimp [multiplier, firstMomentScale]
    rw [← mul_div_assoc, ← Real.rpow_add (by linarith : 0 < X)]
    congr 2
    ring

/-- A bound with a fixed power saving implies the required little-oh
bound for any normed target space. -/
theorem isLittleO_of_powerSaving {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {δ : ℝ} (hδ : 0 < δ)
    (hf : f =O[atTop] (fun X : ℝ => X ^ (5 / 6 - δ : ℝ))) :
    f =o[atTop] firstMomentScale :=
  hf.trans_isLittleO (powerSaving_isLittleO hδ)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrimalFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact support turns the literal completed sum, at every translated
height, into the finite primary cube polynomial used by Montgomery--Vaughan. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticPrimaryPair_injective : Function.Injective metaplecticPrimaryPair := by
  intro du ev h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

lemma metaplecticPrimalSupport_of_nonzero {r : Eisenstein} (ℓ : ℤ)
    (W : ℝ → ℂ) {X B V : ℝ} (hX : 0 < X) (hBV : B*X ≤ V)
    (hW : ∀ x : ℝ, B < x → W x = 0) (du : PrimaryArgument × PrimaryArgument)
    (hn : metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du) ≠ 0) :
    du ∈ metaplecticPrimalSupport V := by
  have hnW : W (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))/X) ≠ 0 := by
    intro hh
    exact hn (by simp [metaplecticPrimalCoefficient,hh])
  have hsize : norm (metaplecticCubeProduct (metaplecticPrimaryPair du)) ≤ V := by
    have hb : norm (metaplecticCubeProduct (metaplecticPrimaryPair du)) ≤ B*X := by
      by_contra h
      exact hnW (hW _ ((lt_div_iff₀ hX).mpr (lt_of_not_ge h)))
    exact hb.trans hBV
  have hcube : primary ((du.1:Eisenstein)^3) := by
    simpa only [pow_succ,pow_zero,one_mul] using
      primary_mul (primary_mul du.1.property du.1.property) du.1.property
  have hp : primary (metaplecticCubeProduct (metaplecticPrimaryPair du)) :=
    primary_mul du.2.property hcube
  have hd : (du.1:Eisenstein) ∣ metaplecticCubeProduct (metaplecticPrimaryPair du) :=
    (dvd_pow_self du.1.val (by norm_num : (3:ℕ) ≠ 0)).trans (dvd_mul_left _ _)
  have hu : (du.2:Eisenstein) ∣ metaplecticCubeProduct (metaplecticPrimaryPair du) := dvd_mul_right _ _
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hsize⟩
  · apply Finset.mem_subtype.mpr
    exact mem_primaryElementBall.mpr ⟨du.1.property,(norm_le_of_dvd (primary_ne_zero hp) hd).trans hsize⟩
  · apply Finset.mem_subtype.mpr
    exact mem_primaryElementBall.mpr ⟨du.2.property,(norm_le_of_dvd (primary_ne_zero hp) hu).trans hsize⟩

/-- Exact finite support, independent of the height parameter. -/
theorem metaplecticHeightCompleted_finite (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {X B V : ℝ} (hX : 0 < X) (hBV : B*X ≤ V)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    metaplecticHeightCompleted r ℓ W X t =
      ∑ du ∈ metaplecticPrimalElementSupport V,
        metaplecticPrimalCoefficient r ℓ W X du*mellinPhase t (norm (metaplecticCubeProduct du)) := by
  rw [metaplecticHeightCompleted,tsum_eq_sum (s := metaplecticPrimalSupport V) (fun du hdu => ?_)]
  · rw [metaplecticPrimalElementSupport,Finset.sum_image]
    exact fun _ _ _ _ h => metaplecticPrimaryPair_injective h
  · have hc : metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du) = 0 := by
      by_contra hn
      exact hdu (metaplecticPrimalSupport_of_nonzero ℓ W hX hBV hW du hn)
    rw [hc,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIOuter
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite level summation of the uniform Type-I estimate. The actual
Gauss sum removes nonsquarefree levels, and the coefficient mass remains
explicit. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma dyadic_finite_norm_sum {α : Type*} (S : Finset α) (a : α → ℂ)
    (f : α → ℝ → ℂ) (hf : ∀ i ∈ S, Continuous (f i)) (T : ℝ) :
    ((∫ t in T..2*T, ∑ i ∈ S, ‖a i‖*‖f i t‖)+
     (∫ t in -(2*T)..(-T), ∑ i ∈ S, ‖a i‖*‖f i t‖))/T =
      ∑ i ∈ S, ‖a i‖*((∫ t in T..2*T, ‖f i t‖)+
        (∫ t in -(2*T)..(-T), ‖f i t‖))/T := by
  rw [intervalIntegral.integral_finsetSum,intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul]
    rw [← Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro i hi
    exact (continuous_const.mul (hf i hi).norm).intervalIntegrable _ _
  · intro i hi
    exact (continuous_const.mul (hf i hi).norm).intervalIntegrable _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The length and level powers in the Type-I height estimate. -/
noncomputable section
namespace CubicFirstMoment

lemma typeI_principal_scaling {R U : ℝ} (hR : 0 < R) (hU : 0 < U) (ε : ℝ) :
    U^(1/2+ε)*(2*R)^(1/4+2*ε)*R =
      2^(1/4+2*ε)*(R*U)^(1/2+ε)*R^(3/4+ε) := by
  have hp : R^(1/4+2*ε)*R = R^(1/2+ε)*R^(3/4+ε) := by
    calc
      _ = R^(1/4+2*ε)*R^(1:ℝ) := by rw [Real.rpow_one]
      _ = R^((1/4+2*ε)+1) := (Real.rpow_add hR _ _).symm
      _ = R^((1/2+ε)+(3/4+ε)) := by congr 1; ring
      _ = _ := Real.rpow_add hR _ _
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hR.le,
    Real.mul_rpow hR.le hU.le]
  calc
    _ = 2^(1/4+2*ε)*U^(1/2+ε)*(R^(1/4+2*ε)*R) := by ring
    _ = _ := by rw [hp]; ring

lemma typeI_residue_scaling {R U : ℝ} (hR : 0 < R) (hU : 0 < U) :
    U^(5/6:ℝ)*R^(-1/6:ℝ)*R = (R*U)^(5/6:ℝ) := by
  have hp : R^(-1/6:ℝ)*R = R^(5/6:ℝ) := by
    calc
      _ = R^(-1/6:ℝ)*R^(1:ℝ) := by rw [Real.rpow_one]
      _ = R^((-1/6:ℝ)+1) := (Real.rpow_add hR _ _).symm
      _ = _ := by norm_num
  rw [Real.mul_rpow hR.le hU.le]
  calc
    _ = U^(5/6:ℝ)*(R^(-1/6:ℝ)*R) := by ring
    _ = _ := by rw [hp]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIFinal
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Type-I height bound with the paper's exponents, obtained by
absorbing the fixed logarithmic coefficient loss. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

lemma typeI_log_power_bound (B : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : ℝ, 0 < L ∧ ∀ X : ℝ, 1 ≤ X → (Real.log X)^B ≤ L*X^δ := by
  cases B with
  | zero =>
    refine ⟨1,zero_lt_one,?_⟩
    intro X hX
    simpa using Real.one_le_rpow hX hδ.le
  | succ n =>
    let η : ℝ := δ/(n+1)
    have hn : (0:ℝ) < n+1 := by positivity
    have hη : 0 < η := div_pos hδ hn
    refine ⟨(1/η)^(n+1),pow_pos (one_div_pos.mpr hη) _,?_⟩
    intro X hX
    have hXp : 0 < X := zero_lt_one.trans_le hX
    have hl := Real.log_le_rpow_div hXp.le hη
    have hp := pow_le_pow_left₀ (Real.log_nonneg hX) hl (n+1)
    have he : (X^η)^(n+1) = X^δ := by
      rw [← Real.rpow_mul_natCast hXp.le]
      congr 1
      dsimp [η]
      push_cast
      exact div_mul_cancel₀ δ hn.ne'
    calc
      _ ≤ (X^η/η)^(n+1) := hp
      _ = (1/η)^(n+1)*X^δ := by rw [div_eq_mul_inv,mul_pow,he]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticHarmonic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite d-sum in the retained angular estimate costs an
arbitrarily small power of its cutoff. The proof uses the already proved
convergent Eisenstein norm series. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem primary_finite_harmonic_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (J : ℝ), 0 < J →
      (∀ d ∈ S, primary d) → (∀ d ∈ S, norm d ≤ J) →
      (∑ d ∈ S, norm d^(-1:ℝ)) ≤ C*J^ε := by
  have hs : Summable (fun d : Eisenstein => norm d^(-1-ε)) := by
    convert summable_eisenstein_norm_rpow (s := 1+ε) (by linarith) using 1
    all_goals try with_reducible_and_instances rfl
    ext d
    congr 1
    ring
  let M : ℝ := ∑' d : Eisenstein, norm d^(-1-ε)
  have hM : 0 ≤ M := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  refine ⟨M+1,by linarith,?_⟩
  intro S J hJ hS hbound
  have hp (d : Eisenstein) (hd : d ∈ S) :
      norm d^(-1:ℝ) ≤ J^ε*norm d^(-1-ε) := by
    have hn := norm_pos_of_ne_zero (primary_ne_zero (hS d hd))
    calc
      _ = norm d^ε*norm d^(-1-ε) := by rw [←Real.rpow_add hn]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hn.le (hbound d hd) hε.le)
        (Real.rpow_nonneg hn.le _)
  calc
    _ ≤ ∑ d ∈ S, J^ε*norm d^(-1-ε) := Finset.sum_le_sum hp
    _ = J^ε*(∑ d ∈ S, norm d^(-1-ε)) := (Finset.mul_sum _ _ _).symm
    _ ≤ J^ε*M := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum S (fun d _ => Real.rpow_nonneg (norm_nonneg d) _))
      (Real.rpow_nonneg hJ.le _)
    _ ≤ (M+1)*J^ε := by nlinarith [Real.rpow_nonneg hJ.le ε]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletedBox
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compactly supported completed sum can be written over a fixed
finite box of primary pairs. This box is independent of the height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_pair_box_image (F : ℝ) :
    (((primaryElementBall F).subtype primary).product
      ((primaryElementBall F).subtype primary)).image metaplecticPrimaryPair =
        (primaryElementBall F).product (primaryElementBall F) := by
  ext du
  constructor
  · intro h
    obtain ⟨ev,hev,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hd,hu⟩ := Finset.mem_product.mp hev
    exact Finset.mem_product.mpr ⟨Finset.mem_subtype.mp hd,Finset.mem_subtype.mp hu⟩
  · intro h
    obtain ⟨hd,hu⟩ := Finset.mem_product.mp h
    refine Finset.mem_image.mpr ⟨(⟨du.1,(mem_primaryElementBall.mp hd).1⟩,
      ⟨du.2,(mem_primaryElementBall.mp hu).1⟩),?_,rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_subtype.mpr hd,Finset.mem_subtype.mpr hu⟩

theorem metaplecticHeightCompleted_box (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {X B F : ℝ} (hX : 0 < X) (hBF : B*X ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    metaplecticHeightCompleted r ℓ W X t =
      ∑ c ∈ primaryElementBall F, ∑ u ∈ primaryElementBall F,
        metaplecticPrimalCoefficient r ℓ W X (c,u)*
          mellinPhase t (norm (metaplecticCubeProduct (c,u))) := by
  let P := ((primaryElementBall F).subtype primary).product
    ((primaryElementBall F).subtype primary)
  have he : metaplecticHeightCompleted r ℓ W X t =
      ∑ du ∈ P, metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du)*
        mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))) := by
    change (∑' du : PrimaryArgument × PrimaryArgument,
      metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du)*
        mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du)))) = _
    apply tsum_eq_sum
    intro du hdu
    have hc : metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du) = 0 := by
      by_contra hn
      have hs := metaplecticPrimalSupport_of_nonzero ℓ W hX hBF hW du hn
      exact hdu (Finset.mem_filter.mp hs).1
    rw [hc,zero_mul]
  rw [he,←Finset.sum_product']
  have himage := primary_pair_box_image F
  change P.image metaplecticPrimaryPair = primaryElementBall F ×ˢ primaryElementBall F at himage
  rw [←himage,Finset.sum_image]
  exact fun _ _ _ _ h => metaplecticPrimaryPair_injective h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inversion of the cubic completion kernel. The Euler variable
for a prime ideal is first weighted, then replaced by its cube. Thus the
series identities below retain the actual cube-divisor support; they are
not ordinary (uncubed) convolution identities. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cube_completion_inverse (x : EisensteinIdealPrime → ℂ) :
    cubeInverseCompletionSeries x*cubeCompletionSeries x = 1 := by
  unfold cubeInverseCompletionSeries cubeCompletionSeries
  rw [← map_mul,← map_mul,← map_mul,idealMoebiusSeries_mul_zeta,map_one,map_one,map_one]

lemma cube_completion_inversion (x : EisensteinIdealPrime → ℂ)
    (A : ComplexIdealSeries) :
    cubeInverseCompletionSeries x*(cubeCompletionSeries x*A) = A := by
  rw [← mul_assoc,cube_completion_inverse,one_mul]

lemma cubeInverseCompletionSeries_coeff (x : EisensteinIdealPrime → ℂ)
    (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff (3 • ν) (cubeInverseCompletionSeries x) =
      ν.prod (fun p k => x p^k)*((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ) := by
  rw [cubeInverseCompletionSeries,MvPowerSeries.coeff_expand_smul,
    MvPowerSeries.coeff_rescale,MvPowerSeries.coeff_map]
  rfl

private lemma primary_nat_pow {a : Eisenstein} (ha : primary a) (k : ℕ) :
    primary (a^k) := by
  induction k with
  | zero => simp [primary]
  | succ k ih => simpa only [pow_succ] using primary_mul ih ha

lemma idealPrimaryGenerator_eq_normalized_prime_product {a : Eisenstein}
    (ha : primary a) {ν : EisensteinIdealExponent} (hν : ν ≤ idealExponentOf a) :
    idealPrimaryGenerator ν =
      ν.prod (fun p k => primaryNormalize (idealPrimeRepresentative p)^k) := by
  have hpp (p : EisensteinIdealPrime) (hp : p ∈ ν.support) :
      primary (primaryNormalize (idealPrimeRepresentative p)) := by
    apply primaryNormalize_primary
    apply unit_residue_of_dvd_primary ha
    apply (idealPrime_dvd_iff (primary_ne_zero ha) p).mpr
    have hpos : 0 < ν p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    exact hpos.trans_le (hν p)
  have hp : primary (ν.prod (fun p k => primaryNormalize (idealPrimeRepresentative p)^k)) :=
    primary_finset_prod _ _ (fun p hp => primary_nat_pow (hpp p hp) _)
  apply primary_associated_eq (idealPrimaryGenerator_primary ha hν) hp
  apply (primaryNormalize_associated _).symm.trans
  unfold idealExponentGenerator
  exact Associated.prod _ _ _ (fun p _ => Associated.pow_pow (n := ν p)
    (primaryNormalize_associated (idealPrimeRepresentative p)))

lemma normalized_prime_product_character {a : Eisenstein} (ha : primary a)
    {ν : EisensteinIdealExponent} (hν : ν ≤ idealExponentOf a)
    (χ : Eisenstein → ℂ) (h1 : χ 1 = 1)
    (hχ : ∀ x y, primary x → primary y → χ (x*y) = χ x*χ y) :
    ν.prod (fun p k => (χ (primaryNormalize (idealPrimeRepresentative p)))^k) =
      χ (idealPrimaryGenerator ν) := by
  rw [idealPrimaryGenerator_eq_normalized_prime_product ha hν]
  have hp (p : EisensteinIdealPrime) (hpm : p ∈ ν.support) :
      primary (primaryNormalize (idealPrimeRepresentative p)) := by
    apply primaryNormalize_primary
    apply unit_residue_of_dvd_primary ha
    apply (idealPrime_dvd_iff (primary_ne_zero ha) p).mpr
    exact (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hpm)).trans_le (hν p)
  have hpow (b : Eisenstein) (hb : primary b) (k : ℕ) : χ (b^k) = (χ b)^k := by
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ,hχ _ _ (primary_nat_pow hb k) hb,ih,pow_succ]
  change (∏ p ∈ ν.support, χ (primaryNormalize (idealPrimeRepresentative p))^ν p) =
    χ (∏ p ∈ ν.support, primaryNormalize (idealPrimeRepresentative p)^ν p)
  suffices hfin : ∀ S : Finset EisensteinIdealPrime,
      (∀ p ∈ S, primary (primaryNormalize (idealPrimeRepresentative p))) →
      (∏ p ∈ S, χ (primaryNormalize (idealPrimeRepresentative p))^ν p) =
        χ (∏ p ∈ S, primaryNormalize (idealPrimeRepresentative p)^ν p) from hfin _ hp
  intro S hS
  induction S using Finset.induction_on with
  | empty => simpa using h1.symm
  | @insert p S hps ih =>
    have hp' := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, primary (primaryNormalize (idealPrimeRepresentative q)) :=
      fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps,Finset.prod_insert hps,
      hχ _ _ (primary_nat_pow hp' _) (primary_finset_prod S _
        (fun q hq => primary_nat_pow (hS' q hq) _)),hpow _ hp']
    congr 1
    exact ih hS'

lemma metaplecticCompletionWeight_mul (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {a b : Eisenstein} (_ha : primary a) (_hb : primary b) :
    metaplecticCompletionWeight r ℓ t (a*b) =
      metaplecticCompletionWeight r ℓ t a*metaplecticCompletionWeight r ℓ t b := by
  unfold metaplecticCompletionWeight
  rw [IsCoprime.mul_left_iff]
  by_cases har : IsCoprime a r
  · by_cases hbr : IsCoprime b r
    · simp only [har,hbr,and_self,ite_true, if_true,norm_mul_eq,theta_mul,
        Real.sqrt_mul (norm_nonneg a),Complex.ofReal_mul]
      rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg a) (norm_nonneg b)]
      ring
    · simp [har,hbr]
  · simp [har]

/-- At a primary principal ideal the expanded inverse kernel has
exactly the arithmetic weight `mu(c)|c| theta_(3ell)(c)(Nc)^(3it)`.
There is no assumption that `c` is squarefree. -/
theorem cubeInverseCompletionSeries_at_primary (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c : Eisenstein} (hc : primary c) :
    MvPowerSeries.coeff (3 • idealExponentOf c)
      (cubeInverseCompletionSeries (fun p => metaplecticCompletionWeight r ℓ t
        (primaryNormalize (idealPrimeRepresentative p)))) =
      (idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ t c := by
  rw [cubeInverseCompletionSeries_coeff,normalized_prime_product_character hc le_rfl
    (metaplecticCompletionWeight r ℓ t) (metaplecticCompletionWeight_one r ℓ t)
    (fun _ _ ha hb => metaplecticCompletionWeight_mul r ℓ t ha hb),
    idealPrimaryGenerator_at_element hc,idealMoebiusSeries_at_element (primary_ne_zero hc)]
  push_cast
  ring

lemma norm_metaplecticCompletionWeight {c : Eisenstein} (hc : primary c)
    (r : Eisenstein) (ℓ : ℤ) (t : ℝ) :
    ‖metaplecticCompletionWeight r ℓ t c‖ =
      if IsCoprime c r then Real.sqrt (norm c) else 0 := by
  unfold metaplecticCompletionWeight
  split_ifs
  · rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),norm_theta (primary_ne_zero hc),mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_of_ne_zero (primary_ne_zero hc))]
    simp
  · exact norm_zero

theorem norm_cubeInverseCompletionSeries_at_primary
    (r : Eisenstein) (ℓ : ℤ) (t : ℝ) {c : Eisenstein} (hc : primary c) :
    ‖MvPowerSeries.coeff (3 • idealExponentOf c)
      (cubeInverseCompletionSeries (fun p => metaplecticCompletionWeight r ℓ t
        (primaryNormalize (idealPrimeRepresentative p))))‖ ≤ Real.sqrt (norm c) := by
  rw [cubeInverseCompletionSeries_at_primary r ℓ t hc,norm_mul]
  have hmu : ‖(idealMoebius c:ℂ)‖ ≤ 1 := by
    have h := idealMoebiusSeries_abs_le_one (idealExponentOf c)
    rw [idealMoebiusSeries_at_element (primary_ne_zero hc)] at h
    have he : (idealMoebius c:ℂ) = ((idealMoebius c:ℝ):ℂ) := by norm_cast
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    exact h
  have hw : ‖metaplecticCompletionWeight r ℓ t c‖ ≤ Real.sqrt (norm c) := by
    rw [norm_metaplecticCompletionWeight hc]
    split_ifs
    · rfl
    · exact Real.sqrt_nonneg _
  exact (mul_le_mul_of_nonneg_right hmu (_root_.norm_nonneg _)).trans (by simpa using hw)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrimaryCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The expanded ideal kernel is exactly a primary cube-divisor sum.
This reindexing retains the finite norm cutoff and arbitrary complex
coefficients; no analytic summability assumption enters the inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma weightedCubeSeries_coeff (B : ComplexIdealSeries) (x : EisensteinIdealPrime → ℂ)
    (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff (3 • ν) (weightedCubeSeries B x) =
      ν.prod (fun p k => x p^k)*MvPowerSeries.coeff ν B := by
  rw [weightedCubeSeries,MvPowerSeries.coeff_expand_smul,MvPowerSeries.coeff_rescale]

lemma primary_cube {c : Eisenstein} (hc : primary c) : primary (c^3) := by
  simpa only [pow_succ,pow_zero,one_mul] using primary_mul (primary_mul hc hc) hc

lemma primary_cube_injective {c d : Eisenstein} (hc : primary c) (hd : primary d)
    (h : c^3 = d^3) : c = d := by
  apply primary_eq_of_idealExponentOf_eq hc hd
  have he := congrArg idealExponentOf h
  rw [idealExponentOf_pow (primary_ne_zero hc),idealExponentOf_pow (primary_ne_zero hd)] at he
  ext p
  have hp := congrArg (fun ν : EisensteinIdealExponent => ν p) he
  simp only [Finsupp.smul_apply,smul_eq_mul] at hp
  omega

lemma weightedCubeSeries_nonzero_primary {B : ComplexIdealSeries}
    {x : EisensteinIdealPrime → ℂ} {b : Eisenstein} (hb : primary b)
    (h : MvPowerSeries.coeff (idealExponentOf b) (weightedCubeSeries B x) ≠ 0) :
    ∃ c : Eisenstein, primary c ∧ c^3 = b := by
  have hs : idealExponentOf b ∈ Function.support (weightedCubeSeries B x) := h
  obtain ⟨ν,_,he⟩ := MvPowerSeries.support_expand_subset 3 (by norm_num)
    (MvPowerSeries.rescale x B) hs
  have hν : ν ≤ idealExponentOf b := by
    rw [← he]
    intro p
    simp only [Finsupp.smul_apply,smul_eq_mul]
    omega
  refine ⟨idealPrimaryGenerator ν,idealPrimaryGenerator_primary hb hν,?_⟩
  apply primary_eq_of_idealExponentOf_eq (primary_cube (idealPrimaryGenerator_primary hb hν)) hb
  rw [idealExponentOf_pow (primary_ne_zero (idealPrimaryGenerator_primary hb hν)),
    idealExponentOf_primaryGenerator]
  exact he

/-- Multiplying by the expanded series is a literal sum over primary
cube divisors, with every argument bounded by the original norm cutoff. -/
theorem weightedCubeSeries_product_primary
    (B A : ComplexIdealSeries) (x : EisensteinIdealPrime → ℂ)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b) (weightedCubeSeries B x*A) =
      ∑ n ∈ primaryCubeFiber F b,
        ((idealExponentOf (n 0)).prod (fun p k => x p^k)*
          MvPowerSeries.coeff (idealExponentOf (n 0)) B)*
          MvPowerSeries.coeff (idealExponentOf (n 1)) A := by
  have he := coeff_product_primary_fiber (ι := Fin 2) ![weightedCubeSeries B x,A] hb hbF
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at he
  rw [he]
  symm
  apply Finset.sum_bij_ne_zero (fun n _ _ => ![n 0^3,n 1])
  · intro n hn _
    obtain ⟨hn,hprod⟩ := Finset.mem_filter.mp hn
    have hnp (i : Fin 2) := (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hn i)).1
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_),?_⟩
    · fin_cases i
      · apply mem_primaryElementBall.mpr
        refine ⟨primary_cube (hnp 0),?_⟩
        exact (norm_le_of_dvd (primary_ne_zero hb) ⟨n 1,hprod.symm⟩).trans hbF
      · simpa using Fintype.mem_piFinset.mp hn 1
    · simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using hprod
  · intro n hn _ m hm _ h
    apply funext
    intro i
    have hn0 := (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 0)).1
    have hm0 := (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hm).1 0)).1
    fin_cases i
    · exact primary_cube_injective hn0 hm0 (congrFun h 0)
    · exact congrFun h 1
  · intro m hm hnon
    obtain ⟨hm,hprod⟩ := Finset.mem_filter.mp hm
    have hmp (i : Fin 2) := (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hm i)).1
    have hzero : MvPowerSeries.coeff (idealExponentOf (m 0)) (weightedCubeSeries B x) ≠ 0 :=
      (mul_ne_zero_iff.mp hnon).1
    obtain ⟨c,hc,hc3⟩ := weightedCubeSeries_nonzero_primary (hmp 0) hzero
    have hcb : c^3*m 1 = b := by simpa only [Fin.prod_univ_two,← hc3] using hprod
    have hcF : norm c ≤ F := (norm_le_of_dvd (primary_ne_zero hb)
      ((dvd_pow_self c (by norm_num : (3:ℕ) ≠ 0)).trans ⟨m 1,hcb.symm⟩)).trans hbF
    refine ⟨![c,m 1],Finset.mem_filter.mpr ⟨?_,?_⟩,?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      fin_cases i
      · exact mem_primaryElementBall.mpr ⟨hc,hcF⟩
      · simpa using Fintype.mem_piFinset.mp hm 1
    · simpa using hcb
    · rw [← hc3] at hnon
      simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
        idealExponentOf_pow (primary_ne_zero hc),weightedCubeSeries_coeff] using hnon
    · funext i
      fin_cases i
      · simpa using hc3
      · simp
  · intro n hn _
    have hnc := (mem_primaryElementBall.mp
      (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 0)).1
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      idealExponentOf_pow (primary_ne_zero hnc),weightedCubeSeries_coeff]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrimaryInverse
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact inverse completion at primary elements. The formal Euler
inverse is reindexed onto the literal primary cube-divisor fibers, with
its actual Möbius, angular and height weights. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma weightedInverseCompletion_eq (r : Eisenstein) (ℓ : ℤ) (t : ℝ) :
    weightedCubeSeries (MvPowerSeries.map Complex.ofRealHom idealMoebiusSeries)
      (metaplecticPrimeCompletionWeights r ℓ t) =
        cubeInverseCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t) := rfl

/-- No cube-divisor is omitted: the finite bound follows from divisibility
of the original primary element, not from an additional support hypothesis. -/
theorem metaplectic_primary_inverse_coefficient
    (r : Eisenstein) (ℓ : ℤ) (t : ℝ) (A : ComplexIdealSeries)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b) A =
      ∑ n ∈ primaryCubeFiber F b,
        ((idealMoebius (n 0):ℂ)*metaplecticCompletionWeight r ℓ t (n 0))*
          MvPowerSeries.coeff (idealExponentOf (n 1))
            (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*A) := by
  have he := weightedCubeSeries_product_primary
    (MvPowerSeries.map Complex.ofRealHom idealMoebiusSeries)
    (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*A)
    (metaplecticPrimeCompletionWeights r ℓ t) hb hbF
  rw [weightedInverseCompletion_eq,cube_completion_inversion] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro n hn
  have hc := (mem_primaryElementBall.mp
    (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 0)).1
  simp only [metaplecticPrimeCompletionWeights]
  rw [MvPowerSeries.coeff_map,
    idealMoebiusSeries_at_element (primary_ne_zero hc),
    normalized_prime_product_character hc le_rfl
      (metaplecticCompletionWeight r ℓ t) (metaplecticCompletionWeight_one r ℓ t)
      (fun _ _ ha hb => metaplecticCompletionWeight_mul r ℓ t ha hb),
    idealPrimaryGenerator_at_element hc]
  simp only [Complex.ofRealHom_eq_coe]
  push_cast
  ring

/-- Any finite smooth norm weight may be applied after the actual primary
inverse identity, without a rearrangement of an infinite series. -/
theorem metaplectic_primary_weighted_inverse
    (r : Eisenstein) (ℓ : ℤ) (t : ℝ) (A : ComplexIdealSeries)
    (F : ℝ) (W : ℝ → ℂ) :
    (∑ b ∈ primaryElementBall F, W (norm b)*MvPowerSeries.coeff (idealExponentOf b) A) =
      ∑ b ∈ primaryElementBall F, W (norm b)*
        ∑ n ∈ primaryCubeFiber F b,
          ((idealMoebius (n 0):ℂ)*metaplecticCompletionWeight r ℓ t (n 0))*
            MvPowerSeries.coeff (idealExponentOf (n 1))
              (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*A) := by
  apply Finset.sum_congr rfl
  intro b hb
  rw [metaplectic_primary_inverse_coefficient r ℓ t A
    (mem_primaryElementBall.mp hb).1 (mem_primaryElementBall.mp hb).2]

lemma metaplecticGaussIdealSeries_at_primary (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {b : Eisenstein} (hb : primary b) :
    MvPowerSeries.coeff (idealExponentOf b) (metaplecticGaussIdealSeries r ℓ t) =
      gauss (r*b)*theta ℓ (r*b)*mellinPhase t (norm b) := by
  simp only [MvPowerSeries.coeff_apply,metaplecticGaussIdealSeries,
    idealPrimaryGenerator_at_element hb,idealExponentOf_norm (primary_ne_zero hb)]

/-- The inverted coefficients are the literal angular Gauss coefficients,
including the original norm twist. -/
theorem metaplectic_gauss_primary_inverse
    (r : Eisenstein) (ℓ : ℤ) (t F : ℝ) (W : ℝ → ℂ) :
    (∑ b ∈ primaryElementBall F, W (norm b)*
      (gauss (r*b)*theta ℓ (r*b)*mellinPhase t (norm b))) =
      ∑ b ∈ primaryElementBall F, W (norm b)*
        ∑ n ∈ primaryCubeFiber F b,
          ((idealMoebius (n 0):ℂ)*metaplecticCompletionWeight r ℓ t (n 0))*
            MvPowerSeries.coeff (idealExponentOf (n 1))
              (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*
                metaplecticGaussIdealSeries r ℓ t) := by
  rw [←metaplectic_primary_weighted_inverse]
  apply Finset.sum_congr rfl
  intro b hb
  rw [metaplecticGaussIdealSeries_at_primary r ℓ t (mem_primaryElementBall.mp hb).1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletionCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed formal coefficients are exactly the actual primary
Gauss cube-divisor coefficients, including the positive angular index
and the height multiplier. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma theta_cube_index (ℓ : ℤ) {c : Eisenstein} (hc : c ≠ 0) :
    theta (3*ℓ) c = theta ℓ (c^3) := by
  rw [show 3*ℓ = (ℓ+ℓ)+ℓ by ring,theta_add (ℓ+ℓ) ℓ hc,theta_add ℓ ℓ hc]
  simp only [pow_succ,pow_zero,one_mul,theta_mul]

lemma mellinPhase_cube_norm (t : ℝ) (x : ℝ) :
    mellinPhase (3*t) x = mellinPhase t (x^3) := by
  unfold mellinPhase
  rw [Real.log_pow]
  congr 1
  push_cast
  ring

lemma metaplecticCompletionWeight_phase (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c : Eisenstein} (hc : primary c) :
    metaplecticCompletionWeight r ℓ t c =
      if IsCoprime c r then
        (Real.sqrt (norm c):ℂ)*theta ℓ (c^3)*mellinPhase t (norm c^3)
      else 0 := by
  unfold metaplecticCompletionWeight
  rw [theta_cube_index ℓ (primary_ne_zero hc),
    ←mellinPhase_eq_cpow (norm_pos_of_ne_zero (primary_ne_zero hc)) (3*t),
    mellinPhase_cube_norm]

lemma metaplectic_completion_factor (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c u : Eisenstein} (hc : primary c) (hu : primary u) :
    metaplecticCompletionWeight r ℓ t c*
      (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u)) =
        metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (c,u)*
          mellinPhase t (norm (metaplecticCubeProduct (c,u))) := by
  rw [metaplecticCompletionWeight_phase r ℓ t hc]
  by_cases hcr : IsCoprime c r
  · simp only [hcr,ite_true, if_true,metaplecticPrimalCoefficient,metaplecticCubeProduct,
      mul_one,theta_mul,norm_mul_eq,eisenstein_norm_pow]
    rw [mellinPhase_mul_pos t (norm_pos_of_ne_zero (primary_ne_zero hu))
      (pow_pos (norm_pos_of_ne_zero (primary_ne_zero hc)) 3)]
    ring
  · simp [hcr,metaplecticPrimalCoefficient]

/-- Completing the actual Gauss ideal series gives exactly the literal
primary cube fiber used by the Voronoi formula. -/
theorem metaplectic_completed_primary_coefficient
    (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b)
      (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*
        metaplecticGaussIdealSeries r ℓ t) =
      ∑ n ∈ primaryCubeFiber F b,
        metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (n 0,n 1)*
          mellinPhase t (norm (metaplecticCubeProduct (n 0,n 1))) := by
  have he := weightedCubeSeries_product_primary
    (MvPowerSeries.map Complex.ofRealHom idealZeta)
    (metaplecticGaussIdealSeries r ℓ t)
    (metaplecticPrimeCompletionWeights r ℓ t) hb hbF
  change MvPowerSeries.coeff (idealExponentOf b)
    (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*
      metaplecticGaussIdealSeries r ℓ t) = _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro n hn
  have hnp (i : Fin 2) := (mem_primaryElementBall.mp
    (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 i)).1
  have hz : MvPowerSeries.coeff (idealExponentOf (n 0))
      (MvPowerSeries.map Complex.ofRealHom idealZeta) = 1 := by
    rw [MvPowerSeries.coeff_map]
    change Complex.ofRealHom (1:ℝ) = 1
    exact map_one _
  rw [hz,mul_one]
  simp only [metaplecticPrimeCompletionWeights]
  rw [normalized_prime_product_character (hnp 0) le_rfl
    (metaplecticCompletionWeight r ℓ t) (metaplecticCompletionWeight_one r ℓ t)
    (fun _ _ ha hb => metaplecticCompletionWeight_mul r ℓ t ha hb),
    idealPrimaryGenerator_at_element (hnp 0),
    metaplecticGaussIdealSeries_at_primary r ℓ t (hnp 1)]
  exact metaplectic_completion_factor r ℓ t (hnp 0) (hnp 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCubeFiberSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite collection of actual primary cube fibers. Compact norm
weights remove the output cutoff without adding any support assumption
on the arithmetic coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma sum_primary_fin_two (S : Finset Eisenstein) (f : Eisenstein → Eisenstein → ℂ) :
    (∑ n ∈ Fintype.piFinset (fun _ : Fin 2 => S), f (n 0) (n 1)) =
      ∑ c ∈ S, ∑ u ∈ S, f c u := by
  rw [←Finset.sum_product' S S f]
  apply Finset.sum_bij (fun n _ => (n 0,n 1))
  · intro n hn
    exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp hn 0,Fintype.mem_piFinset.mp hn 1⟩
  · intro n _ m _ he
    funext i
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  · intro cu hcu
    refine ⟨![cu.1,cu.2],Fintype.mem_piFinset.mpr ?_,?_⟩
    · intro i
      fin_cases i
      · exact (Finset.mem_product.mp hcu).1
      · exact (Finset.mem_product.mp hcu).2
    · rfl
  · intro n _
    rfl

theorem primary_cube_fiber_weighted_sum (F : ℝ) (W : ℝ → ℂ)
    (hW : ∀ x : ℝ, F < x → W x = 0) (f : Eisenstein → Eisenstein → ℂ) :
    (∑ b ∈ primaryElementBall F, W (norm b)*
      ∑ n ∈ primaryCubeFiber F b, f (n 0) (n 1)) =
      ∑ c ∈ primaryElementBall F, ∑ u ∈ primaryElementBall F,
        W (norm (c^3*u))*f c u := by
  let S := Fintype.piFinset (fun _ : Fin 2 => primaryElementBall F)
  let g := fun n : Fin 2 → Eisenstein => n 0^3*n 1
  let w := fun n : Fin 2 → Eisenstein => W (norm (g n))*f (n 0) (n 1)
  have hreplace (b : Eisenstein) : W (norm b)*
      (∑ n ∈ primaryCubeFiber F b, f (n 0) (n 1)) =
      ∑ n ∈ S with g n = b, w n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have he := (Finset.mem_filter.mp hn).2
    dsimp [w,g]
    rw [he]
  simp_rw [hreplace]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  have he : (∑ n ∈ S with g n ∈ primaryElementBall F, w n) = ∑ n ∈ S, w n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    have hn0 := (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hn 0)).1
    have hn1 := (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hn 1)).1
    have hgp : primary (g n) := primary_mul (primary_cube hn0) hn1
    have hgt : F < norm (g n) := by
      by_contra h
      have hgn : g n ∈ primaryElementBall F := mem_primaryElementBall.mpr ⟨hgp,le_of_not_gt h⟩
      exact hnot (Finset.mem_filter.mpr ⟨hn,hgn⟩)
    simp only [w,hW _ hgt,zero_mul]
  rw [he]
  exact sum_primary_fin_two (primaryElementBall F) (fun c u => W (norm (c^3*u))*f c u)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletedPolynomial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the completed ideal polynomial with the
original completed Gauss sum at every real height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_primal_weight_factor (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (X t : ℝ) (c u : Eisenstein) :
    W (norm (c^3*u)/X)*(metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (c,u)*
      mellinPhase t (norm (metaplecticCubeProduct (c,u)))) =
        metaplecticPrimalCoefficient r ℓ W X (c,u)*
          mellinPhase t (norm (metaplecticCubeProduct (c,u))) := by
  by_cases hcr : IsCoprime c r
  · simp only [metaplecticPrimalCoefficient,hcr,ite_true, if_true,mul_one,
      metaplecticCubeProduct]
    rw [show c^3*u = u*c^3 by ring]
    ring
  · simp [metaplecticPrimalCoefficient,hcr]

lemma metaplectic_completed_ideal_fibers
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (X F t : ℝ) :
    (∑ b ∈ primaryElementBall F, W (norm b/X)*
      MvPowerSeries.coeff (idealExponentOf b)
        (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*
          metaplecticGaussIdealSeries r ℓ t)) =
    ∑ b ∈ primaryElementBall F, W (norm b/X)*
      ∑ n ∈ primaryCubeFiber F b,
        metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (n 0,n 1)*
          mellinPhase t (norm (metaplecticCubeProduct (n 0,n 1))) := by
  apply Finset.sum_congr rfl
  intro b hb
  have hcoef := metaplectic_completed_primary_coefficient r ℓ t (b := b)
    (mem_primaryElementBall.mp hb).1 (F := F) (mem_primaryElementBall.mp hb).2
  exact congrArg (fun z : ℂ => W (norm b/X)*z) hcoef

lemma metaplectic_primal_weighted_fibers
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) {X B F : ℝ}
    (hX : 0 < X) (hBF : B*X ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    (∑ b ∈ primaryElementBall F, W (norm b/X)*
      ∑ n ∈ primaryCubeFiber F b,
        metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (n 0,n 1)*
          mellinPhase t (norm (metaplecticCubeProduct (n 0,n 1)))) =
      metaplecticHeightCompleted r ℓ W X t := by
  have hcut : ∀ x : ℝ, F < x → W (x/X) = 0 := by
    intro x hx
    exact hW _ ((lt_div_iff₀ hX).mpr (hBF.trans_lt hx))
  let g : Eisenstein → Eisenstein → ℂ := fun c u =>
    metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (c,u)*
      mellinPhase t (norm (metaplecticCubeProduct (c,u)))
  have he := primary_cube_fiber_weighted_sum F (fun x => W (x/X)) hcut g
  change (∑ b ∈ primaryElementBall F, W (norm b/X)*
    ∑ n ∈ primaryCubeFiber F b, g (n 0) (n 1)) = _
  rw [he,metaplecticHeightCompleted_box r ℓ W hX hBF hW t]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro u _
  exact metaplectic_primal_weight_factor r ℓ W X t c u

theorem metaplectic_completed_ideal_polynomial
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) {X B F : ℝ}
    (hX : 0 < X) (hBF : B*X ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    (∑ b ∈ primaryElementBall F, W (norm b/X)*
      MvPowerSeries.coeff (idealExponentOf b)
        (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*
          metaplecticGaussIdealSeries r ℓ t)) =
      metaplecticHeightCompleted r ℓ W X t :=
  (metaplectic_completed_ideal_fibers r ℓ W X F t).trans
    (metaplectic_primal_weighted_fibers r ℓ W hX hBF hW t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticActualInverse
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inverse completion for the original angular, norm-twisted
smooth Gauss sum. All cube-divisor sums are finite by the actual support
of the weight, and the rescaled completed length is retained literally. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticAngularSmoothSum_finite (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    metaplecticAngularSmoothSum r ℓ W U t =
      ∑ u ∈ primaryElementBall F,
        W (norm u/U)*(gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u)) := by
  let S := (primaryElementBall F).subtype primary
  have he : metaplecticAngularSmoothSum r ℓ W U t =
      ∑ u ∈ S, (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u))*W (norm u/U) := by
    apply tsum_eq_sum
    intro u hu
    have hnorm : F < norm u := by
      by_contra hn
      exact hu (Finset.mem_subtype.mpr (mem_primaryElementBall.mpr ⟨u.property,le_of_not_gt hn⟩))
    rw [hW _ ((lt_div_iff₀ hU).mpr (hBF.trans_lt hnorm)),mul_zero]
  rw [he]
  dsimp only [S]
  rw [Finset.sum_subtype_of_mem
    (fun u : Eisenstein => (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u))*W (norm u/U))
    (fun _ hu => (mem_primaryElementBall.mp hu).1)]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- Equation (angular-inversion), with the height-dependent inverse
weight and the original compactly supported sum on its left. -/
theorem metaplectic_angular_actual_inverse
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    metaplecticAngularSmoothSum r ℓ W U t =
      ∑ c ∈ primaryElementBall F,
        ((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ t c)*
          metaplecticHeightCompleted r ℓ W (U/norm c^3) t := by
  rw [metaplecticAngularSmoothSum_finite r ℓ W hU hBF hW t,
    metaplectic_gauss_primary_inverse r ℓ t F (fun x => W (x/U))]
  have hcut : ∀ x : ℝ, F < x → W (x/U) = 0 := by
    intro x hx
    exact hW _ ((lt_div_iff₀ hU).mpr (hBF.trans_lt hx))
  let g : Eisenstein → Eisenstein → ℂ := fun c u =>
    ((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ t c)*
      MvPowerSeries.coeff (idealExponentOf u)
        (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*
          metaplecticGaussIdealSeries r ℓ t)
  have hg := primary_cube_fiber_weighted_sum F (fun x => W (x/U)) hcut g
  change (∑ b ∈ primaryElementBall F, W (norm b/U)*
    ∑ n ∈ primaryCubeFiber F b, g (n 0) (n 1)) = _
  rw [hg]
  dsimp only [g]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨hcp,hcF⟩ := mem_primaryElementBall.mp hc
  have hcpos := norm_pos_of_ne_zero (primary_ne_zero hcp)
  have hcone := one_le_norm (primary_ne_zero hcp)
  have hX : 0 < U/norm c^3 := div_pos hU (pow_pos hcpos 3)
  have hXU : U/norm c^3 ≤ U := div_le_self hU.le (one_le_pow₀ hcone)
  have hXF : B*(U/norm c^3) ≤ F := (mul_le_mul_of_nonneg_left hXU hB).trans hBF
  rw [←metaplectic_completed_ideal_polynomial r ℓ W hX hXF hW t,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have he : norm (c^3*u)/U = norm u/(U/norm c^3) := by
    rw [norm_mul_eq,eisenstein_norm_pow]
    field_simp
  rw [he]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticInverseScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact amplitude and polynomial length range after angular
inverse completion. Each cube divisor contributes one inverse norm. -/
noncomputable section
namespace CubicFirstMoment

lemma norm_metaplectic_inverse_weight (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c : Eisenstein} (hc : primary c) :
    ‖(idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ t c‖ ≤ Real.sqrt (norm c) := by
  have h := norm_cubeInverseCompletionSeries_at_primary r ℓ t hc
  rwa [cubeInverseCompletionSeries_at_primary r ℓ t hc] at h

lemma metaplectic_inverse_sqrt_scale {U N : ℝ} (hU : 0 ≤ U) (hN : 0 < N) :
    Real.sqrt N*Real.sqrt (U/N^3) = Real.sqrt U/N := by
  have hn : Real.sqrt (N^3) = N*Real.sqrt N := by
    rw [show N^3 = N^2*N by ring,Real.sqrt_mul (sq_nonneg N),Real.sqrt_sq hN.le]
  rw [Real.sqrt_div hU,hn]
  field_simp [hN.ne',(Real.sqrt_pos.mpr hN).ne']

lemma metaplectic_inverse_length_range {Y U N B : ℝ}
    (hY : 1 ≤ Y) (hB : 0 ≤ B) (hUlo : Y^(-B) ≤ U) (hUhi : U ≤ Y^B)
    (hNlo : 1 ≤ N) (hNhi : N ≤ Y^B) :
    0 < U/N^3 ∧ Y^(-(4*B)) ≤ U/N^3 ∧ U/N^3 ≤ Y^(4*B) := by
  have hYp := zero_lt_one.trans_le hY
  have hUp := (Real.rpow_pos_of_pos hYp (-B)).trans_le hUlo
  have hNp := zero_lt_one.trans_le hNlo
  have hNcube : N^3 ≤ Y^(3*B) := by
    calc
      _ ≤ (Y^B)^3 := pow_le_pow_left₀ hNp.le hNhi 3
      _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hYp.le]; congr 1; ring
  refine ⟨div_pos hUp (pow_pos hNp 3),?_,?_⟩
  · apply (le_div_iff₀ (pow_pos hNp 3)).mpr
    calc
      _ ≤ Y^(-(4*B))*Y^(3*B) := mul_le_mul_of_nonneg_left hNcube (by positivity)
      _ = Y^(-B) := by rw [←Real.rpow_add hYp]; congr 1; ring
      _ ≤ U := hUlo
  · exact (div_le_self hUp.le (one_le_pow₀ hNlo)).trans
      (hUhi.trans (Real.rpow_le_rpow_of_exponent_le hY (by linarith)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the actual finite retained transform. The common
critical-line majorant proves it without a uniform-series assumption. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma continuous_metaplectic_height_completed (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {X : ℝ} (hX : 0 < X) :
    Continuous (metaplecticHeightCompleted r ℓ W X) := by
  obtain ⟨B,hB⟩ := hW.isCompact.isBounded.exists_norm_le
  have hcut : ∀ x : ℝ, B < x → W x = 0 := by
    intro x hx
    by_contra hn
    have hh := hB x (subset_tsupport W hn)
    rw [Real.norm_eq_abs] at hh
    linarith [le_abs_self x]
  have he (t : ℝ) := metaplecticHeightCompleted_finite r ℓ W hX
    (le_refl (B*X)) hcut t
  change Continuous (fun t : ℝ => metaplecticHeightCompleted r ℓ W X t)
  simp_rw [he]
  apply continuous_finsetSum
  intro du hdu
  apply continuous_const.mul
  unfold mellinPhase
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticInverseMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite inverse completion transfers actual signed-height means.
The weight norm is estimated pointwise; its height-dependent phase is
retained in the exact identity and never treated as constant. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma continuous_metaplecticAngularSmoothSum_of_cutoff
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) {U B F : ℝ}
    (hU : 0 < U) (hBF : B*U ≤ F) (hW : ∀ x : ℝ, B < x → W x = 0) :
    Continuous (metaplecticAngularSmoothSum r ℓ W U) := by
  have hc : Continuous (fun t : ℝ => ∑ u ∈ primaryElementBall F,
      W (norm u/U)*(gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u))) := by
    apply continuous_finsetSum
    intro u _
    unfold mellinPhase
    fun_prop
  exact hc.congr (fun t => (metaplecticAngularSmoothSum_finite r ℓ W hU hBF hW t).symm)

lemma metaplectic_inverse_pointwise_norm
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) {U B F : ℝ}
    (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    ‖metaplecticAngularSmoothSum r ℓ W U t‖ ≤
      ∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
        ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖ := by
  rw [metaplectic_angular_actual_inverse r ℓ W hU hB hBF hW t]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c hc
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_metaplectic_inverse_weight r ℓ t (mem_primaryElementBall.mp hc).1)
    (_root_.norm_nonneg _)

lemma metaplectic_inverse_interval_norm
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    {U B F a b : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (hab : a ≤ b) :
    (∫ t in a..b, ‖metaplecticAngularSmoothSum r ℓ W U t‖) ≤
      ∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
        (∫ t in a..b, ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖) := by
  have hf := (continuous_metaplecticAngularSmoothSum_of_cutoff r ℓ W hU hBF hW).norm
  have hc (c : Eisenstein) (hc : c ∈ primaryElementBall F) :
      Continuous (fun t : ℝ => Real.sqrt (norm c)*
        ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖) := by
    have hcp := norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp hc).1)
    exact continuous_const.mul
      (continuous_metaplectic_height_completed r ℓ W hWc (div_pos hU (pow_pos hcp 3))).norm
  have hg : Continuous (fun t : ℝ => ∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
      ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖) :=
    continuous_finsetSum _ hc
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (hf.intervalIntegrable a b) (hg.intervalIntegrable a b)
    (fun t _ => metaplectic_inverse_pointwise_norm r ℓ W hU hB hBF hW t)
  apply hi.trans_eq
  rw [intervalIntegral.integral_finsetSum (fun c hc' => (hc c hc').intervalIntegrable a b)]
  simp only [intervalIntegral.integral_const_mul]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticAngularOuter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed nonzero-angular Type-I height estimate for the original
Gauss sums. Finite level summation uses the actual coefficient L1 mass;
its logarithmic loss is absorbed only after the common exponent is chosen. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticAngularSmoothSum_zero_of_not_squarefree {r : Eisenstein}
    (hr : primary r) (hs : ¬Squarefree r) (ℓ : ℤ) (W : ℝ → ℂ) (U t : ℝ) :
    metaplecticAngularSmoothSum r ℓ W U t = 0 := by
  have hg (u : PrimaryArgument) : gauss (r*u) = 0 :=
    gauss_eq_zero_of_not_squarefree (primary_mul hr u.property)
      (fun h => hs (Squarefree.squarefree_of_dvd (dvd_mul_right _ _) h))
  simp [metaplecticAngularSmoothSum,hg]

lemma angular_level_scaling {R U : ℝ} (hR : 0 < R) (hU : 0 < U) :
    Real.sqrt U*(2*R)^(1/4:ℝ)*R =
      2^(1/4:ℝ)*Real.sqrt (R*U)*R^(3/4:ℝ) := by
  simpa only [add_zero,zero_mul,mul_zero,Real.sqrt_eq_rpow] using typeI_principal_scaling hR hU 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticShortResidue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short inverse residue is exactly the same finite Möbius density
as the radial squarefree lattice main term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_inverse_residue_scale {U N : ℝ} (hU : 0 < U) (hN : 0 < N) :
    Real.sqrt N*(U/N^3)^(5/6:ℝ) = U^(5/6:ℝ)*N^(-2:ℝ) := by
  rw [Real.sqrt_eq_rpow,Real.div_rpow hU.le (pow_nonneg hN.le _),
    ←Real.rpow_natCast N 3,←Real.rpow_mul hN.le]
  have he : ((3:ℕ):ℝ)*(5/6) = 5/2 := by norm_num
  rw [he]
  calc
    _ = U^(5/6:ℝ)*(N^(1/2:ℝ)/N^(5/2:ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_sub hN]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIRanges
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two Mellin-height ranges used after the Type-I estimate, with
explicit power gaps and logarithmic decay of the pole term. -/
noncomputable section
namespace CubicFirstMoment

lemma typeI_bulk_power {X R T a b ε : ℝ} (hX : 0 < X) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRa : R ≤ X^a) (hTb : T ≤ X^b) :
    X^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤ X^(1/2+ε+3*a/4+b/2) := by
  have hr := Real.rpow_le_rpow hR hRa (by norm_num : (0:ℝ) ≤ 3/4)
  rw [← Real.rpow_mul hX.le] at hr
  have ht : Real.sqrt T ≤ X^(b/2) := by
    have hh := Real.rpow_le_rpow hT hTb (by norm_num : (0:ℝ) ≤ 1/2)
    rw [← Real.rpow_mul hX.le] at hh
    calc
      Real.sqrt T = T^(1/2:ℝ) := Real.sqrt_eq_rpow _
      _ ≤ X^(b*(1/2:ℝ)) := hh
      _ = _ := by congr 1; ring
  calc
    _ ≤ X^(1/2+ε)*X^(a*(3/4:ℝ))*X^(b/2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hX.le _)) ht
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hX,← Real.rpow_add hX]; congr 1; ring

lemma typeI_first_bulk_exponent {X R T ε : ℝ} (hX : 0 < X) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRa : R ≤ X^(2/5:ℝ)) (hTb : T ≤ X^(1/100:ℝ)) :
    X^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤ X^(161/200+ε) := by
  convert typeI_bulk_power hX hR hT hRa hTb (ε := ε) using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)

lemma typeI_second_bulk_exponent {X R T ε κ ρ : ℝ}
    (hX : 0 < X) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRa : R ≤ X^(1/3-κ/2)) (hTb : T ≤ X^(1/6+ρ)) :
    X^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤ X^(5/6-3*κ/8+ρ/2+ε) := by
  convert typeI_bulk_power hX hR hT hRa hTb (ε := ε) using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)

lemma typeI_first_fixed_gap {X R T ε : ℝ} (hX : 1 ≤ X) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRa : R ≤ X^(2/5:ℝ)) (hTb : T ≤ X^(1/100:ℝ)) (hε : ε ≤ 1/100) :
    X^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤ X^(5/6-1/100:ℝ) := by
  apply (typeI_first_bulk_exponent (zero_lt_one.trans_le hX) hR hT hRa hTb).trans
  exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)

lemma typeI_second_fixed_gap {X R T ε κ ρ : ℝ}
    (hX : 1 ≤ X) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRa : R ≤ X^(1/3-κ/2)) (hTb : T ≤ X^(1/6+ρ))
    (hρ : ρ ≤ κ/4) (hε : ε ≤ κ/16) :
    X^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤ X^(5/6-3*κ/16) := by
  apply (typeI_second_bulk_exponent (zero_lt_one.trans_le hX) hR hT hRa hTb).trans
  exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)

lemma typeI_pole_log_saving {X T : ℝ} (hX : 0 ≤ X) (hlog : 1 ≤ Real.log X)
    (hT : Real.log X ≤ T) {B D M : ℕ} (hD : B+M ≤ D) :
    X^(5/6:ℝ)*(Real.log X)^B/T^D ≤ X^(5/6:ℝ)/(Real.log X)^M := by
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hTp : 0 < T := hLp.trans_le hT
  have hp : (Real.log X)^B/T^D ≤ 1/(Real.log X)^M := by
    apply (div_le_div_iff₀ (pow_pos hTp D) (pow_pos hLp M)).mpr
    rw [one_mul,← pow_add]
    exact (pow_le_pow_right₀ hlog hD).trans (pow_le_pow_left₀ hLp.le hT D)
  calc
    _ = X^(5/6:ℝ)*((Real.log X)^B/T^D) := by ring
    _ ≤ X^(5/6:ℝ)*(1/(Real.log X)^M) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hX _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIMixedDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed number of relative norm dyads covers the full product support.
The number is independent of the product length. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma typeIMixedDyadIndex_bounds {L : ℝ} (hL : 0 < L) {r : Eisenstein}
    (hr : L ≤ norm r) :
    L*(2:ℝ)^typeIMixedDyadIndex L r ≤ norm r ∧
      norm r < 2*(L*(2:ℝ)^typeIMixedDyadIndex L r) := by
  have hratio : 1 ≤ norm r/L := (le_div_iff₀ hL).mpr (by simpa using hr)
  have hb := Classical.choose_spec (exists_nat_pow_near hratio (by norm_num : (1:ℝ) < 2))
  unfold typeIMixedDyadIndex
  rw [dite_eq_left hratio]
  constructor
  · simpa only [mul_comm] using (le_div_iff₀ hL).mp hb.1
  · have hh := (div_lt_iff₀ hL).mp hb.2
    rw [pow_succ] at hh
    nlinarith

lemma typeIMixedDyadIndex_lt {L D : ℝ} {J : ℕ} (hL : 0 < L) (hD : D < (2:ℝ)^J)
    {r : Eisenstein} (hr : L ≤ norm r) (hrD : norm r ≤ D*L) :
    typeIMixedDyadIndex L r < J := by
  apply (pow_right_strictMono₀ (by norm_num : (1:ℝ) < 2)).lt_iff_lt.mp
  have hb := (typeIMixedDyadIndex_bounds hL hr).1
  nlinarith [mul_lt_mul_of_pos_right hD hL]

lemma typeIMixedDyad_partition (S : Finset Eisenstein) {L D : ℝ} {J : ℕ}
    (hL : 0 < L) (hD : D < (2:ℝ)^J)
    (hS : ∀ r ∈ S, L ≤ norm r ∧ norm r ≤ D*L) (f : Eisenstein → ℂ) :
    (∑ r ∈ S, f r) = ∑ j ∈ Finset.range J, ∑ r ∈ typeIMixedDyad S L j, f r := by
  exact (Finset.sum_fiberwise_of_maps_to (fun r hr =>
    Finset.mem_range.mpr (typeIMixedDyadIndex_lt hL hD (hS r hr).1 (hS r hr).2)) f).symm

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightMeanSquare
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite spectral expansion of the height-averaged square.
The diagonal and every off-diagonal pair are retained. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma continuous_normTwist (b : Eisenstein) : Continuous (fun u : ℝ => normTwist u b) := by
  unfold normTwist
  fun_prop

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseEnvelopeWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed product envelope in the sparse branch gives an actual
uniform family of inner weights on every fixed outer norm dyad. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma log_dyad_ratio {a A M : ℝ} (hA : 0 < A) (_hM : 1 ≤ M)
    (ha : A ≤ a) (haM : a ≤ M*A) :
    0 < a/A ∧ |Real.log (a/A)| ≤ Real.log M := by
  have hratio : 1 ≤ a/A := (le_div_iff₀ hA).mpr (by simpa using ha)
  have hupper : a/A ≤ M := (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using haM)
  refine ⟨zero_lt_one.trans_le hratio,?_⟩
  rw [abs_of_nonneg (Real.log_nonneg hratio)]
  exact Real.log_le_log (zero_lt_one.trans_le hratio) hupper

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogPowerSaving
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial logarithmic cost of the central integral is absorbed
by the already proved fixed power saving. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem log_power_powerSaving_isLittleO (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (fun X : ℝ => (1+Real.log X)^d*X^(5/6-δ)) =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := log_power_normalization_bound d (show 0 < δ/2 by positivity)
  apply isLittleO_of_powerSaving (show 0 < δ/2 by positivity)
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
  have he : X^(-(δ/2))*X^(5/6-δ/2) = X^(5/6-δ) := by
    rw [←Real.rpow_add hXp]
    congr 1
    ring
  calc
    _ = (X^(-(δ/2))*(1+Real.log X)^d)*X^(5/6-δ/2) := by rw [←he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hbound X hX) (Real.rpow_nonneg hXp.le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortOuterLow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum all short outer norm dyads in the central corrected kernel.
The dyad count costs one logarithm, and all weights and support are actual. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma shortOuterCount_covers {Y : ℝ} (hY : 0 < Y) : Y < (2:ℝ)^shortOuterCount Y := by
  have hl : Real.log (2*Y) ≤ Real.log ((2:ℝ)^shortOuterCount Y) := by
    rw [Real.log_pow]
    exact (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp (Nat.le_ceil _)
  have hh := (Real.log_le_log_iff (by positivity : 0 < 2*Y) (by positivity)).mp hl
  linarith

lemma shortOuterCount_scale {Y : ℝ} (hY : 0 < Y) {j : ℕ} (hj : j < shortOuterCount Y) :
    (2:ℝ)^j < 2*Y := by
  have hj' : (j:ℝ) < Real.log (2*Y)/Real.log 2 := Nat.lt_ceil.mp hj
  apply (Real.log_lt_log_iff (by positivity : (0:ℝ) < 2^j) (by positivity)).mp
  rw [Real.log_pow]
  exact (lt_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp hj'

theorem shortOuterCount_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y → (shortOuterCount Y:ℝ) ≤ C*(1+Real.log Y) := by
  obtain ⟨C,hC,hbound⟩ := geometricBinCount_log_bound (by norm_num : (1:ℝ) < 2)
  refine ⟨C*(1+Real.log 2),by positivity,?_⟩
  intro Y hY
  apply (hbound (2*Y) (by linarith)).trans
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by linarith : Y ≠ 0)]
  have hlog := Real.log_nonneg hY
  have htwo := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  calc
    C*(1+(Real.log 2+Real.log Y)) ≤ C*((1+Real.log 2)*(1+Real.log Y)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg htwo hlog]) hC.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightWindowSum
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedScalePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript partitions the distinguished prime scales before
splitting the rough remainder. This exact finite partition introduces no
partial-product cutoff in a high-scale coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguishedScaleCoefficient_norm (i : ℕ) (ξ X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (r : Eisenstein) :
    ‖distinguishedScaleCoefficient i ξ X k r‖ ≤ ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ) := by
  simpa only [Fintype.card_fin,distinguishedScaleCoefficient] using distinguishedTupleCoefficient_norm (ι := Fin i) _
    (fun _ _ hp => (mem_primeCutoff.mp hp).1) _
    (fun _ p _ => normPartitionWeight_norm _)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) _ _ r

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every fixed divisor moment on primary squarefree elements follows from
the finite Euler product and the already specified ordinary prime theorem. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_fixed_reciprocal_sum (q : ℝ) (hq : 0 ≤ q) (S U : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hU : ∀ b ∈ S, primaryPrimeFactors b ⊆ U) :
    (∑ b ∈ S, q^(primaryPrimeFactors b).card / norm b) ≤
      ∏ p ∈ U, (1+q/norm p) := by
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
    exact Finset.prod_nonneg (fun p _ => div_nonneg hq (norm_nonneg p))

lemma squarefree_fixed_sum_le_euler (q : ℝ) (hq : 0 ≤ q) (S : Finset Eisenstein) {X : ℝ}
    (hX : 0 ≤ X) (hS : ∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ X) :
    (∑ b ∈ S, q^(primaryPrimeFactors b).card) ≤
      X*Real.exp (q*∑ p ∈ primeCutoff X, (norm p)⁻¹) := by
  have hsub : ∀ b ∈ S, primaryPrimeFactors b ⊆ primeCutoff X := by
    intro b hb p hp
    have hprime := primaryPrimeFactor_spec (hS b hb).1 hp
    exact mem_primeCutoff.mpr ⟨hprime.1,
      (norm_le_of_dvd_nonzero (primary_ne_zero (hS b hb).1) hprime.2).trans (hS b hb).2.2⟩
  have hprod : (∏ p ∈ primeCutoff X, (1+q/norm p)) ≤
      Real.exp (q*∑ p ∈ primeCutoff X, (norm p)⁻¹) := by
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      exact add_nonneg zero_le_one (div_nonneg hq (norm_nonneg p))
    · intro p hp
      simpa only [div_eq_mul_inv,add_comm] using Real.add_one_le_exp (q*(norm p)⁻¹)
  calc
    _ ≤ ∑ b ∈ S, X*(q^(primaryPrimeFactors b).card/norm b) := by
      apply Finset.sum_le_sum
      intro b hb
      have hb0 := norm_pos_of_ne_zero (primary_ne_zero (hS b hb).1)
      calc
        _ = norm b*(q^(primaryPrimeFactors b).card/norm b) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (hS b hb).2.2 (by positivity)
    _ = X*∑ b ∈ S, q^(primaryPrimeFactors b).card/norm b := by rw [Finset.mul_sum]
    _ ≤ X*(∏ p ∈ primeCutoff X, (1+q/norm p)) :=
      mul_le_mul_of_nonneg_left (squarefree_fixed_reciprocal_sum q hq S (primeCutoff X)
        (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) hsub) hX
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod hX

theorem squarefree_fixed_divisor_moment (hpnt : PrimaryPrimePNT) (q : ℝ) (hq : 0 ≤ q) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (X : ℝ) (S : Finset Eisenstein),
      Real.exp 1 ≤ X →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ X) →
      (∑ b ∈ S, q^(primaryPrimeFactors b).card) ≤ K*X*(1+Real.log X)^d := by
  obtain ⟨C,hC,hprime⟩ := primaryPrime_reciprocal_exp_bound hpnt
  obtain ⟨d,hd⟩ := exists_nat_ge (q*C)
  refine ⟨Real.exp (q*C),d,Real.exp_pos _,?_⟩
  intro X S hX hS
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hl : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hl0 : 0 < Real.log X := zero_lt_one.trans_le hl
  have hrec := hprime (Real.log X) hl
  rw [Real.exp_log hX0] at hrec
  have he : Real.exp (q*(C*(1+Real.log (Real.log X)))) =
      Real.exp (q*C)*(Real.log X)^(q*C) := by
    rw [Real.rpow_def_of_pos hl0,←Real.exp_add]
    congr 1
    ring
  have hpow : (Real.log X)^(q*C) ≤ (1+Real.log X)^d := by
    calc
      _ ≤ (Real.log X)^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le hl hd
      _ = (Real.log X)^d := Real.rpow_natCast _ _
      _ ≤ _ := pow_le_pow_left₀ hl0.le (by linarith : Real.log X ≤ 1+Real.log X) d
  calc
    _ ≤ X*Real.exp (q*∑ p ∈ primeCutoff X, (norm p)⁻¹) :=
      squarefree_fixed_sum_le_euler q hq S hX0.le hS
    _ ≤ X*Real.exp (q*(C*(1+Real.log (Real.log X)))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hrec hq)) hX0.le
    _ = X*(Real.exp (q*C)*(Real.log X)^(q*C)) := by rw [he]
    _ ≤ X*(Real.exp (q*C)*(1+Real.log X)^d) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)) hX0.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightIntegralMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer an actual positive height majorant to a supported integral.
No regularity of the complex integrand is assumed beyond the majorant. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma normalized_dyadic_integral_majorant (f h : ℝ → ℂ) (g : ℝ → ℝ)
    (hg : Continuous g) {T : ℝ} (hT : 0 < T)
    (hh : ∀ t, ‖h t‖ ≤ 1)
    (hs : ∀ t, t ∉ dyadicHeightSupport T → h t = 0)
    (hfg : ∀ t, ‖f t‖ ≤ g t) :
    ‖(T:ℂ)⁻¹*(∫ t : ℝ, h t*f t)‖ ≤ dyadicHeightMean g T := by
  let S := dyadicHeightSupport T
  have hS : MeasurableSet S := measurableSet_Icc.union measurableSet_Icc
  have hi : Integrable (S.indicator g) :=
    (hg.continuousOn.integrableOn_compact
      (isCompact_Icc.union isCompact_Icc)).integrable_indicator hS
  have hb : ‖∫ t : ℝ, h t*f t‖ ≤ ∫ t : ℝ, S.indicator g t := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards with t
    by_cases ht : t ∈ S
    · rw [indicator_of_mem ht,norm_mul]
      exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (hh t)).trans (hfg t)
    · rw [indicator_of_notMem ht,hs t ht,zero_mul,norm_zero]
  have hd : Disjoint (Icc T (2*T)) (Icc (-2*T) (-T)) := by
    apply Set.disjoint_left.mpr
    intro t hp hn
    linarith [hp.1,hn.2]
  rw [integral_indicator hS] at hb
  change ‖∫ t : ℝ, h t*f t‖ ≤ ∫ t in Icc T (2*T) ∪ Icc (-2*T) (-T), g t at hb
  rw [setIntegral_union hd measurableSet_Icc hg.integrableOn_Icc hg.integrableOn_Icc,
    integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by linarith : T ≤ 2*T),
    ←intervalIntegral.integral_of_le (by linarith : -2*T ≤ -T)] at hb
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hT.le]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hT.le)).trans_eq
  dsimp [dyadicHeightMean]
  ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticInversePoleMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse completion preserves the radial pole error. Its cube-divisor
weight is the absolutely summable inverse square norm. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_inverse_signed_mean_with_pole
    (r : Eisenstein) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    {U B F T H J : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (hT : 0 < T)
    (hmean : ∀ c ∈ primaryElementBall F,
      ((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r 0 W (U/norm c^3) t‖)+
        (∫ t in T..2*T, ‖metaplecticHeightCompleted r 0 W (U/norm c^3) t‖))/T ≤
          H*Real.sqrt (U/norm c^3)+J*(U/norm c^3)^(5/6:ℝ)) :
    ((∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r 0 W U t‖)+
      (∫ t in T..2*T, ‖metaplecticAngularSmoothSum r 0 W U t‖))/T ≤
        H*Real.sqrt U*(∑ c ∈ primaryElementBall F, norm c^(-1:ℝ))+
          J*U^(5/6:ℝ)*(∑ c ∈ primaryElementBall F, norm c^(-2:ℝ)) := by
  have hn := metaplectic_inverse_interval_norm r 0 W hWc hU hB hBF hW
    (show -(2*T) ≤ -T by linarith)
  have hp := metaplectic_inverse_interval_norm r 0 W hWc hU hB hBF hW
    (show T ≤ 2*T by linarith)
  calc
    _ ≤ ((∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
          (∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r 0 W (U/norm c^3) t‖))+
        (∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
          (∫ t in T..2*T, ‖metaplecticHeightCompleted r 0 W (U/norm c^3) t‖)))/T :=
      div_le_div_of_nonneg_right (add_le_add hn hp) hT.le
    _ = ∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
        (((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r 0 W (U/norm c^3) t‖)+
          (∫ t in T..2*T, ‖metaplecticHeightCompleted r 0 W (U/norm c^3) t‖))/T) := by
      rw [←Finset.sum_add_distrib,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ ∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
        (H*Real.sqrt (U/norm c^3)+J*(U/norm c^3)^(5/6:ℝ)) :=
      Finset.sum_le_sum (fun c hc => mul_le_mul_of_nonneg_left (hmean c hc) (Real.sqrt_nonneg _))
    _ = _ := by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      have hcp := norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp hc).1)
      calc
        _ = H*(Real.sqrt (norm c)*Real.sqrt (U/norm c^3))+
            J*(Real.sqrt (norm c)*(U/norm c^3)^(5/6:ℝ)) := by ring
        _ = _ := by
          rw [metaplectic_inverse_sqrt_scale hU.le hcp,
            metaplectic_inverse_residue_scale hU hcp,Real.rpow_neg_one]
          ring

lemma primary_inverse_square_sum_bound (F : ℝ) :
    (∑ c ∈ primaryElementBall F, norm c^(-2:ℝ)) ≤
      ∑' c : Eisenstein, norm c^(-2:ℝ) :=
  (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 2)).sum_le_tsum _
    (fun c _ => Real.rpow_nonneg (norm_nonneg c) _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIHeightIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal Type-I height integral is bounded by the published-input
mean estimates, with the outer norm phase and interval endpoint retained. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma typeIHeightIntegral_le_mean {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (ℓ : ℤ) {U T : ℝ} (hU : 0 < U) (hT : 0 < T)
    (H X₀ : ℝ) :
    ‖typeIHeightIntegral w S α W ℓ U H T X₀‖ ≤
      dyadicHeightMean (fun t => ∑ r ∈ S,
        ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖) T := by
  apply normalized_dyadic_integral_majorant
  · apply continuous_finsetSum
    intro r _
    exact continuous_const.mul
      (continuous_metaplecticAngularSmoothSum_of_cutoff r ℓ (W (w r)) hU
        (le_refl (Real.exp hW.radius*U)) (hW.upper_support (w r))).norm
  · exact hT
  · intro t
    rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
    exact localizedEndpointWeight_norm_le H hT t
  · intro t ht
    rw [localizedEndpointWeight_zero H hT t ht,zero_mul]
  · intro t
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro r _
    simp only [norm_mul,norm_normTwist,mul_one,le_refl]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RadialTypeIIntegral
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial Type-I cutoff integral from the Voronoi formula alone,
in the two exact height ranges used by the main proof. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma typeI_range_height_le_square {X R T κ ρ : ℝ} (hX : 1 ≤ X) (hR : 1 ≤ R)
    (hρ : ρ ≤ κ/4)
    (hrange : (R ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
      (R ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+ρ))) : T ≤ X^2 := by
  rcases hrange with ⟨_,ht⟩ | ⟨hr,ht⟩
  · exact ht.trans (by simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1/100:ℝ) ≤ 2))
  · by_cases hx : X = 1
    · simpa only [hx,Real.one_rpow,one_pow] using ht
    · have hXgt : 1 < X := lt_of_le_of_ne hX (Ne.symm hx)
      have he : (0:ℝ) ≤ 1/3-κ/2 := by
        apply (Real.rpow_le_rpow_left_iff hXgt).mp
        simpa only [Real.rpow_zero] using hR.trans hr
      exact ht.trans (by simpa only [Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_le hX (by linarith : 1/6+ρ ≤ 2))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RestrictedNoStopCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Type-I collection for a no-stop branch with an additional
predicate on the distinguished and selected factors. In particular the
failed first-stage prefix is preserved. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma restrictedNoStop_coefficient_collection (S R : Finset Eisenstein)
    (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w ρ X Z : ℝ)
    (P : Eisenstein → Eisenstein → Prop) (K : Eisenstein → ℂ) :
    (∑ r ∈ R, v r*∑ u ∈ primaryElementBall X,
      ∑ m ∈ primaryProductSlice S X (r*u) with
        norm r*primeSurrogate (primaryPrimeFactors m)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z ∧ P r m,
        cutoffMoebius ψ w m*K (r*(m*u))) =
    ∑ b ∈ primaryPairSupport R (primaryElementBall X),
      restrictedNoStopCoefficient R (primaryElementBall X) v ψ w ρ X Z P b *
        ∑ u ∈ primaryElementBall X, if b*u ∈ S then K (b*u) else 0 := by
  unfold restrictedNoStopCoefficient stoppedBeta
  rw [primaryPairCoefficient_sum,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r _
  simp only [primaryProductSlice,Finset.sum_filter,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro m _
  have he : (r*u)*m = (r*m)*u := by ring
  simp only [he]
  split_ifs <;> ring_nf

lemma restrictedNoStop_coefficient_divisor_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w ρ X Z : ℝ)
    (P : Eisenstein → Eisenstein → Prop) (v : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ r ∈ R, ‖v r‖ ≤ M) {b : Eisenstein} (hb : primary b) :
    ‖restrictedNoStopCoefficient R D v ψ w ρ X Z P b‖ ≤
      M*((metaplecticPrimaryDivisors b).card:ℝ) := by
  have hsub : R.filter (fun r => r ∣ b) ⊆ metaplecticPrimaryDivisors b := by
    intro r hr
    obtain ⟨hrR,hrb⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr
      ⟨hR r hrR,norm_le_of_dvd (primary_ne_zero hb) hrb⟩,hrb⟩
  apply (stoppedBeta_divisor_bound R D hR hψ w _ v hM hv b).trans
  calc
    _ ≤ ((metaplecticPrimaryDivisors b).card:ℝ)*M :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub)) hM
    _ = _ := mul_comm _ _

lemma restrictedNoStop_coefficient_nonzero (R D : Finset Eisenstein)
    (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w ρ X Z : ℝ)
    (P : Eisenstein → Eisenstein → Prop) {b : Eisenstein}
    (hb : restrictedNoStopCoefficient R D v ψ w ρ X Z P b ≠ 0) :
    ∃ r ∈ R, ∃ m ∈ D, r*m = b ∧ Squarefree m ∧
      norm r*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z := by
  unfold restrictedNoStopCoefficient stoppedBeta primaryPairCoefficient at hb
  obtain ⟨p,hp,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  obtain ⟨hp,hprod⟩ := Finset.mem_filter.mp hp
  obtain ⟨hr,hm⟩ := Finset.mem_product.mp hp
  have hsel : norm p.1*primeSurrogate (primaryPrimeFactors p.2)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z ∧ P p.1 p.2 := by
    by_contra h
    exact hterm (ite_eq_right h)
  rw [ite_eq_left hsel] at hterm
  exact ⟨p.1,hr,p.2,hm,hprod,
    cutoffMoebius_ne_zero_squarefree (mul_ne_zero_iff.mp hterm).2,hsel.1⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RestrictedNoStopSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The additional first-stage predicate does not alter the proved
short support of any surviving no-stop outer coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem restricted_noStop_short_support {κ : ℝ} (hκ : 0 < κ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (R : Finset Eisenstein) (v : Eisenstein → ℂ) (ψ : ℝ → ℝ)
        (w Z : ℝ) (P : Eisenstein → Eisenstein → Prop) (b : Eisenstein),
        restrictedNoStopCoefficient R (primaryElementBall X) v ψ w ρ X Z P b ≠ 0 →
        norm b < X^(κ/4)*Z := by
  obtain ⟨r,hr,hbound⟩ := uniform_prime_bin_distortion hκ (by norm_num : (0:ℝ) < 1)
  let ρ := min (min r cap) 2
  have hρ : 1 < ρ := lt_min (lt_min hr hcap) (by norm_num)
  have hρ₂ : ρ ≤ 2 := min_le_right _ _
  refine ⟨ρ,hρ,hρ₂,(min_le_left _ _).trans (min_le_right _ _),?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with X hX hXp
  intro R v ψ w Z P b hb
  obtain ⟨a,_,m,hm,hab,hms,hsel⟩ := restrictedNoStop_coefficient_nonzero R
    (primaryElementBall X) v ψ w ρ X Z P hb
  obtain ⟨hmp,hmX⟩ := mem_primaryElementBall.mp hm
  have hc (p : Eisenstein) (hp : p ∈ primaryPrimeFactors m) :
      0 ≤ geometricBinLower ρ X (geometricPrimeBin ρ X p) ∧
      geometricBinLower ρ X (geometricPrimeBin ρ X p) ≤ norm p ∧
      norm p ≤ r*geometricBinLower ρ X (geometricPrimeBin ρ X p) := by
    obtain ⟨hpp,hpd⟩ := primaryPrimeFactor_spec hmp hp
    have hpX := (norm_le_of_dvd (primary_ne_zero hmp) hpd).trans hmX
    have hh := geometricPrimeBin_cell hρ hρ₂ hpp hpX
    have hl : 0 ≤ geometricBinLower ρ X (geometricPrimeBin ρ X p) := by
      unfold geometricBinLower
      positivity
    exact ⟨hl,hh.1,hh.2.le.trans (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) hl)⟩
  have hmB := (hX m hmp hms (by simpa only [one_mul] using hmX)
    (primaryPrimeFactors m) (Finset.Subset.refl _) (geometricPrimeBin ρ X)
    (geometricBinLower ρ X) hc).2
  rw [primaryPrimeFactors_prod hmp hms] at hmB
  rw [←hab,norm_mul_eq]
  calc
    _ ≤ norm a*(X^(κ/4)*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)) :=
      mul_le_mul_of_nonneg_left hmB (norm_nonneg _)
    _ = X^(κ/4)*(norm a*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)) := by ring
    _ < _ := mul_lt_mul_of_pos_left hsel (Real.rpow_pos_of_pos hXp _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstEarlyNegligible
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single logarithmic boundary makes all finitely many early stopped
arities negligible. No boundary is chosen before the analytic constants. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stopped_log_quotient_normalize (d k : ℕ) {L K P : ℝ}
    (hL : 1 ≤ L) (hK : 0 ≤ K) (hP : 0 ≤ P) :
    (1+L)^d*(K*P/L^(d+k)) ≤ (K*2^(d+k))*P/(1+L)^k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hL1 : 0 < 1+L := by linarith
  apply (le_div_iff₀ (pow_pos hL1 k)).mpr
  calc
    _ = (K*P)*((1+L)^(d+k)/L^(d+k)) := by
      rw [pow_add]
      field_simp
      ring
    _ ≤ (K*P)*2^(d+k) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK hP)
      apply (div_le_iff₀ (pow_pos hLp (d+k))).mpr
      rw [←mul_pow]
      exact pow_le_pow_left₀ hL1.le (by linarith : 1+L ≤ 2*L) _
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeTypeIMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coefficient mass for the actual squarefree Type-I outer levels.
Only the primary-prime theorem enters the divisor moment. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma squarefree_primary_divisor_card_le {n : Eisenstein}
    (hn : primary n) (hs : Squarefree n) :
    (metaplecticPrimaryDivisors n).card ≤ 2^(primaryPrimeFactors n).card := by
  rw [primary_divisors_of_squarefree_eq hn hs]
  exact (Finset.card_image_le).trans_eq (Finset.card_powerset _)

theorem squarefree_typeI_coefficient_mass (hpnt : PrimaryPrimePNT)
    {M : ℝ} (hM : 0 ≤ M) (k : ℕ) :
    ∃ (K : ℝ) (d : ℕ), 0 ≤ K ∧ ∀ (X R : ℝ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ), 1 ≤ R → R ≤ X → 1 ≤ Real.log X →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, ‖α r‖ ≤ M*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      (∑ r ∈ S, ‖α r‖) ≤ K*R*(Real.log X)^d := by
  obtain ⟨C,d,hC,hmoment⟩ := squarefree_fixed_divisor_moment hpnt ((2:ℝ)^k) (by positivity)
  let A : ℝ := 2+Real.exp 1
  have hA : 1 < A := by dsimp [A]; linarith [Real.exp_pos (1:ℝ)]
  have hAl : 0 ≤ Real.log A := Real.log_nonneg hA.le
  refine ⟨M*C*A*(2+Real.log A)^d,d,by positivity,?_⟩
  intro X R S α hR hRX hlog hS hα
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hXp : 0 < X := hRp.trans_le hRX
  have hAR : Real.exp 1 ≤ A*R := by
    calc
      Real.exp 1 ≤ A := by dsimp [A]; linarith
      _ ≤ A*R := le_mul_of_one_le_right (zero_le_one.trans hA.le) hR
  have htwo : 2*R ≤ A*R := mul_le_mul_of_nonneg_right (by dsimp [A]; linarith [Real.exp_pos (1:ℝ)]) hRp.le
  have hm := hmoment (A*R) S hAR (fun r hr =>
    ⟨(hS r hr).1,(hS r hr).2.1,(hS r hr).2.2.trans htwo⟩)
  have hL : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hlogs : 1+Real.log (A*R) ≤ (2+Real.log A)*Real.log X := by
    rw [Real.log_mul (by positivity : A ≠ 0) hRp.ne']
    have hrl : Real.log R ≤ Real.log X := Real.log_le_log hRp hRX
    nlinarith [mul_nonneg hAl (sub_nonneg.mpr hlog)]
  calc
    _ ≤ ∑ r ∈ S, M*((2:ℝ)^k)^(primaryPrimeFactors r).card := by
      apply Finset.sum_le_sum
      intro r hr
      apply (hα r hr).trans
      have hc : ((metaplecticPrimaryDivisors r).card:ℝ) ≤ (2:ℝ)^(primaryPrimeFactors r).card := by
        exact_mod_cast squarefree_primary_divisor_card_le (hS r hr).1 (hS r hr).2.1
      have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hc k) hM
      simpa only [←pow_mul,mul_comm k] using hh
    _ = M*∑ r ∈ S, ((2:ℝ)^k)^(primaryPrimeFactors r).card := by rw [Finset.mul_sum]
    _ ≤ M*(C*(A*R)*(1+Real.log (A*R))^d) := mul_le_mul_of_nonneg_left hm hM
    _ ≤ M*(C*(A*R)*((2+Real.log A)*Real.log X)^d) := by
      gcongr
      · linarith [Real.log_nonneg (show 1 ≤ A*R by nlinarith)]
    _ = _ := by rw [mul_pow]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeICutoffWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cutoff window of the Type-I polynomial is the difference
of its two normalized endpoint integrals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma continuous_typeIHeightPolynomial {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (ℓ : ℤ) {U : ℝ} (hU : 0 < U) :
    Continuous (typeIHeightPolynomial w S α W ℓ U) := by
  apply continuous_finsetSum
  intro r _
  exact (continuous_const.mul (continuous_normTwist r)).mul
    (continuous_metaplecticAngularSmoothSum_of_cutoff r ℓ (W (w r)) hU
      (le_refl (Real.exp hW.radius*U)) (hW.upper_support (w r)))

theorem typeICutoffWindow_endpoints {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (ℓ : ℤ) {U T X₀ : ℝ} (hU : 0 < U) (hT : 0 < T)
    (hX₀ : 0 < X₀) (H : ℝ) :
    typeICutoffWindow w S α W ℓ U H T X₀ =
      typeIHeightIntegral w S α W ℓ U H T X₀-
        typeIHeightIntegral w S α W ℓ U H T (2*X₀) := by
  let f := typeIHeightPolynomial w S α W ℓ U
  have hf : Continuous f := continuous_typeIHeightPolynomial hW w S α ℓ hU
  have hi (Y : ℝ) : Integrable (fun t : ℝ =>
      (localizedEndpointWeight H T t*Complex.exp ((-Real.log Y*t:ℝ)*Complex.I))*f t) := by
    have he : Continuous (fun t : ℝ => Complex.exp ((-Real.log Y*t:ℝ)*Complex.I)) := by
      fun_prop
    exact (((localizedEndpointWeight_smooth H hT).continuous.mul he).mul hf).integrable_of_hasCompactSupport
      ((localizedEndpointWeight_compact H hT).mul_right.mul_right)
  change (∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow T t*
    Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*f t) =
      (T:ℂ)⁻¹*(∫ t : ℝ, (localizedEndpointWeight H T t*
        Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*f t)-
      (T:ℂ)⁻¹*(∫ t : ℝ, (localizedEndpointWeight H T t*
        Complex.exp ((-Real.log (2*X₀)*t:ℝ)*Complex.I))*f t)
  rw [←mul_sub,←integral_sub (hi X₀) (hi (2*X₀)),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [cutoffHeightMultiplier_window_endpoints H hT t]
  have he : Complex.exp ((-Real.log (2*X₀)*t:ℝ)*Complex.I) =
      Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
        Complex.exp ((-Real.log 2*t:ℝ)*Complex.I) := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hX₀.ne',←Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem typeI_gaussWindow_envelope_row (ℓ : ℤ) (W : ℝ → ℂ)
    {B X R U : ℝ} (hB : 0 ≤ B) (hR : 1 ≤ R) (hU : 0 < U) (hRU : R*U = X)
    (hW : ∀ x : ℝ, B < x → W x = 0) (H T X₀ : ℝ)
    {r : Eisenstein} (hr : primary r) (hRr : R ≤ norm r) :
    (∑ u ∈ primaryElementBall (B*X),
      if r*u ∈ squarefreeProductEnvelope (B*X) then productGaussHeightWindowKernel ℓ W H T X X₀ (r*u) else 0) =
      ∑ u ∈ primaryElementBall (B*U), productGaussHeightWindowKernel ℓ W H T X X₀ (r*u) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hX : 0 < X := by rw [←hRU]; positivity
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left hU.le hR
  have hsub : primaryElementBall (B*U) ⊆ primaryElementBall (B*X) := by
    intro u hu
    obtain ⟨hup,huB⟩ := mem_primaryElementBall.mp hu
    exact mem_primaryElementBall.mpr ⟨hup,huB.trans (mul_le_mul_of_nonneg_left hUX hB)⟩
  calc
    _ = ∑ u ∈ primaryElementBall (B*X), productGaussHeightWindowKernel ℓ W H T X X₀ (r*u) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact productGaussHeightWindowKernel_envelope ℓ W hX hW H T X₀
        (primary_mul hr (mem_primaryElementBall.mp hu).1)
    _ = _ := by
      symm
      apply Finset.sum_subset hsub
      intro u hu hn
      have hup := (mem_primaryElementBall.mp hu).1
      have huB : B*U < norm u := lt_of_not_ge
        (fun huB => hn (mem_primaryElementBall.mpr ⟨hup,huB⟩))
      have hnX : B*X < norm (r*u) := by
        rw [norm_mul_eq,←hRU]
        calc
          B*(R*U) = R*(B*U) := by ring
          _ < R*norm u := mul_lt_mul_of_pos_left huB hRp
          _ ≤ norm r*norm u := mul_le_mul_of_nonneg_right hRr (norm_nonneg _)
      have hz := hW (norm (r*u)/X) ((lt_div_iff₀ hX).mpr hnX)
      simp only [productGaussHeightWindowKernel,hz,mul_zero,zero_mul]

theorem productTypeICutoffWindow_fourier {γ : Type*} (w : Eisenstein → γ)
    (P : Finset Eisenstein) (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ)
    (ℓ : ℤ) (B X U T X₀ : ℝ) {H : ℝ} (hH : 0 < H) :
    productTypeICutoffWindow w P α W ℓ B X U H T X₀ =
      ∑ r ∈ P, α r*∑ u ∈ primaryElementBall (B*U),
        productGaussHeightWindowKernel ℓ (W (w r)) H T X X₀ (r*u) := by
  let Q := primaryElementBall (B*U)
  let c : Eisenstein × Eisenstein → ℂ := fun q =>
    α q.1*(theta ℓ (q.1*q.2)*gauss (q.1*q.2)*W (w q.1) (norm (q.1*q.2)/X))
  have hb := height_norm_polynomial_integral (P.product Q) c (fun q => q.1*q.2)
    (fun t => cutoffHeightMultiplier H t*heightWindow T t)
    (integrable_cutoffHeightMultiplier_window hH T) (Real.log X₀)
  simp only [Finset.product_eq_sprod,Finset.sum_product] at hb
  calc
    _ = ∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow T t*
        Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
          ∑ r ∈ P, ∑ u ∈ Q, c (r,u)*normTwist t (r*u) := by
      unfold productTypeICutoffWindow
      apply integral_congr_ae
      filter_upwards with t
      simp only [Finset.mul_sum,c,Q]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = ∑ r ∈ P, ∑ u ∈ Q, c (r,u)*
        heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow T t)
          (Real.log (norm (r*u))-Real.log X₀) := hb.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      dsimp [c,Q,productGaussHeightWindowKernel]
      ring

/-- The original product polynomial is exactly a Type-I polynomial with
uniformly dilated inner weights. No height-dependent weight is introduced. -/
theorem productTypeICutoffWindow_dilate {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) (w : Eisenstein → γ) (P : Finset Eisenstein)
    (α : Eisenstein → ℂ) (ℓ : ℤ) {X R U : ℝ}
    (hR : 1 ≤ R) (hU : 0 < U) (hRU : R*U = X)
    (hP : ∀ r ∈ P, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) :
    ∃ v : Eisenstein → γ × {s : ℝ // 0 < s ∧ |Real.log s| ≤ Real.log 2},
      ∀ H T X₀ : ℝ,
      productTypeICutoffWindow w P α W ℓ (Real.exp hW.radius) X U H T X₀ =
        typeICutoffWindow v P α
          (fun z : γ × {s : ℝ // 0 < s ∧ |Real.log s| ≤ Real.log 2} =>
            fun x => W z.1 (z.2*x)) ℓ U H T X₀ := by
  let δ := {s : ℝ // 0 < s ∧ |Real.log s| ≤ Real.log 2}
  let V : γ × δ → ℝ → ℂ := fun z x => W z.1 (z.2*x)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  let s : Eisenstein → δ := fun r => if hr : r ∈ P then
    ⟨norm r/R,log_dyad_ratio hRp (by norm_num) (hP r hr).2.1 (hP r hr).2.2⟩
    else ⟨1,by simp; exact Real.log_nonneg (by norm_num)⟩
  let v : Eisenstein → γ × δ := fun r => (w r,s r)
  refine ⟨v,?_⟩
  intro H T X₀
  have hv (r : Eisenstein) (hr : r ∈ P) :
      V (v r) = fun x => W (w r) ((norm r/R)*x) := by
    funext x
    simp only [V,v,s,dite_eq_left hr]
  have hcut (r : Eisenstein) (hr : r ∈ P) (x : ℝ)
      (hx : Real.exp hW.radius < x) : V (v r) x = 0 := by
    rw [hv r hr]
    apply hW.upper_support (w r)
    have hratio : 1 ≤ norm r/R := (le_div_iff₀ hRp).mpr (by simpa using (hP r hr).2.1)
    exact hx.trans_le (le_mul_of_one_le_left (by linarith [Real.exp_pos hW.radius]) hratio)
  unfold productTypeICutoffWindow typeICutoffWindow typeIHeightPolynomial
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [metaplecticAngularSmoothSum_finite r ℓ (V (v r)) hU le_rfl (hcut r hr) t,
    Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have harg : (norm r/R)*(norm u/U) = norm (r*u)/X := by
    rw [norm_mul_eq,←hRU]
    field_simp
  have hp : normTwist t (r*u) = normTwist t r*mellinPhase t (norm u) :=
    normTwist_mul t (primary_ne_zero (hP r hr).1)
      (primary_ne_zero (mem_primaryElementBall.mp hu).1)
  change α r*(theta ℓ (r*u)*gauss (r*u)*normTwist t (r*u)*W (w r) (norm (r*u)/X)) =
    (α r*normTwist t r)*(V (v r) (norm u/U)*
      (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u)))
  rw [hv r hr]
  dsimp only
  rw [harg,hp]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UpperNoStopParameters
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal no-stop thresholds in the two height ranges. The upper
range uses the smaller stopping level required by the Type-I exponent. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventually_ordinary_noStop_window_scales {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) :
    ∀ᶠ X : ℝ in atTop,
      1 ≤ X^(39/100:ℝ) ∧
      (Real.exp hW.radius*X)^((1/100:ℝ)/4)*X^(38/100:ℝ) ≤ X^(39/100:ℝ) ∧
      2*X^(39/100:ℝ) ≤ X^(2/5:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (by norm_num : (1/400:ℝ)+38/100 < 39/100)
      ((Real.exp hW.radius)^(1/400:ℝ)),
    eventually_const_mul_rpow_le (by norm_num : (39/100:ℝ) < 2/5) 2]
    with X hX hd hs
  refine ⟨Real.one_le_rpow hX (by norm_num),?_,hs⟩
  have hXp : 0 < X := zero_lt_one.trans_le hX
  norm_num only [show (1/100:ℝ)/4 = 1/400 by norm_num]
  rw [Real.mul_rpow (Real.exp_pos _).le hXp.le,mul_assoc,←Real.rpow_add hXp]
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstNoStopTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal ordinary-height no-stop row in the prime tail has the
published Type-I saving. Its failed first-stage prefix is preserved. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma scaleFirstTailNoStopRow_eq_window (i : ℕ) (ℓ : ℤ) (ρ ξ H U X : ℝ) (h : ℕ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    scaleFirstTailNoStopRow i ℓ ρ ξ H U X h d =
      restrictedNoStopGaussWindowValue (centralPrimaryFactors X)
        (distinguishedScaleCoefficient i ξ X d) primeDetectorCutoff (X^ξ) ρ
        (X^(38/100:ℝ)) (Real.exp primeProductWeights.radius) ℓ primeProductEnvelope H U X X
        (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h) := by
  unfold scaleFirstTailNoStopRow restrictedNoStopGaussWindowValue stoppingFailedPrefix
  simp only [centralProductEnvelope,centralPrimaryFactors,Finset.sum_filter,and_comm,
    scaleFirstTailKernel,productGaussHeightWindowKernel]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialInverse
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal radial Gauss sum inherits the proved two-sided mean by
finite inverse completion. The pole contributes its summable divisor tail. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_inverted_radial_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) (D : ℕ) :
    ∃ K E : ℝ, 0 ≤ K ∧ 0 ≤ E ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y U F T : ℝ, 1 ≤ Y → 0 < U → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ U → U ≤ Y^B →
      Real.exp h.radius*U ≤ F → F ≤ Y^B →
      ((∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r 0 (W i) U t‖)+
        (∫ t in T..2*T, ‖metaplecticAngularSmoothSum r 0 (W i) U t‖))/T ≤
          K*Real.sqrt U*Y^η*norm r^(1/4:ℝ)*Real.sqrt T+
            E*U^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D := by
  have hS : 1 ≤ Real.exp h.radius := Real.one_le_exp h.radius_nonneg
  have hhalf : 0 < η/2 := by positivity
  obtain ⟨K,E,hK,hE,hcompleted⟩ :=
    h.cubicTheta_completed_signed_radial_mean hMV hM hhalf
      (show 0 ≤ 4*B by positivity) D
  let α : ℝ := η/(2*(B+1))
  have hα : 0 < α := by dsimp [α]; positivity
  have hαB : B*α ≤ η/2 := by
    have he := div_mul_cancel₀ η (show 2*(B+1) ≠ 0 by positivity)
    change α*(2*(B+1)) = η at he
    nlinarith
  obtain ⟨C,hC,harmonic⟩ := primary_finite_harmonic_power hα
  let S : ℝ := ∑' c : Eisenstein, norm c^(-2:ℝ)
  have hSn : 0 ≤ S := tsum_nonneg (fun c => Real.rpow_nonneg (norm_nonneg c) _)
  refine ⟨K*C,E*S,mul_nonneg hK hC.le,mul_nonneg hE hSn,?_⟩
  intro i r hr hsr Y U F T hY hU hT hRY hTY hUlo hUhi hSF hFY
  have hYp := zero_lt_one.trans_le hY
  have hTp := zero_lt_one.trans_le hT
  have hRp := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hFp : 0 < F := (mul_pos (zero_lt_one.trans_le hS) hU).trans_le hSF
  have hB4 : B ≤ 4*B := by linarith
  have hRY4 : norm r ≤ Y^(4*B) := hRY.trans (Real.rpow_le_rpow_of_exponent_le hY hB4)
  have hTY4 : T ≤ Y^(4*B) := hTY.trans (Real.rpow_le_rpow_of_exponent_le hY hB4)
  let H : ℝ := K*Y^(η/2)*norm r^(1/4:ℝ)*Real.sqrt T
  let J : ℝ := E*norm r^(-1/6:ℝ)/T^D
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hmean (c : Eisenstein) (hc : c ∈ primaryElementBall F) :
      ((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r 0 (W i) (U/norm c^3) t‖)+
        (∫ t in T..2*T, ‖metaplecticHeightCompleted r 0 (W i) (U/norm c^3) t‖))/T ≤
          H*Real.sqrt (U/norm c^3)+J*(U/norm c^3)^(5/6:ℝ) := by
    obtain ⟨hcp,hcF⟩ := mem_primaryElementBall.mp hc
    obtain ⟨hX,hXlo,hXhi⟩ := metaplectic_inverse_length_range hY hB hUlo hUhi
      (one_le_norm (primary_ne_zero hcp)) (hcF.trans hFY)
    exact (hcompleted i r hr hsr Y (U/norm c^3) T hY hX hT
      hRY4 hTY4 hXlo hXhi).trans_eq (by dsimp [H,J]; ring)
  have hi := metaplectic_inverse_signed_mean_with_pole r (W i) (h.compact i) hU
    (zero_le_one.trans hS) hSF (h.upper_support i) hTp hmean
  have hs : (∑ c ∈ primaryElementBall F, norm c^(-1:ℝ)) ≤ C*Y^(η/2) := by
    apply (harmonic (primaryElementBall F) F hFp
      (fun c hc => (mem_primaryElementBall.mp hc).1)
      (fun c hc => (mem_primaryElementBall.mp hc).2)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    calc
      _ ≤ (Y^B)^α := Real.rpow_le_rpow hFp.le hFY hα.le
      _ = Y^(B*α) := (Real.rpow_mul hYp.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY hαB
  have hy : Y^(η/2)*Y^(η/2) = Y^η := by rw [←Real.rpow_add hYp]; congr 1; ring
  calc
    _ ≤ H*Real.sqrt U*(∑ c ∈ primaryElementBall F, norm c^(-1:ℝ))+
        J*U^(5/6:ℝ)*(∑ c ∈ primaryElementBall F, norm c^(-2:ℝ)) := hi
    _ ≤ H*Real.sqrt U*(C*Y^(η/2))+J*U^(5/6:ℝ)*S :=
      add_le_add (mul_le_mul_of_nonneg_left hs (by positivity))
        (mul_le_mul_of_nonneg_left (primary_inverse_square_sum_bound F) (by positivity))
    _ = (K*C*Real.sqrt U*norm r^(1/4:ℝ)*Real.sqrt T)*(Y^(η/2)*Y^(η/2))+
        (E*S)*U^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D := by dsimp [H,J]; ring
    _ = _ := by rw [hy]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialDyadic
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial dyadic height estimate in the polynomial range used by
the prime decomposition. No metaplectic mean-square input is required. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_radial_dyadic_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {η : ℝ} (hη : 0 < η) (D : ℕ) :
    ∃ K E : ℝ, 0 ≤ K ∧ 0 ≤ E ∧ ∀ i r, primary r → Squarefree r →
      ∀ X U T : ℝ, 1 ≤ X → 1 ≤ U → U ≤ X → 1 ≤ T → T ≤ X^2 → norm r ≤ 2*X →
      ((∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r 0 (W i) U t‖)+
        (∫ t in T..2*T, ‖metaplecticAngularSmoothSum r 0 (W i) U t‖))/T ≤
          K*Real.sqrt U*X^η*norm r^(1/4:ℝ)*Real.sqrt T+
            E*U^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D := by
  obtain ⟨K,E,hK,hE,hbound⟩ :=
    h.cubicTheta_inverted_radial_mean hMV hM hη (by norm_num : (0:ℝ) ≤ 2) D
  let S := max 2 (Real.exp h.radius)
  have hS : 1 ≤ S := le_trans (by norm_num) (le_max_left _ _)
  have hSp : 0 < S := zero_lt_one.trans_le hS
  refine ⟨K*S^η,E,by positivity,hE,?_⟩
  intro i r hr hsr X U T hX hU hUX hT hTX hRX
  have hXp := zero_lt_one.trans_le hX
  have hUp := zero_lt_one.trans_le hU
  let Y := S*X
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le hS hX
  have hYp := zero_lt_one.trans_le hY
  have hXY : X ≤ Y := le_mul_of_one_le_left hXp.le hS
  have hYsq : Y ≤ Y^2 := by nlinarith only [hY]
  have hR : norm r ≤ Y^2 := by
    apply hRX.trans
    have h2 : 2*X ≤ Y := mul_le_mul_of_nonneg_right (le_max_left _ _) hXp.le
    exact h2.trans hYsq
  have hTY : T ≤ Y^2 := hTX.trans (pow_le_pow_left₀ hXp.le hXY 2)
  have hUY : U ≤ Y^2 := hUX.trans (hXY.trans hYsq)
  have hlo : Y^(-(2:ℝ)) ≤ U := by
    calc
      _ ≤ Y^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
      _ = 1 := Real.rpow_zero _
      _ ≤ U := hU
  have hFY : Real.exp h.radius*U ≤ Y^2 := by
    have he := le_max_right (2:ℝ) (Real.exp h.radius)
    exact (mul_le_mul he hUX hUp.le hSp.le).trans hYsq
  have hb := hbound i r hr hsr Y U (Real.exp h.radius*U) T hY hUp hT
    (by simpa only [Real.rpow_two] using hR)
    (by simpa only [Real.rpow_two] using hTY) hlo
    (by simpa only [Real.rpow_two] using hUY) le_rfl
    (by simpa only [Real.rpow_two] using hFY)
  apply hb.trans_eq
  dsimp [Y]
  rw [Real.mul_rpow hSp.le hXp.le]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialTypeIHeight
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The required radial Type-I height mean, obtained directly from the
completed Voronoi formula and its finite inverse. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicTheta_radial_typeI_height
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {η : ℝ} (hη : 0 < η) (D d : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K E : ℝ, 0 ≤ K ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ) (R U T : ℝ),
      1 ≤ R → 1 ≤ U → 1 ≤ T → T ≤ (R*U)^2 →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^d →
      ((∫ t in T..2*T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖))/T ≤
          K*(R*U)^(1/2+η)*R^(3/4:ℝ)*Real.sqrt T+
            E*(R*U)^(5/6:ℝ)*(Real.log (R*U))^d/T^D := by
  have hhalf : 0 < η/2 := by positivity
  obtain ⟨C,E,hC,hE,hmean⟩ := hW.cubicTheta_radial_dyadic_mean hMV hM hhalf D
  obtain ⟨L,hL,hlog⟩ := typeI_log_power_bound d hhalf
  refine ⟨C*A*L*2^(1/4:ℝ),E*A,by positivity,by positivity,?_⟩
  intro w S α R U T hR hU hT hTX hS hα
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hX : 1 ≤ R*U := by nlinarith
  have hXp : 0 < R*U := by positivity
  have hRX : R ≤ R*U := le_mul_of_one_le_right hRp.le hU
  have hUX : U ≤ R*U := le_mul_of_one_le_left hUp.le hR
  let B : ℝ := C*Real.sqrt U*(R*U)^(η/2)*(2*R)^(1/4:ℝ)*Real.sqrt T+
    E*U^(5/6:ℝ)*R^(-1/6:ℝ)/T^D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (r : Eisenstein) (hr : r ∈ S) :
      ((∫ t in T..2*T, ‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖))/T ≤ B := by
    obtain ⟨hprim,hlower,hupper⟩ := hS r hr
    have hnr := norm_nonneg r
    by_cases hsf : Squarefree r
    · have hbound := hmean (w r) r hprim hsf (R*U) U T hX hU hUX hT hTX
        (hupper.trans (by linarith))
      rw [add_comm] at hbound
      apply hbound.trans
      dsimp [B]
      apply add_le_add
      · gcongr
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hRp hlower (by norm_num))
            (by positivity)) (pow_nonneg (zero_le_one.trans hT) _)
    · simp only [metaplecticAngularSmoothSum_zero_of_not_squarefree hprim hsf,
        norm_zero,intervalIntegral.integral_zero,add_zero,zero_div]
      exact hB
  rw [dyadic_finite_norm_sum S α (fun r => metaplecticAngularSmoothSum r 0 (W (w r)) U)
    (fun r _ => continuous_metaplecticAngularSmoothSum_of_cutoff r 0 (W (w r)) hUp
      (le_refl (Real.exp hW.radius*U)) (hW.upper_support (w r)))]
  have hmain : (C*Real.sqrt U*(R*U)^(η/2)*(2*R)^(1/4:ℝ)*Real.sqrt T)*
      (A*R*(Real.log (R*U))^d) ≤
      (C*A*L*2^(1/4:ℝ))*(R*U)^(1/2+η)*R^(3/4:ℝ)*Real.sqrt T := by
    calc
      _ = (C*A)*(Real.sqrt U*(2*R)^(1/4:ℝ)*R)*
          (R*U)^(η/2)*(Real.log (R*U))^d*Real.sqrt T := by ring
      _ ≤ (C*A)*(Real.sqrt U*(2*R)^(1/4:ℝ)*R)*
          (R*U)^(η/2)*(L*(R*U)^(η/2))*Real.sqrt T := by
        gcongr
        exact hlog _ hX
      _ = (C*A*L*2^(1/4:ℝ))*
          (Real.sqrt (R*U)*((R*U)^(η/2)*(R*U)^(η/2)))*R^(3/4:ℝ)*Real.sqrt T := by
        rw [angular_level_scaling hRp hUp]
        ring
      _ = _ := by
        rw [←Real.rpow_add hXp,show η/2+η/2=η by ring,
          Real.sqrt_eq_rpow,←Real.rpow_add hXp]
  have hpole : (E*U^(5/6:ℝ)*R^(-1/6:ℝ)/T^D)*(A*R*(Real.log (R*U))^d) =
      (E*A)*(R*U)^(5/6:ℝ)*(Real.log (R*U))^d/T^D := by
    calc
      _ = (E*A)*(U^(5/6:ℝ)*R^(-1/6:ℝ)*R)*(Real.log (R*U))^d/T^D := by ring
      _ = _ := by rw [typeI_residue_scaling hRp hUp]
  calc
    _ = ∑ r ∈ S, ‖α r‖*(((∫ t in T..2*T, ‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖))/T) := by
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ ∑ r ∈ S, ‖α r‖*B := Finset.sum_le_sum
      (fun r hr => mul_le_mul_of_nonneg_left (hb r hr) (_root_.norm_nonneg _))
    _ = B*(∑ r ∈ S, ‖α r‖) := by rw [←Finset.sum_mul,mul_comm]
    _ ≤ B*(A*R*(Real.log (R*U))^d) := mul_le_mul_of_nonneg_left hα hB
    _ = (C*Real.sqrt U*(R*U)^(η/2)*(2*R)^(1/4:ℝ)*Real.sqrt T)*(A*R*(Real.log (R*U))^d)+
        (E*U^(5/6:ℝ)*R^(-1/6:ℝ)/T^D)*(A*R*(Real.log (R*U))^d) := by dsimp [B]; ring
    _ ≤ _ := by rw [hpole]; exact add_le_add hmain le_rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialTypeIIntegral
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual radial height integral in the exact two ranges required
by the product decomposition, with its residue tail retained. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicTheta_radial_typeI_selected_ranges
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4) (B M : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ) (R U T : ℝ),
      1 ≤ R → 1 ≤ U → 1 ≤ Real.log (R*U) → Real.log (R*U) ≤ T →
      ((R ≤ (R*U)^(2/5:ℝ) ∧ T ≤ (R*U)^(1/100:ℝ)) ∨
        (R ≤ (R*U)^(1/3-κ/2) ∧ T ≤ (R*U)^(1/6+ρ))) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^B →
      ((∫ t in T..2*T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖))/T ≤
        C*(R*U)^(5/6-min (1/100) (3*κ/16))+
          E*(R*U)^(5/6:ℝ)/(Real.log (R*U))^M := by
  let ε := min (1/100:ℝ) (κ/16)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨C,E,hC,hE,hbound⟩ := cubicTheta_radial_typeI_height hMV hMV0 hW hε (B+M) B hA
  refine ⟨C,E,hC,hE,?_⟩
  intro w S α R U T hR hU hlog hLT hrange hS hmass
  have hT : 1 ≤ T := hlog.trans hLT
  have hX : 1 ≤ R*U := by nlinarith
  have hTX := typeI_range_height_le_square hX hR hρ hrange
  have hp : (R*U)^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤
      (R*U)^(5/6-min (1/100) (3*κ/16)) := by
    rcases hrange with ⟨hr,ht⟩ | ⟨hr,ht⟩
    · apply (typeI_first_fixed_gap hX (by positivity) (by positivity) hr ht
        (min_le_left _ _)).trans
      exact Real.rpow_le_rpow_of_exponent_le hX (by linarith [min_le_left (1/100:ℝ) (3*κ/16)])
    · apply (typeI_second_fixed_gap hX (by positivity) (by positivity) hr ht hρ
        (min_le_right _ _)).trans
      exact Real.rpow_le_rpow_of_exponent_le hX (by linarith [min_le_right (1/100:ℝ) (3*κ/16)])
  have hpole := typeI_pole_log_saving (show 0 ≤ R*U by positivity) hlog hLT
    (show B+M ≤ B+M from le_rfl)
  apply (hbound w S α R U T hR hU hT hTX hS hmass).trans
  apply add_le_add
  · calc
      _ = C*((R*U)^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hC
  · simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_left hpole hE

theorem cubicTheta_radial_typeI_height_integral
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4) (B M : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ)
        (R U T H X₀ : ℝ), 1 ≤ R → 1 ≤ U → 1 ≤ Real.log (R*U) →
        Real.log (R*U) ≤ T →
        ((R ≤ (R*U)^(2/5:ℝ) ∧ T ≤ (R*U)^(1/100:ℝ)) ∨
          (R ≤ (R*U)^(1/3-κ/2) ∧ T ≤ (R*U)^(1/6+ρ))) →
        (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
        (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^B →
        ‖typeIHeightIntegral w S α W 0 U H T X₀‖ ≤
          C*(R*U)^(5/6-min (1/100) (3*κ/16))+
            E*(R*U)^(5/6:ℝ)/(Real.log (R*U))^M := by
  obtain ⟨C,E,hC,hE,hbound⟩ := cubicTheta_radial_typeI_selected_ranges hMV hMV0 hW hκ hρ B M hA
  refine ⟨C,E,hC,hE,?_⟩
  intro w S α R U T H X₀ hR hU hlog hLT hrange hS hmass
  apply (typeIHeightIntegral_le_mean hW w S α 0 (zero_lt_one.trans_le hU)
    (zero_lt_one.trans_le (hlog.trans hLT)) H X₀).trans
  simpa only [dyadicHeightMean,neg_mul] using
    hbound w S α R U T hR hU hlog hLT hrange hS hmass

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProductWindow
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the constructed radial mean to the literal product window.
The bounded dilation of its inner smooth weight is retained exactly. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicTheta_radial_productTypeICutoffWindow_bound
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4)
    (B M : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (P : Finset Eisenstein) (α : Eisenstein → ℂ)
        (X R U T H X₀ : ℝ),
        1 ≤ R → 1 ≤ U → R*U = X → 1 ≤ Real.log X → Real.log X ≤ T →
        0 < X₀ →
        ((R ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
          (R ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+ρ))) →
        (∀ r ∈ P, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
        (∑ r ∈ P, ‖α r‖) ≤ A*R*(Real.log X)^B →
        ‖productTypeICutoffWindow w P α W 0 (Real.exp hW.radius) X U H T X₀‖ ≤
          C*X^(5/6-min (1/100) (3*κ/16))+E*X^(5/6:ℝ)/(Real.log X)^M := by
  have hV := hW.logDilate (Real.log 2) (Real.log_nonneg (by norm_num))
  obtain ⟨C,E,hC,hE,hbound⟩ := cubicTheta_radial_typeI_height_integral hMV hMean0 hV hκ hρ B M hA
  refine ⟨2*C,2*E,by positivity,by positivity,?_⟩
  intro w P α X R U T H X₀ hR hU hRU hlog hLT hX₀ hrange hP hmass
  obtain ⟨v,hv⟩ := productTypeICutoffWindow_dilate hW w P α 0 hR
    (zero_lt_one.trans_le hU) hRU hP
  rw [hv, typeICutoffWindow_endpoints hV v P α 0 (zero_lt_one.trans_le hU)
    (zero_lt_one.trans_le (hlog.trans hLT)) hX₀ H]
  have h₁ := hbound v P α R U T H X₀ hR hU (by simpa only [hRU] using hlog)
    (by simpa only [hRU] using hLT) (by simpa only [hRU] using hrange) hP
    (by simpa only [hRU] using hmass)
  have h₂ := hbound v P α R U T H (2*X₀) hR hU (by simpa only [hRU] using hlog)
    (by simpa only [hRU] using hLT) (by simpa only [hRU] using hrange) hP
    (by simpa only [hRU] using hmass)
  rw [hRU] at h₁ h₂
  apply (norm_sub_le _ _).trans
  exact (add_le_add h₁ h₂).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialShortOuterWindow
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagate the constructed radial transform through the literal tail.
No radial normalization or Voronoi premise is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicTheta_radial_short_outer_window_bound (hpnt : PrimaryPrimePNT)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4)
    {A : ℝ} (hA : 0 ≤ A) (k M : ℕ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ (w : Eisenstein → γ)
      (S : Finset Eisenstein) (α : Eisenstein → ℂ) (X Y H T X₀ : ℝ),
      2 ≤ X → 1 ≤ Real.log X → 1 ≤ Y → Real.log X ≤ T → 0 < H → 0 < X₀ →
      ((2*Y ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
        (2*Y ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+ρ))) →
      (∀ r ∈ S, primary r) →
      (∀ r ∈ S, α r ≠ 0 → norm r ≤ Y) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*∑ u ∈ primaryElementBall (Real.exp hW.radius*X),
        if r*u ∈ squarefreeProductEnvelope (Real.exp hW.radius*X) then
          productGaussHeightWindowKernel 0 (W (w r)) H T X X₀ (r*u) else 0‖ ≤
        (1+Real.log Y)*(C*X^(5/6-min (1/100) (3*κ/16))+
          E*X^(5/6:ℝ)/(Real.log X)^M) := by
  obtain ⟨D,d,hD,hmass⟩ := squarefree_typeI_coefficient_mass hpnt hA k
  obtain ⟨C,E,hC,hE,hbound⟩ := cubicTheta_radial_productTypeICutoffWindow_bound hW
    hMV hMean0 hκ hρ d M hD
  obtain ⟨L,hL,hcount⟩ := shortOuterCount_log_bound
  refine ⟨L*C,L*E,by positivity,by positivity,?_⟩
  intro w S α X Y H T X₀ hX hlog hY hLT hH hX₀ hrange hS hsize hα
  have hXp : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hYL : 0 ≤ 1+Real.log Y := by linarith [Real.log_nonneg hY]
  let S' := S.filter (fun r => α r ≠ 0 ∧ Squarefree r)
  let f : Eisenstein → ℂ := fun r => α r*∑ u ∈ primaryElementBall (Real.exp hW.radius*X),
    if r*u ∈ squarefreeProductEnvelope (Real.exp hW.radius*X) then
      productGaussHeightWindowKernel 0 (W (w r)) H T X X₀ (r*u) else 0
  have hre : (∑ r ∈ S, f r) = ∑ r ∈ S', f r := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases ha : α r = 0
    · simp only [ha,ne_eq,not_true_eq_false,false_and,ite_false, if_false,f,zero_mul]
    · by_cases hs : Squarefree r
      · simp only [ha,ne_eq,not_false_eq_true,hs,and_self,ite_true, if_true]
      · simp only [ha,ne_eq,not_false_eq_true,hs,and_false,ite_false, if_false]
        dsimp only [f]
        rw [show (∑ u ∈ primaryElementBall (Real.exp hW.radius*X),
          if r*u ∈ squarefreeProductEnvelope (Real.exp hW.radius*X) then
            productGaussHeightWindowKernel 0 (W (w r)) H T X X₀ (r*u) else 0) = 0 from ?_,mul_zero]
        apply Finset.sum_eq_zero
        intro u _
        apply ite_eq_right
        intro hp
        have hsf := (Finset.mem_filter.mp hp).2
        exact hs (fun a ha => hsf a (ha.trans (dvd_mul_right r u)))
  have hS' (r : Eisenstein) (hr : r ∈ S') :
      primary r ∧ Squarefree r ∧ 1 ≤ norm r ∧ norm r ≤ Y := by
    obtain ⟨hr,ha,hs⟩ := Finset.mem_filter.mp hr
    exact ⟨hS r hr,hs,one_le_norm (primary_ne_zero (hS r hr)),hsize r hr ha⟩
  have hpart := typeIMixedDyad_partition S' (show (0:ℝ) < 1 by norm_num)
    (shortOuterCount_covers hYp)
    (fun r hr => by simpa only [one_mul,mul_one] using (hS' r hr).2.2) f
  change ‖∑ r ∈ S, f r‖ ≤ _
  rw [hre,hpart]
  let B := C*X^(5/6-min (1/100) (3*κ/16))+E*X^(5/6:ℝ)/(Real.log X)^M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ j ∈ Finset.range (shortOuterCount Y), ‖∑ r ∈ typeIMixedDyad S' 1 j, f r‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (shortOuterCount Y), B := by
      apply Finset.sum_le_sum
      intro j hj
      let R : ℝ := 2^j
      let U : ℝ := X/R
      let P := typeIMixedDyad S' 1 j
      have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
      have hRp : 0 < R := zero_lt_one.trans_le hR
      have hRY : R ≤ 2*Y := (shortOuterCount_scale hYp (Finset.mem_range.mp hj)).le
      have hrange' : (R ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
          (R ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+ρ)) := by
        exact hrange.imp (fun h => ⟨hRY.trans h.1,h.2⟩) (fun h => ⟨hRY.trans h.1,h.2⟩)
      have hRX : R ≤ X := by
        rcases hrange' with h | h
        · exact h.1.trans (by simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (2/5:ℝ) ≤ 1))
        · exact h.1.trans (by simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hX1 (show 1/3-κ/2 ≤ 1 by linarith))
      have hU : 1 ≤ U := (le_div_iff₀ hRp).mpr (by simpa using hRX)
      have hRU : R*U = X := by dsimp [U]; field_simp
      have hP (r : Eisenstein) (hr : r ∈ P) : primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R := by
        obtain ⟨hrS,hrj⟩ := Finset.mem_filter.mp hr
        have hn := typeIMixedDyadIndex_bounds (show (0:ℝ) < 1 by norm_num) (hS' r hrS).2.2.1
        rw [hrj] at hn
        exact ⟨(hS' r hrS).1,by simpa only [one_mul] using hn.1,
          by simpa only [one_mul] using hn.2.le⟩
      have hmassP : (∑ r ∈ P, ‖α r‖) ≤ D*R*(Real.log X)^d :=
        hmass X R P α hR hRX hlog
          (fun r hr => ⟨(hP r hr).1,(hS' r (Finset.mem_filter.mp hr).1).2.1,(hP r hr).2.2⟩)
          (fun r hr => hα r (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1)
      have he : (∑ r ∈ P, f r) = productTypeICutoffWindow w P α W 0
          (Real.exp hW.radius) X U H T X₀ := by
        rw [productTypeICutoffWindow_fourier w P α W 0 _ _ _ _ _ hH]
        apply Finset.sum_congr rfl
        intro r hr
        dsimp only [f]
        congr 1
        exact typeI_gaussWindow_envelope_row 0 (W (w r)) (Real.exp_pos _).le hR
          (zero_lt_one.trans_le hU) hRU (hW.upper_support (w r)) H T X₀
          (hP r hr).1 (hP r hr).2.1
      rw [he]
      exact hbound w P α X R U T H X₀ hR hU hRU hlog hLT hX₀ hrange' hP hmassP
    _ = (shortOuterCount Y:ℝ)*B := by simp
    _ ≤ (L*(1+Real.log Y))*B := mul_le_mul_of_nonneg_right (hcount Y hY) hB
    _ = _ := by dsimp [B]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialRestrictedNoStopWindow
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagate the constructed radial transform through the literal tail.
No radial normalization or Voronoi premise is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicTheta_radial_restricted_noStop_window_bound (hpnt : PrimaryPrimePNT)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {κ η ν A cap : ℝ} (hκ : 0 < κ) (hη : η ≤ κ/4)
    (hν : 0 < ν) (hA : 0 ≤ A) (hcap : 1 < cap) (M : ℕ) :
    ∃ ρ C E : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ 0 ≤ C ∧ 0 ≤ E ∧
      ∀ᶠ X : ℝ in atTop, ∀ (i : γ) (R : Finset Eisenstein)
        (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w Z Y H T X₀ : ℝ)
        (P : Eisenstein → Eisenstein → Prop),
      2 ≤ X → 1 ≤ Real.log X → 1 ≤ Y → Real.log X ≤ T → 0 < H → 0 < X₀ →
      (Real.exp hW.radius*X)^(ν/4)*Z ≤ Y →
      ((2*Y ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
        (2*Y ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+η))) →
      (∀ r ∈ R, primary r) → (∀ r ∈ R, ‖v r‖ ≤ A) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      ‖restrictedNoStopGaussWindowValue R v ψ w ρ Z (Real.exp hW.radius)
        0 (W i) H T X X₀ P‖ ≤
        (1+Real.log Y)*(C*X^(5/6-min (1/100) (3*κ/16))+
          E*X^(5/6:ℝ)/(Real.log X)^M) := by
  obtain ⟨ρ,hρ,hρ₂,hsmall,hgeom⟩ := restricted_noStop_short_support hν hcap
  obtain ⟨C,E,hC,hE,hbound⟩ := cubicTheta_radial_short_outer_window_bound hpnt hW
    hMV hMean0 hκ hη hA 1 M
  refine ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,?_⟩
  have hcomp : Tendsto (fun X : ℝ => Real.exp hW.radius*X) atTop atTop :=
    tendsto_id.const_mul_atTop (Real.exp_pos _)
  filter_upwards [hcomp.eventually hgeom] with X hgeomX
  intro i R v ψ w Z Y H T X₀ P hX hlog hY hLT hH hX₀ hdist hrange hR hv hψ
  let F' := Real.exp hW.radius*X
  let D := primaryElementBall F'
  let Bsupport := primaryPairSupport R D
  let α := restrictedNoStopCoefficient R D v ψ w ρ F' Z P
  have hP (b : Eisenstein) (hb : b ∈ Bsupport) : primary b :=
    primaryPairSupport_primary R D hR (fun m hm => (mem_primaryElementBall.mp hm).1) hb
  have hs (b : Eisenstein) (_hb : b ∈ Bsupport) (hne : α b ≠ 0) : norm b ≤ Y :=
    (hgeomX R v ψ w Z P b hne).le.trans hdist
  have ha (b : Eisenstein) (hb : b ∈ Bsupport) :
      ‖α b‖ ≤ A*((metaplecticPrimaryDivisors b).card:ℝ)^1 := by
    simpa only [pow_one] using restrictedNoStop_coefficient_divisor_bound R D hR
      hψ w ρ F' Z P v hA hv (hP b hb)
  have hb := hbound (fun _ => i) Bsupport α X Y H T X₀ hX hlog hY hLT hH hX₀
    hrange hP hs ha
  change ‖∑ r ∈ R, v r*∑ u ∈ D,
    ∑ m ∈ primaryProductSlice (squarefreeProductEnvelope F') F' (r*u) with
      norm r*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ F') (geometricBinLower ρ F') < Z ∧ P r m,
      cutoffMoebius ψ w m*productGaussHeightWindowKernel 0 (W i) H T X X₀ (r*(m*u))‖ ≤ _
  rw [restrictedNoStop_coefficient_collection]
  exact hb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialScaleFirstNoStopTail
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagate the constructed radial transform through the literal tail.
No radial normalization or Voronoi premise is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicTheta_radial_scaleFirstTailNoStopRow_finite_bound (m : ℕ) (hpnt : PrimaryPrimePNT)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {cap : ℝ} (hcap : 1 < cap) (M : ℕ) :
    ∃ ρ C E : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ 0 ≤ C ∧ 0 ≤ E ∧
      ∀ᶠ X : ℝ in atTop, ∀ i < m, ∀ (ξ H U : ℝ) (h : ℕ)
        (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
        0 < H → Real.log X ≤ U → U ≤ X^(1/100:ℝ) →
        ‖scaleFirstTailNoStopRow i 0 ρ ξ H U X h d‖ ≤
          (1+Real.log X)*(C*X^(5/6-3/1600:ℝ)+E*X^(5/6:ℝ)/(Real.log X)^M) := by
  let A : ℝ := ∑ i ∈ Finset.range m, ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ)
  obtain ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,hbound⟩ := cubicTheta_radial_restricted_noStop_window_bound
    hpnt primeProductWeights hMV hMean0
    (κ := (1/100:ℝ)) (η := 0) (ν := (1/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (A := A) (by dsimp [A]; positivity) hcap M
  refine ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,?_⟩
  filter_upwards [hbound,eventually_ordinary_noStop_window_scales primeProductWeights,
    eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with X hb hs hX hlog
  intro i hi ξ H U h d hH hLU hU
  have hAi : ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ) ≤ A := by
    dsimp only [A]
    exact Finset.single_le_sum (f := fun j : ℕ => ‖(j.factorial:ℂ)⁻¹‖*(j^j:ℕ))
      (fun j _ => by positivity) (Finset.mem_range.mpr hi)
  have hXp : 0 < X := by linarith
  have hlogs : 1+Real.log (X^(39/100:ℝ)) ≤ 1+Real.log X := by
    rw [Real.log_rpow hXp]
    linarith
  rw [scaleFirstTailNoStopRow_eq_window]
  have he := hb () (centralPrimaryFactors X) (distinguishedScaleCoefficient i ξ X d)
    primeDetectorCutoff (X^ξ) (X^(38/100:ℝ)) (X^(39/100:ℝ)) H U X
    (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h)
    hX hlog hs.1 hLU hH hXp hs.2.1 (Or.inl ⟨hs.2.2,hU⟩)
    (fun _ hr => (mem_primaryElementBall.mp hr).1)
    (fun r _ => (distinguishedScaleCoefficient_norm i ξ X d r).trans hAi)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
  convert he.trans (mul_le_mul_of_nonneg_right hlogs (by positivity)) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialNoStopNegligible
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagate the constructed radial transform through the literal tail.
No radial normalization or Voronoi premise is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicTheta_radial_scaleFirstOrdinaryNoStopTail_isLittleO_oai (m : ℕ) (hpnt : PrimaryPrimePNT)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ ∀ (ξ : ℝ)
      (H T : ℝ → ℝ) (h : ℝ → ℕ),
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X ∧ H X ≤ X ∧ Real.log X ≤ T X) →
      (fun X => scaleFirstOrdinaryNoStopTail m ρ ξ (H X) (T X) X (h X))
        =o[atTop] firstMomentScale := by
  obtain ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,hbound⟩ := cubicTheta_radial_scaleFirstTailNoStopRow_finite_bound
    m hpnt hMV hMean0 hcap (m+5)
  obtain ⟨K,hK,hheight⟩ := height_window_sum_bound
  refine ⟨ρ,hρ,hρ₂,hsmall,?_⟩
  intro ξ H T h hsetup
  unfold scaleFirstOrdinaryNoStopTail
  apply IsLittleO.fun_sum
  intro i hi
  have him : i < m := Finset.mem_range.mp hi
  obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i 0
  let g₁ : ℝ → ℝ := fun X => (1+Real.log X)^(m+2)*X^(5/6-3/1600:ℝ)
  let g₂ : ℝ → ℝ := fun X => X^(5/6:ℝ)/(1+Real.log X)^3
  have hg : (fun X => g₁ X+g₂ X) =o[atTop] firstMomentScale :=
    (log_power_powerSaving_isLittleO (m+2) (by norm_num : (0:ℝ) < 3/1600)).add
      cubic_log_saving_isLittleO
  apply IsBigO.trans_isLittleO (g := fun X => g₁ X+g₂ X) ?_ hg
  apply IsBigO.of_bound (K*D*(C+E*2^(m+5)))
  filter_upwards [hsetup,hbound,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with X hs hb hX hlog
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hL : 1 ≤ 1+Real.log X := by linarith
  have hLpos : 0 < 1+Real.log X := zero_lt_one.trans_le hL
  let B := C*X^(5/6-3/1600:ℝ)+E*X^(5/6:ℝ)/(Real.log X)^(m+5)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let f : ℝ → ℂ := fun U => if U ≤ X^(1/100:ℝ) then
    ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      if distinguishedScaleLength d < X^(69/200:ℝ) then
        scaleFirstTailNoStopRow i 0 ρ ξ (H X) U X (h X) d else 0 else 0
  have hf (U : ℝ) (hTU : T X ≤ U) (_hUH : U < 2*Real.pi*(H X)) :
      ‖f U‖ ≤ D*(1+Real.log X)^(m+1)*B := by
    dsimp only [f]
    split_ifs with hU
    · have hpiece (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
          ‖if distinguishedScaleLength d < X^(69/200:ℝ) then
            scaleFirstTailNoStopRow i 0 ρ ξ (H X) U X (h X) d else 0‖ ≤ (1+Real.log X)*B := by
        split_ifs
        · exact hb i him ξ (H X) U (h X) d (zero_lt_one.trans_le hs.1) (hs.2.2.trans hTU) hU
        · simpa only [norm_zero] using mul_nonneg hLpos.le hB
      have hn : (Fintype.card (Fin i → Fin (normPartitionCount
          (Real.exp primeProductWeights.radius*X))):ℝ) ≤ D*(1+Real.log X)^i := by
        simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_sum,Nat.add_zero] using hcount X hX
      apply (norm_sum_le _ _).trans
      apply (Finset.sum_le_sum (fun d _ => hpiece d)).trans
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      apply (mul_le_mul_of_nonneg_right hn (mul_nonneg hLpos.le hB)).trans
      calc
        D*(1+Real.log X)^i*((1+Real.log X)*B) = D*(1+Real.log X)^(i+1)*B := by rw [pow_succ]; ring
        _ ≤ D*(1+Real.log X)^(m+1)*B := by
          gcongr
    · simpa only [norm_zero] using (show 0 ≤ D*(1+Real.log X)^(m+1)*B by positivity)
  have hh := hheight (H X) (T X) (D*(1+Real.log X)^(m+1)*B) f hs.1
    (hlog.trans hs.2.2) (by positivity) hf
  have hlogH : 1+Real.log (H X) ≤ 1+Real.log X :=
    add_le_add le_rfl (Real.log_le_log (zero_lt_one.trans_le hs.1) hs.2.1)
  have hwhole : ‖scaleFirstOrdinaryNoStopArity i ρ ξ (H X) (T X) X (h X)‖ ≤
      K*D*(1+Real.log X)^(m+2)*B := by
    apply hh.trans
    calc
      K*(1+Real.log (H X))*(D*(1+Real.log X)^(m+1)*B) ≤
          K*(1+Real.log X)*(D*(1+Real.log X)^(m+1)*B) := by gcongr
      _ = _ := by rw [show m+2=(m+1)+1 by omega,pow_succ]; ring
  -- Three logarithms remain after both finite summations.
  have hnorm := stopped_log_quotient_normalize (m+2) 3 hlog hE
    (Real.rpow_nonneg hXp.le (5/6:ℝ))
  have hg₁ : 0 ≤ g₁ X := by dsimp [g₁]; positivity
  have hg₂ : 0 ≤ g₂ X := by dsimp [g₂]; positivity
  rw [Real.norm_of_nonneg (add_nonneg hg₁ hg₂)]
  apply hwhole.trans
  have hnorm' : (1+Real.log X)^(m+2)*(E*X^(5/6:ℝ)/(Real.log X)^(m+5)) ≤
      (E*2^(m+5))*g₂ X := by
    dsimp only [g₂]
    simpa only [show m+2+3=m+5 by omega,mul_div_assoc] using hnorm
  calc
    _ = K*D*(C*g₁ X+(1+Real.log X)^(m+2)*
        (E*X^(5/6:ℝ)/(Real.log X)^(m+5))) := by dsimp [B,g₁]; ring
    _ ≤ K*D*(C*g₁ X+(E*2^(m+5))*g₂ X) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hnorm') (by positivity)
    _ ≤ K*D*((C+E*2^(m+5))*(g₁ X+g₂ X)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hC hg₂,mul_nonneg (show 0 ≤ E*2^(m+5) by positivity) hg₁]
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.cubicTheta_radial_scaleFirstOrdinaryNoStopTail_isLittleO_oai := @OAI.CubicFirstMoment.cubicTheta_radial_scaleFirstOrdinaryNoStopTail_isLittleO_oai
