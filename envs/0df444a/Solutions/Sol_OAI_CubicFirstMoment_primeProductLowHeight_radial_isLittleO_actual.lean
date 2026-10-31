-- Prove2me | solution 1 for OAI.CubicFirstMoment.primeProductLowHeight_radial_isLittleO_actual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:49:04.431486+00:00
-- url     : https://prove2.me/submissions/bb28e05d-b7d2-4c38-9834-c1f3c1b06202

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A016
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_ordinary_stopped_low_kernel_bound_actual
import Theorems.Thm_OAI_CubicFirstMoment_primeProductLowHeight_sub_low_scale_isLittleO_actual
import Theorems.Thm_OAI_CubicFirstMoment_scaleFirstStoppedLate_isLittleO
import Theorems.Thm_OAI_CubicFirstMoment_short_outer_low_bound_actual

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
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma idealMoebius_mul {a b : Eisenstein} (h : IsCoprime a b) :
    idealMoebius (a*b) = idealMoebius a * idealMoebius b :=
  (isRelPrime_iff_isCoprime.mpr h).moebius_mul

lemma idealMoebius_primaryPrime {p : Eisenstein} (hp : primaryPrime p) :
    idealMoebius p = -1 := hp.2.irreducible.moebius_eq

lemma idealMoebius_prod_primaryPrimes (s : Finset Eisenstein)
    (hp : ∀ p ∈ s, primaryPrime p) :
    idealMoebius (∏ p ∈ s, p) = (-1 : ℤ)^s.card := by
  induction s using Finset.induction_on with
  | empty => simp [idealMoebius]
  | @insert p s hps ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hc : IsCoprime p (∏ q ∈ s, q) := by
      apply IsCoprime.prod_right
      intro q hq
      exact primaryPrimes_isCoprime hp' (hs q hq) (fun h => hps (h ▸ hq))
    rw [Finset.prod_insert hps, idealMoebius_mul hc, idealMoebius_primaryPrime hp',
      ih hs, Finset.card_insert_of_notMem hps, pow_succ]
    ring

lemma norm_primaryNormalize (p : Eisenstein) : norm (primaryNormalize p) = norm p := by
  simpa only [normNat_cast] using congrArg (fun m : ℕ => (m : ℝ))
    (associated_normNat (primaryNormalize_associated p)).symm

lemma roughProduct_primary_factors (ψ : ℝ → ℝ) (y : ℝ) (n : Eisenstein) :
    roughProduct ψ y n = ∏ p ∈ primaryPrimeFactors n, (1 - ψ (norm p / y)) := by
  rw [primaryPrimeFactors, Finset.prod_image (primaryNormalize_injOn_primeFactors n)]
  simp only [norm_primaryNormalize, roughProduct]

theorem roughProduct_moebius_subsets {n : Eisenstein} (hn : primary n)
    (ψ : ℝ → ℝ) (y : ℝ) :
    roughProduct ψ y n =
      ∑ s ∈ (primaryPrimeFactors n).powerset,
        (idealMoebius (∏ p ∈ s, p) : ℝ) * ∏ p ∈ s, ψ (norm p / y) := by
  rw [roughProduct_primary_factors]
  have hex := Finset.prod_add (fun p : Eisenstein => -ψ (norm p / y))
    (fun _ => (1 : ℝ)) (primaryPrimeFactors n)
  simp only [Finset.prod_const_one, mul_one, ← sub_eq_neg_add] at hex
  rw [hex]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub := Finset.mem_powerset.mp hs
  rw [idealMoebius_prod_primaryPrimes s (fun p hp => (primaryPrimeFactor_spec hn (hsub hp)).1),
    Finset.prod_neg]
  push_cast
  rfl

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

lemma primaryPrimeFactors_finset_prod (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) :
    primaryPrimeFactors (∏ p ∈ U, p) = U := by
  have hprod := primary_finset_prod U (fun p : Eisenstein => p) (fun p hp => (hU p hp).1)
  ext p
  rw [primaryPrime_mem_factors_iff hprod]
  constructor
  · rintro ⟨hp,hd⟩
    obtain ⟨q,hq,hpq⟩ := (hp.2.dvd_finsetProd_iff (fun p : Eisenstein => p)).mp hd
    have he : p = q := primary_associated_eq hp.1 (hU q hq).1
      (hp.2.associated_of_dvd (hU q hq).2 hpq)
    exact he ▸ hq
  · intro hp
    exact ⟨hU p hp,Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp⟩

lemma primaryPrimeFactors_prod_injective {U : Finset Eisenstein}
    (hU : ∀ p ∈ U, primaryPrime p) :
    Set.InjOn (fun s : Finset Eisenstein => ∏ p ∈ s, p) (↑U.powerset : Set (Finset Eisenstein)) := by
  intro s hs t ht he
  have hs' := Finset.mem_powerset.mp hs
  have ht' := Finset.mem_powerset.mp ht
  have hh := congrArg primaryPrimeFactors he
  simpa only [primaryPrimeFactors_finset_prod s (fun p hp => hU p (hs' hp)),
    primaryPrimeFactors_finset_prod t (fun p hp => hU p (ht' hp))] using hh

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_Decomposition
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact coefficient separation

Finite-set versions of the two algebraic identities used in the prime-decomposition section of
*An unconditional first moment for cubic Gauss sums* (25 September 2026):
the distinguished-factor expansion and the normalization at the stopping bin.
Elements of `s` label distinct prime ideals, including conjugate ideals of
equal norm. Thus no identification of factors with their norms is made.
-/

noncomputable section

open scoped BigOperators

namespace CubicFirstMoment

/-- Each choice at a fixed stopping bin has the same multiplicative
coefficient, since its selected and unselected factors partition the bin. -/
theorem stopping_coefficient_split {α : Type*} [DecidableEq α]
    (s t : Finset α) (ht : t ⊆ s) (weight : α → ℂ) :
    (∏ p ∈ t, weight p) * (∏ p ∈ s \ t, weight p) =
      ∏ p ∈ s, weight p := by
  rw [mul_comm]
  exact Finset.prod_sdiff ht

/-- The reciprocal binomial coefficient is well-defined for every possible
count in the final bin. -/
theorem stopping_binomial_ne_zero (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.choose_pos hk).ne'

/-- The weights assigned to all possible selections in the stopping bin
sum to one. This is precisely the scalar in `eq:stopping-scalar`. -/
theorem stopping_bin_weights_sum {α : Type*} (s : Finset α)
    (k : ℕ) (hk : k ≤ s.card) :
    (∑ _t ∈ s.powersetCard k, (s.card.choose k : ℂ)⁻¹) = 1 := by
  simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  exact mul_inv_cancel₀ (stopping_binomial_ne_zero _ _ hk)

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

lemma cutoffMoebius_prime_product (ψ : ℝ → ℝ) (w : ℝ) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) :
    cutoffMoebius ψ w (∏ p ∈ s, p) = ∏ p ∈ s, -(ψ (norm p/w):ℂ) := by
  rw [cutoffMoebius,primaryPrimeFactors_finset_prod s hs,
    idealMoebius_prod_primaryPrimes s hs,Finset.prod_neg]
  push_cast
  rfl

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

/-- The small-R expansion is a sum over genuine primary divisors, with
no ordered-factor or unit multiplicity hidden in the coefficient. -/
theorem roughProduct_primary_divisor_sum {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (ψ : ℝ → ℝ) (w : ℝ) :
    (roughProduct ψ w n:ℂ) = ∑ d ∈ metaplecticPrimaryDivisors n, cutoffMoebius ψ w d := by
  rw [primary_divisors_of_squarefree_eq hn hs,
    Finset.sum_image (primaryPrimeFactors_prod_injective
      (fun p hp => (primaryPrimeFactor_spec hn hp).1))]
  rw [roughProduct_moebius_subsets hn]
  push_cast
  apply Finset.sum_congr rfl
  intro s hsP
  rw [cutoffMoebius,primaryPrimeFactors_finset_prod s
    (fun p hp => (primaryPrimeFactor_spec hn (Finset.mem_powerset.mp hsP hp)).1)]

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

/-- Exact collection of the stopped divisors. The selected test depends
only on r,d and the remaining test only on e. -/
theorem stopped_coefficients_sum (R D E U : Finset Eisenstein)
    (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w : ℝ)
    (selected : Eisenstein → Eisenstein → Prop) (remaining : Eisenstein → Prop)
    (K : Eisenstein → ℂ) :
    (∑ a ∈ primaryPairSupport E U, ∑ b ∈ primaryPairSupport R D,
      stoppedAlpha E U ψ w remaining a*stoppedBeta R D v ψ w selected b*K (a*b)) =
    ∑ p ∈ E ×ˢ U, ∑ q ∈ R ×ˢ D,
      if remaining p.1 ∧ selected q.1 q.2 then
        cutoffMoebius ψ w p.1*v q.1*cutoffMoebius ψ w q.2*
          K ((p.1*p.2)*(q.1*q.2)) else 0 := by
  unfold stoppedAlpha stoppedBeta
  calc
    _ = ∑ a ∈ primaryPairSupport E U,
        primaryPairCoefficient E U
          (fun p => if remaining p.1 then cutoffMoebius ψ w p.1 else 0) a *
        ∑ b ∈ primaryPairSupport R D,
          primaryPairCoefficient R D
            (fun p => if selected p.1 p.2 then v p.1*cutoffMoebius ψ w p.2 else 0) b *
              K (a*b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = _ := by
      rw [primaryPairCoefficient_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [primaryPairCoefficient_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hp' : remaining p.1 <;> by_cases hq' : selected q.1 q.2
      all_goals simp [hp',hq']
      ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual first-crossing count in one prime bin. All subsets with
that count obey the same predicate, so inverse-binomial weighting is exact. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma first_bin_crossing {R ell Z : ℝ} (_hR : 0 < R) (hell : 1 < ell)
    (hstart : R < Z) {N : ℕ} (hend : Z ≤ R*ell^N) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧
      R*ell^k/ell < Z ∧ Z ≤ R*ell^k ∧ R*ell^k < ell*Z := by
  have hex : ∃ k : ℕ, Z ≤ R*ell^k := ⟨N,hend⟩
  let k := Nat.find hex
  have hhit : Z ≤ R*ell^k := Nat.find_spec hex
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
    rw [hk0,pow_zero,mul_one] at hhit
    exact (not_le_of_gt hstart) hhit
  have hprev : R*ell^(k-1) < Z :=
    lt_of_not_ge (Nat.find_min hex (Nat.sub_lt hk (by decide)))
  have hstep : R*ell^k = (R*ell^(k-1))*ell := by
    calc
      _ = R*ell^(k-1+1) := congrArg (fun m : ℕ => R*ell^m) (Nat.sub_add_cancel hk).symm
      _ = _ := by rw [pow_succ]; ring
  have hellp : 0 < ell := zero_lt_one.trans hell
  refine ⟨k,hk,Nat.find_min' hex hend,?_,hhit,?_⟩
  · rwa [hstep,mul_div_cancel_right₀ _ hellp.ne']
  · rw [hstep,mul_comm ell Z]
    exact mul_lt_mul_of_pos_right hprev hellp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeBins
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first stopping bin is selected from actual finite prime bins.
Only the final bin and its selected count are exposed as outer indices. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeBinPrefix_succ (s : Finset Eisenstein) (b : Eisenstein → ℕ) (j : ℕ) :
    primeBinPrefix s b (j+1) = primeBinPrefix s b j ∪ primeBin s b j := by
  ext p
  by_cases hp : p ∈ s
  · simp only [primeBinPrefix,primeBin,Finset.mem_filter,Finset.mem_union,hp,true_and]
    omega
  · simp [primeBinPrefix,primeBin,hp]

lemma primeBinPrefix_disjoint (s : Finset Eisenstein) (b : Eisenstein → ℕ) (j : ℕ) :
    Disjoint (primeBinPrefix s b j) (primeBin s b j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  omega

lemma primeSurrogate_prefix_succ (s : Finset Eisenstein) (b : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (j : ℕ) :
    primeSurrogate (primeBinPrefix s b (j+1)) b ell =
      primeSurrogate (primeBinPrefix s b j) b ell * ell j^(primeBin s b j).card := by
  rw [primeBinPrefix_succ,primeSurrogate,
    Finset.prod_union (primeBinPrefix_disjoint s b j)]
  congr 1
  calc
    _ = ∏ _p ∈ primeBin s b j, ell j := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := Finset.prod_const _

lemma first_crossing_index (f : ℕ → ℝ) {Z : ℝ} (h0 : f 0 < Z)
    {m : ℕ} (hm : Z ≤ f m) :
    ∃ j : ℕ, j < m ∧ f j < Z ∧ Z ≤ f (j+1) := by
  have hex : ∃ k : ℕ, Z ≤ f k := ⟨m,hm⟩
  let k := Nat.find hex
  have hk : 0 < k := by
    by_contra h
    have he : k = 0 := Nat.eq_zero_of_not_pos h
    have hf := Nat.find_spec hex
    change Z ≤ f k at hf
    rw [he] at hf
    exact (not_le_of_gt h0) hf
  have hkm : k ≤ m := Nat.find_min' hex hm
  refine ⟨k-1,by omega,?_,?_⟩
  · exact lt_of_not_ge (Nat.find_min hex (Nat.sub_lt hk (by decide)))
  · rw [Nat.sub_add_cancel hk]
    exact Nat.find_spec hex

/-- Exact selection of the first bin and the first count within it.
The terminal bin contributes no occupancy-vector outer index. -/
theorem first_prime_bin (s : Finset Eisenstein) (b : Eisenstein → ℕ)
    (ell : ℕ → ℝ) {m : ℕ} (hb : ∀ p ∈ s, b p < m)
    (hell : ∀ j < m, 1 < ell j) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (hend : Z ≤ R*primeSurrogate s b ell) :
    ∃ j < m, ∃ k : ℕ, 1 ≤ k ∧ k ≤ (primeBin s b j).card ∧
      (R*primeSurrogate (primeBinPrefix s b j) b ell)*ell j^k/ell j < Z ∧
      Z ≤ (R*primeSurrogate (primeBinPrefix s b j) b ell)*ell j^k := by
  let f := fun j => R*primeSurrogate (primeBinPrefix s b j) b ell
  have h0 : f 0 < Z := by simpa [f,primeSurrogate,primeBinPrefix] using hstart
  have hm : Z ≤ f m := by
    have hset : primeBinPrefix s b m = s := by
      apply Finset.filter_true_of_mem
      exact hb
    simpa only [f,hset] using hend
  obtain ⟨j,hjm,hj,hjnext⟩ := first_crossing_index f h0 hm
  have hRj : 0 < R*primeSurrogate (primeBinPrefix s b j) b ell := by
    apply mul_pos hR
    apply Finset.prod_pos
    intro p hp
    exact zero_lt_one.trans (hell _ (hb p (Finset.mem_filter.mp hp).1))
  have hendj : Z ≤ (R*primeSurrogate (primeBinPrefix s b j) b ell)*
      ell j^(primeBin s b j).card := by
    simpa only [f,primeSurrogate_prefix_succ,mul_assoc] using hjnext
  obtain ⟨k,hk,hks,hprev,hhit,_⟩ := first_bin_crossing hRj (hell j hjm) hj hendj
  exact ⟨j,hjm,k,hk,hks,hprev,hhit⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeStoppingSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-bin identity with the actual selected divisor and its
complement. The crossing test only sees the selected divisor, while
inverse-binomial weighting restores every original squarefree term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppingSelected_subset {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    {j : ℕ} {t : Finset Eisenstein} (ht : t ⊆ primeBin s b j) :
    stoppingSelected s b j t ⊆ s := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (Finset.mem_filter.mp hp).1
  · exact (Finset.mem_filter.mp (ht hp)).1

lemma stoppingSelected_surrogate {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    (ell : ℕ → ℝ) {j : ℕ} {t : Finset Eisenstein} (ht : t ⊆ primeBin s b j) :
    primeSurrogate (stoppingSelected s b j t) b ell =
      primeSurrogate (primeBinPrefix s b j) b ell * ell j^t.card := by
  have hd : Disjoint (primeBinPrefix s b j) t :=
    (primeBinPrefix_disjoint s b j).mono_right ht
  rw [stoppingSelected,primeSurrogate,Finset.prod_union hd]
  congr 1
  calc
    _ = ∏ _p ∈ t, ell j := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp (ht hp)).2]
    _ = _ := Finset.prod_const _

lemma stoppingSelected_bin_count {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    {j : ℕ} {t : Finset Eisenstein} (ht : t ⊆ primeBin s b j) :
    (stoppingSelected s b j t).filter (fun p => b p = j) = t := by
  ext p
  by_cases hp : p ∈ t
  · have he := (Finset.mem_filter.mp (ht hp)).2
    simp [stoppingSelected,hp,he]
  · simp only [Finset.mem_filter,stoppingSelected,Finset.mem_union,
      primeBinPrefix,Finset.mem_filter,hp,or_false]
    constructor
    · rintro ⟨⟨_,hbp⟩,he⟩
      omega
    · intro h
      exact h.elim

lemma stoppingRemainder_bin_count {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    {j : ℕ} {t : Finset Eisenstein} (_ht : t ⊆ primeBin s b j) :
    (stoppingRemainder s b j t).filter (fun p => b p = j) = primeBin s b j \ t := by
  ext p
  simp only [stoppingRemainder,stoppingSelected,primeBinPrefix,primeBin,
    Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union]
  constructor
  · rintro ⟨⟨hp,hn⟩,he⟩
    exact ⟨⟨hp,he⟩,fun h => hn (Or.inr h)⟩
  · rintro ⟨⟨hp,he⟩,hnt⟩
    refine ⟨⟨hp,?_⟩,he⟩
    rintro (⟨_,hlt⟩ | hpt)
    · omega
    · exact hnt hpt

lemma stoppingSelected_bins_le {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    {j : ℕ} {t : Finset Eisenstein} (ht : t ⊆ primeBin s b j)
    {p : Eisenstein} (hp : p ∈ stoppingSelected s b j t) : b p ≤ j := by
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (Finset.mem_filter.mp hp).2.le
  · exact (Finset.mem_filter.mp (ht hp)).2.le

lemma stoppingRemainder_bins_ge {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    {j : ℕ} {t : Finset Eisenstein} {p : Eisenstein}
    (hp : p ∈ stoppingRemainder s b j t) : j ≤ b p := by
  obtain ⟨hpS,hpout⟩ := Finset.mem_sdiff.mp hp
  by_contra h
  apply hpout
  apply Finset.mem_union_left
  exact Finset.mem_filter.mpr ⟨hpS,by omega⟩

/-- The failed first-stage test can be read entirely from the selected
side at a later stopping bin. This is the extra ordinary-block predicate. -/
lemma stoppingSelected_earlier_prefix {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    {j h : ℕ} (hhj : h ≤ j) {t : Finset Eisenstein} (ht : t ⊆ primeBin s b j) :
    (stoppingSelected s b j t).filter (fun p => b p < h) = primeBinPrefix s b h := by
  ext p
  constructor
  · intro hp
    obtain ⟨hps,hph⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨stoppingSelected_subset ht hps,hph⟩
  · intro hp
    obtain ⟨hpS,hph⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpS,?_⟩),hph⟩
    exact hph.trans_le hhj

lemma cutoffMoebius_stoppingSelected (ψ : ℝ → ℝ) (w : ℝ)
    {s : Finset Eisenstein} (hs : ∀ p ∈ s, primaryPrime p)
    {b : Eisenstein → ℕ} {j : ℕ} {t : Finset Eisenstein}
    (ht : t ⊆ primeBin s b j) :
    cutoffMoebius ψ w (∏ p ∈ stoppingSelected s b j t, p) *
      cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s b j t, p) =
        cutoffMoebius ψ w (∏ p ∈ s, p) := by
  have hsel := stoppingSelected_subset ht
  unfold stoppingRemainder
  rw [cutoffMoebius_prime_product ψ w _ (fun p hp => hs p (hsel hp)),
    cutoffMoebius_prime_product ψ w _ (fun p hp => hs p (Finset.mem_sdiff.mp hp).1),
    cutoffMoebius_prime_product ψ w s hs]
  exact stopping_coefficient_split s (stoppingSelected s b j t) hsel _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SelectedPrimeCanonical
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the selected-bin largest-prime role. The
largest prime of the full product is used throughout; its occurrence in
the selected divisor is proved equivalent to the free-prime row test. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrimeFactors_mul_union {r d : Eisenstein} (hr : primary r) (hd : primary d) :
    primaryPrimeFactors (r*d) = primaryPrimeFactors r ∪ primaryPrimeFactors d := by
  ext p
  rw [primaryPrime_mem_factors_iff (primary_mul hr hd),Finset.mem_union,
    primaryPrime_mem_factors_iff hr,primaryPrime_mem_factors_iff hd]
  constructor
  · rintro ⟨hp,hpd⟩
    rcases hp.2.dvd_or_dvd hpd with hpr | hpd
    · exact Or.inl ⟨hp,hpr⟩
    · exact Or.inr ⟨hp,hpd⟩
  · rintro (⟨hp,hpr⟩ | ⟨hp,hpd⟩)
    · exact ⟨hp,dvd_mul_of_dvd_left hpr d⟩
    · exact ⟨hp,dvd_mul_of_dvd_right hpd r⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeFactorPairs
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact primary factor-pair reindexing for a literal squarefree term.
The norm ball only makes the right-hand support finite. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Every subset of the actual prime factors gives one, and only one,
primary factor pair. This retains arbitrary weights on both factors. -/
theorem squarefree_primary_factor_pairs {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {B : ℝ} (hnB : norm n ≤ B)
    (K : Eisenstein → Eisenstein → ℂ) :
    (∑ s ∈ (primaryPrimeFactors n).powerset,
      K (∏ p ∈ s, p) (∏ p ∈ primaryPrimeFactors n \ s, p)) =
    ∑ q ∈ ((primaryElementBall B).product (primaryElementBall B)).filter
        (fun q => q.1*q.2 = n), K q.1 q.2 := by
  let f : Finset Eisenstein → Eisenstein × Eisenstein :=
    fun s => ((∏ p ∈ s, p), (∏ p ∈ primaryPrimeFactors n \ s, p))
  have hfirst (s : Finset Eisenstein) (hsub : s ⊆ primaryPrimeFactors n) :
      primary (f s).1 :=
    primary_finset_prod s (fun p => p)
      (fun p hp => (primaryPrimeFactor_spec hn (hsub hp)).1.1)
  have hsecond (s : Finset Eisenstein) (hsub : s ⊆ primaryPrimeFactors n) :
      primary (f s).2 := by
    exact (primaryFactorRemainder_spec hn hs hsub).1
  have hmul (s : Finset Eisenstein) (hsub : s ⊆ primaryPrimeFactors n) :
      (f s).1*(f s).2 = n :=
    (primaryFactorRemainder_spec hn hs hsub).2.2
  apply Finset.sum_bij (fun s _ => f s)
  · intro s hsmem
    have hsub := Finset.mem_powerset.mp hsmem
    have hd : (f s).1 ∣ n := ⟨(f s).2,(hmul s hsub).symm⟩
    have he : (f s).2 ∣ n := ⟨(f s).1,by simpa only [mul_comm] using (hmul s hsub).symm⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨mem_primaryElementBall.mpr ⟨hfirst s hsub,
        (norm_le_of_dvd (primary_ne_zero hn) hd).trans hnB⟩,
       mem_primaryElementBall.mpr ⟨hsecond s hsub,
        (norm_le_of_dvd (primary_ne_zero hn) he).trans hnB⟩⟩,
      hmul s hsub⟩
  · intro s hsmem t htmem heq
    have hs' := Finset.mem_powerset.mp hsmem
    have ht' := Finset.mem_powerset.mp htmem
    have hh := congrArg primaryPrimeFactors (congrArg Prod.fst heq)
    change primaryPrimeFactors (∏ p ∈ s, p) = primaryPrimeFactors (∏ p ∈ t, p) at hh
    rwa [primaryPrimeFactors_finset_prod s (fun p hp => (primaryPrimeFactor_spec hn (hs' hp)).1),
      primaryPrimeFactors_finset_prod t (fun p hp => (primaryPrimeFactor_spec hn (ht' hp)).1)] at hh
  · intro q hq
    obtain ⟨hqball,hqn⟩ := Finset.mem_filter.mp hq
    have ha := (mem_primaryElementBall.mp (Finset.mem_product.mp hqball).1).1
    have hb := (mem_primaryElementBall.mp (Finset.mem_product.mp hqball).2).1
    have hsq : Squarefree (q.1*q.2) := by rwa [hqn]
    have hsa : Squarefree q.1 := hsq.of_mul_left
    have hsb : Squarefree q.2 := hsq.of_mul_right
    have hcop : IsCoprime q.1 q.2 :=
      isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hsq).1
    have hdis : Disjoint (primaryPrimeFactors q.1) (primaryPrimeFactors q.2) := by
      apply Finset.disjoint_left.mpr
      intro p hp hp'
      have hpa := primaryPrimeFactor_spec ha hp
      have hpb := primaryPrimeFactor_spec hb hp'
      exact hpa.1.2.not_isUnit (hcop.isUnit_of_dvd' hpa.2 hpb.2)
    have hunion : primaryPrimeFactors n =
        primaryPrimeFactors q.1 ∪ primaryPrimeFactors q.2 := by
      rw [←hqn,primaryPrimeFactors_mul_union ha hb]
    have hsub : primaryPrimeFactors q.1 ⊆ primaryPrimeFactors n := by
      rw [hunion]
      exact Finset.subset_union_left
    have hrem : primaryPrimeFactors n \ primaryPrimeFactors q.1 = primaryPrimeFactors q.2 := by
      rw [hunion]
      ext p
      simp only [Finset.mem_sdiff,Finset.mem_union]
      constructor
      · rintro ⟨hp,hnot⟩
        exact hp.resolve_left hnot
      · intro hp
        exact ⟨Or.inr hp,fun hp' => Finset.disjoint_left.mp hdis hp' hp⟩
    refine ⟨primaryPrimeFactors q.1,Finset.mem_powerset.mpr hsub,?_⟩
    apply Prod.ext
    · exact primaryPrimeFactors_prod ha hsa
    · dsimp only [f]
      rw [hrem,primaryPrimeFactors_prod hb hsb]
  · intro s _hsmem
    rfl

/-- Arbitrary original support remains an exact product-support test
after collecting finite primary factor fibres. -/
theorem primary_pair_fiber_support (S : Finset Eisenstein) (B : ℝ)
    (K : Eisenstein → Eisenstein → ℂ) :
    (∑ n ∈ S,
      ∑ q ∈ ((primaryElementBall B).product (primaryElementBall B)).filter
        (fun q => q.1*q.2 = n), K q.1 q.2) =
    ∑ d ∈ primaryElementBall B, ∑ e ∈ primaryElementBall B,
      if d*e ∈ S then K d e else 0 := by
  rw [Finset.sum_fiberwise_eq_sum_filter,Finset.sum_filter,
    Finset.product_eq_sprod,Finset.sum_product]

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

lemma geometricPrimeBin_index {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {p : Eisenstein} (hp : primaryPrime p) (hpB : norm p ≤ B) :
    geometricPrimeBin ρ B p < geometricBinCount ρ B := by
  have hr := Real.log_pos hρ
  have hpn : 0 < norm p := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
    (primaryPrime_norm_ge_two hp)
  have hpρ : ρ ≤ norm p := hρ₂.trans (primaryPrime_norm_ge_two hp)
  have hl : 1 ≤ Real.log (norm p)/Real.log ρ := by
    apply (le_div_iff₀ hr).mpr
    rw [one_mul]
    exact Real.log_le_log (zero_lt_one.trans hρ) hpρ
  have hk : 1 ≤ ⌊Real.log (norm p)/Real.log ρ⌋₊ := (Nat.one_le_floor_iff _).mpr hl
  have hkM : ⌊Real.log (norm p)/Real.log ρ⌋₊ ≤ geometricBinCount ρ B := by
    exact (Nat.floor_mono (div_le_div_of_nonneg_right
      (Real.log_le_log hpn hpB) hr.le)).trans
        (Nat.floor_le_ceil _)
  unfold geometricPrimeBin
  omega

lemma geometricBinLower_gt_one {ρ B : ℝ} (hρ : 1 < ρ)
    {j : ℕ} (hj : j < geometricBinCount ρ B) : 1 < geometricBinLower ρ B j := by
  exact one_lt_pow₀ hρ (by omega)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeStoppingUnique
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness of the actual first crossing bin and the selected count.
This supplies the missing uniqueness direction for the finite stop sum. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

attribute [local instance] Classical.propDecidable

lemma crossing_index_unique (f : ℕ → ℝ) (hf : Monotone f) {Z : ℝ} {j k : ℕ}
    (hj : f j < Z ∧ Z ≤ f (j+1)) (hk : f k < Z ∧ Z ≤ f (k+1)) : j = k := by
  apply le_antisymm
  · by_contra h
    have hkj : k+1 ≤ j := by omega
    exact (not_lt_of_ge (hk.2.trans (hf hkj))) hj.1
  · by_contra h
    have hjk : j+1 ≤ k := by omega
    exact (not_lt_of_ge (hj.2.trans (hf hjk))) hk.1

lemma bin_count_predecessor {R ell : ℝ} (hell : ell ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    R*ell^k/ell = R*ell^(k-1) := by
  have he : k = (k-1)+1 := by omega
  conv_lhs => rw [he,pow_succ]
  rw [←mul_assoc,mul_div_cancel_right₀ _ hell]

lemma first_bin_count_unique {R ell Z : ℝ} (hR : 0 ≤ R) (hell : 1 ≤ ell)
    {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k)
    (hjl : R*ell^j/ell < Z) (hju : Z ≤ R*ell^j)
    (hkl : R*ell^k/ell < Z) (hku : Z ≤ R*ell^k) : j = k := by
  have hell0 : ell ≠ 0 := ne_of_gt (zero_lt_one.trans_le hell)
  have hmono : Monotone (fun n : ℕ => R*ell^n) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hell hab) hR
  have hj' : R*ell^(j-1) < Z ∧ Z ≤ R*ell^((j-1)+1) := by
    rw [Nat.sub_add_cancel hj]
    exact ⟨by rwa [bin_count_predecessor hell0 hj] at hjl,hju⟩
  have hk' : R*ell^(k-1) < Z ∧ Z ≤ R*ell^((k-1)+1) := by
    rw [Nat.sub_add_cancel hk]
    exact ⟨by rwa [bin_count_predecessor hell0 hk] at hkl,hku⟩
  have h := crossing_index_unique _ hmono hj' hk'
  omega

lemma partial_count_bin_crossing {R ell Z : ℝ} (hR : 0 ≤ R) (hell : 1 ≤ ell)
    {k N : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N)
    (hprev : R*ell^k/ell < Z) (hhit : Z ≤ R*ell^k) :
    R < Z ∧ Z ≤ R*ell^N := by
  have hellp : 0 < ell := zero_lt_one.trans_le hell
  have hpow : ell ≤ ell^k := by simpa using pow_le_pow_right₀ hell hk
  have hlo : R ≤ R*ell^k/ell := (le_div_iff₀ hellp).mpr
    (mul_le_mul_of_nonneg_left hpow hR)
  exact ⟨hlo.trans_lt hprev,hhit.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hell hkN) hR)⟩

lemma prime_prefix_monotone (s : Finset Eisenstein) (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j) {R : ℝ} (hR : 0 ≤ R) :
    Monotone (fun j => R*primeSurrogate (primeBinPrefix s bin j) bin ell) := by
  apply monotone_nat_of_le_succ
  intro j
  have hp : 0 ≤ primeSurrogate (primeBinPrefix s bin j) bin ell :=
    Finset.prod_nonneg (fun p _ => zero_le_one.trans (hell (bin p)))
  have hpow : 1 ≤ (ell j)^(primeBin s bin j).card := one_le_pow₀ (hell j)
  rw [primeSurrogate_prefix_succ]
  calc
    _ ≤ (R*primeSurrogate (primeBinPrefix s bin j) bin ell)*
        (ell j)^(primeBin s bin j).card := le_mul_of_one_le_right (mul_nonneg hR hp) hpow
    _ = _ := by ring

lemma selected_crossing_implies_bin_crossing (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    {R Z : ℝ} (hR : 0 ≤ R) {j k : ℕ} {t : Finset Eisenstein}
    (ht : t ∈ (primeBin s bin j).powersetCard k) (hk : 1 ≤ k)
    (hprev : R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z)
    (hhit : Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) :
    R*primeSurrogate (primeBinPrefix s bin j) bin ell < Z ∧
      Z ≤ R*primeSurrogate (primeBinPrefix s bin (j+1)) bin ell := by
  obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp ht
  have hbase : 0 ≤ R*primeSurrogate (primeBinPrefix s bin j) bin ell :=
    mul_nonneg hR (Finset.prod_nonneg (fun p _ => zero_le_one.trans (hell (bin p))))
  have hp : R*primeSurrogate (stoppingSelected s bin j t) bin ell =
      (R*primeSurrogate (primeBinPrefix s bin j) bin ell)*(ell j)^k := by
    rw [stoppingSelected_surrogate ell hsub,hcard]
    ring
  rw [hp] at hprev hhit
  have hkN : k ≤ (primeBin s bin j).card := by
    rw [←hcard]
    exact Finset.card_le_card hsub
  have hcross := partial_count_bin_crossing hbase (hell j) hk hkN hprev hhit
  refine ⟨hcross.1,?_⟩
  simpa only [primeSurrogate_prefix_succ,mul_assoc] using hcross.2

lemma selected_crossing_indices_unique (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    {R Z : ℝ} (hR : 0 ≤ R) {j₀ k₀ j k : ℕ}
    (hk₀ : 1 ≤ k₀) (hk₀N : k₀ ≤ (primeBin s bin j₀).card)
    (hprev₀ : (R*primeSurrogate (primeBinPrefix s bin j₀) bin ell)*ell j₀^k₀/ell j₀ < Z)
    (hhit₀ : Z ≤ (R*primeSurrogate (primeBinPrefix s bin j₀) bin ell)*ell j₀^k₀)
    {t : Finset Eisenstein} (ht : t ∈ (primeBin s bin j).powersetCard k) (hk : 1 ≤ k)
    (hprev : R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z)
    (hhit : Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) :
    j = j₀ ∧ k = k₀ := by
  have hbase (i : ℕ) : 0 ≤ R*primeSurrogate (primeBinPrefix s bin i) bin ell :=
    mul_nonneg hR (Finset.prod_nonneg (fun p _ => zero_le_one.trans (hell (bin p))))
  have hcross₀ := partial_count_bin_crossing (hbase j₀) (hell j₀) hk₀ hk₀N hprev₀ hhit₀
  have hwhole₀ : R*primeSurrogate (primeBinPrefix s bin j₀) bin ell < Z ∧
      Z ≤ R*primeSurrogate (primeBinPrefix s bin (j₀+1)) bin ell := by
    refine ⟨hcross₀.1,?_⟩
    simpa only [primeSurrogate_prefix_succ,mul_assoc] using hcross₀.2
  have hj := crossing_index_unique _ (prime_prefix_monotone s bin ell hell hR)
    (selected_crossing_implies_bin_crossing s bin ell hell hR ht hk hprev hhit) hwhole₀
  refine ⟨hj,?_⟩
  subst j
  obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp ht
  rw [stoppingSelected_surrogate ell hsub,hcard] at hprev hhit
  rw [←mul_assoc] at hprev hhit
  exact first_bin_count_unique (hbase j₀) (hell j₀) hk hk₀ hprev hhit hprev₀ hhit₀

/-- Every original term is restored by summing the actual possible last
bin and selected count. Uniqueness makes all other labels vanish. -/
theorem prime_bin_stopping_sum (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) (bin : Eisenstein → ℕ) (ell : ℕ → ℝ)
    {m : ℕ} (hbin : ∀ p ∈ s, bin p < m) (hell : ∀ j, 1 ≤ ell j)
    (hell' : ∀ j < m, 1 < ell j) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (hend : Z ≤ R*primeSurrogate s bin ell) (ψ : ℝ → ℝ) (w : ℝ) :
    (∑ j ∈ Finset.range m, ∑ k ∈ Finset.Icc 1 s.card,
      ∑ t ∈ (primeBin s bin j).powersetCard k,
        if R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
            Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell then
          ((primeBin s bin j).card.choose k:ℂ)⁻¹ *
            (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s bin j t, p) *
             cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s bin j t, p))
        else 0) = cutoffMoebius ψ w (∏ p ∈ s, p) := by
  obtain ⟨j₀,hj₀,k₀,hk₀,hk₀N,hprev₀,hhit₀⟩ := first_prime_bin s bin ell hbin
    hell' hR hstart hend
  let F := fun j k => ∑ t ∈ (primeBin s bin j).powersetCard k,
    if R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
        Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell then
      ((primeBin s bin j).card.choose k:ℂ)⁻¹ *
        (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s bin j t, p) *
         cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s bin j t, p))
    else 0
  have hmemj : j₀ ∈ Finset.range m := Finset.mem_range.mpr hj₀
  have hmemk : k₀ ∈ Finset.Icc 1 s.card := Finset.mem_Icc.mpr
    ⟨hk₀,hk₀N.trans (Finset.card_filter_le _ _)⟩
  have hindices {j k : ℕ} {t : Finset Eisenstein}
      (ht : t ∈ (primeBin s bin j).powersetCard k) (hk : 1 ≤ k)
      (hc : R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
        Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) :
      j = j₀ ∧ k = k₀ :=
    selected_crossing_indices_unique s bin ell hell hR.le
      hk₀ hk₀N hprev₀ hhit₀ ht hk hc.1 hc.2
  have houter : (∑ j ∈ Finset.range m, ∑ k ∈ Finset.Icc 1 s.card, F j k) =
      ∑ k ∈ Finset.Icc 1 s.card, F j₀ k := by
    apply Finset.sum_eq_single j₀
    · intro j _hj hjne
      apply Finset.sum_eq_zero
      intro k hk
      dsimp only [F]
      apply Finset.sum_eq_zero
      intro t ht
      apply ite_eq_right
      intro hc
      exact hjne (hindices ht (Finset.mem_Icc.mp hk).1 hc).1
    · exact fun h => (h hmemj).elim
  have hinner : (∑ k ∈ Finset.Icc 1 s.card, F j₀ k) = F j₀ k₀ := by
    apply Finset.sum_eq_single k₀
    · intro k hk hkne
      dsimp only [F]
      apply Finset.sum_eq_zero
      intro t ht
      apply ite_eq_right
      intro hc
      exact hkne (hindices ht (Finset.mem_Icc.mp hk).1 hc).2
    · exact fun h => (h hmemk).elim
  change (∑ j ∈ Finset.range m, ∑ k ∈ Finset.Icc 1 s.card, F j k) = _
  rw [houter,hinner]
  calc
    F j₀ k₀ = ∑ _t ∈ (primeBin s bin j₀).powersetCard k₀,
        ((primeBin s bin j₀).card.choose k₀:ℂ)⁻¹*cutoffMoebius ψ w (∏ p ∈ s, p) := by
      dsimp only [F]
      apply Finset.sum_congr rfl
      intro t ht
      obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp ht
      have hc : R*primeSurrogate (stoppingSelected s bin j₀ t) bin ell/ell j₀ < Z ∧
          Z ≤ R*primeSurrogate (stoppingSelected s bin j₀ t) bin ell := by
        rw [stoppingSelected_surrogate ell hsub,hcard,←mul_assoc]
        exact ⟨hprev₀,hhit₀⟩
      rw [ite_eq_left hc,cutoffMoebius_stoppingSelected ψ w hs hsub]
    _ = _ := by
      rw [←Finset.sum_mul,stopping_bin_weights_sum (primeBin s bin j₀) k₀ hk₀N,one_mul]

theorem geometric_bin_stopping_sum (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : ∀ p ∈ s, norm p ≤ X) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (hend : Z ≤ R*primeSurrogate s (geometricPrimeBin ρ X) (geometricBinLower ρ X))
    (ψ : ℝ → ℝ) (w : ℝ) :
    (∑ j ∈ Finset.range (geometricBinCount ρ X), ∑ k ∈ Finset.Icc 1 s.card,
      ∑ t ∈ (primeBin s (geometricPrimeBin ρ X) j).powersetCard k,
        if R*primeSurrogate (stoppingSelected s (geometricPrimeBin ρ X) j t)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X)/geometricBinLower ρ X j < Z ∧
          Z ≤ R*primeSurrogate (stoppingSelected s (geometricPrimeBin ρ X) j t)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) then
          ((primeBin s (geometricPrimeBin ρ X) j).card.choose k:ℂ)⁻¹ *
            (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s (geometricPrimeBin ρ X) j t, p) *
             cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s (geometricPrimeBin ρ X) j t, p))
        else 0) = cutoffMoebius ψ w (∏ p ∈ s, p) := by
  apply prime_bin_stopping_sum s hs
    (geometricPrimeBin ρ X) (geometricBinLower ρ X) _ _ _ hR hstart hend ψ w
  · exact fun p hp => geometricPrimeBin_index hρ hρ₂ (hs p hp) (hX p hp)
  · exact fun j => one_le_pow₀ hρ.le
  · exact fun j hj => geometricBinLower_gt_one hρ hj

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseStoppingLabels
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual final-bin and two-occupancy index set in the stopping
construction has logarithmic size. No complete occupancy vector occurs. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

attribute [local instance] Classical.propDecidable

lemma stoppingFactorLimit_bound {X : ℝ} (hX : 1 ≤ X) :
    (stoppingFactorLimit X:ℝ) ≤ (Real.log 2)⁻¹*Real.log X+1 := by
  have h := (Nat.ceil_lt_add_one
    (div_nonneg (Real.log_nonneg hX) (Real.log_pos (by norm_num : (1:ℝ) < 2)).le)).le
  simpa only [stoppingFactorLimit,div_eq_mul_inv,mul_comm] using h

lemma stopping_prime_factor_count {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n)
    {X : ℝ} (hX : 1 ≤ X) (hnX : norm n ≤ X) :
    s.card ≤ stoppingFactorLimit X := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := (div_le_iff₀ hlog).mp (Nat.le_ceil (Real.log X/Real.log 2))
  have hlarge : X < (2:ℝ)^(stoppingFactorLimit X+1) := by
    apply (Real.lt_pow_iff_log_lt hXp (by norm_num : (0:ℝ) < 2)).mpr
    simp only [Nat.cast_add,Nat.cast_one]
    change Real.log X ≤ (stoppingFactorLimit X:ℝ)*Real.log 2 at hc
    nlinarith
  have hslt := primary_factor_subset_card_lt hn hs hsub (by norm_num : (1:ℝ) ≤ 2)
    (fun p hp => primaryPrime_norm_ge_two (primaryPrimeFactor_spec hn (hsub hp)).1)
    (hnX.trans_lt hlarge)
  omega

lemma stoppingLabelBox_card (ρ X : ℝ) :
    (stoppingLabelBox ρ X).card ≤ geometricBinCount ρ X*(stoppingFactorLimit X+1)^2 := by
  unfold stoppingLabelBox
  simpa only [Finset.product_eq_sprod,Finset.card_product,Finset.card_range,pow_two] using
    (Finset.card_filter_le
      ((Finset.range (geometricBinCount ρ X)).product
        ((Finset.range (stoppingFactorLimit X+1)).product
          (Finset.range (stoppingFactorLimit X+1))))
      (fun t : ℕ × ℕ × ℕ => 1 ≤ t.2.1))

lemma stopping_scalar_norm_le_one (k l : ℕ) :
    ‖((Nat.choose (k+l) k:ℂ)⁻¹)‖ ≤ 1 := by
  have hp : 0 < Nat.choose (k+l) k := Nat.choose_pos (by omega)
  have hc : (1:ℝ) ≤ Nat.choose (k+l) k := by exact_mod_cast hp
  rw [norm_inv,Complex.norm_natCast]
  exact inv_le_one_of_one_le₀ hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeStoppingLabels
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact stopping reconstruction in the three labels occurring in the
manuscript: final bin, selected occupancy, and remaining occupancy. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The independent side predicates recover the exact selected subset. -/
lemma stoppingSelected_of_separated_bins (d e : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (j : ℕ)
    (hd : ∀ p ∈ d, bin p ≤ j) (he : ∀ p ∈ e, j ≤ bin p) :
    stoppingSelected (d ∪ e) bin j (primeBin d bin j) = d := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨hp,hpj⟩ := Finset.mem_filter.mp hp
      rcases Finset.mem_union.mp hp with hpd | hpe
      · exact hpd
      · exact (not_lt_of_ge (he p hpe) hpj).elim
    · exact (Finset.mem_filter.mp hp).1
  · intro hp
    by_cases hpj : bin p < j
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hp,hpj⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hp,by have := hd p hp; omega⟩)

lemma stoppingRemainder_of_separated_bins (d e : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (j : ℕ) (hde : Disjoint d e)
    (hd : ∀ p ∈ d, bin p ≤ j) (he : ∀ p ∈ e, j ≤ bin p) :
    stoppingRemainder (d ∪ e) bin j (primeBin d bin j) = e := by
  rw [stoppingRemainder,stoppingSelected_of_separated_bins d e bin j hd he]
  ext p
  have hdis := Finset.disjoint_left.mp hde
  simp only [Finset.mem_sdiff,Finset.mem_union]
  constructor
  · rintro ⟨hp,hnd⟩
    exact hp.resolve_left hnd
  · intro hp
    exact ⟨Or.inr hp,fun hpd => hdis hpd hp⟩

lemma stopping_occupancies_add {s : Finset Eisenstein} {bin : Eisenstein → ℕ}
    {j k : ℕ} {t : Finset Eisenstein}
    (ht : t ∈ (primeBin s bin j).powersetCard k) :
    k+(primeBin (stoppingRemainder s bin j t) bin j).card =
      (primeBin s bin j).card := by
  obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp ht
  change k+((stoppingRemainder s bin j t).filter (fun p => bin p = j)).card = _
  rw [stoppingRemainder_bin_count hsub,←hcard,Nat.add_comm]
  exact Finset.card_sdiff_add_card_eq_card hsub

/-- Inserting the remaining occupancy changes neither the actual finite
sum nor its inverse-binomial coefficient. -/
lemma stopping_insert_remaining_count (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k M : ℕ)
    (hM : s.card ≤ M) (R Z : ℝ) (ψ : ℝ → ℝ) (w : ℝ) :
    (∑ l ∈ Finset.range (M+1), ∑ t ∈ (primeBin s bin j).powersetCard k,
      if (primeBin (stoppingRemainder s bin j t) bin j).card = l ∧
          (R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
            Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) then
        (Nat.choose (k+l) k:ℂ)⁻¹ *
          (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s bin j t, p) *
           cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s bin j t, p))
      else 0) =
    ∑ t ∈ (primeBin s bin j).powersetCard k,
      if R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
          Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell then
        ((primeBin s bin j).card.choose k:ℂ)⁻¹ *
          (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s bin j t, p) *
           cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s bin j t, p))
      else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  let l := (primeBin (stoppingRemainder s bin j t) bin j).card
  have hl : l ∈ Finset.range (M+1) := by
    apply Finset.mem_range.mpr
    have hr : stoppingRemainder s bin j t ⊆ s := Finset.sdiff_subset
    have hc : l ≤ s.card := (Finset.card_filter_le _ _).trans (Finset.card_le_card hr)
    omega
  rw [Finset.sum_eq_single l]
  · have he := stopping_occupancies_add ht
    dsimp only [l] at *
    simp only [true_and,he]
  · intro l' _hl' hne
    apply ite_eq_right
    exact fun h => hne h.1.symm
  · exact fun h => (h hl).elim

/-- The complete three-label stopping sum, with no assumed reconstruction
identity and no hidden choice of the first bin. -/
theorem geometric_label_stopping_sum (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) (hnorm : norm (∏ p ∈ s, p) ≤ X)
    (hpX : ∀ p ∈ s, norm p ≤ X) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (hend : Z ≤ R*primeSurrogate s (geometricPrimeBin ρ X) (geometricBinLower ρ X))
    (ψ : ℝ → ℝ) (w : ℝ) :
    (∑ q ∈ stoppingLabelBox ρ X,
      ∑ t ∈ (primeBin s (geometricPrimeBin ρ X) q.1).powersetCard q.2.1,
        if (primeBin (stoppingRemainder s (geometricPrimeBin ρ X) q.1 t)
              (geometricPrimeBin ρ X) q.1).card = q.2.2 ∧
            (R*primeSurrogate (stoppingSelected s (geometricPrimeBin ρ X) q.1 t)
                (geometricPrimeBin ρ X) (geometricBinLower ρ X)/
                  geometricBinLower ρ X q.1 < Z ∧
              Z ≤ R*primeSurrogate (stoppingSelected s (geometricPrimeBin ρ X) q.1 t)
                (geometricPrimeBin ρ X) (geometricBinLower ρ X)) then
          (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
            (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s (geometricPrimeBin ρ X) q.1 t, p) *
             cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s (geometricPrimeBin ρ X) q.1 t, p))
        else 0) = cutoffMoebius ψ w (∏ p ∈ s, p) := by
  have hprim : primary (∏ p ∈ s, p) := primary_finset_prod s (fun p => p) (fun p hp => (hs p hp).1)
  have hsf := primaryPrime_product_squarefree s hs
  have hM : s.card ≤ stoppingFactorLimit X := by
    apply stopping_prime_factor_count hprim hsf _ hX hnorm
    rw [primaryPrimeFactors_finset_prod s hs]
  let M := stoppingFactorLimit X
  let bin := geometricPrimeBin ρ X
  let ell := geometricBinLower ρ X
  let F := fun j k => ∑ t ∈ (primeBin s bin j).powersetCard k,
    if R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z ∧
        Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell then
      ((primeBin s bin j).card.choose k:ℂ)⁻¹ *
        (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s bin j t, p) *
         cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s bin j t, p))
    else 0
  simp only [stoppingLabelBox,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  calc
    _ = ∑ j ∈ Finset.range (geometricBinCount ρ X),
        ∑ k ∈ (Finset.range (M+1)).filter (fun k => 1 ≤ k), F j k := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkpos : 1 ≤ k
      · simp only [hkpos,ite_true, if_true]
        exact stopping_insert_remaining_count s bin ell j k M hM R Z ψ w
      · simp only [hkpos,ite_false, if_false,Finset.sum_const_zero]
    _ = ∑ j ∈ Finset.range (geometricBinCount ρ X),
        ∑ k ∈ Finset.Icc 1 s.card, F j k := by
      apply Finset.sum_congr rfl
      intro j _hj
      symm
      apply Finset.sum_subset
      · intro k hk
        obtain ⟨hklo,hkhi⟩ := Finset.mem_Icc.mp hk
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [M]; omega),hklo⟩
      · intro k hk hnot
        have hklo := (Finset.mem_filter.mp hk).2
        have hkhi : s.card < k := by
          by_contra hn
          exact hnot (Finset.mem_Icc.mpr ⟨hklo,by omega⟩)
        have hempty : (primeBin s bin j).powersetCard k = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro t ht
          obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp ht
          have hc := (Finset.card_le_card hsub).trans (Finset.card_filter_le _ _)
          omega
        simp only [F,hempty,Finset.sum_empty]
    _ = _ := geometric_bin_stopping_sum s hs hρ hρ₂ hpX hR hstart hend ψ w

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeStoppingPairs
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverting the independent stopping predicates reconstructs the exact
selected divisor and complementary divisor of the original squarefree term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeFactors_disjoint_of_squarefree_mul {d e : Eisenstein}
    (hd : primary d) (he : primary e) (hs : Squarefree (d*e)) :
    Disjoint (primaryPrimeFactors d) (primaryPrimeFactors e) := by
  have hc : IsCoprime d e := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hpd := primaryPrimeFactor_spec hd hp
  have hpe := primaryPrimeFactor_spec he hq
  exact hpd.1.2.not_isUnit (hc.isUnit_of_dvd' hpd.2 hpe.2)

/-- The independent selected and remaining predicates give an actual
selection in the original factor set, with the exact two products and
exact inverse-binomial denominator. -/
theorem stopping_pair_reconstruction {d e r : Eisenstein}
    (hd : primary d) (he : primary e) (hs : Squarefree (d*e))
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k l : ℕ) (Z : ℝ)
    (hselected : stoppingSideTest bin ell j k Z r d)
    (hremaining : stoppingRemainingTest bin j l e) :
    ∃ t ∈ (primeBin (primaryPrimeFactors (d*e)) bin j).powersetCard k,
      (∏ p ∈ stoppingSelected (primaryPrimeFactors (d*e)) bin j t, p) = d ∧
      (∏ p ∈ stoppingRemainder (primaryPrimeFactors (d*e)) bin j t, p) = e ∧
      (primeBin (primaryPrimeFactors (d*e)) bin j).card = k+l ∧
      (norm r*primeSurrogate
          (stoppingSelected (primaryPrimeFactors (d*e)) bin j t) bin ell/ell j < Z ∧
        Z ≤ norm r*primeSurrogate
          (stoppingSelected (primaryPrimeFactors (d*e)) bin j t) bin ell) := by
  let t := primeBin (primaryPrimeFactors d) bin j
  have hsel : stoppingSelected (primaryPrimeFactors (d*e)) bin j t =
      primaryPrimeFactors d := by
    rw [primaryPrimeFactors_mul_union hd he]
    exact stoppingSelected_of_separated_bins _ _ bin j hselected.1 hremaining.1
  have hrem : stoppingRemainder (primaryPrimeFactors (d*e)) bin j t =
      primaryPrimeFactors e := by
    rw [primaryPrimeFactors_mul_union hd he]
    exact stoppingRemainder_of_separated_bins _ _ bin j
      (primeFactors_disjoint_of_squarefree_mul hd he hs) hselected.1 hremaining.1
  have ht : t ∈ (primeBin (primaryPrimeFactors (d*e)) bin j).powersetCard k := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_,hselected.2.1⟩
    intro p hp
    obtain ⟨hpd,hpj⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    rw [primaryPrimeFactors_mul_union hd he]
    exact ⟨Finset.mem_union_left _ hpd,hpj⟩
  have hsd : Squarefree d := hs.of_mul_left
  have hse : Squarefree e := hs.of_mul_right
  refine ⟨t,ht,?_,?_,?_,?_⟩
  · rw [hsel,primaryPrimeFactors_prod hd hsd]
  · rw [hrem,primaryPrimeFactors_prod he hse]
  · have hc := stopping_occupancies_add ht
    rw [hrem,hremaining.2] at hc
    exact hc.symm
  · rw [hsel]
    exact hselected.2.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeStoppingCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite reindexing from choices in the stopping bin to the
independent selected and complementary divisor subsets. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- This is the finite reindexing behind independent alpha/beta
collection; both subsets, and hence all coefficient weights, are exact. -/
theorem stopping_subset_sum (s : Finset Eisenstein) (bin : Eisenstein → ℕ)
    (j k : ℕ) (K : Finset Eisenstein → Finset Eisenstein → ℂ) :
    (∑ t ∈ (primeBin s bin j).powersetCard k,
      K (stoppingSelected s bin j t) (stoppingRemainder s bin j t)) =
    ∑ d ∈ stoppingDivisorSubsets s bin j k, K d (s \ d) := by
  apply Finset.sum_bij (fun t _ => stoppingSelected s bin j t)
  · intro t ht
    obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (stoppingSelected_subset hsub),
      fun p hp => stoppingSelected_bins_le hsub hp,?_,?_⟩
    · change ((stoppingSelected s bin j t).filter (fun p => bin p = j)).card = k
      rw [stoppingSelected_bin_count hsub,hcard]
    · intro p hp
      exact stoppingRemainder_bins_ge hp
  · intro t ht t' ht' heq
    have hsub := (Finset.mem_powersetCard.mp ht).1
    have hsub' := (Finset.mem_powersetCard.mp ht').1
    have hf := congrArg (fun d : Finset Eisenstein => d.filter (fun p => bin p = j)) heq
    rwa [stoppingSelected_bin_count hsub,stoppingSelected_bin_count hsub'] at hf
  · intro d hd
    obtain ⟨hdsub,hdlo,hdcard,hehi⟩ := Finset.mem_filter.mp hd
    have hdsub' := Finset.mem_powerset.mp hdsub
    let t := primeBin d bin j
    have ht : t ∈ (primeBin s bin j).powersetCard k := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_,hdcard⟩
      intro p hp
      obtain ⟨hpd,hpj⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hdsub' hpd,hpj⟩
    have hsel := stoppingSelected_of_separated_bins d (s \ d) bin j hdlo hehi
    rw [Finset.union_sdiff_of_subset hdsub'] at hsel
    exact ⟨t,ht,hsel⟩
  · intro t _ht
    rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingCoefficientIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal fixed-label stopping contribution as a sum over primary
factor pairs. This is the arithmetic bridge to independent alpha/beta. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Exact fixed-label coefficient identity, before any estimate or
extension by vanishing nonsquarefree terms. -/
theorem stopping_primary_pair_sum {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {B : ℝ} (hnB : norm n ≤ B)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k l : ℕ) (Z : ℝ) (r : Eisenstein)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → Eisenstein → ℂ) :
    (∑ t ∈ (primeBin (primaryPrimeFactors n) bin j).powersetCard k,
      if (primeBin (stoppingRemainder (primaryPrimeFactors n) bin j t) bin j).card = l ∧
          (norm r*primeSurrogate (stoppingSelected (primaryPrimeFactors n) bin j t) bin ell/
              ell j < Z ∧
            Z ≤ norm r*primeSurrogate
              (stoppingSelected (primaryPrimeFactors n) bin j t) bin ell) then
        cutoffMoebius ψ w (∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin j t, p)*
          cutoffMoebius ψ w (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin j t, p)*
          K (∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin j t, p)
            (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin j t, p)
      else 0) =
    ∑ q ∈ ((primaryElementBall B).product (primaryElementBall B)).filter
        (fun q => q.1*q.2 = n),
      if stoppingSideTest bin ell j k Z r q.1 ∧ stoppingRemainingTest bin j l q.2 then
        cutoffMoebius ψ w q.1*cutoffMoebius ψ w q.2*K q.1 q.2 else 0 := by
  rw [←squarefree_primary_factor_pairs hn hs hnB
    (fun d e => if stoppingSideTest bin ell j k Z r d ∧ stoppingRemainingTest bin j l e then
      cutoffMoebius ψ w d*cutoffMoebius ψ w e*K d e else 0)]
  let F := fun d e : Finset Eisenstein =>
    if (primeBin e bin j).card = l ∧
        (norm r*primeSurrogate d bin ell/ell j < Z ∧
          Z ≤ norm r*primeSurrogate d bin ell) then
      cutoffMoebius ψ w (∏ p ∈ d, p)*cutoffMoebius ψ w (∏ p ∈ e, p)*
        K (∏ p ∈ d, p) (∏ p ∈ e, p) else 0
  change (∑ t ∈ (primeBin (primaryPrimeFactors n) bin j).powersetCard k,
    F (stoppingSelected (primaryPrimeFactors n) bin j t)
      (stoppingRemainder (primaryPrimeFactors n) bin j t)) = _
  rw [stopping_subset_sum]
  unfold stoppingDivisorSubsets
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hsub := Finset.mem_powerset.mp hd
  have hdp : ∀ p ∈ d, primaryPrime p :=
    fun p hp => (primaryPrimeFactor_spec hn (hsub hp)).1
  have hep : ∀ p ∈ primaryPrimeFactors n \ d, primaryPrime p :=
    fun p hp => (primaryPrimeFactor_spec hn (Finset.mem_sdiff.mp hp).1).1
  dsimp only [F]
  unfold stoppingSideTest stoppingPrimeSetTest stoppingRemainingTest
  rw [primaryPrimeFactors_finset_prod d hdp,
    primaryPrimeFactors_finset_prod (primaryPrimeFactors n \ d) hep]
  rw [←ite_and]
  split_ifs <;> first | rfl | (exfalso; tauto)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GeometricStoppingKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact all-label stopping with the original product kernel attached.
The product kernel may include a sharp norm cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppingSelected_product_remainder {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) (bin : Eisenstein → ℕ) (j : ℕ)
    {t : Finset Eisenstein} (ht : t ⊆ primeBin (primaryPrimeFactors n) bin j) :
    (∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin j t, p)*
      (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin j t, p) = n := by
  exact (primaryFactorRemainder_spec hn hs (stoppingSelected_subset ht)).2.2

/-- The inverse-binomial stopping sum reconstructs the literal original
kernel, without smoothing or changing the product support. -/
theorem geometric_label_stopping_kernel {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) (hnorm : norm n ≤ X) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (hend : Z ≤ R*primeSurrogate (primaryPrimeFactors n)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X))
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ q ∈ stoppingLabelBox ρ X,
      ∑ t ∈ (primeBin (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1).powersetCard q.2.1,
        if (primeBin (stoppingRemainder (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t)
              (geometricPrimeBin ρ X) q.1).card = q.2.2 ∧
            (R*primeSurrogate (stoppingSelected (primaryPrimeFactors n)
                (geometricPrimeBin ρ X) q.1 t) (geometricPrimeBin ρ X) (geometricBinLower ρ X)/
                geometricBinLower ρ X q.1 < Z ∧
              Z ≤ R*primeSurrogate (stoppingSelected (primaryPrimeFactors n)
                (geometricPrimeBin ρ X) q.1 t) (geometricPrimeBin ρ X) (geometricBinLower ρ X)) then
          (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
            (cutoffMoebius ψ w (∏ p ∈ stoppingSelected (primaryPrimeFactors n)
                (geometricPrimeBin ρ X) q.1 t, p) *
              cutoffMoebius ψ w (∏ p ∈ stoppingRemainder (primaryPrimeFactors n)
                (geometricPrimeBin ρ X) q.1 t, p)) *
            K ((∏ p ∈ stoppingSelected (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t, p)*
              (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t, p))
        else 0) = cutoffMoebius ψ w n*K n := by
  have hp : ∀ p ∈ primaryPrimeFactors n, primaryPrime p :=
    fun p hp => (primaryPrimeFactor_spec hn hp).1
  have hpX : ∀ p ∈ primaryPrimeFactors n, norm p ≤ X := by
    intro p hp
    exact (norm_le_of_dvd (primary_ne_zero hn) (primaryPrimeFactor_spec hn hp).2).trans hnorm
  have hnprod := primaryPrimeFactors_prod hn hs
  have hprod : norm (∏ p ∈ primaryPrimeFactors n, p) ≤ X := by rwa [hnprod]
  have he := congrArg (fun z : ℂ => z*K n)
    (geometric_label_stopping_sum (primaryPrimeFactors n) hp hρ hρ₂ hX hprod hpX
      hR hstart hend ψ w)
  rw [hnprod] at he
  simp_rw [Finset.sum_mul,ite_mul,zero_mul] at he
  refine Eq.trans ?_ he
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro t ht
  rw [stoppingSelected_product_remainder hn hs _ _ (Finset.mem_powersetCard.mp ht).1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingThreshold
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact no-stop/stopped split. The original product kernel may
contain a sharp norm cutoff; no continuity is required. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppingSelected_surrogate_le (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    {j : ℕ} {t : Finset Eisenstein} (ht : t ⊆ primeBin s bin j) :
    primeSurrogate (stoppingSelected s bin j t) bin ell ≤ primeSurrogate s bin ell := by
  exact Finset.prod_le_prod_of_subset_of_one_le (stoppingSelected_subset ht)
    (fun p _ => zero_le_one.trans (hell (bin p))) (fun p _ _ => hell (bin p))

/-- If the entire original factor set is below the threshold, every
putative stopping label contributes zero individually. -/
lemma geometricStoppedElement_eq_zero {ρ X R Z : ℝ} (hρ : 1 ≤ ρ) (hR : 0 ≤ R)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) (n : Eisenstein)
    (hbelow : R*primeSurrogate (primaryPrimeFactors n)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z) :
    geometricStoppedElement ρ X R Z ψ w K n = 0 := by
  apply Finset.sum_eq_zero
  intro q _hq
  apply Finset.sum_eq_zero
  intro t ht
  apply ite_eq_right
  intro hc
  have hs := stoppingSelected_surrogate_le (primaryPrimeFactors n)
    (geometricPrimeBin ρ X) (geometricBinLower ρ X)
    (fun j => one_le_pow₀ hρ) (Finset.mem_powersetCard.mp ht).1
  exact (not_lt_of_ge (hc.2.2.trans (mul_le_mul_of_nonneg_left hs hR))) hbelow

/-- Unconditional in the end-crossing condition: the actual complete
label sum is exactly the original term times its stopping indicator. -/
theorem geometricStoppedElement_exact {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) (hnorm : norm n ≤ X) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    geometricStoppedElement ρ X R Z ψ w K n =
      if Z ≤ R*primeSurrogate (primaryPrimeFactors n)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) then
        cutoffMoebius ψ w n*K n else 0 := by
  by_cases hend : Z ≤ R*primeSurrogate (primaryPrimeFactors n)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X)
  · rw [ite_eq_left hend]
    exact geometric_label_stopping_kernel hn hs hρ hρ₂ hX hnorm hR hstart hend ψ w K
  · rw [ite_eq_right hend]
    exact geometricStoppedElement_eq_zero hρ.le hR.le ψ w K n (lt_of_not_ge hend)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughProductPairs
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the original rough-product divisor expansion
as independent primary factors, with the original product support. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem roughProduct_primary_factor_pair {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {X : ℝ} (hnX : norm n ≤ X)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (roughProduct ψ w n:ℂ)*K n =
      ∑ q ∈ ((primaryElementBall X).product (primaryElementBall X)).filter
          (fun q => q.1*q.2 = n), cutoffMoebius ψ w q.1*K (q.1*q.2) := by
  rw [←squarefree_primary_factor_pairs hn hs hnX
    (fun d e => cutoffMoebius ψ w d*K (d*e))]
  rw [roughProduct_primary_divisor_sum hn hs,Finset.sum_mul,
    primary_divisors_of_squarefree_eq hn hs,
    Finset.sum_image (primaryPrimeFactors_prod_injective
      (fun p hp => (primaryPrimeFactor_spec hn hp).1))]
  apply Finset.sum_congr rfl
  intro s hsubset
  have hprod := (primaryFactorRemainder_spec hn hs
    (Finset.mem_powerset.mp hsubset)).2.2
  unfold primaryFactorRemainder at hprod
  rw [hprod]

/-- The original finite support is kept as an exact product predicate.
There is no coprimality assumption or replacement of its sharp cutoff. -/
theorem roughProduct_finite_factor_pairs (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, (roughProduct ψ w n:ℂ)*K n) =
      ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
        if d*e ∈ S then cutoffMoebius ψ w d*K (d*e) else 0 := by
  calc
    _ = ∑ n ∈ S,
        ∑ q ∈ ((primaryElementBall X).product (primaryElementBall X)).filter
          (fun q => q.1*q.2 = n), cutoffMoebius ψ w q.1*K (q.1*q.2) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact roughProduct_primary_factor_pair (hS n hn).1 (hS n hn).2.1
        (hS n hn).2.2 ψ w K
    _ = _ := primary_pair_fiber_support S X (fun d e => cutoffMoebius ψ w d*K (d*e))

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

lemma primaryProductSlice_support (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (a : Eisenstein) :
    ∀ m ∈ primaryProductSlice S X a, primary m ∧ Squarefree m ∧ norm m ≤ X := by
  intro m hm
  obtain ⟨hmb,hprod⟩ := Finset.mem_filter.mp hm
  obtain ⟨hmp,hmX⟩ := mem_primaryElementBall.mp hmb
  exact ⟨hmp,(hS _ hprod).2.1.of_mul_right,hmX⟩

/-- Reindex the literal rough-product divisor expansion with the
complementary factor first. No condition is imposed on the kernel. -/
theorem roughProduct_slice_pairs (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (r : Eisenstein) (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ primaryProductSlice S X r, (roughProduct ψ w n:ℂ)*K (r*n)) =
      ∑ u ∈ primaryElementBall X, ∑ m ∈ primaryProductSlice S X (r*u),
        cutoffMoebius ψ w m*K (r*(m*u)) := by
  rw [roughProduct_finite_factor_pairs (primaryProductSlice S X r) X
    (primaryProductSlice_support S X hS r) ψ w (fun n => K (r*n)),
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  conv_rhs => rw [primaryProductSlice,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  have hp := primary_mul (mem_primaryElementBall.mp hm).1
    (mem_primaryElementBall.mp hu).1
  have heq : r*(m*u) = (r*u)*m := by ring
  simp only [mem_primaryProductSlice_iff S X hS r hp,heq]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_NoStopParameters
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's actual no-stop threshold is short enough for Type I.
All scale conditions are derived from their strict numerical exponent gaps. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventually_noStop_scales {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) :
    ∀ᶠ X : ℝ in atTop,
      2 ≤ X ∧ 1 ≤ Real.log X ∧ Real.exp hW.radius ≤ X ∧
      1 ≤ X^(2/5:ℝ) ∧
      (Real.exp hW.radius*X)^((1/100:ℝ)/4)*X^(38/100:ℝ) ≤ X^(2/5:ℝ) ∧
      2*X^(2/5:ℝ) ≤ X^(51/100:ℝ) := by
  filter_upwards [eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (Real.exp hW.radius),
    eventually_const_mul_rpow_le (by norm_num : (1/400:ℝ)+38/100 < 2/5)
      ((Real.exp hW.radius)^(1/400:ℝ)),
    eventually_const_mul_rpow_le (by norm_num : (2/5:ℝ) < 51/100) 2]
    with X hX hlog hBX hdist hshort
  refine ⟨hX,hlog,hBX,Real.one_le_rpow (by linarith) (by norm_num),?_,hshort⟩
  have hXp : 0 < X := by linarith
  have he : (1/100:ℝ)/4 = 1/400 := by norm_num
  rw [he,Real.mul_rpow (Real.exp_pos _).le hXp.le,mul_assoc,←Real.rpow_add hXp]
  exact hdist

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

lemma distinguishedScaleCoefficient_range (i : ℕ) (ξ X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    {r : Eisenstein} (hne : distinguishedScaleCoefficient i ξ X k r ≠ 0) :
    distinguishedScaleLength k ≤ norm r ∧ norm r ≤ 2^i*distinguishedScaleLength k := by
  have hn : ∃ f ∈ (Fintype.piFinset (fun _ : Fin i =>
        primeCutoff (Real.exp primeProductWeights.radius*X))).filter (fun f => (∏ a, f a) = r),
      (∏ a, normPartitionWeight (2*norm (f a)/(4/3:ℝ)^(k a).val)*
        distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (f a)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    unfold distinguishedScaleCoefficient distinguishedTupleCoefficient orderedConvolution
    rw [Finset.sum_eq_zero h,mul_zero]
  obtain ⟨f,hf,hw⟩ := hn
  have he := (Finset.mem_filter.mp hf).2
  have hcoord (a : Fin i) := normPartitionWeight_nonzero_scale
    (mul_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hw a (Finset.mem_univ a))).1
  rw [←he,norm_finset_prod]
  constructor
  · apply Finset.prod_le_prod
      (fun a _ => by positivity)
    intro a _
    have hh := (hcoord a).2
    linarith
  · calc
      _ ≤ ∏ a : Fin i, (4/3:ℝ)^(k a).val :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun a _ => (hcoord a).1)
      _ = 2^i*distinguishedScaleLength k := by
        simp only [distinguishedScaleLength,Finset.prod_div_distrib,Finset.prod_const,
          Finset.card_univ,Fintype.card_fin]
        field_simp

lemma distinguishedScaleCoefficient_norm (i : ℕ) (ξ X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (r : Eisenstein) :
    ‖distinguishedScaleCoefficient i ξ X k r‖ ≤ ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ) := by
  simpa only [Fintype.card_fin,distinguishedScaleCoefficient] using distinguishedTupleCoefficient_norm (ι := Fin i) _
    (fun _ _ hp => (mem_primeCutoff.mp hp).1) _
    (fun _ p _ => normPartitionWeight_norm _)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) _ _ r

lemma eventually_distinguishedScale_low_initial (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ k : Fin i →
      Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      distinguishedScaleLength k < X^(69/200:ℝ) → ∀ r : Eisenstein,
      distinguishedScaleCoefficient i ξ X k r ≠ 0 → norm r < X^(9/25:ℝ) := by
  filter_upwards [eventually_const_mul_rpow_le
    (by norm_num : (69/200:ℝ) < 9/25) (2^i)] with X hX
  intro k hk r hr
  exact (distinguishedScaleCoefficient_range i ξ X k hr).2.trans_lt
    ((mul_lt_mul_of_pos_left hk (by positivity)).trans_le hX)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedStoppingWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCharacterRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal stopped character sum as a squarefree coefficient row.
The norm phase preserves its energy, and the energy is derived from the
actual distinguished coefficient rather than supplied as a hypothesis. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedIntervalSupport_spec (X a b : ℝ) (e : Eisenstein)
    {n : Eisenstein} (hn : n ∈ stoppedIntervalSupport ι X a b e) :
    primary n ∧ Squarefree n ∧ norm n ≤ b := by
  obtain ⟨hm,hs,_,_,hb⟩ := Finset.mem_filter.mp hn
  have hp := primaryPairSupport_primary _ _
    (fun r hr => orderedPrimarySupport_primary _
      (fun _ _ h => (mem_primeCutoff.mp h).1.1) hr)
    (fun d hd => (mem_primaryElementBall.mp hd).1) hm
  exact ⟨hp,hs,hb⟩

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

lemma stoppedNormDyad_partition (S : Finset Eisenstein) (f : Eisenstein → ℂ) :
    (∑ n ∈ S, f n) = ∑ j ∈ S.image stoppedNormDyadIndex,
      ∑ n ∈ stoppedNormDyad S j, f n := by
  unfold stoppedNormDyad
  exact (Finset.sum_fiberwise_of_maps_to (s := S)
    (t := S.image stoppedNormDyadIndex) (g := stoppedNormDyadIndex)
    (fun n hn => Finset.mem_image_of_mem _ hn) f).symm

lemma stoppedNormDyad_count (S : Finset Eisenstein) {Y : ℝ}
    (hS : ∀ n ∈ S, norm n ≤ Y) :
    (S.image stoppedNormDyadIndex).card ≤ Nat.log 2 ⌊Y⌋₊+1 := by
  apply le_trans (Finset.card_le_card (show S.image stoppedNormDyadIndex ⊆
    Finset.range (Nat.log 2 ⌊Y⌋₊+1) from ?_)) (by rw [Finset.card_range])
  intro j hj
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hj
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  apply Nat.log_mono_right
  exact (Nat.sub_le _ _).trans (Nat.le_floor (by simpa only [normNat_cast] using hS n hn))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedRowRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-envelope changes for the actual stopped coefficient.
Every factor in a fibre divides its prescribed product. Thus a bounded
product uses only the smaller prime and divisor cutoffs. The selected-side
predicate is retained verbatim, including any extra restriction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedBeta_selected_congr (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected selected' : Eisenstein → Eisenstein → Prop)
    (b : Eisenstein)
    (hselected : ∀ r ∈ R, ∀ d ∈ D, r*d = b → (selected r d ↔ selected' r d)) :
    stoppedBeta R D v ψ w selected b = stoppedBeta R D v ψ w selected' b := by
  unfold stoppedBeta primaryPairCoefficient
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
  obtain ⟨hr,hd⟩ := Finset.mem_product.mp hp
  dsimp only
  rw [propext (hselected p.1 hr p.2 hd he)]

lemma primaryPairFiber_ball_restrict {X F : ℝ} (hXF : X ≤ F)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    primaryPairFiber (primaryElementBall F) (primaryElementBall F) b =
      primaryPairFiber (primaryElementBall X) (primaryElementBall X) b := by
  ext p
  simp only [primaryPairFiber,Finset.mem_filter,Finset.mem_product]
  constructor
  · rintro ⟨⟨hr,hd⟩,he⟩
    have hrb : p.1 ∣ b := ⟨p.2,he.symm⟩
    have hdb : p.2 ∣ b := ⟨p.1,by rw [mul_comm,he]⟩
    exact ⟨⟨mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hr).1,
      (norm_le_of_dvd (primary_ne_zero hb) hrb).trans hbX⟩,
      mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hd).1,
      (norm_le_of_dvd (primary_ne_zero hb) hdb).trans hbX⟩⟩,he⟩
  · rintro ⟨⟨hr,hd⟩,he⟩
    exact ⟨⟨mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hr).1,
      (mem_primaryElementBall.mp hr).2.trans hXF⟩,
      mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hd).1,
      (mem_primaryElementBall.mp hd).2.trans hXF⟩⟩,he⟩

lemma primeTupleFiber_restrict {X F : ℝ} (hXF : X ≤ F)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    (Fintype.piFinset (fun _ : ι => primeCutoff F)).filter (fun f => (∏ i, f i) = b) =
      (Fintype.piFinset (fun _ : ι => primeCutoff X)).filter (fun f => (∏ i, f i) = b) := by
  ext f
  simp only [Finset.mem_filter,Fintype.mem_piFinset]
  constructor
  · rintro ⟨hf,he⟩
    refine ⟨fun i => mem_primeCutoff.mpr ⟨(mem_primeCutoff.mp (hf i)).1,?_⟩,he⟩
    have hd : f i ∣ b := he ▸ Finset.dvd_prod_of_mem f (Finset.mem_univ i)
    exact (norm_le_of_dvd (primary_ne_zero hb) hd).trans hbX
  · rintro ⟨hf,he⟩
    exact ⟨fun i => mem_primeCutoff.mpr ⟨(mem_primeCutoff.mp (hf i)).1,
      (mem_primeCutoff.mp (hf i)).2.trans hXF⟩,he⟩

lemma distinguishedTupleCoefficient_restrict {X F : ℝ} (hXF : X ≤ F)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    distinguishedTupleCoefficient (fun _ : ι => primeCutoff F) W ψ w z b =
      distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z b := by
  unfold distinguishedTupleCoefficient orderedConvolution
  rw [primeTupleFiber_restrict hXF hb hbX]

lemma stoppedBeta_tuple_ball_restrict {X F : ℝ} (hXF : X ≤ F)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ)
    (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F) W ψ w z)
      ψ w selected b =
    stoppedBeta (primaryElementBall X) (primaryElementBall X)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z)
      ψ w selected b := by
  unfold stoppedBeta primaryPairCoefficient
  rw [primaryPairFiber_ball_restrict hXF hb hbX]
  apply Finset.sum_congr rfl
  intro p hp
  have hr := (mem_primaryElementBall.mp (Finset.mem_product.mp
    (Finset.mem_filter.mp hp).1).1)
  dsimp only
  rw [distinguishedTupleCoefficient_restrict hXF W ψ w z hr.1 hr.2]

lemma stoppedBeta_tuple_support (X : ℝ)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ)
    (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    stoppedBeta (primaryElementBall X) (primaryElementBall X)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z)
      ψ w selected b =
    stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff X))
      (primaryElementBall X)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z)
      ψ w selected b := by
  unfold stoppedBeta primaryPairCoefficient
  apply Finset.sum_congr_of_eq_on_inter
  · intro p hp hn
    have hp' := Finset.mem_filter.mp hp
    have hd := (Finset.mem_product.mp hp'.1).2
    have hr : p.1 ∉ orderedConvolutionSupport (fun _ : ι => primeCutoff X) := by
      intro hr
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr,hd⟩,hp'.2⟩)
    have hz : distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z p.1 = 0 := by
      unfold distinguishedTupleCoefficient
      rw [orderedConvolution_eq_zero_of_not_mem _ _ hr,mul_zero]
    simp only [hz,zero_mul,ite_self]
  · intro p hp hn
    have hp' := Finset.mem_filter.mp hp
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp hp'.1
    have hrp : primary p.1 := orderedPrimarySupport_primary _
      (fun _ _ h => (mem_primeCutoff.mp h).1.1) hr
    have hrX : norm p.1 ≤ X :=
      (norm_le_of_dvd (primary_ne_zero hb) ⟨p.2,hp'.2.symm⟩).trans hbX
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨mem_primaryElementBall.mpr ⟨hrp,hrX⟩,hd⟩,hp'.2⟩)).elim
  · intro _ _ _
    rfl

/-- The actual finite-envelope beta, with its exact selected predicate,
is the analytic row at norm twist zero on every bounded primary product. -/
theorem stoppedBeta_eq_stoppedRowCoefficient {X F : ℝ} (hXF : X ≤ F)
    (W : ι → ℝ → ℂ) (w z : ℝ)
    (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun i p => W i (norm p)) primeDetectorCutoff w z)
      primeDetectorCutoff w selected b =
      stoppedRowCoefficient X w z 0 W selected b := by
  rw [stoppedBeta_tuple_ball_restrict hXF,stoppedBeta_tuple_support X]
  · simp only [stoppedRowCoefficient,normTwist,zero_mul,Complex.ofReal_zero,
      Complex.exp_zero,mul_one]
  all_goals assumption

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

lemma geometricBinLower_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (j : ℕ) :
    geometricBinLower ρ F (j+(geometricBinCount ρ F-geometricBinCount ρ X)) =
      geometricBinLower ρ X j := by
  have hc := geometricBinCount_mono hρ hX hXF
  unfold geometricBinLower
  congr 1
  omega

lemma geometricPrimeBin_finset_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p ∧ norm p ≤ X) (j : ℕ) :
    primeBin s (geometricPrimeBin ρ F)
        (j+(geometricBinCount ρ F-geometricBinCount ρ X)) =
      primeBin s (geometricPrimeBin ρ X) j := by
  ext p
  by_cases hp : p ∈ s
  · simp only [primeBin,Finset.mem_filter,hp,true_and,
      geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2,
      Nat.add_right_cancel_iff]
  · simp only [primeBin,Finset.mem_filter,hp,false_and]

lemma geometricPrimeBin_prefix_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p ∧ norm p ≤ X) (j : ℕ) :
    primeBinPrefix s (geometricPrimeBin ρ F)
        (j+(geometricBinCount ρ F-geometricBinCount ρ X)) =
      primeBinPrefix s (geometricPrimeBin ρ X) j := by
  ext p
  by_cases hp : p ∈ s
  · simp only [primeBinPrefix,Finset.mem_filter,hp,true_and,
      geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2,
      Nat.add_lt_add_iff_right]
  · simp only [primeBinPrefix,Finset.mem_filter,hp,false_and]

lemma geometricPrimeSurrogate_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p ∧ norm p ≤ X) :
    primeSurrogate s (geometricPrimeBin ρ F) (geometricBinLower ρ F) =
      primeSurrogate s (geometricPrimeBin ρ X) (geometricBinLower ρ X) := by
  apply Finset.prod_congr rfl
  intro p hp
  rw [geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2,
    geometricBinLower_shift hρ hX hXF]

lemma geometricStoppingPrimeSetTest_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p ∧ norm p ≤ X)
    (j k : ℕ) (Z : ℝ) (r : Eisenstein) :
    stoppingPrimeSetTest s (geometricPrimeBin ρ F) (geometricBinLower ρ F)
      (j+(geometricBinCount ρ F-geometricBinCount ρ X)) k Z r ↔
    stoppingPrimeSetTest s (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k Z r := by
  have hall : (∀ p ∈ s, geometricPrimeBin ρ F p ≤
      j+(geometricBinCount ρ F-geometricBinCount ρ X)) ↔
      ∀ p ∈ s, geometricPrimeBin ρ X p ≤ j := by
    constructor
    · intro h p hp
      have he := h p hp
      rw [geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2] at he
      omega
    · intro h p hp
      rw [geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2]
      exact Nat.add_le_add_right (h p hp) _
  unfold stoppingPrimeSetTest
  rw [hall,geometricPrimeBin_finset_shift hρ hX hXF s hs,
    geometricPrimeSurrogate_shift hρ hX hXF s hs,geometricBinLower_shift hρ hX hXF]

lemma geometricStoppedSideTest_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) {d : Eisenstein}
    (hd : primary d) (hdX : norm d ≤ X)
    (j k h : ℕ) (Z Q : ℝ) (early : Bool) (r : Eisenstein) :
    stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
      (j+(geometricBinCount ρ F-geometricBinCount ρ X)) k
      (h+(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early r d ↔
    stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h Z Q early r d := by
  have hs (p : Eisenstein) (hp : p ∈ primaryPrimeFactors d) :
      primaryPrime p ∧ norm p ≤ X :=
    ⟨(primaryPrimeFactor_spec hd hp).1,
      (norm_le_of_dvd (primary_ne_zero hd) (primaryPrimeFactor_spec hd hp).2).trans hdX⟩
  have hprefix := geometricPrimeBin_prefix_shift hρ hX hXF (primaryPrimeFactors d) hs h
  have hsur := geometricPrimeSurrogate_shift hρ hX hXF
    (primeBinPrefix (primaryPrimeFactors d) (geometricPrimeBin ρ X) h)
    (fun p hp => hs p (Finset.mem_filter.mp hp).1)
  unfold stoppedSideTest stoppingSideTest
  rw [geometricStoppingPrimeSetTest_shift hρ hX hXF (primaryPrimeFactors d) hs,
    hprefix,hsur]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingLogBoundary
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine bin boundary simultaneously preserves logarithmic
roughness in the first stage and bounds every late prime by a logarithmic
power. The choice is uniform in the geometric mesh. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem exists_geometric_boundary {ρ B Y : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hY : 4 ≤ Y) (hYB : Y < B) :
    ∃ h : ℕ, h < geometricBinCount ρ B ∧
      Y/4 ≤ geometricBinLower ρ B h ∧ ρ*geometricBinLower ρ B h ≤ Y := by
  have hρp : 0 < ρ := zero_lt_one.trans hρ
  have hBp : 0 < B := lt_of_lt_of_le (by norm_num) (hY.trans hYB.le)
  have hbase : B ≤ geometricBinLower ρ B 0 := by
    change B ≤ ρ^(geometricBinCount ρ B)
    apply (Real.le_pow_iff_log_le hBp hρp).mpr
    exact (div_le_iff₀ (Real.log_pos hρ)).mp (Nat.le_ceil (Real.log B/Real.log ρ))
  have hex : ∃ h : ℕ, ρ*geometricBinLower ρ B h ≤ Y := by
    refine ⟨geometricBinCount ρ B,?_⟩
    simpa only [geometricBinLower,Nat.sub_self,pow_zero,mul_one] using
      hρ₂.trans (by linarith : (2:ℝ) ≤ Y)
  let h := Nat.find hex
  have hhit : ρ*geometricBinLower ρ B h ≤ Y := Nat.find_spec hex
  have hle : h ≤ geometricBinCount ρ B := by
    apply Nat.find_min' hex
    simpa only [geometricBinLower,Nat.sub_self,pow_zero,mul_one] using
      hρ₂.trans (by linarith : (2:ℝ) ≤ Y)
  have hpos : 0 < h := by
    by_contra hn
    have he : h = 0 := by omega
    rw [he] at hhit
    have hbase' : geometricBinLower ρ B 0 < ρ*geometricBinLower ρ B 0 := by
      exact lt_mul_of_one_lt_left (pow_pos hρp _) hρ
    exact (not_lt_of_ge hhit) ((hYB.trans_le hbase).trans hbase')
  have hprev : Y < ρ*geometricBinLower ρ B (h-1) :=
    lt_of_not_ge (Nat.find_min hex (by change h-1 < h; omega))
  have hstep : geometricBinLower ρ B (h-1) = ρ*geometricBinLower ρ B h := by
    have he : geometricBinCount ρ B-(h-1) = geometricBinCount ρ B-h+1 := by omega
    simp only [geometricBinLower,he,pow_succ']
  rw [hstep] at hprev
  have hpow : 0 ≤ geometricBinLower ρ B h := pow_nonneg hρp.le _
  have hsquare : ρ*ρ ≤ 4 := by
    nlinarith [mul_self_le_mul_self hρp.le hρ₂]
  have hsmall : Y < 4*geometricBinLower ρ B h :=
    hprev.trans_le (by nlinarith [mul_le_mul_of_nonneg_right hsquare hpow])
  have hlt : h < geometricBinCount ρ B := by
    by_contra hn
    have he : h = geometricBinCount ρ B := by omega
    rw [he] at hsmall
    simp only [geometricBinLower,Nat.sub_self,pow_zero,mul_one] at hsmall
    linarith
  exact ⟨h,hlt,by linarith,hhit⟩

theorem eventually_stopping_log_boundary (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∃ h : ℕ, h < geometricBinCount ρ X ∧
        2*(Real.log X)^G ≤ geometricBinLower ρ X h ∧
          ρ*geometricBinLower ρ X h ≤ (Real.log X)^(G+4) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop ((G+4:ℕ):ℝ)
    (by norm_num : (0:ℝ) < 1)).def (by norm_num : (0:ℝ) < 1/2)
  filter_upwards [hsmall,Real.tendsto_log_atTop.eventually_ge_atTop 2,
    eventually_gt_atTop (0:ℝ)] with X hsmall hL hX
  intro ρ hρ hρ₂
  have hlog : 0 ≤ Real.log X := by linarith
  have hYB : (Real.log X)^(G+4) < X := by
    have hbound : (Real.log X)^(G+4) ≤ (1/2:ℝ)*X := by
      simpa only [Real.rpow_natCast,Real.rpow_one,
        Real.norm_of_nonneg (pow_nonneg hlog _),Real.norm_of_nonneg hX.le] using hsmall
    linarith
  have hfour : (8:ℝ) ≤ (Real.log X)^4 := by
    calc
      _ ≤ (2:ℝ)^4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hL _
  have hG : 1 ≤ (Real.log X)^G := one_le_pow₀ (by linarith)
  have hlower : 2*(Real.log X)^G ≤ (Real.log X)^(G+4)/4 := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hfour (pow_nonneg hlog G)]
  obtain ⟨h,hh,hlo,hhi⟩ := exists_geometric_boundary hρ hρ₂
    (by nlinarith : (4:ℝ) ≤ (Real.log X)^(G+4)) hYB
  exact ⟨h,hh,hlower.trans hlo,hhi⟩

theorem eventually_stopping_active_boundary {ξ : ℝ} (hξ : 0 < ξ) (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ h : ℕ, h < geometricBinCount (1+δ) X ∧
        2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) ∧
          (1+δ)*geometricBinLower (1+δ) X h ≤ (Real.log X)^(G+4) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (G:ℝ) hξ).def
    (by norm_num : (0:ℝ) < 1/2)
  filter_upwards [eventually_stopping_log_boundary G,hsmall,
    Real.tendsto_log_atTop.eventually_ge_atTop 0,eventually_gt_atTop (0:ℝ)]
    with X hboundary hsmall hlog hX
  intro δ hδ hδone
  obtain ⟨h,hh,hlo,hhi⟩ := hboundary (1+δ) (by linarith) (by linarith)
  have hpower : 2*(Real.log X)^G ≤ X^ξ := by
    have he : (Real.log X)^G ≤ (1/2:ℝ)*X^ξ := by
      simpa only [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg hlog _),
        Real.norm_of_nonneg (Real.rpow_nonneg hX.le _)] using hsmall
    linarith
  exact ⟨h,hh,le_min hpower hlo,hhi⟩

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedIntervalRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion of the sharp stopped side to the full analytic
interval at exclusion e=1. Coefficients vanish off their actual product
support, so the interval extension adds no term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedNormDyad_mem_iff {S : Finset Eisenstein} {j : ℕ} {n : Eisenstein}
    (hN : 2 ≤ norm n) :
    n ∈ stoppedNormDyad S j ↔
      n ∈ S ∧ stoppedNormDyadLength j/2 < norm n ∧ norm n ≤ stoppedNormDyadLength j := by
  constructor
  · intro hn
    exact ⟨(Finset.mem_filter.mp hn).1,stoppedNormDyad_bounds hn hN⟩
  · rintro ⟨hn,hlo,hhi⟩
    apply Finset.mem_filter.mpr
    refine ⟨hn,?_⟩
    have he : stoppedNormDyadLength j/2 = (2:ℝ)^j := by
      unfold stoppedNormDyadLength
      rw [pow_succ]
      ring
    rw [he] at hlo
    have hl : (2:ℕ)^j < normNat n := by
      exact_mod_cast (show (2:ℝ)^j < (normNat n:ℝ) by simpa only [normNat_cast] using hlo)
    have hu : normNat n ≤ (2:ℕ)^(j+1) := by
      exact_mod_cast (show (normNat n:ℝ) ≤ (2:ℝ)^(j+1) by
        simpa only [normNat_cast,stoppedNormDyadLength] using hhi)
    exact Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)

lemma primaryPairSupport_self_of_mem {F : ℝ} (hF : 1 ≤ F)
    {n : Eisenstein} (hn : n ∈ primaryElementBall F) :
    n ∈ primaryPairSupport (primaryElementBall F) (primaryElementBall F) := by
  refine Finset.mem_image.mpr ⟨(n,1),Finset.mem_product.mpr ⟨hn,?_⟩,by simp⟩
  exact mem_primaryElementBall.mpr ⟨primary_one,by simpa only [norm_one_eq] using hF⟩

lemma stoppedRowCoefficient_eq_zero_of_not_mem (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) {n : Eisenstein}
    (hn : n ∉ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff X))
      (primaryElementBall X)) :
    stoppedRowCoefficient X w z u W selected n = 0 := by
  unfold stoppedRowCoefficient stoppedBeta primaryPairCoefficient
  suffices hs : (∑ p ∈ primaryPairFiber
      (orderedConvolutionSupport (fun _ : ι => primeCutoff X)) (primaryElementBall X) n,
      if selected p.1 p.2 then
        distinguishedTupleCoefficient (fun _ : ι => primeCutoff X)
          (fun i p => W i (norm p)) primeDetectorCutoff w z p.1 *
            cutoffMoebius primeDetectorCutoff w p.2 else 0) = 0 by rw [hs,zero_mul]
  apply Finset.sum_eq_zero
  intro p hp
  exact (hn (Finset.mem_image.mpr ⟨p,(Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2⟩)).elim

theorem stoppedBeta_interval_sum_to_row {X F B : ℝ}
    (hX : 1 ≤ X) (hXF : X ≤ F) (hBX : B ≤ X)
    (W : ι → ℝ → ℂ) (w z a : ℝ)
    (selected : Eisenstein → Eisenstein → Prop) (K : Eisenstein → ℂ) :
    (∑ n ∈ (primaryPairSupport (primaryElementBall F) (primaryElementBall F)).filter
        (fun n => Squarefree n ∧ a < norm n ∧ norm n ≤ B),
      stoppedBeta (primaryElementBall F) (primaryElementBall F)
        (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
          (fun i p => W i (norm p)) primeDetectorCutoff w z)
        primeDetectorCutoff w selected n*K n) =
      ∑ n ∈ stoppedIntervalSupport ι X a B 1,
        stoppedRowCoefficient X w z 0 W selected n*K n := by
  let Q := primaryPairSupport (primaryElementBall F) (primaryElementBall F)
  have hQ (n : Eisenstein) (hn : n ∈ Q) : primary n :=
    primaryPairSupport_primary _ _ (fun _ h => (mem_primaryElementBall.mp h).1)
      (fun _ h => (mem_primaryElementBall.mp h).1) hn
  apply Finset.sum_congr_of_eq_on_inter
  · intro n hn hnot
    obtain ⟨hn,hs,hlo,hhi⟩ := Finset.mem_filter.mp hn
    have hp := hQ n hn
    have hb := stoppedBeta_eq_stoppedRowCoefficient hXF W w z selected hp (hhi.trans hBX)
    rw [hb]
    have hsupport : n ∉ primaryPairSupport
        (orderedConvolutionSupport (fun _ : ι => primeCutoff X)) (primaryElementBall X) := by
      intro hh
      apply hnot
      apply Finset.mem_filter.mpr
      exact ⟨hh,hs,isCoprime_one_right,hlo,hhi⟩
    rw [stoppedRowCoefficient_eq_zero_of_not_mem X w z 0 W selected hsupport,zero_mul]
  · intro n hn hnot
    obtain ⟨hp,hs,hhi⟩ := stoppedIntervalSupport_spec X a B 1 hn
    have hh := Finset.mem_filter.mp hn
    have hnQ : n ∈ Q := primaryPairSupport_self_of_mem (hX.trans hXF)
      (mem_primaryElementBall.mpr ⟨hp,(hhi.trans hBX).trans hXF⟩)
    exact (hnot (Finset.mem_filter.mpr ⟨hnQ,hs,hh.2.2.2.1,hhi⟩)).elim
  · intro n hn _
    obtain ⟨hn,_hs,_hlo,hhi⟩ := Finset.mem_filter.mp hn
    rw [stoppedBeta_eq_stoppedRowCoefficient hXF W w z selected (hQ n hn) (hhi.trans hBX)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDyadRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original squarefree sharp dyad is exactly the full analytic
stopped interval. Its possible norm-one term vanishes by the genuine
stopping lower bound, rather than being discarded from the finite sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedRowCoefficient_geometric_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (W : ι → ℝ → ℂ) (w z u Z Q : ℝ)
    (j k h : ℕ) (early : Bool) (n : Eisenstein) :
    stoppedRowCoefficient X w z u W
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
        (j+(geometricBinCount ρ F-geometricBinCount ρ X)) k
        (h+(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early) n =
      stoppedRowCoefficient X w z u W
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          j k h Z Q early) n := by
  unfold stoppedRowCoefficient
  congr 1
  apply stoppedBeta_selected_congr
  intro r _ d hd _
  have hdp := mem_primaryElementBall.mp hd
  exact geometricStoppedSideTest_shift hρ hX hXF hdp.1 hdp.2 j k h Z Q early r

lemma stoppedRowCoefficient_geometric_shift_of_bounds {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (W : ι → ℝ → ℂ) (w z u Z Q : ℝ)
    (j k h : ℕ) (early : Bool) (n : Eisenstein)
    (hj : geometricBinCount ρ F-geometricBinCount ρ X ≤ j)
    (hh : geometricBinCount ρ F-geometricBinCount ρ X ≤ h) :
    stoppedRowCoefficient X w z u W
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k h Z Q early) n =
      stoppedRowCoefficient X w z u W
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          (j-(geometricBinCount ρ F-geometricBinCount ρ X)) k
          (h-(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early) n := by
  simpa only [Nat.sub_add_cancel hj,Nat.sub_add_cancel hh] using
    stoppedRowCoefficient_geometric_shift hρ hX hXF W w z u Z Q
      (j-(geometricBinCount ρ F-geometricBinCount ρ X)) k
      (h-(geometricBinCount ρ F-geometricBinCount ρ X)) early n

theorem stoppedBeta_sharp_dyad_to_row {ρ X F w Z Q : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X) (hXF : X ≤ F)
    (hw : 0 < w) (hZ : 2 ≤ Z) (W : ι → ℝ → ℂ) (z : ℝ)
    (j k h i : ℕ) (hk : 1 ≤ k) (early : Bool) (K : Eisenstein → ℂ)
    (hBX : stoppedNormDyadLength i ≤ X) :
    let selected := stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
      j k h Z Q early
    let β := stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun a p => W a (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w selected
    (∑ n ∈ stoppedNormDyad
        ((primaryPairSupport (primaryElementBall F) (primaryElementBall F)).filter
          (fun n => Squarefree n ∧ norm n ≤ F)) i, β n*K n) =
      ∑ n ∈ stoppedIntervalSupport ι X (stoppedNormDyadLength i/2)
        (stoppedNormDyadLength i) 1,
        stoppedRowCoefficient X w z 0 W selected n*K n := by
  let selected := stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
    j k h Z Q early
  let β := stoppedBeta (primaryElementBall F) (primaryElementBall F)
    (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
      (fun a p => W a (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w selected
  let R := primaryPairSupport (primaryElementBall F) (primaryElementBall F)
  let B := stoppedNormDyadLength i
  change (∑ n ∈ stoppedNormDyad (R.filter (fun n => Squarefree n ∧ norm n ≤ F)) i,
      β n*K n) = ∑ n ∈ stoppedIntervalSupport ι X (B/2) B 1,
        stoppedRowCoefficient X w z 0 W selected n*K n
  have hB : 2 ≤ B := by
    have hh : (1:ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
    dsimp [B,stoppedNormDyadLength]
    rw [pow_succ]
    nlinarith
  have hlow (n : Eisenstein) (hs : Squarefree n) (hne : β n ≠ 0) :
      2 ≤ norm n := by
    have hh := stoppedBeta_norm_bounds (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun a p => W a (norm p)) primeDetectorCutoff w z)
      (fun x hx => primeDetectorCutoff_zero hx) hρ hρ₂ (by norm_num : (0:ℝ) ≤ 1)
      (by simpa using hρ₂) (by linarith : 0 < Z) hw
      (fun d hd => mem_primaryElementBall.mp hd) hk early hs hne
    exact hZ.trans hh.1
  have heq : (∑ n ∈ stoppedNormDyad (R.filter (fun n => Squarefree n ∧ norm n ≤ F)) i,
      β n*K n) = ∑ n ∈ R.filter (fun n => Squarefree n ∧ B/2 < norm n ∧ norm n ≤ B),
        β n*K n := by
    apply Finset.sum_congr_of_eq_on_inter
    · intro n hn hnot
      by_cases hz : β n = 0
      · rw [hz,zero_mul]
      · have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.1
        have hr := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
        have hd := stoppedNormDyad_bounds hn (hlow n hs hz)
        exact (hnot (Finset.mem_filter.mpr ⟨hr,hs,hd⟩)).elim
    · intro n hn hnot
      obtain ⟨hr,hs,hlo,hhi⟩ := Finset.mem_filter.mp hn
      have hone : (1:ℝ) < norm n := lt_of_le_of_lt (by linarith) hlo
      have hnat : 1 < normNat n := by
        exact_mod_cast (show (1:ℝ) < (normNat n:ℝ) by simpa only [normNat_cast] using hone)
      have hn2 : (2:ℝ) ≤ norm n := by
        rw [←normNat_cast]
        exact_mod_cast (show 2 ≤ normNat n by omega)
      apply (hnot ((stoppedNormDyad_mem_iff hn2).mpr ?_)).elim
      exact ⟨Finset.mem_filter.mpr ⟨hr,hs,(hhi.trans hBX).trans hXF⟩,hlo,hhi⟩
    · intro _ _ _
      rfl
  rw [heq]
  exact stoppedBeta_interval_sum_to_row hX hXF hBX W w z (B/2) selected K

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

lemma centeredHeightKernel_norm_range (ℓ : ℤ) (H T : ℝ) {X : ℝ}
    (hX : 0 < X) {n : Eisenstein}
    (hne : centeredHeightKernel ℓ primeProductEnvelope H T X X n ≠ 0) :
    X/2 < norm n ∧ norm n < 3*X := by
  have hW : primeProductEnvelope (norm n/X) ≠ 0 := by
    intro hz
    apply hne
    simp only [centeredHeightKernel,hz,mul_zero,zero_mul]
  constructor
  · by_contra hn
    apply hW
    apply primeProductEnvelope_zero_lower
    exact (div_le_iff₀ hX).mpr (by linarith)
  · by_contra hn
    apply hW
    apply primeProductEnvelope_zero
    exact (le_div_iff₀ hX).mpr (by linarith)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedMatrixDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independent sharp side dyads for the stopped matrices. The
squarefree product envelope supplies the side support; no coprimality
restriction or boundary contribution is discarded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma centralProduct_factor_support {X : ℝ} {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hab : a*b ∈ centralProductEnvelope X) :
    (Squarefree a ∧ norm a ≤ Real.exp primeProductWeights.radius*X) ∧
      (Squarefree b ∧ norm b ≤ Real.exp primeProductWeights.radius*X) := by
  have hs := centralProductEnvelope_spec hab
  have hn := primary_ne_zero (primary_mul ha hb)
  exact ⟨⟨hs.2.1.of_mul_left,
    (norm_le_of_dvd hn (dvd_mul_right a b)).trans hs.2.2⟩,
    ⟨hs.2.1.of_mul_right,(norm_le_of_dvd hn (dvd_mul_left b a)).trans hs.2.2⟩⟩

lemma stopped_matrix_side_support (P Q : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hQ : ∀ b ∈ Q, primary b)
    (α β K : Eisenstein → ℂ) (X : ℝ) :
    (∑ a ∈ P, ∑ b ∈ Q, α a*β b*
      (if a*b ∈ centralProductEnvelope X then K (a*b) else 0)) =
    ∑ a ∈ stoppedFactorSupport P X, ∑ b ∈ stoppedFactorSupport Q X,
      α a*β b*(if a*b ∈ centralProductEnvelope X then K (a*b) else 0) := by
  unfold stoppedFactorSupport
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hsa : Squarefree a ∧ norm a ≤ Real.exp primeProductWeights.radius*X
  · rw [ite_eq_left hsa]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hsb : Squarefree b ∧ norm b ≤ Real.exp primeProductWeights.radius*X
    · rw [ite_eq_left hsb]
    · have hz : a*b ∉ centralProductEnvelope X :=
        fun hab => hsb (centralProduct_factor_support (hP a ha) (hQ b hb) hab).2
      simp only [ite_eq_right hsb,ite_eq_right hz,mul_zero]
  · rw [ite_eq_right hsa]
    apply Finset.sum_eq_zero
    intro b hb
    have hz : a*b ∉ centralProductEnvelope X :=
      fun hab => hsa (centralProduct_factor_support (hP a ha) (hQ b hb) hab).1
    simp only [ite_eq_right hz,mul_zero]

lemma finite_matrix_stopped_dyads (P Q : Finset Eisenstein)
    (F : Eisenstein → Eisenstein → ℂ) :
    (∑ a ∈ P, ∑ b ∈ Q, F a b) =
      ∑ j ∈ P.image stoppedNormDyadIndex, ∑ k ∈ Q.image stoppedNormDyadIndex,
        ∑ a ∈ stoppedNormDyad P j, ∑ b ∈ stoppedNormDyad Q k, F a b := by
  rw [stoppedNormDyad_partition P]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ a ∈ stoppedNormDyad P j, ∑ k ∈ Q.image stoppedNormDyadIndex,
        ∑ b ∈ stoppedNormDyad Q k, F a b := by
      apply Finset.sum_congr rfl
      intro a _
      exact stoppedNormDyad_partition Q (F a)
    _ = _ := Finset.sum_comm

lemma stopped_matrix_dyadic (P Q : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hQ : ∀ b ∈ Q, primary b)
    (α β K : Eisenstein → ℂ) (X : ℝ) :
    (∑ a ∈ P, ∑ b ∈ Q, α a*β b*
      (if a*b ∈ centralProductEnvelope X then K (a*b) else 0)) =
      ∑ j ∈ (stoppedFactorSupport P X).image stoppedNormDyadIndex,
        ∑ k ∈ (stoppedFactorSupport Q X).image stoppedNormDyadIndex,
          ∑ a ∈ stoppedNormDyad (stoppedFactorSupport P X) j,
            ∑ b ∈ stoppedNormDyad (stoppedFactorSupport Q X) k,
              α a*β b*(if a*b ∈ centralProductEnvelope X then K (a*b) else 0) := by
  rw [stopped_matrix_side_support P Q hP hQ α β K X]
  exact finite_matrix_stopped_dyads _ _ _

lemma stoppedFactorSupport_log_count :
    ∃ D : ℝ, 0 < D ∧ ∀ (X : ℝ), 1 ≤ X → ∀ P : Finset Eisenstein,
      (((stoppedFactorSupport P X).image stoppedNormDyadIndex).card:ℝ) ≤
        D*(1+Real.log X) := by
  obtain ⟨C,hC,hcount⟩ := metaplectic_dyad_count_log_bound
  let R := primeProductWeights.radius
  refine ⟨C*(1+R),by dsimp [R]; positivity [primeProductWeights.radius_nonneg],?_⟩
  intro X hX P
  have hF : 1 ≤ Real.exp R*X :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  have hc := stoppedNormDyad_count (stoppedFactorSupport P X)
    (fun n hn => (Finset.mem_filter.mp hn).2.2)
  have hm : Nat.log 2 ⌊Real.exp R*X⌋₊+1 ≤ Nat.log 2 ⌊3*(Real.exp R*X)⌋₊+1 :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono (by nlinarith))) 1
  calc
    _ ≤ ((Nat.log 2 ⌊3*(Real.exp R*X)⌋₊+1:ℕ):ℝ) := Nat.cast_le.mpr (hc.trans hm)
    _ ≤ C*(1+Real.log (Real.exp R*X)) := hcount _ hF
    _ ≤ C*(1+R)*(1+Real.log X) := by
      rw [Real.log_mul (Real.exp_pos _).ne' (zero_lt_one.trans_le hX).ne',Real.log_exp]
      have hR : 0 ≤ R := primeProductWeights.radius_nonneg
      have hL := Real.log_nonneg hX
      calc
        _ ≤ C*((1+R)*(1+Real.log X)) := mul_le_mul_of_nonneg_left
          (by nlinarith [mul_nonneg hR hL]) hC.le
        _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedShiftedDyad
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact original-envelope sharp dyad as a smaller-envelope analytic
row, including the selected-bin and failed-prefix boundary shifts. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_shifted_sharp_dyad_to_row {ρ X F w Z Q : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X) (hXF : X ≤ F)
    (hw : 0 < w) (hZ : 2 ≤ Z) (W : ι → ℝ → ℂ) (z : ℝ)
    (j k h i : ℕ) (hk : 1 ≤ k) (early : Bool) (K : Eisenstein → ℂ)
    (hBX : stoppedNormDyadLength i ≤ X)
    (hj : geometricBinCount ρ F-geometricBinCount ρ X ≤ j)
    (hh : geometricBinCount ρ F-geometricBinCount ρ X ≤ h) :
    let β := stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun a p => W a (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k h Z Q early)
    (∑ n ∈ stoppedNormDyad
        ((primaryPairSupport (primaryElementBall F) (primaryElementBall F)).filter
          (fun n => Squarefree n ∧ norm n ≤ F)) i, β n*K n) =
      ∑ n ∈ stoppedIntervalSupport ι X (stoppedNormDyadLength i/2)
        (stoppedNormDyadLength i) 1,
        stoppedRowCoefficient X w z 0 W
          (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
            (j-(geometricBinCount ρ F-geometricBinCount ρ X)) k
            (h-(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early) n*K n := by
  dsimp only
  calc
    _ = ∑ n ∈ stoppedIntervalSupport ι X (stoppedNormDyadLength i/2)
        (stoppedNormDyadLength i) 1,
        stoppedRowCoefficient X w z 0 W
          (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k h Z Q early) n*K n :=
      stoppedBeta_sharp_dyad_to_row hρ hρ₂ hX hXF hw hZ W z j k h i hk early K hBX
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [stoppedRowCoefficient_geometric_shift_of_bounds hρ (zero_lt_one.trans_le hX)
        hXF W w z 0 Z Q j k h early n hj hh]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingBoundaryShift
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An active logarithmic boundary for a larger ambient envelope, with
roughness still measured in the original parameter X. The index shift is
chosen explicitly, so no comparison of logarithms of two scales is needed. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_stopping_active_boundary_envelope {ξ : ℝ}
    (hξ : 0 < ξ) (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ F : ℝ, X ≤ F → ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∃ h : ℕ, h < geometricBinCount ρ F ∧
        geometricBinCount ρ F-geometricBinCount ρ X ≤ h ∧
        2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower ρ F h) ∧
        ρ*geometricBinLower ρ F h ≤ (Real.log X)^(G+4) := by
  filter_upwards [eventually_stopping_active_boundary hξ G,
    eventually_gt_atTop (0:ℝ)] with X hbound hX
  intro F hXF ρ hρ hρ₂
  obtain ⟨h,hh,hlo,hhi⟩ := hbound (ρ-1) (by linarith) (by linarith)
  have hr : 1+(ρ-1) = ρ := by ring
  rw [hr] at hh hlo hhi
  have hc := geometricBinCount_mono hρ hX hXF
  refine ⟨h+(geometricBinCount ρ F-geometricBinCount ρ X),by omega,by omega,?_,?_⟩
  · simpa only [geometricBinLower_shift hρ hX hXF] using hlo
  · simpa only [geometricBinLower_shift hρ hX hXF] using hhi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingFailedStage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The failed first stage of an ordinary stop is a condition on the
selected divisor alone; this identifies it with the original prefix. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma selected_crossing_after_failed_prefix (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    {R Z Q : ℝ} (hR : 0 ≤ R) {h j : ℕ} {t : Finset Eisenstein}
    (ht : t ⊆ primeBin s bin j)
    (hfailed : R*primeSurrogate (primeBinPrefix s bin h) bin ell < Q)
    (hQZ : Q ≤ Z)
    (hhit : Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) : h ≤ j := by
  by_contra hhj
  have hjh : j < h := by omega
  have hsub : stoppingSelected s bin j t ⊆ primeBinPrefix s bin h := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨stoppingSelected_subset ht hp,
      (stoppingSelected_bins_le ht hp).trans_lt hjh⟩
  have hsur : primeSurrogate (stoppingSelected s bin j t) bin ell ≤
      primeSurrogate (primeBinPrefix s bin h) bin ell := by
    exact Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun p _ => zero_le_one.trans (hell (bin p)))
      (fun p _ _ => hell (bin p))
  have hle := hhit.trans (mul_le_mul_of_nonneg_left hsur hR)
  exact (not_lt_of_ge hle) (hfailed.trans_le hQZ)

lemma stoppedSideTest_selected_failed_prefix (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) (bin : Eisenstein → ℕ) (ell : ℕ → ℝ)
    {h j k : ℕ} (hhj : h ≤ j) {t : Finset Eisenstein}
    (ht : t ⊆ primeBin s bin j) (Z Q : ℝ) (r : Eisenstein) :
    stoppedSideTest bin ell j k h Z Q false r (∏ p ∈ stoppingSelected s bin j t, p) ↔
      stoppingSideTest bin ell j k Z r (∏ p ∈ stoppingSelected s bin j t, p) ∧
        norm r*primeSurrogate (primeBinPrefix s bin h) bin ell < Q := by
  have hp : ∀ p ∈ stoppingSelected s bin j t, primaryPrime p :=
    fun p hp => hs p (stoppingSelected_subset ht hp)
  have hprefix : primeBinPrefix
      (primaryPrimeFactors (∏ p ∈ stoppingSelected s bin j t, p)) bin h =
      primeBinPrefix s bin h := by
    rw [primaryPrimeFactors_finset_prod _ hp]
    exact stoppingSelected_earlier_prefix hhj ht
  simp only [stoppedSideTest,Bool.false_eq_true,false_or,hprefix]

/-- On an original term which failed the first threshold, every later
crossing automatically satisfies the selected-side failure predicate. -/
lemma stoppedSideTest_selected_of_failed_prefix (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) (bin : Eisenstein → ℕ) (ell : ℕ → ℝ)
    (hell : ∀ j, 1 ≤ ell j) {h j k : ℕ} {t : Finset Eisenstein}
    (ht : t ⊆ primeBin s bin j) (Z Q : ℝ) (r : Eisenstein)
    (hfailed : norm r*primeSurrogate (primeBinPrefix s bin h) bin ell < Q)
    (hQZ : Q ≤ Z) :
    stoppedSideTest bin ell j k h Z Q false r (∏ p ∈ stoppingSelected s bin j t, p) ↔
      stoppingSideTest bin ell j k Z r (∏ p ∈ stoppingSelected s bin j t, p) := by
  constructor
  · exact And.left
  · intro hstop
    have hp : ∀ p ∈ stoppingSelected s bin j t, primaryPrime p :=
      fun p hp => hs p (stoppingSelected_subset ht hp)
    have htest : stoppingPrimeSetTest (stoppingSelected s bin j t) bin ell j k Z r := by
      simpa only [stoppingSideTest,primaryPrimeFactors_finset_prod _ hp] using hstop
    have hhj := selected_crossing_after_failed_prefix s bin ell hell (norm_nonneg r)
      ht hfailed hQZ htest.2.2.2
    exact (stoppedSideTest_selected_failed_prefix s hs bin ell hhj ht Z Q r).mpr
      ⟨hstop,hfailed⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingFailedPair
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The late-stage failure condition is exactly a predicate on the
selected divisor, even before restricting the original support. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma stoppedSideTest_late_boundary (bin : Eisenstein → ℕ) (ell : ℕ → ℝ)
    {j k h : ℕ} {Z Q : ℝ} (hQZ : Q ≤ Z) {r d : Eisenstein}
    (hs : stoppedSideTest bin ell j k h Z Q false r d) : h ≤ j := by
  have hstop : stoppingSideTest bin ell j k Z r d := hs.1
  have hfailed : norm r*primeSurrogate
      (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell < Q := by
    simpa only [Bool.false_eq_true, false_or] using hs.2
  by_contra hh
  have hjh : j < h := by omega
  have hp : primeBinPrefix (primaryPrimeFactors d) bin h = primaryPrimeFactors d := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact (hstop.1 p hp).trans_lt hjh
  rw [hp] at hfailed
  exact (not_lt_of_ge (hQZ.trans hstop.2.2.2)) hfailed

theorem stoppedSideTest_failed_pair_iff {d e r : Eisenstein}
    (hd : primary d) (he : primary e) (hs : Squarefree (d*e))
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    (j k l h : ℕ) (Z Q : ℝ) (hQZ : Q ≤ Z)
    (hrem : stoppingRemainingTest bin j l e) :
    stoppedSideTest bin ell j k h Z Q false r d ↔
      stoppingSideTest bin ell j k Z r d ∧
        norm r*primeSurrogate (primeBinPrefix (primaryPrimeFactors (d*e)) bin h)
          bin ell < Q := by
  constructor
  · intro hlate
    have hstop : stoppingSideTest bin ell j k Z r d := hlate.1
    have hhj := stoppedSideTest_late_boundary bin ell hQZ hlate
    obtain ⟨t,ht,hprod,_,_,_⟩ :=
      stopping_pair_reconstruction hd he hs bin ell j k l Z hstop hrem
    have hp : ∀ p ∈ primaryPrimeFactors (d*e), primaryPrime p :=
      fun p hp => (primaryPrimeFactor_spec (primary_mul hd he) hp).1
    have hf := stoppedSideTest_selected_failed_prefix (primaryPrimeFactors (d*e))
      hp bin ell (h := h) (j := j) (k := k) hhj (Finset.mem_powersetCard.mp ht).1 Z Q r
    rw [hprod] at hf
    exact hf.mp hlate
  · rintro ⟨hstop,hfailed⟩
    obtain ⟨t,ht,hprod,_,_,_⟩ :=
      stopping_pair_reconstruction hd he hs bin ell j k l Z hstop hrem
    have hp : ∀ p ∈ primaryPrimeFactors (d*e), primaryPrime p :=
      fun p hp => (primaryPrimeFactor_spec (primary_mul hd he) hp).1
    have hf := stoppedSideTest_selected_of_failed_prefix (primaryPrimeFactors (d*e))
      hp bin ell hell (h := h) (j := j) (k := k) (Finset.mem_powersetCard.mp ht).1 Z Q r hfailed hQZ
    rw [hprod] at hf
    exact hf.mpr hstop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingPrefixCrossing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact location of the first crossing relative to a bin boundary.
This connects the manuscript's high-bin stage to the actual stopping
labels, without imposing the boundary condition on the other variable. -/
noncomputable section
namespace CubicFirstMoment

lemma selected_crossing_before_prefix_iff (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    {R Z : ℝ} (hR : 0 ≤ R) {j k h : ℕ} {t : Finset Eisenstein}
    (ht : t ∈ (primeBin s bin j).powersetCard k) (hk : 1 ≤ k)
    (hprev : R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z)
    (hhit : Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) :
    j < h ↔ Z ≤ R*primeSurrogate (primeBinPrefix s bin h) bin ell := by
  have hc := selected_crossing_implies_bin_crossing s bin ell hell hR ht hk hprev hhit
  have hm := prime_prefix_monotone s bin ell hell hR
  constructor
  · intro hj
    exact hc.2.trans (hm (by omega : j+1 ≤ h))
  · intro hh
    by_contra hn
    have hle := hh.trans (hm (by omega : h ≤ j))
    exact (not_lt_of_ge hle) hc.1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingTwoStage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact two-stage stopping, first above a bin boundary and then after
failure of that high-prime stage. The original kernel and inverse
binomial coefficients remain unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


lemma geometricStoppedElement_eq_labels (ρ X R Z : ℝ) (ψ : ℝ → ℝ) (w : ℝ)
    (K : Eisenstein → ℂ) (n : Eisenstein) :
    geometricStoppedElement ρ X R Z ψ w K n =
      ∑ q ∈ stoppingLabelBox ρ X, geometricStoppingLabel ρ X R Z ψ w K n q := rfl

lemma geometricStoppingLabel_zero_boundary {ρ X R Z : ℝ} (hρ : 1 ≤ ρ) (hR : 0 ≤ R)
    (h : ℕ) (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) (n : Eisenstein)
    {q : ℕ × ℕ × ℕ} (hq : q ∈ stoppingLabelBox ρ X)
    (hmiss : ¬ (q.1 < h ↔ Z ≤ R*primeSurrogate
      (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X))) :
    geometricStoppingLabel ρ X R Z ψ w K n q = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  apply ite_eq_right
  intro hc
  exact hmiss (selected_crossing_before_prefix_iff (primaryPrimeFactors n)
    (geometricPrimeBin ρ X) (geometricBinLower ρ X)
    (fun j => one_le_pow₀ hρ) hR ht (Finset.mem_filter.mp hq).2 hc.2.1 hc.2.2)

theorem geometricHighStoppedElement_exact {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) (hnorm : norm n ≤ X) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (h : ℕ) (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    geometricHighStoppedElement ρ X R Z h ψ w K n =
      if Z ≤ R*primeSurrogate
        (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X) then
          cutoffMoebius ψ w n*K n else 0 := by
  by_cases hh : Z ≤ R*primeSurrogate
      (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X)
  · rw [ite_eq_left hh]
    have he : geometricHighStoppedElement ρ X R Z h ψ w K n =
        geometricStoppedElement ρ X R Z ψ w K n := by
      rw [geometricStoppedElement_eq_labels]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q hq hnot
      apply geometricStoppingLabel_zero_boundary hρ.le hR.le h ψ w K n hq
      intro hc
      exact hnot (Finset.mem_filter.mpr ⟨hq,hc.mpr hh⟩)
    rw [he,geometricStoppedElement_exact hn hs hρ hρ₂ hX hnorm hR hstart]
    apply ite_eq_left
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hR.le
    exact Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
      (fun p _ => zero_le_one.trans (one_le_pow₀ hρ.le))
      (fun p _ _ => one_le_pow₀ hρ.le)
  · rw [ite_eq_right hh]
    apply Finset.sum_eq_zero
    intro q hq
    obtain ⟨hq,hj⟩ := Finset.mem_filter.mp hq
    apply geometricStoppingLabel_zero_boundary hρ.le hR.le h ψ w K n hq
    intro hc
    exact hh (hc.mp hj)

/-- Exact ordinary two-stage decomposition before any estimate. The
late term carries the failed-prefix condition on the selected divisor. -/
theorem two_stage_stopping_split {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) (hnorm : norm n ≤ X) {R Q Z : ℝ} (hR : 0 < R)
    (hstart : R < Q) (hQZ : Q ≤ Z) (h : ℕ)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    cutoffMoebius ψ w n*K n =
      (if R*primeSurrogate
          (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q ∧
        R*primeSurrogate (primaryPrimeFactors n)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z then
        cutoffMoebius ψ w n*K n else 0) +
      geometricHighStoppedElement ρ X R Q h ψ w K n +
      (if R*primeSurrogate
          (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q then
        geometricStoppedElement ρ X R Z ψ w K n else 0) := by
  rw [geometricHighStoppedElement_exact hn hs hρ hρ₂ hX hnorm hR hstart,
    geometricStoppedElement_exact hn hs hρ hρ₂ hX hnorm hR (hstart.trans_le hQZ)]
  by_cases hh : R*primeSurrogate
      (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q
  · have hnh : ¬ Q ≤ R*primeSurrogate
        (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X) := not_le.mpr hh
    by_cases hz : Z ≤ R*primeSurrogate (primaryPrimeFactors n)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)
    · simp only [hh,hnh,hz,not_lt_of_ge hz,true_and,ite_true, if_true,ite_false, if_false,zero_add,add_zero]
    · simp only [hh,hnh,hz,lt_of_not_ge hz,true_and,ite_true, if_true,ite_false, if_false,add_zero]
  · have hh' := le_of_not_gt hh
    simp only [hh,hh',false_and,ite_true, if_true,ite_false, if_false,zero_add,add_zero]

/-- The literal finite rough-Moebius sum has the same two-stage split,
with the product kernel unchanged in all three terms. -/
theorem finite_two_stage_stopping_split (S : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {R Q Z : ℝ} (hR : 0 < R) (hstart : R < Q) (hQZ : Q ≤ Z)
    (h : ℕ) (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, cutoffMoebius ψ w n*K n) =
      (∑ n ∈ S with R*primeSurrogate
          (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q ∧
        R*primeSurrogate (primaryPrimeFactors n)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
        cutoffMoebius ψ w n*K n) +
      (∑ n ∈ S, geometricHighStoppedElement ρ X R Q h ψ w K n) +
      ∑ n ∈ S with R*primeSurrogate
          (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q,
        geometricStoppedElement ρ X R Z ψ w K n := by
  simp only [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact two_stage_stopping_split (hS n hn).1 (hS n hn).2.1 hρ hρ₂ hX
    (hS n hn).2.2 hR hstart hQZ h ψ w K

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingLabelCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact primary-pair collection on an arbitrary finite stopping-label
set. No end-crossing premise is needed for this fixed-label identity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem geometric_stopping_label_collection (S : Finset Eisenstein)
    {X : ℝ} (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (ρ Z : ℝ) (r : Eisenstein) (I : Finset (ℕ × ℕ × ℕ))
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, ∑ q ∈ I, geometricStoppingLabel ρ X (norm r) Z ψ w K n q) =
      ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if d*e ∈ S then
            (if stoppingSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 Z r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (d*e) else 0)
          else 0 := by
  let bin := geometricPrimeBin ρ X
  let ell := geometricBinLower ρ X
  let F := fun (q : ℕ × ℕ × ℕ) (n : Eisenstein) =>
    ∑ t ∈ (primeBin (primaryPrimeFactors n) bin q.1).powersetCard q.2.1,
      if (primeBin (stoppingRemainder (primaryPrimeFactors n) bin q.1 t) bin q.1).card = q.2.2 ∧
          (norm r*primeSurrogate (stoppingSelected (primaryPrimeFactors n) bin q.1 t) bin ell/
              ell q.1 < Z ∧
            Z ≤ norm r*primeSurrogate (stoppingSelected (primaryPrimeFactors n) bin q.1 t) bin ell) then
        cutoffMoebius ψ w (∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin q.1 t, p)*
          cutoffMoebius ψ w (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin q.1 t, p)*
          K ((∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin q.1 t, p)*
            (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin q.1 t, p))
      else 0
  have hF (q : ℕ × ℕ × ℕ) (n : Eisenstein) :
      geometricStoppingLabel ρ X (norm r) Z ψ w K n q =
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ * F q n := by
    dsimp only [geometricStoppingLabel,F,bin,ell]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _ht
    split_ifs <;> ring
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  simp_rw [hF]
  rw [←Finset.mul_sum]
  congr 1
  let G := fun d e : Eisenstein =>
    if stoppingSideTest bin ell q.1 q.2.1 Z r d ∧
        stoppingRemainingTest bin q.1 q.2.2 e then
      cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (d*e) else 0
  calc
    _ = ∑ n ∈ S,
        ∑ p ∈ ((primaryElementBall X).product (primaryElementBall X)).filter
            (fun p => p.1*p.2 = n), G p.1 p.2 := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hnp,hns,hnX⟩ := hS n hn
      exact stopping_primary_pair_sum hnp hns hnX bin ell q.1 q.2.1 q.2.2 Z r ψ w
        (fun d e => K (d*e))
    _ = _ := primary_pair_fiber_support S X G

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingLabelWeights
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit logarithmic aggregation costs for the actual finite stopping
labels on a fixed dilation of X. The inverse-binomial scalar is retained,
and the bounds apply to every early or late subset of labels. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stoppingLabelBox_card_fixed {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ F : ℝ, 1 ≤ F →
      ((stoppingLabelBox ρ F).card:ℝ) ≤ K*(1+Real.log F)^3 := by
  obtain ⟨C,hC,hbin⟩ := geometricBinCount_log_bound hρ
  let D : ℝ := (Real.log 2)⁻¹+2
  have hlog2 : 0 < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos (by norm_num))
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨C*D^2,by positivity,?_⟩
  intro F hF
  have hL := Real.log_nonneg hF
  have hf := stoppingFactorLimit_bound hF
  have hfac : ((stoppingFactorLimit F+1:ℕ):ℝ) ≤ D*(1+Real.log F) := by
    simp only [Nat.cast_add,Nat.cast_one]
    dsimp [D]
    nlinarith
  have hcard : ((stoppingLabelBox ρ F).card:ℝ) ≤
      (geometricBinCount ρ F:ℝ)*((stoppingFactorLimit F+1:ℕ):ℝ)^2 := by
    exact_mod_cast stoppingLabelBox_card ρ F
  calc
    _ ≤ (C*(1+Real.log F))*(D*(1+Real.log F))^2 :=
      hcard.trans (mul_le_mul (hbin F hF)
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hfac 2) (sq_nonneg _) (by positivity))
    _ = (C*D^2)*(1+Real.log F)^3 := by ring

theorem stoppingLabelBox_card_dilated {ρ c : ℝ} (hρ : 1 < ρ) (hc : 1 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      ((stoppingLabelBox ρ (c*X)).card:ℝ) ≤ K*(1+Real.log X)^3 := by
  obtain ⟨C,hC,hbound⟩ := stoppingLabelBox_card_fixed hρ
  have hclog := Real.log_nonneg hc
  have hcp : 0 < c := zero_lt_one.trans_le hc
  refine ⟨C*(1+Real.log c)^3,by positivity,?_⟩
  intro X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hlogX := Real.log_nonneg hX
  have hF : 1 ≤ c*X := one_le_mul_of_one_le_of_one_le hc hX
  have hL : 1+Real.log (c*X) ≤ (1+Real.log c)*(1+Real.log X) := by
    rw [Real.log_mul hcp.ne' hXp.ne']
    nlinarith [mul_nonneg hclog hlogX]
  calc
    _ ≤ C*(1+Real.log (c*X))^3 := hbound _ hF
    _ ≤ C*((1+Real.log c)*(1+Real.log X))^3 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity [Real.log_nonneg hF]) hL 3) hC.le
    _ = (C*(1+Real.log c)^3)*(1+Real.log X)^3 := by ring

/-- One constant covers arbitrary early/late label subsets and every
family of piece bounds. In particular, no sign is discarded from a piece. -/
theorem stopping_label_weighted_sum_dilated {ρ c : ℝ} (hρ : 1 < ρ) (hc : 1 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ I : Finset (ℕ × ℕ × ℕ), I ⊆ stoppingLabelBox ρ (c*X) →
      (I.card:ℝ) ≤ K*(1+Real.log X)^3 ∧
      ∀ (f : (ℕ × ℕ × ℕ) → ℂ) (M : ℝ), 0 ≤ M →
        (∀ q ∈ I, ‖f q‖ ≤ M) →
        ‖∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*f q‖ ≤
          K*(1+Real.log X)^3*M := by
  obtain ⟨K,hK,hcount⟩ := stoppingLabelBox_card_dilated hρ hc
  refine ⟨K,hK,?_⟩
  intro X hX I hI
  have hcard : (I.card:ℝ) ≤ K*(1+Real.log X)^3 :=
    (Nat.cast_le.mpr (Finset.card_le_card hI)).trans (hcount X hX)
  refine ⟨hcard,?_⟩
  intro f M hM hf
  calc
    _ ≤ ∑ q ∈ I, ‖(Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*f q‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ I, M := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact (mul_le_mul (stopping_scalar_norm_le_one q.2.1 q.2.2) (hf q hq)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul M)
    _ = (I.card:ℝ)*M := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hM

/-- The low distinguished-scale restriction can only lower the number of
norm-partition indices; its exact cutoff need not be relaxed. -/
theorem stopped_norm_partition_subset_count (i : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ I : Finset (Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
        (I.card:ℝ) ≤ D*(1+Real.log X)^i := by
  obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i 0
  refine ⟨D,hD,?_⟩
  intro X hX I
  have hi : (I.card:ℝ) ≤ (Fintype.card
      (Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))):ℝ) := by
    exact_mod_cast Finset.card_le_univ I
  apply hi.trans
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_sum,Nat.add_zero,Nat.cast_pow]
    using hcount X hX

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingMatrixLabels
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent coefficient collection on any finite family of actual
stopping labels, including the high-bin first-stage labels. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stopping_matrix_collection_on_labels (I : Finset (ℕ × ℕ × ℕ)) (ρ X Z Q : ℝ) (h : ℕ) (early : Bool)
    (R D E U : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
      ∑ e ∈ E, ∑ u ∈ U, ∑ r ∈ R, ∑ d ∈ D,
        if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
              q.1 q.2.1 h Z Q early r d ∧
            stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
          v r*cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0) =
    ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
      ∑ a ∈ primaryPairSupport E U, ∑ b ∈ primaryPairSupport R D,
        stoppedAlpha E U ψ w
            (stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2) a *
          stoppedBeta R D v ψ w
            (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
              q.1 q.2.1 h Z Q early) b * K (a*b) := by
  apply Finset.sum_congr rfl
  intro q _hq
  congr 1
  rw [stopped_coefficients_sum]
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro e _he
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro r _hr
  apply Finset.sum_congr rfl
  intro d _hd
  have hmul : (e*u)*(r*d) = r*(d*e)*u := by ring
  rw [hmul]
  by_cases hs : stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      q.1 q.2.1 h Z Q early r d
  · by_cases he : stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e
    · simp only [hs,he,and_self,ite_true, if_true]
      ring
    · simp only [hs,he,and_false,false_and,ite_false, if_false]
  · simp only [hs,and_false,false_and,ite_false, if_false]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingStageCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of both stages, including terms which never reach
the late threshold. The original support remains inside each pair sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem geometric_high_stopping_support_collection (S : Finset Eisenstein)
    {X : ℝ} (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (ρ Q : ℝ) (r : Eisenstein) (h : ℕ)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, geometricHighStoppedElement ρ X (norm r) Q h ψ w K n) =
      ∑ q ∈ (stoppingLabelBox ρ X).filter (fun q => q.1 < h),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
            if d*e ∈ S then
              (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                    q.1 q.2.1 h Q Q true r d ∧
                  stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
                cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (d*e) else 0)
            else 0 := by
  simpa only [geometricHighStoppedElement,stoppedSideTest,true_or,and_true] using
    geometric_stopping_label_collection S hS ρ Q r
      ((stoppingLabelBox ρ X).filter (fun q => q.1 < h)) ψ w K

theorem geometric_late_stopping_support_collection (S : Finset Eisenstein)
    {X : ℝ} (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (r : Eisenstein) (h : ℕ)
    {Z Q : ℝ} (hQZ : Q ≤ Z)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S with norm r*primeSurrogate
        (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q,
      geometricStoppedElement ρ X (norm r) Z ψ w K n) =
      ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if d*e ∈ S then
            (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q false r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (d*e) else 0)
          else 0 := by
  let T := S.filter (fun n => norm r*primeSurrogate
    (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
    (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q)
  have hT : ∀ n ∈ T, primary n ∧ Squarefree n ∧ norm n ≤ X :=
    fun n hn => hS n (Finset.mem_filter.mp hn).1
  change (∑ n ∈ T, geometricStoppedElement ρ X (norm r) Z ψ w K n) = _
  simp_rw [geometricStoppedElement_eq_labels]
  rw [geometric_stopping_label_collection T hT ρ Z r (stoppingLabelBox ρ X) ψ w K]
  apply Finset.sum_congr rfl
  intro q _hq
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  by_cases hde : d*e ∈ S
  · simp only [T,Finset.mem_filter,hde,true_and,ite_true, if_true]
    by_cases hrem : stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e
    · rw [stoppedSideTest_failed_pair_iff (mem_primaryElementBall.mp hd).1
        (mem_primaryElementBall.mp he).1 (hS (d*e) hde).2.1
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        (fun j => one_le_pow₀ hρ) q.1 q.2.1 q.2.2 h Z Q hQZ hrem]
      by_cases hstop : stoppingSideTest (geometricPrimeBin ρ X)
          (geometricBinLower ρ X) q.1 q.2.1 Z r d
      · simp only [hrem,hstop,true_and,and_true,ite_true, if_true]
      · simp only [hrem,hstop,false_and,and_true,ite_false, if_false,ite_self]
    · simp only [hrem,and_false,ite_false, if_false,ite_self]
  · simp only [T,Finset.mem_filter,hde,false_and,ite_false, if_false]

theorem finite_two_stage_stopping_pair_split (S : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {r : Eisenstein} (hr : primary r) {Q Z : ℝ}
    (hstart : norm r < Q) (hQZ : Q ≤ Z) (h : ℕ)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, cutoffMoebius ψ w n*K n) =
      (∑ n ∈ S with norm r*primeSurrogate
          (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q ∧
        norm r*primeSurrogate (primaryPrimeFactors n)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
        cutoffMoebius ψ w n*K n) +
      (∑ q ∈ (stoppingLabelBox ρ X).filter (fun q => q.1 < h),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
            if d*e ∈ S then
              (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                    q.1 q.2.1 h Q Q true r d ∧
                  stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
                cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (d*e) else 0)
            else 0) +
      ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if d*e ∈ S then
            (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q false r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (d*e) else 0)
          else 0 := by
  rw [finite_two_stage_stopping_split S hρ hρ₂ hX hS (norm_pos_of_ne_zero (primary_ne_zero hr)) hstart hQZ h ψ w K,
    geometric_high_stopping_support_collection S hS ρ Q r h ψ w K,
    geometric_late_stopping_support_collection S hS hρ.le r h hQZ ψ w K]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingSliceTwoStage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-stage collection on the actual product slices. Multiplication
only changes the location of the original support predicate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stopping_slice_pair_rows (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (r u : Eisenstein) (I : Finset (ℕ × ℕ × ℕ))
    (F : (ℕ × ℕ × ℕ) → Eisenstein → Eisenstein → ℂ) :
    (∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
      ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
        if d*e ∈ primaryProductSlice S X (r*u) then F q d e else 0) =
      ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if r*(d*e)*u ∈ S then F q d e else 0 := by
  apply Finset.sum_congr rfl
  intro q _hq
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hm : primary (d*e) :=
    primary_mul (mem_primaryElementBall.mp hd).1 (mem_primaryElementBall.mp he).1
  have heq : (r*u)*(d*e) = r*(d*e)*u := by ring
  simp only [mem_primaryProductSlice_iff S X hS (r*u) hm,heq]

theorem stopping_product_slice_two_stage (S : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {r : Eisenstein} (hr : primary r) (u : Eisenstein) {Q Z : ℝ}
    (hstart : norm r < Q) (hQZ : Q ≤ Z) (h : ℕ)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ m ∈ primaryProductSlice S X (r*u), cutoffMoebius ψ w m*K (r*(m*u))) =
      (∑ m ∈ primaryProductSlice S X (r*u) with
          norm r*primeSurrogate
            (primeBinPrefix (primaryPrimeFactors m) (geometricPrimeBin ρ X) h)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q ∧
          norm r*primeSurrogate (primaryPrimeFactors m)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
        cutoffMoebius ψ w m*K (r*(m*u))) +
      (∑ q ∈ (stoppingLabelBox ρ X).filter (fun q => q.1 < h),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
            if r*(d*e)*u ∈ S then
              (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                    q.1 q.2.1 h Q Q true r d ∧
                  stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
                cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0)
            else 0) +
      ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if r*(d*e)*u ∈ S then
            (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q false r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0)
          else 0 := by
  rw [finite_two_stage_stopping_pair_split (primaryProductSlice S X (r*u))
    hρ hρ₂ hX (primaryProductSlice_support S X hS (r*u)) hr hstart hQZ h ψ w
    (fun m => K (r*(m*u)))]
  have hrows (I : Finset (ℕ × ℕ × ℕ)) (T : ℝ) (early : Bool) :
      (∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if d*e ∈ primaryProductSlice S X (r*u) then
            (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h T Q early r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*((d*e)*u)) else 0)
          else 0) =
        ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
            if r*(d*e)*u ∈ S then
              (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                    q.1 q.2.1 h T Q early r d ∧
                  stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
                cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0)
            else 0 := by
    simpa only [mul_assoc] using stopping_slice_pair_rows S X hS r u I
      (fun q d e => if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          q.1 q.2.1 h T Q early r d ∧
        stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
          cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*((d*e)*u)) else 0)
  rw [hrows,hrows]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughProductTwoStage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-stage rough-product decomposition in independent coefficient
form. The distinguished coefficient is arbitrary and the original sharp
product support remains inside the kernel. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma sum_four_reorder_two_stage {α β γ δ : Type*}
    (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (F : α → β → γ → δ → ℂ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, F a b c d) =
      ∑ d ∈ D, ∑ b ∈ B, ∑ a ∈ A, ∑ c ∈ C, F a b c d := by
  calc
    _ = ∑ a ∈ A, ∑ d ∈ D, ∑ b ∈ B, ∑ c ∈ C, F a b c d := by
      apply Finset.sum_congr rfl
      intro a _ha
      calc
        _ = ∑ b ∈ B, ∑ d ∈ D, ∑ c ∈ C, F a b c d := by
          apply Finset.sum_congr rfl
          intro b _hb
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _hd
      exact Finset.sum_comm

theorem rough_stopping_matrix_reindex (S R : Finset Eisenstein)
    (I : Finset (ℕ × ℕ × ℕ)) (ρ X Z Q : ℝ) (h : ℕ) (early : Bool)
    (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ r ∈ R, v r * ∑ u ∈ primaryElementBall X,
      ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if r*(d*e)*u ∈ S then
            (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q early r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0)
          else 0) =
      ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ a ∈ primaryPairSupport (primaryElementBall X) (primaryElementBall X),
          ∑ b ∈ primaryPairSupport R (primaryElementBall X),
            stoppedAlpha (primaryElementBall X) (primaryElementBall X) ψ w
                (stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2) a *
              stoppedBeta R (primaryElementBall X) v ψ w
                (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q early) b *
              (if a*b ∈ S then K (a*b) else 0) := by
  conv_lhs =>
    arg 2
    ext r
    arg 2
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum]
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [←stopping_matrix_collection_on_labels I ρ X Z Q h early R
    (primaryElementBall X) (primaryElementBall X) (primaryElementBall X)
    v ψ w (fun n => if n ∈ S then K n else 0)]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [sum_four_reorder_two_stage R (primaryElementBall X) (primaryElementBall X)
    (primaryElementBall X)]
  apply Finset.sum_congr rfl
  intro e _he
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro r _hr
  apply Finset.sum_congr rfl
  intro d _hd
  split_ifs <;> ring

theorem roughProduct_matrix_two_stage (S R : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (hR : ∀ r ∈ R, primary r) {Q Z : ℝ}
    (v : Eisenstein → ℂ) (hstart : ∀ r ∈ R, v r ≠ 0 → norm r < Q) (hQZ : Q ≤ Z)
    (h : ℕ) (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ r ∈ R, v r *
      ∑ n ∈ primaryProductSlice S X r, (roughProduct ψ w n:ℂ)*K (r*n)) =
      (∑ r ∈ R, v r * ∑ u ∈ primaryElementBall X,
        ∑ m ∈ primaryProductSlice S X (r*u) with
          norm r*primeSurrogate
            (primeBinPrefix (primaryPrimeFactors m) (geometricPrimeBin ρ X) h)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q ∧
          norm r*primeSurrogate (primaryPrimeFactors m)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
          cutoffMoebius ψ w m*K (r*(m*u))) +
      (∑ q ∈ (stoppingLabelBox ρ X).filter (fun q => q.1 < h),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ a ∈ primaryPairSupport (primaryElementBall X) (primaryElementBall X),
            ∑ b ∈ primaryPairSupport R (primaryElementBall X),
              stoppedAlpha (primaryElementBall X) (primaryElementBall X) ψ w
                  (stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2) a *
                stoppedBeta R (primaryElementBall X) v ψ w
                  (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                    q.1 q.2.1 h Q Q true) b *
                (if a*b ∈ S then K (a*b) else 0)) +
      ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ a ∈ primaryPairSupport (primaryElementBall X) (primaryElementBall X),
          ∑ b ∈ primaryPairSupport R (primaryElementBall X),
            stoppedAlpha (primaryElementBall X) (primaryElementBall X) ψ w
                (stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2) a *
              stoppedBeta R (primaryElementBall X) v ψ w
                (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q false) b *
              (if a*b ∈ S then K (a*b) else 0) := by
  simp_rw [roughProduct_slice_pairs S X hS]
  rw [←rough_stopping_matrix_reindex S R _ ρ X Q Q h true v ψ w K,
    ←rough_stopping_matrix_reindex S R _ ρ X Z Q h false v ψ w K]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hv : v r = 0
  · simp only [hv,zero_mul,zero_add]
  rw [←mul_add,←mul_add]
  congr 1
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _hu
  exact stopping_product_slice_two_stage S hρ hρ₂ hX hS
    (hR r hr) u (hstart r hr hv) hQZ h ψ w K

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStopping
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual low scale-first rows satisfy the two-stage stopping
identity. The no-stop prefix test and both independent stopped matrices
are retained exactly. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem distinguishedScaleRow_two_stage (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∀ (Ct : ℕ) (H : ℝ) (h : ℕ)
        (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      distinguishedScaleLength k < X^(69/200:ℝ) →
      distinguishedScaleRow i 0 ξ Ct H X k =
        restrictedNoStopCenteredValue (centralPrimaryFactors X)
          (distinguishedScaleCoefficient i ξ X k) primeDetectorCutoff (X^ξ) ρ
          (X^(38/100:ℝ)) (Real.exp primeProductWeights.radius) 0 primeProductEnvelope
          H ((1+Real.log X)^Ct) X X
          (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h) +
        distinguishedScaleStoppedRow i ρ ξ Ct H X h true k +
        distinguishedScaleStoppedRow i ρ ξ Ct H X h false k := by
  filter_upwards [eventually_distinguishedScale_low_initial i ξ,
    eventually_ge_atTop (1:ℝ)] with X hstart hX
  intro ρ hρ hρ₂ Ct H h k hk
  have hF : 1 ≤ Real.exp primeProductWeights.radius*X :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  have he := roughProduct_matrix_two_stage (centralProductEnvelope X) (centralPrimaryFactors X)
    hρ hρ₂ hF (fun _ hn => centralProductEnvelope_spec hn)
    (fun _ hr => (mem_primaryElementBall.mp hr).1)
    (distinguishedScaleCoefficient i ξ X k) (fun r _ hr => hstart k hk r hr)
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (9/25:ℝ) ≤ 38/100))
    h primeDetectorCutoff (X^ξ)
    (centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X)
  unfold distinguishedScaleRow
  rw [he]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · unfold restrictedNoStopCenteredValue stoppingFailedPrefix
      simp only [centralProductEnvelope]
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hp : norm r*primeSurrogate
          (primeBinPrefix (primaryPrimeFactors d)
            (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X)) h)
          (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
          (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) < X^(9/25:ℝ)
      <;> by_cases hq : norm r*primeSurrogate (primaryPrimeFactors d)
          (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
          (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) < X^(38/100:ℝ)
      all_goals simp only [hp,hq,and_self,and_true,and_false,ite_true, if_true,ite_false, if_false]
    · rfl
  · rfl

theorem distinguishedLowScaleRows_two_stage (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∀ (Ct : ℕ) (H : ℝ) (h : ℕ),
      distinguishedLowScaleRows i 0 ξ Ct H X =
        distinguishedScaleNoStop i ρ ξ Ct H X
          (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h) +
        distinguishedScaleStopped i ρ ξ Ct H X h true +
        distinguishedScaleStopped i ρ ξ Ct H X h false := by
  filter_upwards [distinguishedScaleRow_two_stage i ξ] with X hX
  intro ρ hρ hρ₂ Ct H h
  unfold distinguishedLowScaleRows distinguishedScaleNoStop distinguishedScaleStopped
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : distinguishedScaleLength k < X^(69/200:ℝ)
  · simp only [hk,ite_true, if_true]
    exact hX ρ hρ hρ₂ Ct H h k hk
  · simp only [hk,ite_false, if_false,zero_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact dyadic form of each original stopped row. The inverse
binomial scalar and both stopping predicates are retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem distinguishedScaleStoppedRow_dyads (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    distinguishedScaleStoppedRow i ρ ξ Ct H X h early d =
      ∑ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
          (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ j ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
            ∑ k ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
              distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k := by
  unfold distinguishedScaleStoppedRow
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  exact stopped_matrix_dyadic _ _
    (fun a ha => primaryPairSupport_primary _ _
      (fun _ hn => (mem_primaryElementBall.mp hn).1)
      (fun _ hn => (mem_primaryElementBall.mp hn).1) ha)
    (fun b hb => primaryPairSupport_primary _ _
      (fun _ hn => (mem_primaryElementBall.mp hn).1)
      (fun _ hn => (mem_primaryElementBall.mp hn).1) hb)
    _ _ _ X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedAggregation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite stopping sums cost only a fixed power of log X. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_double_sum_le_card_sq {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (f : ι → κ → ℂ) {M : ℝ} (hf : ∀ i ∈ S, ∀ j ∈ T, ‖f i j‖ ≤ M) :
    ‖∑ i ∈ S, ∑ j ∈ T, f i j‖ ≤ (S.card:ℝ)*(T.card:ℝ)*M := by
  calc
    _ ≤ ∑ i ∈ S, ‖∑ j ∈ T, f i j‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, (T.card:ℝ)*M := by
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      simpa only [Finset.sum_const,nsmul_eq_mul] using
        Finset.sum_le_sum (s := T) (fun j hj => hf i hi j hj)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem distinguishedScaleStoppedRow_bound {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i Ct : ℕ) (ξ H X : ℝ), 1 ≤ X → ∀ (h : ℕ) (early : Bool)
      (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (M : ℝ), 0 ≤ M →
      (∀ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
        (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
        ∀ j k : ℕ, ‖distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k‖ ≤ M) →
      ‖distinguishedScaleStoppedRow i ρ ξ Ct H X h early d‖ ≤
        K*(1+Real.log X)^5*M := by
  obtain ⟨D,hD,hcount⟩ := stoppedFactorSupport_log_count
  obtain ⟨C,hC,hlabels⟩ := stopping_label_weighted_sum_dilated hρ
    (Real.one_le_exp primeProductWeights.radius_nonneg)
  refine ⟨C*D^2,by positivity,?_⟩
  intro i Ct ξ H X hX h early d M hM hpiece
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  let I := if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
    (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)
  let J := (distinguishedStoppedSide X).image stoppedNormDyadIndex
  have hI : I ⊆ stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X) := by
    dsimp [I]
    split
    · exact Finset.filter_subset _ _
    · exact Finset.Subset.refl _
  have hJ : (J.card:ℝ) ≤ D*(1+Real.log X) := hcount X hX _
  have hJ0 : 0 ≤ (J.card:ℝ) := Nat.cast_nonneg _
  have hinner (q) (hq : q ∈ I) :
      ‖∑ j ∈ J, ∑ k ∈ J, distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k‖ ≤
        D^2*(1+Real.log X)^2*M := by
    apply (norm_double_sum_le_card_sq J J _ (fun j _ k _ => hpiece q hq j k)).trans
    have hs := mul_le_mul hJ hJ hJ0 (by positivity : 0 ≤ D*(1+Real.log X))
    calc
      _ ≤ (D*(1+Real.log X))*(D*(1+Real.log X))*M := mul_le_mul_of_nonneg_right hs hM
      _ = _ := by ring
  rw [distinguishedScaleStoppedRow_dyads]
  have hh := (hlabels X hX I hI).2 _ (D^2*(1+Real.log X)^2*M)
    (by positivity) hinner
  apply hh.trans_eq
  ring

theorem distinguishedScaleStopped_bound (i : ℕ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ct : ℕ) (ξ H X : ℝ), 1 ≤ X → ∀ (h : ℕ) (early : Bool)
      (M : ℝ), 0 ≤ M →
      (∀ (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ),
        q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
          (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)) →
        ∀ j k : ℕ, ‖distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k‖ ≤ M) →
      ‖distinguishedScaleStopped i ρ ξ Ct H X h early‖ ≤
        K*(1+Real.log X)^(i+5)*M := by
  obtain ⟨C,hC,hrow⟩ := distinguishedScaleStoppedRow_bound hρ
  obtain ⟨D,hD,hcount⟩ := stopped_norm_partition_subset_count i
  refine ⟨D*C,by positivity,?_⟩
  intro Ct ξ H X hX h early M hM hpiece
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  let S := (Finset.univ : Finset (Fin i → Fin
    (normPartitionCount (Real.exp primeProductWeights.radius*X))))
  have hb (d) : ‖(if distinguishedScaleLength d < X^(69/200:ℝ) then
      distinguishedScaleStoppedRow i ρ ξ Ct H X h early d else 0)‖ ≤
      C*(1+Real.log X)^5*M := by
    split_ifs
    · exact hrow i Ct ξ H X hX h early d M hM (hpiece d)
    · rw [norm_zero]; positivity
  calc
    _ ≤ ∑ d ∈ S, C*(1+Real.log X)^5*M := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun d _ => hb d)
    _ = (S.card:ℝ)*(C*(1+Real.log X)^5*M) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (D*(1+Real.log X)^i)*(C*(1+Real.log X)^5*M) :=
      mul_le_mul_of_nonneg_right (hcount X hX S) (by positivity)
    _ = _ := by rw [pow_add]; ring

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

lemma distinguishedStoppedBeta_as_weights (i : ℕ) (ρ ξ X : ℝ) (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) :
    distinguishedStoppedBeta i ρ ξ X h early d q =
      stoppedBeta (centralPrimaryFactors X) (centralPrimaryFactors X)
        (distinguishedTupleCoefficient
          (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
          (fun a p => distinguishedStoppingWeights d a (norm p))
          primeDetectorCutoff (X^ξ) (X^(2/5:ℝ))) primeDetectorCutoff (X^ξ)
        (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
          (geometricBinLower ρ (Real.exp primeProductWeights.radius*X))
          q.1 q.2.1 h (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) (X^(9/25:ℝ)) early) := by
  unfold distinguishedStoppedBeta distinguishedScaleCoefficient
  have he : (fun a p => normPartitionWeight (2*norm p/(4/3:ℝ)^(d a).val)) =
      (fun a p => distinguishedStoppingWeights d a (norm p)) := by
    funext a p
    exact (distinguishedStoppingWeights_at d a p).symm
  rw [he]

lemma distinguishedStoppedDyad_witness (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ)
    (hne : distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k ≠ 0) :
    ∃ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
      ∃ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
        distinguishedStoppedBeta i ρ ξ X h early d q b ≠ 0 ∧
        centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) ≠ 0 := by
  obtain ⟨a,ha,hsum⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨b,hb,ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine ⟨a,ha,b,hb,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ht).1).2,?_⟩
  intro hz
  apply ht
  simp only [hz,ite_self,mul_zero]

theorem eventually_distinguishedStoppedDyad_geometry {ρ ξ ε : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    (hgap : ξ+ε < 1/100) :
    ∀ᶠ X : ℝ in atTop, ∀ (i Ct : ℕ) (H : ℝ) (h : ℕ) (early : Bool)
      (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (q : ℕ × ℕ × ℕ) (j k : ℕ), 1 ≤ q.2.1 →
      distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k ≠ 0 →
      X^(7/20:ℝ) ≤ stoppedNormDyadLength k ∧
      stoppedNormDyadLength k ≤ X^(39/100:ℝ) ∧
      stoppedNormDyadLength k ≤ X ∧
      X/16 ≤ (stoppedNormDyadLength j/2)*stoppedNormDyadLength k ∧
      (stoppedNormDyadLength j/2)*stoppedNormDyadLength k ≤ 16*X ∧
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ q.1 := by
  filter_upwards [eventually_two_stage_stopped_dyad_range_dilation
    (Real.exp_pos primeProductWeights.radius) hgap,eventually_ge_atTop (1:ℝ)] with X hr hX
  intro i Ct H h early d q j k hk hne
  obtain ⟨a,ha,b,hb,hβ,hK⟩ := distinguishedStoppedDyad_witness i ρ ξ Ct H X h early d q j k hne
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
  have hKR := centeredHeightKernel_norm_range 0 H _ hXp hK
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original finite dyad is the analytic interval row, with the exact
selected-bin shift and failed-prefix predicate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem distinguishedStoppedDyad_to_row (i : ℕ) {ρ ξ X : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X) (Ct : ℕ) (H : ℝ)
    (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) (hk : 1 ≤ q.2.1)
    (hZ : 2 ≤ (if early then X^(9/25:ℝ) else X^(38/100:ℝ)))
    (hBX : stoppedNormDyadLength k ≤ X)
    (hj : geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ q.1)
    (hh : geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h) :
    distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k =
      ∑ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
        ∑ b ∈ stoppedIntervalSupport (Fin i) X (stoppedNormDyadLength k/2)
          (stoppedNormDyadLength k) 1,
          distinguishedStoppedAlpha ρ ξ X q a*
            stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 (distinguishedStoppingWeights d)
              (distinguishedShiftedSideTest ρ X h early q) b*
            centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hXF : X ≤ Real.exp primeProductWeights.radius*X :=
    le_mul_of_one_le_left hXp.le (Real.one_le_exp primeProductWeights.radius_nonneg)
  unfold distinguishedStoppedDyad
  apply Finset.sum_congr rfl
  intro a ha
  have hap := (distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1).1
  calc
    _ = distinguishedStoppedAlpha ρ ξ X q a *
        ∑ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
          distinguishedStoppedBeta i ρ ξ X h early d q b*
            centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [←mul_assoc]
      congr 1
      exact centeredHeightKernel_envelope 0 primeProductEnvelope hXp
        (primeProductWeights.upper_support ()) H ((1+Real.log X)^Ct) X
        (primary_mul hap (distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1).1)
    _ = distinguishedStoppedAlpha ρ ξ X q a *
        ∑ b ∈ stoppedIntervalSupport (Fin i) X (stoppedNormDyadLength k/2)
          (stoppedNormDyadLength k) 1,
          stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 (distinguishedStoppingWeights d)
            (distinguishedShiftedSideTest ρ X h early q) b*
            centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) := by
      congr 1
      simpa only [distinguishedStoppedBeta_as_weights,distinguishedStoppedSide,
        stoppedFactorSupport,centralPrimaryFactors,distinguishedShiftedSideTest] using
        stoppedBeta_shifted_sharp_dyad_to_row hρ hρ₂ hX hXF
          (Real.rpow_pos_of_pos hXp ξ) hZ (distinguishedStoppingWeights d) (X^(2/5:ℝ))
          q.1 q.2.1 h k hk early
          (fun b => centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b))
          hBX hj hh
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralRestrictedNoStopCentral
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original no-stop branch, retaining an arbitrary extra predicate
on the two outer factors, obeys the derived central Type-I estimate. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem restricted_noStop_central_bound_actual
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) (Ct : ℕ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ K : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ 0 ≤ K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (i : γ) (R : Finset Eisenstein) (v : Eisenstein → ℂ)
        (ψ : ℝ → ℝ) (w Z Y H X₀ : ℝ) (P : Eisenstein → Eisenstein → Prop),
        2 ≤ X → 1 ≤ Real.log X → Real.exp hW.radius ≤ X →
        1 ≤ Y → (Real.exp hW.radius*X)^(κ/4)*Z ≤ Y →
        2*Y ≤ X^(51/100:ℝ) → 0 < H →
        (∀ r ∈ R, primary r) → (∀ r ∈ R, ‖v r‖ ≤ M) →
        (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
        ‖restrictedNoStopCenteredValue R v ψ w ρ Z (Real.exp hW.radius) ℓ (W i)
          H ((1+Real.log X)^Ct) X X₀ P‖ ≤
          K*(1+Real.log Y)*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := by
  obtain ⟨ρ,hρ,hρ₂,hsmall,hgeom⟩ := restricted_noStop_short_support hκ hcap
  obtain ⟨K,hK,hbound⟩ := short_outer_low_bound_actual  hW ℓ hGamma hM 1 Ct
  refine ⟨ρ,K,hρ,hρ₂,hsmall,hK,?_⟩
  have hcomp : Tendsto (fun X : ℝ => Real.exp hW.radius*X) atTop atTop :=
    tendsto_id.const_mul_atTop (Real.exp_pos _)
  filter_upwards [hcomp.eventually hgeom] with X hgeomX
  intro i R v ψ w Z Y H X₀ P hX hlog hBX hY hdist hYX hH hR hv hψ
  let F := Real.exp hW.radius*X
  let D := primaryElementBall F
  let Bsupport := primaryPairSupport R D
  let α := restrictedNoStopCoefficient R D v ψ w ρ F Z P
  have hP (b : Eisenstein) (hb : b ∈ Bsupport) : primary b :=
    primaryPairSupport_primary R D hR (fun m hm => (mem_primaryElementBall.mp hm).1) hb
  have hs (b : Eisenstein) (_hb : b ∈ Bsupport) (hne : α b ≠ 0) : norm b ≤ Y :=
    (hgeomX R v ψ w Z P b hne).le.trans hdist
  have ha (b : Eisenstein) (hb : b ∈ Bsupport) :
      ‖α b‖ ≤ M*((metaplecticPrimaryDivisors b).card:ℝ)^1 := by
    simpa only [pow_one] using restrictedNoStop_coefficient_divisor_bound R D hR hψ w ρ F Z P v hM hv (hP b hb)
  have hb := hbound (fun _ => i) Bsupport α X Y H X₀ hX hlog hBX hY hYX hH hP hs ha
  have he := restrictedNoStop_coefficient_collection (squarefreeProductEnvelope F) R v ψ w ρ F Z P
    (centeredHeightKernel ℓ (W i) H ((1+Real.log X)^Ct) X X₀)
  change ‖restrictedNoStopCenteredValue R v ψ w ρ Z (Real.exp hW.radius) ℓ (W i)
    H ((1+Real.log X)^Ct) X X₀ P‖ ≤ _
  change ‖∑ r ∈ R, v r*∑ u ∈ D,
    ∑ m ∈ primaryProductSlice (squarefreeProductEnvelope F) F (r*u) with
      norm r*primeSurrogate (primaryPrimeFactors m) (geometricPrimeBin ρ F)
        (geometricBinLower ρ F) < Z ∧ P r m,
      cutoffMoebius ψ w m*centeredHeightKernel ℓ (W i) H ((1+Real.log X)^Ct) X X₀ (r*(m*u))‖ ≤ _
  rw [he]
  exact hb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralRestrictedNoStopParameters
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform power saving for the literal no-stop term with the
first-stage predicate retained, including a growing finite norm partition. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem restricted_noStop_patterson_bound_actual
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {M : ℝ} (hM : 0 ≤ M) (Ct : ℕ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ K : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ 0 ≤ K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (i : γ) (R : Finset Eisenstein) (v : Eisenstein → ℂ)
        (P : Eisenstein → Eisenstein → Prop) (ψ : ℝ → ℝ) (w H X₀ : ℝ),
      0 < H → (∀ r ∈ R, primary r) → (∀ r ∈ R, ‖v r‖ ≤ M) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      ‖restrictedNoStopCenteredValue R v ψ w ρ (X^(38/100:ℝ))
        (Real.exp hW.radius) ℓ (W i) H ((1+Real.log X)^Ct) X X₀ P‖ ≤
        K*(1+Real.log X)^(Ct+1)*X^(5/6-1/100:ℝ) := by
  obtain ⟨ρ,K,hρ,hρ₂,hsmall,hK,hbound⟩ := restricted_noStop_central_bound_actual  hW ℓ hGamma
    (by norm_num : (0:ℝ) < 1/100) hM Ct hcap
  refine ⟨ρ,K,hρ,hρ₂,hsmall,hK,?_⟩
  filter_upwards [hbound,eventually_noStop_scales hW] with X hb hx
  intro i R v P ψ w H X₀ hH hR hv hψ
  have he := hb i R v ψ w (X^(38/100:ℝ)) (X^(2/5:ℝ)) H X₀ P
    hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2 hH hR hv hψ
  have hXp : 0 < X := by linarith [hx.1]
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith [hx.1])
  have hlogs : 1+Real.log (X^(2/5:ℝ)) ≤ 1+Real.log X := by
    rw [Real.log_rpow hXp]
    linarith
  apply he.trans
  calc
    _ ≤ K*(1+Real.log X)*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := by gcongr
    _ = _ := by rw [pow_succ]; ring

theorem distinguishedScaleNoStop_finite_isLittleO_actual (m : ℕ)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (ξ : ℝ) (Ct : ℕ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ ∀ i < m, ∀ (H : ℝ → ℝ)
      (P : ℝ → Eisenstein → Eisenstein → Prop),
      (∀ᶠ X : ℝ in atTop, 0 < H X) →
      (fun X => distinguishedScaleNoStop i ρ ξ Ct (H X) X (P X))
        =o[atTop] firstMomentScale := by
  let M : ℝ := ∑ j ∈ Finset.range m, ‖(j.factorial:ℂ)⁻¹‖*(j^j:ℕ)
  obtain ⟨ρ,K,hρ,hρ₂,hsmall,hK,hbound⟩ := restricted_noStop_patterson_bound_actual  primeProductWeights 0
    hGamma (show 0 ≤ M by dsimp [M]; positivity) Ct hcap
  refine ⟨ρ,hρ,hρ₂,hsmall,?_⟩
  intro i hi H P hH
  have hMi : ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ) ≤ M := by
    dsimp only [M]
    exact Finset.single_le_sum (f := fun j : ℕ => ‖(j.factorial:ℂ)⁻¹‖*(j^j:ℕ))
      (fun j _ => by positivity) (Finset.mem_range.mpr hi)
  obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i 0
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => (1+Real.log X)^(Ct+1+i)*X^(5/6-1/100:ℝ)) ?_
    (log_power_powerSaving_isLittleO (Ct+1+i) (by norm_num))
  apply Asymptotics.IsBigO.of_bound (D*K)
  filter_upwards [hbound,hH,eventually_ge_atTop (1:ℝ)] with X hb hH hX
  have hL : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  let B := K*(1+Real.log X)^(Ct+1)*X^(5/6-1/100:ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpiece (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
      ‖if distinguishedScaleLength k < X^(69/200:ℝ) then
        restrictedNoStopCenteredValue (centralPrimaryFactors X)
          (distinguishedScaleCoefficient i ξ X k) primeDetectorCutoff (X^ξ) ρ
          (X^(38/100:ℝ)) (Real.exp primeProductWeights.radius) 0 primeProductEnvelope
          (H X) ((1+Real.log X)^Ct) X X (P X) else 0‖ ≤ B := by
    split_ifs
    · exact hb () (centralPrimaryFactors X) (distinguishedScaleCoefficient i ξ X k)
        (P X) primeDetectorCutoff (X^ξ) (H X) X hH
        (fun _ hr => (mem_primaryElementBall.mp hr).1)
        (fun r _ => (distinguishedScaleCoefficient_norm i ξ X k r).trans hMi)
        (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
    · simpa only [norm_zero] using hB
  have hn : (Fintype.card (Fin i → Fin
      (normPartitionCount (Real.exp primeProductWeights.radius*X))):ℝ) ≤ D*(1+Real.log X)^i := by
    simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_sum,Nat.add_zero]
      using hcount X hX
  rw [Real.norm_of_nonneg (by positivity)]
  unfold distinguishedScaleNoStop
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun k _ => hpiece k)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  apply (mul_le_mul_of_nonneg_right hn hB).trans_eq
  dsimp [B]
  rw [pow_add]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralScaleFirstStoppedEarly
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary cancellation for every actual early stopped dyad. All length,
weight and support conditions are derived from its original finite sum. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem distinguishedStoppedDyad_early_bound_actual (i : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C ξ ρ ε : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100)
    (k Ct : ℕ) :
    ∃ (G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ H : ℝ, 0 < H → ∀ h : ℕ,
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ)
        (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) h) →
      ∀ (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ) (j r : ℕ), 1 ≤ q.2.1 → q.1 < h →
      ‖distinguishedStoppedDyad i ρ ξ Ct H X h true d q j r‖ ≤
        K*X^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨G,K,hK,hbound⟩ := ordinary_stopped_low_kernel_bound_actual i hpnt hSW hMV hC
    hHuxley  hGamma hξ hξz hρ hρ₂ k Ct
  refine ⟨G,K,hK,?_⟩
  filter_upwards [hbound,eventually_distinguishedStoppedDyad_geometry hρ hρ₂ hε hsmall hgap,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 9/25)).eventually_ge_atTop 2,
    eventually_gt_atTop (1:ℝ)] with X hb hg hZ hX
  intro H hH h hh hrough d q j r hk hjh
  have hXp : 0 < X := zero_lt_one.trans hX
  have hlog : 0 < Real.log X := Real.log_pos hX
  by_cases hz : distinguishedStoppedDyad i ρ ξ Ct H X h true d q j r = 0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨hBlo,hBhi,hBX,hABlo,hABhi,hj⟩ := hg i Ct H h true d q j r hk hz
  have hXF : X ≤ Real.exp primeProductWeights.radius*X :=
    le_mul_of_one_le_left hXp.le (Real.one_le_exp primeProductWeights.radius_nonneg)
  have he : geometricBinLower ρ (Real.exp primeProductWeights.radius*X) h =
      geometricBinLower ρ X
        (h-(geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X)) := by
    simpa only [Nat.sub_add_cancel hh] using
      geometricBinLower_shift hρ hXp hXF
        (h-(geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X))
  rw [distinguishedStoppedDyad_to_row i hρ hρ₂ hX.le Ct H h true d q j r hk
    (by simpa only [Bool.true_eq,ite_true, if_true] using hZ) hBX hj hh]
  have hP (n : Eisenstein) (hn : n ∈ stoppedNormDyad (distinguishedStoppedSide X) j) :
      primary n ∧ Squarefree n ∧ stoppedNormDyadLength j/2 ≤ norm n ∧
        norm n ≤ 2*(stoppedNormDyadLength j/2) := by
    have hs := distinguishedStoppedSide_spec (Finset.mem_filter.mp hn).1
    have hh := stoppedNormDyad_outer_bounds hn hs.1
    exact ⟨hs.1,hs.2.1,hh.1,by nlinarith [hh.2]⟩
  have hresult := hb _ d (stoppedNormDyadLength j/2) (stoppedNormDyadLength r) H
    hABlo hABhi hBlo hBhi hH
    (q.1-(geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X))
    q.2.1 (h-(geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X))
    (X^(9/25:ℝ)) (X^(9/25:ℝ)) true (by omega)
    (by simpa only [he] using hrough)
    (centralPrimaryFactors X) (centralPrimaryFactors X)
    (stoppedNormDyad (distinguishedStoppedSide X) j)
    (stoppingRemainingTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.2)
    (fun n hn => (mem_primaryElementBall.mp hn).1) hP
  simpa only [distinguishedStoppedAlpha,distinguishedShiftedSideTest,Bool.true_eq,ite_true, if_true]
    using hresult

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralScaleFirstEarlyNegligible
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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


theorem scaleFirstStoppedEarly_isLittleO_actual (m : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C ξ ρ ε : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100)
    (Ct : ℕ) :
    ∃ G : ℕ, ∀ (H : ℝ → ℝ) (h : ℝ → ℕ),
      (∀ᶠ X : ℝ in atTop, 0 < H X) →
      (∀ᶠ X : ℝ in atTop,
        geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h X) →
      (∀ᶠ X : ℝ in atTop, 2*(Real.log X)^G ≤ min (X^ξ)
        (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X))) →
      (fun X => scaleFirstStoppedSum m ρ ξ Ct (H X) X (h X) true)
        =o[atTop] firstMomentScale := by
  have hdata (i : Fin m) := distinguishedStoppedDyad_early_bound_actual i.val hpnt hSW hMV hC
    hHuxley  hGamma hξ hξz hρ hρ₂ hε hsmall hgap (i.val+8) Ct
  choose G K hK hb using hdata
  let G₀ := ∑ i : Fin m, G i
  refine ⟨G₀,?_⟩
  intro H h hH hh hrough
  unfold scaleFirstStoppedSum
  apply Asymptotics.IsLittleO.fun_sum
  intro i hi
  let ii : Fin m := ⟨i,Finset.mem_range.mp hi⟩
  obtain ⟨D,hD,hagg⟩ := distinguishedScaleStopped_bound i hρ
  have hGG : G ii ≤ G₀ := Finset.single_le_sum (fun j _ => Nat.zero_le (G j)) (Finset.mem_univ ii)
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound (D*K ii*2^(i+8))
  filter_upwards [hb ii,hH,hh,hrough,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with X hbound hH hh hrough hX hlog
  have hKi : 0 < K ii := hK ii
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hL : 0 < 1+Real.log X := by linarith
  have hroughi : 2*(Real.log X)^(G ii) ≤ min (X^ξ)
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X)) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog hGG) (by norm_num)).trans hrough
  have hpiece (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (q : ℕ × ℕ × ℕ)
      (hq : q ∈ (if true then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
        (fun q => q.1 < h X) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)))
      (j r : ℕ) :
      ‖distinguishedStoppedDyad i ρ ξ Ct (H X) X (h X) true d q j r‖ ≤
        K ii*X^(5/6:ℝ)/(Real.log X)^(i+8) := by
    have hq' := Finset.mem_filter.mp hq
    have hk : 1 ≤ q.2.1 := (Finset.mem_filter.mp hq'.1).2
    exact hbound (H X) hH (h X) hh hroughi d q j r hk hq'.2
  have hsum := hagg Ct ξ (H X) X hX (h X) true
    (K ii*X^(5/6:ℝ)/(Real.log X)^(i+8)) (by positivity) hpiece
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
  apply hsum.trans
  have hn := stopped_log_quotient_normalize (i+5) 3 hlog (hK ii).le
    (Real.rpow_nonneg hXp.le (5/6:ℝ))
  have hn' : (1+Real.log X)^(i+5)*(K ii*X^(5/6:ℝ)/(Real.log X)^(i+8)) ≤
      (K ii*2^(i+8))*X^(5/6:ℝ)/(1+Real.log X)^3 := by
    simpa only [show i+5+3=i+8 by omega] using hn
  calc
    _ = D*((1+Real.log X)^(i+5)*(K ii*X^(5/6:ℝ)/(Real.log X)^(i+8))) := by ring
    _ ≤ D*((K ii*2^(i+8))*X^(5/6:ℝ)/(1+Real.log X)^3) :=
      mul_le_mul_of_nonneg_left hn' hD.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralScaleFirstStoppedReduction
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial central kernel reduced to the two actual stopped branches.
The no-stop term is removed using one arbitrarily small fixed mesh for
all arities and all first-stage boundary choices. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment


theorem scaleFirstLow_sub_stopped_isLittleO_actual (m : ℕ)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (ξ : ℝ) (Ct : ℕ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ ∀ (H : ℝ → ℝ),
      (∀ᶠ X : ℝ in atTop, 0 < H X) → ∀ h : ℝ → ℕ,
      (fun X => scaleFirstLowAritySum m 0 ξ Ct (H X) X -
        (scaleFirstStoppedSum m ρ ξ Ct (H X) X (h X) true +
          scaleFirstStoppedSum m ρ ξ Ct (H X) X (h X) false))
        =o[atTop] firstMomentScale := by
  obtain ⟨ρ,hρ,hρ₂,hsmall,hn⟩ :=
    distinguishedScaleNoStop_finite_isLittleO_actual m  hGamma ξ Ct hcap
  refine ⟨ρ,hρ,hρ₂,hsmall,?_⟩
  intro H hH h
  have hsum := Asymptotics.IsLittleO.fun_sum (s := Finset.range m)
    (fun i hi => hn i (Finset.mem_range.mp hi) H
      (fun X => stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X)
        (X^(9/25:ℝ)) (h X)) hH)
  apply hsum.congr' ?_ Filter.EventuallyEq.rfl
  have hid : ∀ᶠ X : ℝ in atTop, ∀ i ∈ Finset.range m,
      ∀ (H : ℝ) (h : ℕ), distinguishedLowScaleRows i 0 ξ Ct H X =
        distinguishedScaleNoStop i ρ ξ Ct H X
          (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h) +
        distinguishedScaleStopped i ρ ξ Ct H X h true +
        distinguishedScaleStopped i ρ ξ Ct H X h false := by
    rw [Filter.eventually_all_finset]
    intro i _
    filter_upwards [distinguishedLowScaleRows_two_stage i ξ] with X hX
    exact fun H h => hX ρ hρ hρ₂ Ct H h
  filter_upwards [hid] with X hid
  unfold scaleFirstLowAritySum scaleFirstStoppedSum
  have he : (∑ i ∈ Finset.range m, distinguishedLowScaleRows i 0 ξ Ct (H X) X) =
      ∑ i ∈ Finset.range m,
        (distinguishedScaleNoStop i ρ ξ Ct (H X) X
          (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) (h X)) +
        distinguishedScaleStopped i ρ ξ Ct (H X) X (h X) true +
        distinguishedScaleStopped i ρ ξ Ct (H X) X (h X) false) :=
    Finset.sum_congr rfl (fun i hi => hid i hi (H X) (h X))
  rw [he,Finset.sum_add_distrib,Finset.sum_add_distrib]
  ring

theorem primeProductLowHeight_sub_stopped_isLittleO_actual
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ (m : ℕ) (ρ : ℝ), 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧
      ∀ (H : ℝ → ℝ), (∀ᶠ X : ℝ in atTop, 0 < H X) → ∀ h : ℝ → ℕ,
      (fun X => primeProductLowHeight 0 (H X) ((1+Real.log X)^Ct) X -
        (scaleFirstStoppedSum m ρ ξ Ct (H X) X (h X) true +
          scaleFirstStoppedSum m ρ ξ Ct (H X) X (h X) false))
        =o[atTop] firstMomentScale := by
  obtain ⟨m,hm⟩ := primeProductLowHeight_sub_low_scale_isLittleO_actual hpnt hSW hpub hHuxley hperiod
    hMV hC hξ hξz hGI hGQ  hGamma Ct
  obtain ⟨ρ,hρ,hρ₂,hsmall,hr⟩ := scaleFirstLow_sub_stopped_isLittleO_actual m  hGamma ξ Ct hcap
  refine ⟨m,ρ,hρ,hρ₂,hsmall,?_⟩
  intro H hH h
  apply ((hm H hH).add (hr H hH h)).congr' ?_ Filter.EventuallyEq.rfl
  exact Filter.Eventually.of_forall (fun X => by dsimp; ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralScaleFirstCentralNegligible
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original radial low-height prime kernel is negligible, after
choosing the genuine two-stage logarithmic boundary. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem primeProductLowHeight_radial_isLittleO_actual_oai
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξsmall : ξ < 1/100)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => primeProductLowHeight 0 (H X) ((1+Real.log X)^Ct) X)
      =o[atTop] firstMomentScale := by
  let ε := (1/100-ξ)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : ξ+ε < 1/100 := by dsimp [ε]; linarith
  have hcap : 1 < (2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  have hξz : ξ ≤ 2/5 := by linarith
  obtain ⟨m,ρ,hρ,hρ₂,hsmall,hred⟩ := primeProductLowHeight_sub_stopped_isLittleO_actual
    hpnt hSW hpub hHuxley hperiod hMV hC hξ hξz hGI hGQ  hGamma Ct hcap
  obtain ⟨G,hearly⟩ := scaleFirstStoppedEarly_isLittleO_actual m hpnt hSW hMV hC hHuxley
     hGamma hξ hξz hρ hρ₂ hε.le hsmall hgap Ct
  let P (X : ℝ) (h : ℕ) : Prop :=
    h < geometricBinCount ρ (Real.exp primeProductWeights.radius*X) ∧
    geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h ∧
    2*(Real.log X)^G ≤ min (X^ξ)
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) h) ∧
    ρ*geometricBinLower ρ (Real.exp primeProductWeights.radius*X) h ≤ (Real.log X)^(G+4)
  let h (X : ℝ) : ℕ := Classical.epsilon (P X)
  have hspec : ∀ᶠ X : ℝ in atTop, P X (h X) := by
    filter_upwards [eventually_stopping_active_boundary_envelope hξ G,
      eventually_ge_atTop (1:ℝ)] with X hb hX
    apply Classical.epsilon_spec
    exact hb (Real.exp primeProductWeights.radius*X)
      (le_mul_of_one_le_left (zero_lt_one.trans_le hX).le
        (Real.one_le_exp primeProductWeights.radius_nonneg)) ρ hρ hρ₂
  have hindex : ∀ᶠ X : ℝ in atTop,
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h X :=
    hspec.mono (fun _ hx => hx.2.1)
  have hrough : ∀ᶠ X : ℝ in atTop, 2*(Real.log X)^G ≤ min (X^ξ)
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X)) :=
    hspec.mono (fun _ hx => hx.2.2.1)
  have hboundary : ∀ᶠ X : ℝ in atTop,
      ρ*geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X) ≤
        (Real.log X)^((G+4:ℕ):ℝ) :=
    hspec.mono (fun X hx => by simpa only [Real.rpow_natCast] using hx.2.2.2)
  have he := hearly H h hH hindex hrough
  have hl := scaleFirstStoppedLate_isLittleO m hpnt
    (show (0:ℝ) < ((G+4:ℕ):ℝ) by positivity) hξ hρ hρ₂ hε.le hsmall hgap Ct H h
    hH hindex hboundary
  apply ((hred H hH h).add (he.add hl)).congr' ?_ Filter.EventuallyEq.rfl
  exact Filter.Eventually.of_forall (fun X => by dsimp; ring)

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.primeProductLowHeight_radial_isLittleO_actual_oai := @OAI.CubicFirstMoment.primeProductLowHeight_radial_isLittleO_actual_oai
