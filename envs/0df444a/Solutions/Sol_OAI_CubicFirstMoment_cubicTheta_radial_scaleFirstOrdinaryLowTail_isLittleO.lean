-- Prove2me | solution 1 for OAI.CubicFirstMoment.cubicTheta_radial_scaleFirstOrdinaryLowTail_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:33:42.066042+00:00
-- url     : https://prove2.me/submissions/87f0a236-161e-4d5b-9d95-91b855afded5

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_cubicTheta_radial_scaleFirstOrdinaryNoStopTail_isLittleO
import Theorems.Thm_OAI_CubicFirstMoment_distinguishedStoppedEnvelopeTail_bound

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedAggregation
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstTailDecompositionRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scale-first and two-stage stopping identities for the original
Gauss height windows. Every matrix retains its total-product envelope. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem scaleFirstTailScaleRow_two_stage (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∀ (ℓ : ℤ) (H U : ℝ) (h : ℕ)
        (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      distinguishedScaleLength d < X^(69/200:ℝ) →
      scaleFirstTailScaleRow i ℓ ξ H U X d =
        scaleFirstTailNoStopRow i ℓ ρ ξ H U X h d+
        scaleFirstTailStoppedRow i ℓ ρ ξ H U X h true d+
        scaleFirstTailStoppedRow i ℓ ρ ξ H U X h false d := by
  filter_upwards [eventually_distinguishedScale_low_initial i ξ,
    eventually_ge_atTop (1:ℝ)] with X hstart hX
  intro ρ hρ hρ₂ ℓ H U h d hd
  have hF : 1 ≤ Real.exp primeProductWeights.radius*X :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  have he := roughProduct_matrix_two_stage (centralProductEnvelope X) (centralPrimaryFactors X)
    hρ hρ₂ hF (fun _ hn => centralProductEnvelope_spec hn)
    (fun _ hr => (mem_primaryElementBall.mp hr).1)
    (distinguishedScaleCoefficient i ξ X d) (fun r _ hr => hstart d hd r hr)
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (9/25:ℝ) ≤ 38/100))
    h primeDetectorCutoff (X^ξ) (scaleFirstTailKernel ℓ H U X)
  unfold scaleFirstTailScaleRow
  rw [he]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · unfold scaleFirstTailNoStopRow stoppingFailedPrefix
      apply Finset.sum_congr rfl
      intro r _
      congr 1
    · rfl
  · rfl

theorem scaleFirstTailStoppedRow_dyads (i : ℕ) (ℓ : ℤ) (ρ ξ H U X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    scaleFirstTailStoppedRow i ℓ ρ ξ H U X h early d =
      ∑ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
          (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*
          ∑ j ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
            ∑ k ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
              scaleFirstTailStoppedDyad i ℓ ρ ξ H U X h early d q j k := by
  unfold scaleFirstTailStoppedRow
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstTailAggregation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact summation of retained-envelope height tails over the original
labels, sharp side dyads and low distinguished-scale pieces. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma scaleFirstTailStoppedRow_height_dyads (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      scaleFirstTailStoppedRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d) =
      ∑ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
        (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*
          ∑ j ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
            ∑ k ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
              ∑ s ∈ Finset.range (heightWindowCount H T),
                scaleFirstTailStoppedDyad i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k := by
  simp_rw [scaleFirstTailStoppedRow_dyads]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [←Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

theorem scaleFirstStoppedEnvelopeTail_aggregate (i : ℕ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ξ H T X : ℝ), 1 ≤ X → ∀ (h : ℕ) (early : Bool)
      (M : ℝ), 0 ≤ M →
      (∀ (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ),
        q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
          (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)) →
        ∀ j k : ℕ, ‖∑ s ∈ Finset.range (heightWindowCount H T),
          scaleFirstTailStoppedDyad i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k‖ ≤ M) →
      ‖scaleFirstStoppedEnvelopeTail i ρ ξ H T X h early‖ ≤
        K*(1+Real.log X)^(i+5)*M := by
  obtain ⟨D,hD,hcount⟩ := stoppedFactorSupport_log_count
  obtain ⟨C,hC,hlabels⟩ := stopping_label_weighted_sum_dilated hρ
    (Real.one_le_exp primeProductWeights.radius_nonneg)
  obtain ⟨E,hE,hparts⟩ := stopped_norm_partition_subset_count i
  refine ⟨E*(C*D^2),by positivity,?_⟩
  intro ξ H T X hX h early M hM hpiece
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  let I := if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
    (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)
  let J := (distinguishedStoppedSide X).image stoppedNormDyadIndex
  let S := (Finset.univ : Finset (Fin i → Fin (normPartitionCount
    (Real.exp primeProductWeights.radius*X))))
  have hI : I ⊆ stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X) := by
    dsimp [I]
    split
    · exact Finset.filter_subset _ _
    · exact Finset.Subset.refl _
  have hJ : (J.card:ℝ) ≤ D*(1+Real.log X) := hcount X hX _
  have hrow (d) : ‖∑ s ∈ Finset.range (heightWindowCount H T),
      scaleFirstTailStoppedRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d‖ ≤
      (C*D^2)*(1+Real.log X)^5*M := by
    rw [scaleFirstTailStoppedRow_height_dyads]
    have hinner (q) (hq : q ∈ I) :
        ‖∑ j ∈ J, ∑ k ∈ J, ∑ s ∈ Finset.range (heightWindowCount H T),
          scaleFirstTailStoppedDyad i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k‖ ≤
        D^2*(1+Real.log X)^2*M := by
      apply (norm_double_sum_le_card_sq J J _ (fun j _ k _ => hpiece d q hq j k)).trans
      have hs := mul_le_mul hJ hJ (Nat.cast_nonneg J.card)
        (by positivity : 0 ≤ D*(1+Real.log X))
      calc
        _ ≤ (D*(1+Real.log X))*(D*(1+Real.log X))*M := mul_le_mul_of_nonneg_right hs hM
        _ = _ := by ring
    exact ((hlabels X hX I hI).2 _ (D^2*(1+Real.log X)^2*M)
      (by positivity) hinner).trans_eq (by ring)
  have hb (d) : ‖(if distinguishedScaleLength d < X^(69/200:ℝ) then
      ∑ s ∈ Finset.range (heightWindowCount H T),
        scaleFirstTailStoppedRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d else 0)‖ ≤
      (C*D^2)*(1+Real.log X)^5*M := by
    split_ifs
    · exact hrow d
    · rw [norm_zero]; positivity
  calc
    _ ≤ ∑ d ∈ S, (C*D^2)*(1+Real.log X)^5*M := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun d _ => hb d)
    _ = (S.card:ℝ)*((C*D^2)*(1+Real.log X)^5*M) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (E*(1+Real.log X)^i)*((C*D^2)*(1+Real.log X)^5*M) :=
      mul_le_mul_of_nonneg_right (hparts X hX S) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem scaleFirstStoppedEnvelopeTail_bound (i : ℕ)
    (hpnt : PrimaryPrimePNT) {C ξ ρ ε : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100) (n : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H T : ℝ) (h : ℕ) (early : Bool),
      (1+Real.log X)^Ct ≤ T → 1 ≤ H → H ≤ X →
      ‖scaleFirstStoppedEnvelopeTail i ρ ξ H T X h early‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨K,Ct,hK,hbound⟩ := distinguishedStoppedEnvelopeTail_bound i hpnt hMV hC hHuxley
    hξ hξz hρ hρ₂ hε hsmall hgap (i+5+n)
  obtain ⟨D,hD,hagg⟩ := scaleFirstStoppedEnvelopeTail_aggregate i hρ
  refine ⟨D*K,Ct,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with X hb hX
  intro H T h early hT hH hHX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hs := hagg ξ H T X hX h early
    (K*X^(5/6:ℝ)/(1+Real.log X)^(i+5+n)) (by positivity)
    (fun d q hq j k => hb H T h early d q j k hT hH hHX (by
      cases early
      · exact (Finset.mem_filter.mp hq).2
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2))
  apply hs.trans_eq
  rw [pow_add]
  field_simp
  simp only [pow_add]
  ring


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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstOrdinaryStoppedTail
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary-height stopped contribution is an exact prefix of the
retained-envelope tail, bounded as a difference of two complete tails. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma scaleFirstStoppedWindow_sum (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) (early : Bool) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      scaleFirstStoppedWindow i ρ ξ H (T*(3/2:ℝ)^s) X h early) =
      scaleFirstStoppedEnvelopeTail i ρ ξ H T X h early := by
  unfold scaleFirstStoppedWindow scaleFirstStoppedEnvelopeTail
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : distinguishedScaleLength d < X^(69/200:ℝ)
  · simp only [hd,ite_true, if_true]
  · simp only [hd,ite_false, if_false,Finset.sum_const_zero]

lemma scaleFirstOrdinaryStoppedArity_prefix (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ)
    (early : Bool) (hH : 0 < H) (hT : 0 < T) :
    ∃ j ≤ heightWindowCount H T,
      scaleFirstOrdinaryStoppedArity i ρ ξ H T X h early =
        scaleFirstStoppedEnvelopeTail i ρ ξ H T X h early-
          scaleFirstStoppedEnvelopeTail i ρ ξ H (T*(3/2:ℝ)^j) X h early := by
  obtain ⟨j,hj,he⟩ := geometricHeight_filtered_prefix
    (fun U => scaleFirstStoppedWindow i ρ ξ H U X h early) hH hT (X^(1/100:ℝ))
  refine ⟨j,hj,?_⟩
  simpa only [scaleFirstOrdinaryStoppedArity,scaleFirstStoppedWindow_sum] using he

theorem scaleFirstOrdinaryStoppedArity_bound (i : ℕ)
    (hpnt : PrimaryPrimePNT) {C ξ ρ ε : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100) (n : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H T : ℝ) (h : ℕ) (early : Bool),
      (1+Real.log X)^Ct ≤ T → 1 ≤ H → H ≤ X →
      ‖scaleFirstOrdinaryStoppedArity i ρ ξ H T X h early‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨K,Ct,hK,hbound⟩ := scaleFirstStoppedEnvelopeTail_bound i hpnt hMV hC hHuxley
    hξ hξz hρ hρ₂ hε hsmall hgap n
  refine ⟨2*K,Ct,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with X hb hX
  intro H T h early hT hH hHX
  have hL : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hTp : 0 < T := zero_lt_one.trans_le ((one_le_pow₀ hL).trans hT)
  obtain ⟨j,_hj,he⟩ := scaleFirstOrdinaryStoppedArity_prefix i ρ ξ H T X h early
    (zero_lt_one.trans_le hH) hTp
  have hT' : (1+Real.log X)^Ct ≤ T*(3/2:ℝ)^j := by
    apply hT.trans
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left
        (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3/2) : 1 ≤ (3/2:ℝ)^j) hTp.le)
  rw [he]
  exact (norm_sub_le _ _).trans
    ((add_le_add (hb H T h early hT hH hHX)
      (hb H (T*(3/2:ℝ)^j) h early hT' hH hHX)).trans_eq (by ring))

theorem scaleFirstOrdinaryStoppedTail_isLittleO (m : ℕ)
    (hpnt : PrimaryPrimePNT) {C ξ ρ ε : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100) :
    ∃ Ct : ℕ, ∀ (H T : ℝ → ℝ) (h : ℝ → ℕ) (early : ℝ → Bool),
      (∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X) →
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
      (∀ᶠ X : ℝ in atTop, H X ≤ X) →
      (fun X => ∑ i ∈ Finset.range m,
        scaleFirstOrdinaryStoppedArity i ρ ξ (H X) (T X) X (h X) (early X))
        =o[atTop] firstMomentScale := by
  have hd (i : Fin m) := scaleFirstOrdinaryStoppedArity_bound i.val hpnt hMV hC hHuxley
    hξ hξz hρ hρ₂ hε hsmall hgap 3
  choose K Ct hK hb using hd
  let Ct₀ := ∑ i : Fin m, Ct i
  refine ⟨Ct₀,?_⟩
  intro H T h early hT hH hHX
  apply Asymptotics.IsLittleO.fun_sum
  intro i hi
  let ii : Fin m := ⟨i,Finset.mem_range.mp hi⟩
  have hCt : Ct ii ≤ Ct₀ :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (Ct j)) (Finset.mem_univ ii)
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound (K ii)
  filter_upwards [hb ii,hT,hH,hHX,eventually_ge_atTop (1:ℝ)]
    with X hbound hT hH hHX hX
  have hL : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hT' : (1+Real.log X)^(Ct ii) ≤ T X := (pow_le_pow_right₀ hL hCt).trans hT
  simpa only [Real.norm_of_nonneg (by positivity :
    0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3),mul_div_assoc] using
    hbound (H X) (T X) (h X) (early X) hT' hH hHX

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstOrdinaryTail
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordinary-height low distinguished-scale contribution is
negligible, by the exact no-stop and two-stage stopped decomposition. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma scaleFirstOrdinaryLowArity_two_stage (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ (H T : ℝ) (h : ℕ),
      scaleFirstOrdinaryLowArity i ξ H T X =
        scaleFirstOrdinaryNoStopArity i ρ ξ H T X h+
        scaleFirstOrdinaryStoppedArity i ρ ξ H T X h true+
        scaleFirstOrdinaryStoppedArity i ρ ξ H T X h false := by
  filter_upwards [scaleFirstTailScaleRow_two_stage i ξ] with X hrow
  intro ρ hρ hρ₂ H T h
  unfold scaleFirstOrdinaryLowArity scaleFirstOrdinaryNoStopArity
    scaleFirstOrdinaryStoppedArity scaleFirstStoppedWindow
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : T*(3/2:ℝ)^s ≤ X^(1/100:ℝ)
  · simp only [hs,ite_true, if_true]
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : distinguishedScaleLength d < X^(69/200:ℝ)
    · simp only [hd,ite_true, if_true]
      exact hrow ρ hρ hρ₂ 0 H (T*(3/2:ℝ)^s) h d hd
    · simp only [hd,ite_false, if_false,zero_add]
  · simp only [hs,ite_false, if_false,zero_add]

lemma scaleFirstOrdinaryLowTail_two_stage (m : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ (H T : ℝ) (h : ℕ),
      scaleFirstOrdinaryLowTail m ξ H T X = scaleFirstOrdinaryNoStopTail m ρ ξ H T X h+
        (∑ i ∈ Finset.range m, scaleFirstOrdinaryStoppedArity i ρ ξ H T X h true)+
        (∑ i ∈ Finset.range m, scaleFirstOrdinaryStoppedArity i ρ ξ H T X h false) := by
  have hall : ∀ᶠ X : ℝ in atTop, ∀ i ∈ Finset.range m,
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 → ∀ (H T : ℝ) (h : ℕ),
      scaleFirstOrdinaryLowArity i ξ H T X =
        scaleFirstOrdinaryNoStopArity i ρ ξ H T X h+
        scaleFirstOrdinaryStoppedArity i ρ ξ H T X h true+
        scaleFirstOrdinaryStoppedArity i ρ ξ H T X h false := by
    rw [Filter.eventually_all_finset]
    exact fun i _ => scaleFirstOrdinaryLowArity_two_stage i ξ
  filter_upwards [hall] with X hr
  intro ρ hρ hρ₂ H T h
  unfold scaleFirstOrdinaryLowTail scaleFirstOrdinaryNoStopTail
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i hi => hr i hi ρ hρ hρ₂ H T h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialOrdinaryTail
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

theorem cubicTheta_radial_scaleFirstOrdinaryLowTail_isLittleO_oai (m : ℕ)
    (hpnt : PrimaryPrimePNT) {C ξ : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hξ : 0 < ξ) (hξsmall : ξ < 1/100) :
    ∃ Ct : ℕ, ∀ (H T : ℝ → ℝ),
      (∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X) →
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
      (∀ᶠ X : ℝ in atTop, H X ≤ X) →
      (fun X => scaleFirstOrdinaryLowTail m ξ (H X) (T X) X)
        =o[atTop] firstMomentScale := by
  let ε := (1/100-ξ)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : ξ+ε < 1/100 := by dsimp [ε]; linarith
  have hcap : 1 < (2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  obtain ⟨ρ,hρ,hρ₂,hsmall,hn⟩ := cubicTheta_radial_scaleFirstOrdinaryNoStopTail_isLittleO
    m hpnt hMV hC hcap
  obtain ⟨Ct,hs⟩ := scaleFirstOrdinaryStoppedTail_isLittleO m hpnt hMV hC hHuxley
    hξ (by linarith : ξ ≤ 2/5) hρ hρ₂ hε.le hsmall hgap
  refine ⟨Ct+1,?_⟩
  intro H T hT hH hHX
  have hT' : ∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X := by
    filter_upwards [hT,eventually_ge_atTop (1:ℝ)] with X ht hX
    exact (pow_le_pow_right₀ (by linarith [Real.log_nonneg hX]) (Nat.le_succ Ct)).trans ht
  have hsetup : ∀ᶠ X : ℝ in atTop, 1 ≤ H X ∧ H X ≤ X ∧ Real.log X ≤ T X := by
    filter_upwards [hT,hH,hHX,eventually_ge_atTop (1:ℝ)] with X ht hH hHX hX
    have hL : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
    exact ⟨hH,hHX,(by linarith : Real.log X ≤ 1+Real.log X).trans
      ((le_self_pow₀ hL (Nat.succ_ne_zero Ct)).trans ht)⟩
  let h : ℝ → ℕ := fun _ => 0
  have hsum := ((hn ξ H T h hsetup).add
    (hs H T h (fun _ => true) hT' hH hHX)).add
      (hs H T h (fun _ => false) hT' hH hHX)
  apply hsum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [scaleFirstOrdinaryLowTail_two_stage m ξ] with X hid
  exact (hid ρ hρ hρ₂ (H X) (T X) (h X)).symm

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.cubicTheta_radial_scaleFirstOrdinaryLowTail_isLittleO_oai := @OAI.CubicFirstMoment.cubicTheta_radial_scaleFirstOrdinaryLowTail_isLittleO_oai
