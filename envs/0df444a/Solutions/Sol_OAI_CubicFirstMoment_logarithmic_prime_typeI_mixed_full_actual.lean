-- Prove2me | solution 1 for OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:37:49.478454+00:00
-- url     : https://prove2.me/submissions/92e8e53a-d3d0-4b1d-9519-60a6982f7a64

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A016
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_LogarithmicWeightFamily_cubicTheta_centered_short_low_power
import Theorems.Thm_OAI_CubicFirstMoment_LogarithmicWeightFamily_cubicTheta_short_low_power
import Theorems.Thm_OAI_CubicFirstMoment_LogarithmicWeightFamily_metaplectic_long_sieve

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
-- module Solutions.OAIQ096_CM.CubicGram_GramPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal character Gram kernel and normalized radial Poisson expansion. -/

section

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

noncomputable section
open Filter
open scoped ContDiff

namespace CubicFirstMoment

lemma primaryCosetMap_bijective (c : Eisenstein) (hc : primary c) :
    Function.Bijective (primaryCosetMap c hc) := by
  constructor
  · intro s t hst
    have he : c+3*s=c+3*t := congrArg Subtype.val hst
    have hn : (3 : Eisenstein) ≠ 0 := by norm_num
    exact mul_left_cancel₀ hn (add_left_cancel he)
  · intro n
    obtain ⟨u, hu⟩ := n.property
    obtain ⟨v, hv⟩ := hc
    refine ⟨u-v, Subtype.ext ?_⟩
    change c+3*(u-v) = n.val
    linear_combination hv - hu

end CubicFirstMoment

end
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

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CommonFactors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem primary_moebius_coprimality {k : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) (n : Eisenstein) :
    (if IsCoprime k n then (1 : ℂ) else 0) =
      ∑ s ∈ (primaryPrimeFactors k).powerset,
        (idealMoebius (∏ p ∈ s, p) : ℂ) *
          (if (∏ p ∈ s, p) ∣ n then 1 else 0) := by
  let P := primaryPrimeFactors k
  have hprod : (∏ p ∈ P, (1 - (if p ∣ n then (1 : ℂ) else 0))) =
      if IsCoprime k n then 1 else 0 := by
    by_cases h : IsCoprime k n
    · rw [ite_eq_left h]
      apply Finset.prod_eq_one
      intro p hp
      have hpn : ¬p ∣ n := by
        intro hd
        exact (primaryPrimeFactor_spec hk hp).1.2.not_isUnit
          (h.isUnit_of_dvd' (primaryPrimeFactor_spec hk hp).2 hd)
      simp [hpn]
    · rw [ite_eq_right h]
      have hex : ∃ p ∈ P, p ∣ n := by
        by_contra hn
        have hall : ∀ p ∈ P, IsCoprime p n := by
          intro p hp
          exact ((primaryPrimeFactor_spec hk hp).1.2.irreducible.coprime_iff_not_dvd).mpr
            (fun hd => hn ⟨p, hp, hd⟩)
        have := IsCoprime.prod_left hall
        rw [primaryPrimeFactors_prod hk hsk] at this
        exact h this
      obtain ⟨p, hp, hpn⟩ := hex
      apply Finset.prod_eq_zero hp
      simp [hpn]
  rw [← hprod]
  have hex := Finset.prod_add (fun p : Eisenstein => -(if p ∣ n then (1 : ℂ) else 0))
    (fun _ => (1 : ℂ)) P
  simp only [Finset.prod_const_one, mul_one, ← sub_eq_neg_add] at hex
  rw [hex]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub : s ⊆ primaryPrimeFactors k := Finset.mem_powerset.mp hs
  rw [idealMoebius_prod_primaryPrimes s
    (fun p hp => (primaryPrimeFactor_spec hk (hsub hp)).1), Finset.prod_neg]
  push_cast
  congr 1
  by_cases h : (∏ p ∈ s, p) ∣ n
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro p hp
    simp [(primary_subsets_prod_dvd hk hsub n).mp h p hp]
  · rw [ite_eq_right h]
    have hex : ∃ p ∈ s, ¬p ∣ n := by
      by_contra hn
      apply h
      apply (primary_subsets_prod_dvd hk hsub n).mpr
      intro p hp
      by_contra hpn
      exact hn ⟨p, hp, hpn⟩
    obtain ⟨p, hp, hpn⟩ := hex
    exact Finset.prod_eq_zero hp (by simp [hpn])

end CubicFirstMoment

namespace CubicFirstMoment

lemma multiplesMap_bijective {m : Eisenstein} (hm : m ≠ 0) :
    Function.Bijective (multiplesMap m) := by
  constructor
  · intro x y h
    exact mul_left_cancel₀ hm (congrArg Subtype.val h)
  · intro n
    obtain ⟨x, hx⟩ := n.property
    exact ⟨x, Subtype.ext hx.symm⟩

lemma tsum_dvd_eq_multiples {m : Eisenstein} (hm : m ≠ 0) (F : Eisenstein → ℂ) :
    (∑' n : Eisenstein, if m ∣ n then F n else 0) =
      ∑' x : Eisenstein, F (m*x) := by
  have he := (Equiv.ofBijective (multiplesMap m) (multiplesMap_bijective hm)).tsum_eq
    (fun n => F n.val)
  change (∑' n : Eisenstein, Set.indicator {n | m ∣ n} F n) = _
  rw [← tsum_subtype]
  exact he.symm

lemma tsum_primary_dvd_eq_multiples {m : Eisenstein} (hm : primary m)
    (F : Eisenstein → ℂ) :
    (∑' n : Eisenstein, if primary n ∧ m ∣ n then F n else 0) =
      ∑' x : Eisenstein, if primary x then F (m*x) else 0 := by
  have he := tsum_dvd_eq_multiples (primary_ne_zero hm)
    (fun n => if primary n then F n else 0)
  convert he using 1
  · apply tsum_congr
    intro n
    by_cases hn : primary n <;> by_cases hd : m ∣ n <;> simp [hn, hd]
  · apply tsum_congr
    intro n
    have hp : primary (m*n) ↔ primary n := ⟨primary_of_mul hm, primary_mul hm⟩
    simp only [hp]

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primeDivisorWeight_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Eisenstein, primary a → Squarefree a →
      (2 : ℝ)^(primaryPrimeFactors a).card ≤ C * norm a ^ ε := by
  let R : ℝ := (2 : ℝ)^(1/ε)
  let U : Finset Eisenstein := (finite_norm_le R).toFinset
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  have hRe : R^ε = 2 := by
    dsimp [R]
    rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hε.ne', Real.rpow_one]
  refine ⟨(2 : ℝ)^U.card, by positivity, ?_⟩
  intro a ha hsa
  let P := primaryPrimeFactors a
  have hpoint : ∀ p ∈ P, (2 : ℝ) ≤ (if p ∈ U then 2 else 1) * norm p ^ ε := by
    intro p hp
    have hn1 := one_le_norm (primaryPrimeFactor_spec ha hp).1.2.ne_zero
    by_cases hpU : p ∈ U
    · simp only [ite_eq_left hpU]
      nlinarith [Real.one_le_rpow hn1 hε.le]
    · simp only [ite_eq_right hpU, one_mul]
      have hRp : R ≤ norm p := le_of_lt (not_le.mp (by
        intro he
        exact hpU (by simpa [U] using he)))
      rw [← hRe]
      exact Real.rpow_le_rpow hR.le hRp hε.le
  have hprod := Finset.prod_le_prod (s := P) (fun _ _ => (by norm_num : (0 : ℝ) ≤ 2)) hpoint
  rw [Finset.prod_const, Finset.prod_mul_distrib] at hprod
  have hsmall : (∏ p ∈ P, if p ∈ U then (2 : ℝ) else 1) ≤ (2 : ℝ)^U.card := by
    rw [Finset.prod_ite_mem, Finset.prod_const]
    exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (Finset.inter_subset_right))
  have heq : (∏ p ∈ P, norm p ^ ε) = norm a ^ ε := by
    rw [Real.finsetProd_rpow P norm (fun p _ => norm_nonneg p), ← norm_finset_prod]
    rw [primaryPrimeFactors_prod ha hsa]
  rw [heq] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (norm_nonneg a) _))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frequency dyads and summable base Gram recurrences. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma normNat_ne_zero_of_ne_zero {h : Eisenstein} (hh : h ≠ 0) : normNat h ≠ 0 := by
  intro hz
  apply hh
  apply norm_eq_zero_iff.mp
  rw [← normNat_cast,hz,Nat.cast_zero]

lemma mem_frequencyDyad {j : ℕ} {h : Eisenstein} :
    h ∈ frequencyDyad j ↔ h ≠ 0 ∧ Nat.log 2 (normNat h) = j := by
  simp only [frequencyDyad, Finset.mem_filter, mem_nonzeroNormBall]
  refine ⟨fun h => ⟨h.1.2,h.2⟩,fun hh => ⟨⟨?_,hh.1⟩,hh.2⟩⟩
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at ht
  rw [← normNat_cast]
  exact_mod_cast ht.le

lemma frequencyDyad_norm {j : ℕ} {h : Eisenstein} (hh : h ∈ frequencyDyad j) :
    (2 : ℝ)^j ≤ norm h ∧ norm h ≤ 2*(2 : ℝ)^j := by
  rw [mem_frequencyDyad] at hh
  have hl := Nat.pow_log_le_self 2 (normNat_ne_zero_of_ne_zero hh.1)
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at hl ht
  rw [← normNat_cast]
  constructor
  · exact_mod_cast hl
  · have ht' : (normNat h : ℝ) ≤ (2 : ℝ)^(j+1) := by exact_mod_cast ht.le
    simpa [pow_succ,mul_comm] using ht'

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergent norm series on the Eisenstein lattice

These elementary lattice bounds provide a quantitative tail for the
Möbius residue sum after square-divisor truncation.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment

lemma norm_rpow_tail_pointwise {D s t : ℝ} (hD : 0 < D) (hst : s < t)
    {a : Eisenstein} (ha : D < norm a) :
    norm a^(-t) ≤ D^(s-t)*norm a^(-s) := by
  have hn : 0 < norm a := hD.trans ha
  calc
    _ = norm a^(s-t)*norm a^(-s) := by
      rw [← Real.rpow_add hn]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hD ha.le (by linarith))
      (Real.rpow_nonneg hn.le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SchwartzLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Poisson proof of the lattice approximation needed by the cubic profile. -/

noncomputable section
open scoped BigOperators SchwartzMap
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma traceFourier_zero (F : ℂ → ℂ) : traceFourier F 0 = ∫ z : ℂ, F z := by
  simp [traceFourier,tracePair]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLatticeProfile
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual angular annulus is a smooth compactly supported plane
function. Its area integral is zero in every nonzero integral mode. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff SchwartzMap Topology
namespace CubicFirstMoment

lemma angularPlanePhase_mul (ℓ : ℤ) (z w : ℂ) :
    angularPlanePhase ℓ (z*w) = angularPlanePhase ℓ z*angularPlanePhase ℓ w := by
  simp only [angularPlanePhase,norm_mul,Complex.ofReal_mul]
  rw [mul_div_mul_comm,mul_zpow]

lemma angularPlanePhase_coe (ℓ : ℤ) (a : Eisenstein) :
    angularPlanePhase ℓ (a:ℂ) = theta ℓ a := rfl

lemma angularAnnulus_rotation (ℓ : ℤ) (W : ℝ → ℂ) {q : ℂ} (hq : ‖q‖ = 1) (z : ℂ) :
    angularAnnulus ℓ W (q*z) = angularPlanePhase ℓ q*angularAnnulus ℓ W z := by
  have hn : Complex.normSq q = 1 := by rw [Complex.normSq_eq_norm_sq,hq]; norm_num
  simp only [angularAnnulus,angularPlanePhase_mul,Complex.normSq_mul,hn,one_mul]
  ring

lemma exists_angular_sign_rotation {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ∃ q : ℂ, ‖q‖ = 1 ∧ angularPlanePhase ℓ q = -1 := by
  let q : ℂ := Complex.exp (((Real.pi/(ℓ:ℝ):ℝ):ℂ)*Complex.I)
  have hq : ‖q‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  refine ⟨q,hq,?_⟩
  rw [angularPlanePhase,hq,Complex.ofReal_one,div_one]
  dsimp [q]
  rw [←Complex.exp_int_mul]
  convert Complex.exp_pi_mul_I using 1
  all_goals try with_reducible_and_instances rfl
  have hc : (ℓ:ℂ) ≠ 0 := Int.cast_ne_zero.mpr hℓ
  push_cast
  field_simp

/-- Continuous rotational symmetry kills the area term; the discrete
primary-lattice sum itself need not vanish. -/
theorem integral_angularAnnulus_eq_zero {ℓ : ℤ} (hℓ : ℓ ≠ 0) (W : ℝ → ℂ) :
    (∫ z : ℂ, angularAnnulus ℓ W z) = 0 := by
  obtain ⟨q,hq,hphase⟩ := exists_angular_sign_rotation hℓ
  have hq0 : q ≠ 0 := by intro hh; simp [hh] at hq
  have hN : Complex.normSq q = 1 := by rw [Complex.normSq_eq_norm_sq,hq]; norm_num
  have hi := integral_complexMul q hq0 (angularAnnulus ℓ W)
  simp_rw [angularAnnulus_rotation ℓ W hq,hphase,neg_one_mul] at hi
  rw [integral_neg,hN,inv_one,one_smul] at hi
  have he : (2:ℂ)*(∫ z : ℂ, angularAnnulus ℓ W z) = 0 := by linear_combination -hi
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSmooth
attribute [-instance] _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-angular metaplectic inputs, stated for the literal Gauss series.

Sources: Heath-Brown, *Kummer's conjecture for cubic Gauss sums* (2000),
§3 Lemma 3 (author manuscript p.9), with angular index zero; Dunn–Radziwiłł,
*Bias in cubic Gauss sums* (2024), arXiv:2109.07463v3, Proposition 5.2,
pp.29–30. No Type-I estimate or Mellin contour identity is an input here. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticTotient_le_norm {r : Eisenstein} (hr : primary r) :
    metaplecticTotient r ≤ norm r := by
  let := finite_residues (primary_ne_zero hr)
  have h := Nat.card_le_card_of_injective (Units.val : (Residues r)ˣ → Residues r)
    Units.val_injective
  rw [residues_card (primary_ne_zero hr)] at h
  exact (Nat.cast_le (α := ℝ).mpr h).trans_eq (normNat_cast r)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimaryLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cancellation on the actual primary congruence class. The annulus
has zero area, and scaled coset Poisson summation controls every length. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

lemma angularPlanePhase_pos_mul (ℓ : ℤ) {s : ℝ} (hs : 0 < s) (z : ℂ) :
    angularPlanePhase ℓ ((s:ℂ)*z) = angularPlanePhase ℓ z := by
  rw [angularPlanePhase_mul]
  have he : angularPlanePhase ℓ (s:ℂ) = 1 := by
    simp [angularPlanePhase,Complex.norm_real,abs_of_pos hs,hs.ne']
  rw [he,one_mul]

lemma angularAnnulus_scaled (ℓ : ℤ) (W : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (a : Eisenstein) :
    angularAnnulus ℓ W (((1/Real.sqrt Y:ℝ):ℂ)*(a:ℂ)) =
      theta ℓ a*W (norm a/Y) := by
  have hs : 0 < 1/Real.sqrt Y := by positivity
  have hn : Complex.normSq (((1/Real.sqrt Y:ℝ):ℂ)*(a:ℂ)) = norm a/Y := by
    rw [Complex.normSq_mul,Complex.normSq_ofReal]
    change (1/Real.sqrt Y)*(1/Real.sqrt Y)*norm a = norm a/Y
    rw [one_div,←mul_inv,←pow_two,Real.sq_sqrt hY.le]
    ring
  rw [angularAnnulus,angularPlanePhase_pos_mul ℓ hs,angularPlanePhase_coe,hn]

lemma primary_scaled_coset (F : ℂ → ℂ) (s : ℂ) :
    (∑' u : PrimaryArgument, F (s*(u:ℂ))) =
      ∑' a : Eisenstein, F (s+(s*3)*(a:ℂ)) := by
  let e := Equiv.ofBijective (primaryCosetMap 1 primary_one)
    (primaryCosetMap_bijective 1 primary_one)
  have he := e.tsum_eq (fun u : PrimaryArgument => F (s*(u:ℂ)))
  change (∑' a : Eisenstein, F (s*((primaryCosetMap 1 primary_one a:PrimaryArgument):ℂ))) = _ at he
  have h3 : ((3:Eisenstein):ℂ) = 3 := map_ofNat eisensteinRing.val 3
  simpa [primaryCosetMap,mul_add,mul_assoc,h3] using he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCoprimeLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coprimality removal for the angular lattice model. The
primary congruence class and all divisor phases remain literal. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryAngularLattice_eq_indicator (ℓ : ℤ) (W : ℝ → ℂ) (Y : ℝ) :
    primaryAngularLattice ℓ W Y =
      ∑' u : Eisenstein, if primary u then theta ℓ u*W (norm u/Y) else 0 := by
  symm
  change (∑' u : Eisenstein, Set.indicator {u | primary u}
    (fun u => theta ℓ u*W (norm u/Y)) u) = _
  rw [←tsum_subtype]
  rfl

lemma summable_primary_angular_restricted (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hsm : ContDiff ℝ ∞ W) {Y : ℝ} (hY : 0 < Y)
    (P : Eisenstein → Prop) :
    Summable (fun u : Eisenstein => if primary u ∧ P u then theta ℓ u*W (norm u/Y) else 0) := by
  apply (schwartz_summable_eisenstein (normProfileSchwartz W hW hsm Y hY)).norm.of_norm_bounded
  intro u
  change ‖ite _ _ _‖ ≤ ‖W (norm u/Y)‖
  split_ifs with hu
  · rw [norm_mul,norm_theta (primary_ne_zero hu.1),one_mul]
  · simp

lemma primaryAngularLattice_divisor (ℓ : ℤ) (W : ℝ → ℂ) (Y : ℝ)
    {d : Eisenstein} (hd : primary d) :
    (∑' u : Eisenstein, if primary u ∧ d ∣ u then theta ℓ u*W (norm u/Y) else 0) =
      theta ℓ d*primaryAngularLattice ℓ W (Y/norm d) := by
  rw [tsum_primary_dvd_eq_multiples hd,primaryAngularLattice_eq_indicator,←tsum_mul_left]
  apply tsum_congr
  intro u
  by_cases hu : primary u
  · simp only [hu,ite_true, if_true,theta_mul,norm_mul_eq]
    have hn : norm d ≠ 0 := ne_of_gt (norm_pos_of_ne_zero (primary_ne_zero hd))
    have he : norm d*norm u/Y = norm u/(Y/norm d) := by field_simp
    rw [he]
    ring
  · simp only [hu,ite_false, if_false,mul_zero]

lemma primaryCoprimeAngularLattice_expansion {r : Eisenstein}
    (hr : primary r) (hsr : Squarefree r) (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hsm : ContDiff ℝ ∞ W) {Y : ℝ} (hY : 0 < Y) :
    primaryCoprimeAngularLattice r ℓ W Y =
      ∑ s ∈ (primaryPrimeFactors r).powerset,
        (idealMoebius (∏ p ∈ s, p):ℂ)*theta ℓ (∏ p ∈ s, p)*
          primaryAngularLattice ℓ W (Y/norm (∏ p ∈ s, p)) := by
  let P := (primaryPrimeFactors r).powerset
  let f : Finset Eisenstein → Eisenstein → ℂ := fun s u =>
    (idealMoebius (∏ p ∈ s, p):ℂ)*
      (if primary u ∧ (∏ p ∈ s, p) ∣ u then theta ℓ u*W (norm u/Y) else 0)
  have hf (s : Finset Eisenstein) (_hs : s ∈ P) : Summable (f s) :=
    (summable_primary_angular_restricted ℓ W hW hsm hY _).mul_left _
  have he (u : Eisenstein) :
      (if primary u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0) =
        ∑ s ∈ P, f s u := by
    by_cases hu : primary u
    · have hi := congrArg (fun z : ℂ => z*(theta ℓ u*W (norm u/Y)))
        (primary_moebius_coprimality hr hsr u)
      rw [Finset.sum_mul] at hi
      calc
        _ = (if IsCoprime r u then (1:ℂ) else 0)*(theta ℓ u*W (norm u/Y)) := by
          by_cases hc : IsCoprime r u <;> simp [hu,hc]
        _ = _ := hi
        _ = _ := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases hd : (∏ p ∈ s, p) ∣ u <;> simp [f,hu,hd]
    · simp [f,hu]
  unfold primaryCoprimeAngularLattice
  simp_rw [he]
  rw [Summable.tsum_finsetSum hf]
  apply Finset.sum_congr rfl
  intro s hs
  have hd : primary (∏ p ∈ s, p) := primary_finset_prod _ _
    (fun p hp => (primaryPrimeFactor_spec hr (Finset.mem_powerset.mp hs hp)).1.1)
  change (∑' u : Eisenstein, (idealMoebius (∏ p ∈ s, p):ℂ)*_) = _
  rw [tsum_mul_left,primaryAngularLattice_divisor ℓ W Y hd]
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

lemma mem_squarefreeDivisorTruncation {D : ℝ} {c : Eisenstein} :
    c ∈ squarefreeDivisorTruncation D ↔ primary c ∧ Squarefree c ∧ norm c ≤ D := by
  simp only [squarefreeDivisorTruncation,squareDivisorTruncation,Finset.mem_filter,
    mem_nonzeroNormBall]
  constructor
  · rintro ⟨⟨⟨hn,_⟩,hp⟩,hs⟩
    exact ⟨hp,hs,hn⟩
  · rintro ⟨hp,hs,hn⟩
    exact ⟨⟨⟨hn,primary_ne_zero hp⟩,hp⟩,hs⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSquarefreeIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact square-divisor Möbius identity on primary elements.
This is the arithmetic inversion used by the low-height angular model. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_subset_square_dvd {a : Eisenstein} (ha : primary a)
    {s : Finset Eisenstein} (hs : s ⊆ primaryPrimeFactors a) :
    (∏ p ∈ s, p)^2 ∣ a ↔ ∀ p ∈ s, p^2 ∣ a := by
  constructor
  · intro h p hp
    exact (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp) 2).trans h
  · intro h
    rw [←Finset.prod_pow]
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact (primaryPrimes_isCoprime (primaryPrimeFactor_spec ha (hs hp)).1
        (primaryPrimeFactor_spec ha (hs hq)).1 hpq).pow
    · exact h

lemma primarySquarePrimeFactors_empty_iff {a : Eisenstein} (ha : primary a) :
    primarySquarePrimeFactors a = ∅ ↔ Squarefree a := by
  constructor
  · intro he
    by_contra hs
    obtain ⟨p,hp,hpa⟩ := exists_primary_prime_square_dvd ha hs
    have hd : p ∣ a := (dvd_mul_right p p).trans hpa
    have hm : p ∈ primarySquarePrimeFactors a := by
      exact Finset.mem_filter.mpr ⟨(primaryPrime_mem_factors_iff ha).mpr ⟨hp,hd⟩,
        by simpa only [pow_two] using hpa⟩
    simp only [he,Finset.notMem_empty] at hm
  · intro hs
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hh := Finset.mem_filter.mp hp
    have hu : IsUnit p := hs p (by simpa only [pow_two] using hh.2)
    exact (primaryPrimeFactor_spec ha hh.1).1.2.not_isUnit hu

lemma primary_square_divisors_image (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) {a : Eisenstein} (ha : primary a)
    (hcomplete : ∀ c, primary c → Squarefree c → c^2 ∣ a → c ∈ C) :
    C.filter (fun c => c^2 ∣ a) =
      (primarySquarePrimeFactors a).powerset.image (fun s => ∏ p ∈ s, p) := by
  ext c
  constructor
  · intro hc
    obtain ⟨hc,hd⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_image.mpr ⟨primaryPrimeFactors c,Finset.mem_powerset.mpr ?_,
      primaryPrimeFactors_prod (hC c hc).1 (hC c hc).2⟩
    intro p hp
    have hpc := (primaryPrimeFactor_spec (hC c hc).1 hp).2
    have hpa := (pow_dvd_pow_of_dvd hpc 2).trans hd
    exact Finset.mem_filter.mpr
      ⟨(primaryPrime_mem_factors_iff ha).mpr
        ⟨(primaryPrimeFactor_spec (hC c hc).1 hp).1,
          (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hpa⟩,hpa⟩
  · intro hc
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hc
    have hsub := Finset.mem_powerset.mp hs
    have hpr : ∀ p ∈ s, primaryPrime p := fun p hp =>
      (primaryPrimeFactor_spec ha (Finset.mem_filter.mp (hsub hp)).1).1
    have hprim := primary_finset_prod s (fun p : Eisenstein => p) (fun p hp => (hpr p hp).1)
    have hsq := primaryPrime_product_squarefree s hpr
    have hd : (∏ p ∈ s, p)^2 ∣ a :=
      (primary_subset_square_dvd ha (fun p hp => (Finset.mem_filter.mp (hsub hp)).1)).mpr
        (fun p hp => (Finset.mem_filter.mp (hsub hp)).2)
    exact Finset.mem_filter.mpr ⟨hcomplete _ hprim hsq hd,hd⟩

lemma sum_powerset_sign (P : Finset Eisenstein) :
    (∑ s ∈ P.powerset, (-1:ℝ)^s.card) = if P = ∅ then 1 else 0 := by
  have he := Finset.prod_add (fun _ : Eisenstein => (-1:ℝ)) (fun _ => (1:ℝ)) P
  simp only [Finset.prod_const_one,mul_one,Finset.prod_const,neg_add_cancel] at he
  rw [←he]
  by_cases hP : P = ∅
  · simp [hP]
  · simp [hP,Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hP)]

/-- Every square divisor is included, so the actual truncated coefficient
equals the squarefree indicator; no error term occurs. -/
theorem primary_square_moebius_inversion (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) {a : Eisenstein} (ha : primary a)
    (hcomplete : ∀ c, primary c → Squarefree c → c^2 ∣ a → c ∈ C) :
    (∑ c ∈ C, if c^2 ∣ a then (idealMoebius c:ℝ) else 0) =
      (idealMoebius a:ℝ)^2 := by
  rw [←Finset.sum_filter,primary_square_divisors_image C hC ha hcomplete]
  have hinj : Set.InjOn (fun s : Finset Eisenstein => ∏ p ∈ s, p)
      (↑(primarySquarePrimeFactors a).powerset : Set (Finset Eisenstein)) :=
    primaryPrimeFactors_prod_injective (fun p hp =>
      (primaryPrimeFactor_spec ha (Finset.mem_filter.mp hp).1).1)
  rw [Finset.sum_image hinj]
  have he : (∑ s ∈ (primarySquarePrimeFactors a).powerset,
      (idealMoebius (∏ p ∈ s, p):ℝ)) =
      ∑ s ∈ (primarySquarePrimeFactors a).powerset,(-1:ℝ)^s.card := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [idealMoebius_prod_primaryPrimes s (fun p hp =>
      (primaryPrimeFactor_spec ha (Finset.mem_filter.mp (Finset.mem_powerset.mp hs hp)).1).1)]
    push_cast
    rfl
  rw [he,sum_powerset_sign,idealMoebius_sq]
  simp only [primarySquarePrimeFactors_empty_iff ha]

lemma squarefreeDivisorTruncation_complete {a : Eisenstein} (ha : primary a)
    {X : ℝ} (hX : norm a ≤ X) {c : Eisenstein} (hc : primary c)
    (hsc : Squarefree c) (hd : c^2 ∣ a) :
    c ∈ squarefreeDivisorTruncation (Real.sqrt X) := by
  apply mem_squarefreeDivisorTruncation.mpr
  refine ⟨hc,hsc,Real.le_sqrt_of_sq_le ?_⟩
  have hn := (norm_le_of_dvd_nonzero (primary_ne_zero ha) hd).trans hX
  simpa only [pow_two,norm_mul_eq] using hn

theorem primary_square_moebius_truncation {a : Eisenstein} (ha : primary a)
    {X : ℝ} (hX : norm a ≤ X) :
    (∑ c ∈ squarefreeDivisorTruncation (Real.sqrt X),
      if c^2 ∣ a then (idealMoebius c:ℝ) else 0) = (idealMoebius a:ℝ)^2 := by
  exact primary_square_moebius_inversion _
    (fun c hc => ⟨(mem_squarefreeDivisorTruncation.mp hc).1,
      (mem_squarefreeDivisorTruncation.mp hc).2.1⟩) ha
    (fun c hc hs hd => squarefreeDivisorTruncation_complete ha hX hc hs hd)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSquarefreeLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-height angular cancellation for the literal squarefree,
coprime primary lattice sum. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coprimeAngularLattice_divisor (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (Y : ℝ) {d : Eisenstein} (hd : primary d) :
    (∑' u : Eisenstein, if primary u ∧ d ∣ u ∧ IsCoprime r u then
      theta ℓ u*W (norm u/Y) else 0) =
      if IsCoprime r d then theta ℓ d*primaryCoprimeAngularLattice r ℓ W (Y/norm d)
      else 0 := by
  have he (u : Eisenstein) :
      (if primary u ∧ d ∣ u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0) =
      if primary u ∧ d ∣ u then
        (if IsCoprime r u then theta ℓ u*W (norm u/Y) else 0) else 0 := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [tsum_primary_dvd_eq_multiples hd]
  by_cases hc : IsCoprime r d
  · rw [ite_eq_left hc,primaryCoprimeAngularLattice,←tsum_mul_left]
    apply tsum_congr
    intro u
    have hn : norm d ≠ 0 := ne_of_gt (norm_pos_of_ne_zero (primary_ne_zero hd))
    have hs : norm d*norm u/Y = norm u/(Y/norm d) := by field_simp
    simp only [IsCoprime.mul_right_iff,hc,true_and]
    by_cases hu : primary u <;> by_cases hru : IsCoprime r u <;>
      simp [hu,hru,theta_mul,norm_mul_eq,hs,mul_assoc]
  · rw [ite_eq_right hc]
    simp only [IsCoprime.mul_right_iff,hc,false_and,ite_false, if_false]
    simp

private lemma squarefreeAngular_pointwise_inversion (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) {Y S : ℝ} (hY : 0 < Y)
    (hcut : ∀ x : ℝ, S < x → W x = 0) (u : Eisenstein) :
    (if primary u ∧ IsCoprime r u then (idealMoebius u:ℂ)^2*theta ℓ u*W (norm u/Y) else 0) =
      ∑ c ∈ squarefreeDivisorTruncation (Real.sqrt (S*Y)),
        (idealMoebius c:ℂ)*
          (if primary u ∧ c^2 ∣ u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0) := by
  by_cases hu : primary u
  · by_cases hc : IsCoprime r u
    · by_cases hw : W (norm u/Y) = 0
      · simp [hw]
      · have hn : norm u ≤ S*Y := by
          have hh : norm u/Y ≤ S := le_of_not_gt (fun hh => hw (hcut _ hh))
          exact (div_le_iff₀ hY).mp hh
        have hi : (∑ c ∈ squarefreeDivisorTruncation (Real.sqrt (S*Y)),
            if c^2 ∣ u then (idealMoebius c:ℂ) else 0) = (idealMoebius u:ℂ)^2 := by
          exact_mod_cast primary_square_moebius_truncation hu hn
        rw [ite_eq_left ⟨hu,hc⟩,←hi,Finset.sum_mul,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c hc'
        by_cases hd : c^2 ∣ u <;> simp [hu,hc,hd,mul_assoc]
    · simp [hu,hc]
  · simp [hu]

private lemma squarefreeAngular_summable (r c : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hsm : ContDiff ℝ ∞ W)
    {Y : ℝ} (hY : 0 < Y) :
    Summable (fun u : Eisenstein => (idealMoebius c:ℂ)*
      (if primary u ∧ c^2 ∣ u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0)) := by
  have hs := summable_primary_angular_restricted ℓ W hW hsm hY
    (fun u => c^2 ∣ u ∧ IsCoprime r u)
  apply (hs.mul_left (idealMoebius c:ℂ)).congr
  intro u
  by_cases hu : primary u ∧ c^2 ∣ u ∧ IsCoprime r u
  · simp only [hu]
  · simp only [hu,ite_false, if_false]

theorem squarefreeCoprimeAngularLattice_expansion
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hsm : ContDiff ℝ ∞ W)
    {Y S : ℝ} (hY : 0 < Y)
    (hcut : ∀ x : ℝ, S < x → W x = 0) :
    squarefreeCoprimeAngularLattice r ℓ W Y =
      ∑ c ∈ squarefreeDivisorTruncation (Real.sqrt (S*Y)),
        (idealMoebius c:ℂ)*
          (if IsCoprime r (c^2) then theta ℓ (c^2)*
            primaryCoprimeAngularLattice r ℓ W (Y/norm (c^2)) else 0) := by
  let C := squarefreeDivisorTruncation (Real.sqrt (S*Y))
  let T (c u : Eisenstein) : ℂ := (idealMoebius c:ℂ)*
    (if primary u ∧ c^2 ∣ u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0)
  have hsum (c : Eisenstein) : Summable (T c) := squarefreeAngular_summable r c ℓ W hW hsm hY
  have he (u : Eisenstein) :
      (if primary u ∧ IsCoprime r u then (idealMoebius u:ℂ)^2*theta ℓ u*W (norm u/Y) else 0) =
        ∑ c ∈ C,T c u := squarefreeAngular_pointwise_inversion r ℓ W hY hcut u
  unfold squarefreeCoprimeAngularLattice
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun c _ => hsum c)]
  apply Finset.sum_congr rfl
  intro c hc
  have hprim : primary (c^2) := by
    simpa only [pow_two] using primary_mul (mem_squarefreeDivisorTruncation.mp hc).1
      (mem_squarefreeDivisorTruncation.mp hc).1
  change (∑' u : Eisenstein,(idealMoebius c:ℂ)*_) = _
  rw [tsum_mul_left,coprimeAngularLattice_divisor r ℓ W Y hprim]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeightFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Mellin estimates for the smooth weight families occurring in
Type I. The hypotheses state common support and derivative bounds in
logarithmic coordinates. No transform or moment estimate is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology SchwartzMap ContDiff FourierTransform BigOperators
namespace CubicFirstMoment

private lemma weight_exp_derivative_bound {M R σ u : ℝ} (hM : 0 ≤ M)
    (hσ : |σ| ≤ M) (hu : |u| ≤ R) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v : ℝ => Real.exp (-σ*v)) u‖ ≤
      M^n * Real.exp (M*R) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_exp_const_mul]
  simp only [norm_mul,Real.norm_eq_abs,abs_pow,abs_neg,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hσ n) _ (by positivity) (by positivity)
  apply Real.exp_le_exp.mpr
  calc
    -σ*u ≤ |-σ*u| := le_abs_self _
    _ = |σ| *|u| := by rw [abs_mul,abs_neg]
    _ ≤ M*R := mul_le_mul hσ hu (abs_nonneg _) hM

lemma UniformLogWeights.log_seminorms {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i σ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n
        (mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) ≤ C := by
  choose B hB hder using h.derivative_bound
  let M' := max M 0
  let A := ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*
    (M'^j*Real.exp (M'*h.radius))*B (n-j)
  have hM : 0 ≤ M' := le_max_right _ _
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j hj => by
    have hjB := hB (n-j)
    positivity)
  refine ⟨h.radius^k*A,mul_nonneg (pow_nonneg h.radius_nonneg _) hA,?_⟩
  intro i σ hσ
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (pow_nonneg h.radius_nonneg _) hA)
  intro u
  by_cases hu : |u| ≤ h.radius
  · have he : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (-σ*v)) := by fun_prop
    have hw : ContDiff ℝ ∞ (fun v : ℝ => W i (Real.exp (-v))) :=
      (h.smooth i).comp (Real.contDiff_exp.comp contDiff_id.neg)
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) he hw u (n := n) (mod_cast le_top)
    have hb : ‖iteratedFDeriv ℝ n
        (mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) u‖ ≤ A := by
      change ‖iteratedFDeriv ℝ n (fun v : ℝ =>
        Real.exp (-σ*v) • W i (Real.exp (-v))) u‖ ≤ A
      apply hd.trans
      apply Finset.sum_le_sum
      intro j hj
      have hjB := hB (n-j)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (weight_exp_derivative_bound hM (hσ.trans (le_max_left _ _)) hu j) (by positivity)
      · exact hder (n-j) i u
      · positivity
      · positivity
    simpa only [Real.norm_eq_abs] using
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu k) hb
        (_root_.norm_nonneg _) (pow_nonneg h.radius_nonneg _)
  · have hz : iteratedFDeriv ℝ n
        (mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) u = 0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
        (f := mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) n hn
      have hs' : u ∈ tsupport (fun v : ℝ => W i (Real.exp (-v))) :=
        tsupport_smul_subset_right (fun v : ℝ => Real.exp (-σ*v))
          (fun v : ℝ => W i (Real.exp (-v))) hs
      exact hu (h.support_bound i u hs')
    rw [hz,norm_zero,mul_zero]
    exact mul_nonneg (pow_nonneg h.radius_nonneg _) hA

lemma UniformLogWeights.vertical_bounded {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) :
    Bornology.IsVonNBounded ℝ
      ((fun p : ι × ℝ => mellinVerticalSchwartz (W p.1) (h.compact p.1)
        (h.positive p.1) (h.smooth p.1) p.2) '' {p | |p.2| ≤ M}) := by
  let f : ι × ℝ → 𝓢(ℝ,ℂ) := fun p =>
    mellinLogSchwartz (W p.1) (h.compact p.1) (h.positive p.1) (h.smooth p.1) p.2
  have hb : Bornology.IsVonNBounded ℝ (f '' {p | |p.2| ≤ M}) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro a
    obtain ⟨C,hC,hbound⟩ := h.log_seminorms M a.1 a.2
    exact ⟨C+1,by linarith,fun p hp => (hbound p.1 p.2 hp).trans_lt (by linarith)⟩
  let L : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.compCLM ℝ (by
      simp only [div_eq_mul_inv]
      fun_prop : (fun t : ℝ => t/(2*Real.pi)).HasTemperateGrowth)
      mellin_frequency_growth).comp (SchwartzMap.fourierTransformCLM ℝ)
  convert hb.image L using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Set.image_comp]
  rfl

/-- Uniform rapid decay, derived from support and derivative bounds. -/
theorem UniformLogWeights.mellin_decay {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i σ, |σ| ≤ M → ∀ t : ℝ,
      (1+|t|)^A*‖mellin (W i) ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_finset_seminorm_bounded
      (fun p : ι × ℝ => mellinVerticalSchwartz (W p.1) (h.compact p.1)
        (h.positive p.1) (h.smooth p.1) p.2) |>.mp (h.vertical_bounded M) (Finset.Iic (A,0))
  refine ⟨2^A*C,by positivity,?_⟩
  intro i σ hσ t
  have hp := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (A,0)) (k := A) (n := 0) le_rfl le_rfl
      (mellinVerticalSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) t
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,mellinVerticalSchwartz_apply] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (hb (i,σ) hσ).le (by positivity))

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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularWeightOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed continuous operator from logarithmic test functions to plane
annuli. It makes the angular lattice bounds uniform over the given weights. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology SchwartzMap
namespace CubicFirstMoment

lemma angularComplexCutoff_compact {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasCompactSupport (angularComplexCutoff a b) :=
  (angularPositiveCutoff_compact ha hb).comp_left Complex.ofReal_zero

lemma angularComplexCutoff_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (angularComplexCutoff a b) :=
  Complex.ofRealCLM.contDiff.comp (angularPositiveCutoff_smooth a b)

lemma angularComplexCutoff_positive {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    tsupport (angularComplexCutoff a b) ⊆ Ioi 0 := by
  have he : Function.support (angularComplexCutoff a b) =
      Function.support (angularPositiveCutoff a b) := by
    ext x
    simp only [Function.mem_support,angularComplexCutoff,ne_eq,Complex.ofReal_eq_zero]
  change closure (Function.support _) ⊆ _
  rw [he]
  exact angularPositiveCutoff_positive ha hb

lemma angularWeightOperator_apply (ℓ : ℤ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (F : 𝓢(ℝ,ℂ)) (z : ℂ) :
    angularWeightOperator ℓ a b ha hb F z =
      angularAnnulus ℓ (angularComplexCutoff a b) z *
        F (angularLogExtension (a/2) (2*b) (Complex.normSq z)) := by
  have hq := (angularAnnulus_compact ℓ (angularComplexCutoff_compact ha hb)).hasTemperateGrowth
    (angularAnnulus_smooth ℓ (angularComplexCutoff_positive ha hb) (angularComplexCutoff_smooth a b))
  change (SchwartzMap.smulLeftCLM ℂ (angularAnnulus ℓ (angularComplexCutoff a b))) _ z = _
  rw [SchwartzMap.smulLeftCLM_apply_apply hq]
  rfl

lemma angularWeightOperator_log_apply (ℓ : ℤ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (hsupp : tsupport W ⊆ Icc a b) :
    angularWeightOperator ℓ a b ha hb (mellinLogSchwartz W hW hpos hsm 0) =
      angularAnnulusSchwartz ℓ W hW hpos hsm := by
  ext z
  rw [angularWeightOperator_apply]
  let x := Complex.normSq z
  by_cases hk : angularPositiveCutoff a b x = 0
  · have hw : W x = 0 := by
      by_contra hn
      have hix := hsupp (subset_tsupport _ hn)
      have ho := angularPositiveCutoff_one ha hb hix
      exact zero_ne_one (hk.symm.trans ho)
    change (angularPlanePhase ℓ z*(angularPositiveCutoff a b x:ℂ))*
      mellinLogSchwartz W hW hpos hsm 0 (angularLogExtension (a/2) (2*b) x) =
        angularPlanePhase ℓ z*W x
    simp only [hk,Complex.ofReal_zero,mul_zero,zero_mul,hw]
  · have hx := angularPositiveCutoff_tsupport ha hb (subset_tsupport _ hk)
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
    have hg := angularLogExtension_eq_log (by positivity : 0 < a/2)
      (by positivity : 0 < 2*b) hx
    have hc : (angularPositiveCutoff a b x:ℂ)*W x = W x := by
      by_cases hw : W x = 0
      · simp only [hw,mul_zero]
      · rw [angularPositiveCutoff_one ha hb (hsupp (subset_tsupport _ hw)),
          Complex.ofReal_one,one_mul]
    change (angularPlanePhase ℓ z*(angularPositiveCutoff a b x:ℂ))*
      mellinLogSchwartz W hW hpos hsm 0 (angularLogExtension (a/2) (2*b) x) =
        angularPlanePhase ℓ z*W x
    rw [hg]
    simp only [mellinLogSchwartz_apply,neg_zero,zero_mul,Real.exp_zero,one_smul,neg_neg,Real.exp_log hx0]
    rw [mul_assoc,hc]

theorem UniformLogWeights.angularAnnulus_bounded {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (ℓ : ℤ) :
    Bornology.IsVonNBounded ℝ
      ((fun i => angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i)) '' Set.univ) := by
  let f : ι → 𝓢(ℝ,ℂ) := fun i => mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) 0
  have hb : Bornology.IsVonNBounded ℝ (f '' Set.univ) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro kn
    obtain ⟨C,hC,hbound⟩ := h.log_seminorms 0 kn.1 kn.2
    refine ⟨C+1,by linarith,?_⟩
    intro i _
    exact (hbound i 0 (by simp)).trans_lt (by linarith)
  let L := angularWeightOperator ℓ (Real.exp (-h.radius)) (Real.exp h.radius)
    (Real.exp_pos _) (Real.exp_pos _)
  have he : L '' (f '' Set.univ) =
      ((fun i => angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i)) '' Set.univ) := by
    rw [←Set.image_comp]
    congr 1
    funext i
    exact angularWeightOperator_log_apply ℓ (Real.exp_pos _) (Real.exp_pos _)
      (W i) (h.compact i) (h.positive i) (h.smooth i) (h.annular_support i)
  rw [←he]
  exact hb.image L

theorem UniformLogWeights.angularFourier_seminorm {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (ℓ : ℤ) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i,
      SchwartzMap.seminorm ℝ k n (traceFourierSchwartz
        (angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i))) ≤ C := by
  let f : ι → 𝓢(ℂ,ℂ) := fun i =>
    angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i)
  have hb := (h.angularAnnulus_bounded ℓ).image angularTraceFourierCLM
  rw [←Set.image_comp] at hb
  obtain ⟨C,hC,hbound⟩ :=
    (schwartz_withSeminorms ℝ ℂ ℂ).image_isVonNBounded_iff_seminorm_bounded
      (angularTraceFourierCLM ∘ f) |>.mp hb (k,n)
  exact ⟨C,hC,fun i => (hbound i (Set.mem_univ i)).le⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularUniformPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-area coset estimate with a constant chosen before the weight.
The common Fourier decay is derived by the continuous operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators SchwartzMap
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem schwartz_weighted_dual_bound (F : 𝓢(ℂ,ℂ)) {D : ℝ} (hD : 0 ≤ D)
    (hdecay : ∀ z : ℂ, ‖z‖^4*‖traceFourier F z‖ ≤ D)
    (w : ℂ) (hw : w ≠ 0) (c : Eisenstein → ℂ) (hc : ∀ h, ‖c h‖ ≤ 1) :
    ‖∑' h : Eisenstein, if h = 0 then 0 else c h*traceFourier F ((h:ℂ)/w)‖ ≤
      (D*(∑' h : Eisenstein, (norm h)^(-(2:ℝ)))+1)*(Complex.normSq w)^2 := by
  have hwN : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have hs : Summable (fun h : Eisenstein => if h = 0 then (0:ℂ) else
      c h*traceFourier F ((h:ℂ)/w)) := by
    apply (traceFourier_summable_eisenstein F w hw).norm.of_norm_bounded
    intro h
    by_cases hh : h = 0
    · simp only [hh,ite_true, if_true,norm_zero]
      exact _root_.norm_nonneg _
    · simp only [hh,ite_false, if_false,norm_mul]
      exact mul_le_of_le_one_left (_root_.norm_nonneg _) (hc h)
  have hbound (h : Eisenstein) :
      ‖if h = 0 then (0:ℂ) else c h*traceFourier F ((h:ℂ)/w)‖ ≤
        D*(Complex.normSq w)^2*(norm h)^(-(2:ℝ)) := by
    by_cases hh : h = 0
    · simp only [ite_eq_left hh,norm_zero]
      exact mul_nonneg (mul_nonneg hD (sq_nonneg _)) (Real.rpow_nonneg (norm_nonneg h) _)
    · rw [ite_eq_right hh,norm_mul]
      apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (hc h)).trans
      have hn : 0 < norm h := norm_pos_of_ne_zero hh
      have he : ‖(h:ℂ)/w‖^4 = (norm h)^2/(Complex.normSq w)^2 := by
        rw [show (4:ℕ) = 2*2 by norm_num,pow_mul,←Complex.normSq_eq_norm_sq,
          Complex.normSq_div,div_pow]
        rfl
      have hd := hdecay ((h:ℂ)/w)
      rw [he] at hd
      rw [Real.rpow_neg hn.le,Real.rpow_ofNat]
      apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
      apply (div_le_iff₀ (sq_pos_of_pos hwN)).mp
      convert hd using 1
      all_goals try with_reducible_and_instances rfl
      ring
  calc
    _ ≤ ∑' h : Eisenstein, ‖if h = 0 then (0:ℂ) else c h*traceFourier F ((h:ℂ)/w)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' h : Eisenstein, D*(Complex.normSq w)^2*(norm h)^(-(2:ℝ)) :=
      Summable.tsum_le_tsum hbound hs.norm
        ((summable_eisenstein_norm_rpow (s := 2) (by norm_num)).mul_left _)
    _ = D*(∑' h : Eisenstein, (norm h)^(-(2:ℝ)))*(Complex.normSq w)^2 := by
      rw [tsum_mul_left]
      ring
    _ ≤ _ := by nlinarith [sq_nonneg (Complex.normSq w)]

theorem UniformLogWeights.angular_coset_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ i q, q ≠ 0 → ∀ z : ℂ,
      ‖∑' a : Eisenstein, angularAnnulus ℓ (W i) (z+q*(a:ℂ))‖ ≤ K*Complex.normSq q := by
  obtain ⟨D,hD,hbound⟩ := h.angularFourier_seminorm ℓ 4 0
  let R := ∑' a : Eisenstein, (norm a)^(-(2:ℝ))
  have hR : 0 ≤ R := tsum_nonneg (fun a => Real.rpow_nonneg (norm_nonneg a) _)
  let C := D*R+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨18*C/Real.sqrt 3,by positivity,?_⟩
  intro i q hq z
  let F := angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i)
  have hd : ∀ w : ℂ, ‖w‖^4*‖traceFourier F w‖ ≤ D := by
    intro w
    have hh := SchwartzMap.le_seminorm ℝ 4 0 (traceFourierSchwartz F) w
    simp only [norm_iteratedFDeriv_zero,traceFourierSchwartz_apply] at hh
    exact hh.trans (hbound i)
  have hF : (∫ w : ℂ, F w) = 0 := integral_angularAnnulus_eq_zero hℓ (W i)
  have hN : 0 < Complex.normSq q := Complex.normSq_pos.mpr hq
  have hw : q*traceLambda ≠ 0 := mul_ne_zero hq traceLambda_ne_zero
  let c : Eisenstein → ℂ := fun a =>
    (Real.fourierChar (tracePair z ((a:ℂ)/(q*traceLambda))) : ℂ)
  have hc : ∀ a, ‖c a‖ ≤ 1 := by
    intro a
    exact (Circle.norm_coe _).le
  have hzero : c 0*traceFourier F ((0:ℂ)/(q*traceLambda)) = 0 := by
    simp [traceFourier_zero,hF]
  have he : (∑' a : Eisenstein, c a*traceFourier F ((a:ℂ)/(q*traceLambda))) =
      ∑' a : Eisenstein, if a = 0 then (0:ℂ) else c a*traceFourier F ((a:ℂ)/(q*traceLambda)) := by
    apply tsum_congr
    intro a
    by_cases ha : a = 0
    · subst a
      simpa using hzero
    · simp only [ha,ite_false, if_false]
  change ‖∑' a : Eisenstein, F (z+q*(a:ℂ))‖ ≤ _
  rw [poisson_eisenstein_coset F q hq z]
  change ‖(2/(Real.sqrt 3*Complex.normSq q):ℝ) •
    (∑' a : Eisenstein,c a*traceFourier F ((a:ℂ)/(q*traceLambda)))‖ ≤ _
  rw [he,norm_smul,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (schwartz_weighted_dual_bound F hD.le hd _ hw c hc)
    (by positivity)).trans_eq
  rw [Complex.normSq_mul,traceLambda_normSq]
  dsimp [C,R]
  field_simp
  ring

theorem UniformLogWeights.primaryAngularLattice_decay {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ i Y, 0 < Y → ‖primaryAngularLattice ℓ (W i) Y‖ ≤ K/Y := by
  obtain ⟨C,hC,hbound⟩ := h.angular_coset_bound hℓ
  refine ⟨9*C,by positivity,?_⟩
  intro i Y hY
  let s : ℝ := 1/Real.sqrt Y
  have hs : 0 < s := by dsimp [s]; positivity
  have hq : (s:ℂ)*3 ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne') (by norm_num)
  have hn : Complex.normSq ((s:ℂ)*3) = 9/Y := by
    rw [Complex.normSq_mul,Complex.normSq_ofReal]
    norm_num
    dsimp [s]
    rw [one_div,←pow_two,inv_pow,Real.sq_sqrt hY.le]
    ring
  have he : primaryAngularLattice ℓ (W i) Y = ∑' u : PrimaryArgument,
      angularAnnulus ℓ (W i) ((s:ℂ)*(u:ℂ)) := by
    apply tsum_congr
    intro u
    exact (angularAnnulus_scaled ℓ (W i) hY u).symm
  rw [he,primary_scaled_coset]
  exact (hbound i _ hq _).trans_eq (by rw [hn]; ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularUniformLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform fixed-angular cancellation on the actual primary, coprime,
squarefree lattice. Constants precede every weight and length parameter. -/
noncomputable section
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem UniformLogWeights.primaryAngularLattice_bounded {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ i Y, 0 < Y → ‖primaryAngularLattice ℓ (W i) Y‖ ≤ K := by
  obtain ⟨C,hC,hbound⟩ := h.primaryAngularLattice_decay hℓ
  let S := Real.exp h.radius
  have hS : 0 < S := Real.exp_pos _
  refine ⟨C*S,mul_pos hC hS,?_⟩
  intro i Y hY
  by_cases he : 1 ≤ S*Y
  · apply (hbound i Y hY).trans
    apply (div_le_iff₀ hY).mpr
    nlinarith
  · have hz : primaryAngularLattice ℓ (W i) Y = 0 := by
      have ht (u : PrimaryArgument) : theta ℓ u*W i (norm u/Y) = 0 := by
        have hn := one_le_norm (primary_ne_zero u.property)
        have hw : W i (norm u/Y) = 0 := h.upper_support i _
          ((lt_div_iff₀ hY).mpr ((lt_of_not_ge he).trans_le hn))
        simp only [hw,mul_zero]
      simp only [primaryAngularLattice,ht,tsum_zero]
    rw [hz,norm_zero]
    positivity

theorem UniformLogWeights.primaryCoprimeAngularLattice_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ Y, 0 < Y →
      ‖primaryCoprimeAngularLattice r ℓ (W i) Y‖ ≤ K*norm r^ε := by
  obtain ⟨C,hC,hbound⟩ := h.primaryAngularLattice_bounded hℓ
  obtain ⟨D,hD,hdiv⟩ := primeDivisorWeight_small_power ε hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro i r hr hsr Y hY
  rw [primaryCoprimeAngularLattice_expansion hr hsr ℓ (W i) (h.compact i) (h.smooth i) hY]
  calc
    _ ≤ ∑ s ∈ (primaryPrimeFactors r).powerset,C := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro s hs
      have hd : primary (∏ p ∈ s, p) := primary_finset_prod _ _
        (fun p hp => (primaryPrimeFactor_spec hr (Finset.mem_powerset.mp hs hp)).1.1)
      rw [norm_mul,norm_mul,norm_theta (primary_ne_zero hd),mul_one]
      apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
      exact hbound i _ (div_pos hY (norm_pos_of_ne_zero (primary_ne_zero hd)))
    _ = C*(2:ℝ)^(primaryPrimeFactors r).card := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring
    _ ≤ C*(D*norm r^ε) := mul_le_mul_of_nonneg_left (hdiv r hr hsr) hC.le
    _ = _ := by ring

/-- The angular lattice model, with one constant for the
whole given smooth weight family. -/
theorem UniformLogWeights.squarefreeCoprimeAngularLattice_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ Y, 1 ≤ Y →
      ‖squarefreeCoprimeAngularLattice r ℓ (W i) Y‖ ≤ K*norm r^ε*Real.sqrt Y := by
  obtain ⟨C,hC,hbound⟩ := h.primaryCoprimeAngularLattice_bound hℓ hε
  let S := Real.exp h.radius
  have hS : 0 < S := Real.exp_pos _
  refine ⟨18*Real.sqrt S*C,by positivity,?_⟩
  intro i r hr hsr Y hY
  have hY0 : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hNr : 0 ≤ norm r^ε := Real.rpow_nonneg (norm_nonneg r) _
  let B := squarefreeDivisorTruncation (Real.sqrt (S*Y))
  have hcard : (B.card:ℝ) ≤ 18*Real.sqrt (S*Y) := by
    have hsub : B ⊆ nonzeroNormBall (Real.sqrt (S*Y)) := by
      intro c hc
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (nonzeroNormBall_card_le (Real.sqrt_nonneg _))
  rw [squarefreeCoprimeAngularLattice_expansion r ℓ (W i) (h.compact i) (h.smooth i) hY0
    (h.upper_support i)]
  calc
    _ ≤ ∑ c ∈ B,C*norm r^ε := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro c hc
      have hprim : primary (c^2) := by
        simpa only [pow_two] using primary_mul (mem_squarefreeDivisorTruncation.mp hc).1
          (mem_squarefreeDivisorTruncation.mp hc).1
      by_cases hcop : IsCoprime r (c^2)
      · rw [ite_eq_left hcop,norm_mul,norm_mul,norm_theta (primary_ne_zero hprim),one_mul]
        apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one c)).trans
        exact hbound i r hr hsr _ (div_pos hY0 (norm_pos_of_ne_zero (primary_ne_zero hprim)))
      · simp only [ite_eq_right hcop,mul_zero,norm_zero]
        exact mul_nonneg hC.le hNr
    _ = (B.card:ℝ)*(C*norm r^ε) := by simp
    _ ≤ (18*Real.sqrt (S*Y))*(C*norm r^ε) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hC.le hNr)
    _ = _ := by rw [Real.sqrt_mul hS.le]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformWeightMultiplier
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform support and derivative bounds survive the compact family
of logarithmic-denominator multipliers used in the original coefficients. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma UniformLogWeights.norm_bound {γ : Type*} {W : γ → ℝ → ℂ}
    (h : UniformLogWeights W) : ∃ M : ℝ, 0 ≤ M ∧ ∀ i x, ‖W i x‖ ≤ M := by
  obtain ⟨M,hM,hbound⟩ := h.derivative_bound 0
  refine ⟨M,hM,?_⟩
  intro i x
  by_cases hx : 0 < x
  · have he : Real.exp (-(-Real.log x)) = x := by simp [Real.exp_log hx]
    have hb := hbound i (-Real.log x)
    simpa only [norm_iteratedFDeriv_zero,he] using hb
  · have hz : W i x = 0 := by
      by_contra hn
      have hp := h.positive i (subset_closure hn)
      exact hx hp
    simpa only [hz,norm_zero] using hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLogarithmicLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal low angular model for weights with logarithmic derivative
growth. Every fixed positive power absorbs those derivative costs. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeCoprimeAngularLattice_const_mul (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (U : ℝ) (c : ℂ) :
    squarefreeCoprimeAngularLattice r ℓ (fun x => c*W x) U =
      c*squarefreeCoprimeAngularLattice r ℓ W U := by
  unfold squarefreeCoprimeAngularLattice
  rw [←tsum_mul_left]
  apply tsum_congr
  intro u
  by_cases hu : primary u ∧ IsCoprime r u
  · simp only [hu.1,hu.2,and_self,ite_true, if_true]
    ring
  · simp only [hu,ite_false, if_false,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPowerWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed real powers preserve the actual positive annular weight family.
The smooth extension used in the proof agrees with the power wherever
the original weight is nonzero. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

theorem LogarithmicWeightFamily.power_lattice_bound
    {ι : Type*} {Y : ι → ℝ} {W : ι → ℝ → ℂ} (h : LogarithmicWeightFamily Y W)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) (q : ℝ) {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ U, 1 ≤ U →
      ‖squarefreeCoprimeAngularLattice r ℓ (fun x => ((x^q:ℝ):ℂ)*W i x) U‖ ≤
        K*(Y i)^s*norm r^ε*Real.sqrt U := by
  obtain ⟨K,hK,hbound⟩ := ((h.normalize hs).realPower q).squarefreeCoprimeAngularLattice_bound hℓ hε
  refine ⟨K,hK,?_⟩
  intro i r hr hsr U hU
  have hY : 0 < Y i := zero_lt_one.trans_le (h.length_one i)
  have he : (fun x => ((x^q:ℝ):ℂ)*normalizedLogWeight Y W s i x) =
      (fun x => (((Y i)^(-s):ℝ):ℂ)*(((x^q:ℝ):ℂ)*W i x)) := by
    funext x
    simp only [normalizedLogWeight,Complex.real_smul]
    ring
  have hb := hbound i r hr hsr U hU
  rw [he,squarefreeCoprimeAngularLattice_const_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hY.le _)] at hb
  have hp : (Y i)^s*(Y i)^(-s) = 1 := by
    rw [←Real.rpow_add hY,add_neg_cancel,Real.rpow_zero]
  calc
    _ = (Y i)^s*((Y i)^(-s)*
        ‖squarefreeCoprimeAngularLattice r ℓ (fun x => ((x^q:ℝ):ℂ)*W i x) U‖) := by
      rw [←mul_assoc,hp,one_mul]
    _ ≤ (Y i)^s*(K*norm r^ε*Real.sqrt U) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLatticeModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma idealMoebius_sq_mul_of_squarefree {r : Eisenstein} (hr : Squarefree r)
    (u : Eisenstein) :
    (idealMoebius (r*u):ℂ)^2 = if IsCoprime r u then (idealMoebius u:ℂ)^2 else 0 := by
  simp only [idealMoebius_sq_complex,squarefree_mul_iff,isRelPrime_iff_isCoprime,hr]
  split_ifs <;> simp_all

lemma angularSmoothModel_eq {r : Eisenstein} (hr : Squarefree r)
    (ℓ : ℤ) (W : ℝ → ℂ) {U : ℝ} (hU : 0 < U) :
    angularSmoothModel r ℓ W U =
      (cStar*(norm r*U)^(-1/6:ℝ):ℝ)*theta ℓ r*
        squarefreeCoprimeAngularLattice r ℓ (fun x => ((x^(-1/6:ℝ):ℝ):ℂ)*W x) U := by
  unfold angularSmoothModel squarefreeCoprimeAngularLattice
  rw [←tsum_mul_left]
  apply tsum_congr
  intro u
  rw [idealMoebius_sq_mul_of_squarefree hr]
  by_cases hp : primary u
  · by_cases hc : IsCoprime r u
    · simp only [hp,hc,true_and,ite_true, if_true,theta_mul]
      have he : norm (r*u)^(-1/6:ℝ) =
          (norm r*U)^(-1/6:ℝ)*(norm u/U)^(-1/6:ℝ) := by
        rw [norm_mul_eq,Real.mul_rpow (norm_nonneg r) (norm_nonneg u),
          Real.mul_rpow (norm_nonneg r) hU.le,Real.div_rpow (norm_nonneg u) hU.le]
        have hn : U^(-1/6:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hU _)
        field_simp
      rw [he]
      push_cast
      ring
    · simp only [hp,hc,true_and,ite_true, if_true,ite_false, if_false,mul_zero,zero_mul]
  · simp only [hp,false_and,ite_false, if_false,mul_zero]

theorem LogarithmicWeightFamily.angularSmoothModel_bound
    {ι : Type*} {Y : ι → ℝ} {W : ι → ℝ → ℂ} (h : LogarithmicWeightFamily Y W)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ U, 1 ≤ U →
      ‖angularSmoothModel r ℓ (W i) U‖ ≤
        K*(Y i)^s*norm r^(ε-1/6)*U^(1/3:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := h.power_lattice_bound hℓ (-1/6) hε hs
  refine ⟨|cStar| * K,by have := cStar_pos; positivity,?_⟩
  intro i r hr hsr U hU
  have hnr := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hUp : 0 < U := zero_lt_one.trans_le hU
  rw [angularSmoothModel_eq hsr ℓ (W i) hUp,norm_mul,norm_mul,norm_theta (primary_ne_zero hr),mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (mul_pos hnr hUp) _)]
  calc
    _ ≤ (|cStar| * (norm r*U)^(-1/6:ℝ))*(K*(Y i)^s*norm r^ε*Real.sqrt U) :=
      mul_le_mul_of_nonneg_left (hbound i r hr hsr U hU) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hnr.le hUp.le,Real.sqrt_eq_rpow,
        show ε-1/6 = (-1/6:ℝ)+ε by ring,Real.rpow_add hnr,
        show (1/3:ℝ) = (-1/6:ℝ)+1/2 by norm_num,Real.rpow_add hUp]
      ring

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

/-- For primary factors, fixing the first divisor determines the second. -/
lemma primary_pair_fiber_le_divisors (B : Finset Eisenstein)
    (hB : ∀ a ∈ B, primary a) (n : Eisenstein) :
    ((B.product B).filter (fun z => z.1*z.2 = n)).card ≤
      (B.filter (fun a => a ∣ n)).card := by
  let T := (B.product B).filter (fun z => z.1*z.2 = n)
  have hinj : Set.InjOn Prod.fst (T : Set (Eisenstein × Eisenstein)) := by
    intro a ha b hb he
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply Prod.ext he
    have hn : a.1 ≠ 0 := primary_ne_zero (hB a.1 (Finset.mem_product.mp ha'.1).1)
    apply mul_left_cancel₀ hn
    calc
      a.1*a.2 = n := ha'.2
      _ = b.1*b.2 := hb'.2.symm
      _ = a.1*b.2 := by rw [he]
  have hsub : T.image Prod.fst ⊆ B.filter (fun a => a ∣ n) := by
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hz,hzn⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hz).1,?_⟩
    exact ⟨z.2,hzn.symm⟩
  exact (Finset.card_image_iff.mpr hinj).symm.le.trans (Finset.card_le_card hsub)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorbing the explicit logarithmic factors in the short-polynomial
moments, without making subpower growth an assumption. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma one_add_log_small_power {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 ≤ x → 1+Real.log x ≤ A*x^η := by
  refine ⟨1+1/η,by positivity,?_⟩
  intro x hx
  have hp := Real.one_le_rpow hx hη.le
  have hl := Real.log_le_rpow_div (zero_le_one.trans hx) hη
  calc
    _ ≤ x^η+x^η/η := add_le_add hp hl
    _ = _ := by ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredCoefficientEnergy
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coefficient energy needed by the noncube sieve follows from the
actual independent prime weights, including logarithmic weight families. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma LogarithmicWeightFamily.subpower_norm {L : γ → ℝ} {W : γ → ℝ → ℂ}
    (h : LogarithmicWeightFamily L W) {s : ℝ} (hs : 0 < s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r x, ‖W r x‖ ≤ M*(L r)^s := by
  obtain ⟨M,hM,hbound⟩ := (h.normalize hs).norm_bound
  refine ⟨M,hM,?_⟩
  intro r x
  have hL : 0 < L r := zero_lt_one.trans_le (h.length_one r)
  have hb : (L r)^(-s)*‖W r x‖ ≤ M := by
    simpa only [normalizedLogWeight,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hL.le _)] using hbound r x
  calc
    _ = (L r)^s*((L r)^(-s)*‖W r x‖) := by
      rw [← mul_assoc,← Real.rpow_add hL]; simp
    _ ≤ (L r)^s*M := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hL.le _)
    _ = _ := mul_comm _ _

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
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrimalFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma metaplecticHeightCompleted_zero (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) :
    metaplecticHeightCompleted r ℓ W X 0 = metaplecticCompleted r ℓ W X := by
  unfold metaplecticHeightCompleted metaplecticCompleted
  apply tsum_congr
  intro du
  simp [metaplecticPrimalCoefficient,metaplecticPrimaryPair,metaplecticCubeProduct,mellinPhase]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularModelOuter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of the actual angular lattice model over the level dyad.
This is the model term in the low-height Type-I estimate. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma angularSmoothModel_zero_of_not_squarefree {r : Eisenstein}
    (hr : ¬Squarefree r) (ℓ : ℤ) (W : ℝ → ℂ) (U : ℝ) :
    angularSmoothModel r ℓ W U = 0 := by
  have hs (u : Eisenstein) : ¬Squarefree (r*u) := fun h =>
    hr (Squarefree.squarefree_of_dvd (dvd_mul_right r u) h)
  simp [angularSmoothModel,idealMoebius_sq_complex,hs]

lemma angular_model_outer_power {R U δ : ℝ} (hR : 0 < R) (_hU : 0 < U) :
    R*(R^(δ-1/6)*U^(1/3:ℝ)) = R^δ*R^(5/6:ℝ)*U^(1/3:ℝ) := by
  calc
    _ = (R^(1:ℝ)*R^(δ-1/6))*U^(1/3:ℝ) := by rw [Real.rpow_one]; ring
    _ = R^(1+(δ-1/6))*U^(1/3:ℝ) := by rw [←Real.rpow_add hR]
    _ = R^(δ+5/6)*U^(1/3:ℝ) := by rw [show (1:ℝ)+(δ-1/6) = δ+5/6 by ring]
    _ = _ := by rw [Real.rpow_add hR]

lemma angular_model_level_power {R U : ℝ} (hR : 1 ≤ R) (hU : 1 ≤ U)
    (hRX : R ≤ (R*U)^(51/100:ℝ)) :
    R^(5/6:ℝ)*U^(1/3:ℝ) ≤ (R*U)^(589/1000:ℝ) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hX : 1 ≤ R*U := by nlinarith
  calc
    _ = (R*U)^(1/3:ℝ)*R^(1/2:ℝ) := by
      rw [Real.mul_rpow hRp.le hUp.le,
        show (5/6:ℝ) = 1/3+1/2 by norm_num,Real.rpow_add hRp]
      ring
    _ ≤ (R*U)^(1/3:ℝ)*((R*U)^(51/100:ℝ))^(1/2:ℝ) := by gcongr
    _ = (R*U)^(353/600:ℝ) := by
      rw [←Real.rpow_mul (mul_nonneg hRp.le hUp.le),←Real.rpow_add (mul_pos hRp hUp)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The convergent cube lattice in dispersion

Rapid decay of the actual radial Fourier profile justifies the cube
regrouping. The factor one third is proved from the arithmetic fibers.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eisenstein_norm_pow_lattice (a : Eisenstein) (n : ℕ) : norm (a^n) = (norm a)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,norm_mul_eq,ih,pow_succ]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogarithmicPrimeWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial derivative bounds of a logarithmic family, used to apply
the published prime Siegel–Walfisz input by actual partial summation. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma LogarithmicWeightFamily.norm_log_bound {γ : Type*}
    {L : γ → ℝ} {W : γ → ℝ → ℂ} (h : LogarithmicWeightFamily L W) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ i x, ‖W i x‖ ≤ C*(1+Real.log (L i))^A := by
  obtain ⟨C,A,hC,hbound⟩ := h.derivative_bound 0
  refine ⟨C,A,hC,?_⟩
  intro i x
  by_cases hx : 0 < x
  · have he : Real.exp (-(-Real.log x)) = x := by simp [Real.exp_log hx]
    simpa only [norm_iteratedFDeriv_zero,he] using hbound i (-Real.log x)
  · have hz : W i x = 0 := by
      by_contra hn
      exact hx (h.positive i (subset_closure hn))
    rw [hz,norm_zero]
    exact mul_nonneg hC (pow_nonneg (by linarith [Real.log_nonneg (h.length_one i)]) _)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RadialCubing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three-to-one cubing Jacobian in the radial integral. -/

noncomputable section
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma complex_radial_integral (φ : ℝ → ℂ) :
    (∫ z : ℂ, φ ‖z‖) = (2*Real.pi:ℂ)*(∫ r in Ioi (0:ℝ), (r:ℂ)*φ r) := by
  calc
    _ = ∫ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, (p.1:ℂ)*φ |p.1| := by
      rw [← Complex.integral_comp_polarCoord_symm,polarCoord_target]
      simp only [Complex.norm_polarCoord_symm,Complex.real_smul]
    _ = (∫ r in Ioi (0:ℝ), (r:ℂ)*φ |r|)*(∫ _ in Ioo (-Real.pi) Real.pi, (1:ℂ)) := by
      rw [← setIntegral_prod_mul,volume_eq_prod]
      simp only [mul_one]
    _ = (2*Real.pi:ℂ)*(∫ r in Ioi (0:ℝ), (r:ℂ)*φ r) := by
      have hφ : (∫ r in Ioi (0:ℝ), (r:ℂ)*φ |r|) = ∫ r in Ioi (0:ℝ), (r:ℂ)*φ r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        change (r:ℂ)*φ |r| = (r:ℂ)*φ r
        rw [abs_of_pos hr]
      rw [hφ]
      simp only [integral_const,measureReal_restrict_apply MeasurableSet.univ,
        Set.univ_inter,Complex.real_smul,mul_one]
      rw [Real.volume_real_Ioo_of_le (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos])]
      push_cast
      ring

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

lemma metaplectic_dyad_count_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℝ, 1 ≤ J →
      ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ) ≤ C*J^ε := by
  obtain ⟨D,hD,hd⟩ := metaplectic_dyad_count_log_bound
  obtain ⟨A,hA,ha⟩ := one_add_log_small_power hε
  refine ⟨D*A,mul_pos hD hA,?_⟩
  intro J hJ
  calc
    _ ≤ D*(1+Real.log J) := hd J hJ
    _ ≤ D*(A*J^ε) := mul_le_mul_of_nonneg_left (ha J hJ) hD.le
    _ = _ := by ring

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticForwardCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact forward completion over a finite primary box. This identity
allows the long inverse divisors to be collected by their actual product. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_forward_completion (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) :
    metaplecticCompleted r ℓ W U =
      ∑ d ∈ primaryElementBall F, metaplecticCompletionWeight r ℓ 0 d*
        metaplecticAngularSmoothSum r ℓ W (U/norm d^3) 0 := by
  rw [←metaplecticHeightCompleted_zero r ℓ W U,
    metaplecticHeightCompleted_box r ℓ W hU hBF hW 0]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp := (mem_primaryElementBall.mp hd).1
  have hNd : 0 < norm d := norm_pos_of_ne_zero (primary_ne_zero hdp)
  have hV : 0 < U/norm d^3 := div_pos hU (pow_pos hNd 3)
  have hVU : U/norm d^3 ≤ U := div_le_self hU.le
    (one_le_pow₀ (one_le_norm (primary_ne_zero hdp)))
  have hBV : B*(U/norm d^3) ≤ F := (mul_le_mul_of_nonneg_left hVU hB).trans hBF
  rw [metaplecticAngularSmoothSum_finite r ℓ W hV hBV hW 0,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hup := (mem_primaryElementBall.mp hu).1
  have hf := metaplectic_completion_factor r ℓ 0 hdp hup
  have hw := metaplectic_primal_weight_factor r ℓ W U 0 d u
  simp only [mellinPhase,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one] at hf hw ⊢
  have hn : norm (d^3*u)/U = norm u/(U/norm d^3) := by
    rw [norm_mul_eq,eisenstein_norm_pow]
    field_simp
  rw [hn,←hf] at hw
  rw [←hw]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTailCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal grouped coefficient in the long inverse-completion tail.
Its angular and coprimality phases are retained, while the remaining
Möbius divisor sum is bounded by a proved small norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticTailCoefficient_factor (r : Eisenstein) (ℓ : ℤ) (C F : ℝ)
    (e : Eisenstein) :
    metaplecticTailCoefficient r ℓ C F e =
      metaplecticCompletionWeight r ℓ 0 e*metaplecticTailMoebius C F e := by
  unfold metaplecticTailCoefficient metaplecticTailMoebius
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro cd hcd
  obtain ⟨hmem,he⟩ := Finset.mem_filter.mp hcd
  have hc := (mem_primaryElementBall.mp (Finset.mem_product.mp hmem).1).1
  have hd := (mem_primaryElementBall.mp (Finset.mem_product.mp hmem).2).1
  by_cases hn : C < norm cd.1
  · simp only [hn,ite_true, if_true]
    rw [←he,metaplecticCompletionWeight_mul r ℓ 0 hc hd]
    ring
  · simp only [hn,ite_false, if_false,mul_zero]

/-- Exact collection of the two actual completion divisors into their
product, for any remaining norm-weighted Gauss sum. -/
theorem metaplecticTailCoefficient_collect (r : Eisenstein) (ℓ : ℤ) (C F : ℝ)
    (g : Eisenstein → ℂ) :
    (∑ c ∈ primaryElementBall F, ∑ d ∈ primaryElementBall F,
      (if C < norm c then (idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c*
        metaplecticCompletionWeight r ℓ 0 d else 0)*g (c*d)) =
      ∑ e ∈ ((primaryElementBall F).product (primaryElementBall F)).image
        (fun cd => cd.1*cd.2), metaplecticTailCoefficient r ℓ C F e*g e := by
  let P := (primaryElementBall F).product (primaryElementBall F)
  let f : Eisenstein × Eisenstein → ℂ := fun cd =>
    (if C < norm cd.1 then (idealMoebius cd.1:ℂ)*metaplecticCompletionWeight r ℓ 0 cd.1*
      metaplecticCompletionWeight r ℓ 0 cd.2 else 0)*g (cd.1*cd.2)
  rw [←Finset.sum_product']
  change (∑ cd ∈ P, f cd) = _
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun cd hcd => Finset.mem_image_of_mem (fun cd : Eisenstein × Eisenstein => cd.1*cd.2) hcd) f]
  apply Finset.sum_congr rfl
  intro e _
  rw [metaplecticTailCoefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro cd hcd
  dsimp only [f]
  rw [(Finset.mem_filter.mp hcd).2]

lemma metaplecticTailMoebius_zero {e : Eisenstein} (he : primary e) {C F : ℝ}
    (hC : norm e ≤ C) : metaplecticTailMoebius C F e = 0 := by
  apply Finset.sum_eq_zero
  intro cd hcd
  have hd := (Finset.mem_filter.mp hcd).2
  have hn : norm cd.1 ≤ norm e := norm_le_of_dvd (primary_ne_zero he) ⟨cd.2,hd.symm⟩
  exact ite_eq_right (not_lt_of_ge (hn.trans hC))

lemma metaplecticTailCoefficient_zero (r : Eisenstein) (ℓ : ℤ)
    {e : Eisenstein} (he : primary e) {C F : ℝ} (hC : norm e ≤ C) :
    metaplecticTailCoefficient r ℓ C F e = 0 := by
  rw [metaplecticTailCoefficient_factor,metaplecticTailMoebius_zero he hC,mul_zero]

theorem metaplecticTailMoebius_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (C F : ℝ) (e : Eisenstein), primary e →
      ‖metaplecticTailMoebius C F e‖ ≤ D*norm e^ε := by
  obtain ⟨D,hD,hdiv⟩ := primary_divisor_card_small_power hε
  refine ⟨D,hD,?_⟩
  intro C F e he
  have hp (c : Eisenstein) (hc : c ∈ primaryElementBall F) : primary c :=
    (mem_primaryElementBall.mp hc).1
  have hcard : ((metaplecticTailPairs F e).card:ℝ) ≤ D*norm e^ε :=
    (Nat.cast_le.mpr (primary_pair_fiber_le_divisors _ hp e)).trans
      (hdiv _ hp e (primary_ne_zero he))
  unfold metaplecticTailMoebius
  calc
    _ ≤ ∑ cd ∈ metaplecticTailPairs F e,
        ‖if C < norm cd.1 then (idealMoebius cd.1:ℂ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _cd ∈ metaplecticTailPairs F e, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro cd _
      split_ifs
      · exact norm_idealMoebius_le_one _
      · simp
    _ = ((metaplecticTailPairs F e).card:ℝ) := by simp
    _ ≤ _ := hcard

theorem metaplecticTailCoefficient_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r : Eisenstein) (ℓ : ℤ) (C F : ℝ) (e : Eisenstein), primary e →
      ‖metaplecticTailCoefficient r ℓ C F e‖ ≤ D*norm e^(1/2+ε) := by
  obtain ⟨D,hD,hbound⟩ := metaplecticTailMoebius_bound hε
  refine ⟨D,hD,?_⟩
  intro r ℓ C F e he
  have hw : ‖metaplecticCompletionWeight r ℓ 0 e‖ ≤ Real.sqrt (norm e) := by
    rw [norm_metaplecticCompletionWeight he]
    split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  rw [metaplecticTailCoefficient_factor,norm_mul]
  calc
    _ ≤ Real.sqrt (norm e)*(D*norm e^ε) :=
      mul_le_mul hw (hbound C F e he) (_root_.norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,Real.rpow_add (norm_pos_of_ne_zero (primary_ne_zero he))]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLongCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual long inverse-completion sum, collected by e=cd.
The resulting weight is the proved tail coefficient, not an arbitrary
divisor-bounded replacement. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_long_completion_collect (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (C : ℝ) :
    metaplecticLongCompletion r ℓ W U C F =
      ∑ e ∈ ((primaryElementBall F).product (primaryElementBall F)).image
        (fun cd => cd.1*cd.2), metaplecticTailCoefficient r ℓ C F e*
          metaplecticAngularSmoothSum r ℓ W (U/norm e^3) 0 := by
  rw [←metaplecticTailCoefficient_collect]
  unfold metaplecticLongCompletion
  apply Finset.sum_congr rfl
  intro c hc
  have hcp := (mem_primaryElementBall.mp hc).1
  have hNc := norm_pos_of_ne_zero (primary_ne_zero hcp)
  have hV : 0 < U/norm c^3 := div_pos hU (pow_pos hNc 3)
  have hVU : U/norm c^3 ≤ U := div_le_self hU.le
    (one_le_pow₀ (one_le_norm (primary_ne_zero hcp)))
  have hBV : B*(U/norm c^3) ≤ F := (mul_le_mul_of_nonneg_left hVU hB).trans hBF
  by_cases hC : C < norm c
  · rw [ite_eq_left hC,metaplectic_forward_completion r ℓ W hV hB hBV hW,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [ite_eq_left hC]
    have he : U/norm c^3/norm d^3 = U/norm (c*d)^3 := by
      rw [norm_mul_eq,mul_pow]
      field_simp
    rw [he]
    ring
  · simp only [hC,ite_false, if_false,zero_mul,Finset.sum_const_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticInverseSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact short/long splitting of the original finite inverse completion.
The short residue sum remains explicit, and vanishes at nonzero angular index. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryElementBall_filter_norm {C F : ℝ} (hCF : C ≤ F) :
    (primaryElementBall F).filter (fun c => norm c ≤ C) = primaryElementBall C := by
  ext c
  simp only [Finset.mem_filter,mem_primaryElementBall]
  constructor
  · rintro ⟨⟨hp,_⟩,hn⟩
    exact ⟨hp,hn⟩
  · rintro ⟨hp,hn⟩
    exact ⟨⟨hp,hn.trans hCF⟩,hn⟩

theorem metaplectic_inverse_split (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B C F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F) (hCF : C ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) :
    metaplecticAngularSmoothSum r ℓ W U 0 =
      metaplecticShortCompletionError r ℓ W U C+
        (∑ c ∈ primaryElementBall C, ((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c)*
          metaplecticMain r ℓ W (U/norm c^3))+
        metaplecticLongCompletion r ℓ W U C F := by
  let f : Eisenstein → ℂ := fun c =>
    ((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c)*
      metaplecticCompleted r ℓ W (U/norm c^3)
  have hi : metaplecticAngularSmoothSum r ℓ W U 0 = ∑ c ∈ primaryElementBall F, f c := by
    rw [metaplectic_angular_actual_inverse r ℓ W hU hB hBF hW 0]
    simp only [metaplecticHeightCompleted_zero]
    rfl
  have hlong : (∑ c ∈ (primaryElementBall F).filter (fun c => ¬norm c ≤ C), f c) =
      metaplecticLongCompletion r ℓ W U C F := by
    rw [Finset.sum_filter]
    simp only [not_le,metaplecticLongCompletion,f]
  have hsplit := Finset.sum_filter_add_sum_filter_not (primaryElementBall F)
    (fun c => norm c ≤ C) f
  rw [primaryElementBall_filter_norm hCF,hlong] at hsplit
  rw [hi,←hsplit]
  congr 1
  rw [metaplecticShortCompletionError,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  dsimp [f]
  ring

theorem metaplectic_angular_inverse_split (r : Eisenstein) {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    (W : ℝ → ℂ) {U B C F : ℝ} (hU : 0 < U) (hB : 0 ≤ B)
    (hBF : B*U ≤ F) (hCF : C ≤ F) (hW : ∀ x : ℝ, B < x → W x = 0) :
    metaplecticAngularSmoothSum r ℓ W U 0 =
      metaplecticShortCompletionError r ℓ W U C+metaplecticLongCompletion r ℓ W U C F := by
  rw [metaplectic_inverse_split r ℓ W hU hB hBF hCF hW]
  simp only [metaplecticMain,hℓ,ite_false, if_false,mul_zero,Finset.sum_const_zero,add_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCutoffPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two explicit cutoffs in the low-height Type-I argument.
Only elementary real power inequalities are used here. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_short_cutoff_power {X R p q : ℝ}
    (hX : 1 ≤ X) (hR : 0 ≤ R) (hRX : R ≤ X^p) :
    R^(3/2:ℝ)*(X^q)^(3/2:ℝ) ≤ X^((p+q)*(3/2:ℝ)) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  calc
    _ ≤ (X^p)^(3/2:ℝ)*(X^q)^(3/2:ℝ) := by gcongr
    _ = _ := by
      rw [←Real.rpow_mul hXp.le,←Real.rpow_mul hXp.le,←Real.rpow_add hXp]
      congr 1
      ring

lemma metaplectic_short_small_power {X R : ℝ}
    (hX : 1 ≤ X) (hR : 0 ≤ R) (hRX : R ≤ X^(2/5:ℝ)) :
    R^(3/2:ℝ)*(X^(13/100:ℝ))^(3/2:ℝ) ≤ X^(159/200:ℝ) := by
  convert metaplectic_short_cutoff_power (q := (13/100:ℝ)) hX hR hRX using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

lemma metaplectic_short_large_power {X R : ℝ}
    (hX : 1 ≤ X) (hR : 0 ≤ R) (hRX : R ≤ X^(51/100:ℝ)) :
    R^(3/2:ℝ)*(X^(1/50:ℝ))^(3/2:ℝ) ≤ X^(159/200:ℝ) := by
  convert metaplectic_short_cutoff_power (q := (1/50:ℝ)) hX hR hRX using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

lemma metaplectic_large_length {X R U : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (hRU : R*U = X)
    (hRX : X^(2/5:ℝ) ≤ R) : U ≤ X^(3/5:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have he : U = X/R := by rw [←hRU]; field_simp
  rw [he]
  calc
    _ ≤ X/X^(2/5:ℝ) := div_le_div_of_nonneg_left hXp.le
      (Real.rpow_pos_of_pos hXp _) hRX
    _ = _ := by
      conv_lhs => lhs; rw [←Real.rpow_one X]
      rw [←Real.rpow_sub hXp]
      norm_num

lemma metaplectic_large_sieve_power {X R U : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (_hU : 0 ≤ U) (hRU : R*U = X)
    (hRlo : X^(2/5:ℝ) ≤ R) (hRhi : R ≤ X^(51/100:ℝ)) :
    X*(R+U/(X^(1/50:ℝ))^3+(X/(X^(1/50:ℝ))^3)^(2/3:ℝ)) ≤
      3*X^(122/75:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hc : (X^(1/50:ℝ))^3 = X^(3/50:ℝ) := by
    rw [←Real.rpow_mul_natCast hXp.le]
    norm_num
  have hUhi := metaplectic_large_length hX hR hRU hRlo
  have hu : U/(X^(1/50:ℝ))^3 ≤ X^(27/50:ℝ) := by
    rw [hc]
    calc
      _ ≤ X^(3/5:ℝ)/X^(3/50:ℝ) := div_le_div_of_nonneg_right hUhi (by positivity)
      _ = _ := by rw [←Real.rpow_sub hXp]; norm_num
  have hx : (X/(X^(1/50:ℝ))^3)^(2/3:ℝ) = X^(47/75:ℝ) := by
    rw [hc]
    conv_lhs => lhs; lhs; rw [←Real.rpow_one X]
    rw [←Real.rpow_sub hXp,←Real.rpow_mul hXp.le]
    norm_num
  have hr' : R ≤ X^(47/75:ℝ) := hRhi.trans
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num))
  have hu' : U/(X^(1/50:ℝ))^3 ≤ X^(47/75:ℝ) := hu.trans
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num))
  calc
    _ ≤ X*(X^(47/75:ℝ)+X^(47/75:ℝ)+X^(47/75:ℝ)) := by
      rw [hx]
      gcongr
    _ = 3*(X^(1:ℝ)*X^(47/75:ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [←Real.rpow_add hXp]; norm_num

lemma metaplectic_large_sieve_fixed_support {X R U B : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (hU : 0 ≤ U) (hB : 0 ≤ B)
    (hRU : R*U = X) (hRlo : X^(2/5:ℝ) ≤ R) (hRhi : R ≤ X^(51/100:ℝ)) :
    X*(2*R+8*B*U/(X^(1/50:ℝ))^3+
        (16*B*X/(X^(1/50:ℝ))^3)^(2/3:ℝ)) ≤
      (3*(2+8*B+(16*B)^(2/3:ℝ)))*X^(122/75:ℝ) := by
  let C : ℝ := 2+8*B+(16*B)^(2/3:ℝ)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hp : 0 ≤ (16*B)^(2/3:ℝ) := Real.rpow_nonneg (by positivity) _
  have hc2 : 2 ≤ C := by dsimp [C]; linarith
  have hc8 : 8*B ≤ C := by dsimp [C]; linarith
  have hc16 : (16*B)^(2/3:ℝ) ≤ C := by dsimp [C]; linarith
  have hx0 : 0 ≤ X := le_trans zero_le_one hX
  have hscale : (16*B*X/(X^(1/50:ℝ))^3)^(2/3:ℝ) =
      (16*B)^(2/3:ℝ)*(X/(X^(1/50:ℝ))^3)^(2/3:ℝ) := by
    rw [show 16*B*X/(X^(1/50:ℝ))^3 = (16*B)*(X/(X^(1/50:ℝ))^3) by ring,
      Real.mul_rpow (by positivity : 0 ≤ 16*B) (by positivity)]
  calc
    _ = X*(2*R+(8*B)*(U/(X^(1/50:ℝ))^3)+
        (16*B)^(2/3:ℝ)*(X/(X^(1/50:ℝ))^3)^(2/3:ℝ)) := by rw [hscale]; ring
    _ ≤ X*(C*R+C*(U/(X^(1/50:ℝ))^3)+C*(X/(X^(1/50:ℝ))^3)^(2/3:ℝ)) := by
      gcongr
    _ = C*(X*(R+U/(X^(1/50:ℝ))^3+(X/(X^(1/50:ℝ))^3)^(2/3:ℝ))) := by ring
    _ ≤ C*(3*X^(122/75:ℝ)) := mul_le_mul_of_nonneg_left
      (metaplectic_large_sieve_power hX hR hU hRU hRlo hRhi) hC0
    _ = _ := by dsimp [C]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLongDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual long inverse sum has a finite, canonical norm-dyad
partition. Each nonempty block lies above half the inverse cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticLongSupport_primary {C F : ℝ} {e : Eisenstein}
    (he : e ∈ metaplecticLongSupport C F) : primary e := by
  obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
  exact primary_mul (mem_primaryElementBall.mp hc).1 (mem_primaryElementBall.mp hd).1

lemma metaplecticLongSupport_norm {C F : ℝ} (hF : 0 ≤ F) {e : Eisenstein}
    (he : e ∈ metaplecticLongSupport C F) : norm e ≤ F^2 := by
  obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
  rw [norm_mul_eq,pow_two]
  exact mul_le_mul (mem_primaryElementBall.mp hc).2 (mem_primaryElementBall.mp hd).2
    (norm_nonneg _) hF

lemma metaplecticLongDyad_norm {C F : ℝ} {j : ℕ} {e : Eisenstein}
    (he : e ∈ metaplecticLongDyad C F j) :
    primary e ∧ (2:ℝ)^j ≤ norm e ∧ norm e ≤ 2*(2:ℝ)^j := by
  obtain ⟨hs,hj⟩ := Finset.mem_filter.mp he
  have hp := metaplecticLongSupport_primary hs
  have hd : e ∈ frequencyDyad j := mem_frequencyDyad.mpr ⟨primary_ne_zero hp,hj⟩
  have hn := frequencyDyad_norm hd
  exact ⟨hp,hn.1,hn.2⟩

lemma metaplecticLongDyad_cutoff {C F : ℝ} {j : ℕ}
    (hj : j ∈ metaplecticLongDyads C F) : C < 2*(2:ℝ)^j := by
  obtain ⟨e,he,hlog⟩ := Finset.mem_image.mp hj
  have hmem : e ∈ metaplecticLongDyad C F j := Finset.mem_filter.mpr ⟨he,hlog⟩
  exact (Finset.mem_filter.mp he).2.trans_le (metaplecticLongDyad_norm hmem).2.2

lemma metaplecticLongDyads_card {C F : ℝ} (hF : 0 ≤ F) :
    (metaplecticLongDyads C F).card ≤ Nat.log 2 ⌊F^2⌋₊+1 := by
  have hsub : metaplecticLongDyads C F ⊆ Finset.range (Nat.log 2 ⌊F^2⌋₊+1) := by
    intro j hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    apply Nat.le_floor
    simpa only [normNat_cast] using metaplecticLongSupport_norm hF he
  simpa only [Finset.card_range] using Finset.card_le_card hsub

theorem metaplectic_long_completion_active (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (C : ℝ) :
    metaplecticLongCompletion r ℓ W U C F =
      ∑ e ∈ metaplecticLongSupport C F, metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ W (U/norm e^3) 0 := by
  rw [metaplectic_long_completion_collect r ℓ W hU hB hBF hW C]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hn
  have hp : primary e := by
    obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    exact primary_mul (mem_primaryElementBall.mp hc).1 (mem_primaryElementBall.mp hd).1
  have hCe : norm e ≤ C := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨he,lt_of_not_ge h⟩)
  rw [metaplecticTailCoefficient_zero r ℓ hp hCe,zero_mul]

lemma metaplectic_long_dyad_partition (C F : ℝ) (f : Eisenstein → ℂ) :
    (∑ e ∈ metaplecticLongSupport C F, f e) =
      ∑ j ∈ metaplecticLongDyads C F, ∑ e ∈ metaplecticLongDyad C F j, f e := by
  exact (Finset.sum_fiberwise_of_maps_to
    (fun e he => Finset.mem_image_of_mem (fun e => Nat.log 2 (normNat e)) he) f).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLongCard
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite inverse-completion dyad count is a subpower of
the finite completion cutoff. -/
noncomputable section
namespace CubicFirstMoment

theorem metaplecticLongDyads_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ C F : ℝ, 1 ≤ F →
      ((metaplecticLongDyads C F).card:ℝ) ≤ K*F^ε := by
  obtain ⟨K,hK,hbound⟩ := metaplectic_dyad_count_small_power (half_pos hε)
  refine ⟨K,hK,?_⟩
  intro C F hF
  have hF0 : 0 ≤ F := le_trans zero_le_one hF
  have hcard : (metaplecticLongDyads C F).card ≤ Nat.log 2 ⌊3*F^2⌋₊+1 := by
    apply (metaplecticLongDyads_card hF0).trans
    apply Nat.add_le_add_right
    apply Nat.log_mono_right
    apply Nat.floor_mono
    nlinarith [sq_nonneg F]
  calc
    _ ≤ ((Nat.log 2 ⌊3*(F^2)⌋₊+1:ℕ):ℝ) := Nat.cast_le.mpr hcard
    _ ≤ K*(F^2)^(ε/2) := hbound (F^2) (one_le_pow₀ hF)
    _ = _ := by
      rw [←Real.rpow_natCast F 2,←Real.rpow_mul hF0]
      congr 2
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTrivialSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal point-count bound for the original smooth angular Gauss
sum, valid also below the first nonzero norm. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem metaplecticAngularSmoothSum_trivial {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) {V B M : ℝ} (hV : 0 < V) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hcut : ∀ x : ℝ, B < x → W x = 0) (hW : ∀ x, ‖W x‖ ≤ M) :
    ‖metaplecticAngularSmoothSum r ℓ W V 0‖ ≤ 18*B*M*V := by
  rw [metaplecticAngularSmoothSum_finite r ℓ W hV (le_refl (B*V)) hcut 0]
  have hb (u : Eisenstein) (hu : u ∈ primaryElementBall (B*V)) :
      ‖W (norm u/V)*(gauss (r*u)*theta ℓ (r*u)*mellinPhase 0 (norm u))‖ ≤ M := by
    have hp := primary_mul hr (mem_primaryElementBall.mp hu).1
    simp only [mellinPhase,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one,
      norm_mul,norm_theta (primary_ne_zero hp),mul_one]
    exact (mul_le_mul_of_nonneg_left (norm_gauss_le_one hp) (_root_.norm_nonneg _)).trans
      (by simpa only [mul_one] using hW (norm u/V))
  calc
    _ ≤ ∑ u ∈ primaryElementBall (B*V), M :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hb)
    _ = ((primaryElementBall (B*V)).card:ℝ)*M := by simp
    _ ≤ (18*(B*V))*M := mul_le_mul_of_nonneg_right
      (primaryElementBall_card_le (mul_nonneg hB hV.le)) hM
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLogTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long-tail cubic estimate for the original logarithmically
varying weights, obtained by exact scalar normalization. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplecticAngularSmoothSum_const_mul (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (U t : ℝ) (z : ℂ) :
    metaplecticAngularSmoothSum r ℓ (fun x => z*W x) U t =
      z*metaplecticAngularSmoothSum r ℓ W U t := by
  unfold metaplecticAngularSmoothSum
  rw [←tsum_mul_left]
  apply tsum_congr
  intro u
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLargeLow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual long inverse tail in the large-level branch of low Type I.
The source cutoff is X^(1/50); the completion cutoff is the harmless X^2. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem LogarithmicWeightFamily.metaplectic_long_large_power
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {B D : ℝ} (hB : 1 ≤ B) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (ℓ : ℤ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X →
      X^(2/5:ℝ) ≤ R → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) ≤ X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∑ r ∈ S, ‖α r‖^2) ≤ D*R*X^(2*κ) →
      ‖∑ r ∈ S, α r*metaplecticLongCompletion r ℓ (W (w r)) U
        (X^(1/50:ℝ)) (X^2)‖ ≤ K*X^(41/50:ℝ) := by
  obtain ⟨A,hA,hbound⟩ := hW.metaplectic_long_sieve
    (by norm_num : 0 < κ) (by norm_num : κ ≤ 1) (by norm_num : 0 < κ)
  obtain ⟨J,hJ,hcard⟩ := metaplecticLongDyads_small_power (by norm_num : 0 < κ)
  let C : ℝ := A*J^2*D*B*(2*B)^κ
  let H : ℝ := 3*(2+8*B+(16*B)^(2/3:ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨Real.sqrt (C*H),Real.sqrt_nonneg _,?_⟩
  intro w S α ℓ X R U hX hBX hR hU hRU hRlo hRhi hS hY hcut henergy
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hRp : 0 < R := by linarith
  have hUp : 0 < U := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left hUp.le hR
  have hBU : B*U ≤ X^2 := by nlinarith [mul_le_mul hBX hUX hUp.le hXp.le]
  have hc : ((metaplecticLongDyads (X^(1/50:ℝ)) (X^2)).card:ℝ) ≤ J*X^(2*κ) := by
    apply (hcard _ _ (one_le_pow₀ hX1)).trans_eq
    rw [←Real.rpow_natCast X 2,←Real.rpow_mul hXp.le]
    congr 2
  have hn : (2*R*(B*U))^κ = (2*B)^κ*X^κ := by
    rw [show 2*R*(B*U) = (2*B)*(R*U) by ring,hRU,Real.mul_rpow (by positivity) hXp.le]
  have hf : (X^2)^(4*κ) = X^(8*κ) := by
    rw [←Real.rpow_natCast X 2,←Real.rpow_mul hXp.le]
    congr 1
    ring
  have hpow : (X^(2*κ))^2 = X^(4*κ) := by
    rw [←Real.rpow_mul_natCast hXp.le]
    congr 1
    norm_num
  have hp : X^(4*κ)*X^(2*κ)*X^κ*X^(8*κ)*X^(2*κ) = X^(17*κ) := by
    rw [←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp]
    congr 1
    ring
  let Q : ℝ := 2*R+8*B*U/(X^(1/50:ℝ))^3+(16*B*X/(X^(1/50:ℝ))^3)^(2/3:ℝ)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hb := hbound w S X (2*R) U B (X^(1/50:ℝ)) (X^2)
    hX1 (by linarith) hUp hB0 (by positivity) (one_le_pow₀ hX1) hBU hS hY hcut α ℓ
  have hsq : ‖∑ r ∈ S, α r*metaplecticLongCompletion r ℓ (W (w r)) U
      (X^(1/50:ℝ)) (X^2)‖^2 ≤ (C*H)*X^(41/25:ℝ) := by
    apply hb.trans
    have hshape : 2*R+8*B*U/(X^(1/50:ℝ))^3+
        (8*(2*R)*B*U/(X^(1/50:ℝ))^3)^(2/3:ℝ) = Q := by
      dsimp [Q]
      rw [show 8*(2*R)*B*U = 16*B*(R*U) by ring,hRU]
    rw [hshape]
    calc
      _ ≤ A*(J*X^(2*κ))^2*X^(2*κ)*(2*R*(B*U))^κ*(B*U)*(X^2)^(4*κ)*Q*
          (D*R*X^(2*κ)) := by gcongr
      _ = C*X^(17*κ)*(X*Q) := by
        rw [mul_pow,hpow,hn,hf]
        calc
          _ = (A*J^2*D*B*(2*B)^κ)*(X^(4*κ)*X^(2*κ)*X^κ*X^(8*κ)*X^(2*κ))*((R*U)*Q) := by ring
          _ = _ := by rw [hp,hRU]
      _ ≤ C*X^(17*κ)*(H*X^(122/75:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact metaplectic_large_sieve_fixed_support hX1 hRp hUp.le hB0 hRU hRlo hRhi
      _ = (C*H)*X^(17*κ+122/75) := by rw [Real.rpow_add hXp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (mul_nonneg hC hH)
  have htarget : (Real.sqrt (C*H)*X^(41/50:ℝ))^2 = (C*H)*X^(41/25:ℝ) := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hC hH),←Real.rpow_mul_natCast hXp.le]
    norm_num
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mp (hsq.trans_eq htarget.symm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLevelMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual primary divisor bound supplies both outer coefficient
masses needed by the counting and cubic-sieve parts of Type I. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_level_masses (S : Finset Eisenstein) (α : Eisenstein → ℂ)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hS : ∀ r ∈ S, primary r ∧ norm r ≤ 2*R)
    (hα : ∀ r ∈ S, ‖α r‖ ≤ M) :
    (∑ r ∈ S, ‖α r‖) ≤ 36*R*M ∧ (∑ r ∈ S, ‖α r‖^2) ≤ 36*R*M^2 := by
  have hsub : S ⊆ primaryElementBall (2*R) := fun r hr => mem_primaryElementBall.mpr (hS r hr)
  have hc : (S.card:ℝ) ≤ 36*R :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      ((primaryElementBall_card_le (by positivity)).trans_eq (by ring))
  constructor
  · calc
      _ ≤ ∑ _r ∈ S, M := Finset.sum_le_sum hα
      _ = (S.card:ℝ)*M := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hM
  · calc
      _ ≤ ∑ _r ∈ S, M^2 := Finset.sum_le_sum
        (fun r hr => pow_le_pow_left₀ (_root_.norm_nonneg _) (hα r hr) 2)
      _ = (S.card:ℝ)*M^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg _)

theorem metaplectic_divisor_coefficient_power {ε A : ℝ} (hε : 0 < ε)
    (hA : 0 ≤ A) (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (r : Eisenstein), primary r →
      ∀ X : ℝ, 1 ≤ X → norm r ≤ 2*X → ∀ z : ℂ,
      ‖z‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k → ‖z‖ ≤ D*X^ε := by
  let δ : ℝ := ε/((k:ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have he : δ*(k:ℝ) ≤ ε := by
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
    have hd : δ*((k:ℝ)+1) = ε := by
      dsimp [δ]
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨C,hC,hdiv⟩ := primary_divisor_card_small_power hδ
  refine ⟨A*C^k*2^ε,by positivity,?_⟩
  intro r hr X hX hNr z hz
  have hnr : 1 ≤ norm r := one_le_norm (primary_ne_zero hr)
  have hc : ((metaplecticPrimaryDivisors r).card:ℝ) ≤ C*norm r^δ := by
    exact hdiv (primaryElementBall (norm r))
      (fun a ha => (mem_primaryElementBall.mp ha).1) r (primary_ne_zero hr)
  have hp : norm r^(δ*(k:ℝ)) ≤ (2*X)^ε :=
    (Real.rpow_le_rpow_of_exponent_le hnr he).trans
      (Real.rpow_le_rpow (norm_nonneg _) hNr hε.le)
  calc
    _ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k := hz
    _ ≤ A*(C*norm r^δ)^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hc k) hA
    _ = (A*C^k)*norm r^(δ*(k:ℝ)) := by
      rw [mul_pow,←Real.rpow_mul_natCast (norm_nonneg r)]
      ring
    _ ≤ (A*C^k)*(2*X)^ε := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith : 0 ≤ X)]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticShortLogInverse
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short inverse-completion error for the original logarithmically
varying weights, in both the radial and fixed angular modes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticMain_const_mul (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U : ℝ) (z : ℂ) :
    metaplecticMain r ℓ (fun x => z*W x) U = z*metaplecticMain r ℓ W U := by
  have hm : mellin (fun x => z*W x) (5/6) = z*mellin W (5/6) := by
    simpa only [smul_eq_mul] using mellin_const_smul W (5/6) z
  unfold metaplecticMain
  split_ifs
  · rw [hm]
    ring
  · exact (mul_zero _).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticSelectedOuter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform outer estimates with the weight selected independently for
each actual level. Constants precede the selector and the finite level set. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem LogarithmicWeightFamily.angular_selected_model
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδsmall : δ ≤ 1/6) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      1 ≤ X → 0 < R → 1 ≤ U →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ R ≤ norm r) →
      (∀ r ∈ S, Y (w r) ≤ X) →
      ‖∑ r ∈ S, α r*angularSmoothModel r ℓ (W (w r)) U‖ ≤
        K*X^ε*R^(δ-1/6)*U^(1/3:ℝ)*(∑ r ∈ S, ‖α r‖) := by
  obtain ⟨K,hK,hbound⟩ := hW.angularSmoothModel_bound hℓ hδ hε
  refine ⟨K,hK.le,?_⟩
  intro w S α X R U _hX hR hU hS hY
  have hbnd (r : Eisenstein) (hr : r ∈ S) :
      ‖angularSmoothModel r ℓ (W (w r)) U‖ ≤ K*X^ε*R^(δ-1/6)*U^(1/3:ℝ) := by
    obtain ⟨hp,hs,hn⟩ := hS r hr
    apply (hbound (w r) r hp hs U hU).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith [hW.length_one (w r)]) (hY r hr) hε.le) hK.le)
      (Real.rpow_le_rpow_of_nonpos hR hn (by linarith))
      (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  calc
    _ ≤ ∑ r ∈ S, ‖α r‖*‖angularSmoothModel r ℓ (W (w r)) U‖ := by
      simpa only [norm_mul] using norm_sum_le S (fun r => α r*angularSmoothModel r ℓ (W (w r)) U)
    _ ≤ ∑ r ∈ S, ‖α r‖*(K*X^ε*R^(δ-1/6)*U^(1/3:ℝ)) :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hbnd r hr) (_root_.norm_nonneg _))
    _ = _ := by rw [←Finset.sum_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticShortModelLow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Power-saving forms of the actual short completion error and the
nonzero-angular lattice model, with the source level geometry. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem LogarithmicWeightFamily.angular_model_low_power
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ R ≤ norm r) →
      (∀ r ∈ S, Y (w r) ≤ X) →
      (∑ r ∈ S, ‖α r‖) ≤ D*R*X^κ →
      ‖∑ r ∈ S, α r*angularSmoothModel r ℓ (W (w r)) U‖ ≤ K*X^(41/50:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := hW.angular_selected_model hℓ
    (by norm_num : 0 < κ) (by norm_num : 0 < κ) (by norm_num : κ ≤ 1/6)
  refine ⟨K*D,mul_nonneg hK hD,?_⟩
  intro w S α X R U hX hR hU hRU hRhi hS hY hmass
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hRp : 0 < R := by linarith
  have hUp : 0 < U := by linarith
  have hRX : R ≤ X := by rw [←hRU]; exact le_mul_of_one_le_right hRp.le hU
  have hb := hbound w S α X R U hX1 hRp hU hS hY
  have hp := angular_model_level_power hR hU (by simpa only [hRU] using hRhi)
  rw [hRU] at hp
  apply hb.trans
  calc
    _ ≤ K*X^κ*R^(κ-1/6)*U^(1/3:ℝ)*(D*R*X^κ) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (K*D)*(X^κ*X^κ)*(R*(R^(κ-1/6)*U^(1/3:ℝ))) := by ring
    _ = (K*D)*X^(2*κ)*R^κ*(R^(5/6:ℝ)*U^(1/3:ℝ)) := by
      rw [angular_model_outer_power hRp hUp,←Real.rpow_add hXp]
      have he : κ+κ = 2*κ := by ring
      rw [he]
      ring
    _ ≤ (K*D)*X^(2*κ)*X^κ*X^(589/1000:ℝ) := by
      gcongr
    _ = (K*D)*((X^(2*κ)*X^κ)*X^(589/1000:ℝ)) := by ring
    _ = (K*D)*X^(3*κ+589/1000) := by
      rw [←Real.rpow_add hXp,←Real.rpow_add hXp]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (mul_nonneg hK hD)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTailCounting
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal grouped long-completion coefficient has the counting
bound used in the low-height Type-I argument, on every norm dyad. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_tail_counting_scale {n E U ε : ℝ}
    (hE : 0 < E) (hEn : E ≤ n) (hU : 0 ≤ U) (hε : ε ≤ 1/2) :
    n^(1/2+ε)*(U/n^3) ≤ U*E^(-5/2+ε) := by
  have hn : 0 < n := hE.trans_le hEn
  have he : n^(1/2+ε)/n^3 = n^(-5/2+ε) := by
    rw [←Real.rpow_natCast n 3,←Real.rpow_sub hn]
    congr 1
    ring
  calc
    _ = U*(n^(1/2+ε)/n^3) := by ring
    _ = U*n^(-5/2+ε) := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hE hEn (by linarith)) hU

theorem metaplectic_tail_dyad_counting {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r : Eisenstein), primary r →
      ∀ (ℓ : ℤ) (C F : ℝ) (S : Finset Eisenstein) (E U B M : ℝ),
      0 < E → 0 < U → 0 ≤ B → 0 ≤ M →
      (∀ e ∈ S, primary e ∧ E ≤ norm e ∧ norm e ≤ 2*E) →
      ∀ W : ℝ → ℂ, (∀ x : ℝ, B < x → W x = 0) → (∀ x, ‖W x‖ ≤ M) →
      ‖∑ e ∈ S, metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ W (U/norm e^3) 0‖ ≤
        D*B*M*U*E^(-3/2+ε) := by
  obtain ⟨D,hD,hcoeff⟩ := metaplecticTailCoefficient_bound hε
  refine ⟨648*D,by positivity,?_⟩
  intro r hr ℓ C F S E U B M hE hU hB hM hS W hcut hW
  have hcard : (S.card:ℝ) ≤ 36*E := by
    have hs : S ⊆ primaryElementBall (2*E) := by
      intro e he
      exact mem_primaryElementBall.mpr ⟨(hS e he).1,(hS e he).2.2⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans
      ((primaryElementBall_card_le (by positivity)).trans_eq (by ring))
  have hb (e : Eisenstein) (he : e ∈ S) :
      ‖metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ W (U/norm e^3) 0‖ ≤
        (18*D*B*M*U)*E^(-5/2+ε) := by
    have hne : 0 < norm e := norm_pos_of_ne_zero (primary_ne_zero (hS e he).1)
    rw [norm_mul]
    calc
      _ ≤ (D*norm e^(1/2+ε))*(18*B*M*(U/norm e^3)) :=
        mul_le_mul (hcoeff r ℓ C F e (hS e he).1)
          (metaplecticAngularSmoothSum_trivial hr ℓ W (div_pos hU (pow_pos hne 3)) hB hM hcut hW)
          (_root_.norm_nonneg _) (by positivity)
      _ = (18*D*B*M)*(norm e^(1/2+ε)*(U/norm e^3)) := by ring
      _ ≤ (18*D*B*M)*(U*E^(-5/2+ε)) := mul_le_mul_of_nonneg_left
        (metaplectic_tail_counting_scale hE (hS e he).2.1 hU.le hεsmall) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ _e ∈ S, (18*D*B*M*U)*E^(-5/2+ε) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hb)
    _ = (S.card:ℝ)*((18*D*B*M*U)*E^(-5/2+ε)) := by simp
    _ ≤ (36*E)*((18*D*B*M*U)*E^(-5/2+ε)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (648*D)*B*M*U*E^(-3/2+ε) := by
      have he : E*E^(-5/2+ε) = E^(-3/2+ε) := by
        conv_lhs => lhs; rw [←Real.rpow_one E]
        rw [←Real.rpow_add hE]
        congr 1
        ring
      calc
        _ = (648*D)*B*M*U*(E*E^(-5/2+ε)) := by ring
        _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLongCounting
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual long-completion dyads with the counting estimate. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem metaplectic_long_counting {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r : Eisenstein), primary r →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ) (U B C F M : ℝ),
      0 < U → 0 ≤ B → 0 < C → B*U ≤ F → 0 ≤ M →
      (∀ x : ℝ, B < x → W x = 0) → (∀ x, ‖W x‖ ≤ M) →
      ‖metaplecticLongCompletion r ℓ W U C F‖ ≤
        D*B*M*U*(C/2)^(-3/2+ε)*(metaplecticLongDyads C F).card := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_tail_dyad_counting hε hεsmall
  refine ⟨D,hD,?_⟩
  intro r hr ℓ W U B C F M hU hB hC hF hM hcut hW
  rw [metaplectic_long_completion_active r ℓ W hU hB hF hcut C,
    metaplectic_long_dyad_partition]
  have hb (j : ℕ) (hj : j ∈ metaplecticLongDyads C F) :
      ‖∑ e ∈ metaplecticLongDyad C F j, metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ W (U/norm e^3) 0‖ ≤
        D*B*M*U*(C/2)^(-3/2+ε) := by
    have hCE : C/2 ≤ (2:ℝ)^j := by linarith [metaplecticLongDyad_cutoff hj]
    have hs := hbound r hr ℓ C F (metaplecticLongDyad C F j) ((2:ℝ)^j) U B M
      (by positivity) hU hB hM (fun e he => metaplecticLongDyad_norm he) W hcut hW
    apply hs.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hCE (by linarith)
  calc
    _ ≤ ∑ j ∈ metaplecticLongDyads C F, D*B*M*U*(C/2)^(-3/2+ε) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hb)
    _ = _ := by simp; ring

theorem metaplectic_long_outer_counting {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Finset Eisenstein) (α : Eisenstein → ℂ)
      (ℓ : ℤ) (W : Eisenstein → ℝ → ℂ) (U B C F M : ℝ),
      0 < U → 0 ≤ B → 0 < C → B*U ≤ F → 0 ≤ M →
      (∀ r ∈ A, primary r) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W r x = 0) →
      (∀ r ∈ A, ∀ x, ‖W r x‖ ≤ M) →
      ‖∑ r ∈ A, α r*metaplecticLongCompletion r ℓ (W r) U C F‖ ≤
        D*B*M*U*(C/2)^(-3/2+ε)*(metaplecticLongDyads C F).card*(∑ r ∈ A, ‖α r‖) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_long_counting hε hεsmall
  refine ⟨D,hD,?_⟩
  intro A α ℓ W U B C F M hU hB hC hF hM hA hcut hW
  calc
    _ ≤ ∑ r ∈ A, ‖α r‖*‖metaplecticLongCompletion r ℓ (W r) U C F‖ := by
      simpa only [norm_mul] using norm_sum_le A (fun r => α r*metaplecticLongCompletion r ℓ (W r) U C F)
    _ ≤ ∑ r ∈ A, ‖α r‖*(D*B*M*U*(C/2)^(-3/2+ε)*(metaplecticLongDyads C F).card) :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left
        (hbound r (hA r hr) ℓ (W r) U B C F M hU hB hC hF hM (hcut r hr) (hW r hr))
        (_root_.norm_nonneg _))
    _ = _ := by rw [←Finset.sum_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLogCounting
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual long inverse-completion counting estimate for an
arbitrary logarithmic weight family, with all outer coefficients kept. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem LogarithmicWeightFamily.metaplectic_long_counting
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {ε s : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1/2) (hs : 0 < s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (A : Finset Eisenstein)
      (α : Eisenstein → ℂ) (ℓ : ℤ) (X U B C F : ℝ),
      1 ≤ X → 0 < U → 0 ≤ B → 0 < C → B*U ≤ F →
      (∀ r ∈ A, primary r) → (∀ r ∈ A, Y (w r) ≤ X) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ‖∑ r ∈ A, α r*metaplecticLongCompletion r ℓ (W (w r)) U C F‖ ≤
        K*B*U*X^s*(C/2)^(-3/2+ε)*((metaplecticLongDyads C F).card:ℝ)*
          (∑ r ∈ A, ‖α r‖) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_long_outer_counting hε hεsmall
  obtain ⟨M,hM,hMbound⟩ := hW.subpower_norm hs
  refine ⟨D*M,by positivity,?_⟩
  intro w A α ℓ X U B C F hX hU hB hC hF hA hY hcut
  have hb : ∀ r ∈ A, ∀ x, ‖W (w r) x‖ ≤ M*X^s := by
    intro r hr x
    exact (hMbound (w r) x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith [hW.length_one (w r)]) (hY r hr) hs.le) hM)
  have hh := hbound A α ℓ (fun r => W (w r)) U B C F (M*X^s)
    hU hB hC hF (by positivity) hA hcut hb
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticSmallLow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The counting bound at the source small-level cutoff X^(13/100),
including the actual finite dyads and original logarithmic weights. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem LogarithmicWeightFamily.metaplectic_long_small_power
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {B D : ℝ} (hB : 1 ≤ B) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (ℓ : ℤ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X →
      (∀ r ∈ S, primary r) → (∀ r ∈ S, Y (w r) ≤ X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∑ r ∈ S, ‖α r‖) ≤ D*R*X^κ →
      ‖∑ r ∈ S, α r*metaplecticLongCompletion r ℓ (W (w r)) U
        (X^(13/100:ℝ)) (X^2)‖ ≤ K*X^(41/50:ℝ) := by
  obtain ⟨A,hA,hbound⟩ := hW.metaplectic_long_counting
    (by norm_num : 0 < κ) (by norm_num : κ ≤ 1/2) (by norm_num : 0 < κ)
  obtain ⟨J,hJ,hcard⟩ := metaplecticLongDyads_small_power (by norm_num : 0 < κ)
  let T : ℝ := (2⁻¹:ℝ)^(-3/2+κ)
  refine ⟨A*B*T*J*D,by dsimp [T]; positivity,?_⟩
  intro w S α ℓ X R U hX hBX hR hU hRU hS hY hcut hmass
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hUp : 0 < U := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left hUp.le hR
  have hBU : B*U ≤ X^2 := by nlinarith [mul_le_mul hBX hUX hUp.le hXp.le]
  have hc : ((metaplecticLongDyads (X^(13/100:ℝ)) (X^2)).card:ℝ) ≤ J*X^(2*κ) := by
    apply (hcard _ _ (one_le_pow₀ hX1)).trans_eq
    rw [←Real.rpow_natCast X 2,←Real.rpow_mul hXp.le]
    congr 2
  have hcp : (X^(13/100:ℝ)/2)^(-3/2+κ) = T*X^((13/100)*(-3/2+κ)) := by
    rw [div_eq_mul_inv,Real.mul_rpow (Real.rpow_nonneg hXp.le _) (by norm_num),
      ←Real.rpow_mul hXp.le]
    exact mul_comm _ _
  have hp : X^κ*X^((13/100)*(-3/2+κ))*X^(2*κ)*X^κ*X =
      X^(1+4*κ+(13/100)*(-3/2+κ)) := by
    conv_lhs => rhs; rw [←Real.rpow_one X]
    rw [←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp]
    congr 1
    ring
  have hb := hbound w S α ℓ X U B (X^(13/100:ℝ)) (X^2)
    hX1 hUp hB0 (by positivity) hBU hS hY hcut
  apply hb.trans
  rw [hcp]
  calc
    _ ≤ A*B*U*X^κ*(T*X^((13/100)*(-3/2+κ)))*(J*X^(2*κ))*(D*R*X^κ) := by gcongr
    _ = (A*B*T*J*D)*X^(1+4*κ+(13/100)*(-3/2+κ)) := by
      calc
        _ = (A*B*T*J*D)*(X^κ*X^((13/100)*(-3/2+κ))*X^(2*κ)*X^κ*(R*U)) := by ring
        _ = _ := by rw [hRU,hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by dsimp [T]; positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial residue cutoff lies within the squarefree lattice cutoff,
and its elementary Euler tail has a power margin at the source scales. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_radial_cutoff_le_sqrt {X R U C B : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (hU : 0 < U) (hRU : R*U = X)
    (hRhi : R ≤ X^(51/100:ℝ)) (hB : 1 ≤ B)
    (hC : 0 ≤ C) (hChi : C ≤ X^(13/100:ℝ)) : C ≤ Real.sqrt (B*U) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hcR : C^2*R ≤ X := by
    calc
      _ ≤ (X^(13/100:ℝ))^2*X^(51/100:ℝ) :=
        mul_le_mul (pow_le_pow_left₀ hC hChi 2) hRhi hR.le (by positivity)
      _ = X^(77/100:ℝ) := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_add hXp]
        norm_num
      _ ≤ X := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hX (show (77/100:ℝ) ≤ 1 by norm_num)
  have hcU : C^2 ≤ U := (mul_le_mul_iff_left₀ hR).mp (by simpa [hRU,mul_comm] using hcR)
  exact Real.le_sqrt_of_sq_le (hcU.trans (le_mul_of_one_le_left hU.le hB))

lemma metaplectic_radial_euler_power {X C : ℝ} (hX : 1 ≤ X)
    (hC : X^(1/50:ℝ) ≤ C) :
    X^(5/6:ℝ)*C^(-(99/100):ℝ)*X^(2/10000:ℝ) ≤ X^(41/50:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hc : X^(5/6:ℝ)*C^(-(99/100):ℝ)*X^(2/10000:ℝ) ≤
      X^(5/6:ℝ)*(X^(1/50:ℝ))^(-(99/100):ℝ)*X^(2/10000:ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hXp _) hC (by norm_num))
      (by positivity)) (by positivity)
  apply hc.trans
  rw [←Real.rpow_mul hXp.le,←Real.rpow_add hXp,←Real.rpow_add hXp]
  exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual area term in primary radial lattice summation. The
nonzero dual frequencies are bounded by the existing Schwartz estimate. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators SchwartzMap
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma integral_normSq_profile (W : ℝ → ℂ) :
    (∫ z : ℂ, W (Complex.normSq z)) = (Real.pi:ℂ)*(∫ x in Ioi (0:ℝ), W x) := by
  simp_rw [Complex.normSq_eq_norm_sq]
  rw [complex_radial_integral (fun r => W (r^2))]
  have hsub := integral_comp_rpow_Ioi W (show (2:ℝ) ≠ 0 by norm_num)
  have hh : (2:ℂ)*(∫ r in Ioi (0:ℝ), (r:ℂ)*W (r^2)) = ∫ x in Ioi (0:ℝ), W x := by
    rw [←integral_const_mul,←hsub]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2),show (2:ℝ)-1 = 1 by norm_num,Real.rpow_one,Real.rpow_two,
      Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  linear_combination (Real.pi:ℂ)*hh

theorem UniformLogWeights.radial_coset_error {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i q, q ≠ 0 → ∀ z : ℂ,
      ‖(∑' a : Eisenstein, W i (Complex.normSq (z+q*(a:ℂ))))-
        (2/(Real.sqrt 3*Complex.normSq q):ℝ) • (∫ w : ℂ, W i (Complex.normSq w))‖ ≤
        K*Complex.normSq q := by
  obtain ⟨D,hD,hbound⟩ := h.angularFourier_seminorm 0 4 0
  let R := ∑' a : Eisenstein, (norm a)^(-(2:ℝ))
  have hR : 0 ≤ R := tsum_nonneg (fun a => Real.rpow_nonneg (norm_nonneg a) _)
  let C := D*R+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨18*C/Real.sqrt 3,by positivity,?_⟩
  intro i q hq z
  let F := angularAnnulusSchwartz 0 (W i) (h.compact i) (h.positive i) (h.smooth i)
  have hF (w : ℂ) : F w = W i (Complex.normSq w) := by simp [F,angularAnnulusSchwartz,angularAnnulus,angularPlanePhase]
  have hd : ∀ w : ℂ, ‖w‖^4*‖traceFourier F w‖ ≤ D := by
    intro w
    have hh := SchwartzMap.le_seminorm ℝ 4 0 (traceFourierSchwartz F) w
    simp only [norm_iteratedFDeriv_zero,traceFourierSchwartz_apply] at hh
    exact hh.trans (hbound i)
  have hN : 0 < Complex.normSq q := Complex.normSq_pos.mpr hq
  have hw : q*traceLambda ≠ 0 := mul_ne_zero hq traceLambda_ne_zero
  let c : Eisenstein → ℂ := fun a =>
    (Real.fourierChar (tracePair z ((a:ℂ)/(q*traceLambda))) : ℂ)
  have hc : ∀ a, ‖c a‖ ≤ 1 := by
    intro a
    exact (Circle.norm_coe _).le
  have hs : Summable (fun a : Eisenstein => c a*traceFourier F ((a:ℂ)/(q*traceLambda))) := by
    apply (traceFourier_summable_eisenstein F _ hw).norm.of_norm_bounded
    intro a
    rw [norm_mul]
    exact mul_le_of_le_one_left (_root_.norm_nonneg _) (hc a)
  have hzero : c 0*traceFourier F (((0:Eisenstein):ℂ)/(q*traceLambda)) = ∫ w : ℂ, F w := by
    simp [c,traceFourier_zero,tracePair]
  simp_rw [←hF]
  rw [poisson_eisenstein_coset F q hq z]
  change ‖(2/(Real.sqrt 3*Complex.normSq q):ℝ) •
    (∑' a : Eisenstein, c a*traceFourier F ((a:ℂ)/(q*traceLambda)))-
    (2/(Real.sqrt 3*Complex.normSq q):ℝ) • (∫ w : ℂ, F w)‖ ≤ _
  rw [hs.tsum_eq_add_tsum_ite 0,hzero,smul_add,add_sub_cancel_left,norm_smul,
    Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (schwartz_weighted_dual_bound F hD.le hd _ hw c hc)
    (by positivity)).trans_eq
  rw [Complex.normSq_mul,traceLambda_normSq]
  dsimp [C,R]
  field_simp
  ring

theorem UniformLogWeights.primaryRadialLattice_error {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i Y, 0 < Y →
      ‖primaryAngularLattice 0 (W i) Y-primaryRadialMain (W i) Y‖ ≤ K/Y := by
  obtain ⟨C,hC,hbound⟩ := h.radial_coset_error
  refine ⟨9*C,by positivity,?_⟩
  intro i Y hY
  let s : ℝ := 1/Real.sqrt Y
  have hs : 0 < s := by dsimp [s]; positivity
  have hq : (s:ℂ)*3 ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne') (by norm_num)
  have hn : Complex.normSq ((s:ℂ)*3) = 9/Y := by
    rw [Complex.normSq_mul,Complex.normSq_ofReal]
    norm_num
    dsimp [s]
    rw [one_div,←pow_two,inv_pow,Real.sq_sqrt hY.le]
    ring
  have he : primaryAngularLattice 0 (W i) Y =
      ∑' u : PrimaryArgument, W i (Complex.normSq ((s:ℂ)*(u:ℂ))) := by
    apply tsum_congr
    intro u
    simpa only [angularAnnulus,angularPlanePhase,zpow_zero,one_mul] using
      (angularAnnulus_scaled 0 (W i) hY u).symm
  rw [he,primary_scaled_coset (fun z : ℂ => W i (Complex.normSq z)) (s:ℂ)]
  have hb := hbound i _ hq (s:ℂ)
  rw [hn,integral_normSq_profile] at hb
  have hm : (2/(Real.sqrt 3*(9/Y)):ℝ) • ((Real.pi:ℂ)*(∫ x in Ioi (0:ℝ), W i x)) =
      primaryRadialMain (W i) Y := by
    rw [Complex.real_smul,primaryRadialMain]
    push_cast
    field_simp
  rw [hm] at hb
  exact hb.trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialCentered
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform centered radial lattice sums, including the short empty range.
The coprimality correction is a literal finite Möbius expansion. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma UniformLogWeights.radial_integral_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ M : ℝ, 0 < M ∧ ∀ i, ‖∫ x in Ioi (0:ℝ), W i x‖ ≤ M := by
  obtain ⟨M,hM,hb⟩ := h.mellin_decay 1 0
  refine ⟨M,hM,?_⟩
  intro i
  have hh := hb i 1 (by norm_num) 0
  simpa [mellin] using hh

theorem UniformLogWeights.primaryRadialLattice_centered {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i Y, 0 < Y →
      ‖primaryAngularLattice 0 (W i) Y-primaryRadialMain (W i) Y‖ ≤ K := by
  obtain ⟨C,hC,hbound⟩ := h.primaryRadialLattice_error
  obtain ⟨M,hM,hMbound⟩ := h.radial_integral_bound
  let S := Real.exp h.radius
  have hS : 1 ≤ S := Real.one_le_exp h.radius_nonneg
  have hSpos : 0 < S := Real.exp_pos _
  let A := 2*Real.pi/(9*Real.sqrt 3)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨C*S+A*M,by positivity,?_⟩
  intro i Y hY
  by_cases he : 1 ≤ S*Y
  · apply (hbound i Y hY).trans
    have hh : C/Y ≤ C*S := (div_le_iff₀ hY).mpr (by nlinarith)
    exact hh.trans (le_add_of_nonneg_right (mul_nonneg hA hM.le))
  · have hz : primaryAngularLattice 0 (W i) Y = 0 := by
      have ht (u : PrimaryArgument) : theta 0 u*W i (norm u/Y) = 0 := by
        have hn := one_le_norm (primary_ne_zero u.property)
        have hw : W i (norm u/Y) = 0 := h.upper_support i _
          ((lt_div_iff₀ hY).mpr ((lt_of_not_ge he).trans_le hn))
        rw [hw,mul_zero]
      simp only [primaryAngularLattice,ht,tsum_zero]
    have hY1 : Y ≤ 1 := by nlinarith
    have hm : ‖primaryRadialMain (W i) Y‖ ≤ A*M := by
      rw [primaryRadialMain,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      change (2*Real.pi*Y/(9*Real.sqrt 3))*_ ≤ A*M
      calc
        _ = (A*Y)*‖∫ x in Ioi (0:ℝ), W i x‖ := by dsimp [A]; ring
        _ ≤ A*M := by
          apply mul_le_mul
          · exact mul_le_of_le_one_right hA hY1
          · exact hMbound i
          · positivity
          · exact hA
    rw [hz,zero_sub,norm_neg]
    exact hm.trans (le_add_of_nonneg_left (by positivity))

theorem UniformLogWeights.primaryCoprimeRadialLattice_centered
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ Y, 0 < Y →
      ‖primaryCoprimeAngularLattice r 0 (W i) Y-primaryCoprimeRadialMain r (W i) Y‖ ≤
        K*norm r^ε := by
  obtain ⟨C,hC,hbound⟩ := h.primaryRadialLattice_centered
  obtain ⟨D,hD,hdiv⟩ := primeDivisorWeight_small_power ε hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro i r hr hsr Y hY
  rw [primaryCoprimeAngularLattice_expansion hr hsr 0 (W i) (h.compact i) (h.smooth i) hY,
    primaryCoprimeRadialMain,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ s ∈ (primaryPrimeFactors r).powerset,C := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro s hs
      have hd : primary (∏ p ∈ s,p) := primary_finset_prod _ _
        (fun p hp => (primaryPrimeFactor_spec hr (Finset.mem_powerset.mp hs hp)).1.1)
      have hθ : theta 0 (∏ p ∈ s,p) = 1 := by simp [theta]
      rw [hθ,mul_one,←mul_sub,norm_mul]
      exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
        (hbound i _ (div_pos hY (norm_pos_of_ne_zero (primary_ne_zero hd))))
    _ = C*(2:ℝ)^(primaryPrimeFactors r).card := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring
    _ ≤ C*(D*norm r^ε) := mul_le_mul_of_nonneg_left (hdiv r hr hsr) hC.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTotient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite coprimality density at a squarefree primary level.
Only residue-ring cardinalities and the ordinary Chinese remainder theorem
enter this calculation. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticTotient_mul {a b : Eisenstein} (hab : IsCoprime a b) :
    metaplecticTotient (a*b) = metaplecticTotient a*metaplecticTotient b := by
  let e : Residues (a*b) ≃+* Residues a × Residues b :=
    (Ideal.quotEquivOfEq (show modulus (a*b) = modulus a*modulus b by
      exact (Ideal.span_singleton_mul_span_singleton a b).symm)).trans
      (Ideal.quotientMulEquivQuotientProd _ _
        ((Ideal.isCoprime_span_singleton_iff a b).mpr hab))
  have hc := Nat.card_congr ((Units.mapEquiv e.toMulEquiv).trans MulEquiv.prodUnits).toEquiv
  simpa only [metaplecticTotient,Nat.card_prod,Nat.cast_mul] using congrArg (fun n : ℕ => (n:ℝ)) hc

lemma metaplecticTotient_prime {p : Eisenstein} (hp : primaryPrime p) :
    metaplecticTotient p = norm p-1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  have hn : 1 ≤ normNat p := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (normNat_ne_zero hp.2.ne_zero))
  rw [metaplecticTotient,Nat.card_units,residues_card hp.2.ne_zero,Nat.cast_sub hn,normNat_cast]
  norm_num

lemma metaplecticTotient_prod (s : Finset Eisenstein)
    (hp : ∀ p ∈ s, primaryPrime p) :
    metaplecticTotient (∏ p ∈ s,p) = ∏ p ∈ s,(norm p-1) := by
  induction s using Finset.induction_on with
  | empty =>
      change (Nat.card (Residues (1:Eisenstein))ˣ:ℝ) = 1
      have hc : Nat.card (Residues (1:Eisenstein)) = 1 := by
        rw [residues_card one_ne_zero,normNat_one]
      have hsub : Subsingleton (Residues (1:Eisenstein)) :=
        (Nat.card_eq_one_iff_unique.mp hc).1
      have hunit : ∀ u : (Residues (1:Eisenstein))ˣ, u = 1 := by
        intro u
        apply Units.ext
        exact hsub.elim _ _
      have hu : Nat.card (Residues (1:Eisenstein))ˣ = 1 :=
        Nat.card_eq_one_iff_exists.mpr ⟨1,hunit⟩
      exact_mod_cast hu
  | @insert p s hps ih =>
      have hp' := hp p (Finset.mem_insert_self _ _)
      have hs : ∀ q ∈ s, primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
      have hc : IsCoprime p (∏ q ∈ s,q) := by
        apply IsCoprime.prod_right
        intro q hq
        exact primaryPrimes_isCoprime hp' (hs q hq) (fun heq => hps (heq ▸ hq))
      rw [Finset.prod_insert hps,metaplecticTotient_mul hc,metaplecticTotient_prime hp',
        ih hs,Finset.prod_insert hps]

lemma metaplecticTotient_density {r : Eisenstein} (hr : primary r) (hsr : Squarefree r) :
    metaplecticTotient r/norm r =
      ∏ p ∈ primaryPrimeFactors r,(1-(norm p)⁻¹) := by
  have hp : ∀ p ∈ primaryPrimeFactors r, primaryPrime p :=
    fun p hp => (primaryPrimeFactor_spec hr hp).1
  have hn : (∏ p ∈ primaryPrimeFactors r,norm p) = norm r := by
    rw [←norm_finset_prod,primaryPrimeFactors_prod hr hsr]
  have hφ := metaplecticTotient_prod (primaryPrimeFactors r) hp
  rw [primaryPrimeFactors_prod hr hsr] at hφ
  rw [hφ]
  rw [←hn,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp'
  have hnp := norm_pos_of_ne_zero (primary_ne_zero (hp p hp').1)
  field_simp

lemma primary_moebius_density {r : Eisenstein} (hr : primary r) (hsr : Squarefree r) :
    (∑ s ∈ (primaryPrimeFactors r).powerset,
      (idealMoebius (∏ p ∈ s,p):ℝ)/norm (∏ p ∈ s,p)) = metaplecticTotient r/norm r := by
  rw [metaplecticTotient_density hr hsr,Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro s hs
  have hp : ∀ p ∈ s, primaryPrime p := fun p hp =>
    (primaryPrimeFactor_spec hr (Finset.mem_powerset.mp hs hp)).1
  rw [idealMoebius_prod_primaryPrimes s hp]
  simp only [Finset.prod_const_one,mul_one]
  rw [Finset.prod_inv_distrib]
  have hn : (∏ p ∈ s,norm p) = norm (∏ p ∈ s,p) := (norm_finset_prod _ _).symm
  rw [hn]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialDensity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the radial lattice density with the literal
metaplectic residue constant. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma integral_radial_model_weight (W : ℝ → ℂ) :
    (∫ x in Ioi (0:ℝ), ((x^(-1/6:ℝ):ℝ):ℂ)*W x) = mellin W (5/6) := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [Complex.ofReal_cpow hx.le]
  norm_num

lemma primaryCoprimeRadialMain_eq {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (Y : ℝ) :
    primaryCoprimeRadialMain r W Y =
      (((2*Real.pi*Y/(9*Real.sqrt 3))*(metaplecticTotient r/norm r):ℝ):ℂ)*
        (∫ x in Ioi (0:ℝ), W x) := by
  have hsum : (∑ s ∈ (primaryPrimeFactors r).powerset,
      ((idealMoebius (∏ p ∈ s,p):ℝ)/norm (∏ p ∈ s,p):ℝ)) =
      metaplecticTotient r/norm r := primary_moebius_density hr hsr
  unfold primaryCoprimeRadialMain primaryRadialMain
  calc
    _ = (∑ s ∈ (primaryPrimeFactors r).powerset,
        (((idealMoebius (∏ p ∈ s,p):ℝ)/norm (∏ p ∈ s,p):ℝ):ℂ))*
          (((2*Real.pi*Y/(9*Real.sqrt 3)):ℝ):ℂ)*(∫ x in Ioi (0:ℝ), W x) := by
      rw [Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      push_cast
      ring
    _ = _ := by rw [←Complex.ofReal_sum,hsum,Complex.ofReal_mul]; ring

lemma cStar_primary_area_constant :
    cStar*(2*Real.pi/(9*Real.sqrt 3)) = metaplecticA0 := by
  have hg : Real.Gamma (2/3:ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hs : Real.sqrt (3:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h3 : (3:ℝ)^(7/2:ℝ) = 27*Real.sqrt 3 := by
    rw [show (7/2:ℝ) = 3+1/2 by norm_num,Real.rpow_add (by norm_num),
      Real.rpow_ofNat,←Real.sqrt_eq_rpow]
    norm_num
  have hp : (2*Real.pi)^(5/3:ℝ) = (2*Real.pi)^(2/3:ℝ)*(2*Real.pi) := by
    rw [show (5/3:ℝ) = 2/3+1 by norm_num,Real.rpow_add (by positivity),Real.rpow_one]
  rw [cStar,metaplecticA0,h3,hp]
  field_simp
  ring

lemma metaplectic_radial_density_scale {N U : ℝ} (hN : 0 < N) (hU : 0 < U)
    (φ : ℝ) :
    cStar*(N*U)^(-1/6:ℝ)*(2*Real.pi*U/(9*Real.sqrt 3))*(φ/N) =
      metaplecticA0*U^(5/6:ℝ)*φ*N^(-7/6:ℝ) := by
  have hUpow : U^(-1/6:ℝ)*U = U^(5/6:ℝ) := by
    calc
      _ = U^(-1/6:ℝ)*U^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hU]; norm_num
  have hNpow : N^(-1/6:ℝ)/N = N^(-7/6:ℝ) := by
    calc
      _ = N^(-1/6:ℝ)/N^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_sub hN]; norm_num
  calc
    _ = (cStar*(2*Real.pi/(9*Real.sqrt 3)))*(U^(-1/6:ℝ)*U)*φ*(N^(-1/6:ℝ)/N) := by
      rw [Real.mul_rpow hN.le hU.le]
      ring
    _ = _ := by rw [cStar_primary_area_constant,hUpow,hNpow]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialEulerTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite Möbius density has a uniform quantitative tail.
A convergent Eisenstein norm series supplies the only estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticRadialEulerPartial_tail :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r C D, 0 < C → C ≤ D →
      ‖metaplecticRadialEulerPartial r D-metaplecticRadialEulerPartial r C‖ ≤
        K*C^(-(99/100):ℝ) := by
  let K := ∑' c : Eisenstein, norm c^(-(101/100):ℝ)
  have hK : 0 ≤ K := tsum_nonneg (fun c => Real.rpow_nonneg (norm_nonneg c) _)
  refine ⟨K,hK,?_⟩
  intro r C D hC hCD
  let S := primaryElementBall D \ primaryElementBall C
  have hsub : primaryElementBall C ⊆ primaryElementBall D := by
    intro c hc
    exact mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hc).1,
      (mem_primaryElementBall.mp hc).2.trans hCD⟩
  let g : Eisenstein → ℂ := fun c => if IsCoprime r c then
    (idealMoebius c:ℂ)*((norm c^(-2:ℝ):ℝ):ℂ) else 0
  have he : metaplecticRadialEulerPartial r D-metaplecticRadialEulerPartial r C =
      ∑ c ∈ S,g c := by
    exact (Finset.sum_sdiff_eq_sub (f := g) hsub).symm
  rw [he]
  have hpoint (c : Eisenstein) (hc : c ∈ S) :
      ‖g c‖ ≤ C^(-(99/100):ℝ)*norm c^(-(101/100):ℝ) := by
    have hm := Finset.mem_sdiff.mp hc
    obtain ⟨hcp,hcn⟩ := mem_primaryElementBall.mp hm.1
    have hnorm : C < norm c := by
      by_contra hn
      exact hm.2 (mem_primaryElementBall.mpr ⟨hcp,le_of_not_gt hn⟩)
    have hbase : ‖g c‖ ≤ norm c^(-2:ℝ) := by
      dsimp [g]
      split_ifs
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg c) _)]
        exact mul_le_of_le_one_left (Real.rpow_nonneg (norm_nonneg c) _)
          (norm_idealMoebius_le_one c)
      · simpa only [norm_zero] using Real.rpow_nonneg (norm_nonneg c) (-2:ℝ)
    apply hbase.trans
    simpa only [show (101/100:ℝ)-2 = -(99/100:ℝ) by norm_num] using
      norm_rpow_tail_pointwise hC (show (101/100:ℝ) < 2 by norm_num) hnorm
  calc
    _ ≤ ∑ c ∈ S, C^(-(99/100):ℝ)*norm c^(-(101/100):ℝ) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hpoint)
    _ = C^(-(99/100):ℝ)*(∑ c ∈ S,norm c^(-(101/100):ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C^(-(99/100):ℝ)*K := mul_le_mul_of_nonneg_left
      ((summable_eisenstein_norm_rpow (show (1:ℝ) < 101/100 by norm_num)).sum_le_tsum S
        (fun c _ => Real.rpow_nonneg (norm_nonneg c) _)) (by positivity)
    _ = _ := mul_comm _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticSquarefreeRadial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squarefree radial model after actual square-divisor inversion.
Its finite main term remains explicit for comparison with the inverse
completion residue. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeCoprimeRadialMain_eq {r : Eisenstein} (hr : primary r)
    (hsr : Squarefree r) (W : ℝ → ℂ) (Y B : ℝ) :
    squarefreeCoprimeRadialMain r W Y B =
      ((((2*Real.pi*Y/(9*Real.sqrt 3))*(metaplecticTotient r/norm r):ℝ):ℂ)*
        (∫ x in Set.Ioi (0:ℝ), W x))*
          metaplecticRadialEulerPartial r (Real.sqrt (B*Y)) := by
  have he : squarefreeDivisorTruncation (Real.sqrt (B*Y)) =
      (primaryElementBall (Real.sqrt (B*Y))).filter Squarefree := by
    ext c
    simp only [mem_squarefreeDivisorTruncation,Finset.mem_filter,mem_primaryElementBall]
    tauto
  unfold squarefreeCoprimeRadialMain metaplecticRadialEulerPartial
  rw [he,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hsf : Squarefree c
  · simp only [hsf,ite_true, if_true]
    have hcop : IsCoprime r (c^2) ↔ IsCoprime r c := by
      rw [pow_two,IsCoprime.mul_right_iff,and_self]
    by_cases hrc : IsCoprime r c
    · simp only [hcop,hrc,ite_true, if_true,primaryCoprimeRadialMain_eq hr hsr]
      rw [eisenstein_norm_pow_lattice,Real.rpow_neg (norm_nonneg c),Real.rpow_ofNat]
      push_cast
      ring
    · simp only [hcop,hrc,ite_false, if_false,mul_zero]
  · simp [hsf,idealMoebius]

theorem UniformLogWeights.squarefreeCoprimeRadialLattice_centered
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ Y, 0 < Y →
      ‖squarefreeCoprimeAngularLattice r 0 (W i) Y-
        squarefreeCoprimeRadialMain r (W i) Y (Real.exp h.radius)‖ ≤
        K*norm r^ε*Real.sqrt Y := by
  obtain ⟨C,hC,hbound⟩ := h.primaryCoprimeRadialLattice_centered hε
  let S := Real.exp h.radius
  have hS : 0 < S := Real.exp_pos _
  refine ⟨18*Real.sqrt S*C,by positivity,?_⟩
  intro i r hr hsr Y hY
  have hNr : 0 ≤ norm r^ε := Real.rpow_nonneg (norm_nonneg r) _
  let B := squarefreeDivisorTruncation (Real.sqrt (S*Y))
  have hcard : (B.card:ℝ) ≤ 18*Real.sqrt (S*Y) := by
    have hsub : B ⊆ nonzeroNormBall (Real.sqrt (S*Y)) := by
      intro c hc
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (nonzeroNormBall_card_le (Real.sqrt_nonneg _))
  rw [squarefreeCoprimeAngularLattice_expansion r 0 (W i) (h.compact i) (h.smooth i)
    hY (h.upper_support i),squarefreeCoprimeRadialMain,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c ∈ B,C*norm r^ε := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro c hc
      have hprim : primary (c^2) := by
        simpa only [pow_two] using primary_mul (mem_squarefreeDivisorTruncation.mp hc).1
          (mem_squarefreeDivisorTruncation.mp hc).1
      by_cases hcop : IsCoprime r (c^2)
      · simp only [hcop,ite_true, if_true,show theta 0 (c^2) = 1 by simp [theta],one_mul]
        rw [←mul_sub,norm_mul]
        exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
          (hbound i r hr hsr _ (div_pos hY (norm_pos_of_ne_zero (primary_ne_zero hprim))))
      · simp only [hcop,ite_false, if_false,mul_zero,sub_self,norm_zero]
        exact mul_nonneg hC.le hNr
    _ = (B.card:ℝ)*(C*norm r^ε) := by simp
    _ ≤ (18*Real.sqrt (S*Y))*(C*norm r^ε) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hC.le hNr)
    _ = _ := by rw [Real.sqrt_mul hS.le]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual radial model has the same finite residue density as the
short inverse completion, up to the proved squarefree lattice error. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angularSmoothModel_const_mul (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U : ℝ) (z : ℂ) :
    angularSmoothModel r ℓ (fun x => z*W x) U = z*angularSmoothModel r ℓ W U := by
  unfold angularSmoothModel
  rw [←tsum_mul_left]
  apply tsum_congr
  intro u
  by_cases hu : primary u
  · simp only [hu,ite_true, if_true]
    ring
  · simp only [hu,ite_false, if_false,mul_zero]

lemma radial_squarefree_main_scaled {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) {U : ℝ} (hU : 0 < U) (B : ℝ) :
    ((cStar*(norm r*U)^(-1/6:ℝ):ℝ):ℂ)*
      squarefreeCoprimeRadialMain r (fun x => ((x^(-1/6:ℝ):ℝ):ℂ)*W x) U B =
        metaplecticMain r 0 W U*metaplecticRadialEulerPartial r (Real.sqrt (B*U)) := by
  rw [squarefreeCoprimeRadialMain_eq hr hsr,integral_radial_model_weight]
  have hs := congrArg (fun x : ℝ => (x:ℂ))
    (metaplectic_radial_density_scale (norm_pos_of_ne_zero (primary_ne_zero hr)) hU
      (metaplecticTotient r))
  push_cast at hs
  simp only [metaplecticMain,ite_true, if_true]
  push_cast
  calc
    _ = ((cStar*(norm r*U)^(-1/6:ℝ)*(2*Real.pi*U/(9*Real.sqrt 3))*
        (metaplecticTotient r/norm r):ℝ):ℂ)*mellin W (5/6)*
          metaplecticRadialEulerPartial r (Real.sqrt (B*U)) := by push_cast; ring
    _ = _ := by push_cast; rw [hs]

theorem UniformLogWeights.radial_model_finite_error {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ U, 0 < U →
      ‖angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r
          (Real.sqrt (Real.exp (h.realPower (-1/6)).radius*U))‖ ≤
        K*norm r^(δ-1/6)*U^(1/3:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := (h.realPower (-1/6)).squarefreeCoprimeRadialLattice_centered hδ
  refine ⟨|cStar| * C,by have := cStar_pos; positivity,?_⟩
  intro i r hr hsr U hU
  have hn := norm_pos_of_ne_zero (primary_ne_zero hr)
  rw [angularSmoothModel_eq hsr 0 (W i) hU,
    show theta 0 r = 1 by simp [theta],mul_one,
    ←radial_squarefree_main_scaled hr hsr (W i) hU,
    ←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (mul_pos hn hU) _)]
  calc
    _ ≤ (|cStar| * (norm r*U)^(-1/6:ℝ))*(C*norm r^δ*Real.sqrt U) :=
      mul_le_mul_of_nonneg_left (hbound i r hr hsr U hU) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hn.le hU.le,Real.sqrt_eq_rpow,
        show δ-1/6 = (-1/6:ℝ)+δ by ring,Real.rpow_add hn,
        show (1/3:ℝ) = (-1/6:ℝ)+1/2 by norm_num,Real.rpow_add hU]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticShortResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma metaplectic_short_residue_eq (r : Eisenstein) (W : ℝ → ℂ)
    {U : ℝ} (hU : 0 < U) (C : ℝ) :
    (∑ c ∈ primaryElementBall C,
      ((idealMoebius c:ℂ)*metaplecticCompletionWeight r 0 0 c)*
        metaplecticMain r 0 W (U/norm c^3)) =
      (((metaplecticA0*U^(5/6:ℝ)*metaplecticTotient r*norm r^(-7/6:ℝ):ℝ):ℂ)*
        mellin W (5/6))*metaplecticRadialEulerPartial r C := by
  rw [metaplecticRadialEulerPartial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hNc := norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp hc).1)
  have hcop : IsCoprime c r ↔ IsCoprime r c := isCoprime_comm
  by_cases hrc : IsCoprime r c
  · simp only [metaplecticCompletionWeight,hcop,hrc,ite_true, if_true,mul_zero,
      Complex.ofReal_zero,zero_mul,Complex.cpow_zero,theta,zpow_zero,mul_one,
      metaplecticMain,ite_true]
    have hs := metaplectic_inverse_residue_scale hU hNc
    push_cast
    calc
      _ = (idealMoebius c:ℂ)*((Real.sqrt (norm c)*(U/norm c^3)^(5/6:ℝ):ℝ):ℂ)*
          ((metaplecticA0*metaplecticTotient r*norm r^(-7/6:ℝ):ℝ):ℂ)*mellin W (5/6) := by
            push_cast
            ring
      _ = _ := by rw [hs]; push_cast; ring
  · simp [metaplecticCompletionWeight,hcop,hrc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial model and the short inverse residue differ only by the
proved squarefree lattice error and an absolutely convergent Euler tail. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma UniformLogWeights.radial_main_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, primary r → ∀ U, 0 < U →
      ‖metaplecticMain r 0 (W i) U‖ ≤ K*U^(5/6:ℝ)*norm r^(-1/6:ℝ) := by
  obtain ⟨M,hM,hb⟩ := h.mellin_decay 1 0
  refine ⟨|metaplecticA0| * M,by positivity,?_⟩
  intro i r hr U hU
  have hn := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hm : ‖mellin (W i) (5/6)‖ ≤ M := by
    simpa using hb i (5/6) (by norm_num) 0
  have hphi := metaplecticTotient_le_norm hr
  have hphi0 : 0 ≤ metaplecticTotient r := by
    unfold metaplecticTotient
    positivity
  rw [metaplecticMain,ite_eq_left rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_mul,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hU _),
    abs_of_nonneg hphi0,abs_of_pos (Real.rpow_pos_of_pos hn _)]
  calc
    _ ≤ |metaplecticA0| * U^(5/6:ℝ)*norm r*norm r^(-7/6:ℝ)*M := by gcongr
    _ = _ := by
      have he : norm r*norm r^(-7/6:ℝ) = norm r^(-1/6:ℝ) := by
        calc
          _ = norm r^(1:ℝ)*norm r^(-7/6:ℝ) := by rw [Real.rpow_one]
          _ = norm r^((1:ℝ)+(-7/6)) := (Real.rpow_add hn _ _).symm
          _ = _ := by norm_num
      calc
        _ = (|metaplecticA0| * M)*U^(5/6:ℝ)*(norm r*norm r^(-7/6:ℝ)) := by ring
        _ = _ := by rw [he]

theorem UniformLogWeights.radial_short_model_error
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K E : ℝ, 0 ≤ K ∧ 0 ≤ E ∧ ∀ i r, primary r → Squarefree r →
      ∀ U C, 0 < U → 0 < C →
      C ≤ Real.sqrt (Real.exp (h.realPower (-1/6)).radius*U) →
      ‖angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r C‖ ≤
        K*norm r^(δ-1/6)*U^(1/3:ℝ)+
          E*U^(5/6:ℝ)*norm r^(-1/6:ℝ)*C^(-(99/100):ℝ) := by
  obtain ⟨K,hK,hmodel⟩ := h.radial_model_finite_error hδ
  obtain ⟨M,hM,hmain⟩ := h.radial_main_bound
  obtain ⟨D,hD,htail⟩ := metaplecticRadialEulerPartial_tail
  refine ⟨K,M*D,hK.le,mul_nonneg hM hD,?_⟩
  intro i r hr hsr U C hU hC hCD
  let V := Real.sqrt (Real.exp (h.realPower (-1/6)).radius*U)
  calc
    _ ≤ ‖angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r V‖+
      ‖metaplecticMain r 0 (W i) U*
        (metaplecticRadialEulerPartial r V-metaplecticRadialEulerPartial r C)‖ := by
      have he : angularSmoothModel r 0 (W i) U-
          metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r C =
        (angularSmoothModel r 0 (W i) U-
          metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r V)+
        metaplecticMain r 0 (W i) U*
          (metaplecticRadialEulerPartial r V-metaplecticRadialEulerPartial r C) := by ring
      rw [he]
      exact norm_add_le _ _
    _ ≤ K*norm r^(δ-1/6)*U^(1/3:ℝ)+
        (M*U^(5/6:ℝ)*norm r^(-1/6:ℝ))*(D*C^(-(99/100):ℝ)) := by
      apply add_le_add (hmodel i r hr hsr U hU)
      rw [norm_mul]
      exact mul_le_mul (hmain i r hr U hU) (htail r C V hC hCD)
        (_root_.norm_nonneg _)
        (mul_nonneg (mul_nonneg hM (Real.rpow_nonneg hU.le _))
          (Real.rpow_nonneg (norm_nonneg r) _))
    _ = _ := by ring

theorem LogarithmicWeightFamily.radial_short_model_error
    {ι : Type*} {Y : ι → ℝ} {W : ι → ℝ → ℂ} (h : LogarithmicWeightFamily Y W)
    {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) :
    ∃ B K E : ℝ, 1 ≤ B ∧ 0 ≤ K ∧ 0 ≤ E ∧ ∀ i r,
      primary r → Squarefree r → ∀ U C, 0 < U → 0 < C →
      C ≤ Real.sqrt (B*U) →
      ‖angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r C‖ ≤
        K*(Y i)^s*norm r^(δ-1/6)*U^(1/3:ℝ)+
          E*(Y i)^s*U^(5/6:ℝ)*norm r^(-1/6:ℝ)*C^(-(99/100):ℝ) := by
  let h₀ := h.normalize hs
  let B := Real.exp (h₀.realPower (-1/6)).radius
  obtain ⟨K,E,hK,hE,hbound⟩ := h₀.radial_short_model_error hδ
  refine ⟨B,K,E,Real.one_le_exp (h₀.realPower (-1/6)).radius_nonneg,hK,hE,?_⟩
  intro i r hr hsr U C hU hC hCD
  have hY : 0 < Y i := zero_lt_one.trans_le (h.length_one i)
  have hb := hbound i r hr hsr U C hU hC hCD
  have he : angularSmoothModel r 0 (normalizedLogWeight Y W s i) U-
      metaplecticMain r 0 (normalizedLogWeight Y W s i) U*metaplecticRadialEulerPartial r C =
      (((Y i)^(-s):ℝ):ℂ)*(angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r C) := by
    unfold normalizedLogWeight
    simp_rw [Complex.real_smul]
    rw [angularSmoothModel_const_mul,metaplecticMain_const_mul]
    ring
  change ‖angularSmoothModel r 0 (normalizedLogWeight Y W s i) U-
    metaplecticMain r 0 (normalizedLogWeight Y W s i) U*metaplecticRadialEulerPartial r C‖ ≤ _ at hb
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hY.le _)] at hb
  have hp : (Y i)^s*(Y i)^(-s) = 1 := by
    rw [←Real.rpow_add hY,add_neg_cancel,Real.rpow_zero]
  calc
    _ = (Y i)^s*((Y i)^(-s)*‖angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r C‖) := by
          rw [←mul_assoc,hp,one_mul]
    _ ≤ (Y i)^s*(K*norm r^(δ-1/6)*U^(1/3:ℝ)+
        E*U^(5/6:ℝ)*norm r^(-1/6:ℝ)*C^(-(99/100):ℝ)) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialSelected
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual radial lattice-to-residue error over an arbitrary
level selector. All constants precede the selector and its coefficient family. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem LogarithmicWeightFamily.radial_selected_error
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδsmall : δ ≤ 1/6) :
    ∃ B K E : ℝ, 1 ≤ B ∧ 0 ≤ K ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ)
      (X R U C : ℝ), 0 < R → 0 < U → 0 < C → C ≤ Real.sqrt (B*U) →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ R ≤ norm r) →
      (∀ r ∈ S, Y (w r) ≤ X) →
      ‖∑ r ∈ S, α r*(angularSmoothModel r 0 (W (w r)) U-
        metaplecticMain r 0 (W (w r)) U*metaplecticRadialEulerPartial r C)‖ ≤
      (K*X^s*R^(δ-1/6)*U^(1/3:ℝ)+E*X^s*U^(5/6:ℝ)*R^(-1/6:ℝ)*C^(-(99/100):ℝ))*
        (∑ r ∈ S, ‖α r‖) := by
  obtain ⟨B,K,E,hB,hK,hE,hbound⟩ := hW.radial_short_model_error hδ hs
  refine ⟨B,K,E,hB,hK,hE,?_⟩
  intro w S α X R U C hR hU hC hCD hS hY
  have hbnd (r : Eisenstein) (hr : r ∈ S) :
      ‖angularSmoothModel r 0 (W (w r)) U-
        metaplecticMain r 0 (W (w r)) U*metaplecticRadialEulerPartial r C‖ ≤
      K*X^s*R^(δ-1/6)*U^(1/3:ℝ)+E*X^s*U^(5/6:ℝ)*R^(-1/6:ℝ)*C^(-(99/100):ℝ) := by
    obtain ⟨hp,hsr,hn⟩ := hS r hr
    have hX : 0 < X := zero_lt_one.trans_le ((hW.length_one (w r)).trans (hY r hr))
    have hnr : 0 ≤ norm r := norm_nonneg r
    have hy := Real.rpow_le_rpow (zero_lt_one.trans_le (hW.length_one (w r))).le
      (hY r hr) hs.le
    have hn1 := Real.rpow_le_rpow_of_nonpos hR hn (show δ-1/6 ≤ 0 by linarith)
    have hn2 := Real.rpow_le_rpow_of_nonpos hR hn (by norm_num : (-1/6:ℝ) ≤ 0)
    apply (hbound (w r) r hp hsr U C hU hC hCD).trans
    gcongr
  calc
    _ ≤ ∑ r ∈ S, ‖α r‖*‖angularSmoothModel r 0 (W (w r)) U-
        metaplecticMain r 0 (W (w r)) U*metaplecticRadialEulerPartial r C‖ := by
      simpa only [norm_mul] using norm_sum_le S (fun r => α r*
        (angularSmoothModel r 0 (W (w r)) U-
          metaplecticMain r 0 (W (w r)) U*metaplecticRadialEulerPartial r C))
    _ ≤ ∑ r ∈ S, ‖α r‖*(K*X^s*R^(δ-1/6)*U^(1/3:ℝ)+
        E*X^s*U^(5/6:ℝ)*R^(-1/6:ℝ)*C^(-(99/100):ℝ)) :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hbnd r hr) (_root_.norm_nonneg _))
    _ = _ := by rw [←Finset.sum_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialLowPower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial lattice and the literal short inverse residue agree with
a power saving at the two source cutoffs. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem LogarithmicWeightFamily.radial_model_low_power
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U C : ℝ),
      2 ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      X^(1/50:ℝ) ≤ C → C ≤ X^(13/100:ℝ) →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ R ≤ norm r) →
      (∀ r ∈ S, Y (w r) ≤ X) →
      (∑ r ∈ S, ‖α r‖) ≤ D*R*X^κ →
      ‖∑ r ∈ S, α r*(angularSmoothModel r 0 (W (w r)) U-
        metaplecticMain r 0 (W (w r)) U*metaplecticRadialEulerPartial r C)‖ ≤
        K*X^(41/50:ℝ) := by
  obtain ⟨B,K,E,hB,hK,hE,hbound⟩ := hW.radial_selected_error
    (by norm_num : 0 < κ) (by norm_num : 0 < κ) (by norm_num : κ ≤ 1/6)
  refine ⟨(K+E)*D,by positivity,?_⟩
  intro w S α X R U C hX hR hU hRU hRhi hClo hChi hS hY hmass
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hRp : 0 < R := by linarith
  have hUp : 0 < U := by linarith
  have hCp : 0 < C := (Real.rpow_pos_of_pos hXp _).trans_le hClo
  have hRX : R ≤ X := by rw [←hRU]; exact le_mul_of_one_le_right hRp.le hU
  have hCD := metaplectic_radial_cutoff_le_sqrt hX1 hRp hUp hRU hRhi hB hCp.le hChi
  have hb := hbound w S α X R U C hRp hUp hCp hCD hS hY
  have hfirst : (K*X^κ*R^(κ-1/6)*U^(1/3:ℝ))*(D*R*X^κ) ≤
      (K*D)*X^(41/50:ℝ) := by
    have hp := angular_model_level_power hR hU (by simpa only [hRU] using hRhi)
    rw [hRU] at hp
    calc
      _ = (K*D)*(X^κ*X^κ)*(R*(R^(κ-1/6)*U^(1/3:ℝ))) := by ring
      _ = (K*D)*X^(2*κ)*R^κ*(R^(5/6:ℝ)*U^(1/3:ℝ)) := by
        rw [angular_model_outer_power hRp hUp,←Real.rpow_add hXp]
        have he : κ+κ = 2*κ := by ring
        rw [he]
        ring
      _ ≤ (K*D)*X^(2*κ)*X^κ*X^(589/1000:ℝ) := by gcongr
      _ = (K*D)*((X^(2*κ)*X^κ)*X^(589/1000:ℝ)) := by ring
      _ = (K*D)*X^(3*κ+589/1000) := by
        rw [←Real.rpow_add hXp,←Real.rpow_add hXp]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by positivity)
  have hsecond : (E*X^κ*U^(5/6:ℝ)*R^(-1/6:ℝ)*C^(-(99/100):ℝ))*(D*R*X^κ) ≤
      (E*D)*X^(41/50:ℝ) := by
    have hrscale : R*R^(-1/6:ℝ)*U^(5/6:ℝ) = X^(5/6:ℝ) := by
      rw [←hRU,Real.mul_rpow hRp.le hUp.le]
      congr 1
      calc
        _ = R^(1:ℝ)*R^(-1/6:ℝ) := by rw [Real.rpow_one]
        _ = R^((1:ℝ)+(-1/6)) := (Real.rpow_add hRp _ _).symm
        _ = _ := by norm_num
    calc
      _ = (E*D)*(R*R^(-1/6:ℝ)*U^(5/6:ℝ))*C^(-(99/100):ℝ)*(X^κ*X^κ) := by ring
      _ = (E*D)*(X^(5/6:ℝ)*C^(-(99/100):ℝ)*X^(2/10000:ℝ)) := by
        rw [hrscale,←Real.rpow_add hXp]
        norm_num
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (metaplectic_radial_euler_power hX1 hClo) (by positivity)
  apply hb.trans
  calc
    _ ≤ (K*X^κ*R^(κ-1/6)*U^(1/3:ℝ)+
        E*X^κ*U^(5/6:ℝ)*R^(-1/6:ℝ)*C^(-(99/100):ℝ))*(D*R*X^κ) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (K*X^κ*R^(κ-1/6)*U^(1/3:ℝ))*(D*R*X^κ)+
        (E*X^κ*U^(5/6:ℝ)*R^(-1/6:ℝ)*C^(-(99/100):ℝ))*(D*R*X^κ) := by ring
    _ ≤ (K*D)*X^(41/50:ℝ)+(E*D)*X^(41/50:ℝ) := add_le_add hfirst hsecond
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIMixedWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mixed-term weight from the corrected square. The factor
`(Na)^(-1/6)` is transferred to a fixed smooth test function and the
squarefree model is retained without removing mutual coprimality. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma typeIMixed_power_scale {n U : ℝ} (hn : 0 ≤ n) (hU : 0 < U) :
    U^(-1/6:ℝ)*(n/U)^(-1/6:ℝ) = n^(-1/6:ℝ) := by
  rw [Real.div_rpow hn hU.le]
  have hne : U^(-1/6:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hU _)
  field_simp

lemma typeIMixedGauss_eq (r : Eisenstein) (W : ℝ → ℂ) {U : ℝ} (hU : 0 < U) :
    typeIMixedGauss r W U = ((U^(-1/6:ℝ):ℝ):ℂ)*
      metaplecticAngularSmoothSum r 0 (fun x => ((x^(-1/6:ℝ):ℝ):ℂ)*W x) U 0 := by
  rw [typeIMixedGauss,metaplecticAngularSmoothSum,←tsum_mul_left]
  apply tsum_congr
  intro u
  have hs := congrArg (fun x : ℝ => (x:ℂ)) (typeIMixed_power_scale (norm_nonneg u) hU)
  push_cast at hs
  simp only [theta,zpow_zero,mellinPhase,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one]
  calc
    _ = gauss (r*u)*( ((U^(-1/6:ℝ):ℝ):ℂ)*(((norm u/U)^(-1/6:ℝ):ℝ):ℂ))*W (norm u/U) := by rw [hs]
    _ = _ := by ring

lemma typeIMixedModel_eq (r : Eisenstein) (W : ℝ → ℂ) {U : ℝ} (hU : 0 < U) :
    typeIMixedModel r W U = ((U^(-1/6:ℝ):ℝ):ℂ)*
      angularSmoothModel r 0 (fun x => ((x^(-1/6:ℝ):ℝ):ℂ)*W x) U := by
  rw [typeIMixedModel,angularSmoothModel,←tsum_mul_left]
  apply tsum_congr
  intro u
  by_cases hu : primary u
  · have hs := congrArg (fun x : ℝ => (x:ℂ)) (typeIMixed_power_scale (norm_nonneg u) hU)
    push_cast at hs
    simp only [hu,ite_true, if_true,theta,zpow_zero,one_mul]
    push_cast
    calc
      _ = (idealMoebius (r*u):ℂ)^2*(cStar:ℂ)*((norm (r*u)^(-1/6:ℝ):ℝ):ℂ)*
          (((U^(-1/6:ℝ):ℝ):ℂ)*(((norm u/U)^(-1/6:ℝ):ℝ):ℂ))*W (norm u/U) := by rw [hs]; ring
      _ = _ := by ring
  · simp only [hu,ite_false, if_false,mul_zero]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialTypeILow
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial low-height Type-I estimate, including the literal finite residue density. The short and
long inverse sums are actual finite sums, and the coefficient masses
are deduced from the literal primary-divisor bound. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem cubicTheta_radial_typeI_low_squarefree
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*(metaplecticAngularSmoothSum r 0 (W (w r)) U 0-
        angularSmoothModel r 0 (W (w r)) U)‖ ≤ K*X^(5/6-1/100:ℝ) := by
  obtain ⟨D,hD,hcoef⟩ := metaplectic_divisor_coefficient_power (by norm_num : 0 < κ) hA k
  obtain ⟨KS,hKS,hshort⟩ := hW.cubicTheta_centered_short_low_power 0
    (show 0 ≤ 36*D by positivity)
  obtain ⟨KM,hKM,hmodel⟩ := hW.radial_model_low_power (show 0 ≤ 36*D by positivity)
  obtain ⟨KC,hKC,hcount⟩ := hW.metaplectic_long_small_power hB (show 0 ≤ 36*D by positivity)
  obtain ⟨KL,hKL,hlarge⟩ := hW.metaplectic_long_large_power hB (show 0 ≤ 36*D^2 by positivity)
  refine ⟨KS+KM+KC+KL,by positivity,?_⟩
  intro w S α X R U hX hBX hR hU hRU hRhi hS hY hcut hα
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hRp : 0 < R := by linarith
  have hUp : 0 < U := by linarith
  have hRX : R ≤ X := by rw [←hRU]; exact le_mul_of_one_le_right hRp.le hU
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left hUp.le hR
  have hB0 : 0 ≤ B := by linarith
  have hBU : B*U ≤ X^2 := by nlinarith [mul_le_mul hBX hUX hUp.le hXp.le]
  have hp (r : Eisenstein) (hr : r ∈ S) : primary r := (hS r hr).1
  have hsn (r : Eisenstein) (hr : r ∈ S) : primary r ∧ norm r ≤ 2*R :=
    ⟨hp r hr,(hS r hr).2.2.2⟩
  have hsfull (r : Eisenstein) (hr : r ∈ S) : primary r ∧ Squarefree r ∧ norm r ≤ 2*R :=
    ⟨hp r hr,(hS r hr).2.1,(hS r hr).2.2.2⟩
  have hym (r : Eisenstein) (hr : r ∈ S) : Y (w r) ≤ X := (hY r hr).le
  have hab (r : Eisenstein) (hr : r ∈ S) : ‖α r‖ ≤ D*X^κ :=
    hcoef r (hp r hr) X hX1 ((hS r hr).2.2.2.trans (by linarith)) (α r) (hα r hr)
  obtain ⟨hm1,hm2⟩ := metaplectic_level_masses S α hRp.le (by positivity) hsn hab
  have hm1' : (∑ r ∈ S, ‖α r‖) ≤ (36*D)*R*X^κ := by
    convert hm1 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hm2' : (∑ r ∈ S, ‖α r‖^2) ≤ (36*D^2)*R*X^(2*κ) := by
    apply hm2.trans_eq
    have hx : (X^κ)^2 = X^(2*κ) := by
      rw [←Real.rpow_mul_natCast hXp.le]
      norm_num
    rw [mul_pow,hx]
    ring
  let C : ℝ := if R ≤ X^(2/5:ℝ) then X^(13/100:ℝ) else X^(1/50:ℝ)
  have hCpos : 0 < C := by dsimp [C]; split_ifs <;> positivity
  have hCX : C ≤ X := by
    dsimp [C]
    split_ifs
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1 (show (13/100:ℝ) ≤ 1 by norm_num)
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1 (show (1/50:ℝ) ≤ 1 by norm_num)
  have hscale : R^(3/2:ℝ)*C^(3/2:ℝ) ≤ X^(159/200:ℝ) := by
    dsimp [C]
    split_ifs with hs
    · exact metaplectic_short_small_power hX1 hRp.le hs
    · exact metaplectic_short_large_power hX1 hRp.le hRhi
  have hs := hshort w S α X R U C hX hR hU hRU hCpos.le hCX hscale hsfull hY hm1'
  have hClo : X^(1/50:ℝ) ≤ C := by
    dsimp [C]
    split_ifs
    · exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    · exact le_rfl
  have hChi : C ≤ X^(13/100:ℝ) := by
    dsimp [C]
    split_ifs
    · exact le_rfl
    · exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hm := hmodel w S α X R U C hX hR hU hRU hRhi hClo hChi
    (fun r hr => ⟨hp r hr,(hS r hr).2.1,(hS r hr).2.2.1⟩) hym hm1'
  have hl : ‖∑ r ∈ S, α r*metaplecticLongCompletion r 0 (W (w r)) U C (X^2)‖ ≤
      (KC+KL)*X^(41/50:ℝ) := by
    dsimp [C]
    split_ifs with hsmall
    · exact (hcount w S α 0 X R U hX hBX hR hU hRU hp hym hcut hm1').trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · exact (hlarge w S α 0 X R U hX hBX hR hU hRU (le_of_lt (lt_of_not_ge hsmall))
        hRhi hsn hym hcut hm2').trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have he : (∑ r ∈ S, α r*(metaplecticAngularSmoothSum r 0 (W (w r)) U 0-
        angularSmoothModel r 0 (W (w r)) U)) =
      (∑ r ∈ S, α r*metaplecticShortCompletionError r 0 (W (w r)) U C)+
      (∑ r ∈ S, α r*metaplecticLongCompletion r 0 (W (w r)) U C (X^2))-
      (∑ r ∈ S, α r*(angularSmoothModel r 0 (W (w r)) U-
        metaplecticMain r 0 (W (w r)) U*metaplecticRadialEulerPartial r C)) := by
    rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [metaplectic_inverse_split r 0 (W (w r)) hUp hB0 hBU
      (hCX.trans (by nlinarith : X ≤ X^2)) (hcut r hr),
      metaplectic_short_residue_eq r (W (w r)) hUp C]
    simp only [metaplecticMain,ite_true, if_true]
    ring
  rw [he]
  calc
    _ ≤ (‖∑ r ∈ S, α r*metaplecticShortCompletionError r 0 (W (w r)) U C‖+
      ‖∑ r ∈ S, α r*metaplecticLongCompletion r 0 (W (w r)) U C (X^2)‖)+
      ‖∑ r ∈ S, α r*(angularSmoothModel r 0 (W (w r)) U-
        metaplecticMain r 0 (W (w r)) U*metaplecticRadialEulerPartial r C)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ KS*X^(41/50:ℝ)+(KC+KL)*X^(41/50:ℝ)+KM*X^(41/50:ℝ) :=
      add_le_add (add_le_add hs hl) hm
    _ = (KS+KM+KC+KL)*X^(41/50:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by positivity)

theorem cubicTheta_radial_typeI_low
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*(metaplecticAngularSmoothSum r 0 (W (w r)) U 0-
        angularSmoothModel r 0 (W (w r)) U)‖ ≤ K*X^(5/6-1/100:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := cubicTheta_radial_typeI_low_squarefree hW hB hA k
  refine ⟨K,hK,?_⟩
  intro w S α X R U hX hBX hR hU hRU hRhi hS hY hcut hα
  let T := S.filter Squarefree
  have hT (r : Eisenstein) (hr : r ∈ T) : r ∈ S ∧ Squarefree r := Finset.mem_filter.mp hr
  have he : (∑ r ∈ S, α r*(metaplecticAngularSmoothSum r 0 (W (w r)) U 0-
      angularSmoothModel r 0 (W (w r)) U)) =
      ∑ r ∈ T, α r*(metaplecticAngularSmoothSum r 0 (W (w r)) U 0-
        angularSmoothModel r 0 (W (w r)) U) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r hr hn
    have hsf : ¬Squarefree r := fun hs => hn (Finset.mem_filter.mpr ⟨hr,hs⟩)
    rw [metaplecticAngularSmoothSum_zero_of_not_squarefree (hS r hr).1 hsf,
      angularSmoothModel_zero_of_not_squarefree hsf,sub_self,mul_zero]
  rw [he]
  exact hbound w T α X R U hX hBX hR hU hRU hRhi
    (fun r hr => ⟨(hS r (hT r hr).1).1,(hT r hr).2,(hS r (hT r hr).1).2⟩)
    (fun r hr => hY r (hT r hr).1) (fun r hr => hcut r (hT r hr).1)
    (fun r hr => hα r (hT r hr).1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTypeILow
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonzero-angular theta formula supplies this central estimate. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem angular_typeI_low_squarefree_proved
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U)‖ ≤ K*X^(5/6-1/100:ℝ) := by
  obtain ⟨D,hD,hcoef⟩ := metaplectic_divisor_coefficient_power (by norm_num : 0 < κ) hA k
  obtain ⟨KS,hKS,hshort⟩ := hW.cubicTheta_short_low_power ℓ hℓ
    (show 0 ≤ 36*D by positivity)
  obtain ⟨KM,hKM,hmodel⟩ := hW.angular_model_low_power hℓ (show 0 ≤ 36*D by positivity)
  obtain ⟨KC,hKC,hcount⟩ := hW.metaplectic_long_small_power hB (show 0 ≤ 36*D by positivity)
  obtain ⟨KL,hKL,hlarge⟩ := hW.metaplectic_long_large_power hB (show 0 ≤ 36*D^2 by positivity)
  refine ⟨KS+KM+KC+KL,by positivity,?_⟩
  intro w S α X R U hX hBX hR hU hRU hRhi hS hY hcut hα
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hRp : 0 < R := by linarith
  have hUp : 0 < U := by linarith
  have hRX : R ≤ X := by rw [←hRU]; exact le_mul_of_one_le_right hRp.le hU
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left hUp.le hR
  have hB0 : 0 ≤ B := by linarith
  have hBU : B*U ≤ X^2 := by nlinarith [mul_le_mul hBX hUX hUp.le hXp.le]
  have hp (r : Eisenstein) (hr : r ∈ S) : primary r := (hS r hr).1
  have hsn (r : Eisenstein) (hr : r ∈ S) : primary r ∧ norm r ≤ 2*R :=
    ⟨hp r hr,(hS r hr).2.2.2⟩
  have hsfull (r : Eisenstein) (hr : r ∈ S) : primary r ∧ Squarefree r ∧ norm r ≤ 2*R :=
    ⟨hp r hr,(hS r hr).2.1,(hS r hr).2.2.2⟩
  have hym (r : Eisenstein) (hr : r ∈ S) : Y (w r) ≤ X := (hY r hr).le
  have hab (r : Eisenstein) (hr : r ∈ S) : ‖α r‖ ≤ D*X^κ :=
    hcoef r (hp r hr) X hX1 ((hS r hr).2.2.2.trans (by linarith)) (α r) (hα r hr)
  obtain ⟨hm1,hm2⟩ := metaplectic_level_masses S α hRp.le (by positivity) hsn hab
  have hm1' : (∑ r ∈ S, ‖α r‖) ≤ (36*D)*R*X^κ := by
    convert hm1 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hm2' : (∑ r ∈ S, ‖α r‖^2) ≤ (36*D^2)*R*X^(2*κ) := by
    apply hm2.trans_eq
    have hx : (X^κ)^2 = X^(2*κ) := by
      rw [←Real.rpow_mul_natCast hXp.le]
      norm_num
    rw [mul_pow,hx]
    ring
  let C : ℝ := if R ≤ X^(2/5:ℝ) then X^(13/100:ℝ) else X^(1/50:ℝ)
  have hCpos : 0 < C := by dsimp [C]; split_ifs <;> positivity
  have hCX : C ≤ X := by
    dsimp [C]
    split_ifs
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1 (show (13/100:ℝ) ≤ 1 by norm_num)
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1 (show (1/50:ℝ) ≤ 1 by norm_num)
  have hscale : R^(3/2:ℝ)*C^(3/2:ℝ) ≤ X^(159/200:ℝ) := by
    dsimp [C]
    split_ifs with hs
    · exact metaplectic_short_small_power hX1 hRp.le hs
    · exact metaplectic_short_large_power hX1 hRp.le hRhi
  have hs := hshort w S α X R U C hX hR hU hRU hCpos.le hCX hscale hsfull hY hm1'
  have hm := hmodel w S α X R U hX hR hU hRU hRhi
    (fun r hr => ⟨hp r hr,(hS r hr).2.1,(hS r hr).2.2.1⟩) hym hm1'
  have hl : ‖∑ r ∈ S, α r*metaplecticLongCompletion r ℓ (W (w r)) U C (X^2)‖ ≤
      (KC+KL)*X^(41/50:ℝ) := by
    dsimp [C]
    split_ifs with hsmall
    · exact (hcount w S α ℓ X R U hX hBX hR hU hRU hp hym hcut hm1').trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · exact (hlarge w S α ℓ X R U hX hBX hR hU hRU (le_of_lt (lt_of_not_ge hsmall))
        hRhi hsn hym hcut hm2').trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have he : (∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U)) =
      (∑ r ∈ S, α r*metaplecticShortCompletionError r ℓ (W (w r)) U C)+
      (∑ r ∈ S, α r*metaplecticLongCompletion r ℓ (W (w r)) U C (X^2))-
      (∑ r ∈ S, α r*angularSmoothModel r ℓ (W (w r)) U) := by
    rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [metaplectic_angular_inverse_split r hℓ (W (w r)) hUp hB0 hBU
      (hCX.trans (by nlinarith : X ≤ X^2)) (hcut r hr)]
    ring
  rw [he]
  calc
    _ ≤ (‖∑ r ∈ S, α r*metaplecticShortCompletionError r ℓ (W (w r)) U C‖+
      ‖∑ r ∈ S, α r*metaplecticLongCompletion r ℓ (W (w r)) U C (X^2)‖)+
      ‖∑ r ∈ S, α r*angularSmoothModel r ℓ (W (w r)) U‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ KS*X^(41/50:ℝ)+(KC+KL)*X^(41/50:ℝ)+KM*X^(41/50:ℝ) :=
      add_le_add (add_le_add hs hl) hm
    _ = (KS+KM+KC+KL)*X^(41/50:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by positivity)

theorem angular_typeI_low_proved
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U)‖ ≤ K*X^(5/6-1/100:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := angular_typeI_low_squarefree_proved hW ℓ hℓ hB hA k
  refine ⟨K,hK,?_⟩
  intro w S α X R U hX hBX hR hU hRU hRhi hS hY hcut hα
  let T := S.filter Squarefree
  have hT (r : Eisenstein) (hr : r ∈ T) : r ∈ S ∧ Squarefree r := Finset.mem_filter.mp hr
  have he : (∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
      angularSmoothModel r ℓ (W (w r)) U)) =
      ∑ r ∈ T, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r hr hn
    have hsf : ¬Squarefree r := fun hs => hn (Finset.mem_filter.mpr ⟨hr,hs⟩)
    rw [metaplecticAngularSmoothSum_zero_of_not_squarefree (hS r hr).1 hsf,
      angularSmoothModel_zero_of_not_squarefree hsf,sub_self,mul_zero]
  rw [he]
  exact hbound w T α X R U hX hBX hR hU hRU hRhi
    (fun r hr => ⟨(hS r (hT r hr).1).1,(hT r hr).2,(hS r (hT r hr).1).2⟩)
    (fun r hr => hY r (hT r hr).1) (fun r hr => hcut r (hT r hr).1)
    (fun r hr => hα r (hT r hr).1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAllTypeILow
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common low-height Type-I interface for every fixed angular mode.
The radial residue and the nonzero-angular lattice cancellation have
both been proved before this final case split. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicTheta_typeI_low
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) 
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U)‖ ≤ K*X^(5/6-1/100:ℝ) := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    exact cubicTheta_radial_typeI_low hW hB hA k
  · exact angular_typeI_low_proved hW ℓ hℓ hB hA k

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTypeILogCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed logarithmic coefficient factors can be retained in the actual
weight family. This is the form used by short logarithmic convolutions. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem cubicTheta_typeI_low_log_coefficients
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) 
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k*(1+Real.log X)^d) →
      ‖∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U)‖ ≤ K*X^(5/6-1/100:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := cubicTheta_typeI_low (hW.logPower d) ℓ hB hA k
  refine ⟨K,hK,?_⟩
  intro w S α X R U hX hBX hR hU hRU hRhi hS hY hcut hα
  let L : ℝ := (1+Real.log X)^d
  have hLb : 0 < 1+Real.log X := by
    linarith [Real.log_nonneg (show 1 ≤ X by linarith)]
  have hLp : 0 < L := pow_pos hLb _
  have hLc : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLp.ne'
  let β : Eisenstein → ℂ := fun r => α r/(L:ℂ)
  have hβ (r : Eisenstein) (hr : r ∈ S) :
      ‖β r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k := by
    rw [show β r = α r/(L:ℂ) from rfl,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
    exact (div_le_iff₀ hLp).mpr (hα r hr)
  have hv (r : Eisenstein) (hr : r ∈ S) :
      logPowerWeight Y W d (w r) = fun x => (L:ℂ)*W (w r) x := by
    funext x
    simp only [logPowerWeight,hY r hr,Complex.real_smul,L]
  have he : (∑ r ∈ S, β r*(metaplecticAngularSmoothSum r ℓ (logPowerWeight Y W d (w r)) U 0-
      angularSmoothModel r ℓ (logPowerWeight Y W d (w r)) U)) =
    ∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
      angularSmoothModel r ℓ (W (w r)) U) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [hv r hr,metaplecticAngularSmoothSum_const_mul,angularSmoothModel_const_mul]
    dsimp [β]
    field_simp [hLc]
  rw [←he]
  exact hbound w S β X R U hX hBX hR hU hRU hRhi hS hY
    (fun r hr x hx => by
      rw [hv r hr]
      change (L:ℂ)*W (w r) x = 0
      rw [hcut r hr x hx,mul_zero]) hβ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTypeIMixedLow
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Type I with the precise radial factor in the mixed term of the
corrected square. The squarefree product model, including common zeros,
is preserved on the right. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicTheta_typeI_mixed_low
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {B D : ℝ} (hB : 1 ≤ B) (hD : 0 ≤ D) (k d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (β : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖β r‖ ≤ D*((metaplecticPrimaryDivisors r).card:ℝ)^k*(1+Real.log X)^d) →
      ‖∑ r ∈ S, β r*(typeIMixedGauss r (W (w r)) U-typeIMixedModel r (W (w r)) U)‖ ≤
        K*U^(-1/6:ℝ)*X^(5/6-1/100:ℝ) := by
  let hP := hW.realPower (-1/6)
  obtain ⟨K,hK,hbound⟩ := cubicTheta_typeI_low_log_coefficients hP.logarithmicWithLength 0 hB hD k d
  refine ⟨K,hK,?_⟩
  intro w S β X R U hX hBX hR hU hRU hRhi hS hcut hβ
  let v : Eisenstein → γ × {X : ℝ // 1 ≤ X} := fun r => (w r,⟨X,by linarith⟩)
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hb := hbound v S β X R U hX hBX hR hU hRU hRhi hS
    (fun _ _ => rfl) (fun r hr x hx => by
      change ((x^(-1/6:ℝ):ℝ):ℂ)*W (w r) x = 0
      rw [hcut r hr x hx,mul_zero]) hβ
  have he : (∑ r ∈ S, β r*(typeIMixedGauss r (W (w r)) U-typeIMixedModel r (W (w r)) U)) =
      ((U^(-1/6:ℝ):ℝ):ℂ)*(∑ r ∈ S, β r*
        (metaplecticAngularSmoothSum r 0 (fun x => ((x^(-1/6:ℝ):ℝ):ℂ)*W (w r) x) U 0-
          angularSmoothModel r 0 (fun x => ((x^(-1/6:ℝ):ℝ):ℂ)*W (w r) x) U)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [typeIMixedGauss_eq r _ hUp,typeIMixedModel_eq r _ hUp]
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hUp _)]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hUp.le _)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralTypeIAdapters
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing low-height interfaces follow from the proved actual theta
transform, including its normalized radial constant. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem typeI_mixed_low_actual
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (_hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {B D : ℝ} (hB : 1 ≤ B) (hD : 0 ≤ D) (k d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (β : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖β r‖ ≤ D*((metaplecticPrimaryDivisors r).card:ℝ)^k*(1+Real.log X)^d) →
      ‖∑ r ∈ S, β r*(typeIMixedGauss r (W (w r)) U-typeIMixedModel r (W (w r)) U)‖ ≤
        K*U^(-1/6:ℝ)*X^(5/6-1/100:ℝ) :=
  cubicTheta_typeI_mixed_low hW hB hD k d

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralTypeIMixedPrime
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed-term replacement for the literal logarithmic prime
convolution, including its norm phase. Coefficient size is derived from
the fixed number of prime factors and the actual weight family. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem logarithmic_prime_typeI_mixed_actual
    {γ : Type*} {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {δ : Type*} {V : δ → ℝ → ℂ} (hVw : UniformLogWeights V)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : γ) (Xi : ι → ℝ) (R₀ : ℝ)
      (w : Eisenstein → δ) (S : Finset Eisenstein) (t X R U : ℝ),
      1 ≤ L j → L j ≤ X → 2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U →
      R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → V (w r) x = 0) →
      let β := fun r => fullPrimeCoefficient R₀ (W j) Xi r*normTwist t r
      ‖∑ r ∈ S, β r*(typeIMixedGauss r (V (w r)) U-typeIMixedModel r (V (w r)) U)‖ ≤
        K*U^(-1/6:ℝ)*X^(5/6-1/100:ℝ) := by
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  let n := Fintype.card ι
  let D : ℝ := (n^n:ℕ)*M^n
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM _)
  obtain ⟨K,hK,hbound⟩ := typeI_mixed_low_actual  hVw hGamma hB hD 0 (m*n)
  refine ⟨K,hK,?_⟩
  intro j Xi R₀ w S t X R U hL hLX hX hBX hR hU hRU hRhi hS hcut
  apply hbound w S _ X R U hX hBX hR hU hRU hRhi hS hcut
  intro r hr
  have hz : 0 ≤ 1+Real.log (L j) := by linarith [Real.log_nonneg hL]
  have hlog : 1+Real.log (L j) ≤ 1+Real.log X := by
    linarith [Real.log_le_log (zero_lt_one.trans_le hL) hLX]
  have hb := fullPrimeCoefficient_norm_bound R₀ (W j) Xi
    (fun _ => M*(1+Real.log (L j))^m)
    (fun _ => mul_nonneg hM (pow_nonneg hz _)) (fun i x => hMb (j,i) x) r
  calc
    ‖fullPrimeCoefficient R₀ (W j) Xi r*normTwist t r‖ =
        ‖fullPrimeCoefficient R₀ (W j) Xi r‖ := by rw [norm_mul,norm_normTwist,mul_one]
    _ ≤ D*(1+Real.log (L j))^(m*n) := by
      simpa only [D,n,Finset.prod_const,Finset.card_univ,mul_pow,←pow_mul,mul_assoc] using hb
    _ ≤ D*(1+Real.log X)^(m*n) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hlog _) hD
    _ = D*((metaplecticPrimaryDivisors r).card:ℝ)^0*(1+Real.log X)^(m*n) := by simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCentralTypeIMixedFull
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the auxiliary level dyad from the actual prime-convolution
mixed term. Only a fixed dilation of the product norm interval is used. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem logarithmic_prime_typeI_mixed_full_actual_oai
    {γ : Type*} {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {δ : Type*} {V : δ → ℝ → ℂ} (hVw : UniformLogWeights V)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {B R₀ : ℝ} (hB : 1 ≤ B) (J : ℕ) (hJ : R₀^Fintype.card ι < (2:ℝ)^J) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : γ) (Xi : ι → ℝ) (e : Eisenstein)
      (w : Eisenstein → δ) (t U : ℝ),
      1 ≤ L j → (∀ i, 0 < Xi i) → (∏ i, Xi i) = L j →
      (∀ i x, x < 1 → W j i x = 0) → (∀ i x, R₀ < x → W j i x = 0) →
      1 ≤ U → 2 ≤ L j*U → B ≤ L j*U → (2:ℝ)^J*L j ≤ (L j*U)^(51/100:ℝ) →
      (∀ r ∈ fullSquarefreePrimeSupport R₀ (W j) Xi e, ∀ x : ℝ, B < x → V (w r) x = 0) →
      let β := fun r => fullPrimeCoefficient R₀ (W j) Xi r*normTwist t r
      ‖∑ r ∈ fullSquarefreePrimeSupport R₀ (W j) Xi e,
          β r*(typeIMixedGauss r (V (w r)) U-typeIMixedModel r (V (w r)) U)‖ ≤
        K*U^(-1/6:ℝ)*(L j*U)^(5/6-1/100:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := logarithmic_prime_typeI_mixed_actual  hW hVw hGamma hB
  let C : ℝ := (2:ℝ)^J
  let p : ℝ := 5/6-1/100
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨(J:ℝ)*K*C^p,by positivity,?_⟩
  intro j Xi e w t U hL hXi hprod hlo hhi hU hX hBX hscale hcut
  let S := fullSquarefreePrimeSupport R₀ (W j) Xi e
  let β := fun r => fullPrimeCoefficient R₀ (W j) Xi r*normTwist t r
  have hLp : 0 < L j := zero_lt_one.trans_le hL
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hXp : 0 < L j*U := mul_pos hLp hUp
  have hSn (r : Eisenstein) (hr : r ∈ S) :
      L j ≤ norm r ∧ norm r ≤ R₀^Fintype.card ι*L j := by
    simpa only [hprod] using fullPrimeProduct_norm_bounds R₀ (W j) Xi hXi hlo hhi
      (Finset.mem_filter.mp hr).1
  change ‖∑ r ∈ S, β r*(typeIMixedGauss r (V (w r)) U-typeIMixedModel r (V (w r)) U)‖ ≤
    ((J:ℝ)*K*C^p)*U^(-1/6:ℝ)*(L j*U)^p
  rw [typeIMixedDyad_partition S hLp hJ hSn]
  calc
    _ ≤ ∑ i ∈ Finset.range J, ‖∑ r ∈ typeIMixedDyad S (L j) i,
        β r*(typeIMixedGauss r (V (w r)) U-typeIMixedModel r (V (w r)) U)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range J, K*U^(-1/6:ℝ)*(C*(L j*U))^p := by
      apply Finset.sum_le_sum
      intro i hi
      let R := L j*(2:ℝ)^i
      have hiJ : i ≤ J := (Finset.mem_range.mp hi).le
      have hpow : (2:ℝ)^i ≤ C := pow_le_pow_right₀ (by norm_num) hiJ
      have hLR : L j ≤ R := by
        dsimp [R]
        exact le_mul_of_one_le_right hLp.le (one_le_pow₀ (by norm_num))
      have hR : 1 ≤ R := hL.trans hLR
      have hRC : R ≤ C*L j := by
        dsimp [R]
        nlinarith [mul_le_mul_of_nonneg_left hpow hLp.le]
      have hXR : L j*U ≤ R*U := mul_le_mul_of_nonneg_right hLR hUp.le
      have hRX : R ≤ (R*U)^(51/100:ℝ) :=
        (hRC.trans hscale).trans (Real.rpow_le_rpow hXp.le hXR (by norm_num))
      have hlevels (r : Eisenstein) (hr : r ∈ typeIMixedDyad S (L j) i) :
          primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R := by
        have hm := Finset.mem_filter.mp hr
        have hn := typeIMixedDyadIndex_bounds hLp (hSn r hm.1).1
        rw [hm.2] at hn
        exact ⟨(fullSquarefreePrimeSupport_primary R₀ (W j) Xi e hm.1).1,hn.1,hn.2.le⟩
      have hb := hbound j Xi R₀ w (typeIMixedDyad S (L j) i) t (R*U) R U hL
        ((le_mul_of_one_le_right hLp.le hU).trans hXR) (hX.trans hXR) (hBX.trans hXR)
        hR hU rfl hRX hlevels (fun r hr => hcut r (Finset.mem_filter.mp hr).1)
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (Real.rpow_nonneg hUp.le _))
      apply Real.rpow_le_rpow (by positivity : 0 ≤ R*U) _ (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hRC hUp.le]
    _ = ((J:ℝ)*K*C^p)*U^(-1/6:ℝ)*(L j*U)^p := by
      rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Real.mul_rpow hC hXp.le]
      ring

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual_oai.{u_1, u_2, u_3} := @OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual_oai.{u_1, u_2, u_3}
