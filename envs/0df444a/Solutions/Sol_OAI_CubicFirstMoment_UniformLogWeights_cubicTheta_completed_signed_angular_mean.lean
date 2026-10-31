-- Prove2me | solution 1 for OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_completed_signed_angular_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:58:55.990698+00:00
-- url     : https://prove2.me/submissions/60e071b2-179a-4bfb-b30a-43d06afcdb95

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_cubicTheta_completed_negative_tail_mean
import Theorems.Thm_OAI_CubicFirstMoment_cubicTheta_completed_tail_mean

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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

/-- Finite Cauchy--Schwarz for the actual complex row sum. -/
theorem complex_bilinear_rows_sq {ι : Type*} (A : Finset ι) (α F : ι → ℂ) :
    ‖∑ a ∈ A, α a * F a‖ ^ 2 ≤
      (∑ a ∈ A, ‖α a‖ ^ 2) * ∑ a ∈ A, ‖F a‖ ^ 2 := by
  calc
    _ ≤ (∑ a ∈ A, ‖α a * F a‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (norm_sum_le _ _) 2
    _ = (∑ a ∈ A, ‖α a‖ * ‖F a‖) ^ 2 := by simp_rw [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq A _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeFunctionalEquation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebra of the published primitive Hecke functional equation.
The completion uses A = sqrt(3 D)/(2 pi), where D is the ideal conductor
norm. See Watkins (2011), Section 3.6, and Rajan (1998), Section 1,
pp. 281--283 for the fixed infinity-type completion. The uncompleted and symmetry-line identities follow from that exact equation. -/

noncomputable section
namespace CubicFirstMoment

lemma hecke_scale_phase {Z : ℝ} (hZ : 0 < Z) (τ : ℝ) :
    (Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I) =
      (Real.sqrt Z:ℂ)*mellinPhase τ Z := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hZ.ne'),
    ← Complex.ofReal_log hZ.le,Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hZ,Complex.ofReal_exp]
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour shifting for the Mellin integrals in the smooth Hecke sum.
The horizontal edges are kept explicit until a uniform decay bound is
available; no functional equation or dual-sum estimate is assumed here. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace CubicFirstMoment

lemma mellin_rectangle_identity {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (T : ℝ) :
    (∫ x in a..b, f (x - (T : ℂ) * Complex.I)) -
      (∫ x in a..b, f (x + (T : ℂ) * Complex.I)) +
      Complex.I * (∫ y in -T..T, f (b + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in -T..T, f (a + (y : ℂ) * Complex.I)) = 0 := by
  have hd := hf.mono (show
      (Set.uIcc a b ×ℂ Set.uIcc (-T) T) ⊆ closedVerticalStrip a b from by
    intro z hz
    simpa only [Set.uIcc_of_le hab, Set.mem_preimage, Set.mem_Icc,
      closedVerticalStrip, Set.mem_ofPred_eq] using hz.1)
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) - (T : ℂ) * Complex.I) ((b : ℂ) + (T : ℂ) * Complex.I)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.add_im, mul_zero,
    sub_zero, add_zero, zero_sub, mul_one, zero_add] at h
  simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.add_im, mul_zero, zero_mul,
    sub_zero, add_zero, zero_sub, mul_one, zero_add, Complex.ofReal_neg,
    neg_mul, add_neg_cancel, sub_self, smul_eq_mul, sub_eq_add_neg] using h hd

/-- Vertical Mellin integrals agree after shifting through a holomorphic
strip, once both horizontal edges vanish. -/
theorem mellin_contour_shift {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (ha : Integrable (fun y : ℝ => f (a + (y : ℂ) * Complex.I)))
    (hb : Integrable (fun y : ℝ => f (b + (y : ℂ) * Complex.I)))
    (hTop : Tendsto (fun T : ℝ => ∫ x in a..b, f (x + (T : ℂ) * Complex.I))
      atTop (𝓝 0))
    (hBot : Tendsto (fun T : ℝ => ∫ x in a..b, f (x - (T : ℂ) * Complex.I))
      atTop (𝓝 0)) :
    (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ, f (b + (y : ℂ) * Complex.I) := by
  have hia := intervalIntegral_tendsto_integral ha
    tendsto_neg_atTop_atBot tendsto_id
  have hib := intervalIntegral_tendsto_integral hb
    tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hBot.sub hTop).add (hib.const_mul Complex.I)).sub
    (hia.const_mul Complex.I)
  have hz : (0 : ℂ) + Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) = 0 := by
    have hz' : 0 - 0 + Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) = 0 := by
      apply tendsto_nhds_unique hlim
      apply tendsto_const_nhds.congr'
      exact Filter.Eventually.of_forall (fun T => (mellin_rectangle_identity hab f hf T).symm)
    simpa only [sub_self] using hz'
  have he : Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) := by
    linear_combination -hz
  exact mul_left_cancel₀ Complex.I_ne_zero he

/-- A common decaying majorant supplies both horizontal limits. This is
the form used for a rapidly decreasing Mellin transform times an
L-function of polynomial growth. -/
theorem mellin_contour_shift_of_majorant {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (H : ℝ → ℝ) (hH : Integrable H)
    (hHtop : Tendsto H atTop (𝓝 0)) (hHbot : Tendsto H atBot (𝓝 0))
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (x + (t : ℂ) * Complex.I)‖ ≤ H t) :
    (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ, f (b + (y : ℂ) * Complex.I) := by
  have hline (x : ℝ) (hx : x ∈ Icc a b) :
      Integrable (fun y : ℝ => f (x + (y : ℂ) * Complex.I)) := by
    have hc : Continuous (fun y : ℝ => f (x + (y : ℂ) * Complex.I)) :=
      hf.continuousOn.comp_continuous
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
        (by intro y; simpa [closedVerticalStrip] using hx)
    exact hH.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall (hbound x hx))
  have hedge (t : ℝ) :
      ‖∫ x in a..b, f (x + (t : ℂ) * Complex.I)‖ ≤ H t * |b-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    apply hbound x
    rw [Set.uIoc_of_le hab] at hx
    exact ⟨hx.1.le,hx.2⟩
  apply mellin_contour_shift hab f hf
    (hline a ⟨le_rfl,hab⟩) (hline b ⟨hab,le_rfl⟩)
  · exact squeeze_zero_norm hedge (by simpa using hHtop.mul_const |b-a|)
  · have he : Tendsto (fun T : ℝ => ∫ x in a..b, f (x + ((-T : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 0) :=
      squeeze_zero_norm (fun T => hedge (-T))
        (by simpa using (hHbot.comp tendsto_neg_atTop_atBot).mul_const |b-a|)
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using he

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinStrip
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform rapid Mellin decay on a fixed closed real strip. The bound
comes from the actual compact logarithmic support, not an additional
analytic input. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

private lemma exp_linear_deriv_bound {M R σ u : ℝ} (hM : 0 ≤ M)
    (hσ : |σ| ≤ M) (hu : |u| ≤ R) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v : ℝ => Real.exp (-σ*v)) u‖ ≤
      M^n * Real.exp (M*R) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul]
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hσ n) _ (by positivity) (by positivity)
  apply Real.exp_le_exp.mpr
  calc
    -σ*u ≤ |-σ*u| := le_abs_self _
    _ = |σ| * |u| := by rw [abs_mul,abs_neg]
    _ ≤ M*R := mul_le_mul hσ hu (abs_nonneg _) hM

private lemma mellinLogSchwartz_eq_smul (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) :
    (mellinLogSchwartz W hW hpos hsm σ : ℝ → ℂ) =
      fun u => Real.exp (-σ*u) • mellinLogSchwartz W hW hpos hsm 0 u := by
  ext u
  simp [mellinLogSchwartz_apply]

theorem mellinLogSchwartz_seminorm_uniform (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ)
    (k n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n (mellinLogSchwartz W hW hpos hsm σ) ≤ C := by
  let G := mellinLogSchwartz W hW hpos hsm 0
  obtain ⟨R₀,hR₀⟩ := (logPullback_compact W hW hpos).isCompact.isBounded.exists_norm_le
  let R := max R₀ 1
  let M' := max M 0
  let B := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    (M'^i * Real.exp (M'*R)) * SchwartzMap.seminorm ℝ 0 (n-i) G
  have hR : 0 ≤ R := le_trans zero_le_one (le_max_right _ _)
  have hM : 0 ≤ M' := le_max_right _ _
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => by positivity)
  refine ⟨R^k*B, by positivity, ?_⟩
  intro σ hσ
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ R
  · have he : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (-σ*v)) := by fun_prop
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) he (G.smooth ⊤) u
      (n := n) (mod_cast le_top)
    have hg (i : ℕ) : ‖iteratedFDeriv ℝ i G u‖ ≤ SchwartzMap.seminorm ℝ 0 i G := by
      simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm ℝ 0 i G u
    have hb : ‖iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u‖ ≤ B := by
      rw [mellinLogSchwartz_eq_smul W hW hpos hsm σ]
      apply hd.trans
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (exp_linear_deriv_bound hM (hσ.trans (le_max_left _ _)) hu i) (by positivity)
      · exact hg (n-i)
      · positivity
      · positivity
    simpa only [Real.norm_eq_abs] using
      mul_le_mul (pow_le_pow_left₀ (by positivity : 0 ≤ |u|) hu k) hb
        (by positivity) (by positivity)
  · have hz : iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u = 0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
        (f := mellinLogSchwartz W hW hpos hsm σ) n hn
      have hs' : u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))) :=
        tsupport_smul_subset_right (fun v : ℝ => Real.exp (-σ*v))
          (fun v : ℝ => W (Real.exp (-v))) hs
      have hb : |u| ≤ R₀ := by simpa only [Real.norm_eq_abs] using hR₀ u hs'
      exact hu (hb.trans (le_max_left _ _))
    rw [hz,norm_zero,mul_zero]
    positivity

theorem mellinVertical_family_bounded (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ) :
    Bornology.IsVonNBounded ℝ
      ((fun σ => mellinVerticalSchwartz W hW hpos hsm σ) '' {σ | |σ| ≤ M}) := by
  let f : ℝ → 𝓢(ℝ,ℂ) := fun σ => mellinLogSchwartz W hW hpos hsm σ
  have hb : Bornology.IsVonNBounded ℝ (f '' {σ | |σ| ≤ M}) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C,hC,h⟩ := mellinLogSchwartz_seminorm_uniform W hW hpos hsm M i.1 i.2
    exact ⟨C+1,by linarith,fun σ hσ => (h σ hσ).trans_lt (by linarith)⟩
  let L : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.compCLM ℝ (by
      simp only [div_eq_mul_inv]
      fun_prop : (fun t : ℝ => t/(2*Real.pi)).HasTemperateGrowth)
      mellin_frequency_growth).comp (SchwartzMap.fourierTransformCLM ℝ)
  convert hb.image L using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Set.image_comp]
  rfl

theorem smooth_mellin_strip_decay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, |σ| ≤ M → ∀ t : ℝ,
      (1+|t|)^A * ‖mellin W (σ + (t : ℂ)*Complex.I)‖ ≤ C := by
  have hb := mellinVertical_family_bounded W hW hpos hsm M
  obtain ⟨C,hC,h⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_finset_seminorm_bounded
      (fun σ => mellinVerticalSchwartz W hW hpos hsm σ) |>.mp hb (Finset.Iic (A,0))
  refine ⟨2^A*C,by positivity,?_⟩
  intro σ hσ t
  have hp := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (A,0)) (k := A) (n := 0) le_rfl le_rfl
      (mellinVerticalSchwartz W hW hpos hsm σ) t
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,mellinVerticalSchwartz_apply] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (h σ hσ).le (by positivity))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinHeckeContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contour step for the full smooth character sum. Polynomial
vertical growth is an analytic property of the L-function; the decay,
integrability and vanishing edges are derived for the actual weight. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma mellinEdgeMajorant_integrable (C : ℝ) : Integrable (mellinEdgeMajorant C) := by
  have hi : Integrable (fun t : ℝ => (1+‖t‖)^(-(2:ℝ))) :=
    integrable_one_add_norm (by norm_num)
  convert hi.const_mul C using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  rw [mellinEdgeMajorant, Real.rpow_neg (by positivity), Real.rpow_ofNat,
    Real.norm_eq_abs, div_eq_mul_inv]

lemma mellinEdgeMajorant_tendsto (C : ℝ) :
    Tendsto (mellinEdgeMajorant C) atTop (𝓝 0) ∧
      Tendsto (mellinEdgeMajorant C) atBot (𝓝 0) := by
  have h (l : Filter ℝ) (hl : Tendsto (fun t : ℝ => |t|) l atTop) :
      Tendsto (mellinEdgeMajorant C) l (𝓝 0) := by
    change Tendsto (fun t : ℝ => C/(1+|t|)^2) l (𝓝 0)
    have hp : Tendsto (fun t : ℝ => (1+|t|)⁻¹) l (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun t => by linarith) hl)
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0),
      mul_zero] using (hp.pow 2).const_mul C
  exact ⟨h atTop tendsto_abs_atTop_atTop,h atBot tendsto_abs_atBot_atTop⟩

lemma norm_mellinHecke_integrand_le (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {a b Z : ℝ} (hZ : 1 ≤ Z) (t : ℝ)
    (L : ℂ → ℂ) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hL : ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖L (σ + ((τ-t : ℝ) : ℂ)*Complex.I)‖ ≤ C*(1+|τ-t|)^N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖mellin W (σ+(τ:ℂ)*Complex.I) * (Z:ℂ)^(σ+(τ:ℂ)*Complex.I) *
          L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤ mellinEdgeMajorant K τ := by
  obtain ⟨Cw,hCw,hdecay⟩ := smooth_mellin_strip_decay W hW hpos hsm (|a|+|b|) (N+2)
  let B := Z^b*C*(1+|t|)^N
  have hB : 0 ≤ B := by positivity
  refine ⟨B*Cw,by positivity,?_⟩
  intro σ hσ τ
  have hσabs : |σ| ≤ |a|+|b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le a,abs_nonneg b,hσ.1]
    · linarith [le_abs_self b,abs_nonneg a,hσ.2]
  have hscale : ‖(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)‖ ≤ Z^b := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < Z)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    exact Real.rpow_le_rpow_of_exponent_le hZ hσ.2
  have hshift : (1+|τ-t|)^N ≤ (1+|t|)^N*(1+|τ|)^N := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hd := abs_sub_le τ 0 t
    simp only [sub_zero,zero_sub,abs_neg] at hd
    nlinarith [mul_nonneg (abs_nonneg τ) (abs_nonneg t)]
  have hL' : ‖L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤
      C*((1+|t|)^N*(1+|τ|)^N) :=
    (hL σ hσ τ).trans (mul_le_mul_of_nonneg_left hshift hC)
  unfold mellinEdgeMajorant
  apply (le_div_iff₀ (by positivity : 0 < (1+|τ|)^2)).mpr
  calc
    _ ≤ (‖mellin W (σ+(τ:ℂ)*Complex.I)‖ * Z^b *
        (C*((1+|t|)^N*(1+|τ|)^N)))*(1+|τ|)^2 := by
      rw [norm_mul,norm_mul]
      gcongr
    _ = B*((1+|τ|)^(N+2)*‖mellin W (σ+(τ:ℂ)*Complex.I)‖) := by
      rw [pow_add]
      dsimp [B]
      ring
    _ ≤ B*Cw := mul_le_mul_of_nonneg_left (hdecay σ hσabs τ) hB

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinDualTail
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual far-left dual-series tails. The integer-line Gamma estimate
and smooth Mellin decay provide the analytic bounds. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma shifted_power_le (N : ℕ) (τ t : ℝ) :
    (1+|τ-t|)^N ≤ (1+|t|)^N*(1+|τ|)^N := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hd := abs_sub_le τ 0 t
  simp only [sub_zero,zero_sub,abs_neg] at hd
  nlinarith [mul_nonneg (abs_nonneg τ) (abs_nonneg t)]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma normPolynomial_collected (s : Finset Eisenstein) (v : Eisenstein → ℂ)
    (Z : ℕ) (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z) (t : ℝ) :
    eisensteinNormPolynomial s v t = integerNormPolynomial Z (normCollectedCoeff s v) t := by
  unfold eisensteinNormPolynomial integerNormPolynomial normCollectedCoeff
  rw [← Finset.sum_fiberwise_of_maps_to hs]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  have he := (Finset.mem_filter.mp hb).2
  rw [← normNat_cast b, he]

lemma norm_sum_sq_le_card_mul (s : Finset Eisenstein) (v : Eisenstein → ℂ) :
    ‖∑ b ∈ s, v b‖ ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, ‖v b‖ ^ 2 := by
  have hnorm := norm_sum_le s v
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun b => ‖v b‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcauchy
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))).mpr
    hnorm |>.trans hcauchy

lemma normCollectedCoeff_energy (s : Finset Eisenstein) (v : Eisenstein → ℂ)
    (Z : ℕ) (M : ℝ) (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M) :
    (∑ n ∈ Finset.Icc 1 Z, ‖normCollectedCoeff s v n‖ ^ 2) ≤
      M * ∑ b ∈ s, ‖v b‖ ^ 2 := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 Z, M * ∑ b ∈ s with normNat b = n, ‖v b‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact (norm_sum_sq_le_card_mul _ v).trans
        (mul_le_mul_of_nonneg_right (hM n hn) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hs]

/-- The mean-square bound with the exact multiplicity loss from collecting
Eisenstein norms. -/
theorem eisensteinNormPolynomial_meanSquare {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (s : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ) (M : ℝ)
    (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖eisensteinNormPolynomial s v t‖ ^ 2) ≤
      C * (b - a + Z) * M * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  simp_rw [normPolynomial_collected s v Z hs]
  have h := hMV Z (normCollectedCoeff s v) a b hab
  have hfactor : 0 ≤ C * (b - a + Z) := mul_nonneg hC (by positivity)
  calc
    _ ≤ C * (b - a + Z) * (M * ∑ c ∈ s, ‖v c‖ ^ 2) :=
      h.trans (mul_le_mul_of_nonneg_left (normCollectedCoeff_energy s v Z M hs hM) hfactor)
    _ = _ := by ring

/-- A fixed angular character and translated height are coefficient phases;
they do not change the original coefficient energy. -/
theorem fixedAngular_translated_meanSquare {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (s : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ) (M : ℝ)
    (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hzero : ∀ b ∈ s, b ≠ 0)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M)
    (ℓ : ℤ) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)‖ ^ 2) ≤
      C * (b - a + Z) * M * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  let w := fun c => v c * theta ℓ c * mellinPhase u (norm c)
  have heq : ∀ t, (∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)) =
      eisensteinNormPolynomial s w t := by
    intro t
    unfold eisensteinNormPolynomial
    apply Finset.sum_congr rfl
    intro c hc
    rw [mellinPhase_add]
    dsimp [w]
    ring
  simp_rw [heq]
  have henergy : (∑ c ∈ s, ‖w c‖ ^ 2) = ∑ c ∈ s, ‖v c‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [w, norm_mul, norm_theta (hzero c hc), mellinPhase_norm, mul_one]
  simpa only [henergy] using eisensteinNormPolynomial_meanSquare hMV hC s w Z M hs hM hab

private lemma continuous_angularNormPolynomial (s : Finset Eisenstein)
    (v : Eisenstein → ℂ) (ℓ : ℤ) (u : ℝ) :
    Continuous (fun t : ℝ => ∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)) := by
  apply continuous_finsetSum
  intro c hc
  apply continuous_const.mul
  unfold mellinPhase
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp
      ((continuous_id.add continuous_const).mul continuous_const)).mul continuous_const)

private lemma interval_integral_sq_le (f : ℝ → ℝ) (hf : Continuous f)
    {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 := by
  let L := b - a
  let I := ∫ t in a..b, f t
  have hL : 0 < L := sub_pos.mpr hab
  have hfint : IntervalIntegrable f volume a b := hf.intervalIntegrable a b
  have hsqint : IntervalIntegrable (fun t => (f t) ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable a b
  have hlinint := (hfint.const_mul (2 * L * I))
  have hvar : (∫ t in a..b, (L * f t - I) ^ 2) =
      L ^ 2 * (∫ t in a..b, (f t) ^ 2) - L * I ^ 2 := by
    calc
      _ = ∫ t in a..b, (L ^ 2 * (f t) ^ 2 - (2 * L * I) * f t) + I ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = L ^ 2 * (∫ t in a..b, (f t) ^ 2) - (2 * L * I) * I + L * I ^ 2 := by
        rw [intervalIntegral.integral_add ((hsqint.const_mul _).sub hlinint)
          intervalIntegrable_const, intervalIntegral.integral_sub (hsqint.const_mul _) hlinint,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        rfl
      _ = _ := by ring
  have hnonneg : 0 ≤ L ^ 2 * (∫ t in a..b, (f t) ^ 2) - L * I ^ 2 := by
    rw [← hvar]
    exact intervalIntegral.integral_nonneg_of_forall hab.le (fun t => sq_nonneg _)
  change I ^ 2 ≤ L * (∫ t in a..b, (f t) ^ 2)
  nlinarith

/-- Mean absolute size on a height interval, derived from the mean square.
This form retains the exact coefficient energy instead of hiding it in a
big-O constant. -/
theorem fixedAngular_translated_meanAbsolute_sq {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (s : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ) (M : ℝ)
    (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hzero : ∀ b ∈ s, b ≠ 0)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M)
    (ℓ : ℤ) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    ((∫ t in T..2 * T, ‖∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)‖) / T) ^ 2 ≤
      C * (1 + (Z : ℝ) / T) * M * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  have hcont := (continuous_angularNormPolynomial s v ℓ u).norm
  have hcs := interval_integral_sq_le _ hcont (a := T) (b := 2 * T) (by linarith)
  have hms := fixedAngular_translated_meanSquare hMV hC s v Z M hs hzero hM ℓ u
    (a := T) (b := 2 * T) (by linarith)
  have h := hcs.trans (mul_le_mul_of_nonneg_left hms (by linarith))
  have hdiv := div_le_div_of_nonneg_right h (sq_nonneg T)
  rw [div_pow]
  refine hdiv.trans (le_of_eq ?_)
  field_simp
  ring

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

lemma UniformLogWeights.vertical_seminorms {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i σ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n
        (mellinVerticalSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ) ≤ C := by
  obtain ⟨C,hC,hb⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded
      (fun p : ι × ℝ => mellinVerticalSchwartz (W p.1) (h.compact p.1)
        (h.positive p.1) (h.smooth p.1) p.2) |>.mp (h.vertical_bounded M) (k,n)
  exact ⟨C,hC,fun i σ hσ => (hb (i,σ) hσ).le⟩

lemma UniformLogWeights.mellin_norm_moment {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (M : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i σ, |σ| ≤ M →
      (∫ t : ℝ, |t|^k*‖mellin (W i) ((σ:ℂ)+(t:ℂ)*Complex.I)‖) ≤ C := by
  let n : ℕ := (volume : Measure ℝ).integrablePower
  obtain ⟨C₀,hC₀,h₀⟩ := h.vertical_seminorms M 0 0
  obtain ⟨C₁,hC₁,h₁⟩ := h.vertical_seminorms M (k+n) 0
  let A : ℝ := 2^n*(∫ t : ℝ, (1+‖t‖)^(-(n:ℝ)))
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg (by norm_num) _)
    (integral_nonneg (fun _ => Real.rpow_nonneg (by positivity) _))
  refine ⟨A*(C₀+C₁),mul_nonneg hA (by positivity),?_⟩
  intro i σ hσ
  let F := mellinVerticalSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) σ
  have hb := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume F k 0
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hb
  change (∫ t : ℝ, |t|^k*‖F t‖) ≤ A*
    (SchwartzMap.seminorm ℝ 0 0 F+SchwartzMap.seminorm ℝ (k+n) 0 F) at hb
  calc
    _ = ∫ t : ℝ, |t|^k*‖F t‖ := by
      congr 1
      ext t
      rw [mellinVerticalSchwartz_apply]
    _ ≤ A*(SchwartzMap.seminorm ℝ 0 0 F+SchwartzMap.seminorm ℝ (k+n) 0 F) := hb
    _ ≤ A*(C₀+C₁) := mul_le_mul_of_nonneg_left
      (add_le_add (h₀ i σ hσ) (h₁ i σ hσ)) hA

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryNormMultiplicity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational norm fibers of arbitrary primary elements. An element of norm
`n` divides the rational integer `n` in the Eisenstein ring. Thus the proved
ideal divisor bound supplies the small multiplicity loss required by the
ordinary Montgomery--Vaughan input, without any prime-factor restriction. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_dvd_of_normNat_eq {b : Eisenstein} {n : ℕ} (hn : normNat b = n) :
    b ∣ (n : Eisenstein) := by
  rw [←hn,normNat_cast_eq_mul_conjugate]
  exact dvd_mul_right _ _

private lemma norm_natCast_eisenstein (n : ℕ) : norm (n : Eisenstein) = (n:ℝ)^2 := by
  change Complex.normSq (n:ℂ) = _
  simpa only [Complex.ofReal_natCast,pow_two] using Complex.normSq_ofReal (n:ℝ)

/-- Uniform small-power bound for positive rational norm fibers. -/
theorem primary_norm_fiber_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset Eisenstein),
      (∀ b ∈ T, primary b) → ∀ n : ℕ, 0 < n →
      ((T.filter (fun b => normNat b = n)).card:ℝ) ≤ C*(n:ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := primary_divisor_card_small_power (half_pos hε)
  refine ⟨C,hC,?_⟩
  intro T hT n hn
  have hn0 : (n:Eisenstein) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsub : T.filter (fun b => normNat b = n) ⊆ T.filter (fun b => b ∣ (n:Eisenstein)) := by
    intro b hb
    obtain ⟨hbT,hbn⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨hbT,primary_dvd_of_normNat_eq hbn⟩
  have hpower : norm (n:Eisenstein)^(ε/2) = (n:ℝ)^ε := by
    rw [norm_natCast_eisenstein,←Real.rpow_natCast_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    ((hdiv T hT (n:Eisenstein) hn0).trans_eq (by rw [hpower]))

lemma primary_norm_fiber_length_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset Eisenstein),
      (∀ b ∈ T, primary b) → ∀ Z n : ℕ, n ∈ Finset.Icc 1 Z →
      ((T.filter (fun b => normNat b = n)).card:ℝ) ≤ C*(Z:ℝ)^ε := by
  obtain ⟨C,hC,hfiber⟩ := primary_norm_fiber_small_power hε
  refine ⟨C,hC,?_⟩
  intro T hT Z n hn
  obtain ⟨hn1,hnZ⟩ := Finset.mem_Icc.mp hn
  exact (hfiber T hT n (by omega)).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnZ) hε.le) hC.le)

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

lemma idealExponent_exponent_bound {ν : EisensteinIdealExponent} {J : ℝ}
    (hν : idealExponentNorm ν ≤ J) (p : EisensteinIdealPrime) :
    ν p ≤ Nat.log 2 ⌊J⌋₊ := by
  have hsingle : Finsupp.single p (ν p) ≤ ν := Finsupp.single_le_iff.mpr le_rfl
  have hN := norm_le_of_dvd (idealExponentGenerator_ne_zero ν)
    (idealExponentGenerator_dvd_of_le hsingle)
  have hpow : (2:ℝ)^(ν p) ≤ idealExponentNorm ν := by
    calc
      _ ≤ (normNat (idealPrimeRepresentative p):ℝ)^(ν p) :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast idealPrimeRepresentative_normNat_ge_two p) _
      _ = idealExponentNorm (Finsupp.single p (ν p)) := (idealExponentNorm_single _ _).symm
      _ ≤ idealExponentNorm ν := by simpa only [idealExponentNorm,normNat_cast] using hN
  apply Nat.le_log_of_pow_le (by norm_num)
  apply Nat.le_floor
  exact_mod_cast hpow.trans hν

lemma mellinPhase_mul_pos (u : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    mellinPhase u (x*y) = mellinPhase u x*mellinPhase u y := by
  unfold mellinPhase
  rw [Real.log_mul hx.ne' hy.ne',mul_add,Complex.ofReal_add,add_mul,Complex.exp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveDualConjugation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugation preserves the normalized dual moment and reverses the
Mellin height. Thus the cubic sieve controls the actual dual coefficients. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma star_mellinPhase (u x : ℝ) : star (mellinPhase u x) = mellinPhase (-u) x := by
  change (starRingEnd ℂ) (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,neg_mul,Complex.ofReal_neg]
  ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SupportedIdealCount
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Rankin bound for ideals supported on a varying small modulus. The
finite Euler product is controlled by an arbitrarily small modulus power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealExponentNorm_prod_of_support_subset (ν : EisensteinIdealExponent)
    (S : Finset EisensteinIdealPrime) (hS : ν.support ⊆ S) :
    idealExponentNorm ν = ∏ p ∈ S, (normNat (idealPrimeRepresentative p):ℝ)^ν p := by
  rw [idealExponentNorm_eq_prod]
  apply Finset.prod_subset hS
  intro p hp hpn
  rw [Finsupp.notMem_support_iff.mp hpn,pow_zero]

lemma supported_norm_rpow (ν : EisensteinIdealExponent)
    (S : Finset EisensteinIdealPrime) (hS : ν.support ⊆ S) (ε : ℝ) :
    idealExponentNorm ν^(-ε) =
      ∏ p : S, ((normNat (idealPrimeRepresentative p):ℝ)^(-ε))^(ν p) := by
  rw [idealExponentNorm_prod_of_support_subset ν S hS,
    ← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity),
    ← Real.rpow_mul_natCast (by positivity)]
  congr 1
  ring

lemma finite_geometric_code_sum {α β : Type*} [Fintype α] [Fintype β]
    (M : ℕ) (f : α → β → Fin M) (hf : Function.Injective f)
    (w : β → ℝ) (hw : ∀ p, 0 ≤ w p ∧ w p < 1) :
    (∑ a : α, ∏ p : β, w p^(f a p).val) ≤ ∏ p : β, (1-w p)⁻¹ := by
  classical
  calc
    _ ≤ ∑ g : β → Fin M, ∏ p : β, w p^(g p).val := by
      apply OAI.sum_le_sum_of_injOn f (fun _ _ _ _ h => hf h)
        (Finset.subset_univ _)
      · intro a ha
        exact le_rfl
      · intro g hg hgn
        exact Finset.prod_nonneg (fun p _ => pow_nonneg (hw p).1 _)
    _ = ∏ p : β, ∑ n : Fin M, w p^n.val := (Fintype.prod_sum (fun (p : β) (n : Fin M) => w p^n.val)).symm
    _ ≤ ∏ p : β, (1-w p)⁻¹ := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Finset.sum_nonneg (fun n _ => pow_nonneg (hw p).1 _)
      · intro p hp
        rw [Fin.sum_univ_eq_sum_range]
        exact sum_le_hasSum (Finset.range M) (fun n _ => pow_nonneg (hw p).1 n)
          (hasSum_geometric_of_lt_one (hw p).1 (hw p).2)

lemma ideal_supported_rankin_sum {ε J : ℝ} (hε : 0 < ε)
    (S : Finset EisensteinIdealPrime) (T : Finset EisensteinIdealExponent)
    (hT : ∀ ν ∈ T, ν.support ⊆ S ∧ idealExponentNorm ν ≤ J) :
    (∑ ν ∈ T, idealExponentNorm ν^(-ε)) ≤
      ∏ p ∈ S, (1-(normNat (idealPrimeRepresentative p):ℝ)^(-ε))⁻¹ := by
  let M := Nat.log 2 ⌊J⌋₊+1
  let f : T → (S → Fin M) := fun ν p =>
    ⟨ν.val p, Nat.lt_succ_of_le (idealExponent_exponent_bound (hT ν ν.property).2 p)⟩
  have hf : Function.Injective f := by
    intro ν κ he
    apply Subtype.ext
    apply Finsupp.ext
    intro p
    by_cases hp : p ∈ S
    · exact congrArg Fin.val (congrFun he ⟨p,hp⟩)
    · rw [Finsupp.notMem_support_iff.mp (fun h => hp ((hT ν ν.property).1 h)),
        Finsupp.notMem_support_iff.mp (fun h => hp ((hT κ κ.property).1 h))]
  let w : S → ℝ := fun p => (normNat (idealPrimeRepresentative p):ℝ)^(-ε)
  have hw (p : S) : 0 ≤ w p ∧ w p < 1 := by
    have hp : (1:ℝ) < normNat (idealPrimeRepresentative p) := by
      have := idealPrimeRepresentative_normNat_ge_two p
      exact_mod_cast (by omega : 1 < normNat (idealPrimeRepresentative p))
    exact ⟨Real.rpow_nonneg (by positivity) _,Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hε)⟩
  have hnorm (ν : T) : idealExponentNorm ν^(-ε) = ∏ p : S, w p^(f ν p).val :=
    supported_norm_rpow ν S (hT ν ν.property).1 ε
  calc
    _ = ∑ ν : T, ∏ p : S, w p^(f ν p).val := by
      rw [← Finset.sum_coe_sort T]
      exact Finset.sum_congr rfl (fun ν _ => hnorm ν)
    _ ≤ ∏ p : S, (1-w p)⁻¹ := finite_geometric_code_sum M f hf w hw
    _ = _ := Finset.prod_coe_sort S
      (fun p => (1-(normNat (idealPrimeRepresentative p):ℝ)^(-ε))⁻¹)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallEulerProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Euler factor for a varying small modulus costs only an
arbitrary positive power of its norm. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

 theorem supported_euler_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : EisensteinIdealExponent,
      (∏ p ∈ ν.support, (1-(normNat (idealPrimeRepresentative p):ℝ)^(-ε))⁻¹) ≤
        C*idealExponentNorm ν^ε := by
  let R : ℝ := (2:ℝ)^(1/ε)
  let T : Finset EisensteinIdealPrime :=
    (fullIdealBall R).biUnion (fun ν => ν.support)
  let A : ℝ := (1-(2:ℝ)^(-ε))⁻¹
  have ht : (2:ℝ)^(-ε) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hA : 1 ≤ A := by
    dsimp [A]
    rw [← one_div]
    apply (le_div_iff₀ (by linarith : 0 < 1-(2:ℝ)^(-ε))).mpr
    rw [one_mul]
    linarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-ε)]
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
  have hpoint : ∀ p ∈ ν.support,
      (1-(normNat (idealPrimeRepresentative p):ℝ)^(-ε))⁻¹ ≤
        (if p ∈ T then A else 1)*(normNat (idealPrimeRepresentative p):ℝ)^(ε*ν p) := by
    intro p hp
    let q : ℝ := normNat (idealPrimeRepresentative p)
    have hq : (2:ℝ) ≤ q := by
      dsimp [q]
      exact_mod_cast idealPrimeRepresentative_normNat_ge_two p
    have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
    have hqt : q^(-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
    have hexp : ε ≤ ε*ν p := by
      have hn : (1:ℝ) ≤ ν p := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp))
      nlinarith
    have hpow : 1 ≤ q^(ε*ν p) := Real.one_le_rpow (by linarith) (by positivity)
    by_cases hpT : p ∈ T
    · simp only [ite_eq_left hpT]
      have hlocal : (1-q^(-ε))⁻¹ ≤ A := by
        apply (inv_le_inv₀ (by linarith) (by linarith)).mpr
        have hmono := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<2) hq (by linarith : -ε ≤ 0)
        linarith
      exact hlocal.trans (le_mul_of_one_le_right (zero_le_one.trans hA) hpow)
    · simp only [ite_eq_right hpT,one_mul]
      have hRp : R ≤ q := le_of_lt (lt_of_not_ge (fun h => hpT (hT p h)))
      have htwo : (2:ℝ) ≤ q^ε := by
        rw [← hRe]
        exact Real.rpow_le_rpow hR.le hRp hε.le
      have hhalf : q^(-ε) ≤ 1/2 := by
        rw [Real.rpow_neg hqp.le]
        simpa only [one_div] using
          (inv_le_inv₀ (Real.rpow_pos_of_pos hqp ε) (by norm_num : (0:ℝ) < 2)).mpr htwo
      have hlocal : (1-q^(-ε))⁻¹ ≤ 2 := by
        rw [← one_div]
        apply (div_le_iff₀ (by linarith : 0 < 1-q^(-ε))).mpr
        linarith
      exact hlocal.trans (htwo.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp))
  have hprod := Finset.prod_le_prod (s := ν.support)
    (fun p _ => inv_nonneg.mpr (by
      have hp : (1:ℝ) < normNat (idealPrimeRepresentative p) := by
        have := idealPrimeRepresentative_normNat_ge_two p
        exact_mod_cast (by omega : 1 < normNat (idealPrimeRepresentative p))
      exact sub_nonneg.mpr (le_of_lt (Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith))))) hpoint
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
      _ = (∏ p ∈ ν.support, ((normNat (idealPrimeRepresentative p):ℝ)^ν p))^ε :=
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity) ε
      _ = _ := by rw [idealExponentNorm_eq_prod]
  rw [hnorm] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (idealExponentNorm_pos ν).le _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed angular multipliers are precisely powers of the actual
complex Fourier frequency and its conjugate. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_div_nine (n : Eisenstein) :
    cubicThetaFrequency n=(n:ℂ)/9 := by
  have hs : traceLambda^2=(-3:ℂ) := by
    have he := congrArg (fun n : Eisenstein => (n:ℂ)) lambdaE_sq
    push_cast at he
    rw [lambdaE_coe] at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
  have h4 : traceLambda^4=(9:ℂ) := by
    calc
      _ = (traceLambda^2)^2 := by ring
      _ = _ := by rw [hs]; norm_num
  simp only [cubicThetaFrequency,h4]

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

lemma primary_norm_rpow_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun u : PrimaryArgument => norm u^(-s)) :=
  (summable_eisenstein_norm_rpow hs).subtype _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal level/angular Voronoi input of Dunn--Radziwill,
arXiv:2109.07463v3, Proposition 5.3, equations (5.79)--(5.82), pp.33--34.
The raw formula is kept separate from its proved Gauss/phase normalization.
The index `n` below denotes the actual frequency `n / lambda`; zero is excluded.
No estimate for a completed sum is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticFrequency_ne_zero (n : MetaplecticDualArgument) :
    metaplecticFrequency n ≠ 0 :=
  div_ne_zero (fun h => n.property (Subtype.ext h)) traceLambda_ne_zero

lemma norm_metaplecticLocalCoefficient_le {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) :
    ‖metaplecticLocalCoefficient r n‖ ≤ metaplecticCommonNorm r n := by
  rw [metaplecticLocalCoefficient,norm_prod]
  have hp (p : Eisenstein) (hp : p ∈ primaryPrimeFactors r) : 1 ≤ norm p :=
    one_le_norm (primaryPrimeFactor_spec hr hp).1.2.ne_zero
  calc
    _ ≤ ∏ p ∈ primaryPrimeFactors r, if p ∣ n.val then norm p else 1 := by
      apply Finset.prod_le_prod (fun _ _ => _root_.norm_nonneg _)
      intro p hpm
      split_ifs with h
      · simp only [Complex.norm_real,Real.norm_eq_abs]
        rw [abs_of_nonneg (by linarith [hp p hpm])]
        linarith
      · norm_num
    _ = metaplecticCommonNorm r n := by
      simp only [metaplecticCommonNorm,Finset.prod_ite,Finset.prod_const_one,mul_one]

lemma norm_metaplecticPrefactor {r : Eisenstein} (hr : r ≠ 0) (ℓ : ℤ) :
    ‖metaplecticPrefactor r ℓ‖ =
      Real.sqrt (norm r)/(3^(7/2:ℝ)*(2*Real.pi)^2) := by
  rw [metaplecticPrefactor,norm_mul,norm_theta hr,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg]
  positivity

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
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticGammaRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact far-left metaplectic Gamma growth from the finite recurrence.
Choosing Re s = 1/2-m gives the sharp height exponent 4m = 2+4A,
A=m-1/2. No additional Stirling or completed-height input is needed. -/
noncomputable section
namespace CubicFirstMoment

private lemma metaplectic_ascPochhammer_norm (n : ℕ) (z : ℂ) :
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

/-- A symmetric Gamma ratio for any fixed real shift, retaining the
zero values at the totalized Gamma poles. -/
lemma metaplectic_symmetric_gamma_ratio (k : ℝ) (m : ℕ) (t : ℝ) :
    ‖Complex.Gamma ((1/2:ℂ)+(m:ℂ)+(k:ℂ)-(t:ℂ)*Complex.I) /
      Complex.Gamma ((1/2:ℂ)-(m:ℂ)+(k:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (|k|+3*(m:ℝ)+1)^(2*m)*(1+|t|)^(2*m) := by
  let z : ℂ := (1/2:ℂ)-(m:ℂ)+(k:ℂ)+(t:ℂ)*Complex.I
  by_cases hG : Complex.Gamma z = 0
  · change ‖_ / Complex.Gamma z‖ ≤ _
    rw [hG,div_zero,norm_zero]
    positivity
  have hreg : ∀ n : ℕ, z ≠ -(n:ℂ) := by
    intro n hn
    apply hG
    rw [hn,Complex.Gamma_neg_nat_eq_zero]
  have he : ((1/2:ℂ)+(m:ℂ)+(k:ℂ)-(t:ℂ)*Complex.I) =
      starRingEnd ℂ (z+(2*m:ℕ)) := by
    dsimp [z]
    simp only [map_add,map_sub,map_mul,Complex.conj_ofReal,Complex.conj_I,
      map_natCast,map_div₀,map_one,map_ofNat]
    push_cast
    ring
  have hq := Complex.Gamma_add_nat_div_Gamma_eq (n := 2*m) z hreg
  have hn : ‖z‖ ≤ |k|+(m:ℝ)+1+|t| := by
    calc
      _ ≤ ‖(1/2:ℂ)-(m:ℂ)+(k:ℂ)‖+‖(t:ℂ)*Complex.I‖ := norm_add_le _ _
      _ ≤ ‖(1/2:ℂ)-(m:ℂ)‖+‖(k:ℂ)‖+‖(t:ℂ)*Complex.I‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖(1/2:ℂ)‖+‖(m:ℂ)‖+‖(k:ℂ)‖+‖(t:ℂ)*Complex.I‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ _ := by simp; linarith
  calc
    _ = ‖Complex.Gamma (z+(2*m:ℕ))/Complex.Gamma z‖ := by
      rw [he,Complex.Gamma_conj,norm_div,norm_div,Complex.norm_conj]
    _ = ‖(ascPochhammer ℂ (2*m)).eval z‖ := congrArg (fun w : ℂ => ‖w‖) hq
    _ ≤ (‖z‖+((2*m:ℕ):ℝ))^(2*m) := metaplectic_ascPochhammer_norm _ _
    _ ≤ ((|k|+3*(m:ℝ)+1)*(1+|t|))^(2*m) := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast
      nlinarith [abs_nonneg k,abs_nonneg t,show (0:ℝ) ≤ m by positivity]
    _ = _ := mul_pow _ _ _

lemma metaplecticGamma_symmetric_factor (ℓ : ℤ) (m : ℕ) (t : ℝ) :
    metaplecticGammaQuotient ℓ ((1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I) =
      (Complex.Gamma ((1/2:ℂ)+(m:ℂ)+((metaplecticAngularShift ℓ-1/6:ℝ):ℂ)-(t:ℂ)*Complex.I) /
       Complex.Gamma ((1/2:ℂ)-(m:ℂ)+((metaplecticAngularShift ℓ-1/6:ℝ):ℂ)+(t:ℂ)*Complex.I)) *
      (Complex.Gamma ((1/2:ℂ)+(m:ℂ)+((metaplecticAngularShift ℓ+1/6:ℝ):ℂ)-(t:ℂ)*Complex.I) /
       Complex.Gamma ((1/2:ℂ)-(m:ℂ)+((metaplecticAngularShift ℓ+1/6:ℝ):ℂ)+(t:ℂ)*Complex.I)) := by
  have hk : (metaplecticAngularShift ℓ:ℂ) = (|ℓ|:ℤ)/2 := by
    simp only [metaplecticAngularShift,Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_ofNat]
  unfold metaplecticGammaQuotient
  have h1 : 5/6+(|ℓ|:ℤ)/2-((1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I) =
      (1/2:ℂ)+(m:ℂ)+((metaplecticAngularShift ℓ-1/6:ℝ):ℂ)-(t:ℂ)*Complex.I := by
    push_cast
    rw [hk]
    ring
  have h2 : 7/6+(|ℓ|:ℤ)/2-((1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I) =
      (1/2:ℂ)+(m:ℂ)+((metaplecticAngularShift ℓ+1/6:ℝ):ℂ)-(t:ℂ)*Complex.I := by
    push_cast
    rw [hk]
    ring
  have h3 : (1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I+(|ℓ|:ℤ)/2-1/6 =
      (1/2:ℂ)-(m:ℂ)+((metaplecticAngularShift ℓ-1/6:ℝ):ℂ)+(t:ℂ)*Complex.I := by
    push_cast
    rw [hk]
    ring
  have h4 : (1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I+(|ℓ|:ℤ)/2+1/6 =
      (1/2:ℂ)-(m:ℂ)+((metaplecticAngularShift ℓ+1/6:ℝ):ℂ)+(t:ℂ)*Complex.I := by
    push_cast
    rw [hk]
    ring
  rw [h1,h2,h3,h4]
  ring

/-- Sharp exponent on the far-left half-integral lines, sufficient for
arbitrary-power angular dual truncation. Constants depend only on ℓ,m. -/
theorem metaplecticGamma_half_integer_bound (ℓ : ℤ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖metaplecticGammaQuotient ℓ ((1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        C*(1+|t|)^(4*m) := by
  let k := metaplecticAngularShift ℓ
  let A := (|k-1/6|+3*(m:ℝ)+1)^(2*m)
  let B := (|k+1/6|+3*(m:ℝ)+1)^(2*m)
  have hA : 0 < A := pow_pos (by positivity) _
  have hB : 0 < B := pow_pos (by positivity) _
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro t
  rw [metaplecticGamma_symmetric_factor,norm_mul]
  have hminus := metaplectic_symmetric_gamma_ratio (k-1/6) m t
  have hplus := metaplectic_symmetric_gamma_ratio (k+1/6) m t
  calc
    _ ≤ (A*(1+|t|)^(2*m))*(B*(1+|t|)^(2*m)) :=
      mul_le_mul hminus hplus (_root_.norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show 4*m = 2*m+2*m by omega,pow_add]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTransformContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour motion for the actual angular metaplectic transform. The two
fixed shifted Hecke Gamma strip estimates are the same published Stirling
input already used for the individual Hecke transforms. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplecticGamma_shift_factor (ℓ : ℤ) (s : ℂ) :
    metaplecticGammaQuotient ℓ s =
      angularGammaFEQuotient (metaplecticAngularShift ℓ-1/6) s *
      angularGammaFEQuotient (metaplecticAngularShift ℓ+1/6) s := by
  have hk : (metaplecticAngularShift ℓ:ℂ) = (|ℓ|:ℤ)/2 := by
    simp only [metaplecticAngularShift,Complex.ofReal_div,Complex.ofReal_intCast,
      Complex.ofReal_ofNat]
  unfold metaplecticGammaQuotient angularGammaFEQuotient
  push_cast
  rw [hk]
  have h1 : 1-s+((|ℓ|:ℤ)/2-1/6) = 5/6+(|ℓ|:ℤ)/2-s := by ring
  have h2 : 1-s+((|ℓ|:ℤ)/2+1/6) = 7/6+(|ℓ|:ℤ)/2-s := by ring
  have h3 : s+((|ℓ|:ℤ)/2-1/6) = s+(|ℓ|:ℤ)/2-1/6 := by ring
  have h4 : s+((|ℓ|:ℤ)/2+1/6) = s+(|ℓ|:ℤ)/2+1/6 := by ring
  rw [h1,h2,h3,h4]
  ring

lemma metaplecticGamma_strip_bound (ℓ : ℤ) (a : ℝ)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) a)
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ ∈ Icc a (1/2:ℝ), ∀ t : ℝ,
      ‖metaplecticGammaQuotient ℓ (σ+(t:ℂ)*Complex.I)‖ ≤ C*(1+|t|)^N := by
  obtain ⟨Cm,Nm,hCm,hgm⟩ := hm
  obtain ⟨Cp,Np,hCp,hgp⟩ := hp
  refine ⟨Cm*Cp,Nm+Np,mul_nonneg hCm hCp,?_⟩
  intro σ hσ t
  rw [metaplecticGamma_shift_factor,norm_mul]
  calc
    _ ≤ (Cm*(1+|t|)^Nm)*(Cp*(1+|t|)^Np) :=
      mul_le_mul (hgm σ hσ t) (hgp σ hσ t) (_root_.norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

lemma differentiableOn_metaplecticGammaQuotient (ℓ : ℤ) :
    DifferentiableOn ℂ (metaplecticGammaQuotient ℓ) {s : ℂ | s.re < 5/6} := by
  intro s hs
  have hk : 0 ≤ ((|ℓ|:ℤ):ℝ)/2 := by positivity
  have hreg (c : ℝ) (hc : 5/6 ≤ c) :
      ∀ n : ℕ, (c:ℂ)+(|ℓ|:ℤ)/2-s ≠ -(n:ℂ) := by
    intro n hn
    have he := congrArg Complex.re hn
    simp only [Complex.sub_re,Complex.add_re,Complex.div_ofNat_re,Complex.ofReal_re,
      Complex.intCast_re,Complex.neg_re,Complex.natCast_re] at he
    change s.re < 5/6 at hs
    have hn0 : (0:ℝ) ≤ n := by positivity
    linarith
  have h1 := (Complex.differentiableAt_Gamma ((5/6:ℂ)+(|ℓ|:ℤ)/2-s)
    (by simpa using hreg (5/6) le_rfl)).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => (5/6:ℂ)+(|ℓ|:ℤ)/2-z) s by fun_prop)
  have h2 := (Complex.differentiableAt_Gamma ((7/6:ℂ)+(|ℓ|:ℤ)/2-s)
    (by simpa using hreg (7/6) (by norm_num))).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => (7/6:ℂ)+(|ℓ|:ℤ)/2-z) s by fun_prop)
  have h3 := (Complex.differentiable_one_div_Gamma (s+(|ℓ|:ℤ)/2-1/6)).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => z+(|ℓ|:ℤ)/2-1/6) s by fun_prop)
  have h4 := (Complex.differentiable_one_div_Gamma (s+(|ℓ|:ℤ)/2+1/6)).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => z+(|ℓ|:ℤ)/2+1/6) s by fun_prop)
  convert ((h1.mul h2).mul (h3.mul h4)).differentiableWithinAt using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  dsimp [metaplecticGammaQuotient]
  ring

lemma norm_angularGammaFEQuotient_half {k : ℝ} (hk : -1/2 < k) (t : ℝ) :
    ‖angularGammaFEQuotient k ((1/2:ℂ)+(t:ℂ)*Complex.I)‖ = 1 := by
  let z : ℂ := (1/2:ℂ)+(t:ℂ)*Complex.I+(k:ℂ)
  have hz : 0 < z.re := by dsimp [z]; simp; linarith
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have he : 1-((1/2:ℂ)+(t:ℂ)*Complex.I)+(k:ℂ) = starRingEnd ℂ z := by
    dsimp [z]
    simp only [map_add,map_mul,map_div₀,map_one,map_ofNat,
      Complex.conj_ofReal,Complex.conj_I]
    ring
  unfold angularGammaFEQuotient
  rw [he,Complex.Gamma_conj,norm_div,Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr hG)

lemma norm_metaplecticGamma_half (ℓ : ℤ) (t : ℝ) :
    ‖metaplecticGammaQuotient ℓ ((1/2:ℂ)+(t:ℂ)*Complex.I)‖ = 1 := by
  rw [metaplecticGamma_shift_factor,norm_mul,
    norm_angularGammaFEQuotient_half (by linarith [metaplecticAngularShift_nonneg ℓ]),
    norm_angularGammaFEQuotient_half (by linarith [metaplecticAngularShift_nonneg ℓ]),one_mul]

private lemma metaplectic_scale_strip {a b v : ℝ} (hv : 0 < v)
    {σ : ℝ} (hσ : σ ∈ Icc a b) :
    v^σ ≤ max (v^a) (v^b) := by
  by_cases h : 1 ≤ v
  · exact (Real.rpow_le_rpow_of_exponent_le h hσ.2).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge hv (le_of_not_ge h) hσ.1).trans (le_max_left _ _)

/-- Exact vertical contour move for the transform integrand. The scale
may lie on either side of one. -/
theorem metaplectic_transform_contour (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {a b v : ℝ} (hab : a ≤ b) (hb : b ≤ 1/2)
    (hv : 0 < v)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) a)
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) a) :
    (∫ t : ℝ, (v:ℂ)^((a:ℂ)+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((a:ℂ)+(t:ℂ)*Complex.I)*
      mellin W ((a:ℂ)+(t:ℂ)*Complex.I)) =
    ∫ t : ℝ, (v:ℂ)^((b:ℂ)+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((b:ℂ)+(t:ℂ)*Complex.I)*
      mellin W ((b:ℂ)+(t:ℂ)*Complex.I) := by
  obtain ⟨C,N,hC,hQ⟩ := metaplecticGamma_strip_bound ℓ a hm hp
  let L : ℂ → ℂ := fun s => (v:ℂ)^s*metaplecticGammaQuotient ℓ s
  let D : ℝ := max (v^a) (v^b)*C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hg (σ : ℝ) (hσ : σ ∈ Icc a b) (t : ℝ) :
      ‖L (σ+((t-0:ℝ):ℂ)*Complex.I)‖ ≤ D*(1+|t-0|)^N := by
    simp only [sub_zero]
    dsimp [L]
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    calc
      _ ≤ max (v^a) (v^b)*(C*(1+|t|)^N) :=
        mul_le_mul (metaplectic_scale_strip hv hσ) (hQ σ ⟨hσ.1,hσ.2.trans hb⟩ t)
          (_root_.norm_nonneg _) (by positivity)
      _ = _ := by dsimp [D]; ring
  have : NeZero (v:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hv.ne'⟩
  have hd : DifferentiableOn ℂ L (closedVerticalStrip a b) := by
    apply (differentiable_const_cpow_of_neZero _).differentiableOn.mul
    exact (differentiableOn_metaplecticGammaQuotient ℓ).mono (by
      intro s hs
      exact lt_of_le_of_lt (hs.2.trans hb) (by norm_num))
  let f : ℂ → ℂ := fun s => mellin W s*L s
  have hf : DifferentiableOn ℂ f (closedVerticalStrip a b) :=
    (smooth_mellin_entire W hW hpos hsm.continuous).differentiableOn.mul hd
  obtain ⟨K,_hK,hbound⟩ := norm_mellinHecke_integrand_le W hW hpos hsm
    (Z := 1) (by norm_num) 0 L hD N hg
  have hmajor (σ : ℝ) (hσ : σ ∈ Icc a b) (t : ℝ) :
      ‖f (σ+(t:ℂ)*Complex.I)‖ ≤ mellinEdgeMajorant K t := by
    simpa only [f,sub_zero,Complex.ofReal_one,Complex.one_cpow,mul_one] using hbound σ hσ t
  have hs := mellin_contour_shift_of_majorant hab f hf (mellinEdgeMajorant K)
    (mellinEdgeMajorant_integrable K) (mellinEdgeMajorant_tendsto K).1
    (mellinEdgeMajorant_tendsto K).2 hmajor
  convert hs using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1 <;> funext t <;> dsimp [f,L] <;> ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCubeEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy of the actual cube-completed primal polynomial. Cube-divisor
fibers cost an arbitrary small power; the remaining weighted pair count
is linear in the norm cutoff, because the d-variable has exponent -2. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticCubeProduct_norm (du : Eisenstein × Eisenstein) :
    norm (metaplecticCubeProduct du) = norm du.2*norm du.1^3 := by
  change Complex.normSq ((du.2:ℂ)*(du.1:ℂ)^3) = _
  rw [Complex.normSq_mul,map_pow]
  rfl

lemma metaplectic_cube_fiber_card (S : Finset (Eisenstein × Eisenstein))
    (hS : ∀ du ∈ S, primary du.1 ∧ primary du.2) {b : Eisenstein} :
    (S.filter (fun du => metaplecticCubeProduct du = b)).card ≤
      (((S.image Prod.fst).filter (fun d => d ∣ b)).card) := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro du hdu
    obtain ⟨hdu,hb⟩ := Finset.mem_filter.mp hdu
    refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hdu,?_⟩
    rw [←hb]
    exact (dvd_pow_self du.1 (by norm_num : (3:ℕ) ≠ 0)).trans
      (dvd_mul_left _ _)
  · intro du hdu ev hev he
    obtain ⟨hdu,hb⟩ := Finset.mem_filter.mp hdu
    obtain ⟨hev,hevb⟩ := Finset.mem_filter.mp hev
    have hd : du.1 ≠ 0 := primary_ne_zero (hS du hdu).1
    apply Prod.ext he
    apply mul_right_cancel₀ (pow_ne_zero 3 hd)
    simpa only [metaplecticCubeProduct,←he] using hb.trans hevb.symm

lemma metaplectic_cube_pair_weight (S : Finset (Eisenstein × Eisenstein))
    (hS : ∀ du ∈ S, primary du.1 ∧ primary du.2) {V : ℝ} (hV : 0 ≤ V)
    (hsize : ∀ du ∈ S, norm (metaplecticCubeProduct du) ≤ V) :
    (∑ du ∈ S, norm du.1) ≤
      18*V*(∑' d : Eisenstein, norm d^(-2:ℝ)) := by
  let D := S.image Prod.fst
  have hrow (d : Eisenstein) (hd : d ∈ D) :
      (∑ du ∈ S with du.1 = d, norm du.1) ≤ 18*V*norm d^(-2:ℝ) := by
    obtain ⟨du,hdu,rfl⟩ := Finset.mem_image.mp hd
    have hdp : 0 < norm du.1 := norm_pos_of_ne_zero (primary_ne_zero (hS du hdu).1)
    let T := S.filter (fun ev => ev.1 = du.1)
    have hcard : (T.card:ℝ) ≤ 18*(V/norm du.1^3) := by
      have hcardN : T.card ≤ (nonzeroNormBall (V/norm du.1^3)).card := by
        apply Finset.card_le_card_of_injOn Prod.snd
        · intro ev hev
          obtain ⟨hev,he⟩ := Finset.mem_filter.mp hev
          apply mem_nonzeroNormBall.mpr
          refine ⟨(le_div_iff₀ (pow_pos hdp 3)).mpr ?_,primary_ne_zero (hS ev hev).2⟩
          have hs := hsize ev hev
          rw [metaplecticCubeProduct_norm,he] at hs
          exact hs
        · intro ev hev ew hew he
          exact Prod.ext ((Finset.mem_filter.mp hev).2.trans (Finset.mem_filter.mp hew).2.symm) he
      exact (Nat.cast_le.mpr hcardN).trans (nonzeroNormBall_card_le (by positivity))
    have hsum : (∑ ev ∈ T, norm ev.1) = (T.card:ℝ)*norm du.1 := by
      calc
        _ = ∑ _ev ∈ T, norm du.1 := Finset.sum_congr rfl (fun ev hev => congrArg norm (Finset.mem_filter.mp hev).2)
        _ = _ := by simp
    change (∑ ev ∈ T, norm ev.1) ≤ _
    rw [hsum]
    apply (mul_le_mul_of_nonneg_right hcard hdp.le).trans_eq
    rw [Real.rpow_neg hdp.le,Real.rpow_two]
    field_simp [hdp.ne']
  calc
    _ = ∑ d ∈ D, ∑ du ∈ S with du.1 = d, norm du.1 :=
      (Finset.sum_fiberwise_of_maps_to (fun du hdu => Finset.mem_image_of_mem _ hdu) _).symm
    _ ≤ ∑ d ∈ D, 18*V*norm d^(-2:ℝ) := Finset.sum_le_sum hrow
    _ = 18*V*(∑ d ∈ D, norm d^(-2:ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_eisenstein_norm_rpow (show (1:ℝ) < 2 by norm_num)).sum_le_tsum D
        (fun d _ => Real.rpow_nonneg (norm_nonneg d) _)) (by positivity)

/-- The coefficient energy after collecting actual cube products. -/
theorem metaplectic_cube_energy {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Eisenstein × Eisenstein)),
      (∀ du ∈ S, primary du.1 ∧ primary du.2) →
      ∀ (w : Eisenstein × Eisenstein → ℂ) (V M : ℝ), 1 ≤ V → 0 ≤ M →
      (∀ du ∈ S, norm (metaplecticCubeProduct du) ≤ V) →
      (∀ du ∈ S, ‖w du‖^2 ≤ norm du.1*M^2) →
      (∑ b ∈ S.image metaplecticCubeProduct, ‖metaplecticCubeCoefficient S w b‖^2) ≤
        C*V^(1+ε)*M^2 := by
  obtain ⟨D,hD,hdiv⟩ := primary_divisor_card_small_power hε
  let B := 18*(∑' d : Eisenstein, norm d^(-2:ℝ))
  have hB : 0 ≤ B := mul_nonneg (by norm_num)
    (tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _))
  refine ⟨D*(B+1),mul_pos hD (by linarith),?_⟩
  intro S hS w V M hV _hM hsize hw
  have hrow (b : Eisenstein) (hb : b ∈ S.image metaplecticCubeProduct) :
      ‖metaplecticCubeCoefficient S w b‖^2 ≤
        D*V^ε*(∑ du ∈ S with metaplecticCubeProduct du = b, ‖w du‖^2) := by
    have hCS := complex_bilinear_rows_sq (S.filter (fun du => metaplecticCubeProduct du = b))
      (fun _ => (1:ℂ)) w
    simp only [one_mul,norm_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hCS
    apply hCS.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    obtain ⟨du,hdu,rfl⟩ := Finset.mem_image.mp hb
    have hb0 : metaplecticCubeProduct du ≠ 0 :=
      mul_ne_zero (primary_ne_zero (hS du hdu).2) (pow_ne_zero 3 (primary_ne_zero (hS du hdu).1))
    exact (Nat.cast_le.mpr (metaplectic_cube_fiber_card S hS)).trans
      ((hdiv (S.image Prod.fst) (fun d hd => by
        obtain ⟨ev,hev,rfl⟩ := Finset.mem_image.mp hd
        exact (hS ev hev).1) _ hb0).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hsize du hdu) hε.le) hD.le))
  have henergy : (∑ du ∈ S, ‖w du‖^2) ≤ B*V*M^2 := by
    calc
      _ ≤ ∑ du ∈ S, norm du.1*M^2 := Finset.sum_le_sum hw
      _ = (∑ du ∈ S, norm du.1)*M^2 := (Finset.sum_mul _ _ _).symm
      _ ≤ (18*V*(∑' d : Eisenstein, norm d^(-2:ℝ)))*M^2 :=
        mul_le_mul_of_nonneg_right (metaplectic_cube_pair_weight S hS (by linarith) hsize) (sq_nonneg M)
      _ = _ := by dsimp [B]; ring
  calc
    _ ≤ ∑ b ∈ S.image metaplecticCubeProduct,
        D*V^ε*(∑ du ∈ S with metaplecticCubeProduct du = b, ‖w du‖^2) := Finset.sum_le_sum hrow
    _ = D*V^ε*(∑ du ∈ S, ‖w du‖^2) := by
      rw [←Finset.mul_sum,Finset.sum_fiberwise_of_maps_to (fun du hdu => Finset.mem_image_of_mem _ hdu)]
    _ ≤ D*V^ε*(B*V*M^2) := mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = D*B*V^(1+ε)*M^2 := by rw [Real.rpow_add (by linarith : 0 < V),Real.rpow_one]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hD.le)
      (Real.rpow_nonneg (by linarith) _)) (sq_nonneg M)

lemma metaplecticPrimalCoefficient_sq_le {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) {du : Eisenstein × Eisenstein}
    (hd : primary du.1) (hu : primary du.2) {M : ℝ} (_hM : 0 ≤ M)
    (hW : ‖W (norm (metaplecticCubeProduct du)/X)‖ ≤ M) :
    ‖metaplecticPrimalCoefficient r ℓ W X du‖^2 ≤ norm du.1*M^2 := by
  have hg : ‖gauss (r*du.2)‖ ≤ 1 := by
    rw [norm_gauss (primary_mul hr hu)]
    split_ifs <;> norm_num
  have ht : ‖theta ℓ (r*metaplecticCubeProduct du)‖ = 1 :=
    norm_theta (primary_ne_zero (primary_mul hr
      (primary_mul hu (by simpa only [pow_succ,pow_zero,one_mul] using primary_mul (primary_mul hd hd) hd)))) ℓ
  unfold metaplecticPrimalCoefficient
  split_ifs
  · have hh : ‖(Real.sqrt (norm du.1):ℂ)*gauss (r*du.2)*
        theta ℓ (r*metaplecticCubeProduct du)*W (norm (metaplecticCubeProduct du)/X)‖ ≤
        Real.sqrt (norm du.1)*M := by
      rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _),ht,mul_one]
      calc
        _ ≤ (Real.sqrt (norm du.1)*1)*M := by gcongr
        _ = _ := by ring
    exact (pow_le_pow_left₀ (_root_.norm_nonneg _) hh 2).trans_eq (by
      rw [mul_pow,Real.sq_sqrt (norm_nonneg _)])
  · rw [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)]
    exact mul_nonneg (norm_nonneg _) (sq_nonneg M)

/-- No coefficient-energy hypothesis remains for the actual completed
Gauss summand: its modulus bound is supplied by the Gauss and angular
identities. -/
theorem metaplectic_primal_energy {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Eisenstein × Eisenstein)),
      (∀ du ∈ S, primary du.1 ∧ primary du.2) →
      ∀ (r : Eisenstein), primary r → ∀ (ℓ : ℤ) (W : ℝ → ℂ) (X V M : ℝ),
      1 ≤ V → 0 ≤ M → (∀ du ∈ S, norm (metaplecticCubeProduct du) ≤ V) →
      (∀ du ∈ S, ‖W (norm (metaplecticCubeProduct du)/X)‖ ≤ M) →
      (∑ b ∈ S.image metaplecticCubeProduct,
        ‖metaplecticCubeCoefficient S (metaplecticPrimalCoefficient r ℓ W X) b‖^2) ≤
          C*V^(1+ε)*M^2 := by
  obtain ⟨C,hC,hE⟩ := metaplectic_cube_energy hε
  refine ⟨C,hC,?_⟩
  intro S hS r hr ℓ W X V M hV hM hsize hW
  exact hE S hS _ V M hV hM hsize (fun du hdu =>
    metaplecticPrimalCoefficient_sq_le hr ℓ W X (hS du hdu).1 (hS du hdu).2 hM (hW du hdu))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCubeMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Montgomery--Vaughan applied to the actual finite cube-completed
angular Gauss sum. Both the rational norm multiplicity and the original
coefficient energy are supplied by proved arithmetic lemmas. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_cube_polynomial_collect (S : Finset (Eisenstein × Eisenstein))
    (w : Eisenstein × Eisenstein → ℂ) (t : ℝ) :
    (∑ du ∈ S, w du*mellinPhase t (norm (metaplecticCubeProduct du))) =
      eisensteinNormPolynomial (S.image metaplecticCubeProduct) (metaplecticCubeCoefficient S w) t := by
  unfold eisensteinNormPolynomial metaplecticCubeCoefficient
  rw [←Finset.sum_fiberwise_of_maps_to (fun du hdu => Finset.mem_image_of_mem metaplecticCubeProduct hdu)
    (fun du => w du*mellinPhase t (norm (metaplecticCubeProduct du)))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro du hdu
  rw [(Finset.mem_filter.mp hdu).2]

lemma metaplectic_cube_output_primary (S : Finset (Eisenstein × Eisenstein))
    (hS : ∀ du ∈ S, primary du.1 ∧ primary du.2) :
    ∀ b ∈ S.image metaplecticCubeProduct, primary b := by
  intro b hb
  obtain ⟨du,hdu,rfl⟩ := Finset.mem_image.mp hb
  exact primary_mul (hS du hdu).2 (by
    simpa only [pow_succ,pow_zero,one_mul] using
      primary_mul (primary_mul (hS du hdu).1 (hS du hdu).1) (hS du hdu).1)

lemma metaplectic_cube_norm_frequencies (S : Finset (Eisenstein × Eisenstein))
    (hS : ∀ du ∈ S, primary du.1 ∧ primary du.2) {V : ℝ}
    (hsize : ∀ du ∈ S, norm (metaplecticCubeProduct du) ≤ V) :
    ∀ b ∈ S.image metaplecticCubeProduct, normNat b ∈ Finset.Icc 1 ⌈V⌉₊ := by
  intro b hb
  have hp := metaplectic_cube_output_primary S hS b hb
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (show (1:ℝ) ≤ (normNat b:ℝ) by rw [normNat_cast]; exact one_le_norm (primary_ne_zero hp))
  · have hbV : norm b ≤ V := by
      obtain ⟨du,hdu,rfl⟩ := Finset.mem_image.mp hb
      exact hsize du hdu
    have hh : (normNat b:ℝ) ≤ (⌈V⌉₊:ℝ) := by
      rw [normNat_cast]
      exact hbV.trans (Nat.le_ceil V)
    exact_mod_cast hh

/-- The one-sided height mean for the literal completed angular
coefficients. The only analytic hypothesis is the published ordinary
Montgomery--Vaughan theorem. -/
theorem metaplectic_primal_meanAbsolute_sq {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset (Eisenstein × Eisenstein)),
      (∀ du ∈ S, primary du.1 ∧ primary du.2) →
      ∀ (r : Eisenstein), primary r → ∀ (ℓ : ℤ) (W : ℝ → ℂ) (X V M T u : ℝ),
      1 ≤ V → 0 ≤ M → 0 < T →
      (∀ du ∈ S, norm (metaplecticCubeProduct du) ≤ V) →
      (∀ du ∈ S, ‖W (norm (metaplecticCubeProduct du)/X)‖ ≤ M) →
      ((∫ t in T..2*T, ‖∑ du ∈ S, metaplecticPrimalCoefficient r ℓ W X du*
        mellinPhase (t+u) (norm (metaplecticCubeProduct du))‖)/T)^2 ≤
          C*K*(1+2*V/T)*V^(1+ε)*M^2 := by
  let δ := ε/2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨D,hD,hfiber⟩ := primary_norm_fiber_length_bound hδ
  obtain ⟨E,hE,henergy⟩ := metaplectic_primal_energy hδ
  refine ⟨D*E*2^δ,by positivity,?_⟩
  intro S hS r hr ℓ W X V M T u hV hM hT hsize hW
  let A := S.image metaplecticCubeProduct
  let v := metaplecticCubeCoefficient S (metaplecticPrimalCoefficient r ℓ W X)
  have hp := metaplectic_cube_output_primary S hS
  have hz := metaplectic_cube_norm_frequencies S hS hsize
  have he := henergy S hS r hr ℓ W X V M hV hM hsize hW
  have hm := fixedAngular_translated_meanAbsolute_sq hMV hC A v ⌈V⌉₊ (D*(⌈V⌉₊:ℝ)^δ)
    hz (fun b hb => primary_ne_zero (hp b hb)) (hfiber A hp ⌈V⌉₊) 0 u hT
  simp only [theta,zpow_zero,mul_one] at hm
  have hV0 : 0 < V := zero_lt_one.trans_le hV
  have hceil : (⌈V⌉₊:ℝ) ≤ 2*V := by linarith [Nat.ceil_lt_add_one hV0.le]
  have hceilP : (⌈V⌉₊:ℝ)^δ ≤ (2*V)^δ :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hceil hδ.le
  have hfactor : 1+(⌈V⌉₊:ℝ)/T ≤ 1+2*V/T := by
    linarith [div_le_div_of_nonneg_right hceil hT.le]
  have hpow : (2*V)^δ*V^(1+δ) = 2^δ*V^(1+ε) := by
    rw [Real.mul_rpow (by norm_num) hV0.le,mul_assoc,←Real.rpow_add hV0]
    congr 2
    dsimp [δ]
    ring
  simp_rw [metaplectic_cube_polynomial_collect] 
  change ((∫ t in T..2*T, ‖eisensteinNormPolynomial A v (t+u)‖)/T)^2 ≤ _
  have hm' : ((∫ t in T..2*T, ‖eisensteinNormPolynomial A v (t+u)‖)/T)^2 ≤
      C*(1+(⌈V⌉₊:ℝ)/T)*(D*(⌈V⌉₊:ℝ)^δ)*(∑ b ∈ A, ‖v b‖^2) := hm
  calc
    _ ≤ C*(1+(⌈V⌉₊:ℝ)/T)*(D*(⌈V⌉₊:ℝ)^δ)*(E*V^(1+δ)*M^2) :=
      hm'.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ ≤ C*(1+2*V/T)*(D*(2*V)^δ)*(E*V^(1+δ)*M^2) := by gcongr
    _ = C*(D*E)*(1+2*V/T)*((2*V)^δ*V^(1+δ))*M^2 := by ring
    _ = _ := by rw [hpow]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrimalFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma metaplecticPrimalElementSupport_primary (V : ℝ) :
    ∀ du ∈ metaplecticPrimalElementSupport V, primary du.1 ∧ primary du.2 := by
  intro du hdu
  obtain ⟨ev,_hev,rfl⟩ := Finset.mem_image.mp hdu
  exact ⟨ev.1.property,ev.2.property⟩

lemma metaplecticPrimalElementSupport_size (V : ℝ) :
    ∀ du ∈ metaplecticPrimalElementSupport V, norm (metaplecticCubeProduct du) ≤ V := by
  intro du hdu
  obtain ⟨ev,hev,rfl⟩ := Finset.mem_image.mp hdu
  exact (Finset.mem_filter.mp hev).2

/-- The mean estimate now applies to the original infinite completed
series, with finiteness and all coefficient bounds discharged. -/
theorem metaplecticHeightCompleted_meanAbsolute_sq {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : Eisenstein, primary r →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ) (X B V M T u : ℝ), 0 < X → B*X ≤ V →
      (∀ x : ℝ, B < x → W x = 0) → (∀ x : ℝ, ‖W x‖ ≤ M) →
      1 ≤ V → 0 ≤ M → 0 < T →
      ((∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W X (t+u)‖)/T)^2 ≤
        C*K*(1+2*V/T)*V^(1+ε)*M^2 := by
  obtain ⟨K,hK,hbound⟩ := metaplectic_primal_meanAbsolute_sq hε hMV hC
  refine ⟨K,hK,?_⟩
  intro r hr ℓ W X B V M T u hX hBV hcut hW hV hM hT
  simp_rw [metaplecticHeightCompleted_finite r ℓ W hX hBV hcut]
  exact hbound _ (metaplecticPrimalElementSupport_primary V) r hr ℓ W X V M T u hV hM hT
    (metaplecticPrimalElementSupport_size V) (fun du _ => hW _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticMellinMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Fubini for the metaplectic height average. The integrable
majorant is deduced from the published mean square and the actual smooth
Mellin transform; no contour identity is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

/-- A bound for the integral in the finite height variable is enough for
absolute Fubini and a bound after integrating in the other variable. -/
lemma integral_height_norm_le (K : ℝ × ℝ → ℂ) (hK : Continuous K)
    {a b : ℝ} (hab : a ≤ b) (B : ℝ → ℝ) (hB : Integrable B)
    (hbound : ∀ v : ℝ, (∫ t in a..b, ‖K (v,t)‖) ≤ B v) :
    (∫ t in a..b, ‖∫ v : ℝ, K (v,t)‖) ≤ ∫ v : ℝ, B v := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hm : AEStronglyMeasurable K (volume.prod μ) := hK.aestronglyMeasurable
  have hb (v : ℝ) : (∫ t, ‖K (v,t)‖ ∂μ) ≤ B v := by
    simpa only [μ,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
      using hbound v
  have hi : Integrable K (volume.prod μ) := by
    apply (integrable_prod_iff hm).mpr
    constructor
    · exact Filter.Eventually.of_forall (fun v =>
        (hK.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc)
    · apply hB.mono' hm.norm.integral_prod_right'
      exact Filter.Eventually.of_forall (fun v => by
        rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => _root_.norm_nonneg _))]
        exact hb v)
  have h := calc
    (∫ t, ‖∫ v : ℝ, K (v,t)‖ ∂μ) ≤ ∫ t, (∫ v : ℝ, ‖K (v,t)‖) ∂μ :=
      integral_mono hi.integral_prod_right.norm hi.integral_norm_prod_right
        (fun t => norm_integral_le_integral_norm _)
    _ = ∫ v : ℝ, ∫ t, ‖K (v,t)‖ ∂μ := (integral_integral_swap hi.norm).symm
    _ ≤ ∫ v : ℝ, B v := integral_mono hi.integral_norm_prod_left hB hb
  simpa only [μ,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCoefficientMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arithmetic bounds for the actual dual coefficients. Clearing the
ramified denominator identifies every common level prime among the two
supported factors; the free factor is coprime to the level. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_numerator_of_frequency (n : MetaplecticDualArgument)
    {j : ℤ} (hj : -1 ≤ j) (ζ : Eisensteinˣ) (h h' w : Eisenstein)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3) :
    n.val = lambdaE^(j+1).toNat*ζ.val*h*w*h'^3 := by
  apply Subtype.ext
  have hz : ((j+1).toNat:ℤ) = j+1 := Int.toNat_of_nonneg (by omega)
  have hn : (n.val:ℂ) = metaplecticFrequency n*traceLambda := by
    rw [metaplecticFrequency,div_mul_cancel₀ _ traceLambda_ne_zero]
  rw [hn,he]
  push_cast
  rw [lambdaE_coe,←zpow_natCast traceLambda (j+1).toNat, hz]
  rw [zpow_add₀ traceLambda_ne_zero,zpow_one]
  ring

lemma metaplecticCommonNorm_le_supported {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) (k : ℕ) (ζ : Eisensteinˣ)
    {h h' w : Eisenstein} (hh : primary h) (hh' : primary h') (hwr : IsCoprime w r)
    (he : n.val = lambdaE^k*ζ.val*h*w*h'^3) :
    metaplecticCommonNorm r n ≤ norm h*norm h' := by
  let S := (primaryPrimeFactors r).filter (fun p => p ∣ n.val)
  have hsub : S ⊆ primaryPrimeFactors r := Finset.filter_subset _ _
  have hp (p : Eisenstein) (hpm : p ∈ S) : p ∣ h*h' := by
    obtain ⟨hpr,hpn⟩ := Finset.mem_filter.mp hpm
    have hspec := primaryPrimeFactor_spec hr hpr
    have hprime := hspec.1.2
    rw [he] at hpn
    rcases hprime.dvd_mul.mp hpn with hpn | hp'
    · rcases hprime.dvd_mul.mp hpn with hpn | hpw
      · rcases hprime.dvd_mul.mp hpn with hpn | hph
        · rcases hprime.dvd_mul.mp hpn with hpl | hpζ
          · exact False.elim (hprime.not_isUnit
              ((primary_coprime_lambda hr).isUnit_of_dvd' hspec.2
                (hprime.dvd_of_dvd_pow hpl)))
          · exact False.elim (hprime.not_isUnit (isUnit_of_dvd_unit hpζ ζ.isUnit))
        · exact dvd_mul_of_dvd_left hph h'
      · exact False.elim (hprime.not_isUnit (hwr.isUnit_of_dvd' hpw hspec.2))
    · exact dvd_mul_of_dvd_right (hprime.dvd_of_dvd_pow hp') h
  have hdiv := (primary_subsets_prod_dvd hr hsub (h*h')).mpr hp
  have heq : metaplecticCommonNorm r n = norm (∏ p ∈ S, p) := by
    rw [norm_finset_prod]
    rfl
  rw [heq,←norm_mul_eq]
  exact norm_le_of_dvd (mul_ne_zero (primary_ne_zero hh) (primary_ne_zero hh')) hdiv

/-- The published coefficient support gives this bound with no angular
restriction. It will be summed using the actual lattice norm series. -/
lemma metaplectic_actual_coefficient_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {r : Eisenstein} (hr : primary r) (n : MetaplecticDualArgument)
    {j : ℤ} (hj : -1 ≤ j) (ζ : Eisensteinˣ) {h h' w : Eisenstein}
    (hh : primary h) (hh' : primary h') (hwr : IsCoprime w r)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3)
    (ha : ‖a r n‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')) :
    ‖a r n*metaplecticLocalCoefficient r n‖ ≤
      C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*(norm h*norm h') := by
  rw [norm_mul]
  apply mul_le_mul ha
    ((norm_metaplecticLocalCoefficient_le hr n).trans
      (metaplecticCommonNorm_le_supported hr n (j+1).toNat ζ hh hh' hwr
        (metaplectic_numerator_of_frequency n hj ζ h h' w he)))
    (_root_.norm_nonneg _) (by positivity)

private lemma metaplectic_norm_pow (a : Eisenstein) (k : ℕ) : norm (a^k) = norm a^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,norm_mul_eq,ih,pow_succ]

private lemma metaplectic_lambda_norm : norm lambdaE = 3 := by
  have hs : norm lambdaE^2 = 9 := by
    rw [←metaplectic_norm_pow,lambdaE_sq]
    change Complex.normSq (-3 : ℂ) = 9
    norm_num
  nlinarith [norm_nonneg lambdaE]

lemma metaplectic_frequency_norm (n : MetaplecticDualArgument) (k : ℕ)
    (ζ : Eisensteinˣ) (h h' w : Eisenstein)
    (he : n.val = lambdaE^k*ζ.val*h*w*h'^3) :
    Complex.normSq (metaplecticFrequency n) =
      (3:ℝ)^((k:ℝ)-1)*norm h*norm w*norm h'^3 := by
  have hLambda : Complex.normSq traceLambda = 3 := by
    rw [←lambdaE_coe]
    exact metaplectic_lambda_norm
  rw [metaplecticFrequency,Complex.normSq_div,hLambda]
  change norm n.val/3 = _
  rw [he,norm_mul_eq,norm_mul_eq,norm_mul_eq,norm_mul_eq,
    metaplectic_norm_pow,metaplectic_norm_pow,metaplectic_lambda_norm,
    norm_of_isUnit ζ.isUnit,mul_one]
  rw [Real.rpow_sub (by norm_num : (0:ℝ)<3),Real.rpow_natCast,Real.rpow_one]
  ring

lemma metaplectic_squarefree_supported_divisor {r h : Eisenstein}
    (hh : Squarefree h) (hs : ∃ k : ℕ, h ∣ r^k) : h ∣ r := by
  obtain ⟨k,hk⟩ := hs
  by_cases hk0 : k = 0
  · subst k
    simpa only [pow_zero] using hk.trans (one_dvd r)
  · exact (hh.dvd_pow_iff_dvd hk0).mp hk

lemma metaplectic_supported_divisor_mem {r h w : Eisenstein}
    (hr : primary r) (hh : primary h) (hs : Squarefree (h*w))
    (hdiv : ∃ k : ℕ, h ∣ r^k) : h ∈ metaplecticPrimaryDivisors r := by
  have hhdiv : h ∣ r := metaplectic_squarefree_supported_divisor (hs.squarefree_of_dvd (dvd_mul_right h w)) hdiv
  exact Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr
    ⟨hh,norm_le_of_dvd (primary_ne_zero hr) hhdiv⟩,hhdiv⟩

lemma metaplectic_units_finite : Finite (Eisensteinˣ) := by
  let f : Eisensteinˣ → {u : Eisenstein // u ∈ nonzeroNormBall 1} := fun u =>
    ⟨u,mem_nonzeroNormBall.mpr ⟨by rw [norm_of_isUnit u.isUnit],u.ne_zero⟩⟩
  have hf : Function.Injective f := by
    intro u v h
    apply Units.ext
    exact congrArg Subtype.val h
  exact Finite.of_injective f hf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCoefficientDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dual coefficient bound becomes a product of a geometric
ramified factor and convergent norm powers. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_monomial_decay {H P W : ℝ} (hH : 0 < H) (hP : 0 < P) (hW : 0 < W)
    (σ : ℝ) (k : ℕ) :
    ((3:ℝ)^((k:ℝ)/3)*Real.sqrt P*(H*P))/
        (((3:ℝ)^((k:ℝ)-1)*H*W*P^3)^(1+σ)) =
      (3:ℝ)^(1+σ)*metaplecticRamifiedRatio σ^k*
        H^(-σ)*W^(-1-σ)*P^(-3/2-3*σ) := by
  have h3 : (3:ℝ)^((k:ℝ)/3)/(((3:ℝ)^((k:ℝ)-1))^(1+σ)) =
      (3:ℝ)^(1+σ)*metaplecticRamifiedRatio σ^k := by
    rw [←Real.rpow_mul (by norm_num),←Real.rpow_sub (by norm_num)]
    unfold metaplecticRamifiedRatio
    rw [←Real.rpow_mul_natCast (by norm_num),←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hH' : H/H^(1+σ) = H^(-σ) := by
    calc
      _ = H^(1:ℝ)/H^(1+σ) := by rw [Real.rpow_one]
      _ = H^(1-(1+σ)) := (Real.rpow_sub hH _ _).symm
      _ = _ := by congr 1; ring
  have hW' : 1/W^(1+σ) = W^(-1-σ) := by
    rw [one_div,←Real.rpow_neg hW.le]
    congr 1
    ring
  have hP' : (Real.sqrt P*P)/(P^3)^(1+σ) = P^(-3/2-3*σ) := by
    calc
      _ = (P^(1/2:ℝ)*P^(1:ℝ))/P^((3:ℝ)*(1+σ)) := by
        rw [Real.sqrt_eq_rpow,Real.rpow_one,←Real.rpow_natCast_mul hP.le]
        norm_num
      _ = P^((1/2+1)-(3:ℝ)*(1+σ)) := by
        rw [←Real.rpow_add hP,←Real.rpow_sub hP]
      _ = _ := by congr 1; ring
  rw [Real.mul_rpow (by positivity) (pow_nonneg hP.le _),
    Real.mul_rpow (by positivity) hW.le,
    Real.mul_rpow (by positivity) hH.le]
  calc
    _ = ((3:ℝ)^((k:ℝ)/3)/(((3:ℝ)^((k:ℝ)-1))^(1+σ)))*
        (H/H^(1+σ))*(1/W^(1+σ))*((Real.sqrt P*P)/(P^3)^(1+σ)) := by ring
    _ = _ := by rw [h3,hH',hW',hP']

lemma metaplecticRamifiedRatio_bounds {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ metaplecticRamifiedRatio σ ∧ metaplecticRamifiedRatio σ < 1 := by
  exact ⟨Real.rpow_nonneg (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩

/-- Decay of an actual nonzero Voronoi coefficient with its published
support representation. The free and cubed factors now have convergent
norm exponents. -/
theorem metaplectic_coefficient_decay
    {a : Eisenstein → MetaplecticDualArgument → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {r : Eisenstein} (hr : primary r) (n : MetaplecticDualArgument)
    {j : ℤ} (hj : -1 ≤ j) (ζ : Eisensteinˣ) {h h' w : Eisenstein}
    (hh : primary h) (hh' : primary h') (hw : primary w) (hwr : IsCoprime w r)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3)
    (ha : ‖a r n‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')) (σ : ℝ) :
    ‖a r n*metaplecticLocalCoefficient r n‖/
        (Complex.normSq (metaplecticFrequency n))^(1+σ) ≤
      C*(3:ℝ)^(1+σ)*metaplecticRamifiedRatio σ^((j+1).toNat)*
        norm h^(-σ)*norm w^(-1-σ)*norm h'^(-3/2-3*σ) := by
  let k := (j+1).toNat
  have hjk : (k:ℝ) = (j:ℝ)+1 := by
    dsimp [k]
    have hi : (((j+1).toNat:ℕ):ℤ) = j+1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hi
  have hmax : ((max j 0:ℤ):ℝ) ≤ k := by
    rw [hjk]
    exact_mod_cast (show max j 0 ≤ j+1 by omega)
  have h3 : (3:ℝ)^((max j 0:ℤ)/3:ℝ) ≤ (3:ℝ)^((k:ℝ)/3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hh0 := norm_nonneg h
  have hhp0 := norm_nonneg h'
  have hw0 := norm_nonneg w
  have hc := metaplectic_actual_coefficient_bound hC hr n hj ζ hh hh' hwr he ha
  have hc' : ‖a r n*metaplecticLocalCoefficient r n‖ ≤
      C*((3:ℝ)^((k:ℝ)/3)*Real.sqrt (norm h')*(norm h*norm h')) := by
    calc
      _ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*(norm h*norm h') := hc
      _ ≤ C*3^((k:ℝ)/3)*Real.sqrt (norm h')*(norm h*norm h') := by gcongr
      _ = _ := by ring
  have hn := metaplectic_frequency_norm n k ζ h h' w
    (metaplectic_numerator_of_frequency n hj ζ h h' w he)
  rw [hn]
  apply (div_le_div_of_nonneg_right hc' (by positivity)).trans_eq
  rw [mul_div_assoc,metaplectic_monomial_decay
    (norm_pos_of_ne_zero (primary_ne_zero hh))
    (norm_pos_of_ne_zero (primary_ne_zero hh'))
    (norm_pos_of_ne_zero (primary_ne_zero hw)) σ k]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCoefficientSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the separated arithmetic majorant from the actual Voronoi
support. The two free norm series and the ramified geometric series
converge, while the squarefree supported factor is a divisor of the level. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_divisor_weight_small_power {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      (∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ)) ≤ C*norm r^ε := by
  obtain ⟨C,hC,hdiv⟩ := primary_divisor_card_small_power hε
  refine ⟨C,hC,?_⟩
  intro r hr
  calc
    _ ≤ ∑ _h ∈ metaplecticPrimaryDivisors r, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (one_le_norm (primary_ne_zero (mem_primaryElementBall.mp (Finset.mem_filter.mp hh).1).1))
        (by linarith)
    _ = ((metaplecticPrimaryDivisors r).card:ℝ) := by simp
    _ ≤ C*norm r^ε := hdiv (primaryElementBall (norm r))
      (fun _ hh => (mem_primaryElementBall.mp hh).1) r (primary_ne_zero hr)

lemma metaplecticCodeWeight_nonneg (r : Eisenstein) (σ : ℝ)
    (z : MetaplecticCoefficientCode r) : 0 ≤ metaplecticCodeWeight r σ z := by
  unfold metaplecticCodeWeight metaplecticRamifiedRatio
  exact mul_nonneg (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
    (mul_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))))

private lemma metaplectic_product_hasSum {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    {A B : ℝ} (hf : HasSum f A) (hg : HasSum g B)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ b, 0 ≤ g b) :
    HasSum (fun z : α × β => f z.1*g z.2) (A*B) :=
  hf.mul hg (hf.summable.mul_of_nonneg hg.summable hf0 hg0)

lemma metaplecticCodeWeight_hasSum (r : Eisenstein) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (metaplecticCodeWeight r σ)
      ((1-metaplecticRamifiedRatio σ)⁻¹*(Nat.card (Eisensteinˣ):ℝ)*
      (∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ))*
      (∑' h : PrimaryArgument, norm h^(-3/2-3*σ))*
      (∑' w : PrimaryArgument, norm w^(-1-σ))) := by
  let : Finite (Eisensteinˣ) := metaplectic_units_finite
  let : Fintype (Eisensteinˣ) := Fintype.ofFinite _
  have hq := metaplecticRamifiedRatio_bounds hσ
  have hk := hasSum_geometric_of_lt_one hq.1 hq.2
  have hw : Summable (fun w : PrimaryArgument => norm w^(-1-σ)) := by
    convert primary_norm_rpow_summable (show 1 < 1+σ by linarith) using 1
    all_goals try with_reducible_and_instances rfl
    ext w
    congr 1
    ring
  have hp : Summable (fun h : PrimaryArgument => norm h^(-3/2-3*σ)) := by
    convert primary_norm_rpow_summable (show 1 < 3/2+3*σ by linarith) using 1
    all_goals try with_reducible_and_instances rfl
    ext w
    congr 1
    ring
  have hpw := metaplectic_product_hasSum hp.hasSum hw.hasSum
    (fun h => Real.rpow_nonneg (norm_nonneg h) _)
    (fun w => Real.rpow_nonneg (norm_nonneg w) _)
  have hh : HasSum (fun h : metaplecticPrimaryDivisors r => norm h.val^(-σ))
      (∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ)) := by
    rw [←Finset.sum_coe_sort]
    exact hasSum_fintype _
  have hhpw := metaplectic_product_hasSum hh hpw
    (fun h => Real.rpow_nonneg (norm_nonneg h.val) _)
    (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg z.1) _)
      (Real.rpow_nonneg (norm_nonneg z.2) _))
  have hu : HasSum (fun _ : Eisensteinˣ => (1:ℝ)) (Nat.card (Eisensteinˣ):ℝ) := by
    simpa using (hasSum_fintype (fun _ : Eisensteinˣ => (1:ℝ)))
  have huh := metaplectic_product_hasSum hu hhpw (fun _ => zero_le_one)
    (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg z.1.val) _)
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg z.2.1) _)
        (Real.rpow_nonneg (norm_nonneg z.2.2) _)))
  have hall := metaplectic_product_hasSum hk huh (fun _ => pow_nonneg hq.1 _)
    (fun z => mul_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg (norm_nonneg z.2.1.val) _)
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg z.2.2.1) _)
        (Real.rpow_nonneg (norm_nonneg z.2.2.2) _))))
  change HasSum (fun z : MetaplecticCoefficientCode r => metaplecticCodeWeight r σ z) _
  simpa only [metaplecticCodeWeight,mul_assoc] using hall

lemma metaplecticCodeWeight_summable (r : Eisenstein) {σ : ℝ} (hσ : 0 < σ) :
    Summable (metaplecticCodeWeight r σ) := (metaplecticCodeWeight_hasSum r hσ).summable

lemma metaplecticCodeWeight_tsum (r : Eisenstein) {σ : ℝ} (hσ : 0 < σ) :
    (∑' z : MetaplecticCoefficientCode r, metaplecticCodeWeight r σ z) =
      (1-metaplecticRamifiedRatio σ)⁻¹*(Nat.card (Eisensteinˣ):ℝ)*
      (∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ))*
      (∑' h : PrimaryArgument, norm h^(-3/2-3*σ))*
      (∑' w : PrimaryArgument, norm w^(-1-σ)) :=
  (metaplecticCodeWeight_hasSum r hσ).tsum_eq

/-- The full separated majorant has an arbitrarily small level loss. -/
theorem metaplecticCodeWeight_small_power {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      (∑' z : MetaplecticCoefficientCode r, metaplecticCodeWeight r σ z) ≤ C*norm r^ε := by
  obtain ⟨D,hD,hdiv⟩ := metaplectic_divisor_weight_small_power hε hσ
  let A := (1-metaplecticRamifiedRatio σ)⁻¹*(Nat.card (Eisensteinˣ):ℝ)*
    (∑' h : PrimaryArgument, norm h^(-3/2-3*σ))*
    (∑' w : PrimaryArgument, norm w^(-1-σ))
  have hA : 0 ≤ A := by
    have hden : 0 ≤ 1-metaplecticRamifiedRatio σ :=
      sub_nonneg.mpr (metaplecticRamifiedRatio_bounds hσ).2.le
    have hp : 0 ≤ ∑' h : PrimaryArgument, norm h^(-3/2-3*σ) :=
      tsum_nonneg (fun h => Real.rpow_nonneg (norm_nonneg h) _)
    have hw : 0 ≤ ∑' w : PrimaryArgument, norm w^(-1-σ) :=
      tsum_nonneg (fun w => Real.rpow_nonneg (norm_nonneg w) _)
    exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hden) (Nat.cast_nonneg _)) hp) hw
  refine ⟨D*(A+1),mul_pos hD (by linarith),?_⟩
  intro r hr
  rw [metaplecticCodeWeight_tsum r hσ]
  calc
    _ = A*(∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ)) := by dsimp [A]; ring
    _ ≤ A*(D*norm r^ε) := mul_le_mul_of_nonneg_left (hdiv r hr) hA
    _ ≤ D*(A+1)*norm r^ε := by nlinarith [Real.rpow_nonneg (norm_nonneg r) ε]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCoefficientMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injective coding of the actual published theta coefficients gives
the absolute dual coefficient mass with a subpower level loss. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticCoefficientMassTerm_nonneg
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (σ : ℝ)
    (n : MetaplecticDualArgument) : 0 ≤ metaplecticCoefficientMassTerm a r σ n := by
  exact div_nonneg (_root_.norm_nonneg _) (Real.rpow_nonneg (Complex.normSq_nonneg _) _)

lemma metaplectic_coefficient_codes
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    (σ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ n : MetaplecticDualArgument, a r n*metaplecticLocalCoefficient r n ≠ 0 →
        ∃ z : MetaplecticCoefficientCode r,
          n.val = metaplecticDecode r z ∧
          metaplecticCoefficientMassTerm a r σ n ≤ K*metaplecticCodeWeight r σ z := by
  obtain ⟨C,hC,hbound⟩ := ha
  refine ⟨C*(3:ℝ)^(1+σ),mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  intro r hr hsr n hn
  obtain ⟨j,ζ,h,h',w,hj,hh,hh',hw,hdiv,_h'div,hwr,hs,he,hcoef⟩ := hbound r hr hsr n hn
  let z : MetaplecticCoefficientCode r :=
    ((j+1).toNat,ζ,⟨h,metaplectic_supported_divisor_mem hr hh hs hdiv⟩,⟨h',hh'⟩,⟨w,hw⟩)
  refine ⟨z,metaplectic_numerator_of_frequency n hj ζ h h' w he,?_⟩
  have hb := metaplectic_coefficient_decay hC.le hr n hj ζ hh hh' hw hwr he hcoef σ
  apply hb.trans_eq
  dsimp [metaplecticCodeWeight,z]
  ring

/-- The absolute dual coefficient sum is derived from the literal
published support formula, not postulated as a Voronoi estimate. -/
theorem metaplectic_coefficient_mass_small_power
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      Summable (metaplecticCoefficientMassTerm a r σ) ∧
      (∑' n : MetaplecticDualArgument, metaplecticCoefficientMassTerm a r σ n) ≤ C*norm r^ε := by
  obtain ⟨K,hK,hcodes⟩ := metaplectic_coefficient_codes ha σ
  obtain ⟨D,hD,hcodeBound⟩ := metaplecticCodeWeight_small_power hε hσ
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro r hr hsr
  let I := {n : MetaplecticDualArgument // a r n*metaplecticLocalCoefficient r n ≠ 0}
  choose f he hb using fun n : I => hcodes r hr hsr n.val n.property
  have hf : Function.Injective f := by
    intro n m hfm
    apply Subtype.ext
    apply Subtype.ext
    exact (he n).trans ((congrArg (metaplecticDecode r) hfm).trans (he m).symm)
  have hfullCode : Summable (fun z : MetaplecticCoefficientCode r => K*metaplecticCodeWeight r σ z) :=
    (metaplecticCodeWeight_summable r hσ).mul_left K
  have hI : Summable (fun n : I => metaplecticCoefficientMassTerm a r σ n) :=
    (hfullCode.comp_injective hf).of_nonneg_of_le
      (fun n => metaplecticCoefficientMassTerm_nonneg a r σ n) hb
  have hsupp : Function.support (metaplecticCoefficientMassTerm a r σ) ⊆
      {n | a r n*metaplecticLocalCoefficient r n ≠ 0} := by
    intro n hn hezero
    exact hn (by simp [metaplecticCoefficientMassTerm,hezero])
  have hsum : HasSum (metaplecticCoefficientMassTerm a r σ)
      (∑' n : I, metaplecticCoefficientMassTerm a r σ n) :=
    (hasSum_subtype_iff_of_support_subset hsupp).mp hI.hasSum
  refine ⟨hsum.summable,?_⟩
  rw [hsum.tsum_eq]
  calc
    _ ≤ ∑' z : MetaplecticCoefficientCode r, K*metaplecticCodeWeight r σ z :=
      hI.tsum_le_tsum_of_inj f hf
        (fun z _ => mul_nonneg hK.le (metaplecticCodeWeight_nonneg r σ z)) hb hfullCode
    _ = K*(∑' z : MetaplecticCoefficientCode r, metaplecticCodeWeight r σ z) :=
      (metaplecticCodeWeight_summable r hσ).tsum_mul_left K
    _ ≤ K*(D*norm r^ε) := mul_le_mul_of_nonneg_left (hcodeBound r hr) hK.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticDualScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scaling of the actual angular Voronoi terms. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma norm_complexAngular {z : ℂ} (hz : z ≠ 0) (ℓ : ℤ) : ‖complexAngular ℓ z‖ = 1 := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp [complexAngular,norm_zpow,hn]

lemma metaplectic_argument_power {B D P R X : ℝ}
    (hB : 0 < B) (hD : 0 < D) (hP : 0 < P) (hR : 0 < R) (hX : 0 < X) (σ : ℝ) :
    ((B^4*D^3*P*X)/R^2)^(-σ) =
      B^(-4*σ)*D^(-3*σ)*P^(-σ)*X^(-σ)*R^(2*σ) := by
  have hb : (B^4)^(-σ) = B^(-4*σ) := by
    rw [←Real.rpow_natCast_mul hB.le]
    congr 1
    norm_num
  have hd : (D^3)^(-σ) = D^(-3*σ) := by
    rw [←Real.rpow_natCast_mul hD.le]
    congr 1
    norm_num
  have hr : (R^2)^(-σ) = (R^(2*σ))⁻¹ := by
    rw [←Real.rpow_natCast_mul hR.le,←Real.rpow_neg hR.le]
    congr 1
    norm_num
  rw [Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hX.le,
    Real.mul_rpow (by positivity) hP.le,
    Real.mul_rpow (by positivity) (pow_nonneg hD.le _),hb,hd,hr,
    div_eq_mul_inv,inv_inv]

lemma metaplectic_dual_scalar {A B D P R X : ℝ}
    (hB : 0 < B) (hD : 0 < D) (hP : 0 < P) (hR : 0 < R) (hX : 0 < X) (σ : ℝ) :
    A/(P*D^(5/2:ℝ))*((B^4*D^3*P*X)/R^2)^(-σ) =
      (B^(-4*σ)*X^(-σ)*R^(2*σ))*(A/P^(1+σ))*D^(-5/2-3*σ) := by
  have hp : P^(-σ)/P = (P^(1+σ))⁻¹ := by
    calc
      _ = P^(-σ)/P^(1:ℝ) := by rw [Real.rpow_one]
      _ = P^(-σ-1) := (Real.rpow_sub hP _ _).symm
      _ = P^(-(1+σ)) := by congr 1; ring
      _ = _ := Real.rpow_neg hP.le _
  have hd : D^(-3*σ)/D^(5/2:ℝ) = D^(-5/2-3*σ) := by
    rw [←Real.rpow_sub hD]
    congr 1
    ring
  rw [metaplectic_argument_power hB hD hP hR hX]
  calc
    _ = (B^(-4*σ)*X^(-σ)*R^(2*σ))*A*(P^(-σ)/P)*(D^(-3*σ)/D^(5/2:ℝ)) := by ring
    _ = _ := by rw [hp,hd]; ring

/-- The actual dual term has the separated coefficient/d-variable
majorant supplied by the published formula and the derived transform bound. -/
lemma metaplecticDualTerm_norm_le
    (a : Eisenstein → MetaplecticDualArgument → ℂ) {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) {σ X C : ℝ} (hX : 0 < X) (hC : 0 ≤ C)
    (hW : ∀ v : ℝ, 0 < v → ‖metaplecticTransform ℓ W σ v‖ ≤ C*v^(-σ))
    (nd : MetaplecticDualArgument × PrimaryArgument) :
    ‖metaplecticDualTerm a r ℓ W σ X nd‖ ≤
      (C*((2*Real.pi)^(-4*σ)*X^(-σ)*norm r^(2*σ)))*
        metaplecticCoefficientMassTerm a r σ nd.1*norm nd.2^(-5/2-3*σ) := by
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hD : 0 < norm nd.2 := norm_pos_of_ne_zero (primary_ne_zero nd.2.property)
  have hP : 0 < Complex.normSq (metaplecticFrequency nd.1) :=
    Complex.normSq_pos.mpr (metaplecticFrequency_ne_zero nd.1)
  have hB : 0 < 2*Real.pi := by positivity
  have hz : ((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (fun h => primary_ne_zero nd.2.property (Subtype.ext h)))
      (metaplecticFrequency_ne_zero nd.1)
  have hnorm : Complex.normSq (((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1) =
      norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1) := by
    rw [Complex.normSq_mul,map_pow]
    rfl
  unfold metaplecticDualTerm
  split_ifs
  · rw [norm_mul,norm_mul,norm_div,Complex.norm_real,
      Real.norm_of_nonneg (by positivity),norm_complexAngular hz,mul_one,hnorm]
    have hv : 0 < (2*Real.pi)^4*(norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1))*X/norm r^2 := by
      positivity
    apply (mul_le_mul_of_nonneg_left (hW _ hv) (by positivity)).trans_eq
    rw [mul_left_comm _ C,mul_assoc]
    have hs := metaplectic_dual_scalar (A := ‖a r nd.1*metaplecticLocalCoefficient r nd.1‖)
      hB hD hP hR hX σ
    change C*(_/(_*_) * _^(-σ)) = _
    rw [show (2*Real.pi)^4*(norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)*X)/norm r^2 =
      ((2*Real.pi)^4*norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)*X)/norm r^2 by ring,hs]
    unfold metaplecticCoefficientMassTerm
    ring
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity))
      (metaplecticCoefficientMassTerm_nonneg a r σ nd.1)) (Real.rpow_nonneg hD.le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticDualTailWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact exponent bookkeeping for truncating the metaplectic dual
series. The cutoff is in the actual norm N(d³ν). -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplecticDualNorm_pos (nd : MetaplecticDualArgument × PrimaryArgument) :
    0 < metaplecticDualNorm nd :=
  mul_pos (pow_pos (norm_pos_of_ne_zero (primary_ne_zero nd.2.property)) _)
    (Complex.normSq_pos.mpr (metaplecticFrequency_ne_zero nd.1))

lemma metaplectic_dual_weight_split
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein)
    (σ A : ℝ) (nd : MetaplecticDualArgument × PrimaryArgument) :
    metaplecticCoefficientMassTerm a r A nd.1*norm nd.2^(-5/2-3*A) =
      (metaplecticCoefficientMassTerm a r σ nd.1*norm nd.2^(-5/2-3*σ))*
        metaplecticDualNorm nd^(-(A-σ)) := by
  let D := norm nd.2
  let P := Complex.normSq (metaplecticFrequency nd.1)
  let H := ‖a r nd.1*metaplecticLocalCoefficient r nd.1‖
  have hD : 0 < D := norm_pos_of_ne_zero (primary_ne_zero nd.2.property)
  have hP : 0 < P := Complex.normSq_pos.mpr (metaplecticFrequency_ne_zero nd.1)
  change H/P^(1+A)*D^(-5/2-3*A) = (H/P^(1+σ)*D^(-5/2-3*σ))*(D^3*P)^(-(A-σ))
  have hpow : (D^3*P)^(-(A-σ)) = D^(-3*(A-σ))*P^(-(A-σ)) := by
    rw [Real.mul_rpow (pow_nonneg hD.le _) hP.le,←Real.rpow_natCast_mul hD.le]
    congr 2
    norm_num
    ring
  rw [hpow]
  have hPe : P^(-(1+A)) = P^(-(1+σ))*P^(-(A-σ)) := by
    rw [←Real.rpow_add hP]
    congr 1
    ring
  have hDe : D^(-5/2-3*A) = D^(-5/2-3*σ)*D^(-3*(A-σ)) := by
    rw [←Real.rpow_add hD]
    congr 1
    ring
  simp only [div_eq_mul_inv] at hDe
  simp only [div_eq_mul_inv,←Real.rpow_neg hP.le]
  rw [hPe,hDe]
  ring

lemma metaplectic_dual_weight_tail
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein)
    {σ A J : ℝ} (hA : σ ≤ A) (hJ : 0 < J)
    (nd : MetaplecticDualArgument × PrimaryArgument) (hcut : J ≤ metaplecticDualNorm nd) :
    metaplecticCoefficientMassTerm a r A nd.1*norm nd.2^(-5/2-3*A) ≤
      J^(-(A-σ))*(metaplecticCoefficientMassTerm a r σ nd.1*norm nd.2^(-5/2-3*σ)) := by
  rw [metaplectic_dual_weight_split]
  have hpow := Real.rpow_le_rpow_of_nonpos hJ hcut (show -(A-σ) ≤ 0 by linarith)
  have hn : 0 ≤ metaplecticCoefficientMassTerm a r σ nd.1*norm nd.2^(-5/2-3*σ) :=
    mul_nonneg (metaplecticCoefficientMassTerm_nonneg a r σ nd.1)
      (Real.rpow_nonneg (norm_nonneg nd.2) _)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hpow hn

/-- The tail costs the cutoff power while retaining only the already
summable small-line coefficient mass. -/
theorem metaplecticFarTail_norm_bound
    (a : Eisenstein → MetaplecticDualArgument → ℂ) {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) {σ A X J C M : ℝ}
    (hσ : 0 < σ) (hA : σ ≤ A) (hX : 0 < X) (hJ : 0 < J) (hC : 0 ≤ C)
    (hW : ∀ v : ℝ, 0 < v → ‖metaplecticTransform ℓ W A v‖ ≤ C*v^(-A))
    (hm : Summable (metaplecticCoefficientMassTerm a r σ))
    (hM : (∑' n, metaplecticCoefficientMassTerm a r σ n) ≤ M) :
    ‖∑' nd, metaplecticFarTailTerm a r ℓ W A X J nd‖ ≤
      (C*((2*Real.pi)^(-4*A)*X^(-A)*norm r^(2*A)))*J^(-(A-σ))*M*
        (∑' d : PrimaryArgument, norm d^(-5/2-3*σ)) := by
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  let K := C*((2*Real.pi)^(-4*A)*X^(-A)*norm r^(2*A))*J^(-(A-σ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let dweight : PrimaryArgument → ℝ := fun d => norm d^(-5/2-3*σ)
  have hd : Summable dweight := by
    dsimp only [dweight]
    convert primary_norm_rpow_summable (show 1 < 5/2+3*σ by linarith) using 1
    all_goals try with_reducible_and_instances rfl
    ext d
    congr 1
    ring
  have hd0 (d : PrimaryArgument) : 0 ≤ dweight d :=
    Real.rpow_nonneg (norm_nonneg d) _
  have hprod := hm.mul_of_nonneg hd (metaplecticCoefficientMassTerm_nonneg a r σ) hd0
  have hs := (hm.hasSum.mul hd.hasSum hprod).mul_left K
  have hb : ‖∑' nd, metaplecticFarTailTerm a r ℓ W A X J nd‖ ≤
      K*((∑' n, metaplecticCoefficientMassTerm a r σ n)*(∑' d, dweight d)) := by
    apply tsum_of_norm_bounded hs
    intro nd
    by_cases hcut : J < metaplecticDualNorm nd
    · simp only [metaplecticFarTailTerm,hcut,ite_true, if_true]
      have hn := metaplecticDualTerm_norm_le a hr ℓ W hX hC hW nd
      have ht := metaplectic_dual_weight_tail a r hA hJ nd hcut.le
      apply hn.trans
      calc
        _ = (C*((2*Real.pi)^(-4*A)*X^(-A)*norm r^(2*A)))*
            (metaplecticCoefficientMassTerm a r A nd.1*norm nd.2^(-5/2-3*A)) := by ring
        _ ≤ (C*((2*Real.pi)^(-4*A)*X^(-A)*norm r^(2*A)))*
            (J^(-(A-σ))*(metaplecticCoefficientMassTerm a r σ nd.1*norm nd.2^(-5/2-3*σ))) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
        _ = _ := by dsimp [K,dweight]; ring
    · simp only [metaplecticFarTailTerm,hcut,ite_false, if_false,norm_zero]
      exact mul_nonneg hK (mul_nonneg (metaplecticCoefficientMassTerm_nonneg a r σ nd.1) (hd0 nd.2))
  apply hb.trans
  calc
    _ ≤ K*(M*(∑' d, dweight d)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hM (tsum_nonneg hd0)) hK
    _ = _ := by dsimp [K,dweight]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTwistedTransform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm twist in the original Voronoi formula is exactly the
translated Mellin variable in the shifted transform. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma mellin_mul_phase (W : ℝ → ℂ) (s : ℂ) (t : ℝ) :
    mellin (fun x => W x*mellinPhase t x) s = mellin W (s+(t:ℂ)*Complex.I) := by
  calc
    _ = mellin (fun x => (x:ℂ)^((t:ℂ)*Complex.I) • W x) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [mellinPhase_eq_cpow hx t]
      simp only [smul_eq_mul]
      ring
    _ = _ := mellin_cpow_smul W s ((t:ℂ)*Complex.I)

/-- Exact scalar identity. Its outside phase has modulus one. -/
theorem metaplecticTransform_twisted (ℓ : ℤ) (W : ℝ → ℂ)
    (σ : ℝ) {v : ℝ} (hv : 0 < v) (t : ℝ) :
    metaplecticTransform ℓ (fun x => W x*mellinPhase t x) σ v =
      mellinPhase (-t) v*metaplecticShiftTransform ℓ W (-σ) v t := by
  let F : ℝ → ℂ := fun τ =>
    (v:ℂ)^(((-σ:ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ (((-σ:ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
      mellin W (((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)
  have he (τ : ℝ) :
      (v:ℂ)^(((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ (((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)*
        mellin (fun x => W x*mellinPhase t x) (((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I) = F (τ+t) := by
    rw [mellin_mul_phase]
    dsimp [F]
    have h1 : ((τ+t-t:ℝ):ℂ) = (τ:ℂ) := by push_cast; ring
    have h2 : ((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I+(t:ℂ)*Complex.I =
        ((-σ:ℝ):ℂ)+((τ+t:ℝ):ℂ)*Complex.I := by push_cast; ring
    rw [h1,h2]
  have hphase (τ : ℝ) : F τ = mellinPhase (-t) v*
      ((v:ℂ)^(((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ (((-σ:ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
        mellin W (((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)) := by
    rw [mellinPhase_eq_cpow hv]
    dsimp [F]
    have hs : (((-σ:ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
        (((-t:ℝ):ℂ)*Complex.I)+(((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I) := by push_cast; ring
    rw [hs,Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
    ring
  unfold metaplecticTransform metaplecticShiftTransform
  simp_rw [he]
  rw [integral_add_right_eq_self F t]
  simp_rw [hphase]
  rw [integral_const_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticShiftedVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The published small-line formula equals the actual far-left series.
Every contour change is proved for the literal transform before summing. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplecticDualNorm_eq (nd : MetaplecticDualArgument × PrimaryArgument) :
    Complex.normSq (((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1) =
      metaplecticDualNorm nd := by
  rw [Complex.normSq_mul,map_pow]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonCoefficientBound
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A sharp coordinate majorant for the actual three-cusp coefficient.
The ramified shift lowers its amplitude by three, exactly compensating
for the prefactor in the shifted-cusp expansion. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma CubicThetaCoordinates.coefficient_norm_le_amplitude_common {n : Eisenstein}
    (R : CubicThetaCoordinates n) : ‖R.coefficient‖≤R.amplitude := by
  unfold coefficient
  split_ifs
  · rw [norm_mul,norm_mul,norm_star,cubicThetaUnitPhase_norm,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
    exact mul_le_of_le_one_right R.amplitude_nonneg
      (cubicThetaTwistedGauss_norm_le R.squarefree_primary R.squarefree _)
  · rw [norm_mul,norm_star,norm_gauss_of_squarefree R.squarefree_primary R.squarefree,
      mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
  · simpa only [norm_zero] using R.amplitude_nonneg

lemma cubicThetaArithmetic_coordinate_bound (e : Eisensteinˣ) (k : ℕ)
    {c d : Eisenstein} (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    ‖cubicThetaArithmeticCoefficient ((e:Eisenstein)*lambdaE^k*(c*d^3))‖≤
      3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d) := by
  let R : CubicThetaCoordinates ((e:Eisenstein)*lambdaE^k*(c*d^3)) := {
    unit := e
    order := k
    squarefreePart := c
    cubePart := d
    squarefree_primary := hc
    cube_primary := hd
    squarefree := hs
    numerator_eq := rfl }
  rw [cubicThetaArithmeticCoefficient_formula R]
  exact R.coefficient_norm_le_amplitude_common

lemma cubicTheta_coordinate_shift_amplitude (k : ℕ) :
    (3:ℝ)*3^(4-(((k+3)/3:ℕ):ℝ))=3^(4-((k/3:ℕ):ℝ)) := by
  have he : (k+3)/3=k/3+1 := by omega
  rw [he]
  push_cast
  rw [show (4-(((k/3:ℕ):ℝ)+1))=(4-((k/3:ℕ):ℝ))-1 by ring]
  rw [Real.rpow_sub (by norm_num : (0:ℝ)<3),Real.rpow_one]
  ring

theorem cubicThetaCommon_coordinate_bound (e : Eisensteinˣ) (k : ℕ)
    {c d : Eisenstein} (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    ‖cubicThetaCommonCuspCoefficient ((e:Eisenstein)*lambdaE^k*(c*d^3))‖≤
      3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d) := by
  let A : ℝ := 3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d)
  have hA : 0≤A := div_nonneg (by positivity)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hb : ‖cubicThetaArithmeticCoefficient (-((e:Eisenstein)*lambdaE^k*(c*d^3)))‖≤A := by
    simpa only [Units.val_neg,neg_mul,A] using
      cubicThetaArithmetic_coordinate_bound (-e) k hc hd hs
  have ht : 3*‖cubicThetaArithmeticCoefficient
      (3*(lambdaE*(-((e:Eisenstein)*lambdaE^k*(c*d^3)))))‖≤A := by
    have he : 3*(lambdaE*(-((e:Eisenstein)*lambdaE^k*(c*d^3))))=
        (e:Eisenstein)*lambdaE^(k+3)*(c*d^3) := by
      have hLam : lambdaE^3= -3*lambdaE := by
        calc
          _ = lambdaE^2*lambdaE := by ring
          _ = _ := by rw [lambdaE_sq]
      rw [pow_add,hLam]
      ring
    rw [he]
    calc
      _ ≤ 3*(3^(4-(((k+3)/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d)) :=
        mul_le_mul_of_nonneg_left (cubicThetaArithmetic_coordinate_bound e (k+3) hc hd hs)
          (by norm_num)
      _ = A := by rw [←mul_div_assoc,cubicTheta_coordinate_shift_amplitude]
  have hb' (j : ℤ) :
      ‖cubicThetaActualCuspCoefficient j (-((e:Eisenstein)*lambdaE^k*(c*d^3)))‖≤A := by
    unfold cubicThetaActualCuspCoefficient
    split_ifs
    · exact hb
    · unfold cubicThetaShiftedLatticeCoefficient
      split_ifs
      · simpa only [norm_mul,Complex.norm_ofNat] using ht
      · simpa only [norm_zero] using hA
  have hw (j : Fin 3) : ‖omega^j.val‖=1 := by
    have ho : ‖omega‖=1 := by
      have h := cubicTheta_unit_norm
        (Units.mkOfMulEqOne omegaE (omegaE^2) (by rw [mul_comm,←pow_succ,omegaE_cube]))
      exact h
    rw [norm_pow,ho,one_pow]
  unfold cubicThetaCommonCuspCoefficient
  rw [norm_div,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<3)).mpr
  calc
    _ ≤ ∑ j : Fin 3, ‖omega^j.val*
        star (cubicThetaActualCuspCoefficient (j.val:ℤ)
          (-((e:Eisenstein)*lambdaE^k*(c*d^3))))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, A := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,norm_star,hw,one_mul]
      exact hb' _
    _ = A*3 := by simp [mul_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonTauBound
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual unnormalized dual coefficient has the ramified growth and
square-root cube-factor bound required for the local summation formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_coordinate_norm (e : Eisensteinˣ) (k : ℕ) (c d : Eisenstein) :
    ‖cubicThetaFrequency ((e:Eisenstein)*lambdaE^k*(c*d^3))‖=
      (Real.sqrt 3)^k*Real.sqrt (norm c)*(Real.sqrt (norm d))^3/9 := by
  have hr (a : Eisenstein) : Real.sqrt (norm a)=‖(a:ℂ)‖ := by
    rw [norm,Complex.normSq_eq_norm_sq,Real.sqrt_sq (_root_.norm_nonneg _)]
  have hl : Real.sqrt (norm lambdaE)=Real.sqrt 3 := by
    rw [norm,lambdaE_coe,traceLambda_normSq]
  rw [cubicThetaFrequency_div_nine,norm_div,Complex.norm_ofNat]
  simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,norm_mul,norm_pow,
    cubicTheta_unit_norm,one_mul]
  rw [←hr lambdaE,←hr c,←hr d,hl]
  ring

lemma cubicTheta_coordinate_amplitude_product (k : ℕ) {c d : Eisenstein}
    (hc : primary c) (hd : primary d) :
    ((Real.sqrt 3)^k*Real.sqrt (norm c)*(Real.sqrt (norm d))^3/9)*
      (3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d))=
        9*3^((k:ℝ)/2-((k/3:ℕ):ℝ))*Real.sqrt (norm d) := by
  have hc0 := (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hc))).ne'
  have hd0 := (norm_pos_of_ne_zero (primary_ne_zero hd)).ne'
  have hp : (Real.sqrt 3)^k*3^(4-((k/3:ℕ):ℝ))/9=
      9*3^((k:ℝ)/2-((k/3:ℕ):ℝ)) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3),
      ←Real.rpow_add (by norm_num : (0:ℝ)<3)]
    calc
      _ = 3^((1/2:ℝ)*k+(4-((k/3:ℕ):ℝ)))/3^(2:ℝ) := by rw [Real.rpow_two]; norm_num
      _ = 3^((1/2:ℝ)*k+(4-((k/3:ℕ):ℝ))-2) :=
        (Real.rpow_sub (by norm_num : (0:ℝ)<3) _ _).symm
      _ = _ := by
        rw [show (1/2:ℝ)*k+(4-((k/3:ℕ):ℝ))-2=
          2+((k:ℝ)/2-((k/3:ℕ):ℝ)) by ring,
          Real.rpow_add (by norm_num : (0:ℝ)<3),Real.rpow_two]
        norm_num
  calc
    _ = ((Real.sqrt 3)^k*3^(4-((k/3:ℕ):ℝ))/9)*Real.sqrt (norm d) := by
      field_simp
      rw [show (Real.sqrt (norm d))^3=Real.sqrt (norm d)*(Real.sqrt (norm d))^2 by ring,
        Real.sq_sqrt (norm_nonneg d)]
    _ = _ := by rw [hp]

lemma cubicTheta_ramified_growth_exponent (k : ℕ) :
    (k:ℝ)/2-((k/3:ℕ):ℝ) ≤ ((max ((k:ℤ)-1) 0:ℤ):ℝ)/3+1 := by
  have hq : k≤3*(k/3)+2 := by omega
  have hq' : (k:ℝ)≤3*((k/3:ℕ):ℝ)+2 := by exact_mod_cast hq
  have hm : (k:ℝ)-1≤((max ((k:ℤ)-1) 0:ℤ):ℝ) := by
    exact_mod_cast (le_max_left ((k:ℤ)-1) 0)
  have hk : 0≤(k:ℝ) := Nat.cast_nonneg k
  linarith

theorem cubicThetaCommonTau_coordinate_bound (e : Eisensteinˣ) (k : ℕ)
    {c d : Eisenstein} (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    ‖cubicThetaCommonTau ((e:Eisenstein)*lambdaE^k*(c*d^3))‖≤
      27*3^(((max ((k:ℤ)-1) 0:ℤ):ℝ)/3)*Real.sqrt (norm d) := by
  unfold cubicThetaCommonTau
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]
  calc
    _ ≤ ‖cubicThetaFrequency ((e:Eisenstein)*lambdaE^k*(c*d^3))‖*
        (3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d)) :=
      mul_le_mul_of_nonneg_left (cubicThetaCommon_coordinate_bound e k hc hd hs)
        (_root_.norm_nonneg _)
    _ = 9*3^((k:ℝ)/2-((k/3:ℕ):ℝ))*Real.sqrt (norm d) := by
      rw [cubicThetaFrequency_coordinate_norm,cubicTheta_coordinate_amplitude_product k hc hd]
    _ ≤ 9*3^(((max ((k:ℤ)-1) 0:ℤ):ℝ)/3+1)*Real.sqrt (norm d) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
            (cubicTheta_ramified_growth_exponent k)) (by norm_num))
        (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<3),Real.rpow_one]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreCoefficient
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete dual coefficient after free-cube removal. Its support
and the required ramified coefficient bound are proved from the actual
three-cusp arithmetic formulas. The summation identity is separate. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma CubicThetaCoordinates.metaplectic_frequency {n : Eisenstein}
    (R : CubicThetaCoordinates n) (hn : n≠0) :
    metaplecticFrequency ⟨n,hn⟩=traceLambda^((R.order:ℤ)-1)*(R.unit:Eisenstein)*
      (R.squarefreePart:ℂ)*(R.cubePart:ℂ)^3 := by
  have hp : traceLambda^((R.order:ℤ)-1)*traceLambda=traceLambda^R.order := by
    calc
      _ = traceLambda^((R.order:ℤ)-1)*traceLambda^(1:ℤ) := by rw [zpow_one]
      _ = _ := by rw [←zpow_add₀ traceLambda_ne_zero,sub_add_cancel,zpow_natCast]
  apply mul_right_cancel₀ traceLambda_ne_zero
  rw [metaplecticFrequency,div_mul_cancel₀ _ traceLambda_ne_zero]
  calc
    _ = (R.unit:Eisenstein)*traceLambda^R.order*
        (R.squarefreePart:ℂ)*(R.cubePart:ℂ)^3 := by
      change (n:ℂ)=_
      conv_lhs => rw [R.numerator_eq]
      push_cast
      rw [lambdaE_coe]
      ring
    _ = _ := by rw [←hp]; ring

theorem cubicThetaCoreCoefficient_bounds :
    MetaplecticCoefficientBounds cubicThetaCoreCoefficient := by
  refine ⟨27,by norm_num,?_⟩
  intro r hr _hs n hne
  have hs : CubicThetaCoreSupport r n := by
    by_contra h
    simp only [cubicThetaCoreCoefficient,ite_eq_right h,zero_mul,ne_eq,not_true_eq_false] at hne
  obtain ⟨R,k,hk⟩ := hs
  let h := primarySmallPart r R.squarefreePart
  let w := primaryOutsidePart r R.squarefreePart
  have hh : primary h := primarySmallPart_primary r R.squarefree_primary
  have hw : primary w := primaryOutsidePart_primary r R.squarefree_primary
  have hc : h*w=R.squarefreePart := primary_small_outside_mul r R.squarefree_primary
  refine ⟨(R.order:ℤ)-1,R.unit,h,R.cubePart,w,by omega,hh,R.cube_primary,hw,
    cubicTheta_primarySmallPart_supported (primary_ne_zero hr) R.squarefree_primary,
    ⟨k,hk⟩,primaryOutsidePart_coprime R.squarefree_primary (primary_ne_zero hr),?_,?_,?_⟩
  · rw [hc]
    exact R.squarefree
  · have he := R.metaplectic_frequency n.property
    rw [←hc] at he
    simpa only [Subalgebra.coe_mul,mul_assoc] using he
  · rw [cubicThetaCoreCoefficient,ite_eq_left ⟨R,k,hk⟩]
    conv_lhs => rw [R.numerator_eq]
    exact cubicThetaCommonTau_coordinate_bound R.unit R.order R.squarefree_primary
      R.cube_primary R.squarefree

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticSupportedSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported primary factors in the retained metaplectic sum have
convergent weighted Euler products with arbitrarily small level loss. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The exponent δ of the convergent supported sum is fixed independently
of the arbitrarily small loss ε in the level. -/
theorem primary_supported_norm_sum {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      ∀ (S : Finset Eisenstein) (J : ℝ), (∀ b ∈ S, primary b) →
      (∀ b ∈ S, ∃ k : ℕ, b ∣ r^k) → (∀ b ∈ S, norm b ≤ J) →
      (∑ b ∈ S, norm b^(-δ)) ≤ C*norm r^ε := by
  let η := min ε δ
  have hη : 0 < η := lt_min hε hδ
  obtain ⟨C,hC,hEuler⟩ := supported_euler_small_power hη
  refine ⟨C,hC,?_⟩
  intro r hr S J hS hsupport hJ
  let T := S.image idealExponentOf
  have hT : ∀ ν ∈ T, ν.support ⊆ (idealExponentOf r).support ∧ idealExponentNorm ν ≤ J := by
    intro ν hν
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hν
    refine ⟨idealExponent_support_of_dvd_power (primary_ne_zero (hS b hb))
      (primary_ne_zero hr) (hsupport b hb),?_⟩
    rw [idealExponentOf_norm (primary_ne_zero (hS b hb))]
    exact hJ b hb
  have hs := ideal_supported_rankin_sum hη (idealExponentOf r).support T hT
  have he : (∑ ν ∈ T, idealExponentNorm ν^(-η)) = ∑ b ∈ S, norm b^(-η) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro b hb
      rw [idealExponentOf_norm (primary_ne_zero (hS b hb))]
    · intro b hb c hc hbc
      exact primary_eq_of_idealExponentOf_eq (hS b hb) (hS c hc) hbc
  rw [he] at hs
  calc
    _ ≤ ∑ b ∈ S, norm b^(-η) := by
      apply Finset.sum_le_sum
      intro b hb
      exact Real.rpow_le_rpow_of_exponent_le (one_le_norm (primary_ne_zero (hS b hb)))
        (neg_le_neg (min_le_right ε δ))
    _ ≤ ∏ p ∈ (idealExponentOf r).support,
        (1-(normNat (idealPrimeRepresentative p):ℝ)^(-η))⁻¹ := hs
    _ ≤ C*idealExponentNorm (idealExponentOf r)^η := hEuler (idealExponentOf r)
    _ = C*norm r^η := by rw [idealExponentOf_norm (primary_ne_zero hr)]
    _ ≤ C*norm r^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (one_le_norm (primary_ne_zero hr)) (min_le_left ε δ)) hC.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCommonBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two complementary common-factor bounds in each retained
metaplectic block. Both come from actual divisibility. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticCommonNorm_le_level {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) : metaplecticCommonNorm r n ≤ norm r := by
  let S := (primaryPrimeFactors r).filter (fun p => p ∣ n.val)
  have hsub : S ⊆ primaryPrimeFactors r := Finset.filter_subset _ _
  have hdiv : (∏ p ∈ S, p) ∣ r := (primary_subsets_prod_dvd hr hsub r).mpr (by
    intro p hp
    exact (primaryPrimeFactor_spec hr (hsub hp)).2)
  have he : metaplecticCommonNorm r n = norm (∏ p ∈ S, p) := by
    rw [norm_finset_prod]
    rfl
  rw [he]
  exact norm_le_of_dvd (primary_ne_zero hr) hdiv

lemma metaplectic_actual_coefficient_common_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {r : Eisenstein} (hr : primary r) (n : MetaplecticDualArgument)
    {j : ℤ} {h' : Eisenstein} (ha : ‖a r n‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')) :
    ‖a r n*metaplecticLocalCoefficient r n‖ ≤
      C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*metaplecticCommonNorm r n := by
  rw [norm_mul]
  exact mul_le_mul ha (norm_metaplecticLocalCoefficient_le hr n)
    (_root_.norm_nonneg _) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticFreeMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free primary variable in each retained metaplectic support block
has inverse-square-root coefficients. Its actual energy and rational norm
multiplicity give the ordinary mean-value bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_free_dyad_energy (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b) (v : Eisenstein → ℂ) {L K : ℝ} (hL : 0 < L)
    (hsize : ∀ b ∈ S, L/2 ≤ norm b ∧ norm b ≤ L)
    (hv : ∀ b ∈ S, ‖v b‖^2 ≤ K^2/norm b) :
    (∑ b ∈ S, ‖v b‖^2) ≤ 36*K^2 := by
  have hsub : S ⊆ nonzeroNormBall L := by
    intro b hb
    exact mem_nonzeroNormBall.mpr ⟨(hsize b hb).2,primary_ne_zero (hS b hb)⟩
  have hcard : (S.card:ℝ) ≤ 18*L :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hL.le)
  have hterm (b : Eisenstein) (hb : b ∈ S) : ‖v b‖^2 ≤ 2*K^2/L := by
    apply (hv b hb).trans
    calc
      _ ≤ K^2/(L/2) := div_le_div_of_nonneg_left (sq_nonneg K) (half_pos hL) (hsize b hb).1
      _ = _ := by field_simp [hL.ne']
  calc
    _ ≤ ∑ b ∈ S, 2*K^2/L := Finset.sum_le_sum hterm
    _ = (S.card:ℝ)*(2*K^2/L) := by simp
    _ ≤ (18*L)*(2*K^2/L) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp [hL.ne']; ring

/-- The actual free-primary dyad mean; the only analytic input is MV. -/
theorem metaplectic_free_meanAbsolute_sq {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S : Finset Eisenstein), (∀ b ∈ S, primary b) →
      ∀ (v : Eisenstein → ℂ) (L K T u : ℝ) (ℓ : ℤ),
      1 ≤ L → 0 < T → (∀ b ∈ S, L/2 ≤ norm b ∧ norm b ≤ L) →
      (∀ b ∈ S, ‖v b‖^2 ≤ K^2/norm b) →
      ((∫ t in T..2*T, ‖∑ b ∈ S, v b*theta ℓ b*mellinPhase (t+u) (norm b)‖)/T)^2 ≤
        C*D*(1+2*L/T)*L^ε*K^2 := by
  obtain ⟨D,hD,hfiber⟩ := primary_norm_fiber_length_bound hε
  refine ⟨36*D*2^ε,by positivity,?_⟩
  intro S hS v L K T u ℓ hL hT hsize hv
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hN (b : Eisenstein) (hb : b ∈ S) : normNat b ∈ Finset.Icc 1 ⌈L⌉₊ := by
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast (show (1:ℝ) ≤ (normNat b:ℝ) by
        rw [normNat_cast]
        exact one_le_norm (primary_ne_zero (hS b hb)))
    · have hh : (normNat b:ℝ) ≤ (⌈L⌉₊:ℝ) := by
        rw [normNat_cast]
        exact (hsize b hb).2.trans (Nat.le_ceil L)
      exact_mod_cast hh
  have he := metaplectic_free_dyad_energy S hS v hLp hsize hv
  have hm := fixedAngular_translated_meanAbsolute_sq hMV hC S v ⌈L⌉₊
    (D*(⌈L⌉₊:ℝ)^ε) hN (fun b hb => primary_ne_zero (hS b hb))
    (hfiber S hS ⌈L⌉₊) ℓ u hT
  have hceil : (⌈L⌉₊:ℝ) ≤ 2*L := by linarith [Nat.ceil_lt_add_one hLp.le]
  have hc : (⌈L⌉₊:ℝ)^ε ≤ (2*L)^ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hceil hε.le
  have hf : 1+(⌈L⌉₊:ℝ)/T ≤ 1+2*L/T := by
    linarith [div_le_div_of_nonneg_right hceil hT.le]
  calc
    _ ≤ C*(1+(⌈L⌉₊:ℝ)/T)*(D*(⌈L⌉₊:ℝ)^ε)*(36*K^2) :=
      hm.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ ≤ C*(1+2*L/T)*(D*(2*L)^ε)*(36*K^2) := by gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num) hLp.le]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticFreeBlock
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed supported parameters only rescale the positive rational
frequencies of the free primary polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_scaled_free_norm (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b) (v : Eisenstein → ℂ)
    {c : ℝ} (hc : 0 < c) (ℓ : ℤ) (t : ℝ) :
    ‖∑ b ∈ S, v b*theta ℓ b*mellinPhase t (c*norm b)‖ =
      ‖∑ b ∈ S, v b*theta ℓ b*mellinPhase t (norm b)‖ := by
  have he : (∑ b ∈ S, v b*theta ℓ b*mellinPhase t (c*norm b)) =
      mellinPhase t c*(∑ b ∈ S, v b*theta ℓ b*mellinPhase t (norm b)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [mellinPhase_mul_pos t hc (norm_pos_of_ne_zero (primary_ne_zero (hS b hb)))]
    ring
  rw [he,norm_mul,mellinPhase_norm,one_mul]

theorem metaplectic_scaled_free_meanAbsolute {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S : Finset Eisenstein), (∀ b ∈ S, primary b) →
      ∀ (v : Eisenstein → ℂ) (L K T u c : ℝ) (ℓ : ℤ),
      1 ≤ L → 0 ≤ K → 0 < T → 0 < c →
      (∀ b ∈ S, L/2 ≤ norm b ∧ norm b ≤ L) →
      (∀ b ∈ S, ‖v b‖^2 ≤ K^2/norm b) →
      (∫ t in T..2*T, ‖∑ b ∈ S, v b*theta ℓ b*mellinPhase (t+u) (c*norm b)‖)/T ≤
        Real.sqrt (C*D)*L^(ε/2)*K*(1+Real.sqrt (2*L/T)) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_free_meanAbsolute_sq hε hMV hC
  refine ⟨D,hD,?_⟩
  intro S hS v L K T u c ℓ hL hK hT hc hsize hv
  simp_rw [metaplectic_scaled_free_norm S hS v hc]
  have hb := hbound S hS v L K T u ℓ hL hT hsize hv
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hq : 0 ≤ 2*L/T := div_nonneg (by positivity) hT.le
  have hpow : (L^(ε/2))^2 = L^ε := by
    rw [←Real.rpow_mul_natCast hLp.le]
    congr 1
    norm_num
  have hs : (Real.sqrt (C*D)*L^(ε/2)*K)^2 = C*D*L^ε*K^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hC hD.le),hpow]
  have hroot : 1+2*L/T ≤ (1+Real.sqrt (2*L/T))^2 := by
    nlinarith [Real.sq_sqrt hq,Real.sqrt_nonneg (2*L/T)]
  apply le_of_sq_le_sq _ (by positivity)
  apply hb.trans
  rw [mul_pow,hs]
  calc
    _ = (C*D*L^ε*K^2)*(1+2*L/T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hroot (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticBlockCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual critical-line coefficients of a retained Voronoi block.
The free-variable inverse-square-root bound follows from the published
coefficient support and the two proved common-divisor bounds. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_metaplecticNormalizedDualCoefficient_le
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument) :
    ‖metaplecticNormalizedDualCoefficient a r ℓ nd‖ ≤
      ‖a r nd.1*metaplecticLocalCoefficient r nd.1‖/
        (Real.sqrt (Complex.normSq (metaplecticFrequency nd.1))*norm nd.2) := by
  have hD := norm_pos_of_ne_zero (primary_ne_zero nd.2.property)
  have hz : ((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (fun h => primary_ne_zero nd.2.property (Subtype.ext h)))
      (metaplecticFrequency_ne_zero nd.1)
  unfold metaplecticNormalizedDualCoefficient
  split_ifs
  · rw [norm_mul,norm_div,norm_complexAngular hz, mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  · rw [norm_zero]
    positivity

lemma metaplectic_free_coefficient_sq {A c B D : ℝ}
    (_hA : 0 ≤ A) (hc : 0 < c) (hB : 0 < B) (_hD : 0 < D)
    {z : ℂ} (hz : ‖z‖ ≤ A/(Real.sqrt (c*B)*D)) :
    ‖z‖^2 ≤ (A/(Real.sqrt c*D))^2/B := by
  apply (pow_le_pow_left₀ (_root_.norm_nonneg _) hz 2).trans_eq
  rw [div_pow,mul_pow,Real.sq_sqrt (by positivity),div_pow,mul_pow,
    Real.sq_sqrt hc.le]
  ring

/-- All dependence on the free primary element has been extracted as
its inverse square root. The coefficient is the actual Voronoi one. -/
lemma metaplectic_actual_free_coefficient_sq
    {a : Eisenstein → MetaplecticDualArgument → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {r : Eisenstein} (hr : primary r) (d : PrimaryArgument) (ℓ : ℤ)
    (n : MetaplecticDualArgument) {j : ℤ} (hj : -1 ≤ j) (ζ : Eisensteinˣ)
    {h h' w : Eisenstein} (hh : primary h) (hh' : primary h') (hw : primary w)
    (hwr : IsCoprime w r)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3)
    (ha : ‖a r n‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')) :
    ‖metaplecticNormalizedDualCoefficient a r ℓ (n,d)‖^2 ≤
      (C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*
        min (norm r) (norm h*norm h') /
        (Real.sqrt ((3:ℝ)^((j+1).toNat-1:ℝ)*norm h*norm h'^3)*norm d))^2/norm w := by
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hH := norm_pos_of_ne_zero (primary_ne_zero hh)
  have hP := norm_pos_of_ne_zero (primary_ne_zero hh')
  have hW := norm_pos_of_ne_zero (primary_ne_zero hw)
  have hD := norm_pos_of_ne_zero (primary_ne_zero d.property)
  have hg := le_min (metaplecticCommonNorm_le_level hr n)
    (metaplecticCommonNorm_le_supported hr n (j+1).toNat ζ hh hh' hwr
      (metaplectic_numerator_of_frequency n hj ζ h h' w he))
  have hc := metaplectic_actual_coefficient_common_bound hC hr n ha
  have hb : ‖a r n*metaplecticLocalCoefficient r n‖ ≤
      C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*min (norm r) (norm h*norm h') :=
    hc.trans (mul_le_mul_of_nonneg_left hg (by positivity))
  have hn := metaplectic_frequency_norm n (j+1).toNat ζ h h' w
    (metaplectic_numerator_of_frequency n hj ζ h h' w he)
  have hn' : Complex.normSq (metaplecticFrequency n) =
      ((3:ℝ)^((j+1).toNat-1:ℝ)*norm h*norm h'^3)*norm w := by
    rw [hn]
    ring
  apply metaplectic_free_coefficient_sq (by positivity) (by positivity) hW hD
  apply (norm_metaplecticNormalizedDualCoefficient_le a r ℓ (n,d)).trans
  rw [hn']
  exact div_le_div_of_nonneg_right hb (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCriticalKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At the critical line the angular Gamma quotient has modulus one.
Thus the actual translated Mellin kernel has one common integrable
weight, independent of height and of the retained frequency polynomial. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma continuous_metaplecticGamma_half (ℓ : ℤ) :
    Continuous (fun t : ℝ => metaplecticGammaQuotient ℓ ((1/2:ℂ)+(t:ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hopen : IsOpen {s : ℂ | s.re < 5/6} := isOpen_lt Complex.continuous_re continuous_const
  have hmem : (1/2:ℂ)+(t:ℂ)*Complex.I ∈ {s : ℂ | s.re < 5/6} := by
    change ((1/2:ℂ)+(t:ℂ)*Complex.I).re < 5/6
    norm_num
  have hg : ContinuousAt (fun u : ℝ => (1/2:ℂ)+(u:ℂ)*Complex.I) t := by fun_prop
  exact ((differentiableOn_metaplecticGammaQuotient ℓ).differentiableAt
    (hopen.mem_nhds hmem)).continuousAt.comp
    (f := fun u : ℝ => (1/2:ℂ)+(u:ℂ)*Complex.I) hg

lemma norm_metaplecticCriticalKernel (ℓ : ℤ) (W : ℝ → ℂ) (c : ℝ)
    (P : ℝ → ℂ) (τ t : ℝ) :
    ‖metaplecticCriticalKernel ℓ W c P τ t‖ =
      ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖*‖P (τ-t)‖ := by
  simp only [metaplecticCriticalKernel,norm_mul,norm_metaplecticGamma_half,
    mellinPhase_norm,mul_one]

lemma continuous_metaplecticCriticalKernel (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (c : ℝ) {P : ℝ → ℂ} (hP : Continuous P) :
    Continuous (fun z : ℝ × ℝ => metaplecticCriticalKernel ℓ W c P z.1 z.2) := by
  have hm := (smooth_mellin_entire W hW hpos hsm.continuous).continuous
  have hg := (continuous_metaplecticGamma_half ℓ).comp
    (continuous_fst.sub continuous_snd)
  have hp : Continuous (fun z : ℝ × ℝ => mellinPhase (z.1-z.2) c) := by
    unfold mellinPhase
    fun_prop
  exact (((hm.comp (by fun_prop)).mul hg).mul hp).mul
    (hP.comp (continuous_fst.sub continuous_snd))

lemma metaplectic_mellin_half_integrable (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    Integrable (fun τ : ℝ => mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)) := by
  convert ((mellinVerticalSchwartz W hW hpos hsm (1/2)).integrable (μ := volume)) using 1
  all_goals try with_reducible_and_instances rfl
  ext τ
  rw [mellinVerticalSchwartz_apply]
  norm_num

lemma metaplecticCriticalKernel_integrable (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (c : ℝ) {P : ℝ → ℂ} (hP : Continuous P)
    {B : ℝ} (hB : ∀ u, ‖P u‖ ≤ B) (t : ℝ) :
    Integrable (fun τ : ℝ => metaplecticCriticalKernel ℓ W c P τ t) := by
  have hx : Continuous (fun τ : ℝ => (τ,t)) := continuous_id.prodMk continuous_const
  have hc := Continuous.comp
    (f := fun τ : ℝ => (τ,t))
    (g := fun z : ℝ × ℝ => metaplecticCriticalKernel ℓ W c P z.1 z.2)
    (continuous_metaplecticCriticalKernel ℓ W hW hpos hsm c hP) hx
  apply ((metaplectic_mellin_half_integrable W hW hpos hsm).norm.mul_const B).mono'
    hc.aestronglyMeasurable
  filter_upwards with τ
  dsimp only [Function.comp_def]
  rw [norm_metaplecticCriticalKernel]
  exact mul_le_mul_of_nonneg_left (hB (τ-t)) (_root_.norm_nonneg _)

/-- A uniform translated polynomial mean passes through the literal
critical-line Gamma kernel with the L1 mass of the actual Mellin transform. -/
theorem metaplectic_critical_kernel_mean (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (c : ℝ) (P : ℝ → ℂ) (hP : Continuous P)
    {T B : ℝ} (hT : 0 < T)
    (hmean : ∀ τ : ℝ, (∫ t in T..2*T, ‖P (τ-t)‖)/T ≤ B) :
    (∫ t in T..2*T, ‖∫ τ : ℝ, metaplecticCriticalKernel ℓ W c P τ t‖)/T ≤
      B*(∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) := by
  have hm := (metaplectic_mellin_half_integrable W hW hpos hsm).norm
  have hb (τ : ℝ) :
      (∫ t in T..2*T, ‖metaplecticCriticalKernel ℓ W c P τ t‖) ≤
        (B*T)*‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖ := by
    simp_rw [norm_metaplecticCriticalKernel]
    rw [intervalIntegral.integral_const_mul]
    calc
      _ ≤ ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖*(B*T) :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hT).mp (hmean τ)) (_root_.norm_nonneg _)
      _ = _ := by ring
  have hi := integral_height_norm_le
    (fun z => metaplecticCriticalKernel ℓ W c P z.1 z.2)
    (continuous_metaplecticCriticalKernel ℓ W hW hpos hsm c hP)
    (show T ≤ 2*T by linarith)
    (fun τ => (B*T)*‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖)
    (hm.const_mul (B*T)) hb
  rw [integral_const_mul] at hi
  apply (div_le_iff₀ hT).mpr
  nlinarith only [hi]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCriticalTransform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Move each finite retained transform to the critical line before
summing. The Mellin weight is translated back to one fixed function. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem metaplecticTransform_critical (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {A v : ℝ} (hA : 0 ≤ A) (hv : 0 < v)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A))
    (t : ℝ) :
    metaplecticTransform ℓ (fun x => W x*mellinPhase t x) A v =
      (Real.sqrt v:ℂ)*((1/(2*Real.pi):ℝ):ℂ)*
        ∫ τ : ℝ, metaplecticCriticalKernel ℓ W v (fun _ => 1) τ t := by
  have hc := metaplectic_transform_contour ℓ (fun x => W x*mellinPhase t x)
    (phaseWeight_compact hW t) (phaseWeight_positive hpos t)
    (phaseWeight_smooth hpos hsm t) (a := -A) (b := 1/2)
    (by linarith) le_rfl hv hm hp
  let F : ℝ → ℂ := fun τ =>
    (v:ℂ)^((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
      mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)
  have he (τ : ℝ) :
      (v:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
        mellin (fun x => W x*mellinPhase t x) ((1/2:ℂ)+(τ:ℂ)*Complex.I) = F (τ+t) := by
    rw [mellin_mul_phase]
    dsimp [F]
    have h1 : ((τ+t-t:ℝ):ℂ) = (τ:ℂ) := by push_cast; ring
    have h2 : (1/2:ℂ)+(τ:ℂ)*Complex.I+(t:ℂ)*Complex.I =
        (1/2:ℂ)+((τ+t:ℝ):ℂ)*Complex.I := by push_cast; ring
    rw [h1,h2]
  have hf (τ : ℝ) : F τ = (Real.sqrt v:ℂ)*
      metaplecticCriticalKernel ℓ W v (fun _ => 1) τ t := by
    dsimp [F,metaplecticCriticalKernel]
    rw [hecke_scale_phase hv]
    ring
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hc
  unfold metaplecticTransform
  rw [hc]
  simp_rw [he]
  rw [integral_add_right_eq_self F t]
  simp_rw [hf]
  rw [integral_const_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCriticalFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact extraction of the common critical-line kernel from a finite
retained frequency sum. No common-majorant hypothesis is introduced. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem metaplectic_finite_transform_critical {ι : Type*} (S : Finset ι)
    (b : ι → ℂ) (q : ι → ℝ) (hq : ∀ i ∈ S, 0 < q i)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A))
    (t : ℝ) :
    (∑ i ∈ S, b i*metaplecticTransform ℓ (fun x => W x*mellinPhase t x) A (c*q i)) =
      (Real.sqrt c:ℂ)*((1/(2*Real.pi):ℝ):ℂ)*
        ∫ τ : ℝ, metaplecticCriticalKernel ℓ W c
          (fun u => ∑ i ∈ S, b i*(Real.sqrt (q i):ℂ)*mellinPhase u (q i)) τ t := by
  let F : ι → ℝ → ℂ := fun i τ => b i*(Real.sqrt (c*q i):ℂ)*
    metaplecticCriticalKernel ℓ W (c*q i) (fun _ => 1) τ t
  have hF (i : ι) (_hi : i ∈ S) : Integrable (F i) := by
    exact (metaplecticCriticalKernel_integrable ℓ W hW hpos hsm (c*q i)
      (P := fun _ => 1) continuous_const (B := 1) (by intro u; norm_num) t).const_mul _
  have ht (i : ι) (hi : i ∈ S) :
      b i*metaplecticTransform ℓ (fun x => W x*mellinPhase t x) A (c*q i) =
        ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ, F i τ := by
    rw [metaplecticTransform_critical ℓ W hW hpos hsm hA (mul_pos hc (hq i hi)) hm hp t]
    dsimp [F]
    rw [integral_const_mul]
    ring
  have hf (τ : ℝ) : (∑ i ∈ S, F i τ) =
      (Real.sqrt c:ℂ)*metaplecticCriticalKernel ℓ W c
        (fun u => ∑ i ∈ S, b i*(Real.sqrt (q i):ℂ)*mellinPhase u (q i)) τ t := by
    unfold metaplecticCriticalKernel
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [F,metaplecticCriticalKernel]
    rw [Real.sqrt_mul hc.le,Complex.ofReal_mul,
      mellinPhase_mul_pos (τ-t) hc (hq i hi)]
    ring
  calc
    _ = ∑ i ∈ S, ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ, F i τ :=
      Finset.sum_congr rfl ht
    _ = ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ, ∑ i ∈ S, F i τ := by
      rw [integral_finsetSum S hF,Finset.mul_sum]
    _ = _ := by simp_rw [hf]; rw [integral_const_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticDualFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained Voronoi sum is an actual finite frequency polynomial.
Its cutoff is independent of the height parameter. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_frequency_norm_numerator (n : MetaplecticDualArgument) :
    Complex.normSq (metaplecticFrequency n) = norm n.val/3 := by
  have hLambda : Complex.normSq traceLambda = 3 := by
    rw [traceLambda_eq,Complex.normSq_mul,Complex.normSq_ofReal]
    norm_num [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [metaplecticFrequency,Complex.normSq_div,hLambda]
  rfl

lemma metaplecticDualNorm_coordinate_bound (nd : MetaplecticDualArgument × PrimaryArgument)
    {J : ℝ} (hcut : metaplecticDualNorm nd ≤ J) :
    norm nd.1.val ≤ 3*J ∧ norm nd.2.val ≤ 3*J := by
  have hN : 1 ≤ norm nd.1.val := one_le_norm nd.1.property
  have hD : 1 ≤ norm nd.2.val := one_le_norm (primary_ne_zero nd.2.property)
  have hD0 : 0 ≤ norm nd.2.val := norm_nonneg _
  have hN0 : 0 ≤ norm nd.1.val := norm_nonneg _
  have hraw : norm nd.2.val^3*norm nd.1.val ≤ 3*J := by
    unfold metaplecticDualNorm at hcut
    rw [metaplectic_frequency_norm_numerator] at hcut
    nlinarith
  have hD3 : 1 ≤ norm nd.2.val^3 := one_le_pow₀ hD
  have hn : norm nd.1.val ≤ norm nd.2.val^3*norm nd.1.val := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hD3 hN0
  have hd3 : norm nd.2.val^3 ≤ norm nd.2.val^3*norm nd.1.val := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hN (pow_nonneg hD0 3)
  have hd : norm nd.2.val ≤ norm nd.2.val^3 := by
    have hsq : 1 ≤ norm nd.2.val^2 := one_le_pow₀ hD
    have hh := mul_le_mul_of_nonneg_left hsq hD0
    nlinarith
  exact ⟨hn.trans hraw,(hd.trans hd3).trans hraw⟩

lemma mem_metaplecticDualBall (nd : MetaplecticDualArgument × PrimaryArgument) (J : ℝ) :
    nd ∈ metaplecticDualBall J ↔ metaplecticDualNorm nd ≤ J := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    obtain ⟨hn,hd⟩ := metaplecticDualNorm_coordinate_bound nd h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,h⟩
    · exact Finset.mem_subtype.mpr (mem_nonzeroNormBall.mpr ⟨hn,nd.1.property⟩)
    · exact Finset.mem_subtype.mpr (mem_primaryElementBall.mpr ⟨nd.2.property,hd⟩)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedCritical
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite retained Voronoi sum on the critical line, with
its coefficients normalized for ordinary free-variable mean value. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_sqrt_quotient {D N : ℝ} (hD : 0 < D) (hN : 0 < N) :
    Real.sqrt (D^3*N)/(N*D^(5/2:ℝ)) = 1/(Real.sqrt N*D) := by
  have hsD : Real.sqrt (D^3) = D*Real.sqrt D := by
    rw [show D^3 = D^2*D by ring,Real.sqrt_mul (sq_nonneg D),Real.sqrt_sq_eq_abs,
      abs_of_pos hD]
  have hpD : D^(5/2:ℝ) = D^2*Real.sqrt D := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_add hD]
    congr 1
    norm_num
  have he : Real.sqrt (D^3*N)*(Real.sqrt N*D) = N*D^(5/2:ℝ) := by
    rw [Real.sqrt_mul (by positivity),hsD,hpD]
    calc
      _ = D^2*Real.sqrt D*(Real.sqrt N)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hN.le]; ring
  apply (div_eq_div_iff (mul_ne_zero hN.ne' (Real.rpow_pos_of_pos hD _).ne')
    (mul_ne_zero (Real.sqrt_pos.mpr hN).ne' hD.ne')).mpr
  simpa only [one_mul] using he

lemma metaplecticRawDualCoefficient_normalize
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument) :
    metaplecticRawDualCoefficient a r ℓ nd*(Real.sqrt (metaplecticDualNorm nd):ℂ) =
      metaplecticNormalizedDualCoefficient a r ℓ nd := by
  have hD := norm_pos_of_ne_zero (primary_ne_zero nd.2.property)
  have hN := Complex.normSq_pos.mpr (metaplecticFrequency_ne_zero nd.1)
  have he := metaplectic_sqrt_quotient hD hN
  unfold metaplecticDualNorm
  have hec : ((Real.sqrt (norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)):ℝ):ℂ)/
      ((Complex.normSq (metaplecticFrequency nd.1)*norm nd.2^(5/2:ℝ):ℝ):ℂ) =
      1/((Real.sqrt (Complex.normSq (metaplecticFrequency nd.1))*norm nd.2:ℝ):ℂ) := by
    exact_mod_cast he
  unfold metaplecticRawDualCoefficient metaplecticNormalizedDualCoefficient
  split_ifs
  · calc
      _ = (a r nd.1*metaplecticLocalCoefficient r nd.1)*
          complexAngular (-ℓ) ((nd.2:Eisenstein)^3*metaplecticFrequency nd.1)*
          (((Real.sqrt (norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)):ℝ):ℂ)/
            ((Complex.normSq (metaplecticFrequency nd.1)*norm nd.2^(5/2:ℝ):ℝ):ℂ)) := by ring
      _ = _ := by rw [hec]; ring
  · simp only [zero_mul]

lemma metaplecticDualTerm_factor
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (A X : ℝ) (nd : MetaplecticDualArgument × PrimaryArgument) :
    metaplecticDualTerm a r ℓ W A X nd =
      metaplecticRawDualCoefficient a r ℓ nd *
        metaplecticTransform ℓ W A
          (((2*Real.pi)^4*X/norm r^2)*metaplecticDualNorm nd) := by
  unfold metaplecticDualTerm metaplecticRawDualCoefficient
  rw [metaplecticDualNorm_eq]
  have he : (2*Real.pi)^4*metaplecticDualNorm nd*X/norm r^2 =
      ((2*Real.pi)^4*X/norm r^2)*metaplecticDualNorm nd := by ring
  rw [he]
  split_ifs <;> ring

/-- The cutoff is arbitrary and independent of height. This is an exact
identity for the original retained Voronoi terms. -/
theorem metaplectic_retained_critical
    (a : Eisenstein → MetaplecticDualArgument → ℂ) {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {A X : ℝ} (hA : 0 ≤ A) (hX : 0 < X) (J t : ℝ)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A)) :
    (∑ nd ∈ metaplecticDualBall J,
      metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X nd) =
      (Real.sqrt ((2*Real.pi)^4*X/norm r^2):ℂ)*((1/(2*Real.pi):ℝ):ℂ)*
        ∫ τ : ℝ, metaplecticCriticalKernel ℓ W ((2*Real.pi)^4*X/norm r^2)
          (fun u => ∑ nd ∈ metaplecticDualBall J,
            metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase u (metaplecticDualNorm nd)) τ t := by
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hc : 0 < (2*Real.pi)^4*X/norm r^2 := by positivity
  simp_rw [metaplecticDualTerm_factor]
  rw [metaplectic_finite_transform_critical _ _ _
    (fun nd _ => metaplecticDualNorm_pos nd) ℓ W hW hpos hsm hA hc hm hp t]
  simp_rw [metaplecticRawDualCoefficient_normalize]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticBlockMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mean value of an actual retained free-variable block, with all
coefficient amplitudes supplied by the literal Voronoi coefficient bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_block_frequency (d : PrimaryArgument) (n : MetaplecticDualArgument)
    (j : ℤ) (hj : -1 ≤ j) (ζ : Eisensteinˣ) (h h' w : Eisenstein)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3) :
    metaplecticDualNorm (n,d) =
      (norm d^3*((3:ℝ)^((j+1).toNat-1:ℝ)*norm h*norm h'^3))*norm w := by
  unfold metaplecticDualNorm
  rw [metaplectic_frequency_norm n (j+1).toNat ζ h h' w
    (metaplectic_numerator_of_frequency n hj ζ h h' w he)]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticFreeFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal free-variable parametrization of each supported Voronoi
block, including the ramified exponent k=0 (j=-1). -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplecticFreeArgument_val (k : ℕ) (ζ : Eisensteinˣ)
    (h h' : PrimaryArgument) {w : Eisenstein} (hw : w ≠ 0) :
    (metaplecticFreeArgument k ζ h h' w).val = lambdaE^k*ζ.val*h.val*w*h'.val^3 := by
  simp only [metaplecticFreeArgument,dite_eq_left hw]

lemma metaplecticFreeArgument_frequency (k : ℕ) (ζ : Eisensteinˣ)
    (h h' : PrimaryArgument) {w : Eisenstein} (hw : w ≠ 0) :
    metaplecticFrequency (metaplecticFreeArgument k ζ h h' w) =
      traceLambda^((k:ℤ)-1)*(ζ.val:ℂ)*(h.val:ℂ)*(w:ℂ)*(h'.val:ℂ)^3 := by
  unfold metaplecticFrequency
  rw [metaplecticFreeArgument_val k ζ h h' hw]
  push_cast
  rw [lambdaE_coe,zpow_sub₀ traceLambda_ne_zero,zpow_natCast,zpow_one]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the literal published support representation once for each
nonzero retained coefficient. The resulting finite code set decodes
injectively to the original frequency set. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticNormalizedDualCoefficient_zero
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument)
    (hz : a r nd.1*metaplecticLocalCoefficient r nd.1 = 0) :
    metaplecticNormalizedDualCoefficient a r ℓ nd = 0 := by
  unfold metaplecticNormalizedDualCoefficient
  split_ifs <;> simp only [hz,zero_div,zero_mul]

/-- The index stores only genuine supported factors. Neither a free
coefficient bound nor a moment estimate is included in this reindexing. -/
theorem metaplectic_retained_support_partition
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ S : Finset (MetaplecticDualArgument × PrimaryArgument),
      ∃ T : Finset (MetaplecticRetainedCode r),
        (∀ z ∈ T, metaplecticRetainedDecode r z ∈ S ∧
          (∃ k : ℕ, z.2.1.2.2.2.val ∣ r^k) ∧ IsCoprime z.2.2.val r ∧
          Squarefree (z.2.1.2.2.1.val*z.2.2.val) ∧
          ‖a r (metaplecticRetainedDecode r z).1‖ ≤
            C*3^((max ((z.2.1.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm z.2.1.2.2.2)) ∧
        ∀ (ℓ : ℤ) (t : ℝ),
          (∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
            mellinPhase t (metaplecticDualNorm nd)) =
          ∑ z ∈ T, metaplecticNormalizedDualCoefficient a r ℓ (metaplecticRetainedDecode r z)*
            mellinPhase t (metaplecticDualNorm (metaplecticRetainedDecode r z)) := by
  obtain ⟨C,hC,hcoef⟩ := ha
  refine ⟨C,hC,?_⟩
  intro r hr hsr S
  let U := S.filter (fun nd => a r nd.1*metaplecticLocalCoefficient r nd.1 ≠ 0)
  have hcode (nd : U) : ∃ z : MetaplecticRetainedCode r,
      metaplecticRetainedDecode r z = nd.val ∧
      (∃ k : ℕ, z.2.1.2.2.2.val ∣ r^k) ∧ IsCoprime z.2.2.val r ∧
      Squarefree (z.2.1.2.2.1.val*z.2.2.val) ∧
      ‖a r (metaplecticRetainedDecode r z).1‖ ≤
        C*3^((max ((z.2.1.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm z.2.1.2.2.2) := by
    have hnd := (Finset.mem_filter.mp nd.property).2
    obtain ⟨j,ζ,h,h',w,hj,hh,hh',hw,hdiv,h'div,hwr,hs,he,hb⟩ :=
      hcoef r hr hsr nd.val.1 hnd
    let z : MetaplecticRetainedCode r :=
      (nd.val.2,((j+1).toNat,ζ,⟨h,metaplectic_supported_divisor_mem hr hh hs hdiv⟩,⟨h',hh'⟩),⟨w,hw⟩)
    have hd : metaplecticRetainedDecode r z = nd.val := by
      apply Prod.ext
      · apply Subtype.ext
        change (metaplecticFreeArgument (j+1).toNat ζ _ _ w).val = nd.val.1.val
        rw [metaplecticFreeArgument_val _ _ _ _ (primary_ne_zero hw)]
        exact (metaplectic_numerator_of_frequency nd.val.1 hj ζ h h' w he).symm
      · rfl
    refine ⟨z,hd,h'div,hwr,hs,?_⟩
    rw [hd]
    have hjk : (((j+1).toNat:ℕ):ℤ)-1 = j := by omega
    simpa only [z,hjk] using hb
  choose code hdecode hsupport hcop hsquare hbound using hcode
  let T : Finset (MetaplecticRetainedCode r) := Finset.univ.image code
  have hinj : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    exact (hdecode x).symm.trans ((congrArg (metaplecticRetainedDecode r) hxy).trans (hdecode y))
  refine ⟨T,?_,?_⟩
  · intro z hz
    obtain ⟨nd,_,rfl⟩ := Finset.mem_image.mp hz
    refine ⟨?_,hsupport nd,hcop nd,hsquare nd,hbound nd⟩
    rw [hdecode nd]
    exact (Finset.mem_filter.mp nd.property).1
  · intro ℓ t
    let F := fun nd : MetaplecticDualArgument × PrimaryArgument =>
      metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase t (metaplecticDualNorm nd)
    have hU : (∑ nd ∈ S, F nd) = ∑ nd ∈ U, F nd := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro nd hnd hnU
      have hz : a r nd.1*metaplecticLocalCoefficient r nd.1 = 0 := by
        by_contra h
        exact hnU (Finset.mem_filter.mpr ⟨hnd,h⟩)
      simp only [F,metaplecticNormalizedDualCoefficient_zero a r ℓ nd hz,zero_mul]
    change (∑ nd ∈ S, F nd) = ∑ z ∈ T, F (metaplecticRetainedDecode r z)
    rw [hU]
    change (∑ nd ∈ U, F nd) = ∑ z ∈ Finset.univ.image code, F (metaplecticRetainedDecode r z)
    rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
    simp_rw [hdecode]
    exact (Finset.sum_coe_sort U F).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCodeDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact norm dyad of each free variable after fixing the supported
parameters in the retained Voronoi sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticFreeScale_pos {r : Eisenstein} (p : MetaplecticDyadPrefix r) :
    0 < metaplecticFreeScale p := by
  have hd := norm_pos_of_ne_zero (primary_ne_zero p.1.property)
  have hh := norm_pos_of_ne_zero (primary_ne_zero (metaplecticDivisorPrimary r p.2.2.2.1).property)
  have hp := norm_pos_of_ne_zero (primary_ne_zero p.2.2.2.2.property)
  change 0 < norm p.1^3*((3:ℝ)^((p.2.1:ℝ)-1)*
    norm (metaplecticDivisorPrimary r p.2.2.2.1)*norm p.2.2.2.2^3)
  positivity

lemma metaplectic_prefix_frequency {r : Eisenstein} (p : MetaplecticDyadPrefix r)
    {w : Eisenstein} (hw : w ≠ 0) :
    metaplecticDualNorm (metaplecticPrefixArgument r p.2 w,p.1) =
      metaplecticFreeScale p*norm w := by
  have he := metaplecticFreeArgument_frequency p.2.1 p.2.2.1
    (metaplecticDivisorPrimary r p.2.2.2.1) p.2.2.2.2 hw
  have hk : -1 ≤ (p.2.1:ℤ)-1 := by omega
  have hn := metaplectic_block_frequency p.1 _ ((p.2.1:ℤ)-1) hk p.2.2.1
    (metaplecticDivisorPrimary r p.2.2.2.1) p.2.2.2.2 w he
  have hnat : (((p.2.1:ℤ)-1+1).toNat) = p.2.1 := by omega
  simpa only [metaplecticPrefixArgument,metaplecticFreeScale,hnat,metaplecticDivisorPrimary] using hn

lemma metaplectic_free_dyad {r : Eisenstein} (p : MetaplecticDyadPrefix r)
    {w : Eisenstein} (hw : w ≠ 0) {I : ℝ}
    (hI : I/2 ≤ metaplecticDualNorm (metaplecticPrefixArgument r p.2 w,p.1) ∧
      metaplecticDualNorm (metaplecticPrefixArgument r p.2 w,p.1) ≤ I) :
    (I/metaplecticFreeScale p)/2 ≤ norm w ∧ norm w ≤ I/metaplecticFreeScale p := by
  have hq := metaplecticFreeScale_pos p
  rw [metaplectic_prefix_frequency p hw] at hI
  constructor
  · rw [show (I/metaplecticFreeScale p)/2 = (I/2)/metaplecticFreeScale p by ring]
    apply (div_le_iff₀ hq).mpr
    nlinarith [hI.1]
  · exact (le_div_iff₀ hq).mpr (by nlinarith [hI.2])

lemma metaplectic_free_length_one {r : Eisenstein} (p : MetaplecticDyadPrefix r)
    {w : Eisenstein} (hw : primary w) {I : ℝ}
    (hI : metaplecticDualNorm (metaplecticPrefixArgument r p.2 w,p.1) ≤ I) :
    1 ≤ I/metaplecticFreeScale p := by
  have hq := metaplecticFreeScale_pos p
  rw [metaplectic_prefix_frequency p (primary_ne_zero hw)] at hI
  apply (le_div_iff₀ hq).mpr
  have h := mul_le_mul_of_nonneg_left (one_le_norm (primary_ne_zero hw)) hq.le
  nlinarith

lemma metaplecticFreeScale_lower {r : Eisenstein} (p : MetaplecticDyadPrefix r) :
    (1/3:ℝ) ≤ metaplecticFreeScale p := by
  have hd := one_le_norm (primary_ne_zero p.1.property)
  have hh := one_le_norm (primary_ne_zero (metaplecticDivisorPrimary r p.2.2.2.1).property)
  have hp := one_le_norm (primary_ne_zero p.2.2.2.2.property)
  have hb : (1/3:ℝ) ≤ (3:ℝ)^((p.2.1:ℝ)-1) := by
    rw [Real.rpow_sub (by norm_num),Real.rpow_one]
    exact div_le_div_of_nonneg_right
      (Real.one_le_rpow (by norm_num) (Nat.cast_nonneg p.2.1)) (by norm_num)
  change (1/3:ℝ) ≤ norm p.1^3*((3:ℝ)^((p.2.1:ℝ)-1)*
    norm (metaplecticDivisorPrimary r p.2.2.2.1)*norm p.2.2.2.2^3)
  calc
    (1/3:ℝ) = 1*((1/3)*1*1) := by ring
    _ ≤ _ := by
      gcongr
      · exact one_le_pow₀ hd
      · exact one_le_pow₀ hp

lemma metaplectic_free_length_upper {r : Eisenstein} (p : MetaplecticDyadPrefix r)
    {I : ℝ} (hI : 0 ≤ I) : I/metaplecticFreeScale p ≤ 3*I := by
  apply (div_le_iff₀ (metaplecticFreeScale_pos p)).mpr
  have h := mul_nonneg hI (sub_nonneg.mpr (metaplecticFreeScale_lower p))
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCodePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite partition of the chosen retained frequencies by their
supported prefix. The remaining index is the literal primary free variable. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_code_ext {r : Eisenstein} {x y : MetaplecticRetainedCode r}
    (hp : metaplecticCodePrefix x = metaplecticCodePrefix y)
    (hw : x.2.2.val = y.2.2.val) : x = y := by
  have hd : x.1 = y.1 := congrArg (fun q : MetaplecticDyadPrefix r => q.1) hp
  have hs : x.2.1 = y.2.1 := congrArg (fun q : MetaplecticDyadPrefix r => q.2) hp
  have hf : x.2.2 = y.2.2 := Subtype.ext hw
  exact Prod.ext hd (Prod.ext hs hf)

lemma metaplectic_decode_of_prefix {r : Eisenstein} {z : MetaplecticRetainedCode r}
    {p : MetaplecticDyadPrefix r} (hp : metaplecticCodePrefix z = p) :
    metaplecticRetainedDecode r z = (metaplecticPrefixArgument r p.2 z.2.2.val,p.1) := by
  have hd : z.1 = p.1 := congrArg (fun q : MetaplecticDyadPrefix r => q.1) hp
  have hs : z.2.1 = p.2 := congrArg (fun q : MetaplecticDyadPrefix r => q.2) hp
  simp only [metaplecticRetainedDecode,hd,hs]

lemma metaplectic_mem_codeFreeSet {r : Eisenstein} {T : Finset (MetaplecticRetainedCode r)}
    {p : MetaplecticDyadPrefix r} {w : Eisenstein} :
    w ∈ metaplecticCodeFreeSet T p ↔
      ∃ z ∈ T, metaplecticCodePrefix z = p ∧ z.2.2.val = w := by
  simp only [metaplecticCodeFreeSet,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨z,⟨hz,hp⟩,hw⟩
    exact ⟨z,hz,hp,hw⟩
  · rintro ⟨z,hz,hp,hw⟩
    exact ⟨z,⟨hz,hp⟩,hw⟩

lemma metaplectic_codeFreeSet_primary {r : Eisenstein} (T : Finset (MetaplecticRetainedCode r))
    (p : MetaplecticDyadPrefix r) {w : Eisenstein} (hw : w ∈ metaplecticCodeFreeSet T p) :
    primary w := by
  obtain ⟨z,_,_,rfl⟩ := metaplectic_mem_codeFreeSet.mp hw
  exact z.2.2.property

lemma metaplectic_code_prefix_sum {r : Eisenstein} (T : Finset (MetaplecticRetainedCode r))
    (p : MetaplecticDyadPrefix r) (F : MetaplecticDualArgument × PrimaryArgument → ℂ) :
    (∑ z ∈ T.filter (fun z => metaplecticCodePrefix z = p), F (metaplecticRetainedDecode r z)) =
      ∑ w ∈ metaplecticCodeFreeSet T p, F (metaplecticPrefixArgument r p.2 w,p.1) := by
  rw [metaplecticCodeFreeSet,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [metaplectic_decode_of_prefix (Finset.mem_filter.mp hz).2]
  · intro x hx y hy hxy
    exact metaplectic_code_ext
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy

/-- No extra multiplicity is introduced by separating the fixed support
parameters from the free primary argument. -/
theorem metaplectic_code_partition {r : Eisenstein} (T : Finset (MetaplecticRetainedCode r))
    (F : MetaplecticDualArgument × PrimaryArgument → ℂ) :
    (∑ z ∈ T, F (metaplecticRetainedDecode r z)) =
      ∑ p ∈ T.image metaplecticCodePrefix,
        ∑ w ∈ metaplecticCodeFreeSet T p, F (metaplecticPrefixArgument r p.2 w,p.1) := by
  calc
    _ = ∑ p ∈ T.image metaplecticCodePrefix,
        ∑ z ∈ T.filter (fun z => metaplecticCodePrefix z = p),
          F (metaplecticRetainedDecode r z) :=
      (Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image metaplecticCodePrefix)
        (g := metaplecticCodePrefix)
        (fun z hz => by
          simp only [Finset.mem_image]
          exact ⟨z,hz,rfl⟩)
        (fun z => F (metaplecticRetainedDecode r z))).symm
    _ = _ := Finset.sum_congr rfl (fun p _ => metaplectic_code_prefix_sum T p F)

lemma metaplectic_codeFreeSet_dyad {r : Eisenstein} (T : Finset (MetaplecticRetainedCode r))
    (p : MetaplecticDyadPrefix r) {I : ℝ}
    (hT : ∀ z ∈ T, I/2 ≤ metaplecticDualNorm (metaplecticRetainedDecode r z) ∧
      metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I) :
    ∀ w ∈ metaplecticCodeFreeSet T p,
      (I/metaplecticFreeScale p)/2 ≤ norm w ∧ norm w ≤ I/metaplecticFreeScale p := by
  intro w hw
  obtain ⟨z,hz,hp,rfl⟩ := metaplectic_mem_codeFreeSet.mp hw
  apply metaplectic_free_dyad p (primary_ne_zero z.2.2.property)
  rw [←metaplectic_decode_of_prefix hp]
  exact hT z hz

lemma metaplectic_codeFreeSet_length_one {r : Eisenstein}
    (T : Finset (MetaplecticRetainedCode r)) {p : MetaplecticDyadPrefix r}
    (hp : p ∈ T.image metaplecticCodePrefix) {I : ℝ}
    (hT : ∀ z ∈ T, metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I) :
    1 ≤ I/metaplecticFreeScale p := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
  apply metaplectic_free_length_one (r := r) (metaplecticCodePrefix z) z.2.2.property
  rw [←metaplectic_decode_of_prefix (rfl : metaplecticCodePrefix z = metaplecticCodePrefix z)]
  exact hT z hz

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticFreeReflection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflection of the free-primary mean for the translated variable
appearing in the actual critical-line Mellin kernel. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_reflected_polynomial_norm (S : Finset Eisenstein)
    (v : Eisenstein → ℂ) (c u t : ℝ) :
    ‖∑ b ∈ S, v b*mellinPhase (u-t) (c*norm b)‖ =
      ‖∑ b ∈ S, star (v b)*mellinPhase (t-u) (c*norm b)‖ := by
  rw [←norm_star (∑ b ∈ S, v b*mellinPhase (u-t) (c*norm b))]
  simp only [star_sum,star_mul,star_mellinPhase,neg_sub,mul_comm]

 theorem metaplectic_reflected_free_mean {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S : Finset Eisenstein), (∀ b ∈ S, primary b) →
      ∀ (v : Eisenstein → ℂ) (L K T u c : ℝ),
      1 ≤ L → 0 ≤ K → 0 < T → 0 < c →
      (∀ b ∈ S, L/2 ≤ norm b ∧ norm b ≤ L) →
      (∀ b ∈ S, ‖v b‖^2 ≤ K^2/norm b) →
      (∫ t in T..2*T, ‖∑ b ∈ S, v b*mellinPhase (u-t) (c*norm b)‖)/T ≤
        Real.sqrt (C*D)*L^(ε/2)*K*(1+Real.sqrt (2*L/T)) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_scaled_free_meanAbsolute hε hMV hC
  refine ⟨D,hD,?_⟩
  intro S hS v L K T u c hL hK hT hc hsize hv
  have h := hbound S hS (fun b => star (v b)) L K T (-u) c 0 hL hK hT hc hsize
    (by intro b hb; simpa only [norm_star] using hv b hb)
  simp only [theta_zero,mul_one] at h
  have he : (fun t : ℝ => ‖∑ b ∈ S, v b*mellinPhase (u-t) (c*norm b)‖) =
      (fun t : ℝ => ‖∑ b ∈ S, star (v b)*mellinPhase (t-u) (c*norm b)‖) :=
    funext (fun t => metaplectic_reflected_polynomial_norm S v c u t)
  rw [he]
  simpa only [sub_eq_add_neg] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCodeMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary mean values for the exact finite prefix partition. The
coefficient hypotheses here are precisely the support data supplied by
`metaplectic_retained_support_partition`. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mean_norm_finset_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ S, Continuous (f i)) {T : ℝ} (hT : 0 < T)
    (B : ι → ℝ) (hB : ∀ i ∈ S, (∫ t in T..2*T, ‖f i t‖)/T ≤ B i) :
    (∫ t in T..2*T, ‖∑ i ∈ S, f i t‖)/T ≤ ∑ i ∈ S, B i := by
  have hc := continuous_finsetSum S hf
  have hn := continuous_finsetSum S (fun i hi => (hf i hi).norm)
  calc
    _ ≤ (∫ t in T..2*T, ∑ i ∈ S, ‖f i t‖)/T := by
      apply div_le_div_of_nonneg_right _ hT.le
      exact intervalIntegral.integral_mono (by linarith)
        (hc.norm.intervalIntegrable _ _) (hn.intervalIntegrable _ _)
        (fun t => norm_sum_le _ _)
    _ = ∑ i ∈ S, (∫ t in T..2*T, ‖f i t‖)/T := by
      rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).norm.intervalIntegrable _ _),
        Finset.sum_div]
    _ ≤ _ := Finset.sum_le_sum hB

theorem metaplectic_code_block_mean {ε M : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a : Eisenstein → MetaplecticDualArgument → ℂ)
      (C : ℝ), 0 ≤ C → ∀ r : Eisenstein, primary r →
      ∀ (S : Finset (MetaplecticRetainedCode r)) (p : MetaplecticDyadPrefix r),
      (∀ z ∈ S, IsCoprime z.2.2.val r) →
      (∀ z ∈ S, ‖a r (metaplecticRetainedDecode r z).1‖ ≤
        C*3^((max ((z.2.1.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm z.2.1.2.2.2)) →
      ∀ I T : ℝ, p ∈ S.image metaplecticCodePrefix → 0 < T →
      (∀ z ∈ S, I/2 ≤ metaplecticDualNorm (metaplecticRetainedDecode r z) ∧
        metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I) →
      ∀ ℓ : ℤ, ∀ τ : ℝ,
      (∫ t in T..2*T, ‖∑ w ∈ metaplecticCodeFreeSet S p,
        metaplecticNormalizedDualCoefficient a r ℓ (metaplecticPrefixArgument r p.2 w,p.1)*
          mellinPhase (τ-t) (metaplecticDualNorm (metaplecticPrefixArgument r p.2 w,p.1))‖)/T ≤
        Real.sqrt (M*D)*(I/metaplecticFreeScale p)^(ε/2)*metaplecticPrefixAmplitude r C p*
          (1+Real.sqrt (2*(I/metaplecticFreeScale p)/T)) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_reflected_free_mean hε hMV hM
  refine ⟨D,hD,?_⟩
  intro a C hC r hr S p hcop hcoef I T hp hT hdyad ℓ τ
  let F := metaplecticCodeFreeSet S p
  let v := fun w => metaplecticNormalizedDualCoefficient a r ℓ
    (metaplecticPrefixArgument r p.2 w,p.1)
  have hj : -1 ≤ (p.2.1:ℤ)-1 := by omega
  have hnat : (((p.2.1:ℤ)-1+1).toNat) = p.2.1 := by omega
  have hcp (w : Eisenstein) (hw : w ∈ F) : IsCoprime w r := by
    obtain ⟨z,hz,_,rfl⟩ := metaplectic_mem_codeFreeSet.mp hw
    exact hcop z hz
  have hcf (w : Eisenstein) (hw : w ∈ F) :
      ‖a r (metaplecticPrefixArgument r p.2 w)‖ ≤
        C*3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm p.2.2.2.2) := by
    obtain ⟨z,hz,hzp,rfl⟩ := metaplectic_mem_codeFreeSet.mp hw
    have he := hcoef z hz
    rw [metaplectic_decode_of_prefix hzp] at he
    have hs : z.2.1 = p.2 := congrArg (fun q : MetaplecticDyadPrefix r => q.2) hzp
    simpa only [hs] using he
  have hv (w : Eisenstein) (hw : w ∈ F) :
      ‖v w‖^2 ≤ (metaplecticPrefixAmplitude r C p)^2/norm w := by
    have h := metaplectic_actual_free_coefficient_sq hC hr p.1 ℓ
      (metaplecticPrefixArgument r p.2 w) hj p.2.2.1
      (metaplecticDivisorPrimary r p.2.2.2.1).property p.2.2.2.2.property
      (metaplectic_codeFreeSet_primary S p hw) (hcp w hw)
      (metaplecticFreeArgument_frequency p.2.1 p.2.2.1
        (metaplecticDivisorPrimary r p.2.2.2.1) p.2.2.2.2
        (primary_ne_zero (metaplectic_codeFreeSet_primary S p hw))) (hcf w hw)
    simpa only [v,metaplecticPrefixAmplitude,hnat,metaplecticDivisorPrimary] using h
  have hK : 0 ≤ metaplecticPrefixAmplitude r C p := by
    have hd := norm_pos_of_ne_zero (primary_ne_zero p.1.property)
    have hh := norm_pos_of_ne_zero (primary_ne_zero (metaplecticDivisorPrimary r p.2.2.2.1).property)
    have hhp := norm_pos_of_ne_zero (primary_ne_zero p.2.2.2.2.property)
    have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
    unfold metaplecticPrefixAmplitude
    change 0 ≤ C*3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm p.2.2.2.2)*
      min (norm r) (norm (metaplecticDivisorPrimary r p.2.2.2.1)*norm p.2.2.2.2)/_
    positivity
  have hb := hbound F (fun w hw => metaplectic_codeFreeSet_primary S p hw)
    v (I/metaplecticFreeScale p) (metaplecticPrefixAmplitude r C p) T τ
    (metaplecticFreeScale p) (metaplectic_codeFreeSet_length_one S hp
      (fun z hz => (hdyad z hz).2)) hK hT (metaplecticFreeScale_pos p)
    (metaplectic_codeFreeSet_dyad S p hdyad) hv
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  funext t
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  rw [metaplectic_prefix_frequency p
    (primary_ne_zero (metaplectic_codeFreeSet_primary S p hw))]

/-- Reassembling the chosen support codes costs only the sum of the explicit
free-block majorants. The original finite frequency polynomial is retained. -/
theorem metaplectic_code_mean {ε M : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a : Eisenstein → MetaplecticDualArgument → ℂ)
      (C : ℝ), 0 ≤ C → ∀ r : Eisenstein, primary r →
      ∀ S : Finset (MetaplecticRetainedCode r),
      (∀ z ∈ S, IsCoprime z.2.2.val r) →
      (∀ z ∈ S, ‖a r (metaplecticRetainedDecode r z).1‖ ≤
        C*3^((max ((z.2.1.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm z.2.1.2.2.2)) →
      ∀ I T : ℝ, 0 < T →
      (∀ z ∈ S, I/2 ≤ metaplecticDualNorm (metaplecticRetainedDecode r z) ∧
        metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I) →
      ∀ ℓ : ℤ, ∀ τ : ℝ,
      (∫ t in T..2*T, ‖∑ z ∈ S,
        metaplecticNormalizedDualCoefficient a r ℓ (metaplecticRetainedDecode r z)*
          mellinPhase (τ-t) (metaplecticDualNorm (metaplecticRetainedDecode r z))‖)/T ≤
        ∑ p ∈ S.image metaplecticCodePrefix,
          Real.sqrt (M*D)*(I/metaplecticFreeScale p)^(ε/2)*metaplecticPrefixAmplitude r C p*
            (1+Real.sqrt (2*(I/metaplecticFreeScale p)/T)) := by
  obtain ⟨D,hD,hb⟩ := metaplectic_code_block_mean hε hMV hM
  refine ⟨D,hD,?_⟩
  intro a C hC r hr S hcop hcoef I T hT hdyad ℓ τ
  let f := fun p : MetaplecticDyadPrefix r => fun t : ℝ =>
    ∑ w ∈ metaplecticCodeFreeSet S p,
      metaplecticNormalizedDualCoefficient a r ℓ (metaplecticPrefixArgument r p.2 w,p.1)*
        mellinPhase (τ-t) (metaplecticDualNorm (metaplecticPrefixArgument r p.2 w,p.1))
  have hf (p : MetaplecticDyadPrefix r) : Continuous (f p) := by
    apply continuous_finsetSum
    intro w hw
    apply continuous_const.mul
    unfold mellinPhase
    fun_prop
  have he (t : ℝ) : (∑ z ∈ S,
      metaplecticNormalizedDualCoefficient a r ℓ (metaplecticRetainedDecode r z)*
        mellinPhase (τ-t) (metaplecticDualNorm (metaplecticRetainedDecode r z))) =
      ∑ p ∈ S.image metaplecticCodePrefix, f p t :=
    metaplectic_code_partition S (fun nd =>
      metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase (τ-t) (metaplecticDualNorm nd))
  simp_rw [he]
  exact mean_norm_finset_sum_le _ f (fun p _ => hf p) hT _
    (fun p hp => hb a C hC r hr S p hcop hcoef I T hp hT hdyad ℓ τ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticBlockAmplitude
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar simplifications of the two actual retained-block amplitudes.
The ramified endpoint k=0 is included in the same geometric sequence. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_sqrt_block_base {b H P : ℝ} (hb : 0 < b) (hH : 0 < H) (hP : 0 < P) :
    Real.sqrt (b*H*P^3) = Real.sqrt b*Real.sqrt H*P*Real.sqrt P := by
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul hb.le]
  have hp : Real.sqrt (P^3) = P*Real.sqrt P := by
    rw [show P^3=P^2*P by ring,Real.sqrt_mul (sq_nonneg P),Real.sqrt_sq_eq_abs,
      abs_of_pos hP]
  rw [hp]
  ring

lemma metaplectic_block_scalar {b H P D : ℝ}
    (hb : 0 < b) (hH : 0 < H) (hP : 0 < P) (hD : 0 < D)
    (C α g : ℝ) :
    C*α*Real.sqrt P*g/(Real.sqrt (b*H*P^3)*D) =
      (C*α/Real.sqrt b)*(g/(D*P*Real.sqrt H)) := by
  rw [metaplectic_sqrt_block_base hb hH hP]
  field_simp [(Real.sqrt_pos.mpr hb).ne',(Real.sqrt_pos.mpr hH).ne',
    (Real.sqrt_pos.mpr hP).ne',hD.ne',hP.ne']

lemma metaplectic_ramified_first_ratio (k : ℕ) :
    (3:ℝ)^((k:ℝ)/3)/Real.sqrt ((3:ℝ)^((k:ℝ)-1)) =
      Real.sqrt 3*((3:ℝ)^(-1/6:ℝ))^k := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul (by norm_num),
    ←Real.rpow_sub (by norm_num),Real.sqrt_eq_rpow,
    ←Real.rpow_mul_natCast (by norm_num),←Real.rpow_add (by norm_num)]
  congr 1
  ring

lemma metaplectic_ramified_second_ratio (k : ℕ) :
    (3:ℝ)^((k:ℝ)/3)/((3:ℝ)^((k:ℝ)-1)) =
      3*((3:ℝ)^(-2/3:ℝ))^k := by
  rw [←Real.rpow_sub (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  calc
    _ = (3:ℝ)^(1+(-2/3)*(k:ℝ)) := by congr 1; ring
    _ = _ := by rw [Real.rpow_add (by norm_num),Real.rpow_one]

lemma metaplectic_common_first_amplitude {R H P D g : ℝ}
    (hR : 0 < R) (hH : 0 < H) (hP : 0 < P) (hD : 0 < D)
    (hg : g ≤ Real.sqrt (R*(H*P))) :
    g/(D*P*Real.sqrt H) ≤ Real.sqrt R/(D*Real.sqrt P) := by
  apply (div_le_iff₀ (by positivity : 0 < D*P*Real.sqrt H)).mpr
  have he : Real.sqrt (R*(H*P)) =
      Real.sqrt R*Real.sqrt H*Real.sqrt P := by
    rw [Real.sqrt_mul hR.le,Real.sqrt_mul hH.le]
    ring
  have ht : Real.sqrt R/(D*Real.sqrt P)*(D*P*Real.sqrt H) =
      Real.sqrt R*Real.sqrt H*Real.sqrt P := by
    have hp : P/Real.sqrt P = Real.sqrt P := by
      apply (div_eq_iff (Real.sqrt_pos.mpr hP).ne').mpr
      nlinarith [Real.sq_sqrt hP.le]
    calc
      _ = Real.sqrt R*Real.sqrt H*(P/Real.sqrt P) := by
        field_simp [(Real.sqrt_pos.mpr hP).ne',hD.ne']
      _ = _ := by rw [hp]
  rw [ht]
  exact hg.trans_eq he

lemma metaplectic_common_second_amplitude {H P D g : ℝ}
    (hH : 0 < H) (hP : 0 < P) (hD : 0 < D) (hg : g ≤ H*P) :
    g/(D*P*Real.sqrt H) ≤ Real.sqrt H/D := by
  apply (div_le_iff₀ (by positivity : 0 < D*P*Real.sqrt H)).mpr
  have he : Real.sqrt H/D*(D*P*Real.sqrt H) = H*P := by
    calc
      _ = P*(Real.sqrt H)^2 := by field_simp [hD.ne']
      _ = _ := by rw [Real.sq_sqrt hH.le]; ring
  rw [he]
  exact hg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticScaledAmplitude
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two separated scalar majorants for a retained norm dyad.
The square-root level normalization is kept explicit. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_ramified_exponent_le (k : ℕ) :
    (3:ℝ)^((max ((k:ℤ)-1) 0:ℤ)/3:ℝ) ≤ (3:ℝ)^((k:ℝ)/3) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h : max ((k:ℤ)-1) 0 ≤ (k:ℤ) := by omega
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num)

lemma metaplectic_first_scaled_amplitude {R H P D g C α b : ℝ}
    (hR : 0 < R) (hH : 0 < H) (hP : 0 < P) (hD : 0 < D)
    (hb : 0 < b) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hg : g ≤ Real.sqrt (R*(H*P))) :
    (C*α*Real.sqrt P*g/(Real.sqrt (b*H*P^3)*D))/Real.sqrt R ≤
      (C*α/Real.sqrt b)/(D*Real.sqrt P) := by
  rw [metaplectic_block_scalar hb hH hP hD]
  have he := metaplectic_common_first_amplitude hR hH hP hD hg
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hR)).mpr
  calc
    _ ≤ (C*α/Real.sqrt b)*(Real.sqrt R/(D*Real.sqrt P)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

lemma metaplectic_free_sqrt {I T D b H P : ℝ}
    (hD : 0 < D) (hb : 0 < b) (hH : 0 < H) (hP : 0 < P) :
    Real.sqrt (2*(I/(D^3*(b*H*P^3)))/T) =
      Real.sqrt (2*I/T)/(D*Real.sqrt D*Real.sqrt b*Real.sqrt H*P*Real.sqrt P) := by
  rw [show 2*(I/(D^3*(b*H*P^3)))/T = (2*I/T)/(D^3*(b*H*P^3)) by ring,
    Real.sqrt_div' _ (by positivity : 0 ≤ D^3*(b*H*P^3)),
    Real.sqrt_mul (by positivity : 0 ≤ D^3),
    metaplectic_sqrt_block_base hb hH hP]
  have hd : Real.sqrt (D^3) = D*Real.sqrt D := by
    rw [show D^3=D^2*D by ring,Real.sqrt_mul (sq_nonneg D),
      Real.sqrt_sq_eq_abs,abs_of_pos hD]
  rw [hd]
  congr 1
  ring

lemma metaplectic_second_scaled_amplitude {R H P D g C α b I T : ℝ}
    (hR : 0 < R) (hH : 0 < H) (hP : 0 < P) (hD : 0 < D)
    (hb : 0 < b) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hg : g ≤ H*P) :
    (C*α*Real.sqrt P*g/(Real.sqrt (b*H*P^3)*D))/Real.sqrt R *
        Real.sqrt (2*(I/(D^3*(b*H*P^3)))/T) ≤
      C*(α/b)*Real.sqrt (2*I/(R*T))/(D^2*Real.sqrt D*P*Real.sqrt P) := by
  rw [metaplectic_block_scalar hb hH hP hD]
  have he := metaplectic_common_second_amplitude hH hP hD hg
  calc
    _ ≤ ((C*α/Real.sqrt b)*(Real.sqrt H/D))/Real.sqrt R *
        Real.sqrt (2*(I/(D^3*(b*H*P^3)))/T) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by
      rw [metaplectic_free_sqrt hD hb hH hP]
      rw [show 2*I/(R*T)=(2*I/T)/R by ring,Real.sqrt_div' _ hR.le]
      have hs := Real.sq_sqrt hb.le
      field_simp [(Real.sqrt_pos.mpr hR).ne',(Real.sqrt_pos.mpr hH).ne',
        (Real.sqrt_pos.mpr hP).ne',(Real.sqrt_pos.mpr hD).ne',
        (Real.sqrt_pos.mpr hb).ne',hD.ne',hP.ne',hb.ne']
      rw [hs]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrefixAmplitude
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the two scalar estimates to the literal prefix amplitude.
The resulting weights are the geometric and primary norm weights already
controlled by the finite arithmetic prefix sums. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_min_common {R H P : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H) (hP : 0 ≤ P) :
    min R (H*P) ≤ Real.sqrt (R*(H*P)) := by
  apply Real.le_sqrt_of_sq_le
  simpa only [pow_two] using mul_le_mul (min_le_left R (H*P))
    (min_le_right R (H*P)) (le_min hR (mul_nonneg hH hP)) hR

lemma metaplectic_first_norm_weight {D P : ℝ} (hP : 0 ≤ P) :
    D^(-1:ℝ)*P^(-(1/2):ℝ) = 1/(D*Real.sqrt P) := by
  rw [Real.rpow_neg_one,Real.rpow_neg hP,←Real.sqrt_eq_rpow]
  ring

lemma metaplectic_second_norm_weight {D P : ℝ} (hD : 0 < D) (hP : 0 < P) :
    D^(-(5/2):ℝ)*P^(-(3/2):ℝ) = 1/(D^2*Real.sqrt D*P*Real.sqrt P) := by
  have hd : D^(5/2:ℝ) = D^2*Real.sqrt D := by
    rw [show (5/2:ℝ)=2+1/2 by ring,Real.rpow_add hD,Real.rpow_two,←Real.sqrt_eq_rpow]
  have hp : P^(3/2:ℝ) = P*Real.sqrt P := by
    rw [show (3/2:ℝ)=1+1/2 by ring,Real.rpow_add hP,Real.rpow_one,←Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hD.le,Real.rpow_neg hP.le,hd,hp]
  ring

lemma metaplecticPrefixAmplitude_nonneg {r : Eisenstein} (hr : primary r)
    {C : ℝ} (hC : 0 ≤ C) (p : MetaplecticDyadPrefix r) :
    0 ≤ metaplecticPrefixAmplitude r C p := by
  have hd := norm_pos_of_ne_zero (primary_ne_zero p.1.property)
  have hh := norm_pos_of_ne_zero (primary_ne_zero (metaplecticDivisorPrimary r p.2.2.2.1).property)
  have hp := norm_pos_of_ne_zero (primary_ne_zero p.2.2.2.2.property)
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  unfold metaplecticPrefixAmplitude
  change 0 ≤ C*3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm p.2.2.2.2)*
    min (norm r) (norm (metaplecticDivisorPrimary r p.2.2.2.1)*norm p.2.2.2.2)/_
  positivity

lemma metaplectic_prefix_first_amplitude {r : Eisenstein} (hr : primary r)
    {C : ℝ} (hC : 0 ≤ C) (p : MetaplecticDyadPrefix r) :
    metaplecticPrefixAmplitude r C p/Real.sqrt (norm r) ≤
      C*Real.sqrt 3*((3:ℝ)^(-1/6:ℝ))^p.2.1*
        (norm p.1^(-1:ℝ)*norm p.2.2.2.2^(-(1/2):ℝ)) := by
  have hd := norm_pos_of_ne_zero (primary_ne_zero p.1.property)
  have hh := norm_pos_of_ne_zero (primary_ne_zero (metaplecticDivisorPrimary r p.2.2.2.1).property)
  have hp := norm_pos_of_ne_zero (primary_ne_zero p.2.2.2.2.property)
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hb : 0 < (3:ℝ)^((p.2.1:ℝ)-1) := by positivity
  have ha : 0 ≤ (3:ℝ)^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ) := by positivity
  have hratio := div_le_div_of_nonneg_right (metaplectic_ramified_exponent_le p.2.1)
    (Real.sqrt_nonneg ((3:ℝ)^((p.2.1:ℝ)-1)))
  rw [metaplectic_ramified_first_ratio] at hratio
  have he := metaplectic_first_scaled_amplitude hR hh hp hd hb hC ha
    (metaplectic_min_common hR.le hh.le hp.le)
  change metaplecticPrefixAmplitude r C p/Real.sqrt (norm r) ≤ _
  calc
    _ ≤ (C*3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)/
        Real.sqrt ((3:ℝ)^((p.2.1:ℝ)-1)))/(norm p.1*Real.sqrt (norm p.2.2.2.2)) := by
      simpa only [metaplecticPrefixAmplitude,metaplecticDivisorPrimary] using he
    _ = C*(3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)/
        Real.sqrt ((3:ℝ)^((p.2.1:ℝ)-1)))*
          (1/(norm p.1*Real.sqrt (norm p.2.2.2.2))) := by ring
    _ ≤ C*(Real.sqrt 3*((3:ℝ)^(-1/6:ℝ))^p.2.1)*
        (1/(norm p.1*Real.sqrt (norm p.2.2.2.2))) := by
      gcongr
    _ = _ := by rw [←metaplectic_first_norm_weight hp.le]; ring

lemma metaplectic_prefix_second_amplitude {r : Eisenstein} (hr : primary r)
    {C : ℝ} (hC : 0 ≤ C) (p : MetaplecticDyadPrefix r) (I T : ℝ) :
    metaplecticPrefixAmplitude r C p/Real.sqrt (norm r)*
        Real.sqrt (2*(I/metaplecticFreeScale p)/T) ≤
      C*3*((3:ℝ)^(-2/3:ℝ))^p.2.1*Real.sqrt (2*I/(norm r*T))*
        (norm p.1^(-(5/2):ℝ)*norm p.2.2.2.2^(-(3/2):ℝ)) := by
  have hd := norm_pos_of_ne_zero (primary_ne_zero p.1.property)
  have hh := norm_pos_of_ne_zero (primary_ne_zero (metaplecticDivisorPrimary r p.2.2.2.1).property)
  have hp := norm_pos_of_ne_zero (primary_ne_zero p.2.2.2.2.property)
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hb : 0 < (3:ℝ)^((p.2.1:ℝ)-1) := by positivity
  have ha : 0 ≤ (3:ℝ)^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ) := by positivity
  have hratio := div_le_div_of_nonneg_right (metaplectic_ramified_exponent_le p.2.1) hb.le
  rw [metaplectic_ramified_second_ratio] at hratio
  have he := metaplectic_second_scaled_amplitude hR hh hp hd hb hC ha
    (min_le_right (norm r) (norm (metaplecticDivisorPrimary r p.2.2.2.1)*norm p.2.2.2.2))
    (I := I) (T := T)
  calc
    _ ≤ C*(3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)/((3:ℝ)^((p.2.1:ℝ)-1)))*
        Real.sqrt (2*I/(norm r*T))/
          (norm p.1^2*Real.sqrt (norm p.1)*norm p.2.2.2.2*Real.sqrt (norm p.2.2.2.2)) := by
      simpa only [metaplecticPrefixAmplitude,metaplecticFreeScale,metaplecticDivisorPrimary] using he
    _ = C*(3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)/((3:ℝ)^((p.2.1:ℝ)-1)))*
        Real.sqrt (2*I/(norm r*T))*
          (1/(norm p.1^2*Real.sqrt (norm p.1)*norm p.2.2.2.2*Real.sqrt (norm p.2.2.2.2))) := by ring
    _ ≤ C*(3*((3:ℝ)^(-2/3:ℝ))^p.2.1)*Real.sqrt (2*I/(norm r*T))*
        (1/(norm p.1^2*Real.sqrt (norm p.1)*norm p.2.2.2.2*Real.sqrt (norm p.2.2.2.2))) := by
      gcongr
    _ = _ := by rw [←metaplectic_second_norm_weight hd hp]; ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrefixSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated finite sums over the actual supported prefixes. A finite
subset of prefixes costs at most the product of its coordinate sums. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_prefix_product_bound {r : Eisenstein}
    (P : Finset (MetaplecticDyadPrefix r))
    (fd : PrimaryArgument → ℝ) (fk : ℕ → ℝ) (fhp : PrimaryArgument → ℝ)
    (hd : ∀ d, 0 ≤ fd d) (hk : ∀ k, 0 ≤ fk k) (hhp : ∀ p, 0 ≤ fhp p) :
    (∑ p ∈ P, fd p.1*fk p.2.1*fhp p.2.2.2.2) ≤
      (∑ d ∈ P.image Prod.fst, fd d)*(∑ k ∈ P.image (fun p => p.2.1), fk k)*
        (Nat.card (Eisensteinˣ):ℝ)*((metaplecticPrimaryDivisors r).card:ℝ)*
          (∑ h ∈ P.image (fun p => p.2.2.2.2), fhp h) := by
  let : Finite (Eisensteinˣ) := metaplectic_units_finite
  let : Fintype (Eisensteinˣ) := Fintype.ofFinite _
  let D := P.image Prod.fst
  let K := P.image (fun p => p.2.1)
  let H := P.image (fun p => p.2.2.2.2)
  have hsub : P ⊆ D ×ˢ (K ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ H))) := by
    intro p hp
    apply Finset.mem_product.mpr
    refine ⟨?_,Finset.mem_product.mpr ⟨?_,Finset.mem_product.mpr
      ⟨Finset.mem_univ _,Finset.mem_product.mpr ⟨Finset.mem_univ _,?_⟩⟩⟩⟩
    · exact Finset.mem_image_of_mem _ hp
    · exact Finset.mem_image_of_mem _ hp
    · exact Finset.mem_image_of_mem _ hp
  calc
    _ ≤ ∑ p ∈ D ×ˢ (K ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ H))),
        fd p.1*fk p.2.1*fhp p.2.2.2.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
        mul_nonneg (mul_nonneg (hd _) (hk _)) (hhp _))
    _ = _ := by
      simp only [Finset.sum_product]
      simp_rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      simp_rw [←Finset.mul_sum,←Finset.sum_mul]
      simp only [Fintype.card_coe,Nat.card_eq_fintype_card]
      simp_rw [←Finset.mul_sum,←Finset.sum_mul]
      dsimp only [D,K,H]
      ring

lemma primary_argument_harmonic {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset PrimaryArgument) (J : ℝ), 0 < J →
      (∀ d ∈ S, norm d ≤ J) → (∑ d ∈ S, norm d^(-1:ℝ)) ≤ C*J^ε := by
  obtain ⟨C,hC,hb⟩ := primary_finite_harmonic_power hε
  refine ⟨C,hC,?_⟩
  intro S J hJ hS
  have hs := hb (S.image Subtype.val) J hJ
    (by rintro d hd; obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hd; exact x.property)
    (by rintro d hd; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hd; exact hS x hx)
  rw [Finset.sum_image] at hs
  · exact hs
  · intro x _ y _ hxy
    exact Subtype.ext hxy

lemma primary_argument_supported_sum {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      ∀ (S : Finset PrimaryArgument) (J : ℝ),
      (∀ h ∈ S, ∃ k : ℕ, h.val ∣ r^k) → (∀ h ∈ S, norm h ≤ J) →
      (∑ h ∈ S, norm h^(-δ)) ≤ C*norm r^ε := by
  obtain ⟨C,hC,hb⟩ := primary_supported_norm_sum hε hδ
  refine ⟨C,hC,?_⟩
  intro r hr S J hs hJ
  have h := hb r hr (S.image Subtype.val) J
    (by rintro d hd; obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hd; exact x.property)
    (by rintro d hd; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hd; exact hs x hx)
    (by rintro d hd; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hd; exact hJ x hx)
  rw [Finset.sum_image] at h
  · exact h
  · intro x _ y _ hxy
    exact Subtype.ext hxy

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrefixMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first retained-block majorant is summable with arbitrary small
powers of its finite norm cutoff and its squarefree level. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_divisor_card_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      ((metaplecticPrimaryDivisors r).card:ℝ) ≤ C*norm r^ε := by
  obtain ⟨C,hC,hb⟩ := primary_divisor_card_small_power hε
  refine ⟨C,hC,?_⟩
  intro r hr
  exact hb (primaryElementBall (norm r))
    (fun d hd => (mem_primaryElementBall.mp hd).1) r (primary_ne_zero hr)

theorem metaplectic_first_prefix_mass {ε ρ : ℝ} (hε : 0 < ε)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      ∀ (P : Finset (MetaplecticDyadPrefix r)) (J : ℝ), 0 < J →
      (∀ p ∈ P, ∃ k : ℕ, p.2.2.2.2.val ∣ r^k) →
      (∀ p ∈ P, norm p.1 ≤ J ∧ norm p.2.2.2.2 ≤ J) →
      (∑ p ∈ P, norm p.1^(-1:ℝ)*ρ^p.2.1*norm p.2.2.2.2^(-(1/2):ℝ)) ≤
        C*J^ε*norm r^(2*ε) := by
  obtain ⟨A,hA,harm⟩ := primary_argument_harmonic hε
  obtain ⟨B,hB,hdiv⟩ := metaplectic_divisor_card_power hε
  obtain ⟨E,hE,hsup⟩ := primary_argument_supported_sum hε (by norm_num : (0:ℝ) < 1/2)
  let U : ℝ := Nat.card (Eisensteinˣ)
  let K : ℝ := A*(1-ρ)⁻¹*U*B*E
  have hden : 0 < 1-ρ := sub_pos.mpr hρ1
  have hK : 0 ≤ K := by dsimp [K,U]; positivity
  refine ⟨K+1,by positivity,?_⟩
  intro r hr P J hJ hsupport hsize
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hd := harm (P.image Prod.fst) J hJ (by
    intro d hd
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
    exact (hsize p hp).1)
  have hh := hsup r hr (P.image (fun p => p.2.2.2.2)) J (by
    intro d hd
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
    exact hsupport p hp) (by
    intro d hd
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
    exact (hsize p hp).2)
  have hk : (∑ k ∈ P.image (fun p => p.2.1), ρ^k) ≤ (1-ρ)⁻¹ := by
    have hg := hasSum_geometric_of_lt_one hρ0 hρ1
    rw [←hg.tsum_eq]
    exact hg.summable.sum_le_tsum _ (fun k _ => pow_nonneg hρ0 k)
  have hhdiv := hdiv r hr
  have hp := metaplectic_prefix_product_bound P
    (fun d => norm d^(-1:ℝ)) (fun k => ρ^k) (fun d => norm d^(-(1/2):ℝ))
    (fun d => Real.rpow_nonneg (norm_nonneg d) _)
    (fun k => pow_nonneg hρ0 k) (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  calc
    _ ≤ (∑ d ∈ P.image Prod.fst, norm d^(-1:ℝ))*
        (∑ k ∈ P.image (fun p => p.2.1), ρ^k)*U*
        ((metaplecticPrimaryDivisors r).card:ℝ)*
        (∑ h ∈ (P.image (fun p => p.2.2.2.2) : Finset PrimaryArgument),
          norm h^(-(1/2):ℝ)) := hp
    _ ≤ (A*J^ε)*(1-ρ)⁻¹*U*(B*norm r^ε)*(E*norm r^ε) := by
      gcongr
      exact Finset.sum_nonneg (fun h _ => Real.rpow_nonneg (norm_nonneg h) _)
    _ = K*J^ε*norm r^(2*ε) := by
      rw [show 2*ε = ε+ε by ring,Real.rpow_add hR]
      dsimp [K]
      ring
    _ ≤ (K+1)*J^ε*norm r^(2*ε) := by
      gcongr
      linarith

/-- The second scalar weight is smaller than the first one termwise; the
same arbitrary small-power estimate therefore suffices for the application. -/
theorem metaplectic_second_prefix_mass {ε ρ : ℝ} (hε : 0 < ε)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      ∀ (P : Finset (MetaplecticDyadPrefix r)) (J : ℝ), 0 < J →
      (∀ p ∈ P, ∃ k : ℕ, p.2.2.2.2.val ∣ r^k) →
      (∀ p ∈ P, norm p.1 ≤ J ∧ norm p.2.2.2.2 ≤ J) →
      (∑ p ∈ P, norm p.1^(-(5/2):ℝ)*ρ^p.2.1*norm p.2.2.2.2^(-(3/2):ℝ)) ≤
        C*J^ε*norm r^(2*ε) := by
  obtain ⟨C,hC,hb⟩ := metaplectic_first_prefix_mass hε hρ0 hρ1
  refine ⟨C,hC,?_⟩
  intro r hr P J hJ hsupport hsize
  apply (Finset.sum_le_sum ?_).trans (hb r hr P J hJ hsupport hsize)
  intro p hp
  have hd := Real.rpow_le_rpow_of_exponent_le (one_le_norm (primary_ne_zero p.1.property))
    (by norm_num : (-(5/2):ℝ) ≤ -1)
  have hh := Real.rpow_le_rpow_of_exponent_le (one_le_norm (primary_ne_zero p.2.2.2.2.property))
    (by norm_num : (-(3/2):ℝ) ≤ -(1/2))
  exact mul_le_mul (mul_le_mul_of_nonneg_right hd (pow_nonneg hρ0 p.2.1)) hh
    (Real.rpow_nonneg (norm_nonneg p.2.2.2.2) _)
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg p.1) _) (pow_nonneg hρ0 p.2.1))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrefixBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing both actual retained-block amplitudes over all supported
prefixes, with no coefficient or support-count estimate left as an assumption. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma two_positive_parts {A B s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s) :
    A+B*s ≤ (A+B)*(1+s) := by
  nlinarith [mul_nonneg hA hs]

theorem metaplectic_prefix_amplitude_sum {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r →
      ∀ (P : Finset (MetaplecticDyadPrefix r)) (J : ℝ), 0 < J →
      (∀ p ∈ P, ∃ k : ℕ, p.2.2.2.2.val ∣ r^k) →
      (∀ p ∈ P, norm p.1 ≤ J ∧ norm p.2.2.2.2 ≤ J) →
      ∀ C : ℝ, 0 ≤ C → ∀ I T : ℝ,
      (∑ p ∈ P, metaplecticPrefixAmplitude r C p/Real.sqrt (norm r)*
        (1+Real.sqrt (2*(I/metaplecticFreeScale p)/T))) ≤
          D*C*J^ε*norm r^(2*ε)*(1+Real.sqrt (2*I/(norm r*T))) := by
  obtain ⟨A,hA,ha⟩ := metaplectic_first_prefix_mass (ρ := (3:ℝ)^(-1/6:ℝ)) hε
    (Real.rpow_nonneg (by norm_num) (-1/6:ℝ))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num : (-1/6:ℝ) < 0))
  obtain ⟨B,hB,hb⟩ := metaplectic_second_prefix_mass (ρ := (3:ℝ)^(-2/3:ℝ)) hε
    (Real.rpow_nonneg (by norm_num) (-2/3:ℝ))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num : (-2/3:ℝ) < 0))
  refine ⟨Real.sqrt 3*A+3*B,by positivity,?_⟩
  intro r hr P J hJ hsupport hsize C hC I T
  have hR := norm_nonneg r
  let w1 := fun p : MetaplecticDyadPrefix r =>
    norm p.1^(-1:ℝ)*((3:ℝ)^(-1/6:ℝ))^p.2.1*norm p.2.2.2.2^(-(1/2):ℝ)
  let w2 := fun p : MetaplecticDyadPrefix r =>
    norm p.1^(-(5/2):ℝ)*((3:ℝ)^(-2/3:ℝ))^p.2.1*norm p.2.2.2.2^(-(3/2):ℝ)
  let s := Real.sqrt (2*I/(norm r*T))
  have h1 := ha r hr P J hJ hsupport hsize
  have h2 := hb r hr P J hJ hsupport hsize
  have hp (p : MetaplecticDyadPrefix r) :
      metaplecticPrefixAmplitude r C p/Real.sqrt (norm r)*
        (1+Real.sqrt (2*(I/metaplecticFreeScale p)/T)) ≤
          C*Real.sqrt 3*w1 p+C*3*s*w2 p := by
    have hf := metaplectic_prefix_first_amplitude hr hC p
    have hs := metaplectic_prefix_second_amplitude hr hC p I T
    calc
      _ = metaplecticPrefixAmplitude r C p/Real.sqrt (norm r)+
          metaplecticPrefixAmplitude r C p/Real.sqrt (norm r)*
            Real.sqrt (2*(I/metaplecticFreeScale p)/T) := by ring
      _ ≤ _ := add_le_add hf hs
      _ = _ := by dsimp [w1,w2,s]; ring
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hn : 0 ≤ C*J^ε*norm r^(2*ε) := by positivity
  calc
    _ ≤ ∑ p ∈ P, (C*Real.sqrt 3*w1 p+C*3*s*w2 p) := Finset.sum_le_sum (fun p _ => hp p)
    _ = C*Real.sqrt 3*(∑ p ∈ P, w1 p)+C*3*s*(∑ p ∈ P, w2 p) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
    _ ≤ C*Real.sqrt 3*(A*J^ε*norm r^(2*ε))+C*3*s*(B*J^ε*norm r^(2*ε)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
        (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = (C*J^ε*norm r^(2*ε))*(Real.sqrt 3*A+(3*B)*s) := by ring
    _ ≤ (C*J^ε*norm r^(2*ε))*((Real.sqrt 3*A+3*B)*(1+s)) :=
      mul_le_mul_of_nonneg_left (two_positive_parts (by positivity) (by positivity) hs0) hn
    _ = _ := by dsimp [s]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrefixCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original retained-frequency cutoff also bounds the d and supported
cube-factor projections used in the arithmetic prefix sums. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_prefix_cube_dvd {r : Eisenstein} (p : MetaplecticDyadPrefix r)
    {w : Eisenstein} (hw : w ≠ 0) :
    p.2.2.2.2.val ∣ (metaplecticPrefixArgument r p.2 w).val := by
  rw [metaplecticPrefixArgument,metaplecticFreeArgument_val _ _ _ _ hw]
  refine ⟨lambdaE^p.2.1*p.2.2.1.val*p.2.2.2.1.val*w*p.2.2.2.2.val^2,?_⟩
  dsimp only [metaplecticDivisorPrimary]
  ring

lemma metaplectic_prefix_cutoff {r : Eisenstein}
    (S : Finset (MetaplecticRetainedCode r)) {I : ℝ}
    (hS : ∀ z ∈ S, metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I) :
    ∀ p ∈ S.image metaplecticCodePrefix,
      norm p.1 ≤ 3*I ∧ norm p.2.2.2.2 ≤ 3*I := by
  intro p hp
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
  have hbound := metaplecticDualNorm_coordinate_bound _ (hS z hz)
  refine ⟨hbound.2,?_⟩
  have hdiv := metaplectic_prefix_cube_dvd (r := r) (metaplecticCodePrefix z)
    (primary_ne_zero z.2.2.property)
  have hn := norm_le_of_dvd (metaplecticRetainedDecode r z).1.property hdiv
  exact hn.trans hbound.1

lemma metaplectic_prefix_support {r : Eisenstein}
    (S : Finset (MetaplecticRetainedCode r))
    (hS : ∀ z ∈ S, ∃ k : ℕ, z.2.1.2.2.2.val ∣ r^k) :
    ∀ p ∈ S.image metaplecticCodePrefix, ∃ k : ℕ, p.2.2.2.2.val ∣ r^k := by
  intro p hp
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
  exact hS z hz

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticSupportedMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete coded norm-block mean. All supported prefixes are summed,
using only the actual coefficient bound and Montgomery--Vaughan. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_supported_block_mean {ε M : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a : Eisenstein → MetaplecticDualArgument → ℂ)
      (C : ℝ), 0 ≤ C → ∀ r : Eisenstein, primary r →
      ∀ S : Finset (MetaplecticRetainedCode r),
      (∀ z ∈ S, IsCoprime z.2.2.val r) →
      (∀ z ∈ S, ∃ k : ℕ, z.2.1.2.2.2.val ∣ r^k) →
      (∀ z ∈ S, ‖a r (metaplecticRetainedDecode r z).1‖ ≤
        C*3^((max ((z.2.1.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm z.2.1.2.2.2)) →
      ∀ I T : ℝ, 0 < I → 0 < T →
      (∀ z ∈ S, I/2 ≤ metaplecticDualNorm (metaplecticRetainedDecode r z) ∧
        metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I) →
      ∀ ℓ : ℤ, ∀ τ : ℝ,
      ((∫ t in T..2*T, ‖∑ z ∈ S,
        metaplecticNormalizedDualCoefficient a r ℓ (metaplecticRetainedDecode r z)*
          mellinPhase (τ-t) (metaplecticDualNorm (metaplecticRetainedDecode r z))‖)/T)/
        Real.sqrt (norm r) ≤
          D*C*(3*I)^(3*ε/2)*norm r^(2*ε)*(1+Real.sqrt (2*I/(norm r*T))) := by
  obtain ⟨B,hB,hmean⟩ := metaplectic_code_mean hε hMV hM
  obtain ⟨E,hE,hsum⟩ := metaplectic_prefix_amplitude_sum hε
  let A := Real.sqrt (M*B)+1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A*E,mul_pos hA hE,?_⟩
  intro a C hC r hr S hcop hsupport hcoef I T hI hT hdyad ℓ τ
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hRroot := Real.sqrt_pos.mpr hR
  have hJ : 0 < 3*I := by positivity
  let P := S.image metaplecticCodePrefix
  let q := fun p : MetaplecticDyadPrefix r => metaplecticPrefixAmplitude r C p/Real.sqrt (norm r)*
    (1+Real.sqrt (2*(I/metaplecticFreeScale p)/T))
  have hq (p : MetaplecticDyadPrefix r) : 0 ≤ q p := by
    dsimp [q]
    exact mul_nonneg (div_nonneg (metaplecticPrefixAmplitude_nonneg hr hC p) hRroot.le)
      (by positivity)
  have hjp (p : MetaplecticDyadPrefix r) :
      (I/metaplecticFreeScale p)^(ε/2) ≤ (3*I)^(ε/2) :=
    Real.rpow_le_rpow (div_nonneg hI.le (metaplecticFreeScale_pos p).le)
      (metaplectic_free_length_upper p hI.le) (by positivity)
  have hc := hmean a C hC r hr S hcop hcoef I T hT hdyad ℓ τ
  have hs := hsum r hr P (3*I) hJ (metaplectic_prefix_support S hsupport)
    (metaplectic_prefix_cutoff S (fun z hz => (hdyad z hz).2)) C hC I T
  calc
    _ ≤ (∑ p ∈ P, Real.sqrt (M*B)*(I/metaplecticFreeScale p)^(ε/2)*
        metaplecticPrefixAmplitude r C p*(1+Real.sqrt (2*(I/metaplecticFreeScale p)/T)))/
          Real.sqrt (norm r) := div_le_div_of_nonneg_right hc hRroot.le
    _ = ∑ p ∈ P, Real.sqrt (M*B)*(I/metaplecticFreeScale p)^(ε/2)*q p := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [q]
      ring
    _ ≤ ∑ p ∈ P, A*(3*I)^(ε/2)*q p := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_right _ (hq p)
      exact mul_le_mul (by dsimp [A]; linarith [Real.sqrt_nonneg (M*B)]) (hjp p)
        (Real.rpow_nonneg (div_nonneg hI.le (metaplecticFreeScale_pos p).le) _) hA.le
    _ = A*(3*I)^(ε/2)*(∑ p ∈ P, q p) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*(3*I)^(ε/2)*(E*C*(3*I)^ε*norm r^(2*ε)*
        (1+Real.sqrt (2*I/(norm r*T)))) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [show 3*ε/2 = ε/2+ε by ring,Real.rpow_add hJ]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticActualBlockMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete retained norm-block mean for the original coefficients.
The supported parametrization and every free coefficient estimate are
constructed from the precisely stated published Voronoi coefficient bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_actual_norm_block_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (I T : ℝ),
      0 < I → 0 < T →
      (∀ nd ∈ S, I/2 ≤ metaplecticDualNorm nd ∧ metaplecticDualNorm nd ≤ I) →
      ∀ (ℓ : ℤ) (τ : ℝ),
      ((∫ t in T..2*T, ‖∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
        mellinPhase (τ-t) (metaplecticDualNorm nd)‖)/T)/Real.sqrt (norm r) ≤
          D*(3*I)^(3*ε/2)*norm r^(2*ε)*(1+Real.sqrt (2*I/(norm r*T))) := by
  obtain ⟨C,hC,hcodes⟩ := metaplectic_retained_support_partition ha
  obtain ⟨D,hD,hmean⟩ := metaplectic_supported_block_mean hε hMV hM
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro r hr hsr S I T hI hT hdyad ℓ τ
  obtain ⟨U,hU,he⟩ := hcodes r hr hsr S
  have huc (z : MetaplecticRetainedCode r) (hz : z ∈ U) :
      IsCoprime z.2.2.val r := (hU z hz).2.2.1
  have hus (z : MetaplecticRetainedCode r) (hz : z ∈ U) :
      ∃ k : ℕ, z.2.1.2.2.2.val ∣ r^k := (hU z hz).2.1
  have hub (z : MetaplecticRetainedCode r) (hz : z ∈ U) :
      ‖a r (metaplecticRetainedDecode r z).1‖ ≤
        C*3^((max ((z.2.1.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm z.2.1.2.2.2) :=
    (hU z hz).2.2.2.2
  have hud (z : MetaplecticRetainedCode r) (hz : z ∈ U) :
      I/2 ≤ metaplecticDualNorm (metaplecticRetainedDecode r z) ∧
        metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I :=
    hdyad _ (hU z hz).1
  have hb := hmean a C hC.le r hr U huc hus hub I T hI hT hud ℓ τ
  have hid (t : ℝ) :
      (∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
        mellinPhase (τ-t) (metaplecticDualNorm nd)) =
      ∑ z ∈ U, metaplecticNormalizedDualCoefficient a r ℓ (metaplecticRetainedDecode r z)*
        mellinPhase (τ-t) (metaplecticDualNorm (metaplecticRetainedDecode r z)) := he ℓ (τ-t)
  simp_rw [hid]
  exact hb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticNormDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical finite norm-dyad partition of the retained Voronoi pairs.
The integral frequency d³n has norm exactly three times N(d³ν). -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticIntegralFrequency_ne_zero (nd : MetaplecticDualArgument × PrimaryArgument) :
    metaplecticIntegralFrequency nd ≠ 0 :=
  mul_ne_zero (pow_ne_zero 3 (primary_ne_zero nd.2.property)) nd.1.property

lemma norm_metaplecticIntegralFrequency (nd : MetaplecticDualArgument × PrimaryArgument) :
    norm (metaplecticIntegralFrequency nd) = 3*metaplecticDualNorm nd := by
  have hn : norm (metaplecticIntegralFrequency nd) = norm nd.2^3*norm nd.1 := by
    change Complex.normSq ((nd.2:ℂ)^3*(nd.1.val:ℂ)) = _
    rw [Complex.normSq_mul,map_pow]
    rfl
  rw [hn]
  unfold metaplecticDualNorm
  rw [metaplectic_frequency_norm_numerator]
  ring

lemma metaplecticNormDyadLength_pos (j : ℕ) : 0 < metaplecticNormDyadLength j := by
  unfold metaplecticNormDyadLength
  positivity

lemma metaplectic_norm_dyad_bounds
    {S : Finset (MetaplecticDualArgument × PrimaryArgument)} {j : ℕ}
    {nd : MetaplecticDualArgument × PrimaryArgument} (hnd : nd ∈ metaplecticNormDyad S j) :
    metaplecticNormDyadLength j/2 ≤ metaplecticDualNorm nd ∧
      metaplecticDualNorm nd ≤ metaplecticNormDyadLength j := by
  have hmem : metaplecticIntegralFrequency nd ∈ frequencyDyad j :=
    mem_frequencyDyad.mpr ⟨metaplecticIntegralFrequency_ne_zero nd,
      (Finset.mem_filter.mp hnd).2⟩
  have hb := frequencyDyad_norm hmem
  rw [norm_metaplecticIntegralFrequency] at hb
  unfold metaplecticNormDyadLength
  constructor <;> nlinarith [hb.1,hb.2]

lemma metaplectic_norm_dyad_partition
    (S : Finset (MetaplecticDualArgument × PrimaryArgument))
    (F : MetaplecticDualArgument × PrimaryArgument → ℂ) :
    (∑ nd ∈ S, F nd) = ∑ j ∈ S.image metaplecticNormDyadIndex,
      ∑ nd ∈ metaplecticNormDyad S j, F nd := by
  unfold metaplecticNormDyad
  exact (Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image metaplecticNormDyadIndex)
    (g := metaplecticNormDyadIndex) (fun nd hnd => by
      simp only [Finset.mem_image]
      exact ⟨nd,hnd,rfl⟩) F).symm

lemma metaplectic_norm_dyad_length_le
    (S : Finset (MetaplecticDualArgument × PrimaryArgument)) {J : ℝ}
    (hS : ∀ nd ∈ S, metaplecticDualNorm nd ≤ J) {j : ℕ}
    (hj : j ∈ S.image metaplecticNormDyadIndex) : metaplecticNormDyadLength j ≤ 2*J := by
  obtain ⟨nd,hnd,rfl⟩ := Finset.mem_image.mp hj
  have hm : nd ∈ metaplecticNormDyad S (metaplecticNormDyadIndex nd) :=
    Finset.mem_filter.mpr ⟨hnd,rfl⟩
  have hb := (metaplectic_norm_dyad_bounds hm).1
  linarith [hS nd hnd]

lemma metaplectic_norm_dyad_count
    (S : Finset (MetaplecticDualArgument × PrimaryArgument)) {J : ℝ}
    (hS : ∀ nd ∈ S, metaplecticDualNorm nd ≤ J) :
    (S.image metaplecticNormDyadIndex).card ≤ Nat.log 2 ⌊3*J⌋₊+1 := by
  apply le_trans (Finset.card_le_card (show S.image metaplecticNormDyadIndex ⊆
    Finset.range (Nat.log 2 ⌊3*J⌋₊+1) from ?_))
    (by rw [Finset.card_range])
  intro j hj
  obtain ⟨nd,hnd,rfl⟩ := Finset.mem_image.mp hj
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  apply Nat.log_mono_right
  apply Nat.le_floor
  rw [normNat_cast,norm_metaplecticIntegralFrequency]
  linarith [hS nd hnd]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The whole actual retained polynomial, with its fixed cutoff, is
controlled by its canonical finite norm-dyad partition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma mean_norm_finset_sum_normalized {ι : Type*} (S : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ S, Continuous (f i))
    {T c B : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hB : ∀ i ∈ S, ((∫ t in T..2*T, ‖f i t‖)/T)/c ≤ B) :
    ((∫ t in T..2*T, ‖∑ i ∈ S, f i t‖)/T)/c ≤ (S.card:ℝ)*B := by
  have hh := mean_norm_finset_sum_le S f hf hT (fun _ => B*c)
    (fun i hi => (div_le_iff₀ hc).mp (hB i hi))
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  apply (div_le_iff₀ hc).mpr
  nlinarith only [hh]

theorem metaplectic_actual_retained_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (J T : ℝ),
      0 < J → 0 < T → (∀ nd ∈ S, metaplecticDualNorm nd ≤ J) →
      ∀ (ℓ : ℤ) (τ : ℝ),
      ((∫ t in T..2*T, ‖∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
        mellinPhase (τ-t) (metaplecticDualNorm nd)‖)/T)/Real.sqrt (norm r) ≤
          ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
            (1+Real.sqrt (4*J/(norm r*T))) := by
  obtain ⟨D,hD,hb⟩ := metaplectic_actual_norm_block_mean ha hε hMV hM
  refine ⟨D,hD,?_⟩
  intro r hr hsr S J T hJ hT hS ℓ τ
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hRroot := Real.sqrt_pos.mpr hR
  let P := S.image metaplecticNormDyadIndex
  let f := fun j : ℕ => fun t : ℝ => ∑ nd ∈ metaplecticNormDyad S j,
    metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase (τ-t) (metaplecticDualNorm nd)
  let B := D*(6*J)^(3*ε/2)*norm r^(2*ε)*(1+Real.sqrt (4*J/(norm r*T)))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hf (j : ℕ) : Continuous (f j) := by
    apply continuous_finsetSum
    intro nd hnd
    apply continuous_const.mul
    unfold mellinPhase
    fun_prop
  have hblock (j : ℕ) (hj : j ∈ P) : ((∫ t in T..2*T, ‖f j t‖)/T)/Real.sqrt (norm r) ≤ B := by
    have hI := metaplecticNormDyadLength_pos j
    have hIJ := metaplectic_norm_dyad_length_le S hS hj
    have hx := hb r hr hsr (metaplecticNormDyad S j) (metaplecticNormDyadLength j) T hI hT
      (fun nd hnd => metaplectic_norm_dyad_bounds hnd) ℓ τ
    apply hx.trans
    have hp : (3*metaplecticNormDyadLength j)^(3*ε/2) ≤ (6*J)^(3*ε/2) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    have hs : Real.sqrt (2*metaplecticNormDyadLength j/(norm r*T)) ≤
        Real.sqrt (4*J/(norm r*T)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) (mul_pos hR hT).le)
    dsimp [B]
    gcongr
  have he (t : ℝ) : (∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
      mellinPhase (τ-t) (metaplecticDualNorm nd)) = ∑ j ∈ P, f j t :=
    metaplectic_norm_dyad_partition S (fun nd =>
      metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase (τ-t) (metaplecticDualNorm nd))
  have hh := mean_norm_finset_sum_normalized P f (fun j _ => hf j) hT hRroot hblock
  simp_rw [he]
  apply hh.trans
  calc
    _ ≤ ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*B := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (metaplectic_norm_dyad_count S hS)) hB
    _ = _ := by dsimp [B]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete retained frequency estimate passes through the actual
critical-line Mellin kernel with its common, integrable weight. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_actual_retained_kernel
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (J T : ℝ),
      0 < J → 0 < T → (∀ nd ∈ S, metaplecticDualNorm nd ≤ J) →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ), HasCompactSupport W → tsupport W ⊆ Ioi 0 →
      ContDiff ℝ ∞ W → ∀ c : ℝ,
      ((∫ t in T..2*T, ‖∫ τ : ℝ, metaplecticCriticalKernel ℓ W c
        (fun u => ∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
          mellinPhase u (metaplecticDualNorm nd)) τ t‖)/T)/Real.sqrt (norm r) ≤
          ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
            (1+Real.sqrt (4*J/(norm r*T)))*
              (∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) := by
  obtain ⟨D,hD,hb⟩ := metaplectic_actual_retained_mean ha hε hMV hM
  refine ⟨D,hD,?_⟩
  intro r hr hsr S J T hJ hT hS ℓ W hW hpos hsm c
  have hR := Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hr))
  let B := ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
    (1+Real.sqrt (4*J/(norm r*T)))
  let P := fun u : ℝ => ∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
    mellinPhase u (metaplecticDualNorm nd)
  have hP : Continuous P := by
    apply continuous_finsetSum
    intro nd hnd
    apply continuous_const.mul
    unfold mellinPhase
    fun_prop
  have hmean (τ : ℝ) : (∫ t in T..2*T, ‖P (τ-t)‖)/T ≤ B*Real.sqrt (norm r) :=
    (div_le_iff₀ hR).mp (hb r hr hsr S J T hJ hT hS ℓ τ)
  have hk := metaplectic_critical_kernel_mean ℓ W hW hpos hsm c P hP hT hmean
  apply (div_le_iff₀ hR).mpr
  calc
    _ ≤ (B*Real.sqrt (norm r))*(∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) := hk
    _ = _ := by dsimp [B]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedEstimate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal retained Voronoi contribution, including its published
prefactor. The conductor square roots cancel exactly before any power
loss is absorbed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_critical_scale {X R : ℝ} (hX : 0 < X) (hR : 0 < R) :
    Real.sqrt ((2*Real.pi)^4*X/R^2) =
      (2*Real.pi)^2*Real.sqrt X/R := by
  rw [Real.sqrt_div (mul_nonneg (by positivity) hX.le),
    Real.sqrt_mul (by positivity),Real.sqrt_sq hR.le,
    show (2*Real.pi)^4 = ((2*Real.pi)^2)^2 by ring,
    Real.sqrt_sq (sq_nonneg _)]

lemma metaplectic_critical_prefactor {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) {X : ℝ} (hX : 0 < X) :
    (‖metaplecticPrefactor r ℓ‖*
      Real.sqrt ((2*Real.pi)^4*X/norm r^2)*(1/(2*Real.pi)))*Real.sqrt (norm r) =
        Real.sqrt X/(3^(7/2:ℝ)*(2*Real.pi)) := by
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  rw [norm_metaplecticPrefactor (primary_ne_zero hr),metaplectic_critical_scale hX hR]
  have hs := Real.sq_sqrt hR.le
  have h3 : (3:ℝ)^(7/2:ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hp : 2*Real.pi ≠ 0 := by positivity
  calc
    _ = (Real.sqrt X/(3^(7/2:ℝ)*(2*Real.pi)))*((Real.sqrt (norm r))^2/norm r) := by
      field_simp
    _ = _ := by rw [hs,div_self hR.ne',mul_one]

/-- Mean value of the actual retained dual contribution. Only the literal
published theta-coefficient bound and ordinary Montgomery--Vaughan are
used for its arithmetic mean; the shifted Gamma inputs move the actual
transform to the critical line. -/
theorem metaplectic_retained_voronoi_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ), HasCompactSupport W → tsupport W ⊆ Ioi 0 →
      ContDiff ℝ ∞ W → ∀ A X J T : ℝ, 0 ≤ A → 0 < X → 0 < J → 0 < T →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A) →
      (∫ t in T..2*T, ‖metaplecticPrefactor r ℓ*
        ∑ nd ∈ metaplecticDualBall J,
          metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X nd‖)/T ≤
        Real.sqrt X/(3^(7/2:ℝ)*(2*Real.pi))*
          (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
            (1+Real.sqrt (4*J/(norm r*T)))*
              (∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖)) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_actual_retained_kernel ha hε hMV hM
  refine ⟨D,hD,?_⟩
  intro r hr hsr ℓ W hW hpos hsm A X J T hA hX hJ hT hm hp
  let c := (2*Real.pi)^4*X/norm r^2
  let K := fun t : ℝ => ∫ τ : ℝ, metaplecticCriticalKernel ℓ W c
    (fun u => ∑ nd ∈ metaplecticDualBall J,
      metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase u (metaplecticDualNorm nd)) τ t
  let Q := ‖metaplecticPrefactor r ℓ‖*Real.sqrt c*(1/(2*Real.pi))
  let B := (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
    (1+Real.sqrt (4*J/(norm r*T)))*
      (∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖))
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hb : ((∫ t in T..2*T, ‖K t‖)/T)/Real.sqrt (norm r) ≤ B :=
    hbound r hr hsr (metaplecticDualBall J) J T hJ hT
      (fun nd hnd => (mem_metaplecticDualBall nd J).mp hnd) ℓ W hW hpos hsm c
  have he (t : ℝ) : ‖metaplecticPrefactor r ℓ*
      ∑ nd ∈ metaplecticDualBall J,
        metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X nd‖ = Q*‖K t‖ := by
    rw [metaplectic_retained_critical a hr ℓ W hW hpos hsm hA hX J t hm hp]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (show (0:ℝ) ≤ 1/(2*Real.pi) by positivity)]
    dsimp [Q,K,c]
    ring
  calc
    _ = Q*((∫ t in T..2*T, ‖K t‖)/T) := by
      simp_rw [he]
      rw [intervalIntegral.integral_const_mul]
      ring
    _ ≤ Q*(B*Real.sqrt (norm r)) :=
      mul_le_mul_of_nonneg_left ((div_le_iff₀ (Real.sqrt_pos.mpr hR)).mp hb) hQ
    _ = _ := by
      rw [show Q*(B*Real.sqrt (norm r)) = (Q*Real.sqrt (norm r))*B by ring,
        show Q*Real.sqrt (norm r) = Real.sqrt X/(3^(7/2:ℝ)*(2*Real.pi)) from
          metaplectic_critical_prefactor hr ℓ hX]

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

/-- The exponent used in the coefficient estimate can be chosen before
all conductor and length parameters. -/
theorem metaplectic_retained_loss_small_power {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ Y R J : ℝ, 1 ≤ Y → 0 < R → 1 ≤ J →
      R ≤ Y^B → J ≤ Y^B →
      ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*(6*J)^(3*ε/2)*R^(2*ε) ≤ C*Y^η := by
  let ε := η/(5*(B+1))
  have hε : 0 < ε := div_pos hη (by positivity)
  obtain ⟨A,hA,ha⟩ := metaplectic_dyad_count_small_power hε
  refine ⟨ε,A*6^(3*ε/2),hε,mul_pos hA (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  intro Y R J hY hR hJ hRY hJY
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have he : B*(5*ε/2)+B*(2*ε) ≤ η := by
    have hh := (div_mul_cancel₀ η (show (5*(B+1):ℝ) ≠ 0 by positivity))
    change ε*(5*(B+1)) = η at hh
    nlinarith
  have hj : J^(5*ε/2) ≤ Y^(B*(5*ε/2)) := by
    apply (Real.rpow_le_rpow hJp.le hJY (by positivity)).trans_eq
    exact (Real.rpow_mul hYp.le _ _).symm
  have hr : R^(2*ε) ≤ Y^(B*(2*ε)) := by
    apply (Real.rpow_le_rpow hR.le hRY (by positivity)).trans_eq
    exact (Real.rpow_mul hYp.le _ _).symm
  calc
    _ ≤ (A*J^ε)*(6*J)^(3*ε/2)*R^(2*ε) := by gcongr; exact ha J hJ
    _ = (A*6^(3*ε/2))*(J^(5*ε/2)*R^(2*ε)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 6) hJp.le]
      have hx : J^ε*J^(3*ε/2) = J^(5*ε/2) := by
        rw [←Real.rpow_add hJp]
        congr 1
        ring
      rw [show A*J^ε*(6^(3*ε/2)*J^(3*ε/2))*R^(2*ε) =
        (A*6^(3*ε/2))*(J^ε*J^(3*ε/2)*R^(2*ε)) by ring,hx]
    _ ≤ (A*6^(3*ε/2))*(Y^(B*(5*ε/2))*Y^(B*(2*ε))) := by gcongr
    _ = (A*6^(3*ε/2))*Y^(B*(5*ε/2)+B*(2*ε)) := by rw [Real.rpow_add hYp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY he) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLongGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The natural dual cutoff in the long-primal branch gives precisely
the quarter-conductor, square-root-height factor. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_long_natural_length {R T X : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hX : 0 < X)
    (hlong : Real.sqrt R*T^2 ≤ X) :
    R^2*T^4/X ≤ R*Real.sqrt R*T^2 := by
  apply (div_le_iff₀ hX).mpr
  have hs := Real.sq_sqrt hR.le
  have hh := mul_le_mul_of_nonneg_left hlong
    (show 0 ≤ R*Real.sqrt R*T^2 by positivity)
  have he : R*Real.sqrt R*T^2*(Real.sqrt R*T^2) = R^2*T^4 := by
    calc
      _ = R*(Real.sqrt R)^2*T^4 := by ring
      _ = _ := by rw [hs]; ring
  simpa only [he] using hh

lemma metaplectic_long_cutoff {Y R T X δ : ℝ}
    (hY : 1 ≤ Y) (hR : 1 ≤ R) (hT : 1 ≤ T) (hX : 0 < X)
    (hδ : 0 ≤ δ) (hlong : Real.sqrt R*T^2 ≤ X) :
    max 1 (Y^δ*(R^2*T^4/X)) ≤ 2*Y^δ*R*Real.sqrt R*T^2 := by
  have hYδ : 1 ≤ Y^δ := Real.one_le_rpow hY hδ
  have hRs : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
  have hT2 : 1 ≤ T^2 := one_le_pow₀ hT
  have hbase : 1 ≤ Y^δ*R*Real.sqrt R*T^2 := by
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hYδ hR) hRs) hT2
  have hnat := metaplectic_long_natural_length (zero_lt_one.trans_le hR)
    (zero_lt_one.trans_le hT) hX hlong
  apply max_le
  · nlinarith only [hbase]
  · calc
      _ ≤ Y^δ*(R*Real.sqrt R*T^2) :=
        mul_le_mul_of_nonneg_left hnat (Real.rpow_nonneg (zero_le_one.trans hY) _)
      _ ≤ _ := by nlinarith only [hbase]

lemma metaplectic_long_sqrt_factor {Y R T J δ : ℝ}
    (hY : 1 ≤ Y) (hR : 1 ≤ R) (hT : 1 ≤ T) (hδ : 0 ≤ δ)
    (hJ : J ≤ 2*Y^δ*R*Real.sqrt R*T^2) :
    1+Real.sqrt (4*J/(R*T)) ≤ 4*Y^(δ/2)*R^(1/4:ℝ)*Real.sqrt T := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let H := Y^(δ/2)*R^(1/4:ℝ)*Real.sqrt T
  have hH : 1 ≤ H := by
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hY (by positivity))
      (Real.one_le_rpow hR (by norm_num))) (Real.one_le_sqrt.mpr hT)
  have hHsq : H^2 = Y^δ*Real.sqrt R*T := by
    dsimp [H]
    rw [mul_pow,mul_pow,Real.sq_sqrt hTp.le,
      ←Real.rpow_mul_natCast hYp.le,←Real.rpow_mul_natCast hRp.le]
    norm_num only [Nat.cast_ofNat]
    rw [show δ/2*2 = δ by ring,←Real.sqrt_eq_rpow]
  have harg : 4*J/(R*T) ≤ 8*H^2 := by
    apply (div_le_iff₀ (mul_pos hRp hTp)).mpr
    rw [hHsq]
    nlinarith only [hJ]
  have hs : Real.sqrt (4*J/(R*T)) ≤ 3*H := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 3*H)).mpr
    nlinarith only [harg,sq_nonneg H]
  have hout : 1+Real.sqrt (4*J/(R*T)) ≤ 4*H := by linarith
  simpa only [H,mul_assoc] using hout

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticNaturalCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One height-independent cutoff serves both the rapid-tail estimate
and the retained mean, with all polynomial scale bounds derived. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplecticNaturalCutoff_ge_one (Y R T X δ : ℝ) :
    1 ≤ metaplecticNaturalCutoff Y R T X δ := le_max_left _ _

lemma metaplecticNaturalCutoff_ratio {Y R T X δ : ℝ}
    (hY : 0 < Y) :
    (R^2*T^4/X)/metaplecticNaturalCutoff Y R T X δ ≤ Y^(-δ) := by
  have hJ : 0 < metaplecticNaturalCutoff Y R T X δ :=
    zero_lt_one.trans_le (metaplecticNaturalCutoff_ge_one _ _ _ _ _)
  apply (div_le_iff₀ hJ).mpr
  have hh := mul_le_mul_of_nonneg_left
    (show Y^δ*(R^2*T^4/X) ≤ metaplecticNaturalCutoff Y R T X δ from le_max_right _ _)
    (Real.rpow_nonneg hY.le (-δ))
  have he : Y^(-δ)*Y^δ = 1 := by rw [←Real.rpow_add hY]; simp
  simpa only [←mul_assoc,he,one_mul] using hh

lemma metaplectic_natural_length_polynomial {Y R T X B : ℝ}
    (hY : 1 ≤ Y) (hR : 0 < R) (hT : 0 < T)
    (hRB : R ≤ Y^B) (hTB : T ≤ Y^B) (hXB : Y^(-B) ≤ X) :
    R^2*T^4/X ≤ Y^(7*B) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hXp : 0 < X := (Real.rpow_pos_of_pos hYp (-B)).trans_le hXB
  have hXinv : 0 ≤ X^(-1:ℝ) := Real.rpow_nonneg hXp.le _
  have hr : R^2 ≤ Y^(2*B) := by
    apply (pow_le_pow_left₀ hR.le hRB 2).trans_eq
    rw [←Real.rpow_natCast,←Real.rpow_mul hYp.le]
    congr 1
    ring
  have ht : T^4 ≤ Y^(4*B) := by
    apply (pow_le_pow_left₀ hT.le hTB 4).trans_eq
    rw [←Real.rpow_natCast,←Real.rpow_mul hYp.le]
    congr 1
    ring
  have hx : X^(-1:ℝ) ≤ Y^B := by
    apply (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hYp _) hXB (by norm_num)).trans_eq
    rw [←Real.rpow_mul hYp.le]
    congr 1
    ring
  calc
    _ = R^2*T^4*X^(-1:ℝ) := by rw [Real.rpow_neg_one]; ring
    _ ≤ Y^(2*B)*Y^(4*B)*Y^B := by gcongr
    _ = _ := by rw [←Real.rpow_add hYp,←Real.rpow_add hYp]; congr 1; ring

lemma metaplecticNaturalCutoff_polynomial {Y R T X B δ : ℝ}
    (hY : 1 ≤ Y) (hR : 0 < R) (hT : 0 < T)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hRB : R ≤ Y^B) (hTB : T ≤ Y^B) (hXB : Y^(-B) ≤ X) :
    metaplecticNaturalCutoff Y R T X δ ≤ Y^(7*B+δ) := by
  apply max_le
  · exact Real.one_le_rpow hY (by positivity)
  · calc
      _ ≤ Y^δ*Y^(7*B) := mul_le_mul_of_nonneg_left
        (metaplectic_natural_length_polynomial hY hR hT hRB hTB hXB)
        (Real.rpow_nonneg (zero_le_one.trans hY) _)
      _ = _ := by rw [←Real.rpow_add (zero_lt_one.trans_le hY)]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTailScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The natural metaplectic dual cutoff and its exact exponent algebra. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplectic_tail_scale_identity {R X T J : ℝ}
    (hR : 0 < R) (hX : 0 < X) (hT : 0 < T) (hJ : 0 < J)
    (ε σ : ℝ) (m : ℕ) :
    R^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*J^(-(((m:ℝ)-1/2)-σ))*T^(4*m) =
      R^ε*T^2*(R^2*T^4/X)^σ*((R^2*T^4/X)/J)^(((m:ℝ)-1/2)-σ) := by
  let A : ℝ := (m:ℝ)-1/2
  let D : ℝ := R^2*T^4/X
  have hD : 0 < D := by dsimp [D]; positivity
  have hcut : D^σ*(D/J)^(A-σ) = D^A*J^(-(A-σ)) := by
    rw [Real.div_rpow hD.le hJ.le,div_eq_mul_inv,←Real.rpow_neg hJ.le,
      ←mul_assoc,←Real.rpow_add hD]
    congr 2
    ring
  have hdpow : D^A = R^(2*A)*T^(4*A)*X^(-A) := by
    dsimp [D]
    rw [Real.div_rpow (by positivity) hX.le,Real.mul_rpow (by positivity) (by positivity),
      ←Real.rpow_natCast_mul hR.le,←Real.rpow_natCast_mul hT.le,
      div_eq_mul_inv,←Real.rpow_neg hX.le]
    norm_num
  have hTpow : T^(4*A)*T^2 = T^(4*m) := by
    rw [←Real.rpow_two,←Real.rpow_add hT]
    have he : 4*A+2 = ((4*m:ℕ):ℝ) := by dsimp [A]; push_cast; ring
    rw [he,Real.rpow_natCast]
  change R^(ε+2*A)*X^(-A)*J^(-(A-σ))*T^(4*m) = R^ε*T^2*D^σ*(D/J)^(A-σ)
  rw [show R^ε*T^2*D^σ*(D/J)^(A-σ) = R^ε*T^2*(D^σ*(D/J)^(A-σ)) by ring,
    hcut,hdpow,Real.rpow_add hR]
  calc
    _ = (R^ε*R^(2*A)*X^(-A)*J^(-(A-σ)))*(T^(4*A)*T^2) := by rw [hTpow]
    _ = _ := by ring

lemma metaplectic_height_nat_power {T t : ℝ} (hT : 1 ≤ T) (ht : |t| ≤ 2*T) (m : ℕ) :
    (1+|t|)^(4*m) ≤ 3^(4*m)*T^(4*m) := by
  rw [←mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTailTruncation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed dyadic cutoff, larger than the natural dual length by a
small power, makes the actual metaplectic tail arbitrarily small. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma exists_metaplectic_tail_order {δ : ℝ} (hδ : 0 < δ) (B ε σ H : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ σ ≤ (m:ℝ)-1/2 ∧
      B*(ε+2+σ)-δ*((m:ℝ)-1/2-σ) ≤ -H := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max 2 (max (σ+1/2)
    (σ+1/2+(B*(ε+2+σ)+H)/δ)))
  have hm2 : (2:ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hml : max (σ+1/2) (σ+1/2+(B*(ε+2+σ)+H)/δ) < m :=
    lt_of_le_of_lt (le_max_right _ _) hm
  have hs : σ+1/2 < m := lt_of_le_of_lt (le_max_left _ _) hml
  have hp : (B*(ε+2+σ)+H)/δ < (m:ℝ)-σ-1/2 := by
    linarith [lt_of_le_of_lt (le_max_right _ _) hml]
  have hmul := (div_lt_iff₀ hδ).mp hp
  refine ⟨m,?_,by linarith,by nlinarith⟩
  have : 2 < m := by exact_mod_cast hm2
  omega

lemma metaplectic_tail_power_absorption {Y R T D J B ε σ δ H A : ℝ}
    (hY : 1 ≤ Y) (hR : 0 < R) (hT : 0 < T) (hD : 0 < D) (hJ : 0 < J)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (hA : 0 ≤ A)
    (hRB : R ≤ Y^B) (hTB : T ≤ Y^B) (hDB : D ≤ Y^B)
    (hcut : D/J ≤ Y^(-δ)) (horder : B*(ε+2+σ)-δ*A ≤ -H) :
    R^ε*T^2*D^σ*(D/J)^A ≤ Y^(-H) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hr : R^ε ≤ Y^(B*ε) := by
    calc
      _ ≤ (Y^B)^ε := Real.rpow_le_rpow hR.le hRB hε
      _ = _ := (Real.rpow_mul hYp.le _ _).symm
  have ht : T^2 ≤ Y^(2*B) := by
    calc
      _ ≤ (Y^B)^2 := pow_le_pow_left₀ hT.le hTB 2
      _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hYp.le]; congr 1; ring
  have hd : D^σ ≤ Y^(B*σ) := by
    calc
      _ ≤ (Y^B)^σ := Real.rpow_le_rpow hD.le hDB hσ
      _ = _ := (Real.rpow_mul hYp.le _ _).symm
  have hc : (D/J)^A ≤ Y^(-δ*A) := by
    calc
      _ ≤ (Y^(-δ))^A := Real.rpow_le_rpow (div_nonneg hD.le hJ.le) hcut hA
      _ = _ := (Real.rpow_mul hYp.le _ _).symm
  calc
    _ ≤ Y^(B*ε)*Y^(2*B)*Y^(B*σ)*Y^(-δ*A) := by gcongr
    _ = Y^(B*(ε+2+σ)-δ*A) := by
      rw [←Real.rpow_add hYp,←Real.rpow_add hYp,←Real.rpow_add hYp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY horder

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticShortScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short completed mean with an arbitrary fixed upper support
endpoint; the arithmetic length X is kept separate from that endpoint. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma metaplectic_short_support_factor {B X R T : ℝ}
    (hB : 0 ≤ B) (hR : 1 ≤ R) (hT : 1 ≤ T)
    (hshort : X ≤ Real.sqrt R*T^2) :
    1+2*(B*X)/T ≤ (1+2*B)*Real.sqrt R*T := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hs : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
  have hRT : 1 ≤ Real.sqrt R*T := one_le_mul_of_one_le_of_one_le hs hT
  have hx : X/T ≤ Real.sqrt R*T := by
    apply (div_le_iff₀ hTp).mpr
    nlinarith only [hshort]
  have hb := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2*B by positivity)
  calc
    _ = 1+(2*B)*(X/T) := by ring
    _ ≤ (1+2*B)*Real.sqrt R*T := by nlinarith only [hb,hRT]

/-- Actual finite primal coefficients supply this estimate, including
an arbitrary fixed support endpoint. -/
theorem metaplecticHeightCompleted_short_scaled_mean {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : Eisenstein, primary r →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ) (X B M T u R : ℝ),
      0 < X → 1 ≤ B → (∀ x : ℝ, B < x → W x = 0) →
      (∀ x : ℝ, ‖W x‖ ≤ M) → 1 ≤ B*X → 0 ≤ M → 1 ≤ T → 1 ≤ R →
      X ≤ Real.sqrt R*T^2 →
      (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W X (t+u)‖)/T ≤
        Real.sqrt (C*K*B^(1+ε)*(1+2*B)*X^(1+ε)*Real.sqrt R*T)*M := by
  obtain ⟨K,hK,hbound⟩ := metaplecticHeightCompleted_meanAbsolute_sq hε hMV hC
  refine ⟨K,hK,?_⟩
  intro r hr ℓ W X B M T u R hX hB hcut hW hVX hM hT hR hshort
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hsq := hbound r hr ℓ W X B (B*X) M T u hX le_rfl hcut hW hVX hM
    (zero_lt_one.trans_le hT)
  have hs := metaplectic_short_support_factor hBp.le hR hT hshort
  have hb : ((∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W X (t+u)‖)/T)^2 ≤
      (C*K*B^(1+ε)*(1+2*B)*X^(1+ε)*Real.sqrt R*T)*M^2 := by
    apply hsq.trans
    calc
      _ = (C*K*(B*X)^(1+ε)*M^2)*(1+2*(B*X)/T) := by ring
      _ ≤ (C*K*(B*X)^(1+ε)*M^2)*((1+2*B)*Real.sqrt R*T) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [Real.mul_rpow hBp.le hX.le]; ring
  have hh := Real.le_sqrt_of_sq_le hb
  simpa only [Real.sqrt_mul (show 0 ≤ C*K*B^(1+ε)*(1+2*B)*X^(1+ε)*Real.sqrt R*T by positivity),
    Real.sqrt_sq hM] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletedShort
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short angular completed mean, with the fixed smooth weight's
actual support and size bounds constructed, including the empty range. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma metaplecticHeightCompleted_zero_of_small_support (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) {X S : ℝ} (hX : 0 < X) (hSX : S*X < 1)
    (hcut : ∀ x : ℝ, S < x → W x = 0) (t : ℝ) :
    metaplecticHeightCompleted r ℓ W X t = 0 := by
  unfold metaplecticHeightCompleted
  have hz (du : PrimaryArgument × PrimaryArgument) :
      metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du)*
        mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))) = 0 := by
    have hp : primary (metaplecticCubeProduct (metaplecticPrimaryPair du)) := by
      apply primary_mul du.2.property
      simpa only [pow_succ,pow_zero,one_mul,metaplecticPrimaryPair] using
        primary_mul (primary_mul du.1.property du.1.property) du.1.property
    have hn := one_le_norm (primary_ne_zero hp)
    have hw : W (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))/X) = 0 :=
      hcut _ ((lt_div_iff₀ hX).mpr (hSX.trans_le hn))
    simp [metaplecticPrimalCoefficient,hw]
  simp_rw [hz,tsum_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompletedMean
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fixed nonzero-angular height mean across both ranges.
The fixed dilation is absorbed in constants and the existing polynomial
scale range; no metaplectic Voronoi premise is used. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicTheta_dilated_lower_scale {Y B : ℝ} (hY : 1≤Y) (hB : 0≤B) :
    (729*Y)^(-(B+1))≤Y^(-B)/729 := by
  have hYp : 0<Y := zero_lt_one.trans_le hY
  have hZp : 0<729*Y := by positivity
  have hbase : Y≤729*Y := by linarith
  have hfirst : (729*Y)^(-B)≤Y^(-B) :=
    Real.rpow_le_rpow_of_nonpos hYp hbase (by linarith)
  have hsecond : (729*Y)^(-(1:ℝ))≤(729:ℝ)^(-(1:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by norm_num)
  calc
    _ = (729*Y)^(-B)*(729*Y)^(-(1:ℝ)) := by
      rw [←Real.rpow_add hZp]
      congr 1
      ring
    _ ≤ Y^(-B)*(729:ℝ)^(-(1:ℝ)) := mul_le_mul hfirst hsecond
      (Real.rpow_nonneg hZp.le _) (Real.rpow_nonneg hYp.le _)
    _ = _ := by norm_num [Real.rpow_neg_one,div_eq_mul_inv]

lemma cubicTheta_dilated_upper_scale {Y B : ℝ} (hY : 1≤Y) (hB : 0≤B) :
    Y^B≤(729*Y)^(B+1) := by
  have hZ : 1≤729*Y := by linarith
  exact (Real.rpow_le_rpow (by linarith) (by linarith) hB).trans
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticConjugateMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient conjugation supplies the opposite height orientation.
The literal published coefficient support is preserved under conjugation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma star_real_complex (x : ℝ) : star (x:ℂ) = (x:ℂ) :=
  Complex.conj_ofReal x

lemma star_metaplecticLocalCoefficient (r : Eisenstein) (n : MetaplecticDualArgument) :
    star (metaplecticLocalCoefficient r n) = metaplecticLocalCoefficient r n := by
  simp only [metaplecticLocalCoefficient,star_prod,star_real_complex]

lemma star_complexAngular {z : ℂ} (hz : z ≠ 0) (ℓ : ℤ) :
    star (complexAngular ℓ z) = complexAngular (-ℓ) z := by
  rw [show complexAngular (-ℓ) z = (complexAngular ℓ z)⁻¹ by
    simp only [complexAngular,zpow_neg]]
  exact (Complex.inv_eq_conj (norm_complexAngular hz ℓ)).symm

lemma MetaplecticCoefficientBounds.conjugate
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a) :
    MetaplecticCoefficientBounds (metaplecticConjugateCoefficients a) := by
  obtain ⟨C,hC,hb⟩ := ha
  refine ⟨C,hC,?_⟩
  intro r hr hsr n hn
  have he : metaplecticConjugateCoefficients a r n*metaplecticLocalCoefficient r n =
      star (a r n*metaplecticLocalCoefficient r n) := by
    rw [star_mul,star_metaplecticLocalCoefficient]
    dsimp [metaplecticConjugateCoefficients]
    ring
  have hraw : a r n*metaplecticLocalCoefficient r n ≠ 0 := by
    intro hz
    apply hn
    rw [he,hz,star_zero]
  obtain ⟨j,ζ,h,h',w,hj,hh,hh',hw,hdiv,hdiv',hwr,hsq,hfreq,hbound⟩ := hb r hr hsr n hraw
  refine ⟨j,ζ,h,h',w,hj,hh,hh',hw,hdiv,hdiv',hwr,hsq,hfreq,?_⟩
  simpa only [metaplecticConjugateCoefficients,norm_star] using hbound

lemma star_metaplecticNormalizedDualCoefficient
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument) :
    star (metaplecticNormalizedDualCoefficient a r ℓ nd) =
      metaplecticNormalizedDualCoefficient (metaplecticConjugateCoefficients a) r (-ℓ) nd := by
  have hz : ((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (fun h => primary_ne_zero nd.2.property (Subtype.ext h)))
      (metaplecticFrequency_ne_zero nd.1)
  unfold metaplecticNormalizedDualCoefficient
  split_ifs
  · simp only [star_mul,star_div₀,star_metaplecticLocalCoefficient,
      star_complexAngular hz,neg_neg,star_real_complex,metaplecticConjugateCoefficients]
    ring
  · simp only [star_zero]

lemma metaplectic_opposite_polynomial_norm
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (τ t : ℝ) :
    ‖∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase (τ+t) (metaplecticDualNorm nd)‖ =
      ‖∑ nd ∈ S, metaplecticNormalizedDualCoefficient (metaplecticConjugateCoefficients a) r (-ℓ) nd*
        mellinPhase (-τ-t) (metaplecticDualNorm nd)‖ := by
  rw [←norm_star (∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
    mellinPhase (τ+t) (metaplecticDualNorm nd))]
  simp only [star_sum,star_mul,star_metaplecticNormalizedDualCoefficient,star_mellinPhase,
    show -(τ+t) = -τ-t by ring,mul_comm]

theorem metaplectic_actual_retained_plus_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (J T : ℝ),
      0 < J → 0 < T → (∀ nd ∈ S, metaplecticDualNorm nd ≤ J) →
      ∀ (ℓ : ℤ) (τ : ℝ),
      ((∫ t in T..2*T, ‖∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
        mellinPhase (τ+t) (metaplecticDualNorm nd)‖)/T)/Real.sqrt (norm r) ≤
          ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
            (1+Real.sqrt (4*J/(norm r*T))) := by
  obtain ⟨D,hD,hb⟩ := metaplectic_actual_retained_mean ha.conjugate hε hMV hM
  refine ⟨D,hD,?_⟩
  intro r hr hsr S J T hJ hT hS ℓ τ
  simp_rw [metaplectic_opposite_polynomial_norm]
  exact hb r hr hsr S J T hJ hT hS (-ℓ) (-τ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticNegativeKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same actual critical kernel on the negative height dyad.
Conjugating the coefficients supplies the required opposite-sign mean. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_negative_kernel_mean (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (c : ℝ) (P : ℝ → ℂ) (hP : Continuous P)
    {T B : ℝ} (hT : 0 < T)
    (hmean : ∀ τ : ℝ, (∫ t in T..2*T, ‖P (τ+t)‖)/T ≤ B) :
    (∫ t in T..2*T, ‖∫ τ : ℝ, metaplecticCriticalKernel ℓ W c P τ (-t)‖)/T ≤
      B*(∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) := by
  have hm := (metaplectic_mellin_half_integrable W hW hpos hsm).norm
  have hc : Continuous (fun z : ℝ × ℝ => metaplecticCriticalKernel ℓ W c P z.1 (-z.2)) :=
    (continuous_metaplecticCriticalKernel ℓ W hW hpos hsm c hP).comp
      (f := fun z : ℝ × ℝ => (z.1,-z.2)) (continuous_fst.prodMk continuous_snd.neg)
  have hb (τ : ℝ) :
      (∫ t in T..2*T, ‖metaplecticCriticalKernel ℓ W c P τ (-t)‖) ≤
        (B*T)*‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖ := by
    simp only [norm_metaplecticCriticalKernel,sub_neg_eq_add]
    rw [intervalIntegral.integral_const_mul]
    calc
      _ ≤ ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖*(B*T) :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hT).mp (hmean τ)) (_root_.norm_nonneg _)
      _ = _ := by ring
  have hi := integral_height_norm_le
    (fun z : ℝ × ℝ => metaplecticCriticalKernel ℓ W c P z.1 (-z.2)) hc
    (show T ≤ 2*T by linarith)
    (fun τ => (B*T)*‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) (hm.const_mul (B*T)) hb
  rw [integral_const_mul] at hi
  apply (div_le_iff₀ hT).mpr
  nlinarith only [hi]

theorem metaplectic_actual_retained_negative_kernel
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (J T : ℝ),
      0 < J → 0 < T → (∀ nd ∈ S, metaplecticDualNorm nd ≤ J) →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ), HasCompactSupport W → tsupport W ⊆ Ioi 0 →
      ContDiff ℝ ∞ W → ∀ c : ℝ,
      ((∫ t in T..2*T, ‖∫ τ : ℝ, metaplecticCriticalKernel ℓ W c
        (fun u => ∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
          mellinPhase u (metaplecticDualNorm nd)) τ (-t)‖)/T)/Real.sqrt (norm r) ≤
          ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
            (1+Real.sqrt (4*J/(norm r*T)))*
              (∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) := by
  obtain ⟨D,hD,hb⟩ := metaplectic_actual_retained_plus_mean ha hε hMV hM
  refine ⟨D,hD,?_⟩
  intro r hr hsr S J T hJ hT hS ℓ W hW hpos hsm c
  have hR := Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hr))
  let B := ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
    (1+Real.sqrt (4*J/(norm r*T)))
  let P := fun u : ℝ => ∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
    mellinPhase u (metaplecticDualNorm nd)
  have hP : Continuous P := by
    apply continuous_finsetSum
    intro nd hnd
    apply continuous_const.mul
    unfold mellinPhase
    fun_prop
  have hmean (τ : ℝ) : (∫ t in T..2*T, ‖P (τ+t)‖)/T ≤ B*Real.sqrt (norm r) :=
    (div_le_iff₀ hR).mp (hb r hr hsr S J T hJ hT hS ℓ τ)
  have hk := metaplectic_negative_kernel_mean ℓ W hW hpos hsm c P hP hT hmean
  apply (div_le_iff₀ hR).mpr
  calc
    _ ≤ (B*Real.sqrt (norm r))*(∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) := hk
    _ = _ := by dsimp [B]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticNegativeEstimate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual negative-height retained Voronoi contribution, with
its unchanged exact prefactor normalization. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_retained_negative_voronoi_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ), HasCompactSupport W → tsupport W ⊆ Ioi 0 →
      ContDiff ℝ ∞ W → ∀ A X J T : ℝ, 0 ≤ A → 0 < X → 0 < J → 0 < T →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A) →
      (∫ t in T..2*T, ‖metaplecticPrefactor r ℓ*
        ∑ nd ∈ metaplecticDualBall J,
          metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase (-t) x) A X nd‖)/T ≤
        Real.sqrt X/(3^(7/2:ℝ)*(2*Real.pi))*
          (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
            (1+Real.sqrt (4*J/(norm r*T)))*
              (∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖)) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_actual_retained_negative_kernel ha hε hMV hM
  refine ⟨D,hD,?_⟩
  intro r hr hsr ℓ W hW hpos hsm A X J T hA hX hJ hT hm hp
  let c := (2*Real.pi)^4*X/norm r^2
  let K := fun t : ℝ => ∫ τ : ℝ, metaplecticCriticalKernel ℓ W c
    (fun u => ∑ nd ∈ metaplecticDualBall J,
      metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase u (metaplecticDualNorm nd)) τ (-t)
  let Q := ‖metaplecticPrefactor r ℓ‖*Real.sqrt c*(1/(2*Real.pi))
  let B := (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
    (1+Real.sqrt (4*J/(norm r*T)))*
      (∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖))
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hb : ((∫ t in T..2*T, ‖K t‖)/T)/Real.sqrt (norm r) ≤ B :=
    hbound r hr hsr (metaplecticDualBall J) J T hJ hT
      (fun nd hnd => (mem_metaplecticDualBall nd J).mp hnd) ℓ W hW hpos hsm c
  have he (t : ℝ) : ‖metaplecticPrefactor r ℓ*
      ∑ nd ∈ metaplecticDualBall J,
        metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase (-t) x) A X nd‖ = Q*‖K t‖ := by
    rw [metaplectic_retained_critical a hr ℓ W hW hpos hsm hA hX J (-t) hm hp]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (show (0:ℝ) ≤ 1/(2*Real.pi) by positivity)]
    dsimp [Q,K,c]
    ring
  calc
    _ = Q*((∫ t in T..2*T, ‖K t‖)/T) := by
      simp_rw [he]
      rw [intervalIntegral.integral_const_mul]
      ring
    _ ≤ Q*(B*Real.sqrt (norm r)) :=
      mul_le_mul_of_nonneg_left ((div_le_iff₀ (Real.sqrt_pos.mpr hR)).mp hb) hQ
    _ = _ := by
      rw [show Q*(B*Real.sqrt (norm r)) = (Q*Real.sqrt (norm r))*B by ring,
        show Q*Real.sqrt (norm r) = Real.sqrt X/(3^(7/2:ℝ)*(2*Real.pi)) from
          metaplectic_critical_prefactor hr ℓ hX]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticUniformRetained
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual retained means for both height signs with one constant
for a uniformly controlled logarithmic weight family. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_retained_voronoi_subpower
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y A X J T : ℝ, 1 ≤ Y → 0 ≤ A → 0 < X → 1 ≤ J → 0 < T →
      norm r ≤ Y^B → J ≤ Y^B →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A) →
      (∫ t in T..2*T, ‖metaplecticPrefactor r ℓ*
        ∑ nd ∈ metaplecticDualBall J,
          metaplecticDualTerm a r ℓ (fun x => W i x*mellinPhase t x) A X nd‖)/T ≤
        K*Real.sqrt X*Y^η*(1+Real.sqrt (4*J/(norm r*T))) := by
  obtain ⟨ε,C,hε,hC,hpower⟩ := metaplectic_retained_loss_small_power hη hB
  obtain ⟨D,hD,hbound⟩ := metaplectic_retained_voronoi_mean ha hε hMV hM
  obtain ⟨L,hL,hLm⟩ := h.mellin_norm_moment (1/2) 0
  have hmass (i : ι) : (∫ τ : ℝ, ‖mellin (W i) ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) ≤ L := by
    simpa only [pow_zero,one_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hLm i (1/2) (by norm_num)
  let P := 3^(7/2:ℝ)*(2*Real.pi)
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨D*L/P*C,by positivity,?_⟩
  intro i r hr hsr Y A X J T hY hA hX hJ hT hRY hJY hm hp
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hb := hbound r hr hsr ℓ (W i) (h.compact i) (h.positive i) (h.smooth i) A X J T hA hX
    (zero_lt_one.trans_le hJ) hT hm hp
  have hs := hpower Y (norm r) J hY hR hJ hRY hJY
  calc
    _ ≤ Real.sqrt X/P*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
          (1+Real.sqrt (4*J/(norm r*T)))*
            (∫ τ : ℝ, ‖mellin (W i) ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖)) := hb
    _ ≤ Real.sqrt X/P*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
          (1+Real.sqrt (4*J/(norm r*T)))*L) := by
      gcongr
      exact hmass i
    _ = (D*L/P*Real.sqrt X)*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*(6*J)^(3*ε/2)*norm r^(2*ε))*
          (1+Real.sqrt (4*J/(norm r*T))) := by ring
    _ ≤ (D*L/P*Real.sqrt X)*(C*Y^η)*
          (1+Real.sqrt (4*J/(norm r*T))) := by gcongr
    _ = _ := by ring


theorem UniformLogWeights.metaplectic_retained_negative_voronoi_subpower
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y A X J T : ℝ, 1 ≤ Y → 0 ≤ A → 0 < X → 1 ≤ J → 0 < T →
      norm r ≤ Y^B → J ≤ Y^B →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A) →
      (∫ t in T..2*T, ‖metaplecticPrefactor r ℓ*
        ∑ nd ∈ metaplecticDualBall J,
          metaplecticDualTerm a r ℓ (fun x => W i x*mellinPhase (-t) x) A X nd‖)/T ≤
        K*Real.sqrt X*Y^η*(1+Real.sqrt (4*J/(norm r*T))) := by
  obtain ⟨ε,C,hε,hC,hpower⟩ := metaplectic_retained_loss_small_power hη hB
  obtain ⟨D,hD,hbound⟩ := metaplectic_retained_negative_voronoi_mean ha hε hMV hM
  obtain ⟨L,hL,hLm⟩ := h.mellin_norm_moment (1/2) 0
  have hmass (i : ι) : (∫ τ : ℝ, ‖mellin (W i) ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) ≤ L := by
    simpa only [pow_zero,one_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hLm i (1/2) (by norm_num)
  let P := 3^(7/2:ℝ)*(2*Real.pi)
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨D*L/P*C,by positivity,?_⟩
  intro i r hr hsr Y A X J T hY hA hX hJ hT hRY hJY hm hp
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hb := hbound r hr hsr ℓ (W i) (h.compact i) (h.positive i) (h.smooth i) A X J T hA hX
    (zero_lt_one.trans_le hJ) hT hm hp
  have hs := hpower Y (norm r) J hY hR hJ hRY hJY
  calc
    _ ≤ Real.sqrt X/P*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
          (1+Real.sqrt (4*J/(norm r*T)))*
            (∫ τ : ℝ, ‖mellin (W i) ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖)) := hb
    _ ≤ Real.sqrt X/P*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
          (1+Real.sqrt (4*J/(norm r*T)))*L) := by
      gcongr
      exact hmass i
    _ = (D*L/P*Real.sqrt X)*
        (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*(6*J)^(3*ε/2)*norm r^(2*ε))*
          (1+Real.sqrt (4*J/(norm r*T))) := by ring
    _ ≤ (D*L/P*Real.sqrt X)*(C*Y^η)*
          (1+Real.sqrt (4*J/(norm r*T))) := by gcongr
    _ = _ := by ring


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticUniformWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma UniformLogWeights.uniform_norm_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i x, ‖W i x‖ ≤ M := by
  obtain ⟨M,hM,hbound⟩ := h.derivative_bound 0
  refine ⟨M,hM,?_⟩
  intro i x
  by_cases hx : 0 < x
  · have he := hbound i (-Real.log x)
    simpa only [norm_iteratedFDeriv_zero,neg_neg,Real.exp_log hx] using he
  · have hz : W i x = 0 := by
      by_contra hn
      exact hx (h.positive i (subset_tsupport _ hn))
    simpa only [hz,norm_zero] using hM

lemma UniformLogWeights.mellin_polynomial_majorant {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (σ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i (t τ : ℝ),
      ‖mellin (W i) (σ+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^N ≤
        mellinEdgeMajorant (C*(1+|t|)^N) τ := by
  obtain ⟨C,hC,hdecay⟩ := h.mellin_decay |σ| (N+2)
  refine ⟨C,hC,?_⟩
  intro i t τ
  unfold mellinEdgeMajorant
  apply (le_div_iff₀ (by positivity : 0 < (1+|τ|)^2)).mpr
  calc
    _ ≤ (‖mellin (W i) (σ+(τ:ℂ)*Complex.I)‖*
        ((1+|t|)^N*(1+|τ|)^N))*(1+|τ|)^2 := by
      gcongr
      exact shifted_power_le N τ t
    _ = (1+|t|)^N*((1+|τ|)^(N+2)*‖mellin (W i) (σ+(τ:ℂ)*Complex.I)‖) := by
      rw [pow_add]
      ring
    _ ≤ (1+|t|)^N*C := mul_le_mul_of_nonneg_left (hdecay i σ le_rfl τ) (by positivity)
    _ = _ := mul_comm _ _

theorem UniformLogWeights.metaplecticShiftTransform_far_left {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (ℓ : ℤ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ v : ℝ, 0 < v → ∀ t : ℝ,
      ‖metaplecticShiftTransform ℓ (W i) (1/2-(m:ℝ)) v t‖ ≤
        C*v^(1/2-(m:ℝ))*(1+|t|)^(4*m) := by
  obtain ⟨Cg,hCg,hQ⟩ := metaplecticGamma_half_integer_bound ℓ m
  obtain ⟨Cw,hCw,hdecay⟩ := h.mellin_polynomial_majorant
    (1/2-(m:ℝ)) (4*m)
  let I : ℝ := ∫ τ : ℝ, mellinEdgeMajorant 1 τ
  have hI : 0 ≤ I := integral_nonneg (fun τ => by
    unfold mellinEdgeMajorant
    positivity)
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)‖*Cg*Cw*I,by positivity,?_⟩
  intro i v hv t
  have hb (τ : ℝ) :
      ‖(v:ℂ)^(((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ (((1/2-(m:ℝ):ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
        mellin (W i) (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I)‖ ≤
      (v^(1/2-(m:ℝ))*Cg*Cw*(1+|t|)^(4*m))*mellinEdgeMajorant 1 τ := by
    have he : (((1/2-(m:ℝ):ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
        (1/2:ℂ)-(m:ℂ)+((τ-t:ℝ):ℂ)*Complex.I := by push_cast; ring
    have hq := hQ (τ-t)
    rw [←he] at hq
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
    have hre : (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I).re = 1/2-(m:ℝ) := by simp
    rw [hre]
    calc
      _ ≤ (v^(1/2-(m:ℝ))*(Cg*(1+|τ-t|)^(4*m)))*
          ‖mellin (W i) (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I)‖ := by
        gcongr
      _ = (v^(1/2-(m:ℝ))*Cg)*
          (‖mellin (W i) (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^(4*m)) := by ring
      _ ≤ (v^(1/2-(m:ℝ))*Cg)*mellinEdgeMajorant (Cw*(1+|t|)^(4*m)) τ :=
        mul_le_mul_of_nonneg_left (hdecay i t τ) (by positivity)
      _ = _ := by unfold mellinEdgeMajorant; ring
  rw [metaplecticShiftTransform,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)‖*
        (∫ τ : ℝ, (v^(1/2-(m:ℝ))*Cg*Cw*(1+|t|)^(4*m))*mellinEdgeMajorant 1 τ) := by
      apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
      exact norm_integral_le_of_norm_le ((mellinEdgeMajorant_integrable 1).const_mul _)
        (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_const_mul]; dsimp [I]; ring


theorem UniformLogWeights.metaplecticTransform_twisted_far_left
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ v : ℝ, 0 < v → ∀ t : ℝ,
      ‖metaplecticTransform ℓ (fun x => W i x*mellinPhase t x) ((m:ℝ)-1/2) v‖ ≤
        C*v^(1/2-(m:ℝ))*(1+|t|)^(4*m) := by
  obtain ⟨C,hC,hbound⟩ := h.metaplecticShiftTransform_far_left ℓ m
  refine ⟨C,hC,?_⟩
  intro i v hv t
  rw [metaplecticTransform_twisted ℓ (W i) _ hv t,norm_mul,mellinPhase_norm,one_mul]
  simpa only [show -((m:ℝ)-1/2) = 1/2-(m:ℝ) by ring] using hbound i v hv t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticUniformTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Far-left truncation of the literal angular Voronoi series. The
absolute coefficient mass is derived from the published theta support,
and the height growth is derived from finite Gamma recurrence. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_twisted_tail_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ) (m : ℕ)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hm : σ ≤ (m:ℝ)-1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ X J : ℝ, 0 < X → 0 < J → ∀ t : ℝ,
      ‖∑' nd, metaplecticFarTailTerm a r ℓ (fun x => W i x*mellinPhase t x)
          ((m:ℝ)-1/2) X J nd‖ ≤
        C*norm r^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*
          J^(-(((m:ℝ)-1/2)-σ))*(1+|t|)^(4*m) := by
  obtain ⟨Cw,hCw,hfar⟩ := h.metaplecticTransform_twisted_far_left ℓ m
  obtain ⟨M,hM,hmass⟩ := metaplectic_coefficient_mass_small_power ha hε hσ
  let A : ℝ := (m:ℝ)-1/2
  let S : ℝ := ∑' d : PrimaryArgument, norm d^(-5/2-3*σ)
  have hS : 0 ≤ S := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  let C : ℝ := Cw*(2*Real.pi)^(-4*A)*M*S
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro i r hr hsr X J hX hJ t
  have ht : 0 ≤ Cw*(1+|t|)^(4*m) := mul_nonneg hCw (by positivity)
  have htransform (v : ℝ) (hv : 0 < v) :
      ‖metaplecticTransform ℓ (fun x => W i x*mellinPhase t x) A v‖ ≤
        (Cw*(1+|t|)^(4*m))*v^(-A) := by
    have he : 1/2-(m:ℝ) = -A := by dsimp [A]; ring
    simpa only [he,mul_right_comm] using hfar i v hv t
  have hb := metaplecticFarTail_norm_bound a hr ℓ (fun x => W i x*mellinPhase t x)
    hσ hm hX hJ ht htransform (hmass r hr hsr).1 (hmass r hr hsr).2
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hRe : norm r^(2*A)*norm r^ε = norm r^(ε+2*A) := by
    rw [←Real.rpow_add hR]
    congr 1
    ring
  calc
    _ ≤ (Cw*(1+|t|)^(4*m)*((2*Real.pi)^(-4*A)*X^(-A)*norm r^(2*A)))*
        J^(-(A-σ))*(M*norm r^ε)*S := hb
    _ = C*(norm r^(2*A)*norm r^ε)*X^(-A)*J^(-(A-σ))*(1+|t|)^(4*m) := by
      dsimp [C]
      ring
    _ = _ := by rw [hRe]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticUniformTruncation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform arbitrary-power truncation for the original weight family.
The far-left line and the constant are chosen before the weight index. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_twisted_tail_natural_cutoff
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ) (m : ℕ)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hm : σ ≤ (m:ℝ)-1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ X J T : ℝ, 0 < X → 0 < J → 1 ≤ T → ∀ t : ℝ, |t| ≤ 2*T →
      ‖∑' nd, metaplecticFarTailTerm a r ℓ (fun x => W i x*mellinPhase t x)
          ((m:ℝ)-1/2) X J nd‖ ≤
        C*norm r^ε*T^2*(norm r^2*T^4/X)^σ*
          ((norm r^2*T^4/X)/J)^(((m:ℝ)-1/2)-σ) := by
  obtain ⟨C,hC,hbound⟩ := h.metaplectic_twisted_tail_bound ha ℓ m hε hσ hm
  refine ⟨C*3^(4*m),mul_nonneg hC (by positivity),?_⟩
  intro i r hr hsr X J T hX hJ hT t ht
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hTp : 0 < T := zero_lt_one.trans_le hT
  calc
    _ ≤ C*norm r^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*
        J^(-(((m:ℝ)-1/2)-σ))*(1+|t|)^(4*m) := hbound i r hr hsr X J hX hJ t
    _ ≤ C*norm r^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*
        J^(-(((m:ℝ)-1/2)-σ))*(3^(4*m)*T^(4*m)) :=
      mul_le_mul_of_nonneg_left (metaplectic_height_nat_power hT ht m) (by positivity)
    _ = (C*3^(4*m))*(norm r^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*
        J^(-(((m:ℝ)-1/2)-σ))*T^(4*m)) := by ring
    _ = _ := by rw [metaplectic_tail_scale_identity hR hX hTp hJ]; ring


theorem UniformLogWeights.metaplectic_twisted_tail_arbitrary_power
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ)
    {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (B H : ℝ) :
    ∃ (m : ℕ) (C : ℝ), 2 ≤ m ∧ σ ≤ (m:ℝ)-1/2 ∧ 0 ≤ C ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X J T : ℝ, 1 ≤ Y → 0 < X → 0 < J → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → norm r^2*T^4/X ≤ Y^B →
      (norm r^2*T^4/X)/J ≤ Y^(-δ) → ∀ t : ℝ, |t| ≤ 2*T →
      ‖∑' nd, metaplecticFarTailTerm a r ℓ (fun x => W i x*mellinPhase t x)
          ((m:ℝ)-1/2) X J nd‖ ≤ C*Y^(-H) := by
  obtain ⟨m,hm2,hms,horder⟩ := exists_metaplectic_tail_order hδ B 1 σ H
  obtain ⟨C,hC,hbound⟩ := h.metaplectic_twisted_tail_natural_cutoff ha ℓ m
    (by norm_num : (0:ℝ) < 1) hσ hms
  refine ⟨m,C,hm2,hms,hC,?_⟩
  intro i r hr hsr Y X J T hY hX hJ hT hRB hTB hDB hcut t ht
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hD : 0 < norm r^2*T^4/X := by positivity
  have hs := metaplectic_tail_power_absorption hY hR hTp hD hJ
    (by norm_num : (0:ℝ) ≤ 1) hσ.le (sub_nonneg.mpr hms)
    hRB hTB hDB hcut horder
  calc
    _ ≤ C*norm r^(1:ℝ)*T^2*(norm r^2*T^4/X)^σ*
        ((norm r^2*T^4/X)/J)^(((m:ℝ)-1/2)-σ) := hbound i r hr hsr X J T hX hJ hT t ht
    _ = C*(norm r^(1:ℝ)*T^2*(norm r^2*T^4/X)^σ*
        ((norm r^2*T^4/X)/J)^(((m:ℝ)-1/2)-σ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hC


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUniformLong
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform actual nonzero-angular long-height estimate, with
its exact primal dilation and proved coefficient bounds. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma sqrt_level_negative_power_p3 {Y R X B : ℝ}
    (hY : 0 < Y) (hRY : R ≤ Y^B) (hYX : Y^(-B) ≤ X) :
    Real.sqrt R*Y^(-B) ≤ Real.sqrt X := by
  have he : Real.sqrt (Y^B)*Y^(-B) = Real.sqrt (Y^(-B)) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hY.le,
      ←Real.rpow_add hY,←Real.rpow_mul hY.le]
    congr 1
    ring
  calc
    _ ≤ Real.sqrt (Y^B)*Y^(-B) := mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt hRY) (Real.rpow_nonneg hY.le _)
    _ = Real.sqrt (Y^(-B)) := he
    _ ≤ _ := Real.sqrt_le_sqrt hYX

/-- For each small loss, the far-left line is chosen once before all
levels, lengths and heights. Its Gamma bounds are exactly the published
bounded-strip input at that chosen line. -/
theorem UniformLogWeights.cubicTheta_completed_dilated_long_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ≠0)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ (m : ℕ) (K : ℝ), 2 ≤ m ∧ 0 ≤ K ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1 ≤ Y → 0 < X → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X →
      Real.sqrt (norm r)*T^2 ≤ X →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)) →
      (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ (W i) (729*X) t‖)/T ≤
          K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  let B' := 7*B+η
  have hB' : 0 ≤ B' := by dsimp [B']; positivity
  have hBB' : B ≤ B' := by dsimp [B']; linarith
  have h7B : 7*B ≤ B' := by dsimp [B']; linarith
  have hσ : (0:ℝ) < 1/20000 := by norm_num
  obtain ⟨m,C,hm,hms,hC,htail⟩ := h.metaplectic_twisted_tail_arbitrary_power cubicThetaCoreCoefficient_bounds ℓ hσ hη B' B
  obtain ⟨D,hD,hret⟩ := h.metaplectic_retained_voronoi_subpower cubicThetaCoreCoefficient_bounds hMV hM ℓ (div_pos hη (by norm_num : (0:ℝ) < 2)) hB'
  let P := 3^(7/2:ℝ)*(2*Real.pi)^2
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨m,81*(4*D+C/P),hm,by positivity,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hlong hgm hgp
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hR1 := one_le_norm (primary_ne_zero hr)
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let J := metaplecticNaturalCutoff Y (norm r) T X η
  have hJ1 : 1 ≤ J := metaplecticNaturalCutoff_ge_one _ _ _ _ _
  have hJ : 0 < J := zero_lt_one.trans_le hJ1
  have hJY : J ≤ Y^B' := metaplecticNaturalCutoff_polynomial hY hR hTp hB hη.le hRY hTY hYX
  have hRY' : norm r ≤ Y^B' := hRY.trans (Real.rpow_le_rpow_of_exponent_le hY hBB')
  have hTY' : T ≤ Y^B' := hTY.trans (Real.rpow_le_rpow_of_exponent_le hY hBB')
  have hDY : norm r^2*T^4/X ≤ Y^B' :=
    (metaplectic_natural_length_polynomial hY hR hTp hRY hTY hYX).trans
      (Real.rpow_le_rpow_of_exponent_le hY h7B)
  have hcut : (norm r^2*T^4/X)/J ≤ Y^(-η) := metaplecticNaturalCutoff_ratio hYp
  have ht (t : ℝ) (htt : |t| ≤ 2*T) :
      ‖∑' nd, metaplecticFarTailTerm cubicThetaCoreCoefficient r ℓ (fun x => W i x*mellinPhase t x)
        ((m:ℝ)-1/2) X J nd‖ ≤ C*Y^(-B) :=
    htail i r hr hsr Y X J T hY hX hJ hT hRY' hTY' hDY hcut t htt
  have ha : 0 ≤ (m:ℝ)-1/2 := hσ.le.trans hms
  have hscale : (729*X)/729=X := by ring
  have hb := cubicTheta_completed_tail_mean hr hsr hℓ (W i) (h.compact i) (h.positive i) (h.smooth i)
    (X:=729*X) (by positivity) (hσ.trans_le hms) hTp hgm hgp
    (by simpa only [hscale] using ht)
  simp only [hscale] at hb
  have hv := hret i r hr hsr Y ((m:ℝ)-1/2) X J T hY ha hX hJ1 hTp hRY' hJY hgm hgp
  have hg := metaplectic_long_sqrt_factor hY hR1 hT hη.le
    (metaplectic_long_cutoff hY hR1 hT hX hη.le hlong)
  change 1+Real.sqrt (4*J/(norm r*T)) ≤ _ at hg
  have hyprod : Y^(η/2)*Y^(η/2) = Y^η := by rw [←Real.rpow_add hYp]; congr 1; ring
  have hmain : (∫ t in T..2*T, ‖metaplecticPrefactor r ℓ*
      ∑ nd ∈ metaplecticDualBall J,
        metaplecticDualTerm cubicThetaCoreCoefficient r ℓ (fun x => W i x*mellinPhase t x) ((m:ℝ)-1/2) X nd‖)/T ≤
        4*D*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
    apply hv.trans
    calc
      _ ≤ D*Real.sqrt X*Y^(η/2)*(4*Y^(η/2)*norm r^(1/4:ℝ)*Real.sqrt T) := by gcongr
      _ = _ := by
        rw [show D*Real.sqrt X*Y^(η/2)*(4*Y^(η/2)*norm r^(1/4:ℝ)*Real.sqrt T) =
          4*D*Real.sqrt X*(Y^(η/2)*Y^(η/2))*norm r^(1/4:ℝ)*Real.sqrt T by ring,hyprod]
  have hf : 1 ≤ Y^η*norm r^(1/4:ℝ)*Real.sqrt T :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hY hη.le)
        (Real.one_le_rpow hR1 (by norm_num))) (Real.one_le_sqrt.mpr hT)
  have htailbound : ‖metaplecticPrefactor r ℓ‖*(C*Y^(-B)) ≤
      C/P*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
    rw [norm_metaplecticPrefactor (primary_ne_zero hr)]
    calc
      _ = C/P*(Real.sqrt (norm r)*Y^(-B)) := by dsimp [P]; ring
      _ ≤ C/P*Real.sqrt X := mul_le_mul_of_nonneg_left
        (sqrt_level_negative_power_p3 hYp hRY hYX) (by positivity)
      _ ≤ (C/P*Real.sqrt X)*(Y^η*norm r^(1/4:ℝ)*Real.sqrt T) :=
        le_mul_of_one_le_right (by positivity) hf
      _ = _ := by ring
  calc
    _ ≤ _ := hb
    _ ≤ 81*(4*D*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T+
        C/P*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T) :=
      mul_le_mul_of_nonneg_left (add_le_add hmain htailbound) (by norm_num)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUniformShort
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform finite primal bound on the enlarged transition range
required by the actual fixed theta dilation. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

private lemma uniform_short_square_root_factor_p0 {A X R T ε : ℝ}
    (hA : 0 ≤ A) (hX : 0 < X) (hR : 0 ≤ R) :
    Real.sqrt (A*X^(1+ε)*Real.sqrt R*T) =
      Real.sqrt A*Real.sqrt X*X^(ε/2)*R^(1/4:ℝ)*Real.sqrt T := by
  have hx : Real.sqrt (X^(1+ε)) = Real.sqrt X*X^(ε/2) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hX.le,←Real.rpow_add hX]
    congr 1
    ring
  have hr : Real.sqrt (Real.sqrt R) = R^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hR]
    norm_num
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hX.le _)) (Real.sqrt_nonneg _)),
    Real.sqrt_mul (mul_nonneg hA (Real.rpow_nonneg hX.le _)),Real.sqrt_mul hA,hx,hr]
  ring

theorem UniformLogWeights.cubicTheta_completed_short_mean
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i, ∀ r : Eisenstein, primary r →
      ∀ (ℓ : ℤ) (Y X T u : ℝ), 1 ≤ Y → 0 < X → 1 ≤ T → X ≤ Y^B →
      X ≤ 729*Real.sqrt (norm r)*T^2 →
      (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ (W i) X (t+u)‖)/T ≤
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  let S := Real.exp h.radius
  have hS : 1 ≤ S := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr h.radius_nonneg
  have hcut : ∀ i x, S < x → W i x = 0 := h.upper_support
  obtain ⟨M,hM,hsize⟩ := h.uniform_norm_bound
  let ε := 2*η/(B+1)
  have hε : 0 < ε := div_pos (by positivity) (by positivity)
  obtain ⟨D,hD,hbound⟩ := metaplecticHeightCompleted_short_scaled_mean hε hMV hC
  let A := C*D*S^(1+ε)*(1+2*S)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨Real.sqrt (A*729)*M,by positivity,?_⟩
  intro i r hr ℓ Y X T u hY hX hT hXY hshort
  have hYp := zero_lt_one.trans_le hY
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have he : B*(ε/2) ≤ η := by
    have hh := div_mul_cancel₀ (2*η) (show B+1 ≠ 0 by positivity)
    change ε*(B+1) = 2*η at hh
    nlinarith
  have hpower : X^(ε/2) ≤ Y^η := by
    calc
      _ ≤ (Y^B)^(ε/2) := Real.rpow_le_rpow hX.le hXY (by positivity)
      _ = Y^(B*(ε/2)) := (Real.rpow_mul hYp.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY he
  have hscale : Real.sqrt ((729:ℝ)^2*norm r)=729*Real.sqrt (norm r) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤729^2),Real.sqrt_sq (by norm_num)]
  by_cases hSX : 1 ≤ S*X
  · have hh := hbound r hr ℓ (W i) X S M T u ((729:ℝ)^2*norm r) hX hS (hcut i) (hsize i) hSX hM hT
      (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_norm (primary_ne_zero hr)))
      (by simpa only [hscale] using hshort)
    apply hh.trans
    change Real.sqrt (A*X^(1+ε)*Real.sqrt ((729:ℝ)^2*norm r)*T)*M ≤ _
    rw [hscale,show A*X^(1+ε)*(729*Real.sqrt (norm r))*T=
      (A*729)*X^(1+ε)*Real.sqrt (norm r)*T by ring,
      uniform_short_square_root_factor_p0 (mul_nonneg hA (by norm_num)) hX hR.le]
    calc
      _ = (Real.sqrt (A*729)*M)*Real.sqrt X*X^(ε/2)*norm r^(1/4:ℝ)*Real.sqrt T := by ring
      _ ≤ _ := by gcongr
  · have hz (t : ℝ) := metaplecticHeightCompleted_zero_of_small_support r ℓ (W i) hX
      (lt_of_not_ge hSX) (hcut i) (t+u)
    simp_rw [hz,norm_zero]
    rw [intervalIntegral.integral_zero,zero_div]
    positivity


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUniformMean
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fixed nonzero-angular height mean across both ranges.
The fixed dilation is absorbed in constants and the existing polynomial
scale range; no metaplectic Voronoi premise is used. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_completed_angular_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0≤M)
    {ι : Type*} {W : ι→ℝ→ℂ} (hW : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ≠0)
    {η B : ℝ} (hη : 0<η) (hB : 0≤B) :
    ∃ K : ℝ, 0≤K ∧ ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1≤Y → 0<X → 1≤T →
      norm r≤Y^B → T≤Y^B → Y^(-B)≤X → X≤Y^B →
      (∫ t in T..2*T,‖metaplecticHeightCompleted r ℓ (W i) X t‖)/T≤
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨C,hC,hshort⟩ := hW.cubicTheta_completed_short_mean hMV hM hη hB
  obtain ⟨m,D,hm,hD,hlong⟩ := hW.cubicTheta_completed_dilated_long_mean hMV hM hℓ
    hη (show 0≤B+1 by linarith)
  have hGammaMinus := angularGammaQuotientStripBound_proved (metaplecticAngularShift ℓ-1/6)
    (-((m:ℝ)-1/2)) (by linarith [metaplecticAngularShift_nonneg ℓ])
  have hGammaPlus := angularGammaQuotientStripBound_proved (metaplecticAngularShift ℓ+1/6)
    (-((m:ℝ)-1/2)) (by linarith [metaplecticAngularShift_nonneg ℓ])
  refine ⟨C+D*(729:ℝ)^η,by positivity,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hXY
  have hnr := norm_nonneg r
  have hcommon : 0≤Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by positivity
  by_cases hs : X≤729*Real.sqrt (norm r)*T^2
  · have hh := hshort i r hr ℓ Y X T 0 hY hX hT hXY hs
    simp only [add_zero] at hh
    apply hh.trans
    nlinarith only [mul_nonneg (mul_nonneg hD (Real.rpow_nonneg (by norm_num : (0:ℝ)≤729) η)) hcommon]
  · have hZ : 1≤729*Y := by linarith
    have hlong' : Real.sqrt (norm r)*T^2≤X/729 := by linarith
    have hdown : (729*Y)^(-(B+1))≤X/729 :=
      (cubicTheta_dilated_lower_scale hY hB).trans (div_le_div_of_nonneg_right hYX (by norm_num))
    have hu := cubicTheta_dilated_upper_scale hY hB
    have hh := hlong i r hr hsr (729*Y) (X/729) T hZ (by positivity) hT
      (hRY.trans hu) (hTY.trans hu) hdown hlong' hGammaMinus hGammaPlus
    have hx : 729*(X/729)=X := by ring
    rw [hx,Real.mul_rpow (by norm_num : (0:ℝ)≤729) (by linarith : 0≤Y)] at hh
    have hsmall : Real.sqrt (X/729)≤Real.sqrt X := Real.sqrt_le_sqrt (by linarith)
    calc
      _ ≤ D*Real.sqrt (X/729)*((729:ℝ)^η*Y^η)*norm r^(1/4:ℝ)*Real.sqrt T := hh
      _ ≤ D*Real.sqrt X*((729:ℝ)^η*Y^η)*norm r^(1/4:ℝ)*Real.sqrt T := by gcongr
      _ ≤ _ := by nlinarith only [mul_nonneg hC hcommon]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUniformNegativeLong
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform actual nonzero-angular long-height estimate, with
its exact primal dilation and proved coefficient bounds. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma sqrt_level_negative_power_p4 {Y R X B : ℝ}
    (hY : 0 < Y) (hRY : R ≤ Y^B) (hYX : Y^(-B) ≤ X) :
    Real.sqrt R*Y^(-B) ≤ Real.sqrt X := by
  have he : Real.sqrt (Y^B)*Y^(-B) = Real.sqrt (Y^(-B)) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hY.le,
      ←Real.rpow_add hY,←Real.rpow_mul hY.le]
    congr 1
    ring
  calc
    _ ≤ Real.sqrt (Y^B)*Y^(-B) := mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt hRY) (Real.rpow_nonneg hY.le _)
    _ = Real.sqrt (Y^(-B)) := he
    _ ≤ _ := Real.sqrt_le_sqrt hYX

/-- For each small loss, the far-left line is chosen once before all
levels, lengths and heights. Its Gamma bounds are exactly the published
bounded-strip input at that chosen line. -/
theorem UniformLogWeights.cubicTheta_completed_dilated_negative_long_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ≠0)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ (m : ℕ) (K : ℝ), 2 ≤ m ∧ 0 ≤ K ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1 ≤ Y → 0 < X → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X →
      Real.sqrt (norm r)*T^2 ≤ X →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)) →
      (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ (W i) (729*X) (-t)‖)/T ≤
          K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  let B' := 7*B+η
  have hB' : 0 ≤ B' := by dsimp [B']; positivity
  have hBB' : B ≤ B' := by dsimp [B']; linarith
  have h7B : 7*B ≤ B' := by dsimp [B']; linarith
  have hσ : (0:ℝ) < 1/20000 := by norm_num
  obtain ⟨m,C,hm,hms,hC,htail⟩ := h.metaplectic_twisted_tail_arbitrary_power cubicThetaCoreCoefficient_bounds ℓ hσ hη B' B
  obtain ⟨D,hD,hret⟩ := h.metaplectic_retained_negative_voronoi_subpower cubicThetaCoreCoefficient_bounds hMV hM ℓ (div_pos hη (by norm_num : (0:ℝ) < 2)) hB'
  let P := 3^(7/2:ℝ)*(2*Real.pi)^2
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨m,81*(4*D+C/P),hm,by positivity,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hlong hgm hgp
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hR1 := one_le_norm (primary_ne_zero hr)
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let J := metaplecticNaturalCutoff Y (norm r) T X η
  have hJ1 : 1 ≤ J := metaplecticNaturalCutoff_ge_one _ _ _ _ _
  have hJ : 0 < J := zero_lt_one.trans_le hJ1
  have hJY : J ≤ Y^B' := metaplecticNaturalCutoff_polynomial hY hR hTp hB hη.le hRY hTY hYX
  have hRY' : norm r ≤ Y^B' := hRY.trans (Real.rpow_le_rpow_of_exponent_le hY hBB')
  have hTY' : T ≤ Y^B' := hTY.trans (Real.rpow_le_rpow_of_exponent_le hY hBB')
  have hDY : norm r^2*T^4/X ≤ Y^B' :=
    (metaplectic_natural_length_polynomial hY hR hTp hRY hTY hYX).trans
      (Real.rpow_le_rpow_of_exponent_le hY h7B)
  have hcut : (norm r^2*T^4/X)/J ≤ Y^(-η) := metaplecticNaturalCutoff_ratio hYp
  have ht (t : ℝ) (htt : |t| ≤ 2*T) :
      ‖∑' nd, metaplecticFarTailTerm cubicThetaCoreCoefficient r ℓ (fun x => W i x*mellinPhase t x)
        ((m:ℝ)-1/2) X J nd‖ ≤ C*Y^(-B) :=
    htail i r hr hsr Y X J T hY hX hJ hT hRY' hTY' hDY hcut t htt
  have ha : 0 ≤ (m:ℝ)-1/2 := hσ.le.trans hms
  have hscale : (729*X)/729=X := by ring
  have hb := cubicTheta_completed_negative_tail_mean hr hsr hℓ (W i) (h.compact i) (h.positive i) (h.smooth i)
    (X:=729*X) (by positivity) (hσ.trans_le hms) hTp hgm hgp
    (by simpa only [hscale] using ht)
  simp only [hscale] at hb
  have hv := hret i r hr hsr Y ((m:ℝ)-1/2) X J T hY ha hX hJ1 hTp hRY' hJY hgm hgp
  have hg := metaplectic_long_sqrt_factor hY hR1 hT hη.le
    (metaplectic_long_cutoff hY hR1 hT hX hη.le hlong)
  change 1+Real.sqrt (4*J/(norm r*T)) ≤ _ at hg
  have hyprod : Y^(η/2)*Y^(η/2) = Y^η := by rw [←Real.rpow_add hYp]; congr 1; ring
  have hmain : (∫ t in T..2*T, ‖metaplecticPrefactor r ℓ*
      ∑ nd ∈ metaplecticDualBall J,
        metaplecticDualTerm cubicThetaCoreCoefficient r ℓ (fun x => W i x*mellinPhase (-t) x) ((m:ℝ)-1/2) X nd‖)/T ≤
        4*D*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
    apply hv.trans
    calc
      _ ≤ D*Real.sqrt X*Y^(η/2)*(4*Y^(η/2)*norm r^(1/4:ℝ)*Real.sqrt T) := by gcongr
      _ = _ := by
        rw [show D*Real.sqrt X*Y^(η/2)*(4*Y^(η/2)*norm r^(1/4:ℝ)*Real.sqrt T) =
          4*D*Real.sqrt X*(Y^(η/2)*Y^(η/2))*norm r^(1/4:ℝ)*Real.sqrt T by ring,hyprod]
  have hf : 1 ≤ Y^η*norm r^(1/4:ℝ)*Real.sqrt T :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hY hη.le)
        (Real.one_le_rpow hR1 (by norm_num))) (Real.one_le_sqrt.mpr hT)
  have htailbound : ‖metaplecticPrefactor r ℓ‖*(C*Y^(-B)) ≤
      C/P*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
    rw [norm_metaplecticPrefactor (primary_ne_zero hr)]
    calc
      _ = C/P*(Real.sqrt (norm r)*Y^(-B)) := by dsimp [P]; ring
      _ ≤ C/P*Real.sqrt X := mul_le_mul_of_nonneg_left
        (sqrt_level_negative_power_p4 hYp hRY hYX) (by positivity)
      _ ≤ (C/P*Real.sqrt X)*(Y^η*norm r^(1/4:ℝ)*Real.sqrt T) :=
        le_mul_of_one_le_right (by positivity) hf
      _ = _ := by ring
  calc
    _ ≤ _ := hb
    _ ≤ 81*(4*D*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T+
        C/P*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T) :=
      mul_le_mul_of_nonneg_left (add_le_add hmain htailbound) (by norm_num)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticNegativeShort
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflection of the interval reduces the negative short-polynomial
mean to the already proved arbitrary-shift primal mean. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma integral_reflected_height (f : ℝ → ℝ) (T : ℝ) :
    (∫ t in T..2*T, f (-t)) = (∫ t in T..2*T, f (t-3*T)) := by
  let g := fun t : ℝ => f (t-3*T)
  have he := intervalIntegral.integral_comp_sub_left (a := T) (b := 2*T) g (3*T)
  rw [show 3*T-2*T = T by ring,show 3*T-T = 2*T by ring] at he
  have hg : (fun t => g (3*T-t)) = (fun t => f (-t)) := by
    funext t
    dsimp [g]
    congr 1
    ring
  rw [hg] at he
  exact he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUniformNegativeMean
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fixed nonzero-angular height mean across both ranges.
The fixed dilation is absorbed in constants and the existing polynomial
scale range; no metaplectic Voronoi premise is used. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_completed_negative_angular_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0≤M)
    {ι : Type*} {W : ι→ℝ→ℂ} (hW : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ≠0)
    {η B : ℝ} (hη : 0<η) (hB : 0≤B) :
    ∃ K : ℝ, 0≤K ∧ ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1≤Y → 0<X → 1≤T →
      norm r≤Y^B → T≤Y^B → Y^(-B)≤X → X≤Y^B →
      (∫ t in T..2*T,‖metaplecticHeightCompleted r ℓ (W i) X (-t)‖)/T≤
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨C,hC,hshort⟩ := hW.cubicTheta_completed_short_mean hMV hM hη hB
  obtain ⟨m,D,hm,hD,hlong⟩ := hW.cubicTheta_completed_dilated_negative_long_mean hMV hM hℓ
    hη (show 0≤B+1 by linarith)
  have hGammaMinus := angularGammaQuotientStripBound_proved (metaplecticAngularShift ℓ-1/6)
    (-((m:ℝ)-1/2)) (by linarith [metaplecticAngularShift_nonneg ℓ])
  have hGammaPlus := angularGammaQuotientStripBound_proved (metaplecticAngularShift ℓ+1/6)
    (-((m:ℝ)-1/2)) (by linarith [metaplecticAngularShift_nonneg ℓ])
  refine ⟨C+D*(729:ℝ)^η,by positivity,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hXY
  have hnr := norm_nonneg r
  have hcommon : 0≤Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by positivity
  by_cases hs : X≤729*Real.sqrt (norm r)*T^2
  · have hh := hshort i r hr ℓ Y X T (-(3*T)) hY hX hT hXY hs
    have he := integral_reflected_height (fun t : ℝ => ‖metaplecticHeightCompleted r ℓ (W i) X t‖) T
    rw [he]
    simp only [sub_eq_add_neg]
    apply hh.trans
    nlinarith only [mul_nonneg (mul_nonneg hD (Real.rpow_nonneg (by norm_num : (0:ℝ)≤729) η)) hcommon]
  · have hZ : 1≤729*Y := by linarith
    have hlong' : Real.sqrt (norm r)*T^2≤X/729 := by linarith
    have hdown : (729*Y)^(-(B+1))≤X/729 :=
      (cubicTheta_dilated_lower_scale hY hB).trans (div_le_div_of_nonneg_right hYX (by norm_num))
    have hu := cubicTheta_dilated_upper_scale hY hB
    have hh := hlong i r hr hsr (729*Y) (X/729) T hZ (by positivity) hT
      (hRY.trans hu) (hTY.trans hu) hdown hlong' hGammaMinus hGammaPlus
    have hx : 729*(X/729)=X := by ring
    rw [hx,Real.mul_rpow (by norm_num : (0:ℝ)≤729) (by linarith : 0≤Y)] at hh
    have hsmall : Real.sqrt (X/729)≤Real.sqrt X := Real.sqrt_le_sqrt (by linarith)
    calc
      _ ≤ D*Real.sqrt (X/729)*((729:ℝ)^η*Y^η)*norm r^(1/4:ℝ)*Real.sqrt T := hh
      _ ≤ D*Real.sqrt X*((729:ℝ)^η*Y^η)*norm r^(1/4:ℝ)*Real.sqrt T := by gcongr
      _ ≤ _ := by nlinarith only [mul_nonneg hC hcommon]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUniformSignedMean
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both actual angular height dyads, uniformly in the smooth family. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_completed_signed_angular_mean_oai
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1 ≤ Y → 0 < X → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X → X ≤ Y^B →
      ((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r ℓ (W i) X t‖)+
        (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ (W i) X t‖))/T ≤
          K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨C,hC,hpositive⟩ :=
    h.cubicTheta_completed_angular_mean hMV hM hℓ hη hB
  obtain ⟨D,hD,hnegative⟩ :=
    h.cubicTheta_completed_negative_angular_mean hMV hM hℓ hη hB
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hXY
  have hp := hpositive i r hr hsr Y X T hY hX hT hRY hTY hYX hXY
  have hn := hnegative i r hr hsr Y X T hY hX hT hRY hTY hYX hXY
  have he := intervalIntegral.integral_comp_neg (a := T) (b := 2*T)
    (fun t : ℝ => ‖metaplecticHeightCompleted r ℓ (W i) X t‖)
  rw [←he,add_div]
  calc
    _ ≤ D*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T+
        C*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := add_le_add hn hp
    _ = _ := by ring


end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_completed_signed_angular_mean_oai.{u_1} := @OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_completed_signed_angular_mean_oai.{u_1}
