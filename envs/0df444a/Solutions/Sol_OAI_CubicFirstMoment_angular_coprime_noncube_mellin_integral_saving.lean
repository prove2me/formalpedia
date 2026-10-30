-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_coprime_noncube_mellin_integral_saving
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:03:03.040129+00:00
-- url     : https://prove2.me/submissions/7dbe9ceb-75ce-42ac-80a8-81e0f4c9b431
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A016
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_angular_large_core_mellin_integral_saving
import Theorems.Thm_OAI_CubicFirstMoment_outer_core_block_sieve

section
-- module Solutions.OAIQ096_CM.CubicGram_Coordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_GramPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma normProfileFourier_mul_unit (W : ℝ → ℂ) {u : ℂ}
    (hu : Complex.normSq u = 1) (w : ℂ) :
    normProfileFourier W (u*w) = normProfileFourier W w := by
  have hu0 : u ≠ 0 := by
    intro he
    simp [he] at hu
  have hf : (fun z : ℂ => W (Complex.normSq (u⁻¹*z))) =
      (fun z : ℂ => W (Complex.normSq z)) := by
    funext z
    simp only [Complex.normSq_mul, Complex.normSq_inv, hu, inv_one, one_mul]
  have he := traceFourier_complexMul u⁻¹ (inv_ne_zero hu0)
    (fun z : ℂ => W (Complex.normSq z)) w
  rw [hf, Complex.normSq_inv, hu, inv_one, inv_one, one_smul] at he
  unfold normProfileFourier
  congr 1
  simpa only [div_inv_eq_mul, mul_comm] using he.symm

lemma normProfileFourier_eq_of_normSq_eq (W : ℝ → ℂ) {y y' : ℂ}
    (hy : Complex.normSq y = Complex.normSq y') :
    normProfileFourier W y = normProfileFourier W y' := by
  by_cases hy0 : y' = 0
  · have hy1 : y = 0 := Complex.normSq_eq_zero.mp (by simpa [hy0] using hy)
    rw [hy0, hy1]
  · have hu : Complex.normSq (y / y') = 1 := by
      rw [Complex.normSq_div, hy, div_self (mt Complex.normSq_eq_zero.mp hy0)]
    simpa only [div_mul_cancel₀ _ hy0] using normProfileFourier_mul_unit W hu y'

end CubicFirstMoment
end
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

theorem cube_decomposition (n : Eisenstein) :
    ∃ s t c : Eisenstein, Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧ n = s*t^2*c^3 := by
  refine UniqueFactorizationMonoid.induction_on_prime n ?_ ?_ ?_
  · exact ⟨1,1,0,squarefree_one,squarefree_one,isCoprime_one_left,by simp⟩
  · intro u hu
    exact ⟨u,1,1,hu.squarefree,squarefree_one,isCoprime_one_right,by simp⟩
  · intro b p hb hp ih
    obtain ⟨s,t,c,hss,hst,hcop,rfl⟩ := ih
    by_cases hps : p ∣ s
    · obtain ⟨s',rfl⟩ := hps
      have hps' : IsCoprime p s' := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hss).1
      have hpt : IsCoprime p t := hcop.of_mul_left_left
      refine ⟨s',p*t,c,hss.of_mul_right,
        squarefree_mul_iff.mpr ⟨hpt.isRelPrime,hp.squarefree,hst⟩,
        hps'.symm.mul_right hcop.of_mul_left_right,?_⟩
      ring
    · by_cases hpt : p ∣ t
      · obtain ⟨t',rfl⟩ := hpt
        refine ⟨s,t',p*c,hss,hst.of_mul_right,hcop.of_mul_right_right,?_⟩
        ring
      · have hps' := hp.coprime_iff_not_dvd.mpr hps
        have hpt' := hp.coprime_iff_not_dvd.mpr hpt
        refine ⟨p*s,t,c,squarefree_mul_iff.mpr ⟨hps'.isRelPrime,hp.squarefree,hss⟩,
          hst,hpt'.mul_left hcop,?_⟩
        ring

theorem squarefree_ramified_split (n : Eisenstein) (hs : Squarefree n) :
    ∃ d e : Eisenstein, d ∣ 3 ∧ IsCoprime e 3 ∧ n = d*e := by
  have h : ∀ n : Eisenstein, Squarefree n →
      ∃ d e : Eisenstein, d ∣ 3 ∧ IsCoprime e 3 ∧ n = d*e := by
    intro n
    refine UniqueFactorizationMonoid.induction_on_prime n ?_ ?_ ?_
    · intro hs
      have hh := hs 0 (by simp)
      exact (not_isUnit_zero hh).elim
    · intro u hu hs
      refine ⟨1,u,one_dvd _,?_,by simp⟩
      exact (isCoprime_zero_right.mpr hu).of_isCoprime_of_dvd_right (dvd_zero 3)
    · intro b p hb hp ih hs
      obtain ⟨d,e,hd,he,hbe⟩ := ih hs.of_mul_right
      have hpb : IsCoprime p b := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
      by_cases hp3 : p ∣ 3
      · have hpd : IsCoprime p d := (hbe ▸ hpb).of_mul_right_left
        refine ⟨p*d,e,hpd.mul_dvd hp3 hd,he,?_⟩
        rw [hbe]; ring
      · refine ⟨d,p*e,hd,(hp.coprime_iff_not_dvd.mpr hp3).mul_left he,?_⟩
        rw [hbe]; ring
  exact h n hs

lemma unit_residue_of_isCoprime_three {e : Eisenstein} (he : IsCoprime e 3) :
    IsUnit (Ideal.Quotient.mk (modulus 3) e) := by
  have h := he.map (Ideal.Quotient.mk (modulus 3))
  simpa only [residue_three_eq_zero, isCoprime_zero_right] using h

lemma norm_le_of_dvd {a b : Eisenstein} (hb : b ≠ 0) (hd : a ∣ b) :
    norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := hd
  have hc : c ≠ 0 := by intro h; simp [h] at hb
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg a) (one_le_norm hc)

theorem squarefree_primary_residual (n : Eisenstein) (hs : Squarefree n) :
    ∃ r s : Eisenstein, r ≠ 0 ∧ norm r ≤ 9 ∧ primary s ∧ Squarefree s ∧ n = r*s := by
  obtain ⟨d,e,hd,he,hde⟩ := squarefree_ramified_split n hs
  obtain ⟨u,hu,hprim⟩ := unit_lift_mod_three (unit_residue_of_isCoprime_three he)
  obtain ⟨v,rfl⟩ := hu
  have hd0 : d ≠ 0 := by
    intro hd0
    rw [hd0, zero_dvd_iff] at hd
    norm_num at hd
  have hvi : norm (↑v⁻¹ : Eisenstein) = 1 := by
    rw [← normNat_cast, normNat_of_isUnit (Units.isUnit _), Nat.cast_one]
  refine ⟨d*(↑v⁻¹ : Eisenstein),e*(↑v : Eisenstein),mul_ne_zero hd0 (Units.ne_zero _),?_,hprim,?_,?_⟩
  · rw [norm_mul_eq, hvi, mul_one]
    have h := norm_le_of_dvd (by norm_num : (3 : Eisenstein) ≠ 0) hd
    have h3 : norm (3 : Eisenstein) = 9 := by
      change Complex.normSq (3 : ℂ) = 9
      norm_num
    simpa only [h3] using h
  · have hes : Squarefree e := (hde ▸ hs).of_mul_right
    exact squarefree_mul_iff.mpr ⟨((isCoprime_zero_left.mpr (Units.isUnit v)).of_isCoprime_of_dvd_left (dvd_zero e)).isRelPrime,hes,
      (Units.isUnit v).squarefree⟩
  · rw [hde]
    simp [mul_assoc, mul_left_comm, mul_comm]

end CubicFirstMoment

namespace CubicFirstMoment

theorem full_cube_decomposition {n : Eisenstein} (hn : n ≠ 0) :
    ∃ r s t c : Eisenstein, r ≠ 0 ∧ norm r ≤ 729 ∧
      primary s ∧ primary t ∧ Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧
      c ≠ 0 ∧ n = r*s*t^2*c^3 := by
  obtain ⟨s₀,t₀,c,hs₀,ht₀,hst,hn'⟩ := cube_decomposition n
  obtain ⟨r,s,hr0,hr,hs,hss,hs'⟩ := squarefree_primary_residual s₀ hs₀
  obtain ⟨q,t,hq0,hq,ht,hst',ht'⟩ := squarefree_primary_residual t₀ ht₀
  have hc0 : c ≠ 0 := by intro hc; simp [hc] at hn'; exact hn hn'
  have hcop : IsCoprime s t :=
    hst.of_isCoprime_of_dvd_left (hs' ▸ dvd_mul_left s r) |>.of_isCoprime_of_dvd_right
      (ht' ▸ dvd_mul_left t q)
  refine ⟨r*q^2,s,t,c,mul_ne_zero hr0 (pow_ne_zero _ hq0),?_,hs,ht,hss,hst',hcop,hc0,?_⟩
  · rw [norm_mul_eq]
    have he : norm (q^2) = norm q ^ 2 := by simp [pow_two]
    rw [he]
    have hq2 : norm q ^ 2 ≤ 81 := by nlinarith [norm_nonneg q]
    nlinarith [norm_nonneg r, sq_nonneg (norm q)]
  · rw [hn',hs',ht']; ring

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeEstimates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric decay, cube frequency dyads and numerical block inequalities. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_squarefreePrimaryDyad {n : Eisenstein} {j : ℕ} :
    n ∈ squarefreePrimaryDyad j ↔ n ∈ frequencyDyad j ∧ primary n ∧ Squarefree n := by
  simp [squarefreePrimaryDyad]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- A stronger convergent exponent gives a power tail without losing a
factor to the norm fibers. -/
theorem eisenstein_norm_rpow_tail {D s t : ℝ} (hD : 0 < D)
    (hs : 1 < s) (hst : s < t) :
    (∑' a : Eisenstein, if D < norm a then norm a^(-t) else 0) ≤
      D^(s-t)*(∑' a : Eisenstein, norm a^(-s)) := by
  have ht := summable_eisenstein_norm_rpow (hs.trans hst)
  have htail := ht.indicator (fun a => D < norm a)
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ htail ((summable_eisenstein_norm_rpow hs).mul_left _)
  intro a
  change (if D < norm a then norm a^(-t) else 0) ≤ D^(s-t)*norm a^(-s)
  by_cases ha : D < norm a
  · simpa only [ha,ite_true, if_true] using norm_rpow_tail_pointwise hD hst ha
  · simp only [ha,ite_false, if_false]
    exact mul_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg (norm_nonneg a) _)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedAbel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth weighting of prime-character sums

Partial summation applies the
published unweighted Hecke prime estimate to independently specified
smooth prime weights. It also retains the derivative cost of a norm twist.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

/-- Complex partial summation with an explicit bound for the cumulative
coefficients. The right side records endpoint values and total variation. -/
theorem weighted_abel_bound (c : ℕ → ℂ) (f : ℝ → ℂ)
    {a b H : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hderiv : IntegrableOn (deriv f) (Set.Icc a b))
    (hc : ∀ t ∈ Set.Icc a b, ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ H) :
    ‖∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k‖ ≤
      H * (‖f a‖ + ‖f b‖ + ∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  let S : ℝ → ℂ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
  have hSa : ‖S a‖ ≤ H := hc a ⟨le_rfl, hab⟩
  have hSb : ‖S b‖ ≤ H := hc b ⟨hab, le_rfl⟩
  have hp : IntegrableOn (fun t => deriv f t * S t) (Set.Ioc a b) :=
    (integrableOn_mul_sum_Icc c ha hderiv).mono_set Set.Ioc_subset_Icc_self
  have hd0 : IntegrableOn (fun t => H * ‖deriv f t‖) (Set.Icc a b) :=
    hderiv.norm.const_mul H
  have hd : IntegrableOn (fun t => H * ‖deriv f t‖) (Set.Ioc a b) :=
    hd0.mono_set Set.Ioc_subset_Icc_self
  have hpoint : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖deriv f t * S t‖ ≤ H * ‖deriv f t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, mul_comm H]
    exact mul_le_mul_of_nonneg_left (hc t (Set.Ioc_subset_Icc_self ht))
      (_root_.norm_nonneg _)
  have hIntegral : ‖∫ t in Set.Ioc a b, deriv f t * S t‖ ≤
      H * ∫ t in Set.Ioc a b, ‖deriv f t‖ := by
    calc
      _ ≤ ∫ t in Set.Ioc a b, ‖deriv f t * S t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc a b, H * ‖deriv f t‖ := integral_mono_ae hp.norm hd hpoint
      _ = _ := integral_const_mul H _
  rw [sum_mul_eq_sub_sub_integral_mul c ha hab hdiff hderiv]
  change ‖f b * S b - f a * S a - ∫ t in Set.Ioc a b, deriv f t * S t‖ ≤ _
  calc
    _ ≤ ‖f b * S b - f a * S a‖ + ‖∫ t in Set.Ioc a b, deriv f t * S t‖ :=
      norm_sub_le _ _
    _ ≤ (‖f b * S b‖ + ‖f a * S a‖) +
        H * ∫ t in Set.Ioc a b, ‖deriv f t‖ :=
      add_le_add (norm_sub_le _ _) hIntegral
    _ ≤ (‖f b‖ * H + ‖f a‖ * H) +
        H * ∫ t in Set.Ioc a b, ‖deriv f t‖ := by
      simp only [norm_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hSb (_root_.norm_nonneg _))
        (mul_le_mul_of_nonneg_left hSa (_root_.norm_nonneg _))) le_rfl
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedPrimeInput
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the published prime input to smooth prime weights

Prime elements of equal norm are collected without identifying conjugate
prime ideals. Complex Abel summation then derives the smooth-weighted
estimate from `CubicPrimeSiegelWalfisz`. The weighted estimate follows by partial summation.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

lemma primeNormCoefficient_cumulative (R t : ℝ) (χ : Eisenstein → ℂ)
    (ht : 0 ≤ t) (htR : t ≤ R) :
    (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, primeNormCoefficient R χ n) = primeCutoffSum χ t := by
  simp only [primeNormCoefficient]
  rw [Finset.sum_comm, primeCutoffSum_eq_sum]
  have he (p : Eisenstein) :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, if n = normNat p then χ p else 0) =
        if norm p ≤ t then χ p else 0 := by
    simp only [Finset.sum_ite_eq', Finset.mem_Icc, Nat.zero_le, true_and]
    simp only [Nat.le_floor_iff ht, normNat_cast]
  simp_rw [he]
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, mem_primeCutoff]
  constructor
  · intro hp
    exact ⟨hp.1.1, hp.2⟩
  · intro hp
    exact ⟨⟨hp.1, hp.2.trans htR⟩, hp.2⟩

lemma primeNormCoefficient_weighted (a b : ℝ) (f : ℝ → ℂ) (χ : Eisenstein → ℂ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * primeNormCoefficient b χ n) =
      ∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p) * χ p := by
  simp only [primeNormCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hpb : normNat p ≤ ⌊b⌋₊ := (Nat.le_floor_iff (ha.trans hab)).mpr
    (by rw [normNat_cast]; exact (mem_primeCutoff.mp hp).2)
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_Ioc, hpb, and_true]
  simp only [Nat.floor_lt ha, normNat_cast]

/-- Weighted interval sums inherit a uniform bound for all their unweighted
prime prefixes, at the explicit cost of total variation of the weight. -/
theorem weighted_prime_bound (χ : Eisenstein → ℂ) (f : ℝ → ℂ)
    {a b H : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hderiv : IntegrableOn (deriv f) (Set.Icc a b))
    (hχ : ∀ t ∈ Set.Icc a b, ‖primeCutoffSum χ t‖ ≤ H) :
    ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p) * χ p‖ ≤
      H * (‖f a‖ + ‖f b‖ + ∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  rw [← primeNormCoefficient_weighted a b f χ ha hab]
  apply weighted_abel_bound (primeNormCoefficient b χ) f ha hab hdiff hderiv
  intro t ht
  rw [primeNormCoefficient_cumulative b t χ (ha.trans ht.1) ht.2]
  exact hχ t ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem hasDerivAt_mellinPhase (u : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (mellinPhase u)
      (mellinPhase u x * ((u / x : ℝ) : ℂ) * Complex.I) x := by
  have h := (((Real.hasDerivAt_log hx).const_mul u).ofReal_comp.mul_const Complex.I).cexp
  unfold mellinPhase
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

theorem hasDerivAt_weighted_mellinPhase {w : ℝ → ℂ} {w' : ℂ} {x : ℝ}
    (hw : HasDerivAt w w' x) (u : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t => w t * mellinPhase u t)
      (w' * mellinPhase u x + w x * (mellinPhase u x * ((u / x : ℝ) : ℂ) * Complex.I)) x :=
  hw.mul (hasDerivAt_mellinPhase u hx)

/-- The derivative loss is linear in the Mellin height and inversely
proportional to the norm variable. -/
theorem norm_deriv_weighted_mellinPhase {w : ℝ → ℂ} {w' : ℂ} {x : ℝ}
    (hw : HasDerivAt w w' x) (u : ℝ) (hx : 0 < x) :
    ‖deriv (fun t => w t * mellinPhase u t) x‖ ≤
      ‖w'‖ + ‖w x‖ * (|u| / x) := by
  rw [(hasDerivAt_weighted_mellinPhase hw u hx.ne').deriv]
  calc
    _ ≤ ‖w' * mellinPhase u x‖ +
        ‖w x * (mellinPhase u x * ((u / x : ℝ) : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ = _ := by
      simp only [norm_mul, mellinPhase_norm, Complex.norm_I, mul_one, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hx]

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

/-- The normalized two-sided height mean used for the small-conductor
noncube contribution. Both positive and negative height intervals occur. -/
theorem fixedAngular_translated_dyadicMeanSquare {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (s : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ) (M : ℝ)
    (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hzero : ∀ b ∈ s, b ≠ 0)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M)
    (ℓ : ℤ) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    ((∫ t in T..2 * T, ‖∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)‖ ^ 2) +
     (∫ t in -2 * T..-T, ‖∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)‖ ^ 2)) / T ≤
      2 * C * (1 + (Z : ℝ) / T) * M * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  have hpos := fixedAngular_translated_meanSquare hMV hC s v Z M hs hzero hM ℓ u
    (a := T) (b := 2 * T) (by linarith)
  have hneg := fixedAngular_translated_meanSquare hMV hC s v Z M hs hzero hM ℓ u
    (a := -2 * T) (b := -T) (by linarith)
  have hsum := div_le_div_of_nonneg_right (add_le_add hpos hneg) hT.le
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeNormFibers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Norm fibers for a fixed number of primary prime factors

Equal norms give `b * conjugate b = b₀ * conjugate b₀`.  Consequently every
prime factor of `b` is one of the prime factors of `b₀` or its conjugate.
For products of `k` primary primes this bounds every norm fiber by
`(2 * k)^k`, uniformly in all prime supports and the norm.  No general
divisor estimate is needed for the structured coefficients.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A prime in a tuple of the same norm must occur in the reference tuple
or in its conjugate. Primary normalization turns association into equality. -/
lemma prime_tuple_norm_range_subset (f g : ι → Eisenstein)
    (hf : ∀ i, primaryPrime (f i)) (hg : ∀ i, primaryPrime (g i))
    (hn : normNat (∏ i, g i) = normNat (∏ i, f i)) (i : ι) :
    g i ∈ Finset.univ.image f ∪ Finset.univ.image (fun j => conjugate (f j)) := by
  have heq : (∏ j, g j) * conjugate (∏ j, g j) =
      (∏ j, f j) * conjugate (∏ j, f j) := by
    rw [← normNat_cast_eq_mul_conjugate, ← normNat_cast_eq_mul_conjugate, hn]
  have hd : g i ∣ (∏ j, f j) * conjugate (∏ j, f j) :=
    heq ▸ dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem g (Finset.mem_univ i)) _
  rcases (hg i).2.dvd_or_dvd hd with hd | hd
  · obtain ⟨j, _, hj⟩ := ((hg i).2.dvd_finsetProd_iff f).mp hd
    have hj' : g i = f j := primary_associated_eq (hg i).1 (hf j).1
      (((hg i).2.dvd_prime_iff_associated (hf j).2).mp hj)
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj'.symm⟩))
  · rw [map_prod] at hd
    obtain ⟨j, _, hj⟩ := ((hg i).2.dvd_finsetProd_iff (fun j => conjugate (f j))).mp hd
    have hj' : g i = conjugate (f j) := primary_associated_eq (hg i).1
      (primaryPrime_conjugate (hf j)).1
      (((hg i).2.dvd_prime_iff_associated (primaryPrime_conjugate (hf j)).2).mp hj)
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj'.symm⟩))

/-- The number of distinct products with a prescribed norm is bounded
solely in terms of the number of prime factors, even with repetitions. -/
theorem primeProduct_norm_fiber_card (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (n : ℕ) :
    ((orderedConvolutionSupport S).filter (fun b => normNat b = n)).card ≤
      (2 * Fintype.card ι) ^ (Fintype.card ι) := by
  let T := (orderedConvolutionSupport S).filter (fun b => normNat b = n)
  by_cases ht : T.Nonempty
  · obtain ⟨b, hb⟩ := ht
    obtain ⟨hbs, hbn⟩ := Finset.mem_filter.mp hb
    obtain ⟨f, hf, hfb⟩ := Finset.mem_image.mp hbs
    let A := Finset.univ.image f ∪ Finset.univ.image (fun j => conjugate (f j))
    have hprime : ∀ i, primaryPrime (f i) :=
      fun i => hS i (f i) ((Fintype.mem_piFinset.mp hf) i)
    have hsub : T ⊆ (Fintype.piFinset (fun _ : ι => A)).image (fun g => ∏ i, g i) := by
      intro b' hb'
      obtain ⟨hb's, hb'n⟩ := Finset.mem_filter.mp hb'
      obtain ⟨g, hg, hgb⟩ := Finset.mem_image.mp hb's
      have hn : normNat (∏ i, g i) = normNat (∏ i, f i) := by
        rw [hgb, hfb, hb'n, hbn]
      refine Finset.mem_image.mpr ⟨g, Fintype.mem_piFinset.mpr ?_, hgb⟩
      intro i
      exact prime_tuple_norm_range_subset f g hprime
        (fun j => hS j (g j) ((Fintype.mem_piFinset.mp hg) j)) hn i
    have hcard : A.card ≤ 2 * Fintype.card ι := by
      have hfcard : (Finset.univ.image f).card ≤ Fintype.card ι := by
        simpa using (Finset.card_image_le (s := (Finset.univ : Finset ι)) (f := f))
      have hccard : (Finset.univ.image (fun j => conjugate (f j))).card ≤ Fintype.card ι := by
        simpa using (Finset.card_image_le (s := (Finset.univ : Finset ι))
          (f := fun j => conjugate (f j)))
      calc
        A.card ≤ (Finset.univ.image f).card +
            (Finset.univ.image (fun j => conjugate (f j))).card := Finset.card_union_le _ _
        _ ≤ Fintype.card ι + Fintype.card ι := add_le_add hfcard hccard
        _ = 2 * Fintype.card ι := by omega
    calc
      T.card ≤ ((Fintype.piFinset (fun _ : ι => A)).image (fun g => ∏ i, g i)).card :=
        Finset.card_le_card hsub
      _ ≤ (Fintype.piFinset (fun _ : ι => A)).card := Finset.card_image_le
      _ = A.card ^ (Fintype.card ι) := by simp [Fintype.card_piFinset]
      _ ≤ _ := Nat.pow_le_pow_left hcard _
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change T.card ≤ _
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeSquareSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse support from a large square divisor, used to remove repeated
large primes in the exceptional character moments. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma square_multiples_normBall {Y : ℝ} {d b : Eisenstein}
    (hd : d ≠ 0) (hb : b ∈ nonzeroNormBall Y) (hdiv : d^2 ∣ b) :
    b ∈ (nonzeroNormBall (Y/(norm d)^2)).image (fun c => d^2*c) := by
  obtain ⟨c,rfl⟩ := hdiv
  have hspec := mem_nonzeroNormBall.mp hb
  have hc : c ≠ 0 := by intro h; simp [h] at hspec
  have hnorm : norm (d^2*c) = (norm d)^2*norm c := by
    simp [pow_two,mul_assoc]
  apply Finset.mem_image.mpr
  refine ⟨c,mem_nonzeroNormBall.mpr ⟨?_,hc⟩,rfl⟩
  apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_of_ne_zero hd))).mpr
  have h := hspec.1
  rw [hnorm] at h
  nlinarith

/-- Cardinality is at most `C Y / sqrt D`, uniformly for positive `D`.
The proof uses only planar lattice counting and a convergent norm series. -/
theorem largeSquareSupport_card_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y D : ℝ, 0 ≤ Y → 0 < D →
      ((largeSquareSupport Y D).card:ℝ) ≤ C*Y*D^(-(1/2:ℝ)) := by
  let Z := ∑' d : Eisenstein, norm d^(-(3/2:ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  refine ⟨18*Z+1,by positivity,?_⟩
  intro Y D hY hD
  let T := (nonzeroNormBall Y).filter (fun d => D < norm d)
  let F (d : Eisenstein) := (nonzeroNormBall (Y/(norm d)^2)).image (fun c => d^2*c)
  have hcover : largeSquareSupport Y D ⊆ T.biUnion F := by
    intro b hb
    obtain ⟨hball,d,hd,hdiv⟩ := Finset.mem_filter.mp hb
    have hd0 : d ≠ 0 := norm_eq_zero_iff.not.mp (ne_of_gt (hD.trans hd))
    have hdvd : d ∣ b := (dvd_pow_self d (by norm_num : 2 ≠ 0)).trans hdiv
    have hdb : norm d ≤ norm b := norm_le_of_dvd (mem_nonzeroNormBall.mp hball).2 hdvd
    apply Finset.mem_biUnion.mpr
    refine ⟨d,Finset.mem_filter.mpr ⟨mem_nonzeroNormBall.mpr
      ⟨hdb.trans (mem_nonzeroNormBall.mp hball).1,hd0⟩,hd⟩,?_⟩
    exact square_multiples_normBall hd0 hball hdiv
  have hcard : ((largeSquareSupport Y D).card:ℝ) ≤ ∑ d ∈ T, ((F d).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hsum : (∑ d ∈ T, 1/(norm d)^2) ≤ D^(-(1/2:ℝ))*Z := by
    have htail := eisenstein_norm_rpow_tail (s := (3/2:ℝ)) (t := 2) hD
      (by norm_num) (by norm_num)
    norm_num only at htail
    apply le_trans _ htail
    have hs := (summable_eisenstein_norm_rpow (s := 2) (by norm_num)).indicator
      (fun d => D < norm d)
    calc
      _ = ∑ d ∈ T, if D < norm d then norm d^(-(2:ℝ)) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hn := (Finset.mem_filter.mp hd).2
        rw [ite_eq_left hn,Real.rpow_neg (norm_nonneg d),Real.rpow_two,one_div]
      _ ≤ _ := hs.sum_le_tsum T (fun d _ => by
        split_ifs
        · exact Real.rpow_nonneg (norm_nonneg d) _
        · exact le_rfl)
  calc
    _ ≤ ∑ d ∈ T, ((F d).card:ℝ) := hcard
    _ ≤ ∑ d ∈ T, 18*(Y/(norm d)^2) := by
      apply Finset.sum_le_sum
      intro d hd
      have hi : ((F d).card:ℝ) ≤ ((nonzeroNormBall (Y/(norm d)^2)).card:ℝ) := by
        exact_mod_cast Finset.card_image_le
      exact hi.trans (nonzeroNormBall_card_le (by positivity))
    _ = 18*Y*(∑ d ∈ T, 1/(norm d)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 18*Y*(D^(-(1/2:ℝ))*Z) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := by nlinarith [Real.rpow_nonneg hD.le (-(1/2:ℝ))]

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

/-- Removing nonsquarefree products never enlarges a coefficient; its
error also obeys the same uniform coefficient bound. -/
theorem convolutionError_norm_bound (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (M : ι → ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (hM : ∀ i, 0 ≤ M i) (hw : ∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i)
    (b : Eisenstein) :
    ‖orderedConvolution S w b-squarefreeConvolution S w b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  by_cases hs : Squarefree b
  · simp only [squarefreeConvolution,ite_eq_left hs,sub_self,norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))
  · simpa only [squarefreeConvolution,ite_eq_right hs,sub_zero] using
      orderedConvolution_norm_bound S w M hS hM hw b

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RepeatedPrimeSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squarefree prime-convolution discrepancy has sparse support.
This supplies the support saving before the character-moment estimates. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every surviving discrepancy coefficient is divisible by the square
of one of the large supported primes. -/
theorem convolutionError_mem_largeSquareSupport
    (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ) (Y D : ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p)
    (hY : ∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y)
    {b : Eisenstein} (hb : squarefreeConvolutionError S w b ≠ 0) :
    b ∈ largeSquareSupport Y D := by
  have hns : ¬Squarefree b := by
    intro hs
    simp [squarefreeConvolutionError,squarefreeConvolution,hs] at hb
  have ho : orderedConvolution S w b ≠ 0 := by
    simpa only [squarefreeConvolutionError,squarefreeConvolution,ite_eq_right hns,sub_zero] using hb
  obtain ⟨f,hf,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero ho
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  have hprime : ∀ i, primaryPrime (f i) :=
    fun i => (hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)).1
  have hnot : ¬Function.Injective f := by
    intro hi
    exact hns (hfb ▸ (squarefree_prime_tuple_iff f hprime).mpr hi)
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hnot
  have hdvd : (f i)^2 ∣ ∏ k, f k := by
    have h := Finset.prod_dvd_prod_of_subset ({i,j}:Finset ι) Finset.univ f
      (Finset.subset_univ _)
    simpa [hne,hij,pow_two] using h
  have hprod0 : (∏ i, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => (hprime i).2.ne_zero)
  apply Finset.mem_filter.mpr
  refine ⟨mem_nonzeroNormBall.mpr ⟨?_,?_⟩,f i,?_,?_⟩
  · exact hfb ▸ hY f hfs
  · exact hfb ▸ hprod0
  · exact (hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)).2
  · exact hfb ▸ hdvd

/-- Uniform energy saving for the actual discrepancy coefficients.
A divisor-type coefficient bound may be inserted as `E`; the support
saving itself is unconditional and independent of that bound. -/
theorem convolutionError_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (Y D E : ℝ),
      0 ≤ Y → 0 < D → 0 ≤ E →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖ ≤ E) →
      (∑ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y*D^(-(1/2:ℝ))*E^2 := by
  obtain ⟨C,hC,hcount⟩ := largeSquareSupport_card_bound
  refine ⟨C,hC,?_⟩
  intro S w Y D E hY hD hE hS hprod hbound
  let T := (orderedConvolutionSupport S).filter (fun b => squarefreeConvolutionError S w b ≠ 0)
  have hsub : T ⊆ largeSquareSupport Y D := by
    intro b hb
    exact convolutionError_mem_largeSquareSupport S w Y D hS hprod (Finset.mem_filter.mp hb).2
  have hcard : (T.card:ℝ) ≤ C*Y*D^(-(1/2:ℝ)) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount Y D hY hD)
  have heq : (∑ b ∈ T, ‖squarefreeConvolutionError S w b‖^2) =
      ∑ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hnot
    have hz : squarefreeConvolutionError S w b = 0 := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨hb,hn⟩)
    simp [hz]
  rw [← heq]
  calc
    _ ≤ ∑ _b ∈ T, E^2 := by
      apply Finset.sum_le_sum
      intro b hb
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) (hbound b (Finset.mem_filter.mp hb).1) 2
    _ = (T.card:ℝ)*E^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg E)

/-- The coefficient-amplitude hypothesis is discharged for the actual prime
convolution by the uniform prime-tuple multiplicity bound. -/
theorem primeConvolutionError_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y D : ℝ),
      0 ≤ Y → 0 < D → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      (∑ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y*D^(-(1/2:ℝ))*
          (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  obtain ⟨C,hC,hbound⟩ := convolutionError_energy_bound (ι := ι)
  refine ⟨C,hC,?_⟩
  intro S w M Y D hY hD hM hS hprod hw
  apply hbound S w Y D _ hY hD (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => hM i)))
    hS hprod
  intro b hb
  exact convolutionError_norm_bound S w M (fun i p hp => (hS i p hp).1) hM hw b

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean values of the squarefree prime-convolution discrepancy

The ordinary Montgomery--Vaughan input is specialized to the actual
coefficients obtained from independent prime factors.  The full polynomial
factors exactly; removing repeated primes costs the energy already proved
in `RepeatedPrimeSupport`.  The maximum multiplicity of an integer norm is
kept explicit, so no divisor estimate is hidden in this deduction.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma theta_finset_prod {κ : Type*} (s : Finset κ) (f : κ → Eisenstein) (ℓ : ℤ) :
    theta ℓ (∏ i ∈ s, f i) = ∏ i ∈ s, theta ℓ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

lemma normTwist_finset_prod {κ : Type*} (s : Finset κ) (f : κ → Eisenstein)
    (u : ℝ) (hf : ∀ i ∈ s, f i ≠ 0) :
    normTwist u (∏ i ∈ s, f i) = ∏ i ∈ s, normTwist u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [normTwist, norm]
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, normTwist_mul u (hf i (Finset.mem_insert_self i s))
      (Finset.prod_ne_zero_iff.mpr hs), ih hs, Finset.prod_insert hi]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Collection by products preserves the independent prime factorization,
including the fixed angular character and the translated Mellin height. -/
theorem orderedConvolution_angular_polynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (ℓ : ℤ) (u t : ℝ) :
    angularCoefficientPolynomial (orderedConvolutionSupport S)
      (orderedConvolution S w) ℓ u t = fullPrimeProductPolynomial S w ℓ u t := by
  unfold angularCoefficientPolynomial fullPrimeProductPolynomial
  simp only [← normTwist_eq_mellinPhase]
  simp_rw [mul_assoc]
  rw [orderedConvolution_sum]
  calc
    _ = ∑ f ∈ Fintype.piFinset S,
        ∏ i, w i (f i) * (theta ℓ (f i) * normTwist (t + u) (f i)) := by
      apply Finset.sum_congr rfl
      intro f hf
      have hn : ∀ i ∈ (Finset.univ : Finset ι), f i ≠ 0 := by
        intro i hi
        exact (hS i (f i) ((Fintype.mem_piFinset.mp hf) i)).2.ne_zero
      rw [theta_finset_prod, normTwist_finset_prod _ _ _ hn,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ = _ := (Finset.prod_univ_sum S
      (fun i p => w i p * (theta ℓ p * normTwist (t + u) p))).symm

/-- The difference between the factored polynomial and its squarefree part
has exactly the repeated-prime discrepancy coefficients. -/
theorem fullPrimeProduct_sub_squarefree (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (ℓ : ℤ) (u t : ℝ) :
    fullPrimeProductPolynomial S w ℓ u t - squarefreePrimePolynomial S w ℓ u t =
      errorPrimePolynomial S w ℓ u t := by
  rw [← orderedConvolution_angular_polynomial S w hS]
  simp only [squarefreePrimePolynomial, errorPrimePolynomial,
    angularCoefficientPolynomial, squarefreeConvolutionError,
    sub_mul, Finset.sum_sub_distrib]

lemma normFiber_card_le (B : Finset Eisenstein) (Z n : ℕ)
    (hn : n ∈ Finset.Icc 1 Z) :
    ((B.filter (fun b => normNat b = n)).card : ℝ) ≤
      (normFiberMultiplicity B Z : ℝ) := by
  exact_mod_cast (Finset.le_sup (f := fun m => (B.filter (fun b => normNat b = m)).card) hn)

lemma normFiberMultiplicity_primeProducts_le (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (Z : ℕ) :
    normFiberMultiplicity (orderedConvolutionSupport S) Z ≤
      (2 * Fintype.card ι) ^ (Fintype.card ι) := by
  apply Finset.sup_le
  intro n _
  exact primeProduct_norm_fiber_card S hS n

lemma orderedConvolutionSupport_ne_zero (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) :
    ∀ b ∈ orderedConvolutionSupport S, b ≠ 0 := by
  intro b hb
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact (hS i (f i) ((Fintype.mem_piFinset.mp hf) i)).2.ne_zero

lemma orderedConvolutionSupport_normNat (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (Y : ℝ) (Z : ℕ)
    (hprod : ∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y)
    (hYZ : Y ≤ (Z : ℝ)) :
    ∀ b ∈ orderedConvolutionSupport S, normNat b ∈ Finset.Icc 1 Z := by
  intro b hb
  have hb₀ := orderedConvolutionSupport_ne_zero S hS b hb
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
  apply Finset.mem_Icc.mpr
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero hb₀)
  · exact_mod_cast (show (normNat (∏ i, f i) : ℝ) ≤ (Z : ℝ) by
      rw [normNat_cast]
      exact (hprod f hf).trans hYZ)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic multiplicities and moments of products of finitely many prime powers. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

/-- A fixed logarithmic power is bounded by every positive norm power,
with an explicit constant uniform down to norm one. -/
lemma natLog_power_bound (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((Nat.log 2 n + 1 : ℕ) : ℝ)^m ≤ C*(n:ℝ)^ε := by
  by_cases hm : m = 0
  · subst m
    refine ⟨1,zero_lt_one,?_⟩
    intro n hn
    simpa using Real.one_le_rpow (by exact_mod_cast hn) hε.le
  let δ : ℝ := ε/m
  have hm0 : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hδ : 0 < δ := div_pos hε hm0
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A : ℝ := 1/(δ*Real.log 2)+1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A^m,pow_pos hA _,?_⟩
  intro n hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := zero_lt_one.trans_le hn1
  have hlog : (Nat.log 2 n:ℝ) ≤ Real.log n/Real.log 2 := by
    change (Nat.log 2 n:ℝ) ≤ Real.logb (2:ℝ) (n:ℝ)
    rw [← Real.natFloor_logb_natCast 2 n]
    exact Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hn1)
  have hx : 1 ≤ (n:ℝ)^δ := Real.one_le_rpow hn1 hδ.le
  have hbase : ((Nat.log 2 n+1:ℕ):ℝ) ≤ A*(n:ℝ)^δ := by
    push_cast
    calc
      _ ≤ Real.log n/Real.log 2+1 := by linarith
      _ ≤ ((n:ℝ)^δ/δ)/Real.log 2+(n:ℝ)^δ :=
        add_le_add (div_le_div_of_nonneg_right (Real.log_le_rpow_div hn0.le hδ) hL.le) hx
      _ = _ := by dsimp [A]; ring
  have he : ((n:ℝ)^δ)^m = (n:ℝ)^ε := by
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    dsimp [δ]
    exact div_mul_cancel₀ ε (ne_of_gt hm0)
  calc
    _ ≤ (A*(n:ℝ)^δ)^m := pow_le_pow_left₀ (by positivity) hbase m
    _ = _ := by rw [mul_pow,he]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the original independently weighted prime tuples,
with the individual support and the global norm cutoff both retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinateSupport_primary (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    ∀ i, ∀ n ∈ coordinateSupport W X Y i, primary n := by
  intro i n hn
  exact (mem_primaryElementBall.mp (Finset.mem_filter.mp hn).1).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting the indicator convolution to genuine primary primes,
followed by the exact squarefree discrepancy. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_primary (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    ∀ i, ∀ p ∈ coordinatePrimeSupport W X Y i, primaryPrime p := by
  intro i p hp
  exact ⟨coordinateSupport_primary W X Y i p (Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeTwists
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplicative twists of the manuscript's squarefree prime coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_mul_character (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (χ : Eisenstein →* ℂ) (z : Eisenstein) :
    orderedConvolution S (fun i n => w i n*χ n) z = orderedConvolution S w z*χ z := by
  unfold orderedConvolution
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.prod_mul_distrib,← map_prod, (Finset.mem_filter.mp hn).2]

lemma squarefreeConvolution_mul_character (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (χ : Eisenstein →* ℂ) (z : Eisenstein) :
    squarefreeConvolution S (fun i n => w i n*χ n) z = squarefreeConvolution S w z*χ z := by
  by_cases hs : Squarefree z
  · simp only [squarefreeConvolution,ite_eq_left hs,orderedConvolution_mul_character]
  · simp only [squarefreeConvolution,ite_eq_right hs,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeMomentCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the structured moment with the original
squarefree ordered-prime coefficient, including numerator and exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma principal_residue_value (e z : Eisenstein) :
    (1 : MulChar (Residues e) ℂ) (Ideal.Quotient.mk (modulus e) z) =
      if IsCoprime z e then 1 else 0 := by
  by_cases hc : IsCoprime z e
  · rw [ite_eq_left hc,MulChar.one_apply (residue_isUnit_of_isCoprime hc.symm)]
  · rw [ite_eq_right hc]
    exact MulChar.map_nonunit _ (fun h => hc (isCoprime_of_residue_isUnit h).symm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredSupportBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The output norm range is derived from the independent coordinate
supports; no product-range hypothesis is imposed on the coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_norm_bounds (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) {R : ℝ}
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (Z : ℝ) (i : ι) (p : Eisenstein) (hp : p ∈ coordinatePrimeSupport W X Z i) :
    X i ≤ norm p ∧ norm p ≤ R*X i := by
  have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  constructor
  · have h : 1 ≤ norm p/X i := le_of_not_gt (fun h => hn (hlo i _ h))
    simpa only [one_mul] using (le_div_iff₀ (hX i)).mp h
  · have h : norm p/X i ≤ R := le_of_not_gt (fun h => hn (hhi i _ h))
    exact (div_le_iff₀ (hX i)).mp h

lemma coordinatePrimeProduct_norm_bounds (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) {R : ℝ} (_hR : 0 ≤ R)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (Z : ℝ) (z : Eisenstein) (hz : z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z)) :
    (∏ i, X i) ≤ norm z ∧ norm z ≤ R^(Fintype.card ι)*(∏ i, X i) := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
  have hb (i : ι) := coordinatePrimeSupport_norm_bounds W X hX hlo hhi Z i (n i)
    (Fintype.mem_piFinset.mp hn i)
  rw [norm_finset_prod]
  constructor
  · exact Finset.prod_le_prod (fun i _ => (hX i).le) (fun i _ => (hb i).1)
  · calc
      _ ≤ ∏ i, R*X i := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (hb i).2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp

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

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_eq_coordinate {R Z : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hhi : ∀ i x, R < x → W i x = 0)
    (hZ : ∀ i, R*X i ≤ 2*Z) : fullPrimeSupport R W X = coordinatePrimeSupport W X Z := by
  funext i
  ext p
  rw [fullPrimeSupport_mem_iff W X hX hhi]
  simp only [coordinatePrimeSupport,coordinateSupport,Finset.mem_filter,mem_primaryElementBall]
  constructor
  · rintro ⟨⟨hp,hq⟩,hw⟩
    have hn : norm p/X i ≤ R := le_of_not_gt (fun h => hw (hhi i _ h))
    exact ⟨⟨⟨hp,((div_le_iff₀ (hX i)).mp hn).trans (hZ i)⟩,hw⟩,hq⟩
  · rintro ⟨⟨⟨hp,_⟩,hw⟩,hq⟩
    exact ⟨⟨hp,hq⟩,hw⟩

lemma coordinate_le_product (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i) (i : ι) :
    X i ≤ ∏ j, X j := by
  rw [← Finset.mul_prod_erase _ X (Finset.mem_univ i)]
  exact le_mul_of_one_le_right (by linarith [hX i]) (Finset.one_le_prod (fun j _ => hX j))

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredCoefficientEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primeMomentCoefficient_norm_le (W : ι → ℝ → ℂ) (X M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (Z : ℝ) (z : Eisenstein) :
    ‖primeMomentCoefficient W X Z z‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  by_cases hz : Squarefree z
  · simpa only [primeMomentCoefficient,squarefreeConvolution,ite_eq_left hz] using
      orderedConvolution_norm_bound (coordinatePrimeSupport W X Z)
        (fun i n => W i (norm n/X i)) M (coordinatePrimeSupport_primary W X Z) hM
        (fun i p _ => hW i _) z
  · simpa only [primeMomentCoefficient,squarefreeConvolution,ite_eq_right hz,norm_zero] using
      mul_nonneg (Nat.cast_nonneg ((Fintype.card ι)^(Fintype.card ι)))
        (Finset.prod_nonneg (fun i _ => hM i))

lemma structuredCoefficient_energy_le (W : ι → ℝ → ℂ) (X M : ι → ℝ)
    (hX : ∀ i, 0 < X i) {R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (Z : ℝ) :
    (∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
      ‖primeMomentCoefficient W X Z z‖^2) ≤
      18*(R^(Fintype.card ι)*(∏ i, X i))*
        (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  let S := orderedConvolutionSupport (coordinatePrimeSupport W X Z)
  have hcard : (S.card:ℝ) ≤ 18*(R^(Fintype.card ι)*(∏ i, X i)) :=
    primary_support_card_le S (mul_nonneg (pow_nonneg hR _)
      (Finset.prod_nonneg (fun i _ => (hX i).le))) (fun z hz =>
      ⟨orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
        (fun i p hp => (coordinatePrimeSupport_primary W X Z i p hp).1) hz,
        (coordinatePrimeProduct_norm_bounds W X hX hR hlo hhi Z z hz).2⟩)
  calc
    _ ≤ ∑ _z ∈ S, (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 :=
      Finset.sum_le_sum (fun z _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
        (primeMomentCoefficient_norm_le W X M hM hW Z z) 2)
    _ = (S.card:ℝ)*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullStructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma fullPrimeSupport_eq_product_cutoff {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i)
    (hhi : ∀ i x, R < x → W i x = 0) :
    fullPrimeSupport R W X = coordinatePrimeSupport W X (R/2*(∏ i, X i)) := by
  apply fullPrimeSupport_eq_coordinate W X (fun i => zero_lt_one.trans_le (hX i)) hhi
  intro i
  have h := mul_le_mul_of_nonneg_left (coordinate_le_product X hX i) hR
  nlinarith

lemma fullStructuredAngularSum_eq (R : ℝ) (h v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    fullStructuredAngularSum R h v e ℓ u W X =
      ∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R W X),
        fullStructuredCoefficient R h v e W X z*theta ℓ z*mellinPhase u (norm z) := by
  unfold fullStructuredAngularSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  unfold fullStructuredCoefficient
  split_ifs <;> simp only [zero_mul]

lemma fullStructuredCoefficient_energy_le (R : ℝ) (h v e : Eisenstein)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    (∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R W X),
      ‖fullStructuredCoefficient R h v e W X z‖^2) ≤
    ∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R W X),
      ‖fullPrimeCoefficient R W X z‖^2 := by
  apply Finset.sum_le_sum
  intro z hz
  have hp := orderedPrimarySupport_primary (fullPrimeSupport R W X)
    (fun i p hp => (fullPrimeSupport_prime R W X i p hp).1) hz
  apply pow_le_pow_left₀ (_root_.norm_nonneg (fullStructuredCoefficient R h v e W X z)) _ 2
  unfold fullStructuredCoefficient
  split_ifs
  · rw [norm_mul]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hp _)
  · simpa only [norm_zero] using _root_.norm_nonneg (fullPrimeCoefficient R W X z)

theorem fullStructured_dyadicMeanSquare {C R : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (Z : ℕ) (hZ : R^(Fintype.card ι)*(∏ i, X i) ≤ (Z:ℝ))
    (h v e : Eisenstein) (ℓ : ℤ) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    ((∫ t in T..2*T, ‖fullStructuredAngularSum R h v e ℓ (t+u) W X‖^2) +
     (∫ t in -2*T..-T, ‖fullStructuredAngularSum R h v e ℓ (t+u) W X‖^2))/T ≤
      2*C*(1+(Z:ℝ)/T)*((2*Fintype.card ι)^(Fintype.card ι):ℕ)*
        ∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R W X),
          ‖fullPrimeCoefficient R W X z‖^2 := by
  let S := fullPrimeSupport R W X
  have hprime : ∀ i, ∀ z ∈ S i, primaryPrime z := fullPrimeSupport_prime R W X
  have hnorm : ∀ z ∈ orderedConvolutionSupport S,
      norm z ≤ R^(Fintype.card ι)*(∏ i, X i) := by
    rw [show S = coordinatePrimeSupport W X (R/2*(∏ i, X i)) from
      fullPrimeSupport_eq_product_cutoff hR W X hX hhi]
    exact fun z hz => (coordinatePrimeProduct_norm_bounds W X
      (fun i => zero_lt_one.trans_le (hX i)) hR hlo hhi _ z hz).2
  have hprod : ∀ f ∈ Fintype.piFinset S,
      norm (∏ i, f i) ≤ R^(Fintype.card ι)*(∏ i, X i) := by
    intro f hf
    exact hnorm _ (Finset.mem_image.mpr ⟨f,hf,rfl⟩)
  have hmult : ∀ n ∈ Finset.Icc 1 Z,
      (((orderedConvolutionSupport S).filter (fun b => normNat b = n)).card:ℝ) ≤
        ((2*Fintype.card ι)^(Fintype.card ι):ℕ) := by
    intro n hn
    exact (normFiber_card_le _ Z n hn).trans
      (by exact_mod_cast normFiberMultiplicity_primeProducts_le S hprime Z)
  simp_rw [fullStructuredAngularSum_eq]
  have hb := fixedAngular_translated_dyadicMeanSquare hMV hC
    (orderedConvolutionSupport S) (fullStructuredCoefficient R h v e W X) Z
    ((2*Fintype.card ι)^(Fintype.card ι):ℕ)
    (orderedConvolutionSupport_normNat S hprime _ Z hprod hZ)
    (orderedConvolutionSupport_ne_zero S hprime) hmult ℓ u hT
  apply hb.trans
  exact mul_le_mul_of_nonneg_left (fullStructuredCoefficient_energy_le R h v e W X)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC)
      (by positivity)) (Nat.cast_nonneg _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularFullPrimeConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

lemma fullStructuredAngularPrimeSum_eq_existing (R : ℝ) (h v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    fullStructuredAngularPrimeSum ℓ R h 1 v e u W X =
      fullStructuredAngularSum R h v e ℓ u W X := by
  unfold fullStructuredAngularPrimeSum fullStructuredAngularSum
  apply Finset.sum_congr rfl
  intro z _
  simp only [one_pow,mul_one]
  ring

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

lemma gramMellinPhase_eq_mellinPhase (t x : ℝ) :
    gramMellinPhase t x = mellinPhase (2*Real.pi*t) x := by
  rw [gramMellinPhase,Real.fourierChar_apply]
  unfold mellinPhase
  congr 1
  push_cast
  ring

lemma mellinPhase_add_height (u v x : ℝ) :
    mellinPhase (u+v) x = mellinPhase u x*mellinPhase v x := by
  unfold mellinPhase
  rw [show (((u+v)*Real.log x:ℝ):ℂ)*Complex.I =
    ((u*Real.log x:ℝ):ℂ)*Complex.I+((v*Real.log x:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add]

lemma gramMellinPhase_ratio (t : ℝ) {x N : ℝ} (hx : 0 < x) (hN : 0 < N) :
    gramMellinPhase t (x/N) =
      mellinPhase (2*Real.pi*t) x*mellinPhase (-(2*Real.pi*t)) N := by
  rw [gramMellinPhase_eq_mellinPhase]
  unfold mellinPhase
  rw [Real.log_div hx.ne' hN.ne']
  rw [show (((2*Real.pi*t)*(Real.log x-Real.log N):ℝ):ℂ)*Complex.I =
    (((2*Real.pi*t)*Real.log x:ℝ):ℂ)*Complex.I+
      ((-(2*Real.pi*t)*Real.log N:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add]

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

lemma fullPrimeCoefficient_sum_squarefree (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (f : Eisenstein → ℂ) :
    (∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter
      (fun b => IsCoprime b e), fullPrimeCoefficient R W X b*f b) =
    ∑ b ∈ fullSquarefreePrimeSupport R W X e, fullPrimeCoefficient R W X b*f b := by
  simp only [fullSquarefreePrimeSupport,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hsf : Squarefree b
  · simp only [hsf,true_and]
  · simp [hsf,fullPrimeCoefficient,squarefreeConvolution]

lemma gramMellinPhase_neg (t x : ℝ) :
    gramMellinPhase (-t) x = star (gramMellinPhase t x) := by
  rw [gramMellinPhase_eq_mellinPhase,gramMellinPhase_eq_mellinPhase,star_mellinPhase]
  congr 1
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeMellinIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integral estimate for the literal radial Poisson form in terms of
the actual divisor-restricted character moments. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coprimeMellinMass_nonneg (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (t : ℝ) : 0 ≤ coprimeMellinMass S H U v w y t := by
  apply Finset.sum_nonneg
  intro s hs
  exact div_nonneg (add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by norm_num)

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

lemma LogarithmicWeightFamily.radial_deriv_bound {γ : Type*}
    {L : γ → ℝ} {W : γ → ℝ → ℂ} (h : LogarithmicWeightFamily L W) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ i x, 0 < x →
      ‖deriv (W i) x‖*x ≤ C*(1+Real.log (L i))^A := by
  obtain ⟨C,A,hC,hbound⟩ := h.derivative_bound 1
  refine ⟨C,A,hC,?_⟩
  intro i x hx
  let v := -Real.log x
  have hexp : Real.exp (-v) = x := by simp [v,Real.exp_log hx]
  have hdW : HasDerivAt (W i) (deriv (W i) x) x :=
    ((h.smooth i).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hdE : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-x) v := by
    have hh := ((hasDerivAt_id v).neg.exp)
    change HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-v)*(-1)) v at hh
    simpa only [hexp,mul_neg,mul_one] using
      hh
  have hd := (show HasDerivAt (W i) (deriv (W i) x) (Real.exp (-v)) by
    rwa [hexp]).scomp v hdE
  have heq : ‖deriv (fun t : ℝ => W i (Real.exp (-t))) v‖ = ‖deriv (W i) x‖*x := by
    change ‖deriv (W i ∘ fun t : ℝ => Real.exp (-t)) v‖ = _
    rw [hd.deriv,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hx,mul_comm]
  have hb := hbound i v
  rw [norm_iteratedFDeriv_one,← norm_deriv_eq_norm_fderiv,heq] at hb
  exact hb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogCoefficientEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit logarithmic, rather than subpower, energy of the actual
full prime convolution. This is used in the small-conductor sieve range. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem logarithmic_full_coefficient_energy {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ (r : γ) (X : ι → ℝ),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      (∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R (W r) X),
        ‖fullPrimeCoefficient R (W r) X z‖^2) ≤
        C*L r*(1+Real.log (L r))^A := by
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  let n := Fintype.card ι
  let C := 18*R^n*((n^n:ℕ)*M^n)^2
  refine ⟨C,2*m*n,?_,?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans hR) _)) (sq_nonneg _)
  intro r X hL hX hprod
  let Z := R/2*L r
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have heq : fullPrimeSupport R (W r) X = coordinatePrimeSupport (W r) X Z := by
    simpa only [Z,hprod] using fullPrimeSupport_eq_product_cutoff (zero_le_one.trans hR)
      (W r) X hX (hhi r)
  have hb := structuredCoefficient_energy_le (W r) X
    (fun _ => M*(1+Real.log (L r))^m) (fun i => zero_lt_one.trans_le (hX i))
    (zero_le_one.trans hR) (hlo r) (hhi r)
    (fun _ => mul_nonneg hM (pow_nonneg hz _)) (fun i x => hMb (r,i) x) Z
  have hcoeff : fullPrimeCoefficient R (W r) X = fun z => primeMomentCoefficient (W r) X Z z := by
    funext z
    unfold fullPrimeCoefficient primeMomentCoefficient
    rw [heq]
  rw [heq,hcoeff]
  apply hb.trans_eq
  rw [hprod,Finset.prod_const,Finset.card_univ,mul_pow,← pow_mul]
  dsimp only [C,n]
  rw [mul_pow,mul_pow,← pow_mul]
  have hm : m*(Fintype.card ι*2) = 2*m*Fintype.card ι := by ring
  rw [hm,pow_mul M (Fintype.card ι) 2]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Fourier decay for the fixed wider log-norm cutoff used by the
actual prime convolution. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma wideGramExp_deriv_bound (M : ℝ) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (i : ℕ), i ≤ n → ∀ u : ℝ, |u| ≤ 2*M →
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D := by
  have hb (i : ℕ) : ∃ D : ℝ, ∀ u ∈ Set.Icc (-2*M) (2*M),
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D :=
    isCompact_Icc.exists_bound_of_continuousOn
      (gramExp_contDiff.continuous_iteratedFDeriv (mod_cast le_top)).continuousOn
  choose B hB using hb
  let D := 1 + ∑ i ∈ Finset.range (n+1), |B i|
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n+1), |B i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨D, by dsimp [D]; linarith, ?_⟩
  intro i hi u hu
  have hbi : |B i| ≤ ∑ j ∈ Finset.range (n+1), |B j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_range.mpr (by omega))
  exact (hB i u ⟨by linarith [(abs_le.mp hu).1], (abs_le.mp hu).2⟩).trans
    ((le_abs_self (B i)).trans (hbi.trans (by dsimp [D]; linarith)))

lemma wideGramExp_scale_growth {M c u : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hu : |u| ≤ 2*M) :
    1+c ≤ Real.exp M * (1+‖c • gramExp u‖) := by
  have hE : 1 ≤ Real.exp M := Real.one_le_exp hM
  have hEu : 1 ≤ Real.exp M * Real.exp (u/2) := by
    rw [← Real.exp_add]
    simpa using Real.exp_le_exp.mpr (show (0:ℝ) ≤ M + u/2 by
      linarith [(abs_le.mp hu).1])
  have hEc := mul_le_mul_of_nonneg_left hEu hc
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, gramExp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  nlinarith

theorem schwartz_wideGramExp_comp_uniform (M : ℝ) (hM : 0 ≤ M) (F : 𝓢(ℂ, ℂ)) (n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c → ∀ u : ℝ, |u| ≤ 2*M →
      (1+c)^K * ‖iteratedFDeriv ℝ n (fun v => F (c • gramExp v)) u‖ ≤ C := by
  obtain ⟨D, hD, hderiv⟩ := wideGramExp_deriv_bound M n
  let L := n+K
  let S := (Finset.Iic (L,n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  let H := (Real.exp M)^L * 2^L * S
  have hS : 0 ≤ S := by positivity
  have hH : 0 ≤ H := by positivity
  refine ⟨(n.factorial : ℝ)*H*D^n, by positivity, ?_⟩
  intro c hc u hu
  have hc1 : 0 < 1+c := by positivity
  have hC (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ ≤ H / (1+c)^L := by
    rw [le_div_iff₀' (pow_pos hc1 L)]
    have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (L,n)) (k := L) (n := i) (le_refl L) hi F (c • gramExp u)
    calc
      _ ≤ (Real.exp M * (1+‖c • gramExp u‖))^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ := by
        gcongr
        exact wideGramExp_scale_growth hM hc hu
      _ = (Real.exp M)^L * ((1+‖c • gramExp u‖)^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖) := by rw [mul_pow]; ring
      _ ≤ (Real.exp M)^L * (2^L*S) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = H := by dsimp [H]; ring
  have hDb (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun v => c • gramExp v) u‖ ≤ ((1+c)*D)^i := by
    rw [iteratedFDeriv_const_smul_apply' (gramExp_contDiff.of_le (mod_cast le_top)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      _ ≤ c*D := mul_le_mul_of_nonneg_left (hderiv i hin u hu) hc
      _ ≤ (1+c)*D := by nlinarith
      _ ≤ ((1+c)*D)^i := le_self_pow₀ (by nlinarith) (by omega)
  have hb := norm_iteratedFDeriv_comp_le (F.smooth ⊤) (gramExp_contDiff.const_smul c)
    (n := n) (mod_cast le_top) u hC hDb
  calc
    _ ≤ (1+c)^K * ((n.factorial : ℝ)*(H/(1+c)^L)*((1+c)*D)^n) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (n.factorial : ℝ)*H*D^n := by
      dsimp [L]
      rw [pow_add, mul_pow]
      field_simp


lemma wideAnnularLogSchwartz_deriv_zero (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (c u : ℝ) (n : ℕ)
    (hu : ¬ |u| ≤ 2*M) : iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u = 0 := by
  by_contra hn
  have hs := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := wideAnnularLogSchwartz M hM F c) n hn
  have hb := tsupport_smul_subset_left ((wideGramLogBump M hM) : ℝ → ℝ)
    (fun v => F (c • gramExp v)) hs
  rw [(wideGramLogBump M hM).tsupport_eq] at hb
  exact hu (by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, wideGramLogBump] using hb)

theorem wideAnnularLogSchwartz_seminorm_uniform (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * SchwartzMap.seminorm ℝ k n (wideAnnularLogSchwartz M hM F c) ≤ C := by
  choose C hC hbound using fun i => schwartz_wideGramExp_comp_uniform M hM.le F i K
  let B : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) * C (n-i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => mul_nonneg (by positivity) (hC (n-i)))
  refine ⟨(2*M)^k * B, by positivity, ?_⟩
  intro c hc
  have hp : 0 < (1+c)^K := pow_pos (by positivity) _
  rw [← le_div_iff₀' hp]
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ 2*M
  · rw [le_div_iff₀' hp]
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (wideGramLogBump M hM).contDiff
      ((F.smooth ⊤).comp (gramExp_contDiff.const_smul c)) u (n := n) (mod_cast le_top)
    have hd' : (1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖ ≤ B := by
      calc
        _ ≤ (1+c)^K * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ *
              ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖ :=
          mul_le_mul_of_nonneg_left hd hp.le
        _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ *
              ((1+c)^K * ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ B := by
          apply Finset.sum_le_sum
          intro i hi
          have hb : ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ ≤
              SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) := by
            have hb := SchwartzMap.le_seminorm ℝ 0 i (wideGramBumpSchwartz M hM) u
            rw [show (wideGramBumpSchwartz M hM : ℝ → ℝ) = ((wideGramLogBump M hM) : ℝ → ℝ) from rfl] at hb
            simpa only [pow_zero, one_mul] using hb
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity))
            (hbound (n-i) c hc u hu) (by positivity) (by positivity)
    calc
      _ = ‖u‖^k * ((1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖) := by ring
      _ ≤ (2*M)^k * B := mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _)
        (by simpa only [Real.norm_eq_abs] using hu) k) hd' (by positivity) (by positivity)
  · rw [wideAnnularLogSchwartz_deriv_zero M hM F c u n hu, norm_zero, mul_zero]
    positivity

lemma wideAnnularLogSchwartz_eq_wideGramLogSchwartz (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    wideAnnularLogSchwartz M hM (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ) =
      wideGramLogSchwartz M hM W hW hW' ρ := by
  ext u
  simp only [wideAnnularLogSchwartz_apply M hM, wideGramLogSchwartz_apply, wideGramLogKernel,
    normProfileFourierSchwartz_apply]
  congr 2
  simp only [gramExp, Complex.real_smul, Complex.ofReal_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormDenominatorMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm denominator in the actual Poisson formula stays in its
Mellin kernel. No real power is inserted into the prime coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma normDenominatorMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    Integrable (normDenominatorMellinCoefficient M hM W hW hW' ρ) :=
  (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integrable

lemma normDenominatorLogSchwartz_apply (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ u : ℝ) :
    normDenominatorLogSchwartz M hM W hW hW' ρ u =
      (Real.exp (u/2):ℂ)*wideGramLogKernel M hM W ρ u := by
  rw [normDenominatorLogSchwartz,SchwartzMap.smulLeftCLM_apply_apply
    (normDenominatorMultiplier M hM).hasTemperateGrowth,wideGramLogSchwartz_apply]
  change ((wideGramLogBump (2*M) (by positivity) u:ℝ) • (Real.exp (u/2):ℂ)) •
    wideGramLogKernel M hM W ρ u = _
  by_cases hu : |u| ≤ 2*M
  · have he : wideGramLogBump (2*M) (by positivity) u = 1 :=
      (wideGramLogBump (2*M) (by positivity)).one_of_mem_closedBall
        (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,wideGramLogBump] using hu)
    rw [he,one_smul,smul_eq_mul]
  · have he : wideGramLogBump M hM u = 0 :=
      (wideGramLogBump M hM).zero_of_le_dist
        (by simpa only [Real.dist_eq,sub_zero,wideGramLogBump] using le_of_not_ge hu)
    simp only [wideGramLogKernel,he,zero_smul,smul_zero,mul_zero]


lemma normDenominatorLogSchwartz_eq_annular (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    normDenominatorLogSchwartz M hM W hW hW' ρ =
      SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
        (wideAnnularLogSchwartz M hM (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ)) := by
  rw [wideAnnularLogSchwartz_eq_wideGramLogSchwartz]
  rfl

lemma normDenominatorFourier_seminorm_uniform (M : ℝ) (hM : 0 < M)
    (F : 𝓢(ℂ,ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c → (1+c)^K * SchwartzMap.seminorm ℝ k n
      (𝓕 (SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
        (wideAnnularLogSchwartz M hM F c))) ≤ C := by
  let f : ℝ → 𝓢(ℝ,ℂ) := fun c => (1+c)^K • wideAnnularLogSchwartz M hM F c
  have hb : Bornology.IsVonNBounded ℝ (f '' Ici 0) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C,hC,hc⟩ := wideAnnularLogSchwartz_seminorm_uniform M hM F i.1 i.2 K
    refine ⟨C+1,by linarith,?_⟩
    intro c hc0
    have hc0' : 0 ≤ c := hc0
    change SchwartzMap.seminorm ℝ i.1 i.2 ((1+c)^K • wideAnnularLogSchwartz M hM F c) < _
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (pow_pos (by linarith [hc0']) _)]
    exact (hc c hc0).trans_lt (by linarith)
  let A : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.fourierTransformCLM ℝ (V := ℝ) (E := ℂ)).comp
      ((SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)).restrictScalars ℝ)
  have hA := hb.image A
  obtain ⟨C,hC,hc⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hA (k,n)
  refine ⟨C,hC,?_⟩
  intro c hc0
  have h := hc (A (f c)) ⟨f c,⟨c,hc0,rfl⟩,rfl⟩
  change SchwartzMap.seminorm ℝ k n (A ((1+c)^K • wideAnnularLogSchwartz M hM F c)) < C at h
  rw [map_smul,map_smul_eq_mul,Real.norm_eq_abs,
    abs_of_pos (pow_pos (by linarith) _)] at h
  exact h.le

theorem normDenominatorMellinCoefficient_pointwise_rapidDecay (M : ℝ) (hM : 0 < M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ t : ℝ,
      (1+ρ)^A * ‖t‖^B * ‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖ ≤ C := by
  obtain ⟨C,hC,hc⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') B 0 (2*A)
  refine ⟨C,hC,?_⟩
  intro ρ hρ t
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_nonneg ρ]
  have hb := SchwartzMap.le_seminorm ℝ B 0
    (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)) t
  simp only [norm_iteratedFDeriv_zero] at hb
  have h := hc (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [← normDenominatorLogSchwartz_eq_annular] at h
  calc
    _ = (1+ρ)^A * (‖t‖^B * ‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) := by ring
    _ ≤ (1+Real.sqrt ρ)^(2*A) * SchwartzMap.seminorm ℝ B 0
        (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)) :=
      mul_le_mul hs hb (by positivity) (by positivity)
    _ ≤ C := h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormMellinMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem normDenominatorMellinCoefficient_moment_decay (M : ℝ) (hM : 0 < M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^A * (∫ t : ℝ, ‖t‖^B*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) ≤ C := by
  let k := (volume : Measure ℝ).integrablePower
  let D : ℝ := 2^k * ∫ t : ℝ, (1+‖t‖)^(-(k:ℝ))
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg (fun t => by positivity))
  obtain ⟨C₀,hC₀,hc₀⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') 0 0 (2*A)
  obtain ⟨C₁,hC₁,hc₁⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') (B+k) 0 (2*A)
  refine ⟨D*(C₀+C₁)+1,by positivity,?_⟩
  intro ρ hρ
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_nonneg ρ]
  have h := (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integral_pow_mul_iteratedFDeriv_le ℝ volume B 0
  simp only [norm_iteratedFDeriv_zero] at h
  have h₀ := hc₀ (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  have h₁ := hc₁ (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [← normDenominatorLogSchwartz_eq_annular] at h₀ h₁
  have hb : (1+ρ)^A * (∫ t : ℝ, ‖t‖^B*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) ≤ D*(C₀+C₁) := by
    calc
      _ ≤ (1+Real.sqrt ρ)^(2*A) * (D *
          (SchwartzMap.seminorm ℝ 0 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
           SchwartzMap.seminorm ℝ (B+k) 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)))) :=
        mul_le_mul hs h (integral_nonneg (fun t => by positivity)) (by positivity)
      _ = D*((1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ 0 0
          (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
        (1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ (B+k) 0
          (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h₀ h₁) hD
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDivisorSubsets
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A product of n primary primes has at most 2^n subsets of prescribed
primary primes dividing it, independently of the ambient prime set. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primeProduct_divisor_subsets_card (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport S) :
    (U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ b)).card ≤ 2^(Fintype.card ι) := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  have hprime (i : ι) : primaryPrime (f i) := hS i (f i) (Fintype.mem_piFinset.mp hf i)
  have hsub : U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ ∏ i, f i) ⊆
      (Finset.univ.image f).powerset := by
    intro s hs
    obtain ⟨hsU,hsd⟩ := Finset.mem_filter.mp hs
    apply Finset.mem_powerset.mpr
    intro p hp
    have hpU := hU p (Finset.mem_powerset.mp hsU hp)
    have hpd : p ∣ ∏ i, f i := (Finset.dvd_prod_of_mem (fun q : Eisenstein => q) hp).trans hsd
    obtain ⟨i,_,hi⟩ := (hpU.2.dvd_finsetProd_iff f).mp hpd
    have he : p = f i := primary_associated_eq hpU.1 (hprime i).1
      ((hpU.2.dvd_prime_iff_associated (hprime i).2).mp hi)
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩
  calc
    _ ≤ ((Finset.univ.image f).powerset).card := Finset.card_le_card hsub
    _ = 2^(Finset.univ.image f).card := Finset.card_powerset _
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      simpa using Finset.card_image_le (s := (Finset.univ:Finset ι)) (f := f))

theorem fullPrime_divisor_subsets_card (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (U : Finset Eisenstein) (hU : ∀ p ∈ U, primaryPrime p)
    {b : Eisenstein} (hb : b ∈ fullSquarefreePrimeSupport R W X e) :
    (U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ b)).card ≤ 2^(Fintype.card ι) :=
  primeProduct_divisor_subsets_card (fullPrimeSupport R W X)
    (fullPrimeSupport_prime R W X) U hU (Finset.mem_filter.mp hb).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeSlice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma fullPrimeSliceSupport_bounds (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (f e : Eisenstein) {n : Eisenstein} (hn : n ∈ fullPrimeSliceSupport R W X f e) :
    primary n ∧ Squarefree n ∧ IsCoprime f n ∧
      norm n ≤ R^Fintype.card ι*(∏ i, X i)/norm f := by
  have hm := Finset.mem_filter.mp hn
  have hp := mem_primaryElementBall.mp hm.1
  have hs := (fullSquarefreePrimeSupport_primary R W X e hm.2).2
  exact ⟨hp.1,hs.squarefree_of_dvd (dvd_mul_left _ _),
    (IsRelPrime.of_squarefree_mul hs).isCoprime,hp.2⟩

lemma fullPrimeSliceSupport_complete {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0)
    {f : Eisenstein} (hf : primary f) (e n : Eisenstein)
    (hn : f*n ∈ fullSquarefreePrimeSupport R W X e) :
    n ∈ fullPrimeSliceSupport R W X f e := by
  have hp := fullSquarefreePrimeSupport_primary R W X e hn
  have hb := (fullPrimeProduct_norm_bounds R W X hX hlo hhi (Finset.mem_filter.mp hn).1).2
  apply Finset.mem_filter.mpr
  refine ⟨mem_primaryElementBall.mpr ⟨primary_of_mul hf hp.1,?_⟩,hn⟩
  apply (le_div_iff₀ (norm_pos_of_ne_zero (primary_ne_zero hf))).mpr
  simpa only [norm_mul_eq,mul_comm] using hb

lemma fullPrime_divisor_sum_eq_slice {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0)
    {f : Eisenstein} (hf : primary f) (e : Eisenstein) (A : Eisenstein → ℂ) :
    (∑ b ∈ (fullSquarefreePrimeSupport R W X e).filter (fun b => f ∣ b), A b) =
      ∑ n ∈ fullPrimeSliceSupport R W X f e, A (f*n) := by
  symm
  apply Finset.sum_bij (fun n _ => f*n)
  · intro n hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).2,dvd_mul_right _ _⟩
  · intro n _ m _ hnm
    exact mul_left_cancel₀ (primary_ne_zero hf) hnm
  · intro b hb
    obtain ⟨n,hn⟩ := (Finset.mem_filter.mp hb).2
    refine ⟨n,?_,hn.symm⟩
    apply fullPrimeSliceSupport_complete W X hX hlo hhi hf
    simpa only [← hn] using (Finset.mem_filter.mp hb).1
  · intro n _
    rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeightCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal angular prime coefficients and the two signed Mellin rows.
Only unit phases are removed; the angular index remains fixed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

lemma angularHeightPrimeCoefficient_sum_squarefree (R : ℝ) (W : ι → ℝ → ℂ)
    (X : ι → ℝ) (e : Eisenstein) (f : Eisenstein → ℂ) :
    (∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter
      (fun b => IsCoprime b e), angularHeightPrimeCoefficient ℓ R W X b*f b) =
    ∑ b ∈ fullSquarefreePrimeSupport R W X e, angularHeightPrimeCoefficient ℓ R W X b*f b := by
  simpa only [angularHeightPrimeCoefficient,mul_assoc] using
    fullPrimeCoefficient_sum_squarefree R W X e (fun b => theta ℓ b*f b)

lemma angular_fullStructured_gram_twist
    (R : ℝ) (h e : Eisenstein) (u t : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {N : ℝ} (hN : 0 < N) :
    (∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter (fun b => IsCoprime b e),
      angularHeightPrimeCoefficient ℓ R W X b*mellinPhase u (norm b)*cubicSymbol b h*
        gramMellinPhase t (norm b/N)) =
      mellinPhase (-(2*Real.pi*t)) N*fullStructuredAngularSum R h 1 e ℓ (u+2*Real.pi*t) W X := by
  unfold fullStructuredAngularSum angularHeightPrimeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hbp := orderedPrimarySupport_primary (fullPrimeSupport R W X)
    (fun i p hp => (fullPrimeSupport_prime R W X i p hp).1) (Finset.mem_filter.mp hb).1
  rw [gramMellinPhase_ratio t (norm_pos_of_ne_zero (primary_ne_zero hbp)) hN,
    mellinPhase_add_height]
  simp only [one_mul]
  ring

theorem angular_fullStructuredPrimeRow_norm (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (h e : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ b ∈ fullSquarefreePrimeSupport R W X e,
      star (angularHeightPrimeCoefficient ℓ R W X b*mellinPhase u (norm b))*
        star (gramMellinPhase t (norm b/N))*star (cubicSymbol b h)‖ =
      ‖fullStructuredAngularSum R h 1 e ℓ (u+2*Real.pi*t) W X‖ := by
  have he : (∑ b ∈ fullSquarefreePrimeSupport R W X e,
      star (angularHeightPrimeCoefficient ℓ R W X b*mellinPhase u (norm b))*
        star (gramMellinPhase t (norm b/N))*star (cubicSymbol b h)) =
      star (mellinPhase (-(2*Real.pi*t)) N*
        fullStructuredAngularSum R h 1 e ℓ (u+2*Real.pi*t) W X) := by
    calc
      _ = star (∑ b ∈ fullSquarefreePrimeSupport R W X e,
          angularHeightPrimeCoefficient ℓ R W X b*
            (mellinPhase u (norm b)*cubicSymbol b h*gramMellinPhase t (norm b/N))) := by
        rw [star_sum]
        apply Finset.sum_congr rfl
        intro b hb
        simp only [star_mul]
        ring
      _ = star (∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter
          (fun b => IsCoprime b e), angularHeightPrimeCoefficient ℓ R W X b*
            (mellinPhase u (norm b)*cubicSymbol b h*gramMellinPhase t (norm b/N))) :=
        congrArg star (angularHeightPrimeCoefficient_sum_squarefree ℓ R W X e _).symm
      _ = _ := by
        congr 1
        convert angular_fullStructured_gram_twist ℓ R h e u t W X hN using 1
        all_goals try with_reducible_and_instances rfl
        apply Finset.sum_congr rfl
        intro b hb
        ring
  rw [he,norm_star,norm_mul,mellinPhase_norm,one_mul]

theorem angular_fullStructuredPrimeRow_reverse_norm (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (h e : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ b ∈ fullSquarefreePrimeSupport R W X e,
      star (angularHeightPrimeCoefficient ℓ R W X b*mellinPhase u (norm b))*
        gramMellinPhase t (norm b/N)*star (cubicSymbol b h)‖ =
      ‖fullStructuredAngularSum R h 1 e ℓ (u-2*Real.pi*t) W X‖ := by
  have he := angular_fullStructuredPrimeRow_norm ℓ R W X h e u (-t) hN
  simp only [gramMellinPhase_neg,star_star] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring


lemma angular_fullPrimeSliceRow_norm_le {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {f : Eisenstein} (hf : primary f)
    (e h : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a))*
        star (gramMellinPhase t (norm a/N))*star (cubicSymbol a h)‖ ≤
    ‖fullPrimeSliceSum R W X f e h 1 ℓ (u+2*Real.pi*t)‖ := by
  rw [fullPrime_divisor_sum_eq_slice W X hX hlo hhi hf]
  have hfp := norm_pos_of_ne_zero (primary_ne_zero hf)
  have he : (∑ n ∈ fullPrimeSliceSupport R W X f e,
      star (angularHeightPrimeCoefficient ℓ R W X (f*n)*mellinPhase u (norm (f*n)))*
        star (gramMellinPhase t (norm (f*n)/N))*star (cubicSymbol (f*n) h)) =
      star ((theta ℓ f*mellinPhase (u+2*Real.pi*t) (norm f)*
        mellinPhase (-(2*Real.pi*t)) N*cubicSymbol f h)*
        fullPrimeSliceSum R W X f e h 1 ℓ (u+2*Real.pi*t)) := by
    rw [fullPrimeSliceSum,Finset.mul_sum,star_sum]
    simp only [angularHeightPrimeCoefficient]
    apply Finset.sum_congr rfl
    intro n hn
    have hnp := (fullPrimeSliceSupport_bounds R W X f e hn).1
    have hnpos := norm_pos_of_ne_zero (primary_ne_zero hnp)
    rw [theta_mul, norm_mul_eq,gramMellinPhase_ratio t (mul_pos hfp hnpos) hN,
      mellinPhase_mul_pos u hfp hnpos,mellinPhase_mul_pos (2*Real.pi*t) hfp hnpos,
      cubicSymbol_mul_lower (primary_ne_zero hf) (primary_ne_zero hnp)]
    simp only [one_mul,mellinPhase_add_height,star_mul]
    ring
  rw [he,norm_star,norm_mul,norm_mul,norm_mul,norm_mul,norm_theta (primary_ne_zero hf),mellinPhase_norm,
    mellinPhase_norm,one_mul,one_mul]
  simp only [one_mul]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hf h)

lemma angular_fullPrimeSliceRow_reverse_norm_le {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {f : Eisenstein} (hf : primary f)
    (e h : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a))*
        gramMellinPhase t (norm a/N)*star (cubicSymbol a h)‖ ≤
    ‖fullPrimeSliceSum R W X f e h 1 ℓ (u-2*Real.pi*t)‖ := by
  have he := angular_fullPrimeSliceRow_norm_le ℓ W X hX hlo hhi hf e h u (-t) hN
  simp only [gramMellinPhase_neg,star_star] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeWeightVariation
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete total-variation control for rescaled prime weights and their
Mellin twists. This is the cost in the proved Abel summation inequality. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma rescaled_mellin_deriv_bound {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    {Y x M D : ℝ} (hY : 0 < Y) (hx : Y ≤ x) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hwm : ‖w (x/Y)‖ ≤ M) (hwd : ‖deriv w (x/Y)‖*(x/Y) ≤ D) (u : ℝ) :
    ‖deriv (fun t => w (t/Y)*mellinPhase u t) x‖ ≤ (D+M*|u|)/Y := by
  have hxp : 0 < x := hY.trans_le hx
  have hdw := ((hw.differentiable (by norm_num)).differentiableAt.hasDerivAt).scomp x
    ((hasDerivAt_id x).div_const Y)
  have hb := norm_deriv_weighted_mellinPhase hdw u hxp
  have hd : ‖(1/Y) • deriv w (x/Y)‖ ≤ D/x := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos zero_lt_one hY)]
    apply (le_div_iff₀ hxp).mpr
    calc
      _ = ‖deriv w (x/Y)‖*(x/Y) := by ring
      _ ≤ _ := hwd
  calc
    _ ≤ D/x+M*(|u|/x) := hb.trans
      (add_le_add hd (mul_le_mul_of_nonneg_right hwm (div_nonneg (abs_nonneg _) hxp.le)))
    _ = (D+M*|u|)/x := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (add_nonneg hD (mul_nonneg hM (abs_nonneg _))) hY hx

lemma contDiffOn_rescaled_mellin {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) (Y u : ℝ) :
    ContDiffOn ℝ ∞ (fun t => w (t/Y)*mellinPhase u t) (Ioi 0) := by
  intro x hx
  have hl : ContDiffAt ℝ ∞ (fun t : ℝ => u*Real.log t) x :=
    contDiffAt_const.mul (Real.contDiffAt_log.mpr (ne_of_gt hx))
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => ((u*Real.log t:ℝ):ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hl
  have hw' : ContDiff ℝ ∞ (fun t : ℝ => w (t/Y)) := hw.comp (contDiff_id.div_const Y)
  exact (hw'.contDiffAt.mul (hc.mul contDiffAt_const).cexp).contDiffWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaledPrimeInput
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rescaled, Mellin-twisted prime estimate derived from the precise
published unweighted Siegel–Walfisz input. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma continuous_zero_on_lower_closed {w : ℝ → ℂ} (hw : Continuous w)
    (hlo : ∀ x, x < 1 → w x = 0) {x : ℝ} (hx : x ≤ 1) : w x = 0 := by
  have hc : closure (Iio (1:ℝ)) ⊆ {x | w x = 0} :=
    closure_minimal (fun x hx => hlo x hx) (isClosed_eq hw continuous_const)
  apply hc
  simpa only [closure_Iio,mem_Iic] using hx

lemma smoothPrimeCharacterSum_eq_interval {R Y : ℝ} (hY : 0 < Y)
    {w : ℝ → ℂ} (hw : Continuous w) (hlo : ∀ x, x < 1 → w x = 0)
    (χ : Eisenstein → ℂ) (u : ℝ) :
    smoothPrimeCharacterSum R Y w χ u =
      ∑ p ∈ (primeCutoff (R*Y)).filter (fun p => Y < norm p),
        (w (norm p/Y)*mellinPhase u (norm p))*χ p := by
  unfold smoothPrimeCharacterSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : Y < norm p
  · simp only [ite_eq_left hp]
  · have hz : w (norm p/Y) = 0 := continuous_zero_on_lower_closed hw hlo
      ((div_le_one hY).mpr (le_of_not_gt hp))
    simp only [ite_eq_right hp,hz,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogSavingPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary logarithmic exponent bookkeeping for the rescaled
prime estimate. -/
noncomputable section
namespace CubicFirstMoment

lemma log_length_comparison {L Y c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (hlog : 1 ≤ Real.log L) (hY : L^c ≤ Y) :
    0 < Real.log Y ∧ 1+Real.log L ≤ (2/c)*Real.log Y := by
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hL c) hY
  rw [Real.log_rpow hL] at hl
  have hpos : 0 < Real.log Y := (mul_pos hc (by linarith)).trans_le hl
  refine ⟨hpos,?_⟩
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  nlinarith

lemma log_variation_power {z R M B u : ℝ} (hz : 1 ≤ z) (hR : 1 ≤ R)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (m b U : ℕ) (hu : |u| ≤ z^U) :
    2*M*z^m+(R-1)*(B*z^b+M*z^m*|u|) ≤
      (2*M+(R-1)*(B+M))*z^(m+b+U) := by
  have hm : z^m ≤ z^(m+b+U) := pow_le_pow_right₀ hz (by omega)
  have hb : z^b ≤ z^(m+b+U) := pow_le_pow_right₀ hz (by omega)
  have hmu : z^m*|u| ≤ z^(m+b+U) := by
    calc
      _ ≤ z^m*z^U := mul_le_mul_of_nonneg_left hu (pow_nonneg (by linarith) _)
      _ = z^(m+U) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hz (by omega)
  have h₁ := mul_le_mul_of_nonneg_left hm (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hM)
  have h₂ := mul_le_mul_of_nonneg_left hb hB
  have h₃ := mul_le_mul_of_nonneg_left hmu hM
  have h₄ := mul_le_mul_of_nonneg_left (add_le_add h₂ h₃) (sub_nonneg.mpr hR)
  nlinarith

lemma log_power_quotient {z a d : ℝ} (hz : 0 < z) (ha : 0 < a)
    (hza : z ≤ d*a) (n k : ℕ) : z^n/a^(n+k) ≤ d^(n+k)/z^k := by
  apply (div_le_div_iff₀ (pow_pos ha _) (pow_pos hz _)).mpr
  rw [← pow_add,← mul_pow]
  exact pow_le_pow_left₀ hz.le hza _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit cost of the coprimality exclusion in a prime constituent.
It follows from the proved ideal-divisor bound, uniformly in the excluded
element, and will be subtracted from the prime Siegel–Walfisz estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_exclusion_difference (S : Finset Eisenstein) (e : Eisenstein)
    (w : Eisenstein → ℂ) {M : ℝ} (hw : ∀ p ∈ S, ‖w p‖ ≤ M) :
    ‖(∑ p ∈ S, w p)-(∑ p ∈ S with IsCoprime p e, w p)‖ ≤
      M*((S.filter (fun p => ¬ IsCoprime p e)).card:ℝ) := by
  have he : (∑ p ∈ S, w p)-(∑ p ∈ S with IsCoprime p e, w p) =
      ∑ p ∈ S with ¬ IsCoprime p e, w p := by
    rw [Finset.sum_filter,Finset.sum_filter,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : IsCoprime p e <;> simp only [hp,ite_true, if_true,ite_false, if_false,not_true_eq_false,
      not_false_eq_true,sub_self,sub_zero]
  rw [he]
  calc
    _ ≤ ∑ p ∈ S with ¬ IsCoprime p e, ‖w p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ S with ¬ IsCoprime _p e, M :=
      Finset.sum_le_sum (fun p hp => hw p (Finset.mem_filter.mp hp).1)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem prime_exclusion_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein),
      (∀ p ∈ S, primaryPrime p) → ∀ e : Eisenstein, e ≠ 0 →
      ∀ (w : Eisenstein → ℂ) (M : ℝ), 0 ≤ M → (∀ p ∈ S, ‖w p‖ ≤ M) →
      ‖(∑ p ∈ S, w p)-(∑ p ∈ S with IsCoprime p e, w p)‖ ≤ C*norm e^ε*M := by
  obtain ⟨C,hC,hdiv⟩ := primary_divisor_card_small_power hε
  refine ⟨C,hC,?_⟩
  intro S hS e he w M hM hw
  have hsub : S.filter (fun p => ¬ IsCoprime p e) ⊆ S.filter (fun p => p ∣ e) := by
    intro p hp
    obtain ⟨hpS,hp⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hpS,?_⟩
    by_contra hn
    exact hp ((hS p hpS).2.irreducible.coprime_iff_not_dvd.mpr hn)
  have hc : ((S.filter (fun p => ¬ IsCoprime p e)).card:ℝ) ≤ C*norm e^ε :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (hdiv S (fun p hp => (hS p hp).1) e he)
  calc
    _ ≤ M*((S.filter (fun p => ¬ IsCoprime p e)).card:ℝ) :=
      prime_exclusion_difference S e w hw
    _ ≤ M*(C*norm e^ε) := mul_le_mul_of_nonneg_left hc hM
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExcludedPrimeInput
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerator-independent coprimality exclusion in the actual smooth
prime sum, with the error supplied by the proved divisor bound. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem excluded_prime_input_error {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R Y M : ℝ) (w : ℝ → ℂ) (χ : Eisenstein → ℂ),
      0 ≤ M → (∀ x, ‖w x‖ ≤ M) → (∀ p ∈ primeCutoff (R*Y), ‖χ p‖ ≤ 1) →
      ∀ e : Eisenstein, e ≠ 0 → ∀ u : ℝ,
      ‖excludedSmoothPrimeCharacterSum R Y w χ e u-smoothPrimeCharacterSum R Y w χ u‖ ≤
        C*norm e^ε*M := by
  obtain ⟨C,hC,hbound⟩ := prime_exclusion_small_power hε
  refine ⟨C,hC,?_⟩
  intro R Y M w χ hM hw hχ e he u
  rw [norm_sub_rev]
  apply hbound (primeCutoff (R*Y)) (fun p hp => (mem_primeCutoff.mp hp).1) e he
    (fun p => w (norm p/Y)*mellinPhase u (norm p)*χ p) M hM
  intro p hp
  rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
  exact (mul_le_of_le_one_right (_root_.norm_nonneg _) (hχ p hp)).trans (hw _)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeFactorization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independent-prime factorization, keeping the squarefree error
and the coprimality exclusion of the actual structured sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeExclusionCharacter_apply (e z : Eisenstein) :
    primeExclusionCharacter e z = if IsCoprime z e then 1 else 0 :=
  principal_residue_value e z

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_eq_prime_filter (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (i : ι) :
    fullPrimeSupport R W X i = (primeCutoff (R*X i)).filter (fun p => W i (norm p/X i) ≠ 0) := by
  ext p
  simp only [fullPrimeSupport,Finset.mem_filter,mem_primaryElementBall,mem_primeCutoff,primaryPrime]
  tauto

omit [Fintype ι] [DecidableEq ι] in
lemma excluded_prime_factor_eq (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (i : ι) (e : Eisenstein) (χ : Eisenstein → ℂ) (u : ℝ) :
    (∑ p ∈ fullPrimeSupport R W X i,
      excludedPrimeWeight e W X i p*χ p*mellinPhase u (norm p)) =
      excludedSmoothPrimeCharacterSum R (X i) (W i) χ e u := by
  rw [fullPrimeSupport_eq_prime_filter]
  unfold excludedSmoothPrimeCharacterSum
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  unfold excludedPrimeWeight
  rw [primeExclusionCharacter_apply]
  by_cases hw : W i (norm p/X i) = 0 <;> by_cases he : IsCoprime p e <;>
    simp only [hw,he,ne_eq,not_true_eq_false,not_false_eq_true,ite_true, if_true,ite_false, if_false,
      zero_mul,mul_zero,mul_one]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeErrorPointwise
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A pointwise power saving for the actual repeated-prime error. This
allows low-height character estimates to pass from independent prime
products to their squarefree restriction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma twistedErrorPrimePolynomial_pointwise_sq (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (χ : Eisenstein → ℂ) (hχ : ∀ b ∈ orderedConvolutionSupport S, ‖χ b‖ ≤ 1)
    (ℓ : ℤ) (u t : ℝ) :
    ‖twistedErrorPrimePolynomial S w χ ℓ u t‖^2 ≤
      ((orderedConvolutionSupport S).card:ℝ)*
        ∑ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖^2 := by
  have he : (∑ b ∈ orderedConvolutionSupport S,
      ‖(squarefreeConvolutionError S w b*χ b)*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) ≤
      ∑ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖^2 := by
    apply Finset.sum_le_sum
    intro b hb
    apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
    rw [norm_mul,norm_mul,norm_mul,mellinPhase_norm,
      norm_theta (orderedConvolutionSupport_ne_zero S hS b hb),mul_one,mul_one]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (hχ b hb)
  exact (norm_sum_sq_le_card_mul (orderedConvolutionSupport S)
    (fun b => (squarefreeConvolutionError S w b*χ b)*theta ℓ b*mellinPhase (t+u) (norm b))).trans
      (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _))

theorem primeConvolutionError_cutoff_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y D : ℝ),
      0 ≤ Y → 0 < D → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ orderedConvolutionSupport S, ‖χ b‖ ≤ 1) →
      ∀ (ℓ : ℤ) (u t : ℝ),
      ‖twistedErrorPrimePolynomial S w χ ℓ u t‖ ≤
        K*Y*D^(-(1/4:ℝ))*((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  obtain ⟨C,hC,henergy⟩ := primeConvolutionError_energy_bound (ι := ι)
  refine ⟨Real.sqrt (18*C),Real.sqrt_pos.2 (by positivity),?_⟩
  intro S w M Y D hY hD hM hS hprod hw χ hχ ℓ u t
  have hprime : ∀ i, ∀ p ∈ S i, primaryPrime p := fun i p hp => (hS i p hp).1
  have hcard : ((orderedConvolutionSupport S).card:ℝ) ≤ 18*Y :=
    primary_support_card_le _ hY (fun z hz => by
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨orderedPrimarySupport_primary S (fun i p hp => (hprime i p hp).1)
        (Finset.mem_image.mpr ⟨f,hf,rfl⟩),hprod f hf⟩)
  let A : ℝ := ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i)
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))
  have hs := twistedErrorPrimePolynomial_pointwise_sq S w hprime χ hχ ℓ u t
  have hb := henergy S w M Y D hY hD hM hS hprod hw
  have htotal : ‖twistedErrorPrimePolynomial S w χ ℓ u t‖^2 ≤
      18*C*Y^2*D^(-(1/2:ℝ))*A^2 := by
    apply hs.trans
    calc
      _ ≤ (18*Y)*(C*Y*D^(-(1/2:ℝ))*A^2) :=
        mul_le_mul hcard hb (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
      _ = _ := by ring
  have heq : (Real.sqrt (18*C)*Y*D^(-(1/4:ℝ))*A)^2 =
      18*C*Y^2*D^(-(1/2:ℝ))*A^2 := by
    rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity),
      ← Real.rpow_natCast (D^(-(1/4:ℝ))) 2,← Real.rpow_mul hD.le]
    norm_num
  have hfinal := (sq_le_sq₀ (_root_.norm_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hY)
      (Real.rpow_nonneg hD.le _)) hA)).mp (htotal.trans_eq heq.symm)
  simpa only [A,mul_assoc] using hfinal

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeErrorSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The repeated-prime error in the literal full convolution has every
logarithmic saving for rough coordinates. Its support saving is proved. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem full_prime_error_log_saving {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    {c R : ℝ} (hc : 0 < c) (hR : 1 ≤ R) (k : ℕ) :
    ∃ L₀ : ℝ, ∀ (r : γ) (X : ι → ℝ), L₀ ≤ L r → 1 ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      ∀ (e : Eisenstein) (χ : Eisenstein → ℂ),
      (∀ b ∈ orderedConvolutionSupport (fullPrimeSupport R (W r) X), ‖χ b‖ ≤ 1) →
      ∀ (ℓ : ℤ) (u t : ℝ),
      ‖twistedErrorPrimePolynomial (fullPrimeSupport R (W r) X)
        (excludedPrimeWeight e (W r) X) χ ℓ u t‖ ≤ L r/(1+Real.log (L r))^k := by
  classical
  obtain ⟨K,hK,hbound⟩ := primeConvolutionError_cutoff_bound (ι := ι)
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  let n := Fintype.card ι
  let C := K*R^n*(n^n:ℕ)*M^n
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg hK.le
    (pow_nonneg (zero_le_one.trans hR) _)) (Nat.cast_nonneg _)) (pow_nonneg hM _)
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp
    (exclusion_log_absorption (c := 1) (d := 1-c/4) (ε := 1)
      (by norm_num) (by linarith) hC (m*n) k)
  refine ⟨L₀,?_⟩
  intro r X hL₀' hL hX hprod hrough e χ hχ ℓ u t
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hXp : ∀ i, 0 < X i := fun i => zero_lt_one.trans_le (hX i)
  have hprime : ∀ i, ∀ p ∈ fullPrimeSupport R (W r) X i,
      primaryPrime p ∧ (L r)^c < norm p := by
    intro i p hp
    refine ⟨fullPrimeSupport_prime R (W r) X i p hp,?_⟩
    have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hcont := ((hW.smooth (r,i)).continuous)
    have hh : 1 < norm p/X i := lt_of_not_ge (fun h => hn
      (continuous_zero_on_lower_closed hcont (hlo r i) h))
    have hh' : X i < norm p := by simpa only [one_mul] using (lt_div_iff₀ (hXp i)).mp hh
    exact (hrough i).trans_lt hh'
  have hnorm : ∀ f ∈ Fintype.piFinset (fullPrimeSupport R (W r) X),
      norm (∏ i, f i) ≤ R^n*L r := by
    intro f hf
    rw [norm_finset_prod]
    calc
      _ ≤ ∏ i, (R*X i) := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ =>
        (mem_primaryElementBall.mp (Finset.mem_filter.mp
          (Finset.mem_filter.mp ((Fintype.mem_piFinset.mp hf) i)).1).1).2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,Finset.card_univ,hprod,n]
  have hw : ∀ i, ∀ p ∈ fullPrimeSupport R (W r) X i,
      ‖excludedPrimeWeight e (W r) X i p‖ ≤ M*(1+Real.log (L r))^m := by
    intro i p _
    rw [excludedPrimeWeight,norm_mul]
    apply le_trans (mul_le_of_le_one_right (_root_.norm_nonneg _) ?_) (hMb (r,i) _)
    rw [primeExclusionCharacter_apply]
    split_ifs <;> simp
  have hb := hbound (fullPrimeSupport R (W r) X) (excludedPrimeWeight e (W r) X)
    (fun _ => M*(1+Real.log (L r))^m) (R^n*L r) ((L r)^c)
    (mul_nonneg (pow_nonneg (zero_le_one.trans hR) _) hLp.le)
    (Real.rpow_pos_of_pos hLp _) (fun _ => mul_nonneg hM (pow_nonneg hz.le _))
    hprime hnorm hw χ hχ ℓ u t
  have he : (L r)^(1-c/4) = L r*(L r)^(c*(-(1/4:ℝ))) := by
    rw [show 1-c/4 = 1+c*(-(1/4:ℝ)) by ring,Real.rpow_add hLp,Real.rpow_one]
  have heq : K*(R^n*L r)*((L r)^c)^(-(1/4:ℝ))*(n^n:ℕ)*
      (∏ _i : ι, M*(1+Real.log (L r))^m) =
      C*(L r)^(1-c/4)*(1+Real.log (L r))^(m*n) := by
    rw [Finset.prod_const,Finset.card_univ,mul_pow,← pow_mul,← Real.rpow_mul hLp.le,he]
    dsimp [C,n]
    ring
  change _ ≤ K*(R^n*L r)*((L r)^c)^(-(1/4:ℝ))*(n^n:ℕ)*
    (∏ _i : ι, M*(1+Real.log (L r))^m) at hb
  rw [heq] at hb
  apply hb.trans
  simpa only [Real.rpow_one] using hL₀ (L r) hL₀' (L r) ((L r)^(1-c/4))
    (Real.rpow_nonneg hLp.le _) le_rfl (by rw [Real.rpow_one])

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentPrimeSaving
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary logarithmic saving for the genuine independent prime product.
All factors retain the specified varying smooth weights and the exclusion. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
lemma prime_product_log_bound (F : ι → ℂ) (X : ι → ℝ) {K L z : ℝ}
    (hK : 0 ≤ K) (hX : ∀ i, 0 ≤ X i) (hprod : (∏ i, X i) = L)
    (hz : 1 ≤ z) (k : ℕ) (hF : ∀ i, ‖F i‖ ≤ K*X i/z^k) :
    ‖∏ i, F i‖ ≤ K^(Fintype.card ι)*L/z^k := by
  have hzp : 0 < z := zero_lt_one.trans_le hz
  have hk : 1 ≤ z^k := one_le_pow₀ hz
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hden : z^k ≤ (z^k)^(Fintype.card ι) := le_self_pow₀ hk (Nat.ne_of_gt hn)
  rw [norm_prod]
  calc
    _ ≤ ∏ i, (K*X i/z^k) := Finset.prod_le_prod (fun i _ => _root_.norm_nonneg _) (fun i _ => hF i)
    _ = K^(Fintype.card ι)*L/(z^k)^(Fintype.card ι) := by
      rw [Finset.prod_div_distrib,Finset.prod_mul_distrib]
      simp only [Finset.prod_const,Finset.card_univ,hprod]
    _ ≤ _ := div_le_div_of_nonneg_left
      (mul_nonneg (pow_nonneg hK _) (hprod ▸ Finset.prod_nonneg (fun i _ => hX i)))
      (pow_pos hzp _) hden

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_KummerPrimeFactorization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independent-prime factorization for arbitrary numerator,
including units and powers of the ramified prime. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicNumeratorHom_primary (v : Eisenstein) {b : Eisenstein} (hb : primary b) :
    cubicNumeratorHom v b = cubicSymbol b v := cubicNumeratorLift_primary v hb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConductorScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conductor powers measured at the full convolution length transfer
to each rough coordinate, with one additional logarithmic power. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma rough_coordinate_conductor_scale {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, L^c ≤ Y →
      (Real.log L)^A ≤ (Real.log Y)^(A+1) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop ((c⁻¹)^A/c)] with L hL hlog
  intro Y hY
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hYp : 0 < Y := (Real.rpow_pos_of_pos hLp c).trans_le hY
  have hlogs : c*Real.log L ≤ Real.log Y := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hLp c) hY
    rwa [Real.log_rpow hLp] at h
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hmul : (c⁻¹)^A ≤ c*Real.log L := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hlog
  have hlogY : 0 < Real.log Y := by
    have hpos : 0 < (c⁻¹)^A := Real.rpow_pos_of_pos (inv_pos.mpr hc) _
    exact hpos.trans_le (hmul.trans hlogs)
  have hcomp : Real.log L ≤ c⁻¹*Real.log Y := by
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hc).mpr (by nlinarith)
  calc
    _ ≤ (c⁻¹*Real.log Y)^A := Real.rpow_le_rpow hlogL hcomp hA
    _ = (c⁻¹)^A*(Real.log Y)^A := Real.mul_rpow (inv_nonneg.mpr hc.le) hlogY.le
    _ ≤ Real.log Y*(Real.log Y)^A := mul_le_mul_of_nonneg_right
      (hmul.trans hlogs) (Real.rpow_nonneg hlogY.le _)
    _ = _ := by rw [Real.rpow_add hlogY,Real.rpow_one]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredResidualFrequencies
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact passage from ramified/cube frequencies to the structured pair
moments. A cube factor becomes an arithmetic exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_primary (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    ∀ i, ∀ z ∈ fullPrimeSupport R W X i, primary z := by
  intro i z hz
  exact (mem_primaryElementBall.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1

lemma cubicSymbol_cube_indicator {z : Eisenstein} (hz : primary z) (j : Eisenstein) :
    cubicSymbol z (j^3) = if IsCoprime z j then 1 else 0 := by
  rw [cubicSymbol_pow_upper hz]
  by_cases hj : IsCoprime z j
  · rw [ite_eq_left hj,cubicSymbol_cube_of_isCoprime hz j hj]
  · rw [ite_eq_right hj,cubicSymbol_eq_zero_of_not_isCoprime hz hj,zero_pow (by norm_num : (3:ℕ) ≠ 0)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete finite low-conductor frequency support: a small
nonzero core times a bounded cube, with precisely the cubes removed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_lowNoncubeSupport {V J : ℝ} {h : Eisenstein} (hh : h ∈ lowNoncubeSupport V J) :
    (¬∃ a : Eisenstein, a^3 = h) ∧ ∃ v j : Eisenstein,
      v ≠ 0 ∧ j ≠ 0 ∧ norm v ≤ V ∧ norm j ≤ J ∧ h = v*j^3 := by
  obtain ⟨hi,hn⟩ := Finset.mem_filter.mp hh
  obtain ⟨⟨v,j⟩,hm,he⟩ := Finset.mem_image.mp hi
  have hv := mem_nonzeroNormBall.mp (Finset.mem_product.mp hm).1
  have hj := mem_nonzeroNormBall.mp (Finset.mem_product.mp hm).2
  exact ⟨hn,v,j,hv.2,hj.2,hv.1,hj.1,he.symm⟩

lemma lowNoncubeSupport_card {V J : ℝ} (hV : 0 ≤ V) (hJ : 0 ≤ J) :
    ((lowNoncubeSupport V J).card:ℝ) ≤ 324*V*J := by
  have hc : (lowNoncubeSupport V J).card ≤
      ((nonzeroNormBall V).product (nonzeroNormBall J)).card :=
    (Finset.card_filter_le _ _).trans (Finset.card_image_le)
  have hb : (((nonzeroNormBall V).product (nonzeroNormBall J)).card:ℝ) =
      ((nonzeroNormBall V).card:ℝ)*((nonzeroNormBall J).card:ℝ) := by
    exact_mod_cast Finset.card_product (nonzeroNormBall V) (nonzeroNormBall J)
  calc
    _ ≤ (((nonzeroNormBall V).product (nonzeroNormBall J)).card:ℝ) := Nat.cast_le.mpr hc
    _ = _ := hb
    _ ≤ (18*V)*(18*J) := mul_le_mul (nonzeroNormBall_card_le hV) (nonzeroNormBall_card_le hJ)
      (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

lemma low_core_log_quotient {z : ℝ} (hz : 1 ≤ z) (a k : ℕ) :
    z^a/(z^(a+k+1))^2 ≤ 1/z^k := by
  have hzp : 0 < z := zero_lt_one.trans_le hz
  apply (div_le_div_iff₀ (pow_pos (pow_pos hzp _) 2) (pow_pos hzp _)).mpr
  rw [one_mul,← pow_add,← pow_mul]
  exact pow_le_pow_right₀ hz (by omega)

lemma low_core_mass_bound {M C J L z : ℝ} {n a k : ℕ}
    (hJ : 0 ≤ J) (hz : 1 ≤ z)
    (hn : (n:ℝ) ≤ 324*z^a*J)
    (hM : M ≤ (n:ℝ)*(C*L/z^(a+k+1))^2) :
    M ≤ (324*C^2)*J*L^2/z^k := by
  have hquot := low_core_log_quotient hz a k
  calc
    M ≤ (324*z^a*J)*(C*L/z^(a+k+1))^2 := hM.trans
      (mul_le_mul_of_nonneg_right hn (sq_nonneg _))
    _ = (324*C^2)*J*L^2*(z^a/(z^(a+k+1))^2) := by rw [div_pow]; ring
    _ ≤ (324*C^2)*J*L^2*(1/z^k) := mul_le_mul_of_nonneg_left hquot
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C)) hJ) (sq_nonneg L))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicCoreCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coverage of a noncube frequency by either the low-core set or
a ramified/squarefree pair of large conductor. No decomposition is assumed. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_cube (j : Eisenstein) : norm (j^3) = norm j^3 := by
  simp only [pow_succ,norm_mul_eq,pow_zero,norm_one_eq]

lemma cube_part_norm_bound {h v j : Eisenstein} {H : ℝ}
    (hv : v ≠ 0) (heq : h = v*j^3) (hh : norm h ≤ H) :
    norm j ≤ H^(1/3:ℝ) := by
  have hcube : norm j^3 ≤ H := by
    calc
      _ ≤ norm v*norm j^3 := le_mul_of_one_le_left (pow_nonneg (norm_nonneg j) _) (one_le_norm hv)
      _ = norm h := by rw [heq,norm_mul_eq,norm_cube]
      _ ≤ H := hh
  have hp := Real.rpow_le_rpow (pow_nonneg (norm_nonneg j) 3) hcube (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (norm j^3)^(1/3:ℝ) = norm j := by
    rw [← Real.rpow_natCast (norm j) 3,← Real.rpow_mul (norm_nonneg j)]
    norm_num
  rwa [he] at hp

lemma mem_lowNoncubeSupport_of_core {h v j : Eisenstein} {V H : ℝ}
    (hv : v ≠ 0) (hj : j ≠ 0) (heq : h = v*j^3) (hh : norm h ≤ H)
    (hsmall : norm v ≤ V) (hn : ¬∃ a : Eisenstein, a^3 = h) :
    h ∈ lowNoncubeSupport V (H^(1/3:ℝ)) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(v,j),?_,heq.symm⟩,hn⟩
  exact Finset.mem_product.mpr ⟨mem_nonzeroNormBall.mpr ⟨hsmall,hv⟩,
    mem_nonzeroNormBall.mpr ⟨cube_part_norm_bound hv heq hh,hj⟩⟩

theorem noncube_large_core_decomposition {h : Eisenstein} {V H : ℝ}
    (hh0 : h ≠ 0) (hh : norm h ≤ H) (hn : ¬∃ a : Eisenstein, a^3 = h)
    (hnot : h ∉ lowNoncubeSupport V (H^(1/3:ℝ))) :
    ∃ r s t j : Eisenstein, r ≠ 0 ∧ norm r ≤ 729 ∧
      primary s ∧ primary t ∧ Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧
      j ≠ 0 ∧ h = r*s*t^2*j^3 ∧
      V/729 < norm s*norm t^2 ∧ norm s*norm t^2 ≤ H ∧ norm j ≤ H^(1/3:ℝ) := by
  obtain ⟨r,s,t,j,hr,hrN,hs,ht,hss,hst,hcop,hj,heq⟩ := full_cube_decomposition hh0
  have hv : r*s*t^2 ≠ 0 := mul_ne_zero (mul_ne_zero hr (primary_ne_zero hs))
    (pow_ne_zero _ (primary_ne_zero ht))
  have hcore : h = (r*s*t^2)*j^3 := heq
  have hlarge : V < norm (r*s*t^2) := lt_of_not_ge (fun hsmall => hnot
    (mem_lowNoncubeSupport_of_core hv hj hcore hh hsmall hn))
  have hc : norm (r*s*t^2) = norm r*(norm s*norm t^2) := by
    rw [norm_mul_eq,norm_mul_eq]
    have ht2 : norm (t^2) = norm t^2 := by simp only [pow_two,norm_mul_eq]
    rw [ht2]
    ring
  have hD0 : 0 ≤ norm s*norm t^2 := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hsmall : norm (r*s*t^2) ≤ norm h := by
    calc
      _ ≤ norm (r*s*t^2)*norm (j^3) :=
        le_mul_of_one_le_right (norm_nonneg _) (one_le_norm (pow_ne_zero _ hj))
      _ = norm h := by simp only [hcore,norm_mul_eq]
  refine ⟨r,s,t,j,hr,hrN,hs,ht,hss,hst,hcop,hj,heq,?_,?_,cube_part_norm_bound hv hcore hh⟩
  · apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 729)).mpr
    rw [hc] at hlarge
    nlinarith [mul_le_mul_of_nonneg_right hrN hD0]
  · apply le_trans _ (hsmall.trans hh)
    rw [hc]
    exact le_mul_of_one_le_left hD0 (one_le_norm hr)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicDyadicCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite cover of all noncube frequencies outside the small-core set
by the actual coprime ramified/squarefree blocks used in the moment bounds. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coreDyadicConductor_pos (i j : ℕ) : 0 < coreDyadicConductor i j := by
  unfold coreDyadicConductor
  positivity

lemma squarefreePrimaryDyad_gramDyad {i : ℕ} {s : Eisenstein}
    (hs : s ∈ squarefreePrimaryDyad i) : gramDyad ((2:ℝ)^i) s := by
  obtain ⟨hf,hp,hq⟩ := mem_squarefreePrimaryDyad.mp hs
  have hlog := (mem_frequencyDyad.mp hf).2
  refine ⟨hp,hq,(frequencyDyad_norm hf).1,?_⟩
  have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (normNat s)
  rw [hlog] at hlt
  have hcast : norm s < (2:ℝ)^(i+1) := by
    rw [← normNat_cast]
    exact_mod_cast hlt
  simpa only [pow_succ,mul_comm] using hcast

lemma real_cube_scale_bound {x B D : ℝ} (hx : 0 ≤ x) (hD : 0 < D)
    (h : x^3*D ≤ B) : x ≤ (B/D)^(1/3:ℝ) := by
  have hc : x^3 ≤ B/D := (le_div_iff₀ hD).mpr h
  have hp := Real.rpow_le_rpow (pow_nonneg hx 3) hc (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (x^3)^(1/3:ℝ) = x := by
    rw [← Real.rpow_natCast x 3,← Real.rpow_mul hx]
    norm_num
  rwa [he] at hp

theorem noncube_mem_coreDyadicBlock {h : Eisenstein} {V B : ℝ}
    (hh0 : h ≠ 0) (hh : norm h ≤ B) (hn : ¬∃ a : Eisenstein, a^3 = h)
    (hnot : h ∉ lowNoncubeSupport V (B^(1/3:ℝ))) :
    ∃ z ∈ largeCoreDyadicIndices V B, h ∈ coreDyadicBlock B z.1 z.2 := by
  obtain ⟨r,s,t,c,hr,hrN,hs,ht,hss,hst,hcop,hc,heq,hlarge,hcore,hcN⟩ :=
    noncube_large_core_decomposition hh0 hh hn hnot
  let i := Nat.log 2 (normNat s)
  let j := Nat.log 2 (normNat t)
  have hsD : s ∈ squarefreePrimaryDyad i := mem_squarefreePrimaryDyad.mpr
    ⟨mem_frequencyDyad.mpr ⟨primary_ne_zero hs,rfl⟩,hs,hss⟩
  have htD : t ∈ squarefreePrimaryDyad j := mem_squarefreePrimaryDyad.mpr
    ⟨mem_frequencyDyad.mpr ⟨primary_ne_zero ht,rfl⟩,ht,hst⟩
  have hsG := squarefreePrimaryDyad_gramDyad hsD
  have htG := squarefreePrimaryDyad_gramDyad htD
  have hDlo : coreDyadicConductor i j ≤ norm s*norm t^2 := by
    exact mul_le_mul hsG.2.2.1 (pow_le_pow_left₀ (by positivity) htG.2.2.1 2)
      (by positivity) (norm_nonneg s)
  have hDhi : norm s*norm t^2 < 8*coreDyadicConductor i j := by
    have ht2 : norm t^2 < (2*(2:ℝ)^j)^2 :=
      (pow_lt_pow_left₀ htG.2.2.2 (norm_nonneg t) (by norm_num : (2:ℕ) ≠ 0))
    calc
      _ < (2*(2:ℝ)^i)*((2*(2:ℝ)^j)^2) := mul_lt_mul hsG.2.2.2 ht2.le
        (sq_pos_of_pos (zero_lt_one.trans_le (one_le_norm (primary_ne_zero ht)))) (by positivity)
      _ = _ := by unfold coreDyadicConductor; ring
  have hDb : coreDyadicConductor i j ≤ B := hDlo.trans hcore
  have hidx : ∀ (a : Eisenstein), primary a → norm a ≤ B →
      Nat.log 2 (normNat a) < Nat.log 2 ⌊B⌋₊+1 := by
    intro a ha haB
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    apply Nat.le_floor
    rwa [normNat_cast]
  have hsB : norm s ≤ B := (le_mul_of_one_le_right (norm_nonneg s)
    (one_le_pow₀ (one_le_norm (primary_ne_zero ht)))).trans hcore
  have htB : norm t ≤ B := by
    have htt : norm t ≤ norm t^2 := by
      nlinarith [one_le_norm (primary_ne_zero ht)]
    exact htt.trans ((le_mul_of_one_le_left (sq_nonneg _) (one_le_norm (primary_ne_zero hs))).trans hcore)
  have hcube : norm c^3*coreDyadicConductor i j ≤ B := by
    have hn : norm h = norm r*(norm s*norm t^2)*norm c^3 := by
      simp only [heq,norm_mul_eq,norm_cube,pow_two]
      ring
    calc
      _ ≤ norm c^3*(norm s*norm t^2) := mul_le_mul_of_nonneg_left hDlo (pow_nonneg (norm_nonneg c) _)
      _ ≤ norm r*(norm s*norm t^2)*norm c^3 := by
        nlinarith [mul_le_mul_of_nonneg_right
          (one_le_norm hr) (mul_nonneg (mul_nonneg (norm_nonneg s) (sq_nonneg (norm t)))
            (pow_nonneg (norm_nonneg c) 3))]
      _ = norm h := hn.symm
      _ ≤ B := hh
  refine ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (hidx s hs hsB),Finset.mem_range.mpr (hidx t ht htB)⟩,
    ⟨by dsimp only; linarith,hDb⟩⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨((r,c),(s,t)),Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨mem_nonzeroNormBall.mpr ⟨hrN,hr⟩,mem_nonzeroNormBall.mpr
      ⟨real_cube_scale_bound (norm_nonneg c) (coreDyadicConductor_pos i j) hcube,hc⟩⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsD,htD⟩,hcop⟩⟩,heq.symm⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicFrequencyMassSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete small-core / dyadic-core partition of a finite noncube
mass. Multiple arithmetic decompositions cost no frequency multiplicity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem noncube_frequency_mass_split (H : Finset Eisenstein) {V B : ℝ}
    (hH : ∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h)
    (f : Eisenstein → ℝ) (hf : ∀ h, 0 ≤ f h) :
    (∑ h ∈ H, f h) ≤
      (∑ h ∈ H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))), f h)+
      ∑ z ∈ largeCoreDyadicIndices V B, ∑ h ∈ coreDyadicBlock B z.1 z.2, f h := by
  let I := (largeCoreDyadicIndices V B).sigma (fun z => coreDyadicBlock B z.1 z.2)
  let F : Sigma (fun _ : ℕ × ℕ => Eisenstein) → Eisenstein := Sigma.snd
  have hcover : H.filter (fun h => h ∉ lowNoncubeSupport V (B^(1/3:ℝ))) ⊆ I.image F := by
    intro h hh
    obtain ⟨hm,hn⟩ := Finset.mem_filter.mp hh
    obtain ⟨z,hz,hb⟩ := noncube_mem_coreDyadicBlock (hH h hm).1
      (hH h hm).2.1 (hH h hm).2.2 hn
    exact Finset.mem_image.mpr ⟨⟨z,h⟩,Finset.mem_sigma.mpr ⟨hz,hb⟩,rfl⟩
  have hsum : (∑ h ∈ H.filter (fun h => h ∉ lowNoncubeSupport V (B^(1/3:ℝ))), f h) ≤
      ∑ z ∈ largeCoreDyadicIndices V B, ∑ h ∈ coreDyadicBlock B z.1 z.2, f h := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun h _ _ => hf h)).trans
    apply (Finset.sum_image_le_of_nonneg (s := I) (g := F) (f := f) (fun h _ => hf h)).trans_eq
    exact Finset.sum_sigma _ _ _
  rw [← Finset.sum_filter_add_sum_filter_not H
    (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))) f]
  exact add_le_add le_rfl hsum

lemma largeCoreDyadicIndices_card (V B : ℝ) :
    (largeCoreDyadicIndices V B).card ≤ (Nat.log 2 ⌊B⌋₊+1)^2 := by
  unfold largeCoreDyadicIndices
  apply (Finset.card_filter_le _ _).trans
  exact le_of_eq ((Finset.card_product _ _).trans (by simp only [Finset.card_range,pow_two]))

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeDivisorExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed positive power saving after shortening a rough common
prime divisor. Only the exponents needed for the dispersion application
are recorded. -/
noncomputable section
namespace CubicFirstMoment

lemma outer_benchmark_factorization {B N : ℝ} (hB : 0 < B) (hN : 0 ≤ N) :
    B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N =
      B^(1/3:ℝ)*(B^(2/3:ℝ)+B^(1/3:ℝ)*N^(2/3:ℝ)+N) := by
  rw [Real.mul_rpow hB.le hN]
  have h₁ : B^(1/3:ℝ)*B^(2/3:ℝ) = B := by rw [← Real.rpow_add hB]; norm_num
  have h₂ : B^(1/3:ℝ)*B^(1/3:ℝ) = B^(2/3:ℝ) := by
    rw [← Real.rpow_add hB]
    norm_num
  rw [mul_add,mul_add,← mul_assoc,h₁,h₂]

lemma shortened_outer_polynomial {L B N A δ η : ℝ}
    (hL : 1 ≤ L) (hB : 0 ≤ B) (hN : 0 ≤ N) (hA : 1 ≤ A)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hη : η ≤ 1/4) (hηδ : η ≤ δ/4)
    (hBL : B ≤ L^(1+η)) (hNL : N ≤ A*L^(1-δ)) :
    B^(2/3:ℝ)+B^(1/3:ℝ)*N^(2/3:ℝ)+N ≤
      (1+A^(2/3:ℝ)+A)*L^(1-δ/8) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hB₂ : B^(2/3:ℝ) ≤ L^(1-δ/8) := by
    calc
      _ ≤ (L^(1+η))^(2/3:ℝ) := Real.rpow_le_rpow hB hBL (by norm_num)
      _ = L^((1+η)*(2/3:ℝ)) := (Real.rpow_mul hLp.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by nlinarith)
  have hBN : B^(1/3:ℝ)*N^(2/3:ℝ) ≤ A^(2/3:ℝ)*L^(1-δ/8) := by
    calc
      _ ≤ (L^(1+η))^(1/3:ℝ)*(A*L^(1-δ))^(2/3:ℝ) :=
        mul_le_mul (Real.rpow_le_rpow hB hBL (by norm_num))
          (Real.rpow_le_rpow hN hNL (by norm_num))
          (Real.rpow_nonneg hN _) (Real.rpow_nonneg (Real.rpow_nonneg hLp.le _) _)
      _ = A^(2/3:ℝ)*L^((1+η)/3+(1-δ)*(2/3:ℝ)) := by
        rw [Real.mul_rpow hAp (Real.rpow_nonneg hLp.le _),
          ← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le]
        rw [show (1+η)*(1/3:ℝ) = (1+η)/3 by ring, Real.rpow_add hLp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (Real.rpow_nonneg hAp _)
  have hN' : N ≤ A*L^(1-δ/8) := hNL.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) hAp)
  calc
    _ ≤ L^(1-δ/8)+A^(2/3:ℝ)*L^(1-δ/8)+A*L^(1-δ/8) :=
      add_le_add (add_le_add hB₂ hBN) hN'
    _ = _ := by ring

lemma shortened_outer_epsilon {L B N A δ η : ℝ}
    (hL : 1 ≤ L) (hB : 0 ≤ B) (hN : 0 ≤ N) (hA : 1 ≤ A)
    (hδ : 0 < δ) (hη : η ≤ 1/4)
    (hBL : B ≤ L^(1+η)) (hNL : N ≤ A*L^(1-δ)) :
    (2*B*N)^(δ/100) ≤ (2*A)^(δ/100)*L^(3*δ/100) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hprod : 2*B*N ≤ (2*A)*L^3 := by
    calc
      _ ≤ 2*(L^(1+η))*(A*L^(1-δ)) := by gcongr
      _ = (2*A)*(L^(1+η)*L^(1-δ)) := by ring
      _ = (2*A)*L^((1+η)+(1-δ)) := by rw [← Real.rpow_add hLp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by rw [← Real.rpow_natCast L 3]; exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num; linarith))
        (by positivity)
  calc
    _ ≤ ((2*A)*L^3)^(δ/100) := Real.rpow_le_rpow (by positivity) hprod (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 2*A) (by positivity : 0 ≤ L^3),
        ← Real.rpow_natCast L 3,← Real.rpow_mul hLp.le]
      congr 2
      ring

lemma shortened_outer_normalized_saving {L B N A δ η : ℝ}
    (hL : 1 ≤ L) (hB : 0 ≤ B) (hN : 0 ≤ N) (hA : 1 ≤ A)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hη : η ≤ 1/4) (hηδ : η ≤ δ/4)
    (hBL : B ≤ L^(1+η)) (hNL : N ≤ A*L^(1-δ)) :
    (2*B*N)^(δ/100)*(B^(2/3:ℝ)+B^(1/3:ℝ)*N^(2/3:ℝ)+N) ≤
      ((2*A)^(δ/100)*(1+A^(2/3:ℝ)+A))*L^(1-δ/20) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hpoly := shortened_outer_polynomial hL hB hN hA hδ hδ₁ hη hηδ hBL hNL
  have hpow := shortened_outer_epsilon hL hB hN hA hδ hη hBL hNL
  calc
    _ ≤ ((2*A)^(δ/100)*L^(3*δ/100))*
        ((1+A^(2/3:ℝ)+A)*L^(1-δ/8)) :=
      mul_le_mul hpow hpoly (by positivity) (by positivity)
    _ = ((2*A)^(δ/100)*(1+A^(2/3:ℝ)+A))*L^(3*δ/100+(1-δ/8)) := by
      rw [Real.rpow_add hLp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)

lemma shortened_outer_power_saving {L B N A δ η : ℝ}
    (hL : 1 ≤ L) (hB : 0 < B) (hN : 0 ≤ N) (hA : 1 ≤ A)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hη : η ≤ 1/4) (hηδ : η ≤ δ/4)
    (hBL : B ≤ L^(1+η)) (hNL : N ≤ A*L^(1-δ)) :
    (2*B*N)^(δ/100)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*L ≤
      ((2*A)^(δ/100)*(1+A^(2/3:ℝ)+A))*L^2*B^(1/3:ℝ)*L^(-δ/20) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hs := mul_le_mul_of_nonneg_right
    (shortened_outer_normalized_saving hL hB.le hN hA hδ hδ₁ hη hηδ hBL hNL)
    (mul_nonneg (Real.rpow_nonneg hB.le (1/3:ℝ)) hLp.le)
  rw [outer_benchmark_factorization hB hN]
  refine (le_of_eq ?_).trans (hs.trans_eq ?_)
  · ring
  · symm
    have he : L^(1-δ/20)*L = L^2*L^(-δ/20) := by
      rw [Real.rpow_sub hLp,Real.rpow_one,
        show -δ/20 = -(δ/20) by ring, Real.rpow_neg hLp.le]
      ring
    calc
      _ = ((2*A)^(δ/100)*(1+A^(2/3:ℝ)+A))*B^(1/3:ℝ)*(L^2*L^(-δ/20)) := by ring
      _ = _ := by rw [← he]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeOuterSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full outer cubic-sieve estimate for finite noncube frequencies,
derived by covering with the actual core dyads and summing their bounds. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma lowNoncubeSupport_zero (J : ℝ) : lowNoncubeSupport 0 J = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro h hh
  obtain ⟨_,v,j,hv,_,hNv,_,_⟩ := mem_lowNoncubeSupport hh
  have hv1 := one_le_norm hv
  linarith

theorem noncube_outer_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (B N : ℝ),
      1 ≤ B → 1 ≤ N →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 := by
  have he : 0 < ε/2 := by linarith
  obtain ⟨C,hC,hblock⟩ := outer_core_block_sieve he
  obtain ⟨D,hD,hlog⟩ := natLog_power_bound 2 he
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro S H B N hB hN hS hH β
  have hB0 := zero_le_one.trans hB
  have hN0 := zero_le_one.trans hN
  have hcount : ((largeCoreDyadicIndices 0 B).card:ℝ) ≤ D*B^(ε/2) := by
    calc
      _ ≤ ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ)^2 := by
        exact_mod_cast largeCoreDyadicIndices_card 0 B
      _ ≤ D*(⌊B⌋₊:ℝ)^(ε/2) := hlog _ ((Nat.one_le_floor_iff B).mpr hB)
      _ ≤ D*B^(ε/2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hB0) he.le) hD.le
  have hsplit := noncube_frequency_mass_split (V := 0) H hH
    (fun h => ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) (fun _ => sq_nonneg _)
  simp only [lowNoncubeSupport_zero,Finset.notMem_empty,Finset.filter_false,
    Finset.sum_empty,zero_add] at hsplit
  have hrows (z : ℕ × ℕ) (hz : z ∈ largeCoreDyadicIndices 0 B) :=
    hblock S (coreDyadicBlock B z.1 z.2) B N z.1 z.2 hB0 hN
      (Finset.mem_filter.mp hz).2.2 hS (fun _ h => h) β
  have hE : 0 ≤ ∑ n ∈ S, ‖β n‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : B^(ε/2)*(2*B*N)^(ε/2) ≤ (2*B*N)^ε := by
    calc
      _ ≤ (2*B*N)^(ε/2)*(2*B*N)^(ε/2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        apply Real.rpow_le_rpow hB0 _ he.le
        nlinarith
      _ = _ := by rw [← Real.rpow_add (by positivity : 0 < 2*B*N)]; congr 1; ring
  calc
    _ ≤ ∑ z ∈ largeCoreDyadicIndices 0 B,
        C*(2*B*N)^(ε/2)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 :=
      hsplit.trans (Finset.sum_le_sum hrows)
    _ = ((largeCoreDyadicIndices 0 B).card:ℝ)*
        (C*(2*B*N)^(ε/2)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2) := by simp
    _ ≤ (D*B^(ε/2))*
        (C*(2*B*N)^(ε/2)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (C*D)*(B^(ε/2)*(2*B*N)^(ε/2))*
        (B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*∑ n ∈ S, ‖β n‖^2 := by ring
    _ ≤ _ := by gcongr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_AllFrequencyOuterSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Add the explicit cube frequencies to the proved outer sieve. The
cube count is a lattice count, not an additional analytic hypothesis. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cube_frequency_card_le (H : Finset Eisenstein) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ∃ j : Eisenstein, j^3 = h) :
    (H.card:ℝ) ≤ 18*B^(1/3:ℝ) := by
  have hs : H ⊆ (nonzeroNormBall (B^(1/3:ℝ))).image (fun j => j^3) := by
    intro h hh
    obtain ⟨hne,hn,j,rfl⟩ := hH h hh
    have hj : j ≠ 0 := fun hj => hne (by rw [hj,zero_pow (by decide)])
    have hpow : (norm j)^3 ≤ B := by simpa only [eisenstein_norm_pow] using hn
    have hr := Real.rpow_le_rpow (pow_nonneg (norm_nonneg j) 3) hpow
      (by norm_num : (0:ℝ) ≤ 1/3)
    rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg j)] at hr
    norm_num at hr
    exact Finset.mem_image.mpr ⟨j,mem_nonzeroNormBall.mpr ⟨hr,hj⟩,rfl⟩
  exact (Nat.cast_le.mpr ((Finset.card_le_card hs).trans Finset.card_image_le)).trans
    (nonzeroNormBall_card_le (Real.rpow_nonneg hB _))

lemma cubic_character_row_sq (S : Finset Eisenstein)
    (hS : ∀ n ∈ S, primary n) (β : Eisenstein → ℂ) (h : Eisenstein) :
    ‖∑ n ∈ S, β n*cubicSymbol n h‖^2 ≤ (S.card:ℝ)*∑ n ∈ S, ‖β n‖^2 := by
  have hn : ‖∑ n ∈ S, β n*cubicSymbol n h‖ ≤ ∑ n ∈ S, ‖β n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS n hn) _)
  apply (pow_le_pow_left₀ (_root_.norm_nonneg _) hn 2).trans
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
    Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun n => ‖β n‖)

theorem all_frequency_outer_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (B N : ℝ),
      1 ≤ B → 1 ≤ N →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) → ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 := by
  obtain ⟨C,hC,hbound⟩ := noncube_outer_sieve hε
  refine ⟨C+324,by positivity,?_⟩
  intro S H B N hB hN hS hH β
  let Q := H.filter (fun h => ∃ j : Eisenstein, j^3 = h)
  let T := H.filter (fun h => ¬∃ j : Eisenstein, j^3 = h)
  let E := ∑ n ∈ S, ‖β n‖^2
  let P := B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hscale : 1 ≤ (2*B*N)^ε := Real.one_le_rpow (by nlinarith) hε.le
  have hnc := hbound S T B N hB hN hS (fun h hh =>
    ⟨(hH h (Finset.mem_filter.mp hh).1).1,
      (hH h (Finset.mem_filter.mp hh).1).2,(Finset.mem_filter.mp hh).2⟩) β
  have hcube : (∑ h ∈ Q, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤ 324*P*E := by
    have hc := cube_frequency_card_le Q (zero_le_one.trans hB) (fun h hh =>
      ⟨(hH h (Finset.mem_filter.mp hh).1).1,
        (hH h (Finset.mem_filter.mp hh).1).2,(Finset.mem_filter.mp hh).2⟩)
    have hs := primary_support_card_le S (zero_le_one.trans hN)
      (fun n hn => ⟨(hS n hn).1,(hS n hn).2.2⟩)
    calc
      _ ≤ ∑ _h ∈ Q, (S.card:ℝ)*E := Finset.sum_le_sum (fun _ _ =>
        cubic_character_row_sq S (fun n hn => (hS n hn).1) β _)
      _ = (Q.card:ℝ)*((S.card:ℝ)*E) := by simp
      _ ≤ (18*B^(1/3:ℝ))*((18*N)*E) := by gcongr
      _ ≤ 324*P*E := by
        dsimp only [P]
        have hp : B^(1/3:ℝ)*N ≤ B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N := by
          exact le_add_of_nonneg_left (add_nonneg (zero_le_one.trans hB) (Real.rpow_nonneg (by positivity) _))
        nlinarith [mul_le_mul_of_nonneg_right hp hE]
  have heq : (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) =
      (∑ h ∈ Q, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) +
      ∑ h ∈ T, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2 := by
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [heq]
  apply (add_le_add hcube hnc).trans
  change 324*P*E+C*(2*B*N)^ε*P*E ≤ (C+324)*(2*B*N)^ε*P*E
  have hh := mul_le_mul_of_nonneg_right hscale (mul_nonneg hP hE)
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeRoughDivisor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nontrivial common prime divisor of a rough prime convolution is
itself large. In the retained small-divisor range only the empty subset
survives; its coefficient remains the original convolution. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrime_prime_divisor_coordinate (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {b p : Eisenstein} (hp : primaryPrime p) (hpd : p ∣ b)
    (hb : b ∈ orderedConvolutionSupport (fullPrimeSupport R W X)) :
    ∃ i, p ∈ fullPrimeSupport R W X i := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨i,_,hi⟩ := (hp.2.dvd_finsetProd_iff f).mp hpd
  have hfi := Fintype.mem_piFinset.mp hf i
  have hfp := fullPrimeSupport_prime R W X i (f i) hfi
  have he : p = f i := primary_associated_eq hp.1 hfp.1
    ((hp.2.dvd_prime_iff_associated hfp.2).mp hi)
  exact ⟨i,he.symm ▸ hfi⟩

lemma fullPrime_nonempty_divisor_large {R D : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) (hrough : ∀ i, D < X i)
    (s : Finset Eisenstein) (hs : ∀ p ∈ s, primaryPrime p) (hsne : s.Nonempty)
    {b : Eisenstein} (hb : b ∈ orderedConvolutionSupport (fullPrimeSupport R W X))
    (hsd : (∏ p ∈ s, p) ∣ b) : D < norm (∏ p ∈ s, p) := by
  obtain ⟨p,hps⟩ := hsne
  have hp := hs p hps
  have hpf : p ∣ ∏ p ∈ s, p := Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hps
  obtain ⟨i,hi⟩ := fullPrime_prime_divisor_coordinate R W X hp (hpf.trans hsd) hb
  have hw := ((fullPrimeSupport_mem_iff W X hX hhi i p).mp hi).2
  have hn : X i ≤ norm p := by
    have hratio : 1 ≤ norm p/X i := le_of_not_gt (fun h => hw (hlo i _ h))
    simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hratio
  have hf : (∏ p ∈ s, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hs p hp).2.ne_zero)
  exact (hrough i).trans_le (hn.trans (norm_le_of_dvd hf hpf))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredHeightMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite frequency blocks retain the proved height mean, with an explicit
row count for the actual ramified and cube decomposition. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma continuous_fullStructuredAngularSum (R : ℝ) (h v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    Continuous (fun t : ℝ => fullStructuredAngularSum R h v e ℓ (t+u) W X) := by
  simp_rw [fullStructuredAngularSum_eq]
  apply continuous_finsetSum
  intro z _
  apply continuous_const.mul
  unfold mellinPhase
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp
      ((continuous_id.add continuous_const).mul continuous_const)).mul continuous_const)

lemma finite_dyadic_integral_sum {α : Type*} (S : Finset α) (f : α → ℝ → ℝ)
    (hf : ∀ a ∈ S, Continuous (f a)) (T : ℝ) :
    ((∫ t in T..2*T, ∑ a ∈ S, f a t) + (∫ t in -2*T..-T, ∑ a ∈ S, f a t))/T =
      ∑ a ∈ S, ((∫ t in T..2*T, f a t)+(∫ t in -2*T..-T, f a t))/T := by
  rw [intervalIntegral.integral_finsetSum (fun a ha => (hf a ha).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun a ha => (hf a ha).intervalIntegrable _ _),
    ← Finset.sum_add_distrib,Finset.sum_div]

lemma fullStructuredHeightMass_le {R D T : ℝ} (H : Finset Eisenstein) (v e : Eisenstein)
    (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hrow : ∀ h ∈ H,
      ((∫ t in T..2*T, ‖fullStructuredAngularSum R h v e ℓ (t+u) W X‖^2) +
       (∫ t in -2*T..-T, ‖fullStructuredAngularSum R h v e ℓ (t+u) W X‖^2))/T ≤ D) :
    ((∫ t in T..2*T, fullStructuredHeightMass R H v e ℓ u W X t)+
     (∫ t in -2*T..-T, fullStructuredHeightMass R H v e ℓ u W X t))/T ≤ H.card*D := by
  unfold fullStructuredHeightMass
  rw [finite_dyadic_integral_sum H
    (fun h t => ‖fullStructuredAngularSum R h v e ℓ (t+u) W X‖^2) (fun h _ =>
    ((continuous_fullStructuredAngularSum R h v e ℓ u W X).norm).pow 2) T]
  calc
    _ ≤ ∑ _h ∈ H, D := Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeSliceEnergySum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the shortened coefficient energies over common divisors without
paying for the ambient prime set. Each n-fold prime product has at most
2^n subsets of prime divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrime_divisor_energy_eq_slice {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {f : Eisenstein} (hf : primary f)
    (e : Eisenstein) :
    (∑ b ∈ (fullSquarefreePrimeSupport R W X e).filter (fun b => f ∣ b),
      ‖fullPrimeCoefficient R W X b‖^2) =
    ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
  have hh := fullPrime_divisor_sum_eq_slice W X hX hlo hhi hf e
    (fun b => (‖fullPrimeCoefficient R W X b‖^2 : ℝ) : Eisenstein → ℂ)
  exact_mod_cast hh

lemma fullPrime_summed_slice_energy {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) (e : Eisenstein)
    (U : Finset Eisenstein) (hU : ∀ p ∈ U, primaryPrime p) :
    (∑ s ∈ U.powerset, ∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
      ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2) ≤
    (2^Fintype.card ι:ℝ)*∑ b ∈ fullSquarefreePrimeSupport R W X e,
      ‖fullPrimeCoefficient R W X b‖^2 := by
  have heq (s : Finset Eisenstein) (hs : s ∈ U.powerset) :=
    fullPrime_divisor_energy_eq_slice W X hX hlo hhi
      (primary_finset_prod s (fun p : Eisenstein => p)
        (fun p hp => (hU p (Finset.mem_powerset.mp hs hp)).1)) e
  calc
    _ = ∑ s ∈ U.powerset, ∑ b ∈ (fullSquarefreePrimeSupport R W X e).filter
        (fun b => (∏ p ∈ s, p) ∣ b), ‖fullPrimeCoefficient R W X b‖^2 :=
      Finset.sum_congr rfl (fun s hs => (heq s hs).symm)
    _ = ∑ b ∈ fullSquarefreePrimeSupport R W X e,
        ((U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ b)).card:ℝ)*
          ‖fullPrimeCoefficient R W X b‖^2 := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ ∑ b ∈ fullSquarefreePrimeSupport R W X e,
        (2^Fintype.card ι:ℝ)*‖fullPrimeCoefficient R W X b‖^2 := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast fullPrime_divisor_subsets_card R W X e U hU hb
    _ = _ := (Finset.mul_sum _ _ _).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredHeightContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and boundedness of the actual finite height mass. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullStructuredHeightMass_nonneg (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein)
    (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (t : ℝ) :
    0 ≤ fullStructuredHeightMass R H v e ℓ u W X t :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma continuous_fullStructuredHeightMass (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein)
    (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    Continuous (fullStructuredHeightMass R H v e ℓ u W X) := by
  exact continuous_finsetSum H (fun h _ =>
    ((continuous_fullStructuredAngularSum R h v e ℓ u W X).norm).pow 2)

lemma fullStructuredHeightMass_bounded (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein)
    (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, fullStructuredHeightMass R H v e ℓ u W X t ≤ B := by
  let A := fun h : Eisenstein => ∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R W X),
    ‖fullStructuredCoefficient R h v e W X z*theta ℓ z‖
  refine ⟨∑ h ∈ H, (A h)^2,Finset.sum_nonneg (fun _ _ => sq_nonneg _),?_⟩
  intro t
  apply Finset.sum_le_sum
  intro h _
  apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
  rw [fullStructuredAngularSum_eq]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro z _
  rw [norm_mul,mellinPhase_norm,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightMassPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact integration of the finite low/large-core split. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integrable_weighted_height_mass {f : ℝ → ℝ} (hf : Integrable f)
    (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    Integrable (fun t => f t*fullStructuredHeightMass R H v e ℓ u W X t) := by
  obtain ⟨B,_hB,hB⟩ := fullStructuredHeightMass_bounded R H v e ℓ u W X
  exact hf.mul_bdd (continuous_fullStructuredHeightMass R H v e ℓ u W X).aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (fullStructuredHeightMass_nonneg R H v e ℓ u W X t)]
      exact hB t))

lemma weighted_height_mass_partition {f : ℝ → ℝ} (hf : Integrable f)
    (R : ℝ) (H : Finset Eisenstein) (P : Eisenstein → Prop)
    (v e : Eisenstein) (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    (∫ t : ℝ, f t*fullStructuredHeightMass R H v e ℓ u W X t) =
      (∫ t : ℝ, f t*fullStructuredHeightMass R (H.filter P) v e ℓ u W X t)+
      (∫ t : ℝ, f t*fullStructuredHeightMass R (H.filter (fun h => ¬P h)) v e ℓ u W X t) := by
  have he (t : ℝ) : fullStructuredHeightMass R H v e ℓ u W X t =
      fullStructuredHeightMass R (H.filter P) v e ℓ u W X t+
      fullStructuredHeightMass R (H.filter (fun h => ¬P h)) v e ℓ u W X t := by
    exact (Finset.sum_filter_add_sum_filter_not H P _).symm
  simp_rw [he,mul_add]
  exact integral_add (integrable_weighted_height_mass hf R (H.filter P) v e ℓ u W X)
    (integrable_weighted_height_mass hf R (H.filter (fun h => ¬P h)) v e ℓ u W X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArithmeticMellinKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the Fourier-transform frequency to the arithmetic height in
N(n)^(it). The fixed factor 2π stays in the actual kernel. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open Set MeasureTheory
namespace CubicFirstMoment

lemma arithmeticMellinCoefficient_continuous (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) :
    Continuous (arithmeticMellinCoefficient M hM V hV hV' ρ) :=
  (𝓕 (normDenominatorLogSchwartz M hM V hV hV' ρ)).continuous.comp
    (continuous_id.div_const _)

lemma arithmeticMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) :
    Integrable (arithmeticMellinCoefficient M hM V hV hV' ρ) :=
  (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).comp_div
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)

theorem arithmeticMellinCoefficient_quadratic_decay (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ t : ℝ,
      (1+ρ)^q*‖t‖^2*‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖ ≤ D := by
  obtain ⟨C,hC,hb⟩ := normDenominatorMellinCoefficient_pointwise_rapidDecay M hM V hV hV' q 2
  have hc : 2*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  refine ⟨C*(2*Real.pi)^2,mul_pos hC (sq_pos_of_ne_zero hc),?_⟩
  intro ρ hρ t
  have h := mul_le_mul_of_nonneg_right (hb ρ hρ (t/(2*Real.pi))) (sq_nonneg (2*Real.pi))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [arithmeticMellinCoefficient,Real.norm_eq_abs,sq_abs,div_pow]
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflection of the actual Mellin kernel is obtained by conjugating its
original radial weight. This handles the reverse character row without
adding an analytic hypothesis. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open MeasureTheory
namespace CubicFirstMoment

lemma star_fourierChar (x : ℝ) :
    star (Real.fourierChar x : ℂ) = (Real.fourierChar (-x) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

lemma traceFourier_conj (f : ℂ → ℂ) (w : ℂ) :
    traceFourier (fun z => star (f z)) w = star (traceFourier f (-w)) := by
  unfold traceFourier
  calc
    _ = ∫ z : ℂ, star ((Real.fourierChar (-tracePair z (-w)) : ℂ)*f z) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [star_mul,star_fourierChar]
      simp only [tracePair,mul_neg,Complex.neg_re,neg_neg]
      ring
    _ = _ := integral_conj

lemma normProfileFourier_conj (V : ℝ → ℂ) (w : ℂ) :
    normProfileFourier (fun x => star (V x)) w = star (normProfileFourier V w) := by
  unfold normProfileFourier
  rw [traceFourier_conj]
  have he := normProfileFourier_eq_of_normSq_eq V
    (show Complex.normSq (-w) = Complex.normSq w by simp)
  change (2 / Real.sqrt 3 : ℝ) • star (traceFourier (fun z => V (Complex.normSq z)) (-w)) = _
  calc
    _ = star ((2 / Real.sqrt 3 : ℝ) •
        traceFourier (fun z => V (Complex.normSq z)) (-w)) := by
      simp only [star_smul,star_trivial]
    _ = _ := congrArg star he

lemma normDenominatorLogSchwartz_conj (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport (fun x => star (V x)))
    (hVc' : ContDiff ℝ ∞ (fun x => star (V x))) (ρ u : ℝ) :
    normDenominatorLogSchwartz M hM (fun x => star (V x)) hVc hVc' ρ u =
      star (normDenominatorLogSchwartz M hM V hV hV' ρ u) := by
  simp only [normDenominatorLogSchwartz_apply,wideGramLogKernel,
    normProfileFourier_conj,star_mul,star_smul,star_trivial]
  rw [show star (Real.exp (u/2) : ℂ) = (Real.exp (u/2) : ℂ) from RCLike.conj_ofReal _]
  ring

lemma real_fourier_conj (f : ℝ → ℂ) (t : ℝ) :
    𝓕 (fun x => star (f x)) t = star (𝓕 f (-t)) := by
  rw [Real.fourier_eq,Real.fourier_eq]
  calc
    _ = ∫ x : ℝ, star ((Real.fourierChar (-inner ℝ x (-t)) : ℂ)*f x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [Circle.smul_def,smul_eq_mul,star_mul,star_fourierChar,inner_neg_right,
        neg_neg]
      ring
    _ = _ := integral_conj

lemma arithmeticMellinCoefficient_conj (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport (fun x => star (V x)))
    (hVc' : ContDiff ℝ ∞ (fun x => star (V x))) (ρ t : ℝ) :
    arithmeticMellinCoefficient M hM (fun x => star (V x)) hVc hVc' ρ t =
      star (arithmeticMellinCoefficient M hM V hV hV' ρ (-t)) := by
  unfold arithmeticMellinCoefficient normDenominatorMellinCoefficient
  rw [SchwartzMap.fourier_coe,SchwartzMap.fourier_coe]
  have he : (normDenominatorLogSchwartz M hM (fun x => star (V x)) hVc hVc' ρ : ℝ → ℂ) =
      fun x => star (normDenominatorLogSchwartz M hM V hV hV' ρ x) := by
    funext x
    exact normDenominatorLogSchwartz_conj M hM V hV hV' hVc hVc' ρ x
  rw [he,real_fourier_conj,neg_div]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSignedIntegration
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact changes of variable for the two signs of the Poisson rows.
The Jacobian 2π is retained. -/
noncomputable section
open scoped ContDiff
open MeasureTheory Filter
namespace CubicFirstMoment

lemma integral_scaled_mass (f g : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, f t*g (c*t)) = c⁻¹*(∫ t : ℝ, f (t/c)*g t) := by
  have he := Measure.integral_comp_mul_left (fun t : ℝ => f (t/c)*g t) c
  simp only [abs_inv,abs_of_pos hc,smul_eq_mul,mul_div_cancel_left₀ _ hc.ne'] at he
  exact he

lemma integral_scaled_signed_mass (f g : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    (hplus : Integrable (fun t : ℝ => f t*g (c*t)))
    (hminus : Integrable (fun t : ℝ => f t*g (-(c*t)))) :
    (∫ t : ℝ, f t*((g (c*t)+g (-(c*t)))/2)) =
      ((∫ t : ℝ, f (t/c)*g t)+(∫ t : ℝ, f (-(t/c))*g t))/(2*c) := by
  have hminus' : (∫ t : ℝ, f t*g (-(c*t))) =
      c⁻¹*(∫ t : ℝ, f (-(t/c))*g t) := by
    have hn := integral_neg_eq_self (fun t : ℝ => f t*g (-(c*t)))
    simp only [mul_neg,neg_neg] at hn
    rw [← hn]
    exact integral_scaled_mass (fun t => f (-t)) g hc
  have hs (t : ℝ) : f t*((g (c*t)+g (-(c*t)))/2) =
      (f t*g (c*t))/2+(f t*g (-(c*t)))/2 := by ring
  simp_rw [hs]
  rw [integral_add (hplus.div_const 2) (hminus.div_const 2),
    integral_div,integral_div,integral_scaled_mass f g hc,hminus']
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integrable_scaled_height_mass {f : ℝ → ℝ} (hf : Integrable f)
    (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (c : ℝ) :
    Integrable (fun t : ℝ => f t*fullStructuredHeightMass R H v e ℓ u W X (c*t)) := by
  obtain ⟨B,_hB,hB⟩ := fullStructuredHeightMass_bounded R H v e ℓ u W X
  apply hf.mul_bdd (c := B)
    ((continuous_fullStructuredHeightMass R H v e ℓ u W X).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun t => by
    change ‖fullStructuredHeightMass R H v e ℓ u W X (c*t)‖ ≤ B
    rw [Real.norm_eq_abs,abs_of_nonneg (fullStructuredHeightMass_nonneg R H v e ℓ u W X _)]
    exact hB (c*t))

lemma normMellin_signed_height_integral (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (ρ : ℝ) :
    (∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖*
      ((fullStructuredHeightMass R H v e ℓ u W X (2*Real.pi*t)+
        fullStructuredHeightMass R H v e ℓ u W X (-(2*Real.pi*t)))/2)) =
    ((∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*
        fullStructuredHeightMass R H v e ℓ u W X t)+
      (∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ (-t)‖*
        fullStructuredHeightMass R H v e ℓ u W X t))/(4*Real.pi) := by
  have hf := (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).norm
  have hp := integrable_scaled_height_mass hf R H v e ℓ u W X (2*Real.pi)
  have hn := integrable_scaled_height_mass hf R H v e ℓ u W X (-(2*Real.pi))
  simp only [neg_mul] at hn
  have he := integral_scaled_signed_mass
    (fun t => ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖)
    (fullStructuredHeightMass R H v e ℓ u W X) (by positivity : 0 < 2*Real.pi) hp hn
  simpa only [arithmeticMellinCoefficient,neg_div,show (2:ℝ)*(2*Real.pi) = 4*Real.pi by ring] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeCutoffMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full finite noncube cutoff, with all arithmetic decompositions,
small conductors and exceptional conductor regions included. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma cube_cutoff_le_length {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hBL : B ≤ L^2) :
    B^(1/3:ℝ) ≤ L := by
  have hcube : B ≤ L^3 := hBL.trans (pow_le_pow_right₀ hL (by norm_num))
  have hr := Real.rpow_le_rpow hB hcube (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (L^3)^(1/3:ℝ) = L := by
    rw [← Real.rpow_natCast L 3,← Real.rpow_mul (zero_le_one.trans hL)]
    norm_num
  rwa [he] at hr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArithmeticMellinMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial integral moments after the exact 2π rescaling. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace CubicFirstMoment

lemma arithmetic_mellin_moment_scale (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) (k : ℕ) (t : ℝ) :
    ‖t‖^k*‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖ =
      (2*Real.pi)^k*(‖t/(2*Real.pi)‖^k*
        ‖normDenominatorMellinCoefficient M hM V hV hV' ρ (t/(2*Real.pi))‖) := by
  have hc : 2*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  simp only [arithmeticMellinCoefficient,norm_div,Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi),div_pow]
  field_simp

theorem arithmeticMellinCoefficient_moment_decay (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖t‖^k*‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖) ≤ C := by
  obtain ⟨C,hC,hb⟩ := normDenominatorMellinCoefficient_moment_decay M hM V hV hV' q k
  refine ⟨(2*Real.pi)^(k+1)*C,by positivity,?_⟩
  intro ρ hρ
  simp_rw [arithmetic_mellin_moment_scale]
  have he := Measure.integral_comp_div
    (fun t : ℝ => ‖t‖^k*‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖) (2*Real.pi)
  rw [integral_const_mul,he,abs_of_pos (by positivity : 0 < 2*Real.pi),smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left (hb ρ hρ) (pow_nonneg (by positivity : 0 ≤ 2*Real.pi) (k+1))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [pow_succ]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogEnergyMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary height mean with the actual logarithmic coefficient
cost retained, for the low-conductor part of the Poisson remainder. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem log_energy_dyadic_mean {C R : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (K D : ℝ) (a : ℕ), 0 ≤ K ∧ 1 ≤ D ∧
      ∀ (r : γ) (X : ι → ℝ), 1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ∀ (h v e : Eisenstein) (ℓ : ℤ) (u T : ℝ), 0 < T →
      ((∫ t in T..2*T, ‖fullStructuredAngularSum R h v e ℓ (t+u) (W r) X‖^2)+
       (∫ t in -2*T..-T, ‖fullStructuredAngularSum R h v e ℓ (t+u) (W r) X‖^2))/T ≤
        K*(1+D*L r/T)*L r*(1+Real.log (L r))^a := by
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  let M : ℝ := ((2*Fintype.card ι)^(Fintype.card ι):ℕ)
  refine ⟨2*C*M*E,2*R^(Fintype.card ι),a,by dsimp [M]; positivity,?_,?_⟩
  · have hh := one_le_pow₀ hR (n := Fintype.card ι)
    linarith
  intro r X hL hX hprod h v e ℓ u T hT
  have hY : 1 ≤ R^(Fintype.card ι)*L r := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) hL
  have hceil : (⌈R^(Fintype.card ι)*L r⌉₊:ℝ) ≤ 2*R^(Fintype.card ι)*L r := by
    linarith [Nat.ceil_lt_add_one (zero_le_one.trans hY)]
  have hb := fullStructured_dyadicMeanSquare hMV hC (zero_le_one.trans hR)
    (W r) X hX (hlo r) (hhi r) ⌈R^(Fintype.card ι)*L r⌉₊
    (by rw [hprod]; exact Nat.le_ceil _) h v e ℓ u hT
  have he := henergy r X hL hX hprod
  have hf : 1+(⌈R^(Fintype.card ι)*L r⌉₊:ℝ)/T ≤
      1+2*R^(Fintype.card ι)*L r/T :=
    add_le_add le_rfl (div_le_div_of_nonneg_right hceil hT.le)
  have hcoef : 0 ≤ 2*C*(1+(⌈R^(Fintype.card ι)*L r⌉₊:ℝ)/T)*M :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC)
      (by positivity)) (Nat.cast_nonneg _)
  apply (hb.trans (mul_le_mul_of_nonneg_left he hcoef)).trans
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC))
      (Nat.cast_nonneg ((2*Fintype.card ι)^(Fintype.card ι))))
    (mul_nonneg (mul_nonneg hE (zero_le_one.trans hL))
      (pow_nonneg (show 0 ≤ 1+Real.log (L r) by linarith [Real.log_nonneg hL]) a))
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [M]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreHeightMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite small-core frequency set at arbitrary height.
This mean-value bound complements the low-height Kummer prime estimate. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem low_core_height_mean {C R : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (a : ℕ) :
    ∃ (K D : ℝ) (b : ℕ), 0 ≤ K ∧ 1 ≤ D ∧
      ∀ (r : γ) (X : ι → ℝ) (J : ℝ) (H : Finset Eisenstein),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → 0 ≤ J →
      H ⊆ lowNoncubeSupport ((Real.log (L r))^a) J →
      ∀ (v e : Eisenstein) (ℓ : ℤ) (u T : ℝ), 0 < T →
      ((∫ t in T..2*T, fullStructuredHeightMass R H v e ℓ u (W r) X t)+
       (∫ t in -2*T..-T, fullStructuredHeightMass R H v e ℓ u (W r) X t))/T ≤
        K*J*(1+D*L r/T)*L r*(1+Real.log (L r))^b := by
  obtain ⟨K,D,b,hK,hD,hbound⟩ := log_energy_dyadic_mean hMV hC hR hW hlo hhi
  refine ⟨324*K,D,a+b,by positivity,hD,?_⟩
  intro r X J H hL hX hprod hJ hH v e ℓ u T hT
  have hz : 0 ≤ Real.log (L r) := Real.log_nonneg hL
  have hcard : (H.card:ℝ) ≤ 324*(1+Real.log (L r))^a*J := by
    calc
      _ ≤ ((lowNoncubeSupport ((Real.log (L r))^a) J).card:ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hH)
      _ ≤ 324*(Real.log (L r))^a*J := lowNoncubeSupport_card (pow_nonneg hz _) hJ
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hz (by linarith) _) (by norm_num)) hJ
  have hm := fullStructuredHeightMass_le H v e ℓ u (W r) X
    (fun h _ => hbound r X hL hX hprod h v e ℓ u T hT)
  apply hm.trans
  have hfactor : 0 ≤ K*(1+D*L r/T)*L r*(1+Real.log (L r))^b := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg hK (by positivity)
      · exact zero_le_one.trans hL
    · exact pow_nonneg (by linarith) _
  apply (mul_le_mul_of_nonneg_right hcard hfactor).trans_eq
  rw [pow_add]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreHeightSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Above a fixed logarithmic height, the actual ordinary mean supplies
every logarithmic saving on the small-core frequency set. -/
noncomputable section
open Filter MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma logarithmic_height_factor {L z D T : ℝ} (hL : 0 ≤ L) (hz : 1 ≤ z)
    (hD : 0 ≤ D) (b k : ℕ) (hlog : z^(b+k) ≤ L) (hT : z^(b+k) ≤ T) :
    (1+D*L/T)*L*z^b ≤ (1+D)*L^2/z^k := by
  have hz0 : 0 < z := zero_lt_one.trans_le hz
  have hT0 : 0 < T := (pow_pos hz0 _).trans_le hT
  apply (le_div_iff₀ (pow_pos hz0 k)).mpr
  calc
    _ = L*z^(b+k)+D*L^2*(z^(b+k)/T) := by rw [pow_add]; ring
    _ ≤ L*L+D*L^2*1 := add_le_add
      (mul_le_mul_of_nonneg_left hlog hL)
      (mul_le_mul_of_nonneg_left ((div_le_one hT0).mpr hT) (mul_nonneg hD (sq_nonneg _)))
    _ = _ := by ring

theorem low_core_height_log_saving {C R : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (a k : ℕ) :
    ∃ (K T₀ : ℝ) (A : ℕ), 0 ≤ K ∧
      ∀ (r : γ) (X : ι → ℝ) (J : ℝ) (H : Finset Eisenstein),
      1 ≤ L r → T₀ ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → 0 ≤ J →
      H ⊆ lowNoncubeSupport ((Real.log (L r))^a) J →
      ∀ (v e : Eisenstein) (ℓ : ℤ) (u T : ℝ), (1+Real.log (L r))^A ≤ T →
      ((∫ t in T..2*T, fullStructuredHeightMass R H v e ℓ u (W r) X t)+
       (∫ t in -2*T..-T, fullStructuredHeightMass R H v e ℓ u (W r) X t))/T ≤
        K*J*(L r)^2/(1+Real.log (L r))^k := by
  obtain ⟨K,D,b,hK,hD,hmean⟩ := low_core_height_mean hMV hC hR hW hlo hhi a
  have hev := exclusion_log_absorption (c := 1) (d := 0) (ε := 1)
    (by norm_num) (by norm_num) (C := 1) (by norm_num) (b+k) 0
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp hev
  refine ⟨K*(1+D),T₀,b+k,mul_nonneg hK (by linarith),?_⟩
  intro r X J H hL hTL hX hprod hJ hH v e ℓ u T hT
  have hz : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hlog := hT₀ (L r) hTL (L r) 1 (by norm_num) (by simp) (by simp)
  simp only [Real.one_rpow,one_mul,pow_zero,div_one] at hlog
  have hTpos : 0 < T := (pow_pos (zero_lt_one.trans_le hz) _).trans_le hT
  apply (hmean r X J H hL hX hprod hJ hH v e ℓ u T hTpos).trans
  have hm := mul_le_mul_of_nonneg_left
    (logarithmic_height_factor (zero_le_one.trans hL) hz (zero_le_one.trans hD) b k hlog hT)
    (mul_nonneg hK hJ)
  first | (convert hm using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hm.trans (le_of_eq (by ring)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicMellinTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem weighted_positive_mellin_tail {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg0 : ∀ t, 0 ≤ g t) (hfg : Integrable (fun t => f t*g t))
    {T B C : ℝ} (hT : 0 < T) (_hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmean : ∀ S : ℝ, T ≤ S → (∫ t in S..2*S, g t) ≤ B*S)
    (hdecay : ∀ t : ℝ, T ≤ t → f t ≤ C/t^2) :
    (∫ t in Ici T, f t*g t) ≤ 2*B*C/T := by
  have hdyad (n : ℕ) : (∫ t in mellinHeightDyad T n, f t*g t) ≤
      (B*C/T)*((1/2:ℝ)^n) := by
    let S := (2:ℝ)^n*T
    have hS : 0 < S := mul_pos (pow_pos (by norm_num) _) hT
    have hTS : T ≤ S := le_mul_of_one_le_left hT.le (one_le_pow₀ (by norm_num))
    have hS2 : S ≤ 2*S := by linarith
    have he : (2:ℝ)^(n+1)*T = 2*S := by dsimp [S]; rw [pow_succ]; ring
    change (∫ t in Ico S ((2:ℝ)^(n+1)*T), f t*g t) ≤ _
    rw [he,integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le hS2]
    have hi := intervalIntegral.integral_mono_on (μ := volume) hS2
      ((hf.mul hg).intervalIntegrable _ _)
      ((continuous_const.mul hg).intervalIntegrable S (2*S))
      (show ∀ t ∈ Icc S (2*S), f t*g t ≤ (C/S^2)*g t from fun t ht => by
        apply mul_le_mul_of_nonneg_right _ (hg0 t)
        apply (hdecay t (hTS.trans ht.1)).trans
        exact div_le_div_of_nonneg_left hC (sq_pos_of_pos hS)
          (pow_le_pow_left₀ hS.le ht.1 2))
    calc
      _ ≤ ∫ t in S..2*S, (C/S^2)*g t := hi
      _ = (C/S^2)*(∫ t in S..2*S, g t) := intervalIntegral.integral_const_mul _ _
      _ ≤ (C/S^2)*(B*S) := mul_le_mul_of_nonneg_left (hmean S hTS) (by positivity)
      _ = (B*C/T)*((1/2:ℝ)^n) := by
        dsimp [S]
        rw [div_pow,one_pow]
        field_simp
  have hsum := hasSum_integral_iUnion (μ := volume)
    (s := mellinHeightDyad T) (f := fun t => f t*g t)
    (fun n : ℕ => (measurableSet_Ico : MeasurableSet (mellinHeightDyad T n))) (mellinHeightDyad_disjoint hT)
    hfg.integrableOn
  rw [mellinHeightDyad_union hT] at hsum
  calc
    _ = ∑' n : ℕ, ∫ t in mellinHeightDyad T n, f t*g t := hsum.tsum_eq.symm
    _ ≤ ∑' n : ℕ, (B*C/T)*((1/2:ℝ)^n) :=
      Summable.tsum_le_tsum hdyad hsum.summable (summable_geometric_two.mul_left _)
    _ = (B*C/T)*2 := (hasSum_geometric_two.mul_left _).tsum_eq
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SignedMellinTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
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

theorem weighted_signed_mellin_tail {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg0 : ∀ t, 0 ≤ g t) (hfg : Integrable (fun t => f t*g t))
    {T B C : ℝ} (hT : 0 < T) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmean : ∀ S : ℝ, T ≤ S →
      ((∫ t in S..2*S, g t)+(∫ t in -2*S..-S, g t))/S ≤ B)
    (hdecay : ∀ t : ℝ, T ≤ |t| → f t ≤ C/t^2) :
    ((∫ t in Ici T, f t*g t)+(∫ t in Ici T, f (-t)*g (-t))) ≤ 4*B*C/T := by
  have hp := weighted_positive_mellin_tail hf hg hg0 hfg hT hB hC
    (signed_height_mean_positive hg hg0 hT hmean) (fun t ht =>
      hdecay t (by rw [abs_of_pos (hT.trans_le ht)]; exact ht))
  have hi : Integrable (fun t : ℝ => f (-t)*g (-t)) :=
    (MeasurePreserving.integrable_comp_emb (Measure.measurePreserving_neg volume)
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hfg
  have hn := weighted_positive_mellin_tail (hf.comp continuous_neg) (hg.comp continuous_neg)
    (fun t => hg0 (-t)) hi hT hB hC (signed_height_mean_negative hg hg0 hT hmean)
    (fun t ht => by
      have hh := hdecay (-t) (by rw [abs_neg,abs_of_pos (hT.trans_le ht)]; exact ht)
      simpa only [Function.comp_apply,neg_sq] using hh)
  calc
    _ ≤ 2*B*C/T+2*B*C/T := add_le_add hp hn
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreArithmeticTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The low-core tail in the arithmetic height appearing in the separated
Poisson kernel, including the precise 2π change of variables.
Only the published ordinary Montgomery--Vaughan input is used here. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem low_core_arithmetic_mellin_tail {C R : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0)
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (a k q : ℕ) :
    ∃ (K T₀ : ℝ) (A : ℕ), 0 ≤ K ∧
      ∀ (r : γ) (X : ι → ℝ) (J : ℝ) (H : Finset Eisenstein),
      1 ≤ L r → T₀ ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → 0 ≤ J →
      H ⊆ lowNoncubeSupport ((Real.log (L r))^a) J →
      ∀ (v e : Eisenstein) (ℓ : ℤ) (u T ρ : ℝ), (1+Real.log (L r))^A ≤ T → 0 ≤ ρ →
      let F := arithmeticMellinCoefficient M hM V hV hV' ρ
      let G := fullStructuredHeightMass R H v e ℓ u (W r) X
      (1+ρ)^q*((∫ t in Ici T, ‖F t‖*G t)+(∫ t in Ici T, ‖F (-t)‖*G (-t))) ≤
        K*J*(L r)^2/((1+Real.log (L r))^k*T) := by
  obtain ⟨K,T₀,A,hK,hmean⟩ := low_core_height_log_saving hMV hC hR hW hlo hhi a k
  obtain ⟨D,hD,hdecay⟩ := arithmeticMellinCoefficient_quadratic_decay M hM V hV hV' q
  refine ⟨4*K*D,T₀,A,by positivity,?_⟩
  intro r X J H hL hTL hX hprod hJ hH v e ℓ u T ρ hT hρ
  dsimp only
  let G := fullStructuredHeightMass R H v e ℓ u (W r) X
  let F := arithmeticMellinCoefficient M hM V hV hV' ρ
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hTp : 0 < T := (pow_pos hz A).trans_le hT
  have hg := continuous_fullStructuredHeightMass R H v e ℓ u (W r) X
  have hg0 := fullStructuredHeightMass_nonneg R H v e ℓ u (W r) X
  obtain ⟨B,_hB,hB⟩ := fullStructuredHeightMass_bounded R H v e ℓ u (W r) X
  have hF : Continuous F := arithmeticMellinCoefficient_continuous M hM V hV hV' ρ
  have hfg : Integrable (fun t => ((1+ρ)^q*‖F t‖)*G t) :=
    ((arithmeticMellinCoefficient_integrable M hM V hV hV' ρ).norm.const_mul _).mul_bdd
      hg.aestronglyMeasurable (Eventually.of_forall (fun t => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hg0 t)]
        exact hB t))
  have hb : 0 ≤ K*J*(L r)^2/(1+Real.log (L r))^k := by positivity
  have ht := weighted_signed_mellin_tail (continuous_const.mul hF.norm) hg hg0 hfg
    hTp hb hD.le (fun S hS => hmean r X J H hL hTL hX hprod hJ hH v e ℓ u S (hT.trans hS))
    (fun t ht => by
      have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
      apply (le_div_iff₀ (sq_pos_of_ne_zero ht0)).mpr
      simpa only [Pi.mul_apply,F,Real.norm_eq_abs,sq_abs,mul_assoc,mul_left_comm,mul_comm]
        using hdecay ρ hρ t)
  simp only [Pi.mul_apply,mul_assoc,integral_const_mul] at ht
  dsimp only [F] at ht
  first | (convert ht using 1 <;> ring) | exact (le_of_eq (by ring)).trans (ht.trans (le_of_eq (by ring)))

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

theorem integral_local_and_signed_tail {f g : ℝ → ℝ} (hfi : Integrable f)
    (hf0 : ∀ t, 0 ≤ f t) (hfg : Integrable (fun t => f t*g t))
    {T B E : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hlocal : ∀ t : ℝ, |t| < T → g t ≤ B)
    (htail : (∫ t in Ici T, f t*g t)+(∫ t in Ici T, f (-t)*g (-t)) ≤ E) :
    (∫ t : ℝ, f t*g t) ≤ B*(∫ t : ℝ, f t)+E := by
  have hi : (∫ t in Ioo (-T) T, f t*g t) ≤ B*(∫ t : ℝ, f t) := by
    calc
      _ ≤ ∫ t in Ioo (-T) T, B*f t := by
        apply setIntegral_mono_on hfg.integrableOn (hfi.const_mul B).integrableOn measurableSet_Ioo
        intro t ht
        calc
          _ ≤ f t*B := mul_le_mul_of_nonneg_left (hlocal t (abs_lt.mpr ht)) (hf0 t)
          _ = _ := mul_comm _ _
      _ = B*(∫ t in Ioo (-T) T, f t) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hfi (Eventually.of_forall hf0)) hB
  rw [integral_height_split hfg hT]
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreMellinIntegral
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full low-core Mellin integral: Kummer cancellation near zero, the
ordinary signed height mean in the tails. Both estimates are applied to
the actual finite structured sums. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma log_height_translate {z t u : ℝ} (hz : 2 ≤ z) (A U : ℕ)
    (ht : |t| ≤ z^A) (hu : |u| ≤ z^U) : |t+u| ≤ z^(max A U+1) := by
  have hz1 : 1 ≤ z := by linarith
  have ha := pow_le_pow_right₀ hz1 (le_max_left A U)
  have hu' := pow_le_pow_right₀ hz1 (le_max_right A U)
  calc
    _ ≤ |t|+|u| := abs_add_le _ _
    _ ≤ z^A+z^U := add_le_add ht hu
    _ ≤ 2*z^(max A U) := by linarith
    _ ≤ z*z^(max A U) := mul_le_mul_of_nonneg_right hz (pow_nonneg (by linarith) _)
    _ = _ := by rw [pow_succ]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreMonotone
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotonicity permits the harmless enlargement of a zero logarithmic
core exponent without changing the actual frequency set being estimated. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma lowNoncubeSupport_mono {V₁ V₂ J₁ J₂ : ℝ} (hV : V₁ ≤ V₂) (hJ : J₁ ≤ J₂) :
    lowNoncubeSupport V₁ J₁ ⊆ lowNoncubeSupport V₂ J₂ := by
  intro h hh
  obtain ⟨hi,hn⟩ := Finset.mem_filter.mp hh
  obtain ⟨⟨v,j⟩,hvj,he⟩ := Finset.mem_image.mp hi
  have hv := mem_nonzeroNormBall.mp (Finset.mem_product.mp hvj).1
  have hj := mem_nonzeroNormBall.mp (Finset.mem_product.mp hvj).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(v,j),Finset.mem_product.mpr ⟨?_,?_⟩,he⟩,hn⟩
  · exact mem_nonzeroNormBall.mpr ⟨hv.1.trans hV,hv.2⟩
  · exact mem_nonzeroNormBall.mpr ⟨hj.1.trans hJ,hj.2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeightDivisorBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual angular common-divisor mass: exact empty row, rough-divisor
split, and shortened outer-sieve bound. The constants do not depend on the
angular index, since its coefficient factors have modulus one. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

lemma angular_fullPrimeDivisorMellinMass_one (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (H : Finset Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    angular_fullPrimeDivisorMellinMass ℓ R W X e H u N 1 t =
      (fullStructuredHeightMass R H 1 e ℓ u W X (2*Real.pi*t)+
        fullStructuredHeightMass R H 1 e ℓ u W X (-(2*Real.pi*t)))/2 := by
  simp only [angular_fullPrimeDivisorMellinMass,one_dvd,Finset.filter_true,
    fullStructuredHeightMass,angular_fullStructuredPrimeRow_norm ℓ R W X _ e u t hN,
    angular_fullStructuredPrimeRow_reverse_norm ℓ R W X _ e u t hN,
    add_comm (2*Real.pi*t) u,sub_eq_add_neg,add_comm (-(2*Real.pi*t)) u]


lemma angular_fullPrimeDivisorMellinMass_small {R D : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) (hrough : ∀ i, D < X i)
    (s : Finset Eisenstein) (hs : ∀ p ∈ s, primaryPrime p) (hsne : s.Nonempty)
    (hsmall : norm (∏ p ∈ s, p) ≤ D) (e : Eisenstein) (H : Finset Eisenstein)
    (u N t : ℝ) :
    angular_fullPrimeDivisorMellinMass ℓ R W X e H u N (∏ p ∈ s, p) t = 0 := by
  have hempty : (fullSquarefreePrimeSupport R W X e).filter
      (fun a => (∏ p ∈ s, p) ∣ a) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨ha,hsd⟩ := Finset.mem_filter.mp ha
    have hh := fullPrime_nonempty_divisor_large W X hX hlo hhi hrough s hs hsne
      (Finset.mem_filter.mp ha).1 hsd
    exact (not_lt_of_ge hsmall) hh
  simp only [angular_fullPrimeDivisorMellinMass,hempty,Finset.sum_empty,norm_zero,zero_pow
    (by decide : (2:ℕ) ≠ 0),Finset.sum_const_zero,zero_add,zero_div]

lemma angular_fullPrime_coprime_mass_split {R D : ℝ} (hD : 1 ≤ D)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) (H U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    coprimeMellinMass (fullSquarefreePrimeSupport R W X e) H U
      (fun a => star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a)))
      (fun a => star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a)))
      (fun a => norm a/N) t =
    (fullStructuredHeightMass R H 1 e ℓ u W X (2*Real.pi*t)+
      fullStructuredHeightMass R H 1 e ℓ u W X (-(2*Real.pi*t)))/2+
    ∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
      angular_fullPrimeDivisorMellinMass ℓ R W X e H u N (∏ p ∈ s, p) t := by
  let F := fun s : Finset Eisenstein =>
    angular_fullPrimeDivisorMellinMass ℓ R W X e H u N (∏ p ∈ s, p) t
  have hsmall : (∑ s ∈ U.powerset.filter (fun s => norm (∏ p ∈ s, p) ≤ D), F s) = F ∅ := by
    apply Finset.sum_eq_single ∅
    · intro s hs hsne
      obtain ⟨hsU,hsmall⟩ := Finset.mem_filter.mp hs
      exact angular_fullPrimeDivisorMellinMass_small ℓ W X hX hlo hhi hrough s
        (fun p hp => hU p (Finset.mem_powerset.mp hsU hp))
        (Finset.nonempty_iff_ne_empty.mpr hsne) hsmall e H u N t
    · intro hn
      exact (hn (by simpa only [Finset.mem_filter,Finset.mem_powerset,Finset.empty_subset,
        true_and,Finset.prod_empty] using (show norm (1:Eisenstein) ≤ D by simpa [norm] using hD))).elim
  have hsplit := Finset.sum_filter_add_sum_filter_not U.powerset
    (fun s => norm (∏ p ∈ s, p) ≤ D) F
  rw [hsmall] at hsplit
  change (∑ s ∈ U.powerset, F s) = _
  rw [← hsplit]
  simp only [not_le] 
  congr 1
  exact angular_fullPrimeDivisorMellinMass_one ℓ R W X e H u t hN

lemma angular_fullPrimeDivisorMellinMass_le {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {f : Eisenstein} (hf : primary f)
    (e : Eisenstein) (H : Finset Eisenstein) (u t : ℝ) {N₀ : ℝ} (hN₀ : 0 < N₀) :
    angular_fullPrimeDivisorMellinMass ℓ R W X e H u N₀ f t ≤
      ((∑ h ∈ H, ‖fullPrimeSliceSum R W X f e h 1 ℓ (u+2*Real.pi*t)‖^2)+
       (∑ h ∈ H, ‖fullPrimeSliceSum R W X f e h 1 ℓ (u-2*Real.pi*t)‖^2))/2 := by
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
  apply add_le_add
  · exact Finset.sum_le_sum (fun h _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
      (angular_fullPrimeSliceRow_norm_le ℓ W X hX hlo hhi hf e h u t hN₀) 2)
  · exact Finset.sum_le_sum (fun h _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
      (angular_fullPrimeSliceRow_reverse_norm_le ℓ W X hX hlo hhi hf e h u t hN₀) 2)

theorem angular_fullPrime_divisor_outer_mass {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
      (f e : Eisenstein) (H : Finset Eisenstein) (u t N₀ B N : ℝ),
      (∀ i, 0 < X i) → (∀ i x, x < 1 → W i x = 0) →
      (∀ i x, R < x → W i x = 0) → primary f → 0 < N₀ →
      1 ≤ B → 1 ≤ N →
      (∀ n ∈ fullPrimeSliceSupport R W X f e, norm n ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      angular_fullPrimeDivisorMellinMass ℓ R W X e H u N₀ f t ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
  obtain ⟨C,hC,houter⟩ := all_frequency_outer_sieve hε
  refine ⟨C,hC,?_⟩
  intro R W X f e H u t N₀ B N hX hlo hhi hf hN₀ hB hN hS hH
  have hbound (v : ℝ) :
      (∑ h ∈ H, ‖fullPrimeSliceSum R W X f e h 1 ℓ v‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
    let β := fun n => fullPrimeCoefficient R W X (f*n)*theta ℓ n*mellinPhase v (norm n)
    have hp : ∀ n ∈ fullPrimeSliceSupport R W X f e,
        primary n ∧ Squarefree n ∧ norm n ≤ N := by
      intro n hn
      have hh := fullPrimeSliceSupport_bounds R W X f e hn
      exact ⟨hh.1,hh.2.1,hS n hn⟩
    have hh := houter (fullPrimeSliceSupport R W X f e) H B N hB hN hp hH β
    have he : (∑ n ∈ fullPrimeSliceSupport R W X f e, ‖β n‖^2) =
        ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [β,norm_mul,mellinPhase_norm,
        norm_theta (primary_ne_zero (fullPrimeSliceSupport_bounds R W X f e hn).1),mul_one]
    rw [he] at hh
    simpa only [fullPrimeSliceSum,one_mul,β] using hh
  apply (angular_fullPrimeDivisorMellinMass_le ℓ W X hX hlo hhi hf e H u t hN₀).trans
  have hp := hbound (u+2*Real.pi*t)
  have hn := hbound (u-2*Real.pi*t)
  linarith


theorem angular_fullPrime_large_divisor_mass {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
      (e : Eisenstein) (H U : Finset Eisenstein) (u t N₀ B D : ℝ),
      1 ≤ R → (∀ i, 0 < X i) → (∀ i x, x < 1 → W i x = 0) →
      (∀ i x, R < x → W i x = 0) → (∀ p ∈ U, primaryPrime p) →
      0 < N₀ → 1 ≤ B → 1 ≤ D → D ≤ ∏ i, X i →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      let N := R^Fintype.card ι*(∏ i, X i)/D
      (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
        angular_fullPrimeDivisorMellinMass ℓ R W X e H u N₀ (∏ p ∈ s, p) t) ≤
      C*(2^Fintype.card ι:ℝ)*(2*B*N)^ε*
        (B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
        ∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖^2 := by
  obtain ⟨C,hC,hbound⟩ := angular_fullPrime_divisor_outer_mass ℓ (ι := ι) hε
  refine ⟨C,hC,?_⟩
  intro R W X e H U u t N₀ B D hR hX hlo hhi hU hN₀ hB hD hDL hH
  dsimp only
  let L := ∏ i, X i
  let N := R^Fintype.card ι*L/D
  let A := C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)
  have hL : 0 < L := Finset.prod_pos (fun i _ => hX i)
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hN : 1 ≤ N := by
    apply (le_div_iff₀ hD0).mpr
    have hRp : 1 ≤ R^Fintype.card ι := one_le_pow₀ hR
    simpa only [one_mul] using hDL.trans (le_mul_of_one_le_left hL.le hRp)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hrow (s : Finset Eisenstein)
      (hs : s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p))) :
      angular_fullPrimeDivisorMellinMass ℓ R W X e H u N₀ (∏ p ∈ s, p) t ≤
        A*∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
          ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2 := by
    obtain ⟨hsU,hfD⟩ := Finset.mem_filter.mp hs
    have hf := primary_finset_prod s (fun p : Eisenstein => p)
      (fun p hp => (hU p (Finset.mem_powerset.mp hsU hp)).1)
    apply hbound R W X (∏ p ∈ s, p) e H u t N₀ B N hX hlo hhi hf hN₀ hB hN _ hH
    intro n hn
    apply (fullPrimeSliceSupport_bounds R W X _ e hn).2.2.2.trans
    exact div_le_div_of_nonneg_left (mul_nonneg (by positivity) hL.le) hD0 hfD.le
  have he := fullPrime_summed_slice_energy W X hX hlo hhi e U hU
  have hesub : (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
      ∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
        ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2) ≤
      (2^Fintype.card ι:ℝ)*∑ b ∈ fullSquarefreePrimeSupport R W X e,
        ‖fullPrimeCoefficient R W X b‖^2 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans he
  calc
    _ ≤ ∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
        A*∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
          ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2 := Finset.sum_le_sum hrow
    _ = A*(∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
        ∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
          ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*((2^Fintype.card ι:ℝ)*∑ b ∈ fullSquarefreePrimeSupport R W X e,
        ‖fullPrimeCoefficient R W X b‖^2) := mul_le_mul_of_nonneg_left hesub hA
    _ = _ := by dsimp [A,N,L]; ring


theorem angular_fullPrime_large_divisor_log_saving {R δ : ℝ} (hR : 1 ≤ R)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (k : ℕ) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (e : Eisenstein) (H U : Finset Eisenstein) (u t N₀ : ℝ),
      T₀ ≤ L r → 1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      1 ≤ B → B ≤ (L r)^(1+δ/4) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ p ∈ U, primaryPrime p) → 0 < N₀ →
      (∑ s ∈ U.powerset.filter (fun s => (L r)^δ < norm (∏ p ∈ s, p)),
        angular_fullPrimeDivisorMellinMass ℓ R (W r) X e H u N₀ (∏ p ∈ s, p) t) ≤
      K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,hC,hbound⟩ := angular_fullPrime_large_divisor_mass ℓ (ι := ι)
    (show 0 < δ/100 by positivity)
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  let A := R^Fintype.card ι
  let D := (2*A)^(δ/100)*(1+A^(2/3:ℝ)+A)
  have hA : 1 ≤ A := one_le_pow₀ hR
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp
    (negative_power_log_saving (show 0 < δ/20 by positivity) (a+k))
  refine ⟨C*(2^Fintype.card ι:ℝ)*(E+1)*D,T₀,by positivity,?_⟩
  intro r X B e H U u t N₀ hT₀ hL hX hprod hB hBL hH hU hN₀
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hDel : 1 ≤ (L r)^δ := Real.one_le_rpow hL hδ.le
  have hDL : (L r)^δ ≤ L r := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL hδ₁
  let N := A*L r/(L r)^δ
  have hNeq : N = A*(L r)^(1-δ) := by
    dsimp [N]
    rw [Real.rpow_sub hLp,Real.rpow_one]
    ring
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hm := hbound R (W r) X e H U u t N₀ B ((L r)^δ) hR
    (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) hU hN₀ hB hDel
    (by simpa only [hprod] using hDL) hH
  rw [hprod] at hm
  have he : (∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
      ‖fullPrimeCoefficient R (W r) X b‖^2) ≤
      (E+1)*L r*(1+Real.log (L r))^a := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans
    apply (henergy r X hL hX hprod).trans
    nlinarith [mul_nonneg hLp.le (pow_nonneg hz.le a)]
  have hn := shortened_outer_power_saving hL (zero_lt_one.trans_le hB) hN hA hδ hδ₁
    (show δ/4 ≤ 1/4 by linarith) le_rfl hBL hNeq.le
  have hlog : (1+Real.log (L r))^a*(L r)^(-δ/20) ≤ 1/(1+Real.log (L r))^k := by
    rw [show -δ/20 = -(δ/20) by ring]
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  calc
    _ ≤ C*(2^Fintype.card ι:ℝ)*(2*B*N)^(δ/100)*
        (B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*((E+1)*L r*(1+Real.log (L r))^a) :=
      hm.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ = (C*(2^Fintype.card ι:ℝ)*(E+1)*(1+Real.log (L r))^a)*
        ((2*B*N)^(δ/100)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*L r) := by ring
    _ ≤ (C*(2^Fintype.card ι:ℝ)*(E+1)*(1+Real.log (L r))^a)*
        (D*(L r)^2*B^(1/3:ℝ)*(L r)^(-δ/20)) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (C*(2^Fintype.card ι:ℝ)*(E+1)*D)*(L r)^2*B^(1/3:ℝ)*
        ((1+Real.log (L r))^a*(L r)^(-δ/20)) := by ring
    _ ≤ _ := by
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hlog
        (show 0 ≤ (C*(2^Fintype.card ι:ℝ)*(E+1)*D)*(L r)^2*B^(1/3:ℝ) by positivity)

theorem angular_fullPrime_coprime_mass_integral_le {R D : ℝ} (hD : 1 ≤ D)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) (H U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (u : ℝ) {N : ℝ} (hN : 0 < N)
    {f : ℝ → ℝ} (hf : Integrable f) (hf0 : ∀ t, 0 ≤ f t) {A : ℝ}
    (hlarge : ∀ t, (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
      angular_fullPrimeDivisorMellinMass ℓ R W X e H u N (∏ p ∈ s, p) t) ≤ A) :
    (∫ t : ℝ, f t * coprimeMellinMass (fullSquarefreePrimeSupport R W X e) H U
      (fun a => star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a)))
      (fun a => star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a)))
      (fun a => norm a/N) t) ≤
    (∫ t : ℝ, f t*((fullStructuredHeightMass R H 1 e ℓ u W X (2*Real.pi*t)+
      fullStructuredHeightMass R H 1 e ℓ u W X (-(2*Real.pi*t)))/2)) + A*(∫ t : ℝ, f t) := by
  have hp := integrable_scaled_height_mass hf R H 1 e ℓ u W X (2*Real.pi)
  have hn := integrable_scaled_height_mass hf R H 1 e ℓ u W X (-(2*Real.pi))
  simp only [neg_mul] at hn
  have hs : Integrable (fun t : ℝ => f t*((fullStructuredHeightMass R H 1 e ℓ u W X (2*Real.pi*t)+
      fullStructuredHeightMass R H 1 e ℓ u W X (-(2*Real.pi*t)))/2)) := by
    convert (hp.add hn).div_const 2 using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    dsimp only [Pi.add_apply]
    ring
  calc
    _ ≤ ∫ t : ℝ, f t*((fullStructuredHeightMass R H 1 e ℓ u W X (2*Real.pi*t)+
        fullStructuredHeightMass R H 1 e ℓ u W X (-(2*Real.pi*t)))/2)+A*f t := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall (fun t => mul_nonneg (hf0 t) (coprimeMellinMass_nonneg _ _ _ _ _ _ t)))
        (hs.add (hf.const_mul A))
      filter_upwards with t
      rw [angular_fullPrime_coprime_mass_split ℓ hD W X hX hlo hhi hrough e H U hU u t hN]
      calc
        _ ≤ f t*((fullStructuredHeightMass R H 1 e ℓ u W X (2*Real.pi*t)+
            fullStructuredHeightMass R H 1 e ℓ u W X (-(2*Real.pi*t)))/2+A) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl (hlarge t)) (hf0 t)
        _ = _ := by dsimp only [Pi.add_apply]; ring
    _ = _ := by rw [integral_add hs (hf.const_mul A),integral_const_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStructuredResidualFrequencies
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact passage from ramified/cube frequencies to the structured pair
moments. A cube factor becomes an arithmetic exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullStructuredAngularPrimeSum_residual (R : ℝ) (r j p q v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    fullStructuredAngularPrimeSum ℓ R (r*p*q^2*j^3) 1 v e u W X =
      fullStructuredAngularPrimeSum ℓ R p q (v*r) (e*j) u W X := by
  unfold fullStructuredAngularPrimeSum
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have hp := orderedPrimarySupport_primary (fullPrimeSupport R W X)
    (fullPrimeSupport_primary R W X) hz
  have hcop : IsCoprime z (e*j) ↔ IsCoprime z e ∧ IsCoprime z j :=
    ⟨fun h => ⟨h.of_mul_right_left,h.of_mul_right_right⟩,fun h => h.1.mul_right h.2⟩
  have hnum : v*(r*p*q^2*j^3)*1^2 = ((v*r)*p*q^2)*j^3 := by ring
  rw [hnum,cubicSymbol_mul_upper hp,cubicSymbol_cube_indicator hp j]
  by_cases he : IsCoprime z e <;> by_cases hj : IsCoprime z j <;>
    simp only [hcop,he,hj,and_self,and_false,false_and,ite_true, if_true,ite_false, if_false,mul_one,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedAngularHecke
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

private lemma eventually_loglog_small (a b ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      a + b * Real.log (Real.log x) ≤ ε * Real.sqrt (Real.log x) := by
  have hlim : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hc : (fun _ : ℝ => a) =o[atTop] (fun x => Real.sqrt (Real.log x)) := by
    apply isLittleO_const_left.mpr
    right
    simpa only [Function.comp_def, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hlim
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
    Real.tendsto_log_atTop
  have hl' : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
      (fun x => Real.sqrt (Real.log x)) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using hl
  have h := (hc.add (hl'.const_mul_left b)).def hε
  filter_upwards [h] with x hx
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hx)

/-- Logarithmic conductor growth makes the published exponential error
smaller than any prescribed logarithmic saving, uniformly in the conductor. -/
lemma heckeExponentialError_logSaving {c K A D : ℝ}
    (hc : 0 < c) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, ∀ Q : ℝ, 1 ≤ Q → Q ≤ K * (Real.log x) ^ A →
      heckeExponentialError c x Q ≤ 16 * x / (Real.log x) ^ D := by
  have hcond := eventually_loglog_small (Real.log K) A 1 zero_lt_one
  have hdecay := eventually_loglog_small 0 (D + 4) (c / 2) (by positivity)
  filter_upwards [hcond, hdecay, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with x hcond hdecay hL hx Q hQ hQmax
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hL₀ : 0 < Real.log x := Real.log_pos hx
  have hQ₀ : 0 < Q := zero_lt_one.trans_le hQ
  have hlogQ₀ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlogQ : Real.log Q ≤ Real.sqrt (Real.log x) := by
    have h := Real.log_le_log hQ₀ hQmax
    rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hL₀ A).ne', Real.log_rpow hL₀] at h
    exact h.trans (by simpa only [one_mul] using hcond)
  have hroot : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hL₀
  have hd : 0 < Real.log Q + Real.sqrt (Real.log x) := by positivity
  have hratio : Real.sqrt (Real.log x) / 2 ≤
      Real.log x / (Real.log Q + Real.sqrt (Real.log x)) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [Real.sq_sqrt hL₀.le]
  have he₁ : Real.exp (-c * Real.log x / (Real.log Q + Real.sqrt (Real.log x))) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = -c * (Real.log x / (Real.log Q + Real.sqrt (Real.log x))) := by ring
      _ ≤ _ := by nlinarith
  have he₂ : Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤
      (Real.log x) ^ (-(D + 4)) := by
    rw [Real.rpow_def_of_pos hL₀]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlogprod : Real.log (x * Q) ≤ 2 * Real.log x := by
    rw [Real.log_mul hx₀.ne' hQ₀.ne']
    have hq := hlogQ.trans (Real.sqrt_le_self_iff.mpr (Or.inr hL))
    linarith
  have hpoly : (Real.log (x * Q)) ^ 4 ≤ 16 * (Real.log x) ^ 4 := by
    calc
      _ ≤ (2 * Real.log x) ^ 4 := by
        gcongr
        exact Real.log_nonneg (by nlinarith)
      _ = _ := by ring
  have hpow : (Real.log x) ^ 4 * (Real.log x) ^ (-(D + 4)) =
      1 / (Real.log x) ^ D := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL₀]
    norm_num
    rw [Real.rpow_neg hL₀.le]
  calc
    heckeExponentialError c x Q ≤
        x * (16 * (Real.log x) ^ 4) * (Real.log x) ^ (-(D + 4)) := by
      unfold heckeExponentialError
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly hx₀.le)
        (he₁.trans he₂) (Real.exp_nonneg _) (by positivity)
    _ = 16 * x / (Real.log x) ^ D := by rw [mul_assoc, mul_assoc, hpow]; ring

/-- The prime-power deletion error is also negligible at every fixed
logarithmic scale. -/
lemma sqrt_logSq_logSaving (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x * (Real.log x) ^ 2 ≤ x / (Real.log x) ^ D := by
  have h := (isLittleO_log_rpow_rpow_atTop (D + 2)
    (by norm_num : (0 : ℝ) < 1 / 2)).def zero_lt_one
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx₁
  have hx₀ : 0 < x := zero_lt_one.trans hx₁
  have hL₀ : 0 < Real.log x := Real.log_pos hx₁
  have hsmall : (Real.log x) ^ (D + 2) ≤ Real.sqrt x := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hL₀.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _), one_mul, Real.sqrt_eq_rpow] using hx
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL₀ D)).mpr
  calc
    _ = Real.sqrt x * (Real.log x) ^ (D + 2) := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hL₀]
      congr 2
      ring
    _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg x)
    _ = x := Real.mul_self_sqrt hx₀.le

lemma angularConductorFactor_ge_one (ℓ : ℤ) : 1 ≤ angularConductorFactor ℓ := by
  unfold angularConductorFactor
  nlinarith [abs_nonneg (ℓ : ℝ)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAngularKummerPrime
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem angular_kummer_chebyshev_logSaving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (_hA : 0 < A) (_hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ x : ℝ, X₀ ≤ x → ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
        norm v ≤ (Real.log x) ^ A →
        ‖primeChebyshev (angularKummerCharacter ℓ v) x‖ ≤ C * x / (Real.log x) ^ D := by
  obtain ⟨B, c, hB, hc, hbound⟩ := hEF ℓ hℓ
  have hK : 0 < angularKummerConductorFactor ℓ := zero_lt_one.trans_le (angularKummerConductorFactor_ge_one ℓ)
  have herr := heckeExponentialError_logSaving (K := angularKummerConductorFactor ℓ)
    (A := A) (D := D) hc hK
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (herr.and (sqrt_logSq_logSaving D))
  refine ⟨17 * B, max X₁ 3, by positivity, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx v hv hnc hcon
  have hx₁ : X₁ ≤ x := (le_max_left _ _).trans hx
  have hx₃ : 3 ≤ x := (le_max_right _ _).trans hx
  have he := (hX₁ x hx₁).1 (angularKummerAnalyticConductor ℓ v)
    (angularKummerAnalyticConductor_ge_one ℓ hv)
    (mul_le_mul_of_nonneg_left hcon hK.le)
  calc
    _ ≤ B * (16 * x / (Real.log x) ^ D + x / (Real.log x) ^ D) :=
      (hbound v hv hnc x hx₃).trans
        (mul_le_mul_of_nonneg_left (add_le_add he (hX₁ x hx₁).2) hB.le)
    _ = _ := by ring

/-- Partial summation removes the logarithmic prime weight, permitting
smooth weights and norm phases. The derivative cost is retained exactly. -/
theorem weighted_angular_kummer_prime_log_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ a b : ℝ, X₀ ≤ a → a ≤ b → ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
        norm v ≤ (Real.log a) ^ A → ∀ f : ℝ → ℂ,
          (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t => f t / (Real.log t : ℂ)) t) →
          IntegrableOn (deriv (fun t => f t / (Real.log t : ℂ))) (Set.Icc a b) →
          ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p),
            f (norm p) * angularKummerCharacter ℓ v p‖ ≤
          (C * b / (Real.log a) ^ D) *
            (‖f a / (Real.log a : ℂ)‖ + ‖f b / (Real.log b : ℂ)‖ +
              ∫ t in Set.Ioc a b, ‖deriv (fun t => f t / (Real.log t : ℂ)) t‖) := by
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ := angular_kummer_chebyshev_logSaving hEF ℓ hℓ A D hA hD
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro a b ha hab v hv hnc hcon f hdiff hderiv
  have ha₁ : 1 < a := hX₀.trans_le ha
  have ha₀ : 0 < a := zero_lt_one.trans ha₁
  have hprefix : ∀ t ∈ Set.Icc a b,
      ‖primeCutoffSum (fun p => angularKummerCharacter ℓ v p * (Real.log (norm p) : ℂ)) t‖ ≤
        C * b / (Real.log a) ^ D := by
    intro t ht
    have ht₀ : 0 < t := ha₀.trans_le ht.1
    have hlog : Real.log a ≤ Real.log t := Real.log_le_log ha₀ ht.1
    have hcon' : norm v ≤ (Real.log t) ^ A :=
      hcon.trans (Real.rpow_le_rpow (Real.log_pos ha₁).le hlog hA.le)
    apply (hbound t (ha.trans ht.1) v hv hnc hcon').trans
    exact div_le_div₀ (mul_nonneg hC.le (ht₀.le.trans ht.2))
      (mul_le_mul_of_nonneg_left ht.2 hC.le)
      (Real.rpow_pos_of_pos (Real.log_pos ha₁) D)
      (Real.rpow_le_rpow (Real.log_pos ha₁).le hlog hD.le)
  have h := weighted_prime_bound
    (fun p => angularKummerCharacter ℓ v p * (Real.log (norm p) : ℂ))
    (fun t => f t / (Real.log t : ℂ)) ha₀.le hab hdiff hderiv hprefix
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro p hp
  have hp₁ : 1 < norm p := ha₁.trans (Finset.mem_filter.mp hp).2
  have hlog : (Real.log (norm p) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hp₁).ne'
  field_simp


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularKummerWeightVariation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dividing a smooth prime weight by log preserves an explicit finite
variation bound above exp(1). This removes the Chebyshev weight without
assuming any weighted prime estimate. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma prime_log_weight_deriv_bound {f : ℝ → ℂ} {Y x M D : ℝ}
    (hY : 0 < Y) (hx : Y ≤ x) (hlog : 1 ≤ Real.log x)
    (hM : 0 ≤ M) (_hD : 0 ≤ D) (hf : DifferentiableAt ℝ f x)
    (hfn : ‖f x‖ ≤ M) (hfd : ‖deriv f x‖ ≤ D/Y) :
    ‖deriv (fun t => f t/(Real.log t:ℂ)) x‖ ≤ (D+M)/Y := by
  have hxp : 0 < x := hY.trans_le hx
  have hLp : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hLc : (Real.log x:ℂ) ≠ 0 := by exact_mod_cast hLp.ne'
  have he : deriv (fun t => f t/(Real.log t:ℂ)) x =
      deriv f x/(Real.log x:ℂ)-f x/((x:ℂ)*(Real.log x:ℂ)^2) := by
    have hd := (hf.hasDerivAt.div (Real.hasDerivAt_log hxp.ne').ofReal_comp hLc).deriv
    change deriv (fun t => f t/(Real.log t:ℂ)) x = _ at hd
    rw [hd]
    push_cast
    field_simp

  rw [he]
  apply (norm_sub_le _ _).trans
  have hfirst : ‖deriv f x/(Real.log x:ℂ)‖ ≤ D/Y := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hLp.le]
    exact (div_le_self (_root_.norm_nonneg _) hlog).trans hfd
  have hden : Y ≤ x*(Real.log x)^2 :=
    hx.trans (le_mul_of_one_le_right hxp.le (one_le_pow₀ hlog))
  have hsecond : ‖f x/((x:ℂ)*(Real.log x:ℂ)^2)‖ ≤ M/Y := by
    rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg hxp.le,Real.norm_of_nonneg hLp.le]
    exact div_le_div₀ hM hfn hY hden
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

lemma log_normalized_rescaled_mellin_variation {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    {Y R M D : ℝ} (hY : Real.exp 1 ≤ Y) (hR : 1 ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hwm : ∀ x, ‖w x‖ ≤ M) (hwd : ∀ x, 0 < x → ‖deriv w x‖*x ≤ D) (u : ℝ) :
    let f := fun t => w (t/Y)*mellinPhase u t/(Real.log t:ℂ)
    (∀ t ∈ Icc Y (R*Y), DifferentiableAt ℝ f t) ∧
    IntegrableOn (deriv f) (Icc Y (R*Y)) ∧
    ‖f Y‖+‖f (R*Y)‖+(∫ t in Ioc Y (R*Y), ‖deriv f t‖) ≤
      2*M+(R-1)*(D+M*|u|+M) := by
  dsimp only
  have hYp : 0 < Y := (Real.exp_pos 1).trans_le hY
  have hY1 : 1 < Y := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hY
  have hab : Y ≤ R*Y := by nlinarith
  have hlogY : 1 ≤ Real.log Y := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hY
  let f := fun t => w (t/Y)*mellinPhase u t
  have hsub : Icc Y (R*Y) ⊆ Ioi (1:ℝ) := fun _ ht => hY1.trans_le ht.1
  have hf := contDiffOn_rescaled_mellin hw Y u
  have hf' : ContDiffOn ℝ ∞ f (Ioi 1) :=
    hf.mono (by
      intro t ht
      change (1:ℝ) < t at ht
      change (0:ℝ) < t
      exact zero_lt_one.trans ht)
  have hl : ContDiffOn ℝ ∞ (fun t : ℝ => (Real.log t:ℂ)) (Ioi 1) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Real.contDiffOn_log.mono (fun t ht => ne_of_gt (zero_lt_one.trans ht)))
  have hg : ContDiffOn ℝ ∞ (fun t => f t/(Real.log t:ℂ)) (Ioi 1) := by
    have hn : ∀ t ∈ Ioi (1:ℝ), (Real.log t:ℂ) ≠ 0 := by
      intro t ht
      exact_mod_cast (Real.log_pos ht).ne'
    simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.inv_apply] using hf'.mul (hl.inv hn)
  have hd : ContinuousOn (deriv (fun t => f t/(Real.log t:ℂ))) (Icc Y (R*Y)) :=
    (hg.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  refine ⟨?_,hd.integrableOn_Icc,?_⟩
  · intro t ht
    exact ((hg t (hsub ht)).contDiffAt (isOpen_Ioi.mem_nhds (hsub ht))).differentiableAt
      (by norm_num)
  have hlog (x : ℝ) (hx : Y ≤ x) : 1 ≤ Real.log x :=
    hlogY.trans (Real.log_le_log hYp hx)
  have hn (x : ℝ) : ‖f x‖ ≤ M := by
    dsimp [f]
    simpa only [norm_mul,mellinPhase_norm,mul_one] using hwm (x/Y)
  have hnlog (x : ℝ) (hx : Y ≤ x) : ‖f x/(Real.log x:ℂ)‖ ≤ M := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans (hlog x hx))]
    exact (div_le_self (_root_.norm_nonneg _) (hlog x hx)).trans (hn x)
  have hb (x : ℝ) (hx : Y ≤ x) :
      ‖deriv (fun t => f t/(Real.log t:ℂ)) x‖ ≤ (D+M*|u|+M)/Y := by
    apply prime_log_weight_deriv_bound hYp hx (hlog x hx) hM (by positivity)
    · exact ((hf x (hYp.trans_le hx)).contDiffAt
        (isOpen_Ioi.mem_nhds (hYp.trans_le hx))).differentiableAt (by norm_num)
    · exact hn x
    · exact rescaled_mellin_deriv_bound hw hYp hx hM hD (hwm _)
        (hwd _ (div_pos (hYp.trans_le hx) hYp)) u
  have hi : (∫ t in Ioc Y (R*Y), ‖deriv (fun t => f t/(Real.log t:ℂ)) t‖) ≤
      (R-1)*(D+M*|u|+M) := by
    rw [←intervalIntegral.integral_of_le hab]
    have hpoint : ∀ t ∈ uIoc Y (R*Y),
        ‖‖deriv (fun t => f t/(Real.log t:ℂ)) t‖‖ ≤ (D+M*|u|+M)/Y := by
      intro t ht
      rw [uIoc_of_le hab] at ht
      rw [Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]
      exact hb t ht.1.le
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := Y) (b := R*Y)
      (f := fun t => ‖deriv (fun t => f t/(Real.log t:ℂ)) t‖) hpoint
    have hnonneg : 0 ≤ ∫ t in Y..R*Y, ‖deriv (fun t => f t/(Real.log t:ℂ)) t‖ :=
      intervalIntegral.integral_nonneg_of_forall hab (fun _ => _root_.norm_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hnonneg,abs_of_nonneg (sub_nonneg.mpr hab)] at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  linarith [hnlog Y le_rfl,hnlog (R*Y) hab]

theorem scaled_angular_kummer_prime_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ (Y R M B : ℝ) (w : ℝ → ℂ),
      X₀ ≤ Y → 1 ≤ R → 0 ≤ M → 0 ≤ B → ContDiff ℝ ∞ w →
      (∀ x, x < 1 → w x = 0) → (∀ x, ‖w x‖ ≤ M) →
      (∀ x, 0 < x → ‖deriv w x‖*x ≤ B) →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log Y)^A → ∀ u : ℝ,
      ‖smoothPrimeCharacterSum R Y w (angularKummerCharacter ℓ v) u‖ ≤
        (C*(R*Y)/(Real.log Y)^D)*(2*M+(R-1)*(B+M*|u|+M)) := by
  obtain ⟨C,X₀,hC,hX₀,hb⟩ := weighted_angular_kummer_prime_log_bound hEF ℓ hℓ A D hA hD
  refine ⟨C,max X₀ (Real.exp 1),hC,hX₀.trans_le (le_max_left _ _),?_⟩
  intro Y R M B w hY hR hM hB hw hlo hwm hwd v hv hnc hNv u
  have hYp : 0 < Y := zero_lt_one.trans (hX₀.trans_le ((le_max_left _ _).trans hY))
  have hab : Y ≤ R*Y := by nlinarith
  have hRp : 0 < R := zero_lt_one.trans_le hR
  obtain ⟨hd,hi,hv'⟩ := log_normalized_rescaled_mellin_variation hw
    ((le_max_right _ _).trans hY) hR hM hB hwm hwd u
  rw [smoothPrimeCharacterSum_eq_interval hYp hw.continuous hlo]
  have hscalar : 0 ≤ C*(R*Y)/(Real.log Y)^D :=
    div_nonneg (mul_nonneg hC.le (mul_nonneg hRp.le hYp.le))
      (Real.rpow_nonneg (Real.log_nonneg (le_of_lt
        (hX₀.trans_le ((le_max_left _ _).trans hY)))) _)
  exact (hb Y (R*Y) ((le_max_left _ _).trans hY) hab v hv hnc hNv _ hd hi).trans
    (mul_le_mul_of_nonneg_left hv' hscalar)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularKummerLogSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary logarithmic saving for actual independent prime weights,
uniform in logarithmic Mellin height and logarithmic conductor. -/
noncomputable section
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_kummer_logarithmic_prime_saving {γ : Type*}
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) {L : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily L W) (hlo : ∀ r x, x < 1 → W r x = 0)
    {c R A : ℝ} (hc : 0 < c) (hR : 1 ≤ R) (hA : 0 < A)
    (k U : ℕ) (hk : 0 < k) :
    ∃ K Y₀ : ℝ, 0 < K ∧ 1 < Y₀ ∧ ∀ (r : γ) (Y : ℝ), Y₀ ≤ Y →
      1 ≤ Real.log (L r) → (L r)^c ≤ Y →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log Y)^A → ∀ u : ℝ, |u| ≤ (1+Real.log (L r))^U →
      ‖smoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) u‖ ≤
        K*Y/(1+Real.log (L r))^k := by
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  obtain ⟨B,b,hB,hBb⟩ := hW.radial_deriv_bound
  let N := m+b+U
  have hD : (0:ℝ) < (N+k:ℕ) := by exact_mod_cast (show 0 < N+k by omega)
  obtain ⟨C,Y₀,hC,hY₀,hbound⟩ := scaled_angular_kummer_prime_bound hSW ℓ hℓ hA hD
  let V := 2*M+(R-1)*(B+2*M)
  let K₀ := C*R*V*(2/c)^(N+k)
  let K := max 1 K₀
  have hV : 0 ≤ V := add_nonneg (mul_nonneg (by norm_num) hM)
    (mul_nonneg (sub_nonneg.mpr hR) (add_nonneg hB (mul_nonneg (by norm_num) hM)))
  refine ⟨K,Y₀,lt_of_lt_of_le zero_lt_one (le_max_left _ _),hY₀,?_⟩
  intro r Y hY hlog hLc v hv hn hcon u hu
  let z := 1+Real.log (L r)
  have hLp : 0 < L r := zero_lt_one.trans_le (hW.length_one r)
  have hz : 1 ≤ z := by dsimp [z]; linarith
  have hzp : 0 < z := zero_lt_one.trans_le hz
  obtain ⟨hlogY,hcompare⟩ := log_length_comparison hLp hc hlog hLc
  have hYp : 0 < Y := zero_lt_one.trans (hY₀.trans_le hY)
  have hb := hbound Y R (M*z^m) (B*z^b) (W r) hY hR
    (mul_nonneg hM (pow_nonneg hzp.le _)) (mul_nonneg hB (pow_nonneg hzp.le _))
    (hW.smooth r) (hlo r) (hMb r) (hBb r) v hv hn hcon u
  have hv : 2*(M*z^m)+(R-1)*(B*z^b+M*z^m*|u|+M*z^m) ≤ V*z^N := by
    have hv₀ := log_variation_power hz hR hM hB m b U hu
    have hm' : (R-1)*(M*z^m) ≤ (R-1)*M*z^N := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by dsimp [N]; omega)) hM)
        (sub_nonneg.mpr hR)
    calc
      _ = (2*(M*z^m)+(R-1)*(B*z^b+M*z^m*|u|))+(R-1)*(M*z^m) := by ring
      _ ≤ (2*M+(R-1)*(B+M))*z^N+(R-1)*M*z^N := add_le_add (by simpa only [N,mul_assoc] using hv₀) hm'
      _ = _ := by dsimp [V]; ring
  have hquot : z^N/(Real.log Y)^(N+k) ≤ (2/c)^(N+k)/z^k :=
    log_power_quotient hzp hlogY hcompare N k
  have hfac : 0 ≤ C*(R*Y)/(Real.log Y)^(N+k) :=
    div_nonneg (mul_nonneg hC.le (mul_nonneg (zero_le_one.trans hR) hYp.le))
      (pow_nonneg hlogY.le _)
  calc
    _ ≤ (C*(R*Y)/(Real.log Y)^(N+k))*(V*z^N) := by
      apply hb.trans
      simpa only [Real.rpow_natCast] using mul_le_mul_of_nonneg_left hv hfac
    _ = (C*R*V*Y)*(z^N/(Real.log Y)^(N+k)) := by ring
    _ ≤ (C*R*V*Y)*((2/c)^(N+k)/z^k) :=
      mul_le_mul_of_nonneg_left hquot
        (mul_nonneg (mul_nonneg (mul_nonneg hC.le (zero_le_one.trans hR)) hV) hYp.le)
    _ = K₀*Y/z^k := by dsimp [K₀]; ring
    _ ≤ K*Y/z^k := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hYp.le) (pow_nonneg hzp.le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularExcludedKummerLogSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual low-height prime Siegel–Walfisz bound, including any
polynomially bounded excluded element. No exclusion estimate is assumed. -/
noncomputable section
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_excluded_kummer_logarithmic_prime_saving {γ : Type*}
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) {L : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily L W) (hlo : ∀ r x, x < 1 → W r x = 0)
    {c d R A : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hR : 1 ≤ R) (hA : 0 < A)
    (k U : ℕ) (hk : 0 < k) :
    ∃ K Y₀ L₀ : ℝ, 0 < K ∧ 1 < Y₀ ∧ ∀ (r : γ) (Y : ℝ), Y₀ ≤ Y → L₀ ≤ L r →
      1 ≤ Real.log (L r) → (L r)^c ≤ Y →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log Y)^A →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ (L r)^d → ∀ u : ℝ,
      |u| ≤ (1+Real.log (L r))^U →
      ‖excludedSmoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) e u‖ ≤
        K*Y/(1+Real.log (L r))^k := by
  obtain ⟨K,Y₀,hK,hY₀,hbase⟩ := angular_kummer_logarithmic_prime_saving ℓ hSW hℓ hW hlo hc hR hA k U hk
  let ε := c/(2*(d+1))
  have hε : 0 < ε := div_pos hc (by positivity)
  have hgap : d*ε < c := by
    have he : ε*(2*(d+1)) = c := div_mul_cancel₀ c (by positivity : 2*(d+1) ≠ 0)
    nlinarith [mul_nonneg hε.le hd]
  obtain ⟨C,hC,herror⟩ := excluded_prime_input_error hε
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp
    (exclusion_log_absorption hε hgap (mul_nonneg hC.le hM) m k)
  refine ⟨K+1,Y₀,L₀,by linarith,hY₀,?_⟩
  intro r Y hY hL hlog hrough v hv hn hcon e he heL u hu
  have hmain := hbase r Y hY hlog hrough v hv hn hcon u hu
  have hn : 0 ≤ 1+Real.log (L r) := by linarith
  have hχ : ∀ p ∈ primeCutoff (R*Y), ‖angularKummerCharacter ℓ v p‖ ≤ 1 := by
    intro p hp
    unfold angularKummerCharacter
    rw [norm_mul,norm_theta (primary_ne_zero (mem_primeCutoff.mp hp).1.1) ℓ,one_mul]
    exact norm_cubicSymbol_le_one (mem_primeCutoff.mp hp).1.1 v
  have herr := herror R Y (M*(1+Real.log (L r))^m) (W r) (angularKummerCharacter ℓ v)
    (mul_nonneg hM (pow_nonneg hn _)) (hMb r) hχ e he u
  have habs := hL₀ (L r) hL Y (norm e) (norm_nonneg _) heL hrough
  have herr' : ‖excludedSmoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) e u-
      smoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) u‖ ≤ Y/(1+Real.log (L r))^k := by
    apply herr.trans
    convert habs using 1 <;> first | rfl | ring
  calc
    _ = ‖smoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) u+
        (excludedSmoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) e u-
          smoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) u)‖ := by
      congr 1
      ring
    _ ≤ ‖smoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) u‖+
        ‖excludedSmoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) e u-
          smoothPrimeCharacterSum R Y (W r) (angularKummerCharacter ℓ v) u‖ := norm_add_le _ _
    _ ≤ K*Y/(1+Real.log (L r))^k+Y/(1+Real.log (L r))^k := add_le_add hmain herr'
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularKummerPrimeFactorization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independent-prime factorization for arbitrary numerator,
including units and powers of the ramified prime. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullStructuredAngularPrimeSum_numerator_squarefree (R : ℝ) (W : ι → ℝ → ℂ)
    (X : ι → ℝ) (v e : Eisenstein) (u : ℝ) :
    fullStructuredAngularPrimeSum ℓ R v 1 1 e u W X =
      squarefreePrimePolynomial (fullPrimeSupport R W X)
        (fun i p => excludedPrimeWeight e W X i p*cubicNumeratorHom v p) ℓ u 0 := by
  classical
  unfold fullStructuredAngularPrimeSum squarefreePrimePolynomial angularCoefficientPolynomial
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b hb
  have hbp := orderedPrimarySupport_primary (fullPrimeSupport R W X)
    (fun i p hp => (fullPrimeSupport_prime R W X i p hp).1) hb
  rw [squarefreeConvolution_mul_character]
  rw [show squarefreeConvolution (fullPrimeSupport R W X) (excludedPrimeWeight e W X) b =
      fullPrimeCoefficient R W X b*primeExclusionCharacter e b from
        squarefreeConvolution_mul_character _ _ _ b]
  rw [primeExclusionCharacter_apply,cubicNumeratorHom_primary v hbp]
  simp only [one_pow,one_mul,mul_one,zero_add]
  by_cases he : IsCoprime b e <;> simp only [he,ite_true, if_true,ite_false, if_false,mul_one,mul_zero,zero_mul]
  ring

lemma fullStructuredAngularPrimeSum_numerator_factorization (R : ℝ) (W : ι → ℝ → ℂ)
    (X : ι → ℝ) (v e : Eisenstein) (u : ℝ) :
    (∏ i, excludedSmoothPrimeCharacterSum R (X i) (W i) (angularKummerCharacter ℓ v) e u)-
      fullStructuredAngularPrimeSum ℓ R v 1 1 e u W X =
      twistedErrorPrimePolynomial (fullPrimeSupport R W X) (excludedPrimeWeight e W X)
        (cubicNumeratorHom v) ℓ u 0 := by
  classical
  have hp := fullPrimeProduct_sub_squarefree (fullPrimeSupport R W X)
    (fun i p => excludedPrimeWeight e W X i p*cubicNumeratorHom v p)
    (fullPrimeSupport_prime R W X) ℓ u 0
  have he : errorPrimePolynomial (fullPrimeSupport R W X)
      (fun i p => excludedPrimeWeight e W X i p*cubicNumeratorHom v p) ℓ u 0 =
      twistedErrorPrimePolynomial (fullPrimeSupport R W X) (excludedPrimeWeight e W X)
        (cubicNumeratorHom v) ℓ u 0 := by
    unfold errorPrimePolynomial twistedErrorPrimePolynomial angularCoefficientPolynomial
    apply Finset.sum_congr rfl
    intro b _
    dsimp only
    rw [squarefreeConvolutionError,orderedConvolution_mul_character,
      squarefreeConvolution_mul_character,squarefreeConvolutionError,sub_mul]
    ring
  rw [he,← fullStructuredAngularPrimeSum_numerator_squarefree ℓ] at hp
  have hprod : fullPrimeProductPolynomial (fullPrimeSupport R W X)
      (fun i p => excludedPrimeWeight e W X i p*cubicNumeratorHom v p) ℓ u 0 =
      ∏ i, excludedSmoothPrimeCharacterSum R (X i) (W i) (angularKummerCharacter ℓ v) e u := by
    unfold fullPrimeProductPolynomial
    simp only [zero_add]
    apply Finset.prod_congr rfl
    intro i _
    rw [← excluded_prime_factor_eq R W X i e (angularKummerCharacter ℓ v) u]
    apply Finset.sum_congr rfl
    intro p hp
    rw [cubicNumeratorHom_primary v (fullPrimeSupport_prime R W X i p hp).1]
    unfold angularKummerCharacter
    ring
  rwa [hprod] at hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularFullKummerLogSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-height saving for the full squarefree convolution with arbitrary
noncube numerator, including its ramified and unit parts. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_full_kummer_log_saving
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    {c d R A : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hR : 1 ≤ R) (hA : 0 < A)
    (k U : ℕ) (hk : 0 < k) :
    ∃ K Y₀ L₀ : ℝ, 0 < K ∧ 1 < Y₀ ∧ ∀ (r : γ) (X : ι → ℝ),
      (∀ i, Y₀ ≤ X i) → L₀ ≤ L r → 1 ≤ Real.log (L r) →
      (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      (∀ i, norm v ≤ (Real.log (X i))^A) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ (L r)^d → ∀ u : ℝ,
      |u| ≤ (1+Real.log (L r))^U →
      ‖fullStructuredAngularPrimeSum ℓ R v 1 1 e u (W r) X‖ ≤
        K*L r/(1+Real.log (L r))^k := by
  obtain ⟨K,Y₀,L₁,hK,hY₀,hprime⟩ := angular_excluded_kummer_logarithmic_prime_saving ℓ hSW hℓ hW
    (fun z => hlo z.1 z.2) hc hd hR hA k U hk
  obtain ⟨L₂,herr⟩ := full_prime_error_log_saving hW hlo hc hR k
  refine ⟨K^(Fintype.card ι)+1,Y₀,max L₁ L₂,by positivity,hY₀,?_⟩
  intro r X hX hL hlog hlen hrough v hv hn hcon e he heL u hu
  have hLone : 1 ≤ L r := hW.length_one (r,Classical.arbitrary ι)
  have hXone : ∀ i, 1 ≤ X i := fun i => hY₀.le.trans (hX i)
  have hb : ‖∏ i, excludedSmoothPrimeCharacterSum R (X i) (W r i)
      (angularKummerCharacter ℓ v) e u‖ ≤ K^(Fintype.card ι)*L r/(1+Real.log (L r))^k := by
    apply prime_product_log_bound _ X hK.le (fun i => zero_le_one.trans (hXone i)) hlen (by linarith) k
    intro i
    exact hprime (r,i) (X i) (hX i) ((le_max_left _ _).trans hL) hlog (hrough i)
      v hv hn (hcon i) e he heL u hu
  have hχ : ∀ b ∈ orderedConvolutionSupport (fullPrimeSupport R (W r) X),
      ‖cubicNumeratorHom v b‖ ≤ 1 := by
    intro b hb
    have hbp := orderedPrimarySupport_primary (fullPrimeSupport R (W r) X)
      (fun i p hp => (fullPrimeSupport_prime R (W r) X i p hp).1) hb
    rw [cubicNumeratorHom_primary v hbp]
    exact norm_cubicSymbol_le_one hbp v
  have he' := herr r X ((le_max_right _ _).trans hL) hLone hXone hlen hrough
    e (cubicNumeratorHom v) hχ ℓ u 0
  have hid := fullStructuredAngularPrimeSum_numerator_factorization ℓ R (W r) X v e u
  calc
    _ = ‖(∏ i, excludedSmoothPrimeCharacterSum R (X i) (W r i) (angularKummerCharacter ℓ v) e u)-
        twistedErrorPrimePolynomial (fullPrimeSupport R (W r) X)
          (excludedPrimeWeight e (W r) X) (cubicNumeratorHom v) ℓ u 0‖ := by
      rw [← hid]
      congr 1
      ring
    _ ≤ ‖∏ i, excludedSmoothPrimeCharacterSum R (X i) (W r i) (angularKummerCharacter ℓ v) e u‖+
        ‖twistedErrorPrimePolynomial (fullPrimeSupport R (W r) X)
          (excludedPrimeWeight e (W r) X) (cubicNumeratorHom v) ℓ u 0‖ := norm_sub_le _ _
    _ ≤ K^(Fintype.card ι)*L r/(1+Real.log (L r))^k+L r/(1+Real.log (L r))^k := add_le_add hb he'
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularRoughKummerLowHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full nonprincipal rough-prime convolution at low height, with the
numerator measured at the actual full length, including its ramified and
unit factors. All prime and squarefree restrictions remain in the conclusion. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_rough_kummer_low_height
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    {c d R A : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hR : 1 ≤ R) (hA : 0 < A)
    (k U : ℕ) (hk : 0 < k) :
    ∃ K L₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log (L r))^A →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ (L r)^d → ∀ u : ℝ,
      |u| ≤ (1+Real.log (L r))^U →
      ‖fullStructuredAngularPrimeSum ℓ R v 1 1 e u (W r) X‖ ≤
        K*L r/(1+Real.log (L r))^k := by
  obtain ⟨K,Y₀,L₁,hK,_,hbound⟩ := angular_full_kummer_log_saving ℓ hSW hℓ hW hlo hc hd hR
    (show 0 < A+1 by linarith) k U hk
  have hevent : ∀ᶠ L : ℝ in atTop,
      L₁ ≤ L ∧ Y₀ ≤ L^c ∧ 1 ≤ Real.log L ∧
      ∀ Y : ℝ, L^c ≤ Y → (Real.log L)^A ≤ (Real.log Y)^(A+1) := by
    filter_upwards [eventually_ge_atTop L₁,
      (tendsto_rpow_atTop hc).eventually_ge_atTop Y₀,
      Real.tendsto_log_atTop.eventually_ge_atTop 1,
      rough_coordinate_conductor_scale hc hA.le] with L hL hY hlog hcon
    exact ⟨hL,hY,hlog,hcon⟩
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp hevent
  refine ⟨K,L₀,hK,?_⟩
  intro r X hL hprod hrough v hv hn hcon e he heL u hu
  obtain ⟨hL₁,hY,hlog,hscale⟩ := hL₀ (L r) hL
  exact hbound r X (fun i => hY.trans (hrough i)) hL₁ hlog hprod hrough
    v hv hn (fun i => hcon.trans (hscale _ (hrough i)))
    e he heL u hu

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularRoughNoncubeLowHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At low height the cube part of an arbitrary noncube frequency is
removed exactly and charged to the proved excluded-prime estimate. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_rough_noncube_low_height
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    {c d₁ d₂ R A : ℝ} (hc : 0 < c) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (hR : 1 ≤ R) (hA : 0 < A) (k U : ℕ) (hk : 0 < k) :
    ∃ K L₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      ∀ v j : Eisenstein, v ≠ 0 → j ≠ 0 →
      (¬∃ a : Eisenstein, a^3 = v*j^3) → norm v ≤ (Real.log (L r))^A → norm j ≤ (L r)^d₂ →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ (L r)^d₁ → ∀ u : ℝ,
      |u| ≤ (1+Real.log (L r))^U →
      ‖fullStructuredAngularPrimeSum ℓ R (v*j^3) 1 1 e u (W r) X‖ ≤
        K*L r/(1+Real.log (L r))^k := by
  obtain ⟨K,L₀,hK,hbound⟩ := angular_rough_kummer_low_height ℓ hSW hℓ hW hlo hc
    (add_nonneg hd₁ hd₂) hR hA k U hk
  refine ⟨K,L₀,hK,?_⟩
  intro r X hL hprod hrough v j hv hj hn hcon hjN e he heN u hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hW.length_one (r,Classical.arbitrary ι))
  have hnv : ¬∃ a : Eisenstein, a^3 = v := by
    rintro ⟨a,ha⟩
    apply hn
    exact ⟨a*j,by rw [mul_pow,ha]⟩
  have hen : norm (e*j) ≤ (L r)^(d₁+d₂) := by
    rw [norm_mul_eq,Real.rpow_add hLp]
    exact mul_le_mul heN hjN (norm_nonneg _) (Real.rpow_nonneg hLp.le _)
  have hb := hbound r X hL hprod hrough v hv hnv hcon (e*j) (mul_ne_zero he hj) hen u hu
  have hid := fullStructuredAngularPrimeSum_residual ℓ R 1 j v 1 1 e u (W r) X
  have hid' : fullStructuredAngularPrimeSum ℓ R (v*j^3) 1 1 e u (W r) X =
      fullStructuredAngularPrimeSum ℓ R v 1 1 (e*j) u (W r) X := by
    simpa only [one_mul,mul_one,one_pow] using hid
  rwa [hid']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLowNoncubeMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite low-noncube frequency mass follows from the raw
published prime estimate, with its cube multiplicity proved by lattice count. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_low_noncube_mass
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    {c d₁ d₂ R : ℝ} (hc : 0 < c) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (hR : 1 ≤ R) (a k U : ℕ) (ha : 0 < a) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ (r : γ) (X : ι → ℝ) (J : ℝ) (H : Finset Eisenstein),
      L₀ ≤ L r → (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) → 0 ≤ J → J ≤ (L r)^d₂ →
      H ⊆ lowNoncubeSupport ((Real.log (L r))^a) J →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ (L r)^d₁ → ∀ u : ℝ,
      |u| ≤ (1+Real.log (L r))^U →
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 1 e u (W r) X‖^2) ≤
        C*J*(L r)^2/(1+Real.log (L r))^k := by
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  obtain ⟨C,L₀,hC,hpoint⟩ := angular_rough_noncube_low_height ℓ hSW hℓ hW hlo hc hd₁ hd₂ hR ha'
    (a+k+1) U (by omega)
  refine ⟨324*C^2,L₀,by positivity,?_⟩
  intro r X J H hL hprod hrough hJ hJL hH e he heL u hu
  have hLone := hW.length_one (r,Classical.arbitrary ι)
  have hlog : 0 ≤ Real.log (L r) := Real.log_nonneg hLone
  have hz : 1 ≤ 1+Real.log (L r) := by linarith
  have hcard : (H.card:ℝ) ≤ 324*(1+Real.log (L r))^a*J := by
    calc
      _ ≤ ((lowNoncubeSupport ((Real.log (L r))^a) J).card:ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hH)
      _ ≤ 324*(Real.log (L r))^a*J := lowNoncubeSupport_card (pow_nonneg hlog _) hJ
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog (by linarith) _) (by norm_num)) hJ
  apply low_core_mass_bound hJ hz hcard
  calc
    _ ≤ ∑ _h ∈ H, (C*L r/(1+Real.log (L r))^(a+k+1))^2 := by
      apply Finset.sum_le_sum
      intro h hh
      obtain ⟨hn,v,j,hv,hj,hvN,hjN,hid⟩ := mem_lowNoncubeSupport (hH hh)
      have hnon : ¬∃ z : Eisenstein, z^3 = v*j^3 := by simpa only [← hid] using hn
      have hp := hpoint r X hL hprod hrough v j hv hj hnon
        (by simpa only [Real.rpow_natCast] using hvN) (hjN.trans hJL) e he heL u hu
      rw [hid]
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) hp 2
    _ = _ := by simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLowCoreMellinIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full low-core Mellin integral: Kummer cancellation near zero, the
ordinary signed height mean in the tails. Both estimates are applied to
the actual finite structured sums. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_low_core_mellin_integral_saving (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    {C R c d₁ d₂ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hR : 1 ≤ R) (hc : 0 < c) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (a k U q : ℕ) (ha : 0 < a) :
    ∃ K T₀ : ℝ, 0 ≤ K ∧ ∀ (r : γ) (X : ι → ℝ) (J : ℝ) (H : Finset Eisenstein),
      T₀ ≤ L r → (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      0 ≤ J → J ≤ (L r)^d₂ → H ⊆ lowNoncubeSupport ((Real.log (L r))^a) J →
      ∀ (e : Eisenstein) (u ρ : ℝ), e ≠ 0 → norm e ≤ (L r)^d₁ →
      |u| ≤ (1+Real.log (L r))^U → 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*
        fullStructuredHeightMass R H 1 e ℓ u (W r) X t) ≤
          K*J*(L r)^2/(1+Real.log (L r))^k := by
  obtain ⟨Kt,Tt,A,hKt,htail⟩ := low_core_arithmetic_mellin_tail hMV hC hR hW hlo hhi
    M hM V hV hV' a k q
  obtain ⟨Kn,Tn,hKn,hnear⟩ := angular_low_noncube_mass ℓ hSW hℓ hW hlo hc hd₁ hd₂ hR a k (max A U+1) ha
  obtain ⟨D,hD,hmoment⟩ := arithmeticMellinCoefficient_moment_decay M hM V hV hV' q 0
  refine ⟨Kn*D+Kt,max (max Tt Tn) (Real.exp 1),by positivity,?_⟩
  intro r X J H hT₀ hprod hrough hJ hJL hH e u ρ he heL hu hρ
  have hL : 1 ≤ L r := hW.length_one (r,Classical.arbitrary ι)
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hTt : Tt ≤ L r := (le_max_left Tt Tn).trans ((le_max_left _ _).trans hT₀)
  have hTn : Tn ≤ L r := (le_max_right Tt Tn).trans ((le_max_left _ _).trans hT₀)
  have hExp : Real.exp 1 ≤ L r := (le_max_right _ _).trans hT₀
  have hz : 2 ≤ 1+Real.log (L r) := by
    have hh := (Real.le_log_iff_exp_le hLp).mpr hExp
    linarith
  let T := (1+Real.log (L r))^A
  let F := arithmeticMellinCoefficient M hM V hV hV' ρ
  let G := fullStructuredHeightMass R H 1 e ℓ u (W r) X
  let B := Kn*J*(L r)^2/(1+Real.log (L r))^k
  have hT1 : 1 ≤ T := one_le_pow₀ (by linarith)
  have hTp : 0 < T := zero_lt_one.trans_le hT1
  have hX : ∀ i, 1 ≤ X i := fun i => (Real.one_le_rpow hL hc.le).trans (hrough i)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg := continuous_fullStructuredHeightMass R H 1 e ℓ u (W r) X
  have hg0 := fullStructuredHeightMass_nonneg R H 1 e ℓ u (W r) X
  obtain ⟨B₀,_hB₀,hB₀⟩ := fullStructuredHeightMass_bounded R H 1 e ℓ u (W r) X
  have hfi : Integrable (fun t => (1+ρ)^q*‖F t‖) :=
    (arithmeticMellinCoefficient_integrable M hM V hV hV' ρ).norm.const_mul _
  have hfg : Integrable (fun t => ((1+ρ)^q*‖F t‖)*G t) :=
    hfi.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hg0 t)]; exact hB₀ t))
  have hn : ∀ t : ℝ, |t| < T → G t ≤ B := by
    intro t ht
    have hs := log_height_translate hz A U ht.le hu
    simpa only [G,B,fullStructuredHeightMass,←fullStructuredAngularPrimeSum_eq_existing ℓ] using
      hnear r X J H hTn hprod hrough hJ hJL hH e he heL (t+u) hs
  have ht := htail r X J H hL hTt hX hprod hJ hH 1 e ℓ u T ρ le_rfl hρ
  dsimp only at ht
  have htail' : (∫ t in Ici T, ((1+ρ)^q*‖F t‖)*G t)+
      (∫ t in Ici T, ((1+ρ)^q*‖F (-t)‖)*G (-t)) ≤
      Kt*J*(L r)^2/(1+Real.log (L r))^k := by
    simp only [mul_assoc,integral_const_mul]
    dsimp only [F,G]
    rw [← mul_add]
    apply ht.trans
    rw [div_mul_eq_div_div]
    have hbase : 0 ≤ Kt*J*(L r)^2/(1+Real.log (L r))^k := by positivity
    simpa only [mul_assoc] using div_le_self hbase hT1
  have hi := integral_local_and_signed_tail hfi (fun t => by positivity) hfg hTp hB hn htail'
  have hm : (∫ t : ℝ, (1+ρ)^q*‖F t‖) ≤ D := by
    rw [integral_const_mul]
    simpa only [pow_zero,one_mul] using hmoment ρ hρ
  have hi' := hi.trans (add_le_add (mul_le_mul_of_nonneg_left hm hB) le_rfl)
  simp only [mul_assoc,integral_const_mul] at hi'
  convert hi' using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [B,F,G]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLowCoreMonotone
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotonicity permits the harmless enlargement of a zero logarithmic
core exponent without changing the actual frequency set being estimated. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_low_core_mellin_integral_all_exponents (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    {C R c d₁ d₂ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hR : 1 ≤ R) (hc : 0 < c) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (a k U q : ℕ) :
    ∃ K T₀ : ℝ, 0 ≤ K ∧ ∀ (r : γ) (X : ι → ℝ) (J : ℝ) (H : Finset Eisenstein),
      T₀ ≤ L r → (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      0 ≤ J → J ≤ (L r)^d₂ → H ⊆ lowNoncubeSupport ((Real.log (L r))^a) J →
      ∀ (e : Eisenstein) (u ρ : ℝ), e ≠ 0 → norm e ≤ (L r)^d₁ →
      |u| ≤ (1+Real.log (L r))^U → 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*
        fullStructuredHeightMass R H 1 e ℓ u (W r) X t) ≤
          K*J*(L r)^2/(1+Real.log (L r))^k := by
  obtain ⟨K,T₀,hK,hb⟩ := angular_low_core_mellin_integral_saving ℓ hSW hℓ hMV hC hR hc hd₁ hd₂
    hW hlo hhi M hM V hV hV' (a+1) k U q (by omega)
  refine ⟨K,max T₀ (Real.exp 1),hK,?_⟩
  intro r X J H hT hprod hX hJ hJL hH e u ρ he heN hu hρ
  have hL : 0 < L r := zero_lt_one.trans_le (hW.length_one (r,Classical.arbitrary ι))
  have hlog : 1 ≤ Real.log (L r) :=
    (Real.le_log_iff_exp_le hL).mpr ((le_max_right _ _).trans hT)
  have hm := lowNoncubeSupport_mono
    (pow_le_pow_right₀ hlog (Nat.le_succ a)) (le_refl J)
  exact hb r X J H ((le_max_left _ _).trans hT) hprod hX hJ hJL
    (hH.trans hm) e u ρ he heN hu hρ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularNoncubeMellinIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All finite noncube frequencies, over the full Mellin line. The
low-core and large-core arguments are now combined without truncating
or modifying the original independent prime coefficients. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_noncube_mellin_integral_saving (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k U q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (H : Finset Eisenstein) (e : Eisenstein) (u ρ : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U → 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*
        fullStructuredHeightMass R H 1 e ℓ u (W r) X t) ≤
          K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hlarge⟩ := angular_large_core_mellin_integral_saving ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hGI hGQ M hM V hV hV' k q
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨Kg,Tg,a,hKg,hlarge⟩ := hlarge L W hL hW hlo hhi
  obtain ⟨Kl,Tl,hKl,hlow⟩ := angular_low_core_mellin_integral_all_exponents ℓ hSW hℓ hMV hC hR hc
    hσ.le (by norm_num : (0:ℝ) ≤ 1) hW hlo hhi M hM V hV hV' a k U q
  have hheight := exclusion_log_absorption (c := 1/4) (d := 0) (ε := 1) (C := 1)
    (by norm_num) (by norm_num) (by norm_num) U 0
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp ((eventually_ge_atTop Tg).and
    ((eventually_ge_atTop Tl).and hheight))
  refine ⟨Kl+Kg,T₀,by positivity,?_⟩
  intro r X B H e u ρ hT hprod hX hB hBL hH he heN hu hρ
  obtain ⟨hTg,hTl,hheight⟩ := hT₀ (L r) hT
  let J := B^(1/3:ℝ)
  let P := fun h : Eisenstein => h ∈ lowNoncubeSupport ((Real.log (L r))^a) J
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hB2 : B ≤ (L r)^2 := by
    apply hBL.trans
    rw [← Real.rpow_natCast (L r) 2]
    exact Real.rpow_le_rpow_of_exponent_le (hL r) (by norm_num; linarith)
  have hJ : 0 ≤ J := Real.rpow_nonneg (zero_le_one.trans hB) _
  have hJL : J ≤ (L r)^(1:ℝ) := by
    simpa only [Real.rpow_one] using cube_cutoff_le_length (zero_le_one.trans hB) (hL r) hB2
  have hrough : ∀ i, (L r)^c ≤ X i := by
    intro i
    exact (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans (hX i).le
  have hulo : |u| ≤ (L r)^(1/4:ℝ) := by
    have hh := hheight ((L r)^(1/4:ℝ)) 1 (by norm_num) (by simp) le_rfl
    simp only [Real.one_rpow,one_mul,pow_zero,div_one] at hh
    exact hu.trans hh
  have hl := hlow r X J (H.filter P) hTl hprod hrough hJ hJL
    (fun h hh => (Finset.mem_filter.mp hh).2) e u ρ he heN hu hρ
  have hg := hlarge r X B (H.filter (fun h => ¬P h)) e u ρ hTg hprod hX hB hBL
    (fun h hh => ⟨(hH h (Finset.mem_filter.mp hh).1).1,
      (hH h (Finset.mem_filter.mp hh).1).2.1,
      (hH h (Finset.mem_filter.mp hh).1).2.2,(Finset.mem_filter.mp hh).2⟩) he heN hulo hρ
  rw [weighted_height_mass_partition
    (arithmeticMellinCoefficient_integrable M hM V hV hV' ρ).norm R H P 1 e ℓ u (W r) X,mul_add]
  refine (le_of_eq ?_).trans ((add_le_add hl hg).trans_eq ?_)
  · congr 4
    all_goals
      funext t
      congr 2
      apply Finset.filter_congr_decidable
  · symm
    try dsimp only [J]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularNoncubeReflectedIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full noncube integral estimate for the reflected radial kernel.
This is deduced by conjugating the original smooth weight. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_noncube_mellin_reflected_integral_saving (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k U q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (H : Finset Eisenstein) (e : Eisenstein) (u ρ : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U → 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ (-t)‖*
        fullStructuredHeightMass R H 1 e ℓ u (W r) X t) ≤
          K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  have hVc : HasCompactSupport (fun x => star (V x)) :=
    hV.comp_left (show star (0:ℂ) = 0 from star_zero _)
  have hVc' : ContDiff ℝ ∞ (fun x => star (V x)) :=
    Complex.conjCLE.contDiff.comp hV'
  have he := angular_noncube_mellin_integral_saving ℓ (γ := γ) (ι := ι)
    hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    M hM (fun x => star (V x)) hVc hVc' k U q
  simpa only [arithmeticMellinCoefficient_conj M hM V hV hV' hVc hVc',norm_star] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSignedNoncubeIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both literal Poisson row signs, with a common range of exponents and
with the exact Fourier-to-arithmetic Jacobian. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_noncube_signed_mellin_integral_saving (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k U q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (H : Finset Eisenstein) (e : Eisenstein) (u ρ : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U → 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖*
        ((fullStructuredHeightMass R H 1 e ℓ u (W r) X (2*Real.pi*t)+
          fullStructuredHeightMass R H 1 e ℓ u (W r) X (-(2*Real.pi*t)))/2)) ≤
          K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η₁,σ₁,hη₁,hη₁',hσ₁,hplus⟩ := angular_noncube_mellin_integral_saving ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    M hM V hV hV' k U q
  obtain ⟨η₂,σ₂,hη₂,hη₂',hσ₂,hminus⟩ := angular_noncube_mellin_reflected_integral_saving ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    M hM V hV hV' k U q
  refine ⟨min η₁ η₂,min σ₁ σ₂,lt_min hη₁ hη₂,(min_le_left _ _).trans hη₁',
    lt_min hσ₁ hσ₂,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K₁,T₁,hK₁,hplus⟩ := hplus L W hL hW hlo hhi
  obtain ⟨K₂,T₂,hK₂,hminus⟩ := hminus L W hL hW hlo hhi
  refine ⟨(K₁+K₂)/(4*Real.pi),max T₁ T₂,by positivity,?_⟩
  intro r X B H e u ρ hT hprod hX hB hBL hH he heN hu hρ
  have hB₁ : B ≤ (L r)^(1+η₁) := hBL.trans
    (Real.rpow_le_rpow_of_exponent_le (hL r) (add_le_add le_rfl (min_le_left _ _)))
  have hB₂ : B ≤ (L r)^(1+η₂) := hBL.trans
    (Real.rpow_le_rpow_of_exponent_le (hL r) (add_le_add le_rfl (min_le_right _ _)))
  have he₁ : norm e ≤ (L r)^σ₁ := heN.trans
    (Real.rpow_le_rpow_of_exponent_le (hL r) (min_le_left _ _))
  have he₂ : norm e ≤ (L r)^σ₂ := heN.trans
    (Real.rpow_le_rpow_of_exponent_le (hL r) (min_le_right _ _))
  have hp := hplus r X B H e u ρ ((le_max_left _ _).trans hT)
    hprod hX hB hB₁ hH he he₁ hu hρ
  have hn := hminus r X B H e u ρ ((le_max_right _ _).trans hT)
    hprod hX hB hB₂ hH he he₂ hu hρ
  rw [normMellin_signed_height_integral]
  calc
    _ = ((1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*
        fullStructuredHeightMass R H 1 e ℓ u (W r) X t)+
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ (-t)‖*
        fullStructuredHeightMass R H 1 e ℓ u (W r) X t))/(4*Real.pi) := by ring
    _ ≤ (K₁*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k+
        K₂*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k)/(4*Real.pi) :=
      div_le_div_of_nonneg_right (add_le_add hp hn) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCoprimeNoncubeIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coprime Poisson mass has a full-line logarithmic saving.
Both signs and all common divisors are retained. Published inputs occur
only in the already proved empty-row noncube estimate. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_coprime_noncube_mellin_integral_saving_oai (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k U q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (H P : Finset Eisenstein) (e : Eisenstein) (u ρ N : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      (∀ p ∈ P, primaryPrime p) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U → 0 ≤ ρ → 0 < N →
      (1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖*
        coprimeMellinMass (fullSquarefreePrimeSupport R (W r) X e) H P
          (fun a => star (angularHeightPrimeCoefficient ℓ R (W r) X a*mellinPhase u (norm a)))
          (fun a => star (angularHeightPrimeCoefficient ℓ R (W r) X a*mellinPhase u (norm a)))
          (fun a => norm a/N) t) ≤
          K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hempty⟩ := angular_noncube_signed_mellin_integral_saving ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    M hM V hV hV' k U q
  obtain ⟨C₀,hC₀,hkernel⟩ := normDenominatorMellinCoefficient_moment_decay M hM V hV hV' q 0
  refine ⟨min η (c/4),σ,lt_min hη (by positivity),
    (min_le_left _ _).trans hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K₁,T₁,hK₁,hempty⟩ := hempty L W hL hW hlo hhi
  obtain ⟨K₂,T₂,hK₂,hlarge⟩ := angular_fullPrime_large_divisor_log_saving ℓ hR hc hc₁ hW hlo hhi k
  refine ⟨K₁+K₂*C₀,max T₁ T₂,by positivity,?_⟩
  intro r X B H P e u ρ N hT hprod hX hB hBL hH hP he heN hu hρ hN
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hX₁ : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le
  have hrough : ∀ i, (L r)^c < X i := fun i =>
    (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hX i)
  have hB₁ := hBL.trans (Real.rpow_le_rpow_of_exponent_le (hL r)
    (add_le_add le_rfl (min_le_left η (c/4))))
  have hB₂ := hBL.trans (Real.rpow_le_rpow_of_exponent_le (hL r)
    (add_le_add le_rfl (min_le_right η (c/4))))
  have hs := hempty r X B H e u ρ ((le_max_left _ _).trans hT)
    hprod hX hB hB₁ hH he heN hu hρ
  have hl := fun t => hlarge r X B e H P u t N ((le_max_right _ _).trans hT)
    (hL r) hX₁ hprod hB hB₂ (fun h hh => ⟨(hH h hh).1,(hH h hh).2.1⟩) hP hN
  have hi := angular_fullPrime_coprime_mass_integral_le ℓ (Real.one_le_rpow (hL r) hc.le)
    (W r) X (fun i => zero_lt_one.trans_le (hX₁ i)) (hlo r) (hhi r) hrough e H P hP u hN
    (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).norm
    (fun _ => _root_.norm_nonneg _) hl
  have hk := hkernel ρ hρ
  simp only [pow_zero,one_mul] at hk
  calc
    _ ≤ (1+ρ)^q*((∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖*
        ((fullStructuredHeightMass R H 1 e ℓ u (W r) X (2*Real.pi*t)+
          fullStructuredHeightMass R H 1 e ℓ u (W r) X (-(2*Real.pi*t)))/2))+
        (K₂*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k)*
          (∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖*
        ((fullStructuredHeightMass R H 1 e ℓ u (W r) X (2*Real.pi*t)+
          fullStructuredHeightMass R H 1 e ℓ u (W r) X (-(2*Real.pi*t)))/2))+
        (K₂*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k)*
          ((1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖)) := by ring
    _ ≤ K₁*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k+
        (K₂*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k)*C₀ :=
      add_le_add hs (mul_le_mul_of_nonneg_left hk (by positivity))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CubicFirstMoment.angular_coprime_noncube_mellin_integral_saving_oai.{u_1, u_2} := @OAI.CubicFirstMoment.angular_coprime_noncube_mellin_integral_saving_oai.{u_1, u_2}
