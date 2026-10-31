-- Prove2me | solution 1 for OAI.CubicFirstMoment.first_common_prime_exponents
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:36:30.182368+00:00
-- url     : https://prove2.me/submissions/70ad4a93-7030-4b2a-a391-dbb0fe1bb937

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_first_primeCoordinateError_moment
import Theorems.Thm_OAI_CubicFirstMoment_first_weighted_tuple_neighborhood

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite-order Hecke prime input

The finite-order Hecke prime-sum input specializes to independent prime
factors using the elementary character laws.

The input is the cubic-character consequence of Thorner--Zaman,
*A unified and improved Chebotarev density theorem*, Algebra & Number
Theory 13 (2019), Theorem 1.4, in the Siegel–Walfisz form for cubic Hecke characters.  Only finite-order characters occur in this input;
smooth weights and norm twists follow by partial summation.
-/

noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CubicFirstMoment

/-- The character of an ordered tuple splits into the characters of its
individual factors. Repeated prime factors are still permitted here;
the squarefree restriction in the manuscript is imposed separately. -/
theorem mixedCubic_prod {ι : Type*} (s : Finset ι) (f : ι → Eisenstein)
    {q₁ q₂ : Eisenstein} (h₁ : primary q₁) (h₂ : primary q₂) :
    mixedCubic q₁ q₂ (∏ i ∈ s, f i) = ∏ i ∈ s, mixedCubic q₁ q₂ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mixedCubic_one h₁ h₂]
  | @insert i s hi ih => simp [hi, mixedCubic_mul h₁ h₂, ih]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialMeanValue
attribute [-instance] _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma norm_mixedCubic_le_one {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) (b : Eisenstein) :
    ‖mixedCubic q₁ q₂ b‖ ≤ 1 := by
  rw [mixedCubic, norm_mul, norm_star]
  simpa only [mul_one] using
    mul_le_mul (norm_cubicSymbol_le_one h₁ b) (norm_cubicSymbol_le_one h₂ b)
      (_root_.norm_nonneg _) zero_le_one

end CubicFirstMoment

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma idealZeta_mul_moebiusSeries : idealZeta * idealMoebiusSeries = 1 := by
  rw [mul_comm, idealMoebiusSeries_mul_zeta]

private lemma exponent_fst_le {ν : EisensteinIdealExponent}
    {p : EisensteinIdealExponent × EisensteinIdealExponent}
    (hp : p ∈ Finset.HasAntidiagonal.antidiagonal ν) :
    p.1 ≤ ν := by
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← h]
  exact le_add_of_nonneg_right zero_le

/-- The truncated Möbius inverse agrees with the full inverse on every
divisor of an ideal whose norm is at most the truncation threshold. -/
lemma shortMoebiusResidual_low_norm (F : ℝ) (ν : EisensteinIdealExponent)
    (hν : idealExponentNorm ν ≤ Real.sqrt F) :
    MvPowerSeries.coeff ν (shortMoebiusResidual F) = 0 := by
  have he : MvPowerSeries.coeff ν (shortIdealMoebius F * idealZeta) =
      MvPowerSeries.coeff ν (idealMoebiusSeries * idealZeta) := by
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hn := (idealExponentNorm_mono (exponent_fst_le hp)).trans hν
    simp only [MvPowerSeries.coeff_apply, shortIdealMoebius, ite_eq_left hn]
  change MvPowerSeries.coeff ν (1 - shortIdealMoebius F * idealZeta) = 0
  rw [map_sub, he, idealMoebiusSeries_mul_zeta, sub_self]

/-- Both nonzero factors of the residual must have norm greater than
`sqrt F`; hence its square vanishes throughout the actual norm ball `F`. -/
lemma shortMoebiusResidual_sq_low_norm {F : ℝ} (hF : 0 ≤ F)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν ((shortMoebiusResidual F) ^ 2) = 0 := by
  rw [pow_two, MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hfst : idealExponentNorm p.1 ≤ Real.sqrt F
  · rw [shortMoebiusResidual_low_norm F p.1 hfst, zero_mul]
  · have hsnd : idealExponentNorm p.2 ≤ Real.sqrt F := by
      have hprod : idealExponentNorm p.1 * idealExponentNorm p.2 ≤ F := by
        rw [← idealExponentNorm_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
        exact hν
      have hroot := Real.sqrt_nonneg F
      have hsq := Real.sq_sqrt hF
      by_contra h
      have ha := lt_of_not_ge hfst
      have hb := lt_of_not_ge h
      nlinarith
    rw [shortMoebiusResidual_low_norm F p.2 hsnd, mul_zero]

lemma shortMoebiusResidual_sq_mul_low_norm {F : ℝ} (hF : 0 ≤ F)
    (L : EisensteinArithmeticFunction) (ν : EisensteinIdealExponent)
    (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν ((shortMoebiusResidual F) ^ 2 * L) = 0 := by
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [shortMoebiusResidual_sq_low_norm hF p.1
    ((idealExponentNorm_mono (exponent_fst_le hp)).trans hν), zero_mul]

lemma idealZeta_mul_vonMangoldt : idealZeta * idealVonMangoldt = idealLogNorm := by
  rw [idealVonMangoldt, ← mul_assoc, idealZeta_mul_moebiusSeries, one_mul]

/-- The short Möbius convolution identity throughout the sharp norm ball. -/
theorem short_moebius_identity {F : ℝ} (hF : 0 ≤ F)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      MvPowerSeries.coeff ν
        ((2 * shortIdealMoebius F - shortIdealMoebius F * shortIdealMoebius F * idealZeta) *
          idealLogNorm) := by
  have halg : idealVonMangoldt -
      (2 * shortIdealMoebius F - shortIdealMoebius F * shortIdealMoebius F * idealZeta) *
        (idealZeta * idealVonMangoldt) = (shortMoebiusResidual F) ^ 2 * idealVonMangoldt := by
    unfold shortMoebiusResidual
    ring
  have h := congrArg (MvPowerSeries.coeff ν) halg
  rw [map_sub, idealZeta_mul_vonMangoldt,
    shortMoebiusResidual_sq_mul_low_norm hF idealVonMangoldt ν hν] at h
  exact sub_eq_zero.mp h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealVonMangoldt
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The convolution definition of ideal von Mangoldt has exactly its usual
prime-power coefficients. This is the arithmetic bridge for prime replacement
in the short Möbius decomposition. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealLogNorm_prime_difference (ν : EisensteinIdealExponent)
    (p : EisensteinIdealPrime) (hp : 1 ≤ ν p) :
    MvPowerSeries.coeff ν idealLogNorm -
        MvPowerSeries.coeff (ν - Finsupp.single p 1) idealLogNorm =
      Real.log (normNat (idealPrimeRepresentative p)) := by
  have hle : Finsupp.single p 1 ≤ ν := Finsupp.single_le_iff.mpr hp
  have he : ν = (ν - Finsupp.single p 1) + Finsupp.single p 1 :=
    (tsub_add_cancel_of_le hle).symm
  change Real.log (idealExponentNorm ν) -
    Real.log (idealExponentNorm (ν - Finsupp.single p 1)) = _
  conv_lhs => lhs; rw [he, idealExponentNorm_add]
  rw [Real.log_mul (idealExponentNorm_pos _).ne' (idealExponentNorm_pos _).ne',
    idealExponentNorm_single, pow_one]
  ring

private lemma coeff_logNorm_finite_nonempty (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) (hS : S.Nonempty) (hν : S ⊆ ν.support) :
    MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius S) =
      if S.card = 1 then ∑ p ∈ S, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty => exact (Finset.not_nonempty_empty hS).elim
  | @insert p S hp ih =>
    have hνp : 1 ≤ ν p := Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp (hν (Finset.mem_insert_self _ _)))
    have he : idealLogNorm * finiteIdealMoebius (insert p S) =
        (idealLogNorm * finiteIdealMoebius S) * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, mul_sub, mul_one, map_sub, MvPowerSeries.X_def,
      MvPowerSeries.coeff_mul_monomial]
    simp only [Finsupp.single_le_iff, ite_eq_left hνp, mul_one]
    by_cases hSE : S = ∅
    · subst S
      simpa [finiteIdealMoebius] using idealLogNorm_prime_difference ν p hνp
    · have hS' : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSE
      have hνS : S ⊆ ν.support := fun q hq => hν (Finset.mem_insert_of_mem hq)
      have hνS' : S ⊆ (ν - Finsupp.single p 1 : EisensteinIdealExponent).support := by
        intro q hq
        apply Finsupp.mem_support_iff.mpr
        have hqp : q ≠ p := ne_of_mem_of_not_mem hq hp
        simpa [Finsupp.tsub_apply, hqp] using Finsupp.mem_support_iff.mp (hνS hq)
      rw [ih ν hS' hνS, ih _ hS' hνS', sub_self]
      have hc : (insert p S).card ≠ 1 := by
        rw [Finset.card_insert_of_notMem hp]
        have := Finset.card_pos.mpr hS'
        omega
      simp [hc]

lemma idealVonMangoldt_coeff_eq_finite (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius ν.support) := by
  rw [idealVonMangoldt, mul_comm idealLogNorm, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hle : a.1 ≤ ν := by
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp ha]
    exact le_add_of_nonneg_right zero_le
  rw [coeff_idealMoebiusSeries_eq_finite ν.support a.1 (Finsupp.support_mono hle)]

/-- The von Mangoldt coefficient is supported precisely on prime-ideal
powers and has weight the logarithm of that prime-ideal norm. -/
lemma idealVonMangoldt_coeff (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      if ν.support.card = 1 then
        ∑ p ∈ ν.support, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  rw [idealVonMangoldt_coeff_eq_finite]
  by_cases hs : ν.support.Nonempty
  · exact coeff_logNorm_finite_nonempty _ _ hs (Finset.Subset.refl _)
  · have hz : ν = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
    subst ν
    simp only [Finsupp.support_zero, finiteIdealMoebius, Finset.prod_empty, mul_one,
      Finset.card_empty, Nat.zero_ne_one, ite_false, if_false]
    change Real.log (idealExponentNorm 0) = 0
    simp [idealExponentNorm, idealExponentGenerator]

lemma idealVonMangoldt_not_prime_power (ν : EisensteinIdealExponent)
    (hν : ν.support.card ≠ 1) :
    MvPowerSeries.coeff ν idealVonMangoldt = 0 := by
  rw [idealVonMangoldt_coeff, ite_eq_right hν]

lemma idealVonMangoldt_coeff_nonneg (ν : EisensteinIdealExponent) :
    0 ≤ MvPowerSeries.coeff ν idealVonMangoldt := by
  rw [idealVonMangoldt_coeff]
  split_ifs
  · apply Finset.sum_nonneg
    intro p hp
    apply Real.log_nonneg
    simpa only [idealExponentNorm_single, pow_one] using
      idealExponentNorm_ge_one (Finsupp.single p 1)
  · exact le_rfl

lemma idealVonMangoldt_coeff_le_logNorm (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt ≤ Real.log (idealExponentNorm ν) := by
  by_cases hc : ν.support.card = 1
  · obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hc
    have hlog : 0 ≤ Real.log (normNat (idealPrimeRepresentative p)) := by
      apply Real.log_nonneg
      simpa only [idealExponentNorm_single, pow_one] using
        idealExponentNorm_ge_one (Finsupp.single p 1)
    have hn : (1 : ℝ) ≤ (ν p : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
    rw [idealVonMangoldt_coeff, ite_eq_left hc, he, Finsupp.support_single _ hp,
      Finset.sum_singleton, idealExponentNorm_single, Real.log_pow]
    exact le_mul_of_one_le_left hlog hn
  · rw [idealVonMangoldt_not_prime_power ν hc]
    exact Real.log_nonneg (idealExponentNorm_ge_one ν)

lemma idealVonMangoldt_coeff_abs_le_logNorm (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν idealVonMangoldt| ≤ Real.log (idealExponentNorm ν) := by
  rw [abs_of_nonneg (idealVonMangoldt_coeff_nonneg ν)]
  exact idealVonMangoldt_coeff_le_logNorm ν

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_AllShortNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conductor-neighborhood savings for the literal short factors,
with cardinality and amplitude bounds derived from their finite supports. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma neighborhood_cubic_card (S : Finset Eisenstein) {Y N : ℝ}
    (hY : 36 ≤ Y) (hN : 1 ≤ N) (hNY : N ≤ Y^2)
    (hS : ∀ p ∈ S, gramDyad N p) : (S.card:ℝ) ≤ Y^4 := by
  have hsub : S ⊆ nonzeroNormBall (2*N) := fun p hp =>
    mem_nonzeroNormBall.mpr ⟨(hS p hp).2.2.2.le,primary_ne_zero (hS p hp).1⟩
  have hc := (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)).trans
    (nonzeroNormBall_card_le (show 0 ≤ 2*N by positivity))
  calc
    _ ≤ 36*N := by linarith
    _ ≤ 36*Y^2 := by gcongr
    _ ≤ Y^2*Y^2 := by gcongr; nlinarith
    _ = _ := by ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueIdealCharacters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite residue character as an actual complete ideal character,
and exact restoration of Euler factors after primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma residueIdealChar_add (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ν κ : EisensteinIdealExponent) :
    residueIdealChar q χ (ν+κ) = residueIdealChar q χ ν*residueIdealChar q χ κ := by
  simp only [residueIdealChar,idealExponentGenerator_add,map_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ConductorLocal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local detection of the squarefree cubic conductor. A nontrivial
prime character survives every inducing modulus, as witnessed by CRT. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma residueIdealChar_primaryNormalize {d : Eisenstein} (ψ : MulChar (Residues d) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (ν : EisensteinIdealExponent) :
    residueIdealChar d ψ ν = ψ (Ideal.Quotient.mk (modulus d) (idealPrimaryGenerator ν)) := by
  obtain ⟨u,hassoc⟩ := primaryNormalize_associated (idealExponentGenerator ν)
  change ψ (Ideal.Quotient.mk (modulus d) (idealExponentGenerator ν)) =
    ψ (Ideal.Quotient.mk (modulus d) (primaryNormalize (idealExponentGenerator ν)))
  rw [← hassoc,map_mul,map_mul,hu,mul_one]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusProducts
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short Möbius identity remains valid inside any fixed product of
prime-weight factors. This is the algebraic replacement before smoothing. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma shortVonMangoldt_two_four (F : ℝ) :
    shortVonMangoldt F = 2*shortTwoFactor F-shortFourFactor F := by
  unfold shortVonMangoldt shortTwoFactor shortFourFactor
  ring

lemma shortVonMangoldt_local {F : ℝ} (hF : 0 ≤ F) :
    NormLocalEq F idealVonMangoldt (shortVonMangoldt F) :=
  fun ν hν => short_moebius_identity hF ν hν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArithmeticTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Twisting actual ideal arithmetic functions by a residue character and
norm phase commutes with convolution. Different original factors may
therefore retain different Mellin heights throughout short inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma residueNormTwist_add (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (ν κ : EisensteinIdealExponent) :
    residueNormTwist q η t (ν+κ) = residueNormTwist q η t ν*residueNormTwist q η t κ := by
  rw [residueNormTwist,residueIdealChar_add,idealExponentNorm_add,
    mellinPhase_mul_pos t (idealExponentNorm_pos ν) (idealExponentNorm_pos κ)]
  unfold residueNormTwist
  ring

lemma twistArithmetic_mul (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A B : EisensteinArithmeticFunction) :
    twistArithmetic q η t (A*B) = twistArithmetic q η t A*twistArithmetic q η t B := by
  apply MvPowerSeries.ext
  intro ν
  change ((MvPowerSeries.coeff ν (A*B):ℝ):ℂ)*residueNormTwist q η t ν = _
  rw [MvPowerSeries.coeff_mul,Complex.ofReal_sum,Finset.sum_mul,MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  change ((MvPowerSeries.coeff p.1 A*MvPowerSeries.coeff p.2 B:ℝ):ℂ)*
      residueNormTwist q η t ν = _
  rw [← he,residueNormTwist_add,Complex.ofReal_mul]
  change _ = (((MvPowerSeries.coeff p.1 A:ℝ):ℂ)*residueNormTwist q η t p.1)*
    (((MvPowerSeries.coeff p.2 B:ℝ):ℂ)*residueNormTwist q η t p.2)
  ring

lemma twistArithmetic_add (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A B : EisensteinArithmeticFunction) :
    twistArithmetic q η t (A+B) = twistArithmetic q η t A+twistArithmetic q η t B := by
  ext ν
  change ((MvPowerSeries.coeff ν (A+B):ℝ):ℂ)*residueNormTwist q η t ν =
    ((MvPowerSeries.coeff ν A:ℝ):ℂ)*residueNormTwist q η t ν +
      ((MvPowerSeries.coeff ν B:ℝ):ℂ)*residueNormTwist q η t ν
  rw [map_add,Complex.ofReal_add,add_mul]

lemma twistArithmetic_sub (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A B : EisensteinArithmeticFunction) :
    twistArithmetic q η t (A-B) = twistArithmetic q η t A-twistArithmetic q η t B := by
  ext ν
  change ((MvPowerSeries.coeff ν (A-B):ℝ):ℂ)*residueNormTwist q η t ν =
    ((MvPowerSeries.coeff ν A:ℝ):ℂ)*residueNormTwist q η t ν -
      ((MvPowerSeries.coeff ν B:ℝ):ℂ)*residueNormTwist q η t ν
  rw [map_sub,Complex.ofReal_sub,sub_mul]

lemma twistArithmetic_coeff_primary (q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (hu : ∀ e : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) e) = 1)
    (t : ℝ) (A : EisensteinArithmeticFunction) {n : Eisenstein} (hn : primary n) :
    MvPowerSeries.coeff (idealExponentOf n) (twistArithmetic q η t A) =
      ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
        η (Ideal.Quotient.mk (modulus q) n)*mellinPhase t (norm n) := by
  change ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
    (residueIdealChar q η (idealExponentOf n)*mellinPhase t (idealExponentNorm (idealExponentOf n))) = _
  rw [residueIdealChar_primaryNormalize η hu,idealPrimaryGenerator_at_element hn,
    idealExponentOf_norm (primary_ne_zero hn)]
  ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinMomentTransfer
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing an actual uniform finite-row moment through an integrable Mellin
weight. The proof is the triangle inequality in the finite Euclidean space. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem finite_row_integral_moment {Ω κ : Type*} [MeasurableSpace Ω]
    [Fintype κ] {μ : Measure Ω} (f : κ → Ω → ℂ) (w : Ω → ℂ)
    (hf : AEStronglyMeasurable (fun t => WithLp.toLp 2 (fun r => f r t)) μ)
    (hw : Integrable w μ) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ᵐ t ∂μ, (∑ r, ‖f r t‖^2) ≤ B) :
    (∑ r, ‖∫ t, w t*f r t ∂μ‖^2) ≤ (∫ t, ‖w t‖ ∂μ)^2*B := by
  let F : Ω → EuclideanSpace ℂ κ := fun t => WithLp.toLp 2 (fun r => f r t)
  let G : Ω → EuclideanSpace ℂ κ := fun t => w t • F t
  have hFn : ∀ᵐ t ∂μ, ‖F t‖ ≤ Real.sqrt B := by
    filter_upwards [hb] with t ht
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_sqrt ht
  have hGn : ∀ᵐ t ∂μ, ‖G t‖ ≤ ‖w t‖*Real.sqrt B := by
    filter_upwards [hFn] with t ht
    dsimp [G]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ht (_root_.norm_nonneg _)
  have hG : Integrable G μ := (hw.norm.mul_const (Real.sqrt B)).mono'
    (hw.aestronglyMeasurable.smul hf) hGn
  have hcoord (r : κ) : (∫ t, G t ∂μ) r = ∫ t, w t*f r t ∂μ := by
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : κ => ℂ) r).integral_comp_comm hG).symm
  have hbound : ‖∫ t, G t ∂μ‖ ≤ (∫ t, ‖w t‖ ∂μ)*Real.sqrt B := by
    apply (norm_integral_le_integral_norm G).trans
    rw [← integral_mul_const]
    exact integral_mono_ae hG.norm (hw.norm.mul_const _) hGn
  calc
    _ = ‖∫ t, G t ∂μ‖^2 := by rw [EuclideanSpace.norm_sq_eq]; simp_rw [hcoord]
    _ ≤ ((∫ t, ‖w t‖ ∂μ)*Real.sqrt B)^2 :=
      pow_le_pow_left₀ (_root_.norm_nonneg _) hbound 2
    _ = _ := by rw [mul_pow,Real.sq_sqrt hB]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullMellinMoment
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joining the central Mellin moment to a proved rapid tail bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma norm_square_le_central_tail (x y : ℂ) {H : ℝ} (h : ‖x-y‖ ≤ H) :
    ‖x‖^2 ≤ 2*‖y‖^2+2*H^2 := by
  have hx : ‖x‖ ≤ ‖y‖+H := by
    calc
      _ = ‖y+(x-y)‖ := by congr 1; ring
      _ ≤ ‖y‖+‖x-y‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl h
  have hH : 0 ≤ H := (_root_.norm_nonneg _).trans h
  have hsq := pow_le_pow_left₀ (_root_.norm_nonneg _) hx 2
  nlinarith [sq_nonneg (‖y‖-H),sq_nonneg ‖x‖]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinMomentPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed powers in the central-plus-tail short-convolution estimate. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem absorb_short_mellin_bounds {ε : ℝ} (hε : 0 < ε) (C E : ℝ)
    (hC : 0 ≤ C) (hE : 0 ≤ E) :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      C*Y^(7/3-ε)+E*Y^(-42/5:ℝ) ≤ Y^(7/3-min ε (1/3)/2) := by
  let η := min ε (1/3:ℝ)
  have hη : 0 < η := lt_min hε (by norm_num)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < η/2 by linarith)).eventually_ge_atTop (C+E))
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hηε : η ≤ ε := min_le_left _ _
  have hη3 : η ≤ 1/3 := min_le_right _ _
  calc
    _ ≤ C*Y^(7/3-η)+E*Y^(7/3-η) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)) hC
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)) hE
    _ = (C+E)*Y^(7/3-η) := by ring
    _ ≤ Y^(η/2)*Y^(7/3-η) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; dsimp [η]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoordinateNeighborhoodPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint Mellin tail with the larger neighborhood row count. -/
noncomputable section
namespace CubicFirstMoment

lemma coordinate_neighborhood_tail_power (k : ℕ) {Y K J : ℝ} (hY : 0 < Y) :
    2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^(1000*(2*k+7)))*J)^2 =
      (2*K^2*J^2)*Y^(-10:ℝ) := by
  have hp : (Y^(1/1000:ℝ))^(1000*(2*k+7)) = Y^(2*k+7) := by
    rw [← Real.rpow_mul_natCast hY.le]
    have he : (1/1000:ℝ)*(1000*(2*k+7):ℕ) = ((2*k+7:ℕ):ℝ) := by push_cast; ring
    rw [he,Real.rpow_natCast]
  have hd : Y^(2*k)/Y^(2*k+7) = Y^(-7:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_sub hY]
    congr 1
    push_cast
    ring
  rw [hp,show K*Y^(2*k)/Y^(2*k+7) = K*(Y^(2*k)/Y^(2*k+7)) by ring,hd]
  have he : Y^4*(Y^(-7:ℝ))^2 = Y^(-10:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le,← Real.rpow_natCast,← Real.rpow_add hY]
    norm_num
  calc
    _ = (2*K^2*J^2)*(Y^4*(Y^(-7:ℝ))^2) := by ring
    _ = _ := by rw [he]

lemma coordinate_neighborhood_tail_le_short_tail (k : ℕ) {Y K J : ℝ} (hY : 1 ≤ Y) :
    2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^(1000*(2*k+7)))*J)^2 ≤
      (2*K^2*J^2)*Y^(-42/5:ℝ) := by
  rw [coordinate_neighborhood_tail_power k (zero_lt_one.trans_le hY)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation of independent coordinate weights on a finite
arithmetic sum. The joint weight has explicitly factored L1 mass. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellin_point (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {N X : ℝ} (hN : 0 < N) (hX : 0 < X) :
    W (N/X) = ∫ τ : ℝ, zeroLineMellinWeight W X τ*mellinPhase (-τ) N := by
  have h : W (N/X) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W ((τ:ℂ)*Complex.I)*(X:ℂ)^((τ:ℂ)*Complex.I)*
        (N:ℂ)^(-((τ:ℂ)*Complex.I)) := by
    simpa using smooth_mellin_finite (fun _ : Unit => (1:ℂ)) (fun _ : Unit => N)
      (fun _ => hN) W hW hpos hsm 0 hX
  rw [h,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with τ
  rw [mellinPhase_eq_cpow hN]
  have he : ((-τ:ℝ):ℂ)*Complex.I = -((τ:ℂ)*Complex.I) := by push_cast; ring
  rw [he]
  unfold zeroLineMellinWeight
  ring

lemma integrable_zeroLineMellin_phase (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (N : ℝ) :
    Integrable (fun τ : ℝ => zeroLineMellinWeight W X τ*mellinPhase (-τ) N) := by
  have hw := zeroLineMellinWeight_integrable W hW hpos hsm hX
  have hp : Continuous (fun τ : ℝ => mellinPhase (-τ) N) := by
    unfold mellinPhase
    fun_prop
  apply hw.norm.mono' (hw.aestronglyMeasurable.mul hp.aestronglyMeasurable)
  filter_upwards with τ
  change ‖zeroLineMellinWeight W X τ*mellinPhase (-τ) N‖ ≤ ‖zeroLineMellinWeight W X τ‖
  rw [norm_mul,mellinPhase_norm,mul_one]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma independentMellinWeight_integrable (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) :
    Integrable (independentMellinWeight W X) :=
  Integrable.fintype_prod (fun i => zeroLineMellinWeight_integrable (W i) (hW i) (hpos i) (hsm i) (hX i))

lemma independentMellinWeight_mass (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i) :
    (∫ τ : ι → ℝ, ‖independentMellinWeight W X τ‖) = ∏ i, zeroLineMellinMass (W i) := by
  simp only [independentMellinWeight,norm_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun (i : ι) (t : ℝ) => ‖zeroLineMellinWeight (W i) (X i) t‖)]
  simp_rw [zeroLineMellinWeight_mass _ (hX _)]

/-- All original factor weights are separated simultaneously. No cutoff or
Mellin-tail assumption is used in this identity. -/
theorem independent_mellin_finite (a : κ → ℂ) (N : ι → κ → ℝ)
    (hN : ∀ i n, 0 < N i n) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) :
    (∑ n, a n*∏ i, W i (N i n/X i)) =
      ∫ τ : ι → ℝ, independentMellinWeight W X τ *
        ∑ n, a n*∏ i, mellinPhase (-(τ i)) (N i n) := by
  have hi (n : κ) : Integrable (fun τ : ι → ℝ =>
      a n*∏ i, zeroLineMellinWeight (W i) (X i) (τ i)*mellinPhase (-(τ i)) (N i n)) :=
    (Integrable.fintype_prod (fun i =>
      integrable_zeroLineMellin_phase (W i) (hW i) (hpos i) (hsm i) (hX i) (N i n))).const_mul (a n)
  calc
    _ = ∑ n, a n*∫ τ : ι → ℝ,
        ∏ i, zeroLineMellinWeight (W i) (X i) (τ i)*mellinPhase (-(τ i)) (N i n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [integral_fintype_prod_volume_eq_prod (fun (i : ι) (τ : ℝ) =>
        zeroLineMellinWeight (W i) (X i) τ*mellinPhase (-τ) (N i n))]
      simp_rw [← zeroLineMellin_point (W _) (hW _) (hpos _) (hsm _) (hN _ n) (hX _)]
    _ = ∫ τ : ι → ℝ, ∑ n, a n*
        ∏ i, zeroLineMellinWeight (W i) (X i) (τ i)*mellinPhase (-(τ i)) (N i n) := by
      simp_rw [← integral_const_mul]
      exact (integral_finsetSum _ (fun n _ => hi n)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with τ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.prod_mul_distrib]
      unfold independentMellinWeight
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentMellinTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-coordinate tail of the genuine product Mellin weight is bounded
by its explicit finite sum of coordinate moments. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma measurableSet_mellinHeightBox (T : ℝ) : MeasurableSet (mellinHeightBox (ι := ι) T) := by
  have he : mellinHeightBox (ι := ι) T = ⋂ i, {τ : ι → ℝ | |τ i| ≤ T} := by
    ext τ
    simp [mellinHeightBox]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_pi_apply i).abs measurable_const)

omit [DecidableEq ι] in
lemma mellinHeightPower_nonneg (A : ℕ) (τ : ι → ℝ) : 0 ≤ mellinHeightPower A τ :=
  Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg (τ i)) A)

omit [DecidableEq ι] in
lemma mellinHeightPower_large {T : ℝ} (hT : 0 ≤ T) (A : ℕ) {τ : ι → ℝ}
    (hτ : τ ∈ (mellinHeightBox T)ᶜ) : T^A ≤ mellinHeightPower A τ := by
  have h : ∃ i, T < |τ i| := by
    simpa only [mellinHeightBox,mem_compl_iff,mem_ofPred_eq,not_forall,not_le] using hτ
  obtain ⟨i,hi⟩ := h
  exact (pow_le_pow_left₀ hT hi.le A).trans
    (Finset.single_le_sum (fun j _ => pow_nonneg (abs_nonneg (τ j)) A) (Finset.mem_univ i))

omit [DecidableEq ι] in
theorem multivariate_weighted_tail (w : (ι → ℝ) → ℂ) (hw : Integrable w)
    (A : ℕ) (hA : Integrable (fun τ => mellinHeightPower A τ*‖w τ‖))
    {T : ℝ} (hT : 0 < T) :
    (∫ τ in (mellinHeightBox T)ᶜ, ‖w τ‖) ≤
      (∫ τ : ι → ℝ, mellinHeightPower A τ*‖w τ‖)/T^A := by
  apply (le_div_iff₀ (pow_pos hT A)).mpr
  rw [mul_comm,← integral_const_mul]
  apply (integral_mono_ae (hw.norm.restrict.const_mul _) hA.restrict ?_).trans
    (setIntegral_le_integral hA (Filter.Eventually.of_forall
      (fun τ => mul_nonneg (mellinHeightPower_nonneg A τ) (_root_.norm_nonneg _))))
  filter_upwards [ae_restrict_mem (measurableSet_mellinHeightBox T).compl] with τ hτ
  exact mul_le_mul_of_nonneg_right (mellinHeightPower_large hT.le A hτ) (_root_.norm_nonneg _)

lemma prod_one_coordinate (f : ι → ℝ) (i : ι) (c : ℝ) :
    (∏ j, if j=i then c*f j else f j) = c*∏ j, f j := by
  classical
  have he (j : ι) : (if j=i then c*f j else f j) = (if j=i then c else 1)*f j := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

lemma independentMellinWeight_coordinate_moment_integrable
    (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ) (i : ι) :
    Integrable (fun τ : ι → ℝ => |τ i|^A*‖independentMellinWeight W X τ‖) := by
  have hh (j : ι) : Integrable (fun t : ℝ =>
      if j=i then |t|^A*‖zeroLineMellinWeight (W j) (X j) t‖ else
        ‖zeroLineMellinWeight (W j) (X j) t‖) := by
    by_cases hj : j=i
    · simp only [hj,ite_true, if_true]
      exact zeroLineMellinWeight_moment_integrable (W i) (hW i) (hpos i) (hsm i) (hX i) A
    · simp only [hj,ite_false, if_false]
      exact (zeroLineMellinWeight_integrable (W j) (hW j) (hpos j) (hsm j) (hX j)).norm
  have hp := Integrable.fintype_prod hh
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  funext τ
  rw [independentMellinWeight,norm_prod]
  symm
  convert prod_one_coordinate (fun j => ‖zeroLineMellinWeight (W j) (X j) (τ j)‖) i (|τ i|^A) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j=i <;> simp [hj]

lemma independentMellinWeight_moment_integrable
    (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ) :
    Integrable (fun τ : ι → ℝ => mellinHeightPower A τ*‖independentMellinWeight W X τ‖) := by
  simp only [mellinHeightPower,Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _ =>
    independentMellinWeight_coordinate_moment_integrable W X hW hpos hsm hX A i)

omit [DecidableEq ι] in
lemma independentMellinWeight_norm_scale (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (τ : ι → ℝ) :
    ‖independentMellinWeight W X τ‖ = ‖independentMellinWeight W (fun _ => 1) τ‖ := by
  simp only [independentMellinWeight,norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [zeroLineMellinWeight_norm (W i) (hX i),
    zeroLineMellinWeight_norm (W i) (by norm_num)]

omit [DecidableEq ι] in
lemma independentMellinMoment_nonneg (W : ι → ℝ → ℂ) (A : ℕ) :
    0 ≤ independentMellinMoment W A :=
  integral_nonneg (fun τ => mul_nonneg (mellinHeightPower_nonneg A τ) (_root_.norm_nonneg _))

omit [DecidableEq ι] in
lemma independentMellinWeight_moment (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (A : ℕ) :
    (∫ τ : ι → ℝ, mellinHeightPower A τ*‖independentMellinWeight W X τ‖) =
      independentMellinMoment W A := by
  simp_rw [independentMellinWeight_norm_scale W X hX]
  rfl

theorem independentMellinWeight_tail (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ)
    {T : ℝ} (hT : 0 < T) :
    (∫ τ in (mellinHeightBox T)ᶜ, ‖independentMellinWeight W X τ‖) ≤
      independentMellinMoment W A/T^A := by
  have h := multivariate_weighted_tail (independentMellinWeight W X)
    (independentMellinWeight_integrable W X hW hpos hsm hX) A
    (independentMellinWeight_moment_integrable W X hW hpos hsm hX A) hT
  rwa [independentMellinWeight_moment W X hX A] at h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentMellinMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-row L2 transfer for independently separated norm weights, with a
proved tail outside the simultaneous height window. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
lemma finite_box_integral_moment (f : κ → (ι → ℝ) → ℂ)
    (hf : ∀ r, Continuous (f r)) (w : (ι → ℝ) → ℂ) (hw : Integrable w)
    (T B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ τ ∈ mellinHeightBox T, (∑ r, ‖f r τ‖^2) ≤ B) :
    (∑ r, ‖∫ τ in mellinHeightBox T, w τ*f r τ‖^2) ≤
      (∫ τ, ‖w τ‖)^2*B := by
  have hc : Continuous (fun τ => WithLp.toLp 2 (fun r => f r τ)) :=
    (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp (continuous_pi hf)
  have ha : ∀ᵐ τ ∂(volume.restrict (mellinHeightBox T)), (∑ r, ‖f r τ‖^2) ≤ B := by
    filter_upwards [ae_restrict_mem (measurableSet_mellinHeightBox T)] with τ hτ
    exact hb τ hτ
  have hm := finite_row_integral_moment f w hc.aestronglyMeasurable hw.restrict hB ha
  apply hm.trans
  have hmass : (∫ τ in mellinHeightBox T, ‖w τ‖) ≤ ∫ τ, ‖w τ‖ :=
    setIntegral_le_integral hw.norm (Filter.Eventually.of_forall (fun _ => _root_.norm_nonneg _))
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (integral_nonneg (fun _ => _root_.norm_nonneg _)) hmass 2) hB

theorem independent_mellin_integral_moment (f : κ → (ι → ℝ) → ℂ)
    (hf : ∀ r, Continuous (f r)) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ)
    {T L B : ℝ} (hT : 0 < T) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hsize : ∀ r τ, ‖f r τ‖ ≤ L)
    (hbound : ∀ τ ∈ mellinHeightBox T, (∑ r, ‖f r τ‖^2) ≤ B) :
    (∑ r, ‖∫ τ, independentMellinWeight W X τ*f r τ‖^2) ≤
      2*(∏ i, zeroLineMellinMass (W i))^2*B+
        2*(Fintype.card κ:ℝ)*((L/T^A)*independentMellinMoment W A)^2 := by
  let w := independentMellinWeight W X
  have hw : Integrable w := independentMellinWeight_integrable W X hW hpos hsm hX
  have hc := finite_box_integral_moment f hf w hw T B hB hbound
  rw [independentMellinWeight_mass W X hX] at hc
  let H := (L/T^A)*independentMellinMoment W A
  have ht (r : κ) : ‖∫ τ in (mellinHeightBox T)ᶜ, w τ*f r τ‖ ≤ H := by
    calc
      _ ≤ L*(∫ τ in (mellinHeightBox T)ᶜ, ‖w τ‖) := by
        rw [← integral_const_mul]
        apply norm_integral_le_of_norm_le (hw.norm.restrict.const_mul L)
        filter_upwards with τ
        rw [norm_mul,mul_comm L]
        exact mul_le_mul_of_nonneg_left (hsize r τ) (_root_.norm_nonneg _)
      _ ≤ L*(independentMellinMoment W A/T^A) :=
        mul_le_mul_of_nonneg_left (independentMellinWeight_tail W X hW hpos hsm hX A hT) hL
      _ = H := by dsimp [H]; ring
  have ha (r : κ) :
      ‖(∫ τ, w τ*f r τ)-(∫ τ in mellinHeightBox T, w τ*f r τ)‖ ≤ H := by
    have hi : Integrable (fun τ => w τ*f r τ) := (hw.norm.mul_const L).mono'
      (hw.aestronglyMeasurable.mul (hf r).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun τ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hsize r τ) (_root_.norm_nonneg _)))
    rw [← integral_add_compl (measurableSet_mellinHeightBox T) hi,add_sub_cancel_left]
    exact ht r
  calc
    _ ≤ ∑ r, (2*‖∫ τ in mellinHeightBox T, w τ*f r τ‖^2+2*H^2) :=
      Finset.sum_le_sum (fun r _ => norm_square_le_central_tail _ _ (ha r))
    _ = 2*(∑ r, ‖∫ τ in mellinHeightBox T, w τ*f r τ‖^2)+2*(Fintype.card κ:ℝ)*H^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _ ≤ _ := by dsimp [H]; nlinarith

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

theorem normPartitionCount_power_bound (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      (normPartitionCount B : ℝ)^d ≤ C*B^ε := by
  obtain ⟨K,hK,hcount⟩ := normPartitionCount_log_bound
  have hd : 0 < (d:ℝ)+1 := by positivity
  obtain ⟨A,hA,hlog⟩ := one_add_log_small_power (div_pos hε hd)
  refine ⟨(K*A)^d,pow_pos (mul_pos hK hA) _,?_⟩
  intro B hB
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hnb : (normPartitionCount B : ℝ) ≤ (K*A)*B^(ε/((d:ℝ)+1)) :=
    (hcount B hB).trans (by
      calc
        K*(1+Real.log B) ≤ K*(A*B^(ε/((d:ℝ)+1))) :=
          mul_le_mul_of_nonneg_left (hlog B hB) hK.le
        _ = _ := by ring)
  have he : ε/((d:ℝ)+1)*(d:ℝ) ≤ ε := by
    have hm := div_mul_cancel₀ ε hd.ne'
    have hp : 0 < ε/((d:ℝ)+1) := div_pos hε hd
    nlinarith
  calc
    _ ≤ ((K*A)*B^(ε/((d:ℝ)+1)))^d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hnb d
    _ = (K*A)^d*B^(ε/((d:ℝ)+1)*(d:ℝ)) := by
      rw [mul_pow,← Real.rpow_mul_natCast hBp.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB he) (pow_nonneg (mul_pos hK hA).le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PartitionMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the explicit smooth norm partition loses only a small part of
an established power saving. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_piece_moment {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (f : κ → ρ → ℂ) :
    (∑ r, ‖∑ k, f k r‖^2) ≤ (Fintype.card κ:ℝ)*(∑ k, ∑ r, ‖f k r‖^2) := by
  calc
    _ ≤ ∑ r, (Fintype.card κ:ℝ)*(∑ k, ‖f k r‖^2) := by
      apply Finset.sum_le_sum
      intro r _
      apply (pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_sum_le _ _) 2).trans
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : κ => (1:ℝ))
        (fun k => ‖f k r‖)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_partition_moment_power {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y → ∀ (ρ : Type*) [Fintype ρ]
      (f : (ι → Fin (normPartitionCount (2*Y))) → ρ → ℂ),
      (∀ k, (∑ r, ‖f k r‖^2) ≤ Y^(7/3-ε)) →
      (∑ r, ‖∑ k, f k r‖^2) ≤ Y^(7/3-ε/2) := by
  obtain ⟨C,hC,hcount⟩ := normPartitionCount_power_bound (2*Fintype.card ι)
    (show 0 < ε/4 by linarith)
  let K : ℝ := C*2^(ε/4)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < ε/4 by linarith)).eventually_ge_atTop K)
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY ρ _ f hf
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hc : ((Fintype.card (ι → Fin (normPartitionCount (2*Y)))):ℝ)^2 ≤ K*Y^(ε/4) := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,← pow_mul]
    rw [Nat.mul_comm]
    apply (hcount (2*Y) (by linarith)).trans_eq
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hYp.le]
    dsimp [K]
    ring
  calc
    _ ≤ (Fintype.card (ι → Fin (normPartitionCount (2*Y))):ℝ)*
        (∑ k, ∑ r, ‖f k r‖^2) := finite_piece_moment f
    _ ≤ (Fintype.card (ι → Fin (normPartitionCount (2*Y))):ℝ)^2*Y^(7/3-ε) := by
      calc
        _ ≤ (Fintype.card (ι → Fin (normPartitionCount (2*Y))):ℝ)*
            (∑ _k : ι → Fin (normPartitionCount (2*Y)), Y^(7/3-ε)) := by
          apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hf k))
            (Nat.cast_nonneg _)
        _ = _ := by simp; ring
    _ ≤ (K*Y^(ε/4))*Y^(7/3-ε) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hYp.le _)
    _ = K*Y^(7/3-3*ε/4) := by
      rw [mul_assoc,← Real.rpow_add hYp,
        show ε/4+(7/3-ε) = 7/3-3*ε/4 by ring]
    _ ≤ Y^(ε/4)*Y^(7/3-3*ε/4) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortTupleScales
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonzero smooth convolution piece automatically has comparable total
length. Thus the moment hypotheses need not be imposed on empty pieces. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma normPartitionWeight_nonzero_length {x X : ℝ} (hX : 0 < X)
    (h : normPartitionWeight (x/(X/2)) ≠ 0) : x ≤ X ∧ X ≤ 2*x := by
  have hp : 0 < X/2 := by linarith
  have hlo : 1 ≤ x/(X/2) := by
    by_contra hn
    exact h (normPartitionWeight_low (lt_of_not_ge hn))
  have hhi : x/(X/2) ≤ 2 := by
    by_contra hn
    exact h (normPartitionWeight_high (lt_of_not_ge hn))
  have h₁ := (le_div_iff₀ hp).mp hlo
  have h₂ := (div_le_iff₀ hp).mp hhi
  constructor <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primaryShortTupleSum_nonzero_scales (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hX : ∀ i, 0 < X i) (hZ : 0 < Z)
    (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (h : primaryShortTupleSum X A a b q η (fun _ => normPartitionWeight) t V Z ≠ 0) :
    Z ≤ ∏ i, X i ∧ (∏ i, X i) ≤ (2:ℝ)^(Fintype.card ι+1)*Z := by
  unfold primaryShortTupleSum at h
  obtain ⟨n,_,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hp := (mul_ne_zero_iff.mp hn).1
  have hv := (mul_ne_zero_iff.mp hn).2
  have hi (i : ι) : norm (n i:Eisenstein) ≤ X i ∧ X i ≤ 2*norm (n i:Eisenstein) := by
    apply normPartitionWeight_nonzero_length (hX i)
    exact (mul_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i))).2
  have hlo : 1 ≤ (∏ i, norm (n i:Eisenstein))/Z := by
    by_contra hlt
    exact hv (hVlo _ (lt_of_not_ge hlt))
  have hhi : (∏ i, norm (n i:Eisenstein))/Z ≤ 2 := by
    by_contra hgt
    exact hv (hVhi _ (lt_of_not_ge hgt))
  constructor
  · simpa only [one_mul] using ((le_div_iff₀ hZ).mp hlo).trans
      (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (hi i).1))
  · calc
      _ ≤ ∏ i, 2*norm (n i:Eisenstein) := Finset.prod_le_prod
        (fun i _ => (hX i).le) (fun i _ => (hi i).2)
      _ = (2:ℝ)^(Fintype.card ι)*(∏ i, norm (n i:Eisenstein)) := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
      _ ≤ (2:ℝ)^(Fintype.card ι)*(2*Z) :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hZ).mp hhi) (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem primaryShortTupleSum_zero_outside_scales (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hX : ∀ i, 0 < X i) (hZ : 0 < Z)
    (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hscale : ¬(Z ≤ ∏ i, X i ∧ (∏ i, X i) ≤ (2:ℝ)^(Fintype.card ι+1)*Z)) :
    primaryShortTupleSum X A a b q η (fun _ => normPartitionWeight) t V Z = 0 := by
  by_contra h
  exact hscale (primaryShortTupleSum_nonzero_scales X A a b q η t V hX hZ hVlo hVhi h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortTuplePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction of the original finite convolution from smooth
norm pieces. The common ball is forced by the global product cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_primary_pi (X : ι → ℝ) (f : (ι → Eisenstein) → ℂ) :
    (∑ n : (i : ι) → primaryElementBall (X i), f (fun i => n i)) =
      ∑ n ∈ Fintype.piFinset (fun i => primaryElementBall (X i)), f n := by
  apply Finset.sum_bij (fun n _ i => (n i : Eisenstein))
  · intro n _
    exact Fintype.mem_piFinset.mpr (fun i => (n i).property)
  · intro n _ m _ h
    funext i
    exact Subtype.ext (congrFun h i)
  · intro n hn
    exact ⟨fun i => ⟨n i,(Fintype.mem_piFinset.mp hn) i⟩,Finset.mem_univ _,rfl⟩
  · intro n _
    rfl

lemma primaryShortTupleSum_eq_core (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) (Z : ℝ) :
    primaryShortTupleSum X A a b q η (fun _ => normPartitionWeight) t V Z =
      ∑ n ∈ Fintype.piFinset (fun i => primaryElementBall (X i)),
        primaryTupleCore A a b q η t V Z n*
          ∏ i, normPartitionWeight (norm (n i)/(X i/2)) := by
  unfold primaryShortTupleSum
  calc
    _ = ∑ n : (i : ι) → primaryElementBall (X i),
        primaryTupleCore A a b q η t V Z (fun i => n i)*
          ∏ i, normPartitionWeight (norm (n i)/(X i/2)) := by
      apply Finset.sum_congr rfl
      intro n _
      unfold primaryTupleCore
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := sum_primary_pi X (fun n => primaryTupleCore A a b q η t V Z n*
      ∏ i, normPartitionWeight (norm (n i)/(X i/2)))

omit [DecidableEq ι] in
lemma primaryTupleCore_support (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (hV : ∀ x, 2 < x → V x = 0)
    (n : ι → Eisenstein) (hn : ∀ i, primary (n i))
    (h : primaryTupleCore A a b q η t V Z n ≠ 0) (i : ι) : norm (n i) ≤ 2*Z := by
  have hv := (mul_ne_zero_iff.mp h).2
  have hp : (∏ j, norm (n j))/Z ≤ 2 := by
    by_contra hgt
    exact hv (hV _ (lt_of_not_ge hgt))
  have hni : norm (n i) ≤ ∏ j, norm (n j) := by
    calc
      _ = ∏ j ∈ ({i} : Finset ι), norm (n j) := by simp
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le (by simp)
        (fun j _ => norm_nonneg _) (fun j _ _ => one_le_norm (primary_ne_zero (hn j)))
  exact hni.trans ((div_le_iff₀ hZ).mp hp)

lemma primaryShortTupleSum_common_ball (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (hV : ∀ x, 2 < x → V x = 0)
    (hX : ∀ i, 0 < X i) :
    primaryShortTupleSum X A a b q η (fun _ => normPartitionWeight) t V Z =
      ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Z)),
        primaryTupleCore A a b q η t V Z n*
          ∏ i, normPartitionWeight (norm (n i)/(X i/2)) := by
  rw [primaryShortTupleSum_eq_core]
  apply Finset.sum_bij_ne_zero (fun n _ _ => n)
  · intro n hn h
    have hc := (mul_ne_zero_iff.mp h).1
    exact Fintype.mem_piFinset.mpr (fun i => mem_primaryElementBall.mpr
      ⟨(mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1,
        primaryTupleCore_support A a b q η t V hZ hV n
          (fun j => (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) j)).1) hc i⟩)
  · intro n _ _ m _ _ h
    exact h
  · intro n hn h
    refine ⟨n,Fintype.mem_piFinset.mpr (fun i => ?_),h,rfl⟩
    have hw := (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp h).2) i (Finset.mem_univ i)
    exact mem_primaryElementBall.mpr
      ⟨(mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1,
        (normPartitionWeight_nonzero_length (hX i) hw).1⟩
  · intro n _ _
    rfl

/-- The unsplit finite tuple sum is exactly the sum of its explicit smooth
pieces. No decomposition hypothesis is assumed. -/
theorem primaryShortTupleSum_partition (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hZ : 1 ≤ Z) (hV : ∀ x, 2 < x → V x = 0) :
    (∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Z)),
      primaryTupleCore A a b q η t V Z n) =
      ∑ k : ι → Fin (normPartitionCount (2*Z)),
        primaryShortTupleSum (fun i => (4/3:ℝ)^(k i).val) A a b q η
          (fun _ => normPartitionWeight) t V Z := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  rw [finite_sum_normTupleWeight (Fintype.piFinset (fun _ : ι => primaryElementBall (2*Z)))
    (primaryTupleCore A a b q η t V Z) (fun n i => norm (n i))
    (fun n hn i => one_le_norm (primary_ne_zero
      (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1))
    (fun n hn i => (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).2)
    (normPartitionCount_covers (by linarith : 1 ≤ 2*Z))]
  apply Finset.sum_congr rfl
  intro k _
  rw [primaryShortTupleSum_common_ball _ A a b q η t V hZp hV
    (fun i => pow_pos (by norm_num) _)]
  apply Finset.sum_congr rfl
  intro n _
  unfold normTupleWeight
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  field_simp

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ComplexWeightedConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex coefficient collection retains the distinct norm and residue
twists of each original prime factor during short inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complex_coeff_product_eq_convolution (A : ι → MvPowerSeries EisensteinIdealPrime ℂ)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i) =
      orderedConvolution (fun _ : ι => primaryElementBall F)
        (fun i n => MvPowerSeries.coeff (idealExponentOf n) (A i)) b := by
  rw [coeff_product_primary_fiber A hb hbF]
  rfl

/-- The global smooth cutoff permits collection on one finite primary
ball, although the unrestricted product support is much larger. -/
theorem primaryComplexProductPolynomial_eq_tuple (A : ι → MvPowerSeries EisensteinIdealPrime ℂ)
    (χ : Eisenstein → ℂ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryComplexProductPolynomial A χ V Y =
      ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        (∏ i, MvPowerSeries.coeff (idealExponentOf (n i)) (A i))*
          χ (∏ i, n i)*V ((∏ i, norm (n i))/Y) := by
  let S : ι → Finset Eisenstein := fun _ => primaryElementBall (2*Y)
  let w : ι → Eisenstein → ℂ := fun i n =>
    MvPowerSeries.coeff (idealExponentOf n) (A i)
  have hc (b : Eisenstein) (hb : b ∈ primaryElementBall (2*Y)) :
      MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i) = orderedConvolution S w b :=
    complex_coeff_product_eq_convolution A (mem_primaryElementBall.mp hb).1 (mem_primaryElementBall.mp hb).2
  unfold primaryComplexProductPolynomial
  have hs : (∑ b ∈ primaryElementBall (2*Y), orderedConvolution S w b*(χ b*V (norm b/Y))) =
      ∑ b ∈ orderedConvolutionSupport S, orderedConvolution S w b*(χ b*V (norm b/Y)) := by
    apply Finset.sum_bij_ne_zero (fun b _ _ => b)
    · intro b _ hn
      by_contra hb
      rw [orderedConvolution_eq_zero_of_not_mem S w hb,zero_mul] at hn
      exact hn rfl
    · intro b _ _ c _ _ h
      exact h
    · intro b hb hn
      have hp : primary b := by
        change b ∈ (Fintype.piFinset S).image (fun n => ∏ i, n i) at hb
        obtain ⟨n,hnmem,rfl⟩ := Finset.mem_image.mp hb
        have hn' : n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)) := hnmem
        have hni (i : ι) : n i ∈ primaryElementBall (2*Y) := (Fintype.mem_piFinset.mp hn') i
        exact primary_finset_prod Finset.univ n (fun i _ => (mem_primaryElementBall.mp (hni i)).1)
      have hv : V (norm b/Y) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).2).2
      have hbn : norm b ≤ 2*Y := by
        by_contra hgt
        exact hv (hV _ ((lt_div_iff₀ hY).mpr (lt_of_not_ge hgt)))
      exact ⟨b,mem_primaryElementBall.mpr ⟨hp,hbn⟩,hn,rfl⟩
    · intro b _ _
      rfl
  calc
    _ = ∑ b ∈ primaryElementBall (2*Y), orderedConvolution S w b*χ b*V (norm b/Y) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hc b hb]
    _ = ∑ b ∈ primaryElementBall (2*Y), orderedConvolution S w b*(χ b*V (norm b/Y)) := by
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := hs
    _ = _ := by
      rw [orderedConvolution_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [norm_finset_prod]
      dsimp only [w]
      ring

/-- Independent residue characters and Mellin heights remain attached to
individual factors after exact collection. -/
theorem twistedProductPolynomial_eq_unsplit (A : ι → EisensteinArithmeticFunction)
    {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hη : ∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1)
    (t : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryComplexProductPolynomial (fun i => twistArithmetic (q i) (η i) (t i) (A i))
      (mixedCubic a b) V Y = primaryUnsplitTuple A a b q η t V Y := by
  rw [primaryComplexProductPolynomial_eq_tuple _ _ V hY hV]
  unfold primaryUnsplitTuple
  apply Finset.sum_congr rfl
  intro n hn
  have hp (i : ι) : primary (n i) :=
    (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1
  simp_rw [twistArithmetic_coeff_primary _ _ (hη _) _ _ (hp _)]
  rw [mixedCubic_prod _ _ ha hb]
  unfold primaryTupleCore
  rw [← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoordinateWeightedTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent smooth weights on the original arithmetic factors, with the
exact Mellin representation by the unweighted convolutions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma primaryTupleCore_shift (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t τ : ι → ℝ)
    (V : ℝ → ℂ) (Y : ℝ) (n : ι → Eisenstein) :
    primaryTupleCore A a b q η t V Y n * ∏ i, mellinPhase (-(τ i)) (norm (n i)) =
      primaryTupleCore A a b q η (fun i => t i-τ i) V Y n := by
  unfold primaryTupleCore
  rw [mul_right_comm,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_assoc,mul_assoc,← mellinPhase_add]
  congr 2

lemma continuous_primaryUnsplitTuple (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (V : ℝ → ℂ) (Y : ℝ) :
    Continuous (fun t : ι → ℝ => primaryUnsplitTuple A a b q η t V Y) := by
  unfold primaryUnsplitTuple primaryTupleCore mellinPhase
  fun_prop

 theorem primaryCoordinateWeightedTuple_mellin (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) :
    primaryCoordinateWeightedTuple A a b q η t W X V Y =
      ∫ τ : ι → ℝ, independentMellinWeight W X τ *
        primaryUnsplitTuple A a b q η (fun i => t i-τ i) V Y := by
  let S := Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y))
  have hN (i : ι) (n : S) : 0 < norm (n.val i) :=
    norm_pos_of_ne_zero (primary_ne_zero
      (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp n.property) i)).1)
  have hm := independent_mellin_finite
    (fun n : S => primaryTupleCore A a b q η t V Y n.val)
    (fun i (n : S) => norm (n.val i)) hN W X hW hpos hsm hX
  have hl : (∑ n : S, primaryTupleCore A a b q η t V Y n.val *
      ∏ i, W i (norm (n.val i)/X i)) = primaryCoordinateWeightedTuple A a b q η t W X V Y := by
    change (∑ n ∈ S.attach, _) = _
    rw [Finset.sum_attach (f := fun n : ι → Eisenstein =>
      primaryTupleCore A a b q η t V Y n * ∏ i, W i (norm (n i)/X i))]
    rfl
  rw [hl] at hm
  rw [hm]
  apply integral_congr_ae
  filter_upwards with τ
  congr 1
  simp_rw [primaryTupleCore_shift]
  change (∑ n ∈ S.attach, primaryTupleCore A a b q η (fun i => t i-τ i) V Y n.val) = _
  rw [Finset.sum_attach (f := fun n : ι → Eisenstein =>
    primaryTupleCore A a b q η (fun i => t i-τ i) V Y n)]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleSize
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial bound for the actual von Mangoldt tuple sum. This coarse
bound is used only against arbitrarily rapid Mellin tails. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma vonMangoldt_coeff_norm_le {Y : ℝ} {n : Eisenstein}
    (hn : n ∈ primaryElementBall (2*Y)) :
    ‖((MvPowerSeries.coeff (idealExponentOf n) idealVonMangoldt:ℝ):ℂ)‖ ≤ 2*Y := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  have hp := (mem_primaryElementBall.mp hn).1
  have h := idealVonMangoldt_coeff_abs_le_logNorm (idealExponentOf n)
  rw [idealExponentOf_norm (primary_ne_zero hp)] at h
  exact h.trans ((Real.log_le_self (norm_nonneg n)).trans (mem_primaryElementBall.mp hn).2)

lemma vonMangoldt_tuple_core_bound (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (V : ℝ → ℂ)
    {M Y : ℝ} (_hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y)
    (n : ι → Eisenstein) (hn : n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y))) :
    ‖primaryTupleCore (fun _ : ι => idealVonMangoldt) a b q η t V Y n‖ ≤
      (2*Y)^(Fintype.card ι)*M := by
  have hi (i : ι) :
      ‖((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*mellinPhase (t i) (norm (n i)))‖ ≤ 2*Y := by
    have htw : ‖mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        mellinPhase (t i) (norm (n i))‖ ≤ 1 := by
      rw [norm_mul,mellinPhase_norm,mul_one,norm_mul]
      exact (mul_le_mul (norm_mixedCubic_le_one ha hb _) (residueChar_norm_le_one (hq i) (η i) _)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (_root_.norm_nonneg _) htw).trans
      (vonMangoldt_coeff_norm_le ((Fintype.mem_piFinset.mp hn) i))
  unfold primaryTupleCore
  rw [norm_mul,norm_prod]
  have hp : (∏ i, ‖((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*mellinPhase (t i) (norm (n i)))‖) ≤
      (2*Y)^(Fintype.card ι) := by
    calc
      _ ≤ ∏ _i : ι, 2*Y :=
        Finset.prod_le_prod (fun i _ => _root_.norm_nonneg _) (fun i _ => hi i)
      _ = _ := by simp
  exact mul_le_mul hp (hV _) (_root_.norm_nonneg _) (pow_nonneg (by positivity) _)

 theorem vonMangoldt_unsplit_size (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (V : ℝ → ℂ)
    {M Y : ℝ} (hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y) :
    ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt) a b q η t V Y‖ ≤
      (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) := by
  unfold primaryUnsplitTuple
  calc
    _ ≤ ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        ‖primaryTupleCore (fun _ : ι => idealVonMangoldt) a b q η t V Y n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        (2*Y)^(Fintype.card ι)*M :=
      Finset.sum_le_sum (fun n hn => vonMangoldt_tuple_core_bound a b ha hb q η hq t V hM hV hY n hn)
    _ = ((primaryElementBall (2*Y)).card:ℝ)^(Fintype.card ι)*((2*Y)^(Fintype.card ι)*M) := by
      simp [Fintype.card_piFinset,Finset.prod_const]
    _ ≤ (36*Y)^(Fintype.card ι)*((2*Y)^(Fintype.card ι)*M) := by
      apply mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _) (mul_nonneg (pow_nonneg (by positivity) _) hM)
      nlinarith [primaryElementBall_card_le (show 0 ≤ 2*Y by positivity)]
    _ = M*((36*Y)*(2*Y))^(Fintype.card ι) := by
      rw [mul_pow (36*Y) (2*Y)]
      ring
    _ = M*(72*Y^2)^(Fintype.card ι) := by congr 1; congr 1; ring
    _ = _ := by rw [mul_pow,pow_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoordinatePrimeMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate Mellin transfer for the actual independently weighted
von Mangoldt tuple sum, with a polynomial bound for every tail row. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

 theorem coordinate_vonMangoldt_moment_bound (r : κ → Eisenstein × Eisenstein)
    (hr : ∀ j, primary (r j).1 ∧ primary (r j).2)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i)
    (V : ℝ → ℂ) {M Y : ℝ} (hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y)
    (A : ℕ) {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hbound : ∀ τ ∈ mellinHeightBox T,
      (∑ j, ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt)
        (r j).1 (r j).2 q η (fun i => t i-τ i) V Y‖^2) ≤ B) :
    (∑ j, ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
      (r j).1 (r j).2 q η t W X V Y‖^2) ≤
      2*(∏ i, zeroLineMellinMass (W i))^2*B+
        2*(Fintype.card κ:ℝ)*
          (((M*72^(Fintype.card ι))*Y^(2*Fintype.card ι)/T^A)*independentMellinMoment W A)^2 := by
  let f : κ → (ι → ℝ) → ℂ := fun j τ =>
    primaryUnsplitTuple (fun _ : ι => idealVonMangoldt) (r j).1 (r j).2 q η
      (fun i => t i-τ i) V Y
  have hf (j : κ) : Continuous (f j) :=
    (continuous_primaryUnsplitTuple _ _ _ q η V Y).comp (by fun_prop)
  have hsize (j : κ) (τ : ι → ℝ) :
      ‖f j τ‖ ≤ (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) :=
    vonMangoldt_unsplit_size _ _ (hr j).1 (hr j).2 q η hq _ V hM hV hY
  have hm := independent_mellin_integral_moment f hf W X hW hpos hsm hX A hT
    (show 0 ≤ (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) by positivity) hB hsize hbound
  have he (j : κ) := primaryCoordinateWeightedTuple_mellin (fun _ : ι => idealVonMangoldt)
    (r j).1 (r j).2 q η t W X V Y hW hpos hsm hX
  simpa only [he] using hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteMomentSaving
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite linear combination preserves a positive moment saving. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_positive_lower_bound {κ : Type*} [Fintype κ] (e : κ → ℝ)
    (he : ∀ k, 0 < e k) : ∃ d : ℝ, 0 < d ∧ ∀ k, d ≤ e k := by
  classical
  have h : ∀ S : Finset κ, ∃ d : ℝ, 0 < d ∧ ∀ k ∈ S, d ≤ e k := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert k S hk ih =>
      obtain ⟨d,hd,hde⟩ := ih
      refine ⟨min d (e k),lt_min hd (he k),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hde j hj)
  obtain ⟨d,hd,hde⟩ := h Finset.univ
  exact ⟨d,hd,fun k => hde k (Finset.mem_univ k)⟩

theorem finite_weighted_moment_saving {κ : Type*} [Fintype κ]
    (e : κ → ℝ) (he : ∀ k, 0 < e k) (c : κ → ℂ) :
    ∃ d : ℝ, 0 < d ∧ ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y →
      ∀ (ρ : Type*) [Fintype ρ] (f : κ → ρ → ℂ),
      (∀ k, (∑ r, ‖f k r‖^2) ≤ Y^(7/3-e k)) →
      (∑ r, ‖∑ k, c k*f k r‖^2) ≤ Y^(7/3-d) := by
  obtain ⟨d,hd,hde⟩ := finite_positive_lower_bound e he
  let C : ℝ := (Fintype.card κ)*(∑ k, ‖c k‖^2)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < d/2 by linarith)).eventually_ge_atTop C)
  refine ⟨d/2,by positivity,max 1 T,le_max_left _ _,?_⟩
  intro Y hY ρ _ f hf
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hf' (k : κ) : (∑ r, ‖f k r‖^2) ≤ Y^(7/3-d) :=
    (hf k).trans (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith [hde k]))
  calc
    _ ≤ (Fintype.card κ:ℝ)*(∑ k, ∑ r, ‖c k*f k r‖^2) :=
      finite_piece_moment (fun k r => c k*f k r)
    _ = (Fintype.card κ:ℝ)*(∑ k, ‖c k‖^2*(∑ r, ‖f k r‖^2)) := by
      simp_rw [norm_mul,mul_pow,← Finset.mul_sum]
    _ ≤ (Fintype.card κ:ℝ)*(∑ k, ‖c k‖^2*Y^(7/3-d)) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hf' k) (sq_nonneg _)))
        (Nat.cast_nonneg _)
    _ = C*Y^(7/3-d) := by rw [← Finset.sum_mul]; dsimp [C]; ring
    _ ≤ Y^(d/2)*Y^(7/3-d) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FirstUnsplitNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact norm-partition reconstruction preserves the exceptional neighborhood. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem first_unsplit_tuple_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y N : ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → F ≤ 2*Y → (∀ i, ShortArithmeticFactor F (A i)) →
      (∀ i, q i ≠ 0) → (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryUnsplitTuple A a 1 q η t V Y‖^2) ≤ Y^(7/3-ε) := by
  let D : ℝ := 2^(Fintype.card ι+1)
  have hD1 : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hD2 : 2 ≤ D := by
    dsimp [D]
    rw [pow_succ]
    have h := one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := Fintype.card ι)
    linarith
  have hD : 0 < D := zero_lt_one.trans_le hD1
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hw⟩ := first_weighted_tuple_neighborhood (ι := ι) hpub V hV hpos hsm hGI hGQ hD
  obtain ⟨T₁,hT₁,hpart⟩ := norm_partition_moment_power (ι := ι) hε
  refine ⟨κ,hκ,hκhi,ε/2,by positivity,max T T₁,?_⟩
  intro F Y N A q η t P hY hNlo hNhi hF hA hq hη hqY ht hP
  have hYT : T ≤ Y := (le_max_left _ _).trans hY
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans hY
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  let f : (ι → Fin (normPartitionCount (2*Y))) → P → ℂ := fun k a =>
    primaryShortTupleSum (fun i => (4/3:ℝ)^(k i).val) A a 1 q η
      (fun _ => normPartitionWeight) t V Y
  have hf (k : ι → Fin (normPartitionCount (2*Y))) : (∑ a : P, ‖f k a‖^2) ≤ Y^(7/3-ε) := by
    by_cases hg : Y ≤ (∏ i, (4/3:ℝ)^(k i).val) ∧ (∏ i, (4/3:ℝ)^(k i).val) ≤ D*Y
    · have h := hw F Y N (fun i => (4/3:ℝ)^(k i).val) A q η t P Y hYT hNlo hNhi
        (hF.trans (mul_le_mul_of_nonneg_right hD2 hYp.le)) hA
        (fun i => one_le_pow₀ (by norm_num)) ((div_le_self hYp.le hD1).trans hg.1)
        hg.2 hq hη hqY ht hP hYp
      change (∑ a ∈ P.attach, ‖f k a‖^2) ≤ _
      dsimp only [f]
      rw [Finset.sum_attach (f := fun a : Eisenstein =>
        ‖primaryShortTupleSum (fun i => (4/3:ℝ)^(k i).val) A a 1 q η
          (fun _ => normPartitionWeight) t V Y‖^2)]
      exact h
    · have hz (a : P) : f k a = 0 := primaryShortTupleSum_zero_outside_scales _ A a 1 q η t V
        (fun i => pow_pos (by norm_num) _) hYp hVlo hVhi hg
      simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
      exact Real.rpow_nonneg hYp.le _
  have hm := hpart Y hYT₁ P f hf
  have he (a : Eisenstein) : primaryUnsplitTuple A a 1 q η t V Y =
      ∑ k : ι → Fin (normPartitionCount (2*Y)),
        primaryShortTupleSum (fun i => (4/3:ℝ)^(k i).val) A a 1 q η
          (fun _ => normPartitionWeight) t V Y :=
    primaryShortTupleSum_partition A a 1 q η t V hY1 hVhi
  simp_rw [he]
  change (∑ a ∈ P.attach, ‖∑ k, f k a‖^2) ≤ _ at hm
  dsimp only [f] at hm
  rw [Finset.sum_attach (f := fun a : Eisenstein =>
    ‖∑ k : ι → Fin (normPartitionCount (2*Y)),
      primaryShortTupleSum (fun i => (4/3:ℝ)^(k i).val) A a 1 q η
        (fun _ => normPartitionWeight) t V Y‖^2)] at hm
  exact hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedConvolutionNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional moments for actual complex convolutions with an independent
residue character and Mellin height on each factor. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem first_twisted_convolution_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y N : ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → F ≤ 2*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) → (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryComplexProductPolynomial (fun i => twistArithmetic (q i) (η i) (t i) (A i)) (mixedCubic a 1) V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := first_unsplit_tuple_neighborhood (ι := ι)
    hpub V hV hpos hsm hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,ε,hε,max 1 T,?_⟩
  intro F Y N A q η t P hY hNlo hNhi hF hA hq hη hqY ht hP
  have hYp : 0 < Y := zero_lt_one.trans_le ((le_max_left _ _).trans hY)
  have he (a : Eisenstein) (ha : a ∈ P) :
      primaryComplexProductPolynomial (fun i => twistArithmetic (q i) (η i) (t i) (A i)) (mixedCubic a 1) V Y =
        primaryUnsplitTuple A a 1 q η t V Y :=
    twistedProductPolynomial_eq_unsplit A (hP a ha).1 (by norm_num [primary])
      q η hη t V hYp hVhi
  calc
    _ = ∑ a ∈ P, ‖primaryUnsplitTuple A a 1 q η t V Y‖^2 :=
      Finset.sum_congr rfl (fun a ha => by rw [he a ha])
    _ ≤ _ := hbound F Y N A q η t P
      ((le_max_right _ _).trans hY) hNlo hNhi hF hA hq hη hqY ht hP

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortConvolutionExpansion
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each term of the short Möbius product expansion is an actual finite
family of the three permitted arithmetic factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma shortBranchFactor_spec (F : ℝ) (S : Finset ι) (i : shortBranchIndex S) :
    ShortArithmeticFactor F (shortBranchFactor F S i) := by
  rcases i with ⟨i,j⟩ | ⟨i,j⟩
  · fin_cases j <;> simp [shortBranchFactor,ShortArithmeticFactor]
  · fin_cases j <;> simp [shortBranchFactor,ShortArithmeticFactor]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedShortProducts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short inversion with a different residue character and Mellin height
on each original prime factor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma twistArithmetic_two (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A : EisensteinArithmeticFunction) :
    twistArithmetic q η t (2*A) = 2*twistArithmetic q η t A := by
  rw [two_mul,twistArithmetic_add,two_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem twisted_short_product_coeff {F : ℝ} (hF : 0 ≤ F)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (t : ι → ℝ) (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν (∏ i, twistArithmetic (q i) (η i) (t i) idealVonMangoldt) =
      MvPowerSeries.coeff ν (∏ i, twistArithmetic (q i) (η i) (t i) (shortVonMangoldt F)) := by
  have h : ∀ S : Finset ι, ∀ κ : EisensteinIdealExponent, idealExponentNorm κ ≤ F →
      MvPowerSeries.coeff κ (∏ i ∈ S, twistArithmetic (q i) (η i) (t i) idealVonMangoldt) =
      MvPowerSeries.coeff κ (∏ i ∈ S, twistArithmetic (q i) (η i) (t i) (shortVonMangoldt F)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intros; rfl
    | @insert i S hi ih =>
      intro κ hκ
      rw [Finset.prod_insert hi,Finset.prod_insert hi,MvPowerSeries.coeff_mul,MvPowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have h₁ : p.1 ≤ κ := by rw [← he]; exact le_add_of_nonneg_right zero_le
      have h₂ : p.2 ≤ κ := by rw [← he]; exact le_add_of_nonneg_left zero_le
      rw [ih p.2 ((idealExponentNorm_mono h₂).trans hκ)]
      congr 1
      change ((MvPowerSeries.coeff p.1 idealVonMangoldt:ℝ):ℂ)*residueNormTwist (q i) (η i) (t i) p.1 =
        ((MvPowerSeries.coeff p.1 (shortVonMangoldt F):ℝ):ℂ)*residueNormTwist (q i) (η i) (t i) p.1
      rw [shortVonMangoldt_local hF p.1 ((idealExponentNorm_mono h₁).trans hκ)]
  exact h Finset.univ ν hν

lemma twisted_branch_product (F : ℝ) (S : Finset ι) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) :
    (∏ j : shortBranchIndex S,
      twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor F S j)) =
      (∏ i ∈ S, twistArithmetic (q i) (η i) (t i) (shortFourFactor F))*
        ∏ i ∈ Finset.univ\S, twistArithmetic (q i) (η i) (t i) (shortTwoFactor F) := by
  rw [Fintype.prod_sum_type,Fintype.prod_prod_type,Fintype.prod_prod_type]
  simp only [shortBranchSource,shortBranchFactor,Fin.prod_univ_four,Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  simp only [← twistArithmetic_mul]
  change (∏ x : S, twistArithmetic (q x) (η x) (t x) (shortFourFactor F))*
    (∏ x : ↥(Finset.univ\S), twistArithmetic (q x) (η x) (t x) (shortTwoFactor F)) = _
  rw [Finset.prod_coe_sort (s := S) (f := fun i => twistArithmetic (q i) (η i) (t i) (shortFourFactor F)),
    Finset.prod_coe_sort (s := Finset.univ\S) (f := fun i => twistArithmetic (q i) (η i) (t i) (shortTwoFactor F))]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedPrimeExpansion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact short inversion with independent residue and norm twists on every
original von Mangoldt factor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma twisted_short_series_expansion (F : ℝ) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) :
    (∏ i, twistArithmetic (q i) (η i) (t i) (shortVonMangoldt F)) =
      ∑ S : Finset ι, MvPowerSeries.C (shortBranchScalar S)*
        ∏ j : shortBranchIndex S,
          twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
            (t (shortBranchSource S j)) (shortBranchFactor F S j) := by
  simp_rw [shortVonMangoldt_two_four,twistArithmetic_sub,twistArithmetic_two]
  rw [Finset.prod_sub,Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S _
  rw [twisted_branch_product]
  have hp : (∏ i ∈ Finset.univ\S, 2*twistArithmetic (q i) (η i) (t i) (shortTwoFactor F)) =
      (2 : MvPowerSeries EisensteinIdealPrime ℂ)^(Fintype.card ι-S.card)*
        ∏ i ∈ Finset.univ\S, twistArithmetic (q i) (η i) (t i) (shortTwoFactor F) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ]
  rw [hp]
  simp only [shortBranchScalar,map_mul,map_pow,map_neg,map_one,map_ofNat]
  ring

theorem twisted_prime_coeff_expansion {F : ℝ} (hF : 0 ≤ F)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν (∏ i, twistArithmetic (q i) (η i) (t i) idealVonMangoldt) =
      ∑ S : Finset ι, shortBranchScalar S * MvPowerSeries.coeff ν
        (∏ j : shortBranchIndex S,
          twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
            (t (shortBranchSource S j)) (shortBranchFactor F S j)) := by
  rw [twisted_short_product_coeff hF q η t ν hν,
    twisted_short_series_expansion F q η t,map_sum]
  simp only [MvPowerSeries.coeff_C_mul]

theorem primaryTwistedPrimeWeight_expansion (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (χ : Eisenstein → ℂ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y) :
    primaryComplexProductPolynomial (fun i => twistArithmetic (q i) (η i) (t i) idealVonMangoldt) χ V Y =
      ∑ S : Finset ι, shortBranchScalar S * primaryComplexProductPolynomial
        (fun j : shortBranchIndex S =>
          twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
            (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) χ V Y := by
  unfold primaryComplexProductPolynomial
  calc
    _ = ∑ b ∈ primaryElementBall (2*Y), ∑ S : Finset ι, shortBranchScalar S *
        MvPowerSeries.coeff (idealExponentOf b)
          (∏ j : shortBranchIndex S,
            twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
              (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j))*χ b*V (norm b/Y) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' := mem_primaryElementBall.mp hb
      have hN : idealExponentNorm (idealExponentOf b) ≤ 2*Y := by
        simpa only [idealExponentOf_norm (primary_ne_zero hb'.1)] using hb'.2
      rw [twisted_prime_coeff_expansion (by positivity : 0 ≤ 2*Y) q η t _ hN,
        Finset.sum_mul,Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedPrimeNeighborhood
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original von Mangoldt convolutions with independent factor twists inherit
the short-factor power saving by an exact finite expansion. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem first_twisted_vonMangoldt_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (Y N : ℝ) (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset Eisenstein), Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) → (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryComplexProductPolynomial (fun i => twistArithmetic (q i) (η i) (t i) idealVonMangoldt)
        (mixedCubic a 1) V Y‖^2) ≤ Y^(7/3-ε) := by
  choose κ hκ hκhi e he T hb using fun S : Finset ι =>
    first_twisted_convolution_neighborhood (ι := shortBranchIndex S) hpub V hV hpos hsm hVlo hVhi hGI hGQ
  obtain ⟨κ₀,hκ₀,hκall⟩ := finite_positive_lower_bound κ hκ
  obtain ⟨d,hd,T₁,hT₁,hsave⟩ := finite_weighted_moment_saving e he (shortBranchScalar (ι := ι))
  refine ⟨min κ₀ (1/10000),by positivity,min_le_right _ _,d,hd,max T₁ (1+∑ S, |T S|),?_⟩
  intro Y N q η t P hY hNlo hNhi hq hη hqY ht hP
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hYT (S : Finset ι) : T S ≤ Y := by
    have hS : |T S| ≤ ∑ U : Finset ι, |T U| :=
      Finset.single_le_sum (fun U _ => abs_nonneg (T U)) (Finset.mem_univ S)
    have hh : 1+∑ U : Finset ι, |T U| ≤ Y := (le_max_right _ _).trans hY
    linarith [le_abs_self (T S)]
  let f : Finset ι → P → ℂ := fun S a =>
    primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic a 1) V Y
  have hf (S : Finset ι) : (∑ a : P, ‖f S a‖^2) ≤ Y^(7/3-e S) := by
    have h := hb S (2*Y) Y N (shortBranchFactor (2*Y) S)
      (fun j => q (shortBranchSource S j)) (fun j => η (shortBranchSource S j))
      (fun j => t (shortBranchSource S j)) P
      (hYT S)
      ((Real.rpow_le_rpow_of_exponent_le hY1
        (by have := (min_le_left κ₀ (1/10000)).trans (hκall S); linarith)).trans hNlo)
      (hNhi.trans (Real.rpow_le_rpow_of_exponent_le hY1
        (by have := (min_le_left κ₀ (1/10000)).trans (hκall S); linarith))) le_rfl (shortBranchFactor_spec (2*Y) S)
      (fun j => hq _) (fun j => hη _) (fun j => hqY _) (fun j => ht _) hP
    change (∑ a ∈ P.attach, ‖f S a‖^2) ≤ _
    dsimp only [f]
    rw [Finset.sum_attach (f := fun a : Eisenstein =>
      ‖primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic a 1) V Y‖^2)]
    exact h
  have hm := hsave Y hYT₁ P f hf
  simp_rw [primaryTwistedPrimeWeight_expansion q η t _ V hYp]
  change (∑ a ∈ P.attach, ‖∑ S, shortBranchScalar S*f S a‖^2) ≤ _ at hm
  dsimp only [f] at hm
  rw [Finset.sum_attach (f := fun a : Eisenstein =>
    ‖∑ S : Finset ι, shortBranchScalar S*
      primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic a 1) V Y‖^2)] at hm
  exact hm

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformCoordinateWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma UniformLogWeights.zeroLine_moment {γ : Type*} {W : γ → ℝ → ℂ}
    (h : UniformLogWeights W) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, (∫ t : ℝ, |t|^A*‖zeroLineMellinWeight (W i) 1 t‖) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := h.mellin_norm_moment 0 A
  refine ⟨(1/(2*Real.pi))*C,by positivity,?_⟩
  intro i
  rw [zeroLineMellinWeight_moment (W i) (by norm_num) A]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Complex.ofReal_zero,zero_add] using hbound i 0 (by norm_num)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma independentMellinMoment_factorization (W : ι → ℝ → ℂ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (A : ℕ) :
    independentMellinMoment W A = ∑ i, ∏ j,
      (∫ t : ℝ, if j=i then |t|^A*‖zeroLineMellinWeight (W j) 1 t‖
        else ‖zeroLineMellinWeight (W j) 1 t‖) := by
  unfold independentMellinMoment mellinHeightPower
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ =>
    independentMellinWeight_coordinate_moment_integrable W (fun _ => 1) hW hpos hsm
      (fun _ => by norm_num) A i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_fintype_prod_volume_eq_prod (fun (j : ι) (t : ℝ) =>
    if j=i then |t|^A*‖zeroLineMellinWeight (W j) 1 t‖
      else ‖zeroLineMellinWeight (W j) 1 t‖)]
  apply integral_congr_ae
  filter_upwards with τ
  rw [independentMellinWeight,norm_prod]
  symm
  convert prod_one_coordinate (fun j => ‖zeroLineMellinWeight (W j) 1 (τ j)‖)
    i (|τ i|^A) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j=i <;> simp [hj]

/-- One bound controls the product L1 mass and the genuine joint tail moment
for every member of a uniformly smooth coordinate family. -/
theorem UniformLogWeights.coordinate_moments {γ : Type*} {W : γ → ι → ℝ → ℂ}
    (h : UniformLogWeights (fun z : γ × ι => W z.1 z.2)) (A : ℕ) :
    ∃ C J : ℝ, 0 ≤ C ∧ 0 ≤ J ∧ ∀ u : γ,
      (∏ i, zeroLineMellinMass (W u i)) ≤ C ∧ independentMellinMoment (W u) A ≤ J := by
  obtain ⟨C₀,hC₀,h₀⟩ := h.zeroLine_moment 0
  obtain ⟨C₁,hC₁,h₁⟩ := h.zeroLine_moment A
  let K := max C₀ C₁
  have hK : 0 ≤ K := hC₀.trans (le_max_left _ _)
  refine ⟨K^(Fintype.card ι),(Fintype.card ι:ℝ)*K^(Fintype.card ι),
    pow_nonneg hK _,by positivity,?_⟩
  intro u
  have hmass (i : ι) : zeroLineMellinMass (W u i) ≤ K := by
    have hh := (h₀ (u,i)).trans (le_max_left C₀ C₁)
    simp only [pow_zero,one_mul] at hh
    rw [zeroLineMellinWeight_mass (W u i) (Z := 1) (by norm_num)] at hh
    exact hh
  constructor
  · calc
      _ ≤ ∏ _i : ι, K := Finset.prod_le_prod (fun i _ => zeroLineMellinMass_nonneg (W u i))
        (fun i _ => hmass i)
      _ = _ := by simp
  · rw [independentMellinMoment_factorization (W u) (fun i => h.compact (u,i))
        (fun i => h.positive (u,i)) (fun i => h.smooth (u,i)) A]
    calc
      _ ≤ ∑ _i : ι, K^(Fintype.card ι) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ∏ _j : ι, K := by
            apply Finset.prod_le_prod
            · intro j _
              exact integral_nonneg (fun t => by split_ifs <;> positivity)
            · intro j _
              by_cases hj : j=i
              · simp only [hj,ite_true, if_true]
                exact (h₁ (u,i)).trans (le_max_right _ _)
              · simp only [hj,ite_false, if_false]
                rw [zeroLineMellinWeight_mass (W u j) (Z := 1) (by norm_num)]
                exact hmass j
          _ = _ := by simp
      _ = _ := by simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DilatedMomentPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventual_dilated_shift_height_bound :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ t τ : ℝ,
      |t| ≤ Y^(721/2000:ℝ) → |τ| ≤ Y^(1/1000:ℝ) → |t-τ| ≤ Y^(361/1000:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 1/2000 by norm_num)).eventually_ge_atTop (2:ℝ))
  refine ⟨max 1 T,?_⟩
  intro Y hY t τ ht hτ
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hτ' : |τ| ≤ Y^(721/2000:ℝ) := hτ.trans
    (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
  calc
    _ ≤ |t|+|τ| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le t 0 τ
    _ ≤ 2*Y^(721/2000:ℝ) := by linarith
    _ ≤ Y^(1/2000:ℝ)*Y^(721/2000:ℝ) :=
      mul_le_mul_of_nonneg_right (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonCoordinateExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional exponent is chosen before the smooth-weight family.
Only the threshold depends on its derivative constants. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem first_common_coordinate_exponents (hpub : PrimitiveResidueHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      ∃ Y₀ : ℝ, ∀ (u : γ) (Y N : ℝ) (X : ι → ℝ)
      (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → (∀ i, 0 < X i) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
        a 1 q η t (W u) X V Y‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,e,he,T,hraw⟩ := first_twisted_vonMangoldt_neighborhood (ι := ι)
    hpub V hV hposV hsmV hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,min e (1/3)/2,by positivity,?_⟩
  intro W hW
  obtain ⟨M,hM⟩ := hV.exists_bound_of_continuous hsmV.continuous
  have hM0 : 0 ≤ M := (_root_.norm_nonneg (V 0)).trans (hM 0)
  let k := Fintype.card ι
  let A := 1000*(2*k+7)
  let K : ℝ := M*72^k
  obtain ⟨L,J,hL,hJ,hMoments⟩ := hW.coordinate_moments A
  obtain ⟨T₁,hshift⟩ := eventual_dilated_shift_height_bound
  obtain ⟨T₂,hT₂,habs⟩ := absorb_short_mellin_bounds he (2*L^2) (2*K^2*J^2)
    (by positivity) (by positivity)
  refine ⟨max 36 (max T (max T₁ T₂)),?_⟩
  intro u Y N X q η t P hY hNlo hNhi hX hq hη hqY ht hP
  have hY36 : 36 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := by linarith
  have hYp : 0 < Y := by linarith
  have hYT : T ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYT₂ : T₂ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hb (τ : ι → ℝ) (hτ : τ ∈ mellinHeightBox (Y^(1/1000:ℝ))) :
      (∑ a : P, ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt)
        a 1 q η (fun i => t i-τ i) V Y‖^2) ≤ Y^(7/3-e) := by
    have hh := hraw Y N q η (fun i => t i-τ i) P hYT hNlo hNhi hq hη hqY
      (fun i => hshift Y hYT₁ _ _ (ht i) (hτ i)) hP
    have heq (a : Eisenstein) (ha : a ∈ P) :=
      twistedProductPolynomial_eq_unsplit (a := a) (b := 1) (fun _ : ι => idealVonMangoldt)
        (hP a ha).1 (by norm_num [primary]) q η hη (fun i => t i-τ i) V hYp hVhi
    have hh' : (∑ a ∈ P, ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt)
        a 1 q η (fun i => t i-τ i) V Y‖^2) ≤ Y^(7/3-e) := by
      calc
        _ = ∑ a ∈ P, ‖primaryComplexProductPolynomial
            (fun i => twistArithmetic (q i) (η i) (t i-τ i) idealVonMangoldt) (mixedCubic a 1) V Y‖^2 :=
          Finset.sum_congr rfl (fun a ha => by rw [heq a ha])
        _ ≤ _ := hh
    change (∑ a ∈ P.attach, ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt)
      a 1 q η (fun i => t i-τ i) V Y‖^2) ≤ _
    rw [Finset.sum_attach (f := fun a : Eisenstein =>
      ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt) a 1 q η (fun i => t i-τ i) V Y‖^2)]
    exact hh'
  have hm := coordinate_vonMangoldt_moment_bound (fun a : P => ((a : Eisenstein),1))
    (fun a => ⟨(hP a a.property).1,by norm_num [primary]⟩) q η hq t (W u) X
    (fun i => hW.compact (u,i)) (fun i => hW.positive (u,i))
    (fun i => hW.smooth (u,i)) hX V hM0 hM hYp.le A (Real.rpow_pos_of_pos hYp _)
    (Real.rpow_nonneg hYp.le _) hb
  have hcard : (Fintype.card P:ℝ) ≤ Y^4 := by
    have hN : 1 ≤ N := (Real.one_le_rpow hY1 (by linarith : 0 ≤ 1-κ)).trans hNlo
    have hNY : N ≤ Y^2 := by
      simpa only [Real.rpow_two] using hNhi.trans
        (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith : 1+κ ≤ 2))
    simpa only [Fintype.card_coe] using neighborhood_cubic_card P hY36 hN hNY hP
  have hm' : (∑ a ∈ P, ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
      a 1 q η t (W u) X V Y‖^2) ≤ 2*L^2*Y^(7/3-e)+
        2*(Fintype.card P:ℝ)*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := by
    change (∑ a ∈ P.attach, _) ≤ _ at hm
    rw [Finset.sum_attach (f := fun a : Eisenstein =>
      ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt) a 1 q η t (W u) X V Y‖^2)] at hm
    have hmass0 : 0 ≤ ∏ i, zeroLineMellinMass (W u i) :=
      Finset.prod_nonneg (fun i _ => zeroLineMellinMass_nonneg _)
    have hjoint0 := independentMellinMoment_nonneg (W u) A
    apply hm.trans
    gcongr
    · exact (hMoments u).1
    · exact (hMoments u).2
  calc
    _ ≤ 2*L^2*Y^(7/3-e)+2*(Fintype.card P:ℝ)*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := hm'
    _ ≤ 2*L^2*Y^(7/3-e)+2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := by gcongr
    _ ≤ 2*L^2*Y^(7/3-e)+(2*K^2*J^2)*Y^(-42/5:ℝ) := by
      exact add_le_add le_rfl (coordinate_neighborhood_tail_le_short_tail (K := K) (J := J) k hY1)
    _ ≤ _ := habs Y hYT₂


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothLogDenominator
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth, globally defined extensions of the logarithmic denominator
weights. The extension equals the literal reciprocal on the application
range, so no pole can interfere with parameter-uniform differentiation. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CubicFirstMoment

lemma positiveSmoothExtension_eq {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    positiveSmoothExtension c x = x := by
  have h : 1 ≤ 2*x/c-1 := by
    have hd : 2 ≤ 2*x/c := (le_div_iff₀ hc).mpr (by linarith)
    linarith
  simp [positiveSmoothExtension,Real.smoothTransition.one_of_one_le h]

lemma smoothReciprocal_eq {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    smoothReciprocal c x = x⁻¹ := by
  simp only [smoothReciprocal,positiveSmoothExtension_eq hc hx]

lemma smoothLog_eq {x : ℝ} (hx : 1 ≤ x) : smoothLog x = Real.log x := by
  simp only [smoothLog,positiveSmoothExtension_eq (by norm_num : (0:ℝ) < 1) hx]

lemma logDenominatorWeight_eq {c : ℝ} (hc : 0 < c) (w : ℝ → ℂ)
    {p : ℝ × ℝ} (ha : c ≤ p.1) (ht : 0 ≤ p.2) {x : ℝ} (hx : 1 ≤ x) :
    logDenominatorWeight c w p x = w x/(p.1+p.2*Real.log x:ℝ) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hd : c ≤ p.1+p.2*Real.log x := by nlinarith
  rw [logDenominatorWeight,smoothLog_eq hx,smoothReciprocal_eq hc hd]
  push_cast
  ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideLogDenominator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic coordinate range accommodates the fixed dilations in
an output norm partition. The denominator identities need no upper range. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

lemma wideLogWeightParameters_mem {c Y X : ℝ} (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y)
    (hlo : Y^c ≤ X) (hhi : X ≤ Y^2) :
    (Real.log X/Real.log Y,1/Real.log Y) ∈ wideLogWeightParameters c := by
  have hlogY : 0 < Real.log Y := by linarith
  have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
  refine ⟨⟨?_,?_⟩,⟨by positivity,?_⟩⟩
  · apply (le_div_iff₀ hlogY).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hY0 c) hlo
    rw [Real.log_rpow hY0] at h
    nlinarith
  · apply (div_le_iff₀ hlogY).mpr
    have h := Real.log_le_log hX hhi
    rw [Real.log_pow] at h
    norm_num at h ⊢
    linarith
  · exact (one_div_le_one_div_of_le (by norm_num) hY).trans_eq (by norm_num)

lemma logDenominatorWeight_scale_lower {c Y X x : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (hlo : Y^c ≤ X) (hx : 1 ≤ x)
    (w : ℝ → ℂ) :
    logDenominatorWeight c w (Real.log X/Real.log Y,1/Real.log Y) x =
      (Real.log Y:ℂ)*w x/(Real.log (X*x):ℂ) := by
  have hlogY : 0 < Real.log Y := by linarith
  have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
  have hp : c ≤ Real.log X/Real.log Y := by
    apply (le_div_iff₀ hlogY).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hY0 c) hlo
    rw [Real.log_rpow hY0] at h
    linarith
  have hx0 : 0 < x := by linarith
  rw [logDenominatorWeight_eq hc w hp (by positivity) hx,Real.log_mul hX.ne' hx0.ne']
  push_cast
  have hCY : (Real.log Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogY.ne'
  field_simp

lemma normalizedVonMangoldt_weight_lower {c Y X : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (hlo : Y^c ≤ X)
    (w : ℝ → ℂ) (hw : ∀ x, x < 1 → w x = 0) (a : Eisenstein) :
    (normalizedVonMangoldt a:ℂ)*w (norm a/X) =
      (1/(Real.log Y:ℂ))*((MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt:ℝ):ℂ)*
        logDenominatorWeight c w (Real.log X/Real.log Y,1/Real.log Y) (norm a/X) := by
  by_cases hx : 1 ≤ norm a/X
  · have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
    rw [logDenominatorWeight_scale_lower hc hY0 hY hlo hx]
    have he : X*(norm a/X) = norm a := by field_simp
    rw [he]
    unfold normalizedVonMangoldt
    push_cast
    have hCY : (Real.log Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith))
    field_simp
  · have hz := hw _ (lt_of_not_ge hx)
    simp only [hz,mul_zero,logDenominatorWeight]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primaryNormalizedVonMangoldtTuple_eq_lower {c Y : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) :
    primaryNormalizedVonMangoldtTuple a b q η t W X V Y =
      (1/(Real.log Y:ℂ))^(Fintype.card ι)*
      primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y := by
  unfold primaryNormalizedVonMangoldtTuple primaryCoordinateWeightedTuple primaryTupleCore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [normalizedVonMangoldt_weight_lower hc hY0 hY (hXlo _) _ (hWlo _)]
  have he (i : ι) :
      1/(Real.log Y:ℂ)*((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        logDenominatorWeight c (W i) (Real.log (X i)/Real.log Y,1/Real.log Y) (norm (n i)/X i)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
          mellinPhase (t i) (norm (n i))) =
      (1/(Real.log Y:ℂ))*
        (((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
          mellinPhase (t i) (norm (n i))))*
        logDenominatorWeight c (W i) (Real.log (X i)/Real.log Y,1/Real.log Y) (norm (n i)/X i) := by ring
  simp_rw [he,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  ring

lemma normalizedCoordinate_norm_le_lower {c Y : ℝ} (hc : 0 < c) (hY0 : 0 < Y)
    (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) :
    ‖primaryNormalizedVonMangoldtTuple a b q η t W X V Y‖ ≤
      ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y‖ := by
  rw [primaryNormalizedVonMangoldtTuple_eq_lower hc hY0 hY a b q η t W X V hWlo hXlo,
    norm_mul,norm_pow]
  apply mul_le_of_le_one_left (_root_.norm_nonneg _)
  apply pow_le_one₀ (_root_.norm_nonneg _) _
  rw [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
  exact (div_le_one (by linarith)).mpr hY

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonNormalizedExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both normalized prime moments uniformly over actual smooth-weight families. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem first_common_normalized_exponents (hpub : PrimitiveResidueHeckeInput)
    {c : ℝ} (hc : 0 < c)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y N : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → 0 < Y → 1 ≤ Real.log Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) →
      (∀ i, Y^c ≤ X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryNormalizedVonMangoldtTuple a 1 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,e,he,hraw⟩ := first_common_coordinate_exponents
    (γ := γ × (ι → wideLogWeightParameters c)) (ι := ι) hpub V hV hposV hsmV hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,e,he,?_⟩
  intro W hW hWlo
  let L : (γ × (ι → wideLogWeightParameters c)) → ι → ℝ → ℂ :=
    fun r i => logDenominatorWeight c (W r.1 i) (r.2 i)
  have hL : UniformLogWeights (fun z : (γ × (ι → wideLogWeightParameters c)) × ι => L z.1 z.2) :=
    uniformCoordinateWideLogDenominatorWeights hc hW
  obtain ⟨T,hfamily⟩ := hraw L hL
  refine ⟨T,?_⟩
  intro r Y N X q η t P hYT hY0 hlog hNlo hNhi hXlo hXhi hq hη hqY ht hP
  let p : ι → wideLogWeightParameters c := fun i =>
    ⟨(Real.log (X i)/Real.log Y,1/Real.log Y),wideLogWeightParameters_mem hY0 hlog (hXlo i) (hXhi i)⟩
  have hb := hfamily (r,p) Y N X q η t P hYT hNlo hNhi
    (fun i => (Real.rpow_pos_of_pos hY0 c).trans_le (hXlo i)) hq hη hqY ht hP
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro a ha
  exact pow_le_pow_left₀ (_root_.norm_nonneg _)
    (normalizedCoordinate_norm_le_lower hc hY0 hlog a 1 q η t (W r) X V (hWlo r) hXlo) 2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary power margins used to return from a global cutoff at
2Y to the original exceptional conductor neighborhoods. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma twice_rpow_le_mul_rpow {Y e : ℝ} (hY : 0 ≤ Y) (he : 1 ≤ e) :
    2*Y^e ≤ (2*Y)^e := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hY]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hY _)
  calc
    (2:ℝ) = 2^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) he

lemma first_prime_error_rows {Y N κ c : ℝ} (hY : 1 ≤ Y) (hc : 0 < c)
    (hκ : κ ≤ c/256) (hN : N ≤ Y^(1+κ)) (a : Eisenstein) (ha : gramDyad N a) :
    primary a ∧ Squarefree a ∧ norm a ≤ (2*Y)^(1+c/256) := by
  refine ⟨ha.1,ha.2.1,?_⟩
  calc
    norm a ≤ 2*N := ha.2.2.2.le
    _ ≤ 2*Y^(1+κ) := by gcongr
    _ ≤ 2*Y^(1+c/256) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hY (by linarith)) (by norm_num)
    _ ≤ _ := twice_rpow_le_mul_rpow (by linarith) (by linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExplicitMomentAbsorption
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit error exponents, independent of the coefficient-bound constants. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma absorb_prime_coordinate_error_explicit {e d C : ℝ} (he : 0 < e) (hd : 0 < d)
    (hC : 0 ≤ C) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y →
      2*Y^(7/3-e)+2*C*(2*Y)^(7/3-d) ≤ Y^(7/3-min e d/2) := by
  let δ := min e d
  let K := 2+2*C*2^(7/3-d)
  have hδ : 0 < δ := lt_min he hd
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < δ/2 by positivity)).eventually_ge_atTop K)
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have h₁ : Y^(7/3-e) ≤ Y^(7/3-δ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by dsimp [δ]; linarith [min_le_left e d])
  have h₂ : Y^(7/3-d) ≤ Y^(7/3-δ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by dsimp [δ]; linarith [min_le_right e d])
  calc
    _ = 2*Y^(7/3-e)+(2*C*2^(7/3-d))*Y^(7/3-d) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hYp.le]
      ring
    _ ≤ 2*Y^(7/3-δ)+(2*C*2^(7/3-d))*Y^(7/3-δ) := by gcongr
    _ = K*Y^(7/3-δ) := by dsimp [K]; ring
    _ ≤ Y^(δ/2)*Y^(7/3-δ) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

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

/-- Collection and support restriction are identities for arbitrary
coefficient functions; the prime and normalized prime cases specialize it. -/
lemma coordinate_convolution_collection (A : Eisenstein → ℂ)
    (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    (∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
      (∏ i, A (n i)*W i (norm (n i)/X i)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
          mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y)) =
    ∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
      orderedConvolution (coordinateSupport W X Y)
        (fun i n => A n*coordinateFactor q η t W X i n) z*
        (mixedCubic a b z*V (norm z/Y)) := by
  rw [orderedConvolution_sum]
  let S : ι → Finset Eisenstein := fun _ => primaryElementBall (2*Y)
  let F : (ι → Eisenstein) → ℂ := fun n =>
    (∏ i, A (n i)*W i (norm (n i)/X i)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y)
  have hsub : Fintype.piFinset (coordinateSupport W X Y) ⊆ Fintype.piFinset S := by
    intro n hn
    exact Fintype.mem_piFinset.mpr (fun i => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1)
  have he : (∑ n ∈ Fintype.piFinset (coordinateSupport W X Y), F n) =
      ∑ n ∈ Fintype.piFinset S, F n := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hex : ∃ i, W i (norm (n i)/X i) = 0 := by
      by_contra hh
      push Not at hh
      exact hnot (Fintype.mem_piFinset.mpr (fun i =>
        Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hn i,hh i⟩))
    obtain ⟨i,hi⟩ := hex
    dsimp [F]
    have hz : (∏ j, A (n j)*W j (norm (n j)/X j)*
      (mixedCubic a b (n j)*η j (Ideal.Quotient.mk (modulus (q j)) (n j))*
        mellinPhase (t j) (norm (n j)))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hi,mul_zero,zero_mul]
    rw [hz,zero_mul]
  change (∑ n ∈ Fintype.piFinset S, F n) = _
  rw [← he]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [F,coordinateFactor]
  rw [mixedCubic_prod _ _ ha hb,norm_finset_prod]
  rw [← mul_assoc,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateDifference
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact difference between normalized von Mangoldt tuples and
original prime-indicator tuples on the global smooth cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normalized_prime_tuple_difference (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryNormalizedVonMangoldtTuple a b q η t W X V Y-
        primaryPrimeIndicatorTuple a b q η t W X V Y =
      ∑ z ∈ coordinateProductCutoff W X Y,
        primeLogConvolutionError (coordinateSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*V (norm z/Y)) := by
  have hn := coordinate_convolution_collection (fun n => (normalizedVonMangoldt n:ℂ))
    a b ha hb q η t W X V Y
  have hp := coordinate_convolution_collection (fun n => (primeIndicator n:ℂ))
    a b ha hb q η t W X V Y
  change primaryNormalizedVonMangoldtTuple a b q η t W X V Y = _ at hn
  change primaryPrimeIndicatorTuple a b q η t W X V Y = _ at hp
  rw [hn,hp,← Finset.sum_sub_distrib]
  have he : (∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
      (orderedConvolution (coordinateSupport W X Y)
        (fun i n => (normalizedVonMangoldt n:ℂ)*coordinateFactor q η t W X i n) z*
          (mixedCubic a b z*V (norm z/Y))-
       orderedConvolution (coordinateSupport W X Y)
        (fun i n => (primeIndicator n:ℂ)*coordinateFactor q η t W X i n) z*
          (mixedCubic a b z*V (norm z/Y)))) =
      ∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
        primeLogConvolutionError (coordinateSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*V (norm z/Y)) := by
    apply Finset.sum_congr rfl
    intro z hz
    unfold primeLogConvolutionError
    ring
  rw [he]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hlarge : 2*Y < norm z := lt_of_not_ge (fun h => hnot (Finset.mem_filter.mpr ⟨hz,h⟩))
  have hv := hV (norm z/Y) ((lt_div_iff₀ hY).mpr hlarge)
  rw [hv,mul_zero,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorMomentTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact normalized-prime discrepancy transfers second moments to
original prime-indicator convolutions. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeIndicator_moment_transfer {ρ : Type*} (P : Finset ρ)
    (a b : ρ → Eisenstein) (hab : ∀ r ∈ P, primary (a r) ∧ primary (b r))
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    (∑ r ∈ P, ‖primaryPrimeIndicatorTuple (a r) (b r) q η t W X V Y‖^2) ≤
      2*(∑ r ∈ P, ‖primaryNormalizedVonMangoldtTuple (a r) (b r) q η t W X V Y‖^2)+
      2*(∑ r ∈ P, ‖primeCoordinateError (a r) (b r) q η t W X V Y‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  apply norm_square_le_central_tail
  rw [norm_sub_rev,normalized_prime_tuple_difference (a r) (b r)
    (hab r hr).1 (hab r hr).2 q η t W X V hY hV]
  exact le_rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonPrimeIndicatorExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weight-independent exponents for uniform smooth families. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem first_common_prime_exponents_oai (hpub : PrimitiveResidueHeckeInput)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y N : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → 1 ≤ Real.log Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) →
      (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryPrimeIndicatorTuple a 1 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ₀,hκ₀,hκ₀hi,e,he,hfamily⟩ := first_common_normalized_exponents (γ := γ) (ι := ι)
    hpub hc V hV hposV hsmV hVlo hVhi hGI hGQ
  obtain ⟨C,hC,herr⟩ := first_primeCoordinateError_moment (ι := ι) hc hc₁
  let κ := min κ₀ (c/256)
  have hκ : 0 < κ := lt_min hκ₀ (by positivity)
  have hκle : κ ≤ κ₀ := min_le_left _ _
  have hκc : κ ≤ c/256 := min_le_right _ _
  refine ⟨κ,hκ,hκle.trans hκ₀hi,min e (c/32)/2,by positivity,?_⟩
  intro W hW hWlo
  obtain ⟨T₀,hnorm⟩ := hfamily W hW hWlo
  obtain ⟨K,hK,hbound⟩ := hW.norm_bound
  let M : ι → ℝ := fun _ => K
  have hM0 : ∀ i, 0 ≤ M i := fun _ => hK
  let E := C*(∏ i, M i)^2
  obtain ⟨T₁,hT₁,habs⟩ := absorb_prime_coordinate_error_explicit he
    (show 0 < c/32 by positivity) (show 0 ≤ E by dsimp [E]; positivity)
  refine ⟨max T₀ T₁,?_⟩
  intro r Y N X q η t P hYT hlog hNlo hNhi hXlo hXhi hq hη hqY ht hP
  have hM : ∀ i x, ‖W r i x‖ ≤ M i := fun i x => hbound (r,i) x
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans hYT
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans hYT
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hNXlo : ∀ i, Y^c ≤ X i := fun i =>
    (Real.rpow_le_rpow hYp.le (by linarith : Y ≤ 2*Y) hc.le).trans (hXlo i).le
  have hNlo₀ : Y^(1-κ₀) ≤ N :=
    (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)).trans hNlo
  have hNhi₀ : N ≤ Y^(1+κ₀) := hNhi.trans
    (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith))
  have hn := hnorm r Y N X q η t P hYT₀ hYp hlog hNlo₀ hNhi₀ hNXlo hXhi hq hη hqY ht hP
  have hd := herr q η t (W r) M X V Y hY1 hq hM0 hM (hWlo r) hXlo hVnorm P
    (fun a ha => first_prime_error_rows hY1 hc hκc hNhi a (hP a ha))
  have hm := primeIndicator_moment_transfer P (fun a => a) (fun _ => 1)
    (fun a ha => ⟨(hP a ha).1,by norm_num [primary]⟩) q η t (W r) X V hYp hVhi
  calc
    _ ≤ 2*(∑ a ∈ P, ‖primaryNormalizedVonMangoldtTuple a 1 q η t (W r) X V Y‖^2)+
        2*(∑ a ∈ P, ‖primeCoordinateError a 1 q η t (W r) X V Y‖^2) := hm
    _ ≤ 2*Y^(7/3-e)+2*E*(2*Y)^(7/3-c/32) := by dsimp [E]; linarith
    _ ≤ _ := habs Y hYT₁


end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CubicFirstMoment.first_common_prime_exponents_oai.{u_1, u_2} := @OAI.CubicFirstMoment.first_common_prime_exponents_oai.{u_1, u_2}
