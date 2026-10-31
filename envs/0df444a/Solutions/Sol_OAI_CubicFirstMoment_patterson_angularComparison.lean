-- Prove2me | solution 1 for OAI.CubicFirstMoment.patterson_angularComparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:44:15.52882+00:00
-- url     : https://prove2.me/submissions/11f63860-a4cc-4797-b149-6aa281ce7cf6

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_cubicTheta_primeProductGaussTail_isLittleO
import Theorems.Thm_OAI_CubicFirstMoment_cubicTheta_primeProductLowHeight_isLittleO

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

lemma idealMoebius_primaryPrime {p : Eisenstein} (hp : primaryPrime p) :
    idealMoebius p = -1 := hp.2.irreducible.moebius_eq

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

/-- The bias constant in the manuscript is strictly positive. -/
theorem cStar_pos : 0 < cStar := by
  unfold cStar
  positivity

/-- The scale of the first moment is positive beyond one. -/
theorem firstMomentScale_pos {X : ℝ} (hX : 1 < X) : 0 < firstMomentScale X := by
  unfold firstMomentScale
  exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos hX)

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

/-- The Fourier truncation loss is controlled by a fixed power saving.
The harmless `1` term is dominated by the interval-length term. -/
theorem truncationError_le {X ε ρ : ℝ} (hX : 1 ≤ X) (hρ : ρ ≤ 5 / 6) :
    X ^ ε * (1 + X / X ^ (1 / 6 + ρ : ℝ)) ≤
      2 * X ^ (5 / 6 - (ρ - ε) : ℝ) := by
  have hX₀ : 0 < X := zero_lt_one.trans_le hX
  have hpow : X / X ^ (1 / 6 + ρ : ℝ) = X ^ (5 / 6 - ρ : ℝ) := by
    calc
      X / X ^ (1 / 6 + ρ : ℝ) =
          X ^ (1 : ℝ) / X ^ (1 / 6 + ρ : ℝ) := by rw [Real.rpow_one]
      _ = X ^ (1 - (1 / 6 + ρ) : ℝ) := (Real.rpow_sub hX₀ _ _).symm
      _ = X ^ (5 / 6 - ρ : ℝ) := by congr 1; ring
  rw [hpow]
  have h₁ : (1 : ℝ) ≤ X ^ (5 / 6 - ρ : ℝ) :=
    Real.one_le_rpow hX (by linarith)
  have hε : 0 ≤ X ^ ε := Real.rpow_nonneg hX₀.le ε
  have hmul : X ^ ε * X ^ (5 / 6 - ρ : ℝ) =
      X ^ (5 / 6 - (ρ - ε) : ℝ) := by
    rw [← Real.rpow_add hX₀]
    congr 1
    ring
  nlinarith [mul_le_mul_of_nonneg_left h₁ hε]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_EndpointKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summing the sharp-cutoff endpoint kernel

The Fourier truncation argument sums rapidly decaying endpoint errors over
integer norms. These bounds supply the quantitative lattice step in
`eq:perron-error`, uniformly in the location of the endpoint.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

lemma endpointKernel_nat_step {h : ℝ} (hh : 0 < h) (k : ℕ) :
    h ^ 2 / (h + (k : ℝ) + 1) ^ 2 ≤
      h ^ 2 / (h + (k : ℝ)) - h ^ 2 / (h + (k : ℝ) + 1) := by
  have hk : 0 < h + (k : ℝ) := by positivity
  have hk' : 0 < h + (k : ℝ) + 1 := by positivity
  have he : h ^ 2 / (h + (k : ℝ)) - h ^ 2 / (h + (k : ℝ) + 1) =
      h ^ 2 / ((h + (k : ℝ)) * (h + (k : ℝ) + 1)) := by
    field_simp
    ring
  rw [he]
  exact div_le_div_of_nonneg_left (sq_nonneg h) (by positivity) (by nlinarith)

lemma endpointKernel_tail_sum {h : ℝ} (hh : 0 < h) (n : ℕ) :
    (∑ k ∈ Finset.range n, h ^ 2 / (h + (k : ℝ) + 1) ^ 2) ≤
      h - h ^ 2 / (h + (n : ℝ)) := by
  induction n with
  | zero => simp [hh.ne', pow_two]
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_add_one]
    have hn := endpointKernel_nat_step hh n
    simp only [add_assoc] at *
    linarith

lemma endpointKernel_range_sum {h : ℝ} (hh : 0 < h) (n : ℕ) :
    (∑ k ∈ Finset.range n, h ^ 2 / (h + (k : ℝ)) ^ 2) ≤ 1 + h := by
  cases n with
  | zero => simp; positivity
  | succ n =>
    rw [Finset.sum_range_succ']
    have he : (∑ k ∈ Finset.range n, h ^ 2 / (h + ((k + 1 : ℕ) : ℝ)) ^ 2) =
        ∑ k ∈ Finset.range n, h ^ 2 / (h + (k : ℝ) + 1) ^ 2 := by
      simp only [Nat.cast_add_one, add_assoc]
    rw [he]
    have h0 : h ^ 2 / (h + (0 : ℕ)) ^ 2 = 1 := by simp [hh.ne']
    rw [h0]
    have hn := endpointKernel_tail_sum hh n
    have hpos : 0 ≤ h ^ 2 / (h + (n : ℝ)) := by positivity
    linarith

lemma endpointKernel_finite_nat_sum {h : ℝ} (hh : 0 < h) (s : Finset ℕ) :
    (∑ k ∈ s, h ^ 2 / (h + (k : ℝ)) ^ 2) ≤ 1 + h := by
  have hs : s ⊆ Finset.range (s.sup id + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun _ _ _ => div_nonneg (sq_nonneg h) (sq_nonneg _))).trans
      (endpointKernel_range_sum hh _)

lemma endpointKernel_mono {h d e : ℝ} (hh : 0 < h)
    (hd : 0 ≤ d) (hde : d ≤ |e|) :
    endpointKernel h e ≤ h ^ 2 / (h + d) ^ 2 := by
  unfold endpointKernel
  apply div_le_div_of_nonneg_left (sq_nonneg h) (by positivity)
  nlinarith [abs_nonneg e]

/-- All integer norms to the left of an endpoint can be indexed by their
distinct nonnegative integer distances from a fixed integer below it. -/
lemma endpointKernel_integer_left {h x : ℝ} (hh : 0 < h) (z : ℤ)
    (hz : (z : ℝ) ≤ x) (s : Finset ℤ) (hs : ∀ n ∈ s, n ≤ z) :
    (∑ n ∈ s, endpointKernel h ((n : ℝ) - x)) ≤ 1 + h := by
  let g : ℤ → ℕ := fun n => (z - n).toNat
  have hgc n (hn : n ∈ s) : (g n : ℝ) = (z : ℝ) - (n : ℝ) := by
    dsimp [g]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr (hs n hn)), Int.cast_sub]
  have hinj : Set.InjOn g s := by
    intro a ha b hb he
    have h := congrArg (fun n : ℕ => (n : ℝ)) he
    rw [hgc a ha, hgc b hb] at h
    have hab : (a : ℝ) = (b : ℝ) := by linarith
    exact_mod_cast hab
  calc
    _ ≤ ∑ n ∈ s, h ^ 2 / (h + (g n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply endpointKernel_mono hh (Nat.cast_nonneg _)
      rw [hgc n hn]
      have hnz : (n : ℝ) ≤ z := by exact_mod_cast hs n hn
      rw [abs_of_nonpos (by linarith : (n : ℝ) - x ≤ 0)]
      linarith
    _ = ∑ k ∈ s.image g, h ^ 2 / (h + (k : ℝ)) ^ 2 := (Finset.sum_image (f := fun k : ℕ => h ^ 2 / (h + (k : ℝ)) ^ 2) hinj).symm
    _ ≤ _ := endpointKernel_finite_nat_sum hh _

lemma endpointKernel_integer_right {h x : ℝ} (hh : 0 < h) (z : ℤ)
    (hz : x ≤ (z : ℝ)) (s : Finset ℤ) (hs : ∀ n ∈ s, z ≤ n) :
    (∑ n ∈ s, endpointKernel h ((n : ℝ) - x)) ≤ 1 + h := by
  let g : ℤ → ℕ := fun n => (n - z).toNat
  have hgc n (hn : n ∈ s) : (g n : ℝ) = (n : ℝ) - (z : ℝ) := by
    dsimp [g]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr (hs n hn)), Int.cast_sub]
  have hinj : Set.InjOn g s := by
    intro a ha b hb he
    have h := congrArg (fun n : ℕ => (n : ℝ)) he
    rw [hgc a ha, hgc b hb] at h
    have hab : (a : ℝ) = (b : ℝ) := by linarith
    exact_mod_cast hab
  calc
    _ ≤ ∑ n ∈ s, h ^ 2 / (h + (g n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply endpointKernel_mono hh (Nat.cast_nonneg _)
      rw [hgc n hn]
      have hzn : (z : ℝ) ≤ n := by exact_mod_cast hs n hn
      rw [abs_of_nonneg (by linarith : 0 ≤ (n : ℝ) - x)]
      linarith
    _ = ∑ k ∈ s.image g, h ^ 2 / (h + (k : ℝ)) ^ 2 := (Finset.sum_image (f := fun k : ℕ => h ^ 2 / (h + (k : ℝ)) ^ 2) hinj).symm
    _ ≤ _ := endpointKernel_finite_nat_sum hh _

/-- Uniform in the real endpoint, including exact equality with an integer.
This supplies the `O(1+X/T)` integer-norm sum in Fourier truncation. -/
theorem endpointKernel_integer_sum {h : ℝ} (hh : 0 < h) (x : ℝ) (s : Finset ℤ) :
    (∑ n ∈ s, endpointKernel h ((n : ℝ) - x)) ≤ 2 * (1 + h) := by
  have hleft := endpointKernel_integer_left (x := x) hh ⌊x⌋ (Int.floor_le x)
    (s.filter (fun n => n ≤ ⌊x⌋)) (fun n hn => (Finset.mem_filter.mp hn).2)
  have hright := endpointKernel_integer_right (x := x) hh (⌊x⌋ + 1)
    (by have h := Int.lt_floor_add_one x; push_cast; linarith)
    (s.filter (fun n => ¬n ≤ ⌊x⌋)) (fun n hn => by
      have h := (Finset.mem_filter.mp hn).2
      omega)
  have he := Finset.sum_filter_add_sum_filter_not s (fun n => n ≤ ⌊x⌋)
    (fun n => endpointKernel h ((n : ℝ) - x))
  linarith

/-- Summing errors localized near the two endpoints, including endpoints
that are integer norms. The coefficient bound is imposed after collecting
equal norms, as required by the manuscript. -/
theorem weighted_endpoint_error {h C M : ℝ} (hh : 0 < h) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (s : Finset ℤ) (x y : ℝ) (c error : ℤ → ℂ)
    (hc : ∀ n ∈ s, ‖c n‖ ≤ M)
    (he : ∀ n ∈ s, ‖error n‖ ≤ C *
      (endpointKernel h ((n : ℝ) - x) + endpointKernel h ((n : ℝ) - y))) :
    ‖∑ n ∈ s, c n * error n‖ ≤ 4 * C * M * (1 + h) := by
  calc
    _ ≤ ∑ n ∈ s, ‖c n * error n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, M * (C *
        (endpointKernel h ((n : ℝ) - x) + endpointKernel h ((n : ℝ) - y))) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul (hc n hn) (he n hn) (_root_.norm_nonneg _) hM
    _ = M * C * ((∑ n ∈ s, endpointKernel h ((n : ℝ) - x)) +
        ∑ n ∈ s, endpointKernel h ((n : ℝ) - y)) := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib]
      ring
    _ ≤ M * C * (2 * (1 + h) + 2 * (1 + h)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (endpointKernel_integer_sum hh x s) (endpointKernel_integer_sum hh y s))
        (mul_nonneg hM hC)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IntervalSmoothing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The endpoint error of a smoothed interval

A normalized integrable kernel approximates an interval indicator with
error controlled by its two tails. The proof retains exact endpoints.
This is the physical-space step of the Fourier truncation argument.
-/

noncomputable section
open MeasureTheory

namespace CubicFirstMoment

/-- A shift smaller than the distance to both endpoints preserves membership. -/
theorem intervalStep_eq_of_away {a b s y : ℝ}
    (ha : |y| < |s - a|) (hb : |y| < |s - b|) :
    intervalStep a b (s - y) = intervalStep a b s := by
  have hae : a ≤ s - y ↔ a ≤ s := by
    by_cases h : a ≤ s
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at ha
      have hy := le_abs_self y
      constructor <;> intro <;> linarith
    · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))] at ha
      have hy := neg_abs_le y
      constructor <;> intro <;> linarith
  have hbe : s - y ≤ b ↔ s ≤ b := by
    by_cases h : s ≤ b
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hb
      have hy := neg_abs_le y
      constructor <;> intro <;> linarith
    · rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge h))] at hb
      have hy := le_abs_self y
      constructor <;> intro <;> linarith
  simp only [intervalStep, Set.mem_Icc, hae, hbe]

/-- Any change in the indicator crosses at least one endpoint. -/
theorem intervalStep_jump_le (a b s y : ℝ) :
    |intervalStep a b s - intervalStep a b (s - y)| ≤
      (if |s - a| ≤ |y| then (1 : ℝ) else 0) +
      (if |s - b| ≤ |y| then (1 : ℝ) else 0) := by
  have hone : |intervalStep a b s - intervalStep a b (s - y)| ≤ 1 := by
    unfold intervalStep
    split_ifs <;> norm_num
  by_cases ha : |s - a| ≤ |y|
  · by_cases hb : |s - b| ≤ |y| <;> simp only [ha, hb, ite_true, if_true, ite_false, if_false] <;> linarith
  · by_cases hb : |s - b| ≤ |y|
    · simpa only [ha, hb, ite_true, if_true, ite_false, if_false, zero_add] using hone
    · rw [intervalStep_eq_of_away (lt_of_not_ge ha) (lt_of_not_ge hb)]
      simp [ha, hb]

theorem integrable_intervalSmoothing_integrand {k : ℝ → ℂ} (hk : Integrable k)
    (a b s : ℝ) : Integrable (fun y => (intervalStep a b (s-y) : ℂ) * k y) := by
  have hm : MeasurableSet {y : ℝ | s-y ∈ Set.Icc a b} :=
    measurableSet_Icc.preimage (measurable_const.sub measurable_id)
  have heq : (fun y => (intervalStep a b (s-y) : ℂ) * k y) =
      {y : ℝ | s-y ∈ Set.Icc a b}.indicator k := by
    funext y
    by_cases hy : s-y ∈ Set.Icc a b <;>
      simp only [intervalStep, Set.indicator_apply, Set.mem_ofPred_eq, hy,
        ite_true, if_true, ite_false, if_false, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul]
  rw [heq]
  exact hk.indicator hm

/-- The smoothed indicator has an error bounded by the kernel mass beyond
the distances to the two endpoints. No positivity of the kernel is needed. -/
theorem intervalSmoothing_error_le_tails {k : ℝ → ℂ} (hk : Integrable k)
    (hmass : ∫ y, k y = 1) (a b s : ℝ) :
    ‖(intervalStep a b s : ℂ) - intervalSmoothing k a b s‖ ≤
      (∫ y, if |s-a| ≤ |y| then ‖k y‖ else 0) +
      (∫ y, if |s-b| ≤ |y| then ‖k y‖ else 0) := by
  have hshift := integrable_intervalSmoothing_integrand hk a b s
  have hconst := hk.const_mul (intervalStep a b s : ℂ)
  have hid : (intervalStep a b s : ℂ) - intervalSmoothing k a b s =
      ∫ y, ((intervalStep a b s : ℂ) - (intervalStep a b (s-y) : ℂ)) * k y := by
    calc
      _ = (∫ y, (intervalStep a b s : ℂ) * k y) -
          ∫ y, (intervalStep a b (s-y) : ℂ) * k y := by
        rw [integral_const_mul, hmass, mul_one]
        rfl
      _ = _ := by
        rw [← integral_sub hconst hshift]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => (sub_mul _ _ _).symm)
  have hta : Integrable (fun y => if |s-a| ≤ |y| then ‖k y‖ else 0) := by
    exact hk.norm.indicator (measurableSet_le measurable_const measurable_id.abs)
  have htb : Integrable (fun y => if |s-b| ≤ |y| then ‖k y‖ else 0) := by
    exact hk.norm.indicator (measurableSet_le measurable_const measurable_id.abs)
  rw [hid, ← integral_add hta htb]
  apply (norm_integral_le_integral_norm _).trans
  have hdiff : Integrable (fun y =>
      ((intervalStep a b s : ℂ) - (intervalStep a b (s-y) : ℂ)) * k y) := by
    apply (hconst.sub hshift).congr
    exact Filter.Eventually.of_forall (fun y => (sub_mul _ _ _).symm)
  apply integral_mono hdiff.norm (hta.add htb)
  intro y
  change ‖((intervalStep a b s : ℂ) - (intervalStep a b (s-y) : ℂ)) * k y‖ ≤
    (if |s-a| ≤ |y| then ‖k y‖ else 0) + (if |s-b| ≤ |y| then ‖k y‖ else 0)
  rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_right (intervalStep_jump_le a b s y) (_root_.norm_nonneg (k y))
  simpa only [add_mul, ite_mul, one_mul, zero_mul] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_KernelTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative kernel tails

A finite weighted L¹ moment gives a uniform bound for the two endpoint
tails. Scaling the kernel will make the moment independent of the
truncation height, as required for a sharp cutoff.
-/

noncomputable section
open MeasureTheory

namespace CubicFirstMoment

theorem kernel_tail_le_moment {k : ℝ → ℂ} (hk : Integrable k)
    {T d : ℝ} (hT : 0 ≤ T) (hd : 0 ≤ d)
    (hM : Integrable (fun y => ‖k y‖ * (1 + T * |y|) ^ 2)) :
    (∫ y, if d ≤ |y| then ‖k y‖ else 0) ≤ kernelMoment k T / (1 + T*d)^2 := by
  have hden : 0 < (1 + T*d)^2 := sq_pos_of_pos (by positivity)
  rw [kernelMoment, ← integral_div]
  apply integral_mono
    (hk.norm.indicator (measurableSet_le measurable_const measurable_id.abs))
    (hM.div_const _)
  intro y
  change (if d ≤ |y| then ‖k y‖ else 0) ≤ (‖k y‖ * (1 + T*|y|)^2) / (1 + T*d)^2
  by_cases hy : d ≤ |y|
  · simp only [hy, ite_true, if_true]
    apply (le_div_iff₀ hden).mpr
    have hh : (1 + T*d)^2 ≤ (1 + T*|y|)^2 :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) 2
    exact mul_le_mul_of_nonneg_left hh (_root_.norm_nonneg (k y))
  · simp only [hy, ite_false, if_false]
    positivity

/-- A moment bound proves the error estimate; it is not assumed as an
unproved boundary approximation. -/
theorem intervalSmoothing_error_le_moment {k : ℝ → ℂ} (hk : Integrable k)
    (hmass : ∫ y, k y = 1) {T : ℝ} (hT : 0 ≤ T)
    (hM : Integrable (fun y => ‖k y‖ * (1 + T * |y|) ^ 2)) (a b s : ℝ) :
    ‖(intervalStep a b s : ℂ) - intervalSmoothing k a b s‖ ≤
      kernelMoment k T / (1 + T*|s-a|)^2 +
        kernelMoment k T / (1 + T*|s-b|)^2 :=
  (intervalSmoothing_error_le_tails hk hmass a b s).trans
    (add_le_add (kernel_tail_le_moment hk hT (abs_nonneg _) hM)
      (kernel_tail_le_moment hk hT (abs_nonneg _) hM))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_KernelScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
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

theorem integral_scaledKernel (k : ℝ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ y, scaledKernel k T y) = ∫ y, k y := by
  unfold scaledKernel
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  simp only [abs_of_pos (inv_pos.mpr hT), Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, mul_inv_cancel₀ hT.ne', Complex.ofReal_one, one_mul]

private theorem scaledKernel_moment_integrand (k : ℝ → ℂ) {T : ℝ} (hT : 0 < T) :
    (fun y => ‖scaledKernel k T y‖ * (1 + T*|y|)^2) =
      (fun y => T * (‖k (T*y)‖ * (1 + |T*y|)^2)) := by
  funext y
  simp only [scaledKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hT, abs_mul]
  ring

theorem integrable_scaledKernel_moment {k : ℝ → ℂ}
    (hM : Integrable (fun y => ‖k y‖ * (1 + |y|)^2))
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun y => ‖scaledKernel k T y‖ * (1 + T*|y|)^2) := by
  rw [scaledKernel_moment_integrand k hT]
  exact (hM.comp_mul_left' hT.ne').const_mul T

theorem kernelMoment_scaledKernel (k : ℝ → ℂ) {T : ℝ} (hT : 0 < T) :
    kernelMoment (scaledKernel k T) T = kernelMoment k 1 := by
  rw [kernelMoment, scaledKernel_moment_integrand k hT, integral_const_mul,
    Measure.integral_comp_mul_left (fun y : ℝ => ‖k y‖ * (1 + |y|)^2) T]
  simp only [abs_of_pos (inv_pos.mpr hT), smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hT.ne', one_mul, kernelMoment]

/-- Schwartz decay supplies the integrable moment needed by the cutoff,
without imposing a quantitative tail estimate as a hypothesis. -/
theorem integrable_kernelMoment_schwartz (k : SchwartzMap ℝ ℂ) :
    Integrable (fun y => ‖k y‖ * (1 + |y|)^2) := by
  have h₀ : Integrable (fun y : ℝ => ‖k y‖) :=
    (show Integrable (fun y : ℝ => k y) from k.integrable).norm
  have h₁ := k.integrable_pow_mul volume 1
  have h₂ := k.integrable_pow_mul volume 2
  have h := h₀.add ((h₁.const_mul 2).add h₂)
  apply h.congr
  filter_upwards [] with y
  simp only [Pi.add_apply, Real.norm_eq_abs, pow_one]
  ring

/-- Uniform endpoint estimate for the entire scaled Schwartz family. -/
theorem scaled_schwartz_interval_error (k : SchwartzMap ℝ ℂ)
    (hmass : ∫ y, k y = 1) {T : ℝ} (hT : 0 < T) (a b s : ℝ) :
    ‖(intervalStep a b s : ℂ) - intervalSmoothing (scaledKernel k T) a b s‖ ≤
      kernelMoment k 1 / (1 + T*|s-a|)^2 +
        kernelMoment k 1 / (1 + T*|s-b|)^2 := by
  have h := intervalSmoothing_error_le_moment
    (integrable_scaledKernel k.integrable hT)
    ((integral_scaledKernel k hT).trans hmass) hT.le
    (integrable_scaledKernel_moment (integrable_kernelMoment_schwartz k) hT) a b s
  simpa only [kernelMoment_scaledKernel k hT] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FourierCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
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

theorem frequencyCutoff_zero {x : ℝ} (hx : 1 ≤ |x|) : frequencyCutoff x = 0 := by
  rw [frequencyCutoff_apply, frequencyBump.zero_of_le_dist]
  · rfl
  · simpa only [Real.dist_eq, sub_zero, frequencyBump] using hx

/-- Inversion identifies the Fourier transform with the actual compact cutoff. -/
theorem fourier_truncationKernel : 𝓕 truncationKernel = frequencyCutoff :=
  fourier_fourierInv_eq frequencyCutoff

/-- Normalization follows from the value of the Fourier transform at zero. -/
theorem integral_truncationKernel : (∫ y, truncationKernel y) = 1 := by
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => f 0) fourier_truncationKernel
  rw [SchwartzMap.fourier_coe, Real.fourier_eq'] at h
  simpa only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul, frequencyCutoff_one (by norm_num : |(0 : ℝ)| ≤ 1/2)] using h

/-- The chosen Fourier kernel gives the uniform two-endpoint approximation. -/
theorem fourier_interval_error {T : ℝ} (hT : 0 < T) (a b s : ℝ) :
    ‖(intervalStep a b s : ℂ) - intervalSmoothing (scaledKernel truncationKernel T) a b s‖ ≤
      kernelMoment truncationKernel 1 / (1 + T*|s-a|)^2 +
        kernelMoment truncationKernel 1 / (1 + T*|s-b|)^2 :=
  scaled_schwartz_interval_error truncationKernel integral_truncationKernel hT a b s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogEndpoint
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From logarithmic boundary distance to integer norm distance

This is the missing metric step between Fourier smoothing in log norm and
the summable endpoint kernel in the norm variable.
-/

noncomputable section

namespace CubicFirstMoment

private theorem sub_le_mul_log_sub {v w : ℝ} (hv : 0 < v) (hw : 0 < w) :
    v-w ≤ v * (Real.log v - Real.log w) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hv hw)
  rw [inv_div, Real.log_div hv.ne' hw.ne'] at h
  have h' := mul_le_mul_of_nonneg_left h hv.le
  have he : v * (1 - w/v) = v-w := by field_simp
  rwa [he] at h'

theorem abs_sub_le_four_mul_log_distance {v w : ℝ}
    (hv : 0 < v) (hw : 0 < w) (hv4 : v ≤ 4) (hw4 : w ≤ 4) :
    |v-w| ≤ 4 * |Real.log v - Real.log w| := by
  have hord : ∀ {v w : ℝ}, 0 < v → 0 < w → v ≤ 4 → w ≤ v →
      |v-w| ≤ 4 * |Real.log v - Real.log w| := by
    intro v w hv hw hv4 hwv
    have hl : 0 ≤ Real.log v - Real.log w := sub_nonneg.mpr (Real.log_le_log hw hwv)
    rw [abs_of_nonneg (sub_nonneg.mpr hwv), abs_of_nonneg hl]
    exact (sub_le_mul_log_sub hv hw).trans (mul_le_mul_of_nonneg_right hv4 hl)
  rcases le_total w v with h | h
  · exact hord hv hw hv4 h
  · rw [abs_sub_comm v w, abs_sub_comm (Real.log v) (Real.log w)]
    exact hord hw hv hw4 h

private theorem reciprocal_sq_le_endpoint {h d r : ℝ}
    (hh : 0 < h) (hd : 0 ≤ d) (hr : 0 ≤ r) (hdis : d ≤ 4*h*r) :
    1 / (1+r)^2 ≤ 16 * (h^2 / (h+d)^2) := by
  rw [← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos (by positivity))
    (sq_pos_of_pos (by positivity))]
  have hsum : h+d ≤ 4*h*(1+r) := by nlinarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ h+d) hsum 2
  nlinarith only [hs]

/-- On the fixed norm envelope, the Fourier boundary majorant is at most
an absolute constant times the summable integer endpoint kernel. -/
theorem log_boundary_le_endpoint {X T n b : ℝ}
    (hX : 0 < X) (hT : 0 < T) (hn : 0 < n) (hn4 : n ≤ 4*X)
    (hb : 0 < b) (hb4 : b ≤ 4) :
    1 / (1 + T*|Real.log (n/X) - Real.log b|)^2 ≤
      16 * endpointKernel (X/T) (n - b*X) := by
  have hdist := abs_sub_le_four_mul_log_distance (div_pos hn hX) hb
    ((div_le_iff₀ hX).mpr hn4) hb4
  have hid : |n - b*X| = X * |n/X-b| := by
    calc
      |n - b*X| = |X*(n/X-b)| := by congr 1; field_simp
      _ = |X| * |n/X-b| := abs_mul _ _
      _ = X * |n/X-b| := by rw [abs_of_pos hX]
  have hdis : |n-b*X| ≤ 4*(X/T)*(T*|Real.log (n/X)-Real.log b|) := by
    rw [hid]
    have he : 4*(X/T)*(T*|Real.log (n/X)-Real.log b|) =
        X*(4*|Real.log (n/X)-Real.log b|) := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hdist hX.le
  exact reciprocal_sq_le_endpoint (div_pos hX hT) (abs_nonneg _) (by positivity) hdis

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The sharp-cutoff error at integer norms

The smoothing constructed from the fixed Fourier kernel has a summable
endpoint error.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

theorem intervalStep_log {v : ℝ} (hv : 0 < v) :
    intervalStep 0 (Real.log 2) (Real.log v) = intervalStep 1 2 v := by
  have he : Real.log v ∈ Set.Icc 0 (Real.log 2) ↔ v ∈ Set.Icc 1 2 := by
    rw [Set.mem_Icc, Set.mem_Icc, ← Real.log_one]
    exact and_congr (Real.log_le_log_iff (by norm_num) hv)
      (Real.log_le_log_iff hv (by norm_num))
  simp only [intervalStep, he]

theorem intervalStep_div {X n : ℝ} (hX : 0 < X) :
    intervalStep 1 2 (n/X) = intervalStep X (2*X) n := by
  simp only [intervalStep, Set.mem_Icc, le_div_iff₀ hX, div_le_iff₀ hX, one_mul]

theorem kernelMoment_nonneg (k : ℝ → ℂ) (T : ℝ) : 0 ≤ kernelMoment k T :=
  integral_nonneg (fun _ => mul_nonneg (_root_.norm_nonneg _) (sq_nonneg _))

/-- The concrete error has the two summable endpoint majorants. -/
theorem sharpIntervalError_bound {X T n : ℝ}
    (hX : 0 < X) (hT : 0 < T) (hn : 0 < n) (hn4 : n ≤ 4*X) :
    ‖sharpIntervalError X T n‖ ≤ 16 * kernelMoment truncationKernel 1 *
      (endpointKernel (X/T) (n-X) + endpointKernel (X/T) (n-2*X)) := by
  have h := fourier_interval_error hT 0 (Real.log 2) (Real.log (n/X))
  rw [intervalStep_log (div_pos hn hX), intervalStep_div hX] at h
  have h₁ := log_boundary_le_endpoint hX hT hn hn4
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 4)
  have h₂ := log_boundary_le_endpoint hX hT hn hn4
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 4)
  simp only [Real.log_one, sub_zero, one_mul] at h₁
  simp only [sub_zero] at h
  have hM := kernelMoment_nonneg truncationKernel 1
  calc
    _ ≤ kernelMoment truncationKernel 1 / (1 + T*|Real.log (n/X)|)^2 +
        kernelMoment truncationKernel 1 / (1 + T*|Real.log (n/X)-Real.log 2|)^2 := h
    _ ≤ kernelMoment truncationKernel 1 * (16 * endpointKernel (X/T) (n-X)) +
        kernelMoment truncationKernel 1 * (16 * endpointKernel (X/T) (n-2*X)) := by
      simpa only [← mul_div_assoc, mul_one] using add_le_add
        (mul_le_mul_of_nonneg_left h₁ hM) (mul_le_mul_of_nonneg_left h₂ hM)
    _ = _ := by ring

/-- Collected integer coefficients incur exactly the permitted truncation cost. -/
theorem sharp_interval_sum_error {X T M : ℝ} (hX : 0 < X) (hT : 0 < T)
    (hM : 0 ≤ M) (s : Finset ℤ) (c : ℤ → ℂ)
    (hs : ∀ n ∈ s, 0 < (n : ℝ) ∧ (n : ℝ) ≤ 4*X)
    (hc : ∀ n ∈ s, ‖c n‖ ≤ M) :
    ‖∑ n ∈ s, c n * sharpIntervalError X T n‖ ≤
      64 * kernelMoment truncationKernel 1 * M * (1 + X/T) := by
  have h := weighted_endpoint_error (div_pos hX hT)
    (mul_nonneg (by norm_num) (kernelMoment_nonneg truncationKernel 1)) hM
    s X (2*X) c (fun n => sharpIntervalError X T n) hc
    (fun n hn => sharpIntervalError_bound hX hT (hs n hn).1 (hs n hn).2)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
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

theorem continuous_concrete_intervalSmoothing {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    Continuous (intervalSmoothing (scaledKernel truncationKernel T) a b) := by
  rw [intervalSmoothing_eq_convolution]
  have hbounded : BddAbove (Set.range (fun y => ‖scaledKernel truncationKernel T y‖)) := by
    refine ⟨T * SchwartzMap.seminorm ℝ 0 0 truncationKernel, ?_⟩
    rintro z ⟨y, rfl⟩
    simp only [scaledKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ truncationKernel _) hT.le
  have hcont : Continuous (scaledKernel truncationKernel T) := by
    unfold scaledKernel
    exact continuous_const.mul (truncationKernel.continuous.comp (continuous_const.mul continuous_id))
  exact hbounded.continuous_convolution_left_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) hcont (integrable_intervalStep a b)

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

/-- The inverse integral has support only in the prescribed frequency band,
by `fourier_intervalSmoothing_zero`. -/
theorem concrete_interval_fourier_integral {T : ℝ} (hT : 0 < T) (a b s : ℝ) :
    intervalSmoothing (scaledKernel truncationKernel T) a b s =
      ∫ ξ : ℝ, Complex.exp ((2 * Real.pi * ξ * s : ℝ) * Complex.I) *
        (frequencyCutoff (ξ/T) * 𝓕 (fun x => (intervalStep a b x : ℂ)) ξ) := by
  have h := (integrable_concrete_intervalSmoothing hT a b).fourierInv_fourier_eq (v := s)
    (integrable_fourier_intervalSmoothing hT a b)
    (continuous_concrete_intervalSmoothing hT a b).continuousAt
  rw [Real.fourierInv_eq'] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [fourier_intervalSmoothing hT]
  change Complex.exp ((2 * Real.pi * inner ℝ ξ s : ℝ) * Complex.I) * _ = _
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

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

lemma dyadicHeightMean_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (T : ℝ) :
    dyadicHeightMean (fun t => f t+g t) T = dyadicHeightMean f T+dyadicHeightMean g T := by
  simp only [dyadicHeightMean,intervalIntegral.integral_add
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

lemma dyadicHeightMean_const_mul (c : ℝ) (f : ℝ → ℝ) (T : ℝ) :
    dyadicHeightMean (fun t => c*f t) T = c*dyadicHeightMean f T := by
  simp only [dyadicHeightMean,intervalIntegral.integral_const_mul]
  ring

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

lemma normalized_dyadicWeightIntegral_bound (f h : ℝ → ℂ) (hf : Continuous f)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hh : ∀ t, ‖h t‖ ≤ M)
    (hs : ∀ t, t ∉ dyadicHeightSupport T → h t = 0) :
    ‖(T:ℂ)⁻¹*(∫ t : ℝ, h t*f t)‖ ≤ M*dyadicHeightMean (fun t => ‖f t‖) T := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hT.le]
  have hb := mul_le_mul_of_nonneg_left (dyadicWeightIntegral_bound f h hf hT hM hh hs)
    (inv_nonneg.mpr hT.le)
  apply hb.trans_eq
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeSharpCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sharp Fourier cutoff for actual prime sums

A fixed integer norm contains at most a conjugate pair of primary primes.
Thus collecting prime coefficients by norm supplies the coefficient bound
needed in the endpoint-kernel argument, without a norm-counting hypothesis.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_eq_or_conjugate_of_norm_eq_sharp {p q : Eisenstein}
    (hp : primaryPrime p) (hq : primaryPrime q) (hn : norm p = norm q) :
    p = q ∨ p = conjugate q := by
  have hnat : normNat p = normNat q := by
    exact_mod_cast (show (normNat p : ℝ) = normNat q from by
      rw [normNat_cast,normNat_cast,hn])
  have hd : p ∣ q*conjugate q := by
    rw [← normNat_cast_eq_mul_conjugate, ← hnat, normNat_cast_eq_mul_conjugate]
    exact dvd_mul_right p (conjugate p)
  rcases hp.2.dvd_or_dvd hd with hd | hd
  · exact Or.inl (primary_associated_eq hp.1 hq.1 (hp.2.associated_of_dvd hq.2 hd))
  · exact Or.inr (primary_associated_eq hp.1 (primary_conjugate hq.1)
      (hp.2.associated_of_dvd (primaryPrime_conjugate hq).2 hd))

lemma prime_norm_fiber_card_le_two (P : Finset Eisenstein)
    (hP : ∀ p ∈ P, primaryPrime p) (n : ℤ) :
    (P.filter (fun p => (normNat p : ℤ) = n)).card ≤ 2 := by
  let Q := P.filter (fun p => (normNat p : ℤ) = n)
  by_cases he : Q.Nonempty
  · obtain ⟨q,hq⟩ := he
    have hsub : Q ⊆ {q,conjugate q} := by
      intro p hp
      have hnp : normNat p = normNat q := by
        exact_mod_cast ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
      have hn : norm p = norm q := by rw [← normNat_cast,← normNat_cast,hnp]
      rcases primaryPrime_eq_or_conjugate_of_norm_eq_sharp
        (hP p (Finset.mem_filter.mp hp).1) (hP q (Finset.mem_filter.mp hq).1) hn with h | h
      · simp [h]
      · simp [h]
    calc
      Q.card ≤ ({q,conjugate q} : Finset Eisenstein).card := Finset.card_le_card hsub
      _ ≤ ({conjugate q} : Finset Eisenstein).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  · have hQ : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    change Q.card ≤ 2
    rw [hQ]
    decide

lemma collectedPrimeCoefficient_bound (P : Finset Eisenstein)
    (hP : ∀ p ∈ P, primaryPrime p) (c : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) (n : ℤ) :
    ‖collectedPrimeCoefficient P c n‖ ≤ 2*M := by
  calc
    _ ≤ ∑ p ∈ P.filter (fun p => (normNat p : ℤ) = n), ‖c p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ P.filter (fun p => (normNat p : ℤ) = n), M :=
      Finset.sum_le_sum (fun p hp => hc p (Finset.mem_filter.mp hp).1)
    _ = ((P.filter (fun p => (normNat p : ℤ) = n)).card : ℝ)*M := by simp
    _ ≤ 2*M := mul_le_mul_of_nonneg_right (by
      exact_mod_cast prime_norm_fiber_card_le_two P hP n) hM

/-- An actual prime sum has the claimed endpoint cost after collecting
both conjugates at each integer norm. -/
theorem prime_sharp_interval_sum_error (P : Finset Eisenstein)
    (hP : ∀ p ∈ P, primaryPrime p) (c : Eisenstein → ℂ)
    {X T M : ℝ} (hX : 0 < X) (hT : 0 < T) (hM : 0 ≤ M)
    (hPX : ∀ p ∈ P, norm p ≤ 4*X) (hc : ∀ p ∈ P, ‖c p‖ ≤ M) :
    ‖∑ p ∈ P, c p*sharpIntervalError X T (norm p)‖ ≤
      128*kernelMoment truncationKernel 1*M*(1+X/T) := by
  let S : Finset ℤ := P.image (fun p => (normNat p : ℤ))
  have hf := Finset.sum_fiberwise_of_maps_to (s := P) (t := S)
    (g := fun p => (normNat p : ℤ))
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩)
    (fun p => c p*sharpIntervalError X T (norm p))
  have he : (∑ p ∈ P, c p*sharpIntervalError X T (norm p)) =
      ∑ n ∈ S, collectedPrimeCoefficient P c n*sharpIntervalError X T n := by
    rw [← hf]
    apply Finset.sum_congr rfl
    intro n hn
    rw [collectedPrimeCoefficient,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hn : norm p = (n : ℝ) := by
      rw [← normNat_cast]
      exact_mod_cast (Finset.mem_filter.mp hp).2
    rw [hn]
  have hs : ∀ n ∈ S, 0 < (n : ℝ) ∧ (n : ℝ) ≤ 4*X := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    simp only [Int.cast_natCast,normNat_cast]
    exact ⟨norm_pos_of_ne_zero (hP p hp).2.ne_zero,hPX p hp⟩
  rw [he]
  convert sharp_interval_sum_error hX hT (mul_nonneg (by norm_num) hM) S
    (collectedPrimeCoefficient P c) hs (fun n _ => collectedPrimeCoefficient_bound P hP c hM hc n)
    using 1; ring

/-- The endpoint error for uniformly bounded prime coefficients is
negligible at the Patterson scale for every positive extra height. -/
theorem prime_sharp_interval_error_isLittleO {ρ M : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 5/6)
    (hM : 0 ≤ M) (P : ℝ → Finset Eisenstein) (c : ℝ → Eisenstein → ℂ)
    (hP : ∀ X, 1 ≤ X → ∀ p ∈ P X, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ X, 1 ≤ X → ∀ p ∈ P X, ‖c X p‖ ≤ M) :
    (fun X : ℝ => ∑ p ∈ P X, c X p*
      sharpIntervalError X (X^(1/6+ρ : ℝ)) (norm p)) =o[Filter.atTop] firstMomentScale := by
  apply isLittleO_of_powerSaving hρ
  apply Asymptotics.IsBigO.of_bound (256*kernelMoment truncationKernel 1*M)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have h := prime_sharp_interval_sum_error (P X) (fun p hp => (hP X hX p hp).1)
    (c X) hX0 (Real.rpow_pos_of_pos hX0 (1/6+ρ)) hM (fun p hp => (hP X hX p hp).2)
    (hc X hX)
  have ht := truncationError_le (ε := 0) hX hρ₁
  simp only [Real.rpow_zero,one_mul,sub_zero] at ht
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)]
  have hm := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ 128*kernelMoment truncationKernel 1*M from by
      exact mul_nonneg (mul_nonneg (by norm_num) (kernelMoment_nonneg _ _)) hM)
  exact h.trans (by convert hm using 1; ring)

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

lemma cutoffHeightMultiplier_zero {T t : ℝ} (hT : 0 < T)
    (ht : 2*Real.pi*T ≤ |t|) : cutoffHeightMultiplier T t = 0 := by
  unfold cutoffHeightMultiplier
  rw [frequencyCutoff_zero, zero_mul]
  rw [abs_div, abs_div, abs_of_pos hT, abs_of_pos (by positivity : 0 < 2*Real.pi)]
  apply (le_div_iff₀ hT).mpr
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
  nlinarith

lemma smoothLogInterval_eq_height {T v : ℝ} (hT : 0 < T) :
    smoothLogInterval T v = ((2*Real.pi : ℝ) : ℂ)⁻¹ *
      heightFourierIntegral (cutoffHeightMultiplier T) (Real.log v) := by
  let f : ℝ → ℂ := fun ξ =>
    Complex.exp ((2*Real.pi*ξ*Real.log v : ℝ)*Complex.I) *
      (frequencyCutoff (ξ/T) *
        𝓕 (fun x => (intervalStep 0 (Real.log 2) x : ℂ)) ξ)
  calc
    smoothLogInterval T v = ∫ ξ : ℝ, f ξ :=
      concrete_interval_fourier_integral hT 0 (Real.log 2) (Real.log v)
    _ = ((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, f (t/(2*Real.pi)) := by
      rw [Measure.integral_comp_div, abs_of_pos (by positivity : 0 < 2*Real.pi),
        Complex.real_smul, inv_mul_cancel_left₀ (by exact_mod_cast
          (show 2*Real.pi ≠ 0 by positivity))]
    _ = _ := by
      congr 1
      rw [heightFourierIntegral_eq]
      apply integral_congr_ae
      filter_upwards with t
      have he : 2*Real.pi*(t/(2*Real.pi))*Real.log v = Real.log v*t := by
        field_simp
      dsimp only [f, cutoffHeightMultiplier]
      rw [he, mul_comm]

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

lemma heightWindow_telescope (T t : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, heightWindow (T*(3/2:ℝ)^j) t) =
      ((heightPartitionBump (t/(T*(3/2:ℝ)^n)) - heightPartitionBump (t/T) : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have he : (3/2:ℝ)*(T*(3/2:ℝ)^n) = T*(3/2:ℝ)^(n+1) := by rw [pow_succ]; ring
    simp only [heightWindow, he, Complex.ofReal_sub]
    ring

lemma cutoffHeightMultiplier_partition {S T : ℝ} (hS : 0 < S) (hT : 0 < T)
    (n : ℕ) (hn : 2*Real.pi*S ≤ T*(3/2:ℝ)^n) (t : ℝ) :
    cutoffHeightMultiplier S t =
      cutoffHeightMultiplier S t*(heightPartitionBump (t/T) : ℂ) +
        ∑ j ∈ Finset.range n,
          cutoffHeightMultiplier S t*heightWindow (T*(3/2:ℝ)^j) t := by
  rw [← Finset.mul_sum, heightWindow_telescope]
  by_cases ht : |t| ≤ 2*Real.pi*S
  · have hpos : 0 < T*(3/2:ℝ)^n := by positivity
    have hsmall : |t/(T*(3/2:ℝ)^n)| ≤ 1 := by
      rw [abs_div, abs_of_pos hpos]
      exact (div_le_one hpos).mpr (ht.trans hn)
    rw [heightPartitionBump_one hsmall]
    push_cast
    ring
  · rw [cutoffHeightMultiplier_zero hS (le_of_lt (lt_of_not_ge ht))]
    simp

lemma integrable_cutoffHeightMultiplier_window {S : ℝ} (hS : 0 < S) (T : ℝ) :
    Integrable (fun t => cutoffHeightMultiplier S t*heightWindow T t) :=
  (cutoffHeightMultiplier_integrable hS).mul_bdd
    (heightWindow_smooth T).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (heightWindow_norm_le T))

lemma cutoffHeightMultiplier_integral_partition {S T B : ℝ}
    (hS : 0 < S) (hT : 0 < T) (n : ℕ) (hn : 2*Real.pi*S ≤ T*(3/2:ℝ)^n)
    (f : ℝ → ℂ) (hf : Continuous f) (hB : ∀ t, ‖f t‖ ≤ B) :
    (∫ t : ℝ, cutoffHeightMultiplier S t*f t) =
      (∫ t : ℝ, (cutoffHeightMultiplier S t*(heightPartitionBump (t/T):ℂ))*f t) +
        ∑ j ∈ Finset.range n, ∫ t : ℝ,
          (cutoffHeightMultiplier S t*heightWindow (T*(3/2:ℝ)^j) t)*f t := by
  have hlow : Integrable (fun t =>
      (cutoffHeightMultiplier S t*(heightPartitionBump (t/T):ℂ))*f t) := by
    apply Integrable.mul_bdd _ hf.aestronglyMeasurable (Filter.Eventually.of_forall hB)
    apply (cutoffHeightMultiplier_integrable hS).mul_bdd (c := 1)
    · exact (Complex.continuous_ofReal.comp
        (heightPartitionBump.continuous.comp (continuous_id.div_const T))).aestronglyMeasurable
    · filter_upwards with t
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg heightPartitionBump.nonneg] using
          (heightPartitionBump.le_one (x := t/T))
  have hpiece (j : ℕ) : Integrable (fun t =>
      (cutoffHeightMultiplier S t*heightWindow (T*(3/2:ℝ)^j) t)*f t) :=
    (integrable_cutoffHeightMultiplier_window hS _).mul_bdd hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hB)
  calc
    _ = ∫ t : ℝ, (cutoffHeightMultiplier S t*(heightPartitionBump (t/T):ℂ))*f t +
        ∑ j ∈ Finset.range n,
          (cutoffHeightMultiplier S t*heightWindow (T*(3/2:ℝ)^j) t)*f t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [← Finset.sum_mul, ← add_mul, ← cutoffHeightMultiplier_partition hS hT n hn t]
    _ = _ := by
      rw [integral_add hlow (integrable_finsetSum _ (fun j _ => hpiece j)),
        integral_finsetSum _ (fun j _ => hpiece j)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeMellinTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The prime comparison through a common-height integral

The angular Gauss-minus-model coefficients are uniformly bounded. The
actual sharp dyadic prime sum differs negligibly from the same finite
polynomial integrated against the constructed Mellin cutoff.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma primeComparisonCoefficient_bound (ℓ : ℤ) {p : Eisenstein} (hp : primaryPrime p) :
    ‖primeComparisonCoefficient ℓ p‖ ≤ 1+cStar := by
  have hg : ‖gaussAtPrime p‖ = 1 := by
    rw [← gauss_prime hp]
    exact norm_gauss_of_squarefree hp.1 hp.2.squarefree
  have hw : norm p^(-1/6 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_norm hp.2.ne_zero) (by norm_num)
  have hmodel : ‖((cStar*norm p^(-1/6 : ℝ) : ℝ) : ℂ)‖ ≤ cStar := by
    rw [Complex.norm_real,Real.norm_of_nonneg (mul_nonneg cStar_pos.le (Real.rpow_nonneg (norm_nonneg p) _))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hw cStar_pos.le
  rw [primeComparisonCoefficient,norm_theta_mul hp.2.ne_zero]
  exact (norm_sub_le _ _).trans (by rw [hg]; linarith)

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

lemma heightWindowCount_covers {S T : ℝ} (hS : 0 < S) (hT : 0 < T) :
    2*Real.pi*S ≤ T*(3/2:ℝ)^heightWindowCount S T := by
  have hr : 0 < Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  have hp : 0 < (3/2:ℝ)^heightWindowCount S T := by positivity
  have hlog : Real.log ((2*Real.pi*S)/T) ≤
      Real.log ((3/2:ℝ)^heightWindowCount S T) := by
    rw [Real.log_pow]
    exact (div_le_iff₀ hr).mp (Nat.le_ceil _)
  have hb := (Real.log_le_log_iff (div_pos (by positivity) hT) hp).mp hlog
  simpa only [mul_comm] using (div_le_iff₀ hT).mp hb

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightBilinearScale
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the genuine height-averaged bilinear estimate. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma dyadicHeightMean_norm_le_of_sq_le {f : ℝ → ℂ} (hf : Continuous f)
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R)
    (hsq : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ R^2) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤ 2*R := by
  have hm := dyadicHeightMean_mono
    (f := fun t => (2*R)*‖f t‖) (g := fun t => ‖f t‖^2+R^2)
    (continuous_const.mul hf.norm) ((hf.norm.pow 2).add continuous_const) hT
    (fun t _ => by nlinarith [sq_nonneg (‖f t‖-R)])
  rw [dyadicHeightMean_const_mul,
    dyadicHeightMean_add (f := fun t => ‖f t‖^2) (g := fun _ => R^2)
      (hf.norm.pow 2) continuous_const,
    dyadicHeightMean_const _ hT.ne'] at hm
  nlinarith [sq_pos_of_pos hR]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightSquareRoot
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unsquaring a two-sided height mean, including zero coefficient energy. -/
noncomputable section
namespace CubicFirstMoment

lemma dyadicHeightMean_norm_le_of_sq_le_nonneg {f : ℝ → ℂ} (hf : Continuous f)
    {T R : ℝ} (hT : 0 < T) (hR : 0 ≤ R)
    (hsq : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ R^2) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤ 2*R := by
  by_cases hp : 0 < R
  · exact dyadicHeightMean_norm_le_of_sq_le hf hT hp hsq
  have hz : R = 0 := le_antisymm (le_of_not_gt hp) hR
  subst R
  by_contra hh
  have hm : 0 < dyadicHeightMean (fun t => ‖f t‖) T := by linarith
  have hb := dyadicHeightMean_norm_le_of_sq_le hf hT
    (R := dyadicHeightMean (fun t => ‖f t‖) T/4) (by positivity)
    (hsq.trans (by nlinarith [sq_nonneg (dyadicHeightMean (fun t => ‖f t‖) T/4)]))
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeModelEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The model coefficient energy on a full initial prime segment.
The elementary integral test keeps the small primes in the actual sum. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma sum_neg_third_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(-1/3:ℝ)) ≤ (3/2:ℝ)*(N:ℝ)^(2/3:ℝ) := by
  have he : (∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(-1/3:ℝ)) =
      ∑ i ∈ Finset.range N, ((i+1:ℕ):ℝ)^(-1/3:ℝ) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
  rw [he]
  cases N with
  | zero => simp
  | succ M =>
    have ha : AntitoneOn (fun x : ℝ => x^(-1/3:ℝ)) (Set.Icc 1 (1+(M:ℝ))) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by norm_num)
    have hb := ha.sum_le_integral (x₀ := 1) (a := M)
    have hpos : (0:ℝ) ∉ Set.uIcc 1 (1+(M:ℝ)) := by
      rw [Set.uIcc_of_le (by linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)])]
      intro h
      linarith [h.1]
    rw [integral_rpow (r := (-1/3:ℝ)) (Or.inr ⟨by norm_num, hpos⟩)] at hb
    rw [Finset.sum_range_succ']
    have hs : (∑ i ∈ Finset.range M, ((i+1+1:ℕ):ℝ)^(-1/3:ℝ)) =
        ∑ i ∈ Finset.range M, (1+((i+1:ℕ):ℝ))^(-1/3:ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring_nf
    rw [hs]
    simp only [show (-1/3:ℝ)+1 = 2/3 by norm_num, Real.one_rpow] at hb
    have hc : ((M+1:ℕ):ℝ) = 1+(M:ℝ) := by push_cast; ring
    rw [hc]
    have h2 : (0:ℝ) ≤ (1+(M:ℝ))^(2/3:ℝ) := by positivity
    have h1 : (((0:ℕ)+1:ℕ):ℝ)^(-1/3:ℝ) = 1 := by simp
    rw [h1]
    linarith

lemma prime_initial_segment_neg_third (P : Finset Eisenstein) (N : ℕ)
    (hP : ∀ p ∈ P, primaryPrime p ∧ normNat p ≤ N) :
    (∑ p ∈ P, norm p^(-1/3:ℝ)) ≤ 3*(N:ℝ)^(2/3:ℝ) := by
  have hi : ∀ p ∈ P, normNat p ∈ Finset.Icc 1 N := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (normNat_ne_zero (hP p hp).1.2.ne_zero), (hP p hp).2⟩
  have hf (n : ℕ) : ((P.filter (fun p => normNat p = n)).card:ℝ) ≤ 2 := by
    have hh := prime_norm_fiber_card_le_two P (fun p hp => (hP p hp).1) (n:ℤ)
    have he : (P.filter (fun p => (normNat p:ℤ) = (n:ℤ))) =
        P.filter (fun p => normNat p = n) := by ext; simp
    rw [he] at hh
    exact_mod_cast hh
  calc
    _ = ∑ n ∈ Finset.Icc 1 N,
        ((P.filter (fun p => normNat p = n)).card:ℝ)*(n:ℝ)^(-1/3:ℝ) := by
      rw [← Finset.sum_fiberwise_of_maps_to hi]
      apply Finset.sum_congr rfl
      intro n hn
      have he (p : Eisenstein) (hp : p ∈ P.filter (fun p => normNat p = n)) :
          norm p^(-1/3:ℝ) = (n:ℝ)^(-1/3:ℝ) := by
        rw [← normNat_cast, (Finset.mem_filter.mp hp).2]
      simp_rw [Finset.sum_congr rfl he]
      simp
    _ ≤ ∑ n ∈ Finset.Icc 1 N, 2*(n:ℝ)^(-1/3:ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (hf n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = 2*∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(-1/3:ℝ) := by rw [Finset.mul_sum]
    _ ≤ 3*(N:ℝ)^(2/3:ℝ) := by linarith [sum_neg_third_le N]

lemma prime_model_initial_segment_energy (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X M : ℝ} (hX : 0 < X) (_hM : 0 ≤ M)
    (hP : ∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) :
    (∑ p ∈ P, ‖c p*((norm p^(-1/6:ℝ):ℝ):ℂ)‖^2) ≤
      36*M^2*X^(2/3:ℝ) := by
  let N := ⌊4*X⌋₊
  have hN : (N:ℝ) ≤ 4*X := Nat.floor_le (by positivity)
  have hn : ∀ p ∈ P, primaryPrime p ∧ normNat p ≤ N := by
    intro p hp
    refine ⟨(hP p hp).1,Nat.le_floor ?_⟩
    simpa only [normNat_cast] using (hP p hp).2
  have he (p : Eisenstein) (hp : p ∈ P) :
      ‖c p*((norm p^(-1/6:ℝ):ℝ):ℂ)‖^2 ≤ M^2*norm p^(-1/3:ℝ) := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg p) _)]
    have hpow : (norm p^(-1/6:ℝ))^2 = norm p^(-1/3:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg p)]
      norm_num
    rw [hpow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (_root_.norm_nonneg _) (hc p hp) 2)
      (Real.rpow_nonneg (norm_nonneg p) _)
  have hfour : (4:ℝ)^(2/3:ℝ) ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 4) (by norm_num : (2/3:ℝ) ≤ 1)
  calc
    _ ≤ M^2*∑ p ∈ P, norm p^(-1/3:ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum he
    _ ≤ M^2*(3*(N:ℝ)^(2/3:ℝ)) :=
      mul_le_mul_of_nonneg_left (prime_initial_segment_neg_third P N hn) (sq_nonneg _)
    _ ≤ M^2*(3*(4*X)^(2/3:ℝ)) := by gcongr
    _ ≤ 36*M^2*X^(2/3:ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hX.le]
      have hz : 0 ≤ M^2*X^(2/3:ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hfour
        hz]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeModelHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The undecomposed prime model at large heights. The norm fibre has
size at most two, so Montgomery--Vaughan gives its genuine mean square
without a divisor loss or an assumed model cancellation estimate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem prime_model_height_mean_square {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X T M : ℝ} (hX : 0 < X) (hT : 0 < T) (hM : 0 ≤ M)
    (hP : ∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) (ℓ : ℤ) (u : ℝ) :
    dyadicHeightMean (fun t =>
      ‖dispersionModel P (fun p => c p*theta ℓ p) (t+u)‖^2) T ≤
      144*C*M^2*(1+4*X/T)*X^(2/3:ℝ) := by
  let N := ⌊4*X⌋₊
  let v := fun p => c p*((norm p^(-1/6:ℝ):ℝ):ℂ)
  have hN : (N:ℝ) ≤ 4*X := Nat.floor_le (by positivity)
  have hi : ∀ p ∈ P, normNat p ∈ Finset.Icc 1 N := by
    intro p hp
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (hP p hp).1.2.ne_zero),?_⟩
    apply Nat.le_floor
    simpa only [normNat_cast] using (hP p hp).2
  have hf : ∀ n ∈ Finset.Icc 1 N,
      ((P.filter (fun p => normNat p = n)).card:ℝ) ≤ 2 := by
    intro n hn
    have hh := prime_norm_fiber_card_le_two P (fun p hp => (hP p hp).1) (n:ℤ)
    have hn' : (P.filter (fun p => (normNat p:ℤ) = (n:ℤ))) =
        P.filter (fun p => normNat p = n) := by ext; simp
    rw [hn'] at hh
    exact_mod_cast hh
  have hb := fixedAngular_translated_dyadicMeanSquare hMV hC P v N 2 hi
    (fun p hp => (hP p hp).1.2.ne_zero) hf ℓ u hT
  have he (t : ℝ) :
      (∑ p ∈ P, v p*theta ℓ p*mellinPhase (t+u) (norm p)) =
        dispersionModel P (fun p => c p*theta ℓ p) (t+u) := by
    unfold dispersionModel v
    apply Finset.sum_congr rfl
    intro p hp
    rw [normTwist_eq_mellinPhase]
    ring
  simp_rw [he] at hb
  change dyadicHeightMean _ T ≤ _
  change dyadicHeightMean _ T ≤ _ at hb
  have henergy := prime_model_initial_segment_energy P c hX hM hP hc
  have hfactor : 1+(N:ℝ)/T ≤ 1+4*X/T :=
    add_le_add le_rfl (div_le_div_of_nonneg_right hN hT.le)
  apply hb.trans
  calc
    _ ≤ 2*C*(1+4*X/T)*2*(36*M^2*X^(2/3:ℝ)) := by
      apply mul_le_mul
      · gcongr
      · exact henergy
      · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      · positivity
    _ = _ := by ring

lemma continuous_prime_model_height (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    (ℓ : ℤ) (u : ℝ) :
    Continuous (fun t => dispersionModel P (fun p => c p*theta ℓ p) (t+u)) := by
  unfold dispersionModel
  apply continuous_finsetSum
  intro p hp
  exact (continuous_const.mul ((continuous_normTwist p).comp
    (continuous_id.add continuous_const))).mul continuous_const

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeModelCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The undecomposed prime model in the actual cutoff windows. The
power saving comes from ordinary mean value, with the endpoint phases
and the angular character retained exactly. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_cutoff_window_endpoints (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    (H : ℝ) {T X₀ : ℝ} (hT : 0 < T) (hX₀ : 0 < X₀) :
    (∑ p ∈ P, c p*heightFourierIntegral
      (fun t => cutoffHeightMultiplier H t*heightWindow T t)
        (Real.log (norm p)-Real.log X₀)) =
      (T:ℂ)⁻¹*((∫ t : ℝ,
        (localizedEndpointWeight H T t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
          ∑ p ∈ P, c p*normTwist t p) -
        (∫ t : ℝ,
        (localizedEndpointWeight H T t*Complex.exp ((-Real.log (2*X₀)*t:ℝ)*Complex.I))*
          ∑ p ∈ P, c p*normTwist t p)) := by
  have he (p : Eisenstein) : Real.log (norm p)-Real.log X₀-Real.log 2 =
      Real.log (norm p)-Real.log (2*X₀) := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hX₀.ne']
    ring
  calc
    _ = (T:ℂ)⁻¹*((∑ p ∈ P, c p*heightFourierIntegral (localizedEndpointWeight H T)
          (Real.log (norm p)-Real.log X₀)) -
        ∑ p ∈ P, c p*heightFourierIntegral (localizedEndpointWeight H T)
          (Real.log (norm p)-Real.log (2*X₀))) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [cutoff_window_fourier_endpoints H hT, he]
      ring
    _ = _ := by
      have h₁ := height_norm_polynomial_integral P c id _
        (localizedEndpointWeight_integrable H hT) (Real.log X₀)
      have h₂ := height_norm_polynomial_integral P c id _
        (localizedEndpointWeight_integrable H hT) (Real.log (2*X₀))
      simp only [id_eq] at h₁ h₂
      rw [h₁,h₂]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeHeightDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact low-height and dyadic-window decomposition of the sharp prime
comparison. The large-height model is controlled before any factorization
of the Gauss sum is used. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma heightFourierIntegral_partition {H T : ℝ} (hH : 0 < H) (hT : 0 < T)
    (x : ℝ) :
    heightFourierIntegral (cutoffHeightMultiplier H) x =
      heightFourierIntegral
        (fun t => cutoffHeightMultiplier H t*(heightPartitionBump (t/T):ℂ)) x +
      ∑ j ∈ Finset.range (heightWindowCount H T), heightFourierIntegral
        (fun t => cutoffHeightMultiplier H t*heightWindow (T*(3/2:ℝ)^j) t) x := by
  simp only [heightFourierIntegral_eq]
  apply cutoffHeightMultiplier_integral_partition (B := 1) hH hT _
    (heightWindowCount_covers hH hT)
  · fun_prop
  · intro t
    simp only [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
      sub_self,Real.exp_zero]
    exact le_rfl

lemma finite_height_partition (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {H T : ℝ} (hH : 0 < H) (hT : 0 < T) (X₀ : ℝ) :
    (∑ p ∈ P, c p*heightFourierIntegral (cutoffHeightMultiplier H)
      (Real.log (norm p)-Real.log X₀)) =
      finiteHeightLow P c H T X₀ + finiteHeightTail P c H T X₀ := by
  simp_rw [heightFourierIntegral_partition hH hT]
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib,
    finiteHeightLow,finiteHeightTail]
  rw [Finset.sum_comm]

lemma finite_smooth_low_tail (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {H T X : ℝ} (hH : 0 < H) (hT : 0 < T) (hX : 0 < X)
    (hP : ∀ p ∈ P, p ≠ 0) :
    (∑ p ∈ P, c p*smoothLogInterval H (norm p/X)) =
      ((2*Real.pi:ℝ):ℂ)⁻¹*(finiteHeightLow P c H T X + finiteHeightTail P c H T X) := by
  rw [← finite_height_partition P c hH hT X,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [smoothLogInterval_eq_height hH,
    Real.log_div (norm_pos_of_ne_zero (hP p hp)).ne' hX.ne']
  ring

lemma finiteHeightTail_linear (P : Finset Eisenstein) (c d : Eisenstein → ℂ)
    (z : ℂ) (H T X : ℝ) :
    finiteHeightTail P (fun p => c p-z*d p) H T X =
      finiteHeightTail P c H T X-z*finiteHeightTail P d H T X := by
  simp only [finiteHeightTail,sub_mul,Finset.sum_sub_distrib,
    Finset.mul_sum,mul_assoc]

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem prime_model_height_log_saving {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X T L M : ℝ} (hX : 1 ≤ X) (hL : 0 < L) (hTX : T ≤ X)
    (hTL : L^8 ≤ T) (hM : 0 ≤ M)
    (hP : ∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) (ℓ : ℤ) (u : ℝ) :
    dyadicHeightMean (fun t =>
      ‖dispersionModel P (fun p => c p*theta ℓ p) (t+u)‖) T ≤
      2*Real.sqrt (720*C)*M*X^(5/6:ℝ)/L^4 := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hT : 0 < T := (pow_pos hL 8).trans_le hTL
  have hf : 1+4*X/T ≤ 5*(X/L^8) := by
    have hratio : 1 ≤ X/T := (le_div_iff₀ hT).mpr (by simpa using hTX)
    have ht : X/T ≤ X/L^8 := div_le_div_of_nonneg_left hXp.le (pow_pos hL 8) hTL
    calc
      1+4*X/T = 1+4*(X/T) := by ring
      _ ≤ 5*(X/T) := by linarith
      _ ≤ 5*(X/L^8) := by linarith
  have he : 144*C*M^2*(1+4*X/T)*X^(2/3:ℝ) ≤
      (Real.sqrt (720*C)*M*X^(5/6:ℝ)/L^4)^2 := by
    have hx : X*X^(2/3:ℝ) = X^(5/3:ℝ) := by
      nth_rw 1 [← Real.rpow_one X]
      rw [← Real.rpow_add hXp]
      norm_num
    have hx2 : (X^(5/6:ℝ))^2 = X^(5/3:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le]
      norm_num
    calc
      _ ≤ 144*C*M^2*(5*(X/L^8))*X^(2/3:ℝ) := by gcongr
      _ = (720*C)*M^2*X^(5/3:ℝ)/L^8 := by
        rw [← hx]
        ring
      _ = _ := by
        rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity),hx2,←pow_mul]
  have hb := dyadicHeightMean_norm_le_of_sq_le_nonneg
    (continuous_prime_model_height P c ℓ u) hT (by positivity)
    ((prime_model_height_mean_square hMV hC P c hXp hT hM hP hc ℓ u).trans he)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem prime_model_cutoff_log_saving {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X T L M X₀ : ℝ} (H : ℝ) (hX : 1 ≤ X) (hL : 0 < L) (hX₀ : 0 < X₀)
    (hTX : T ≤ X) (hTL : L^8 ≤ T) (hM : 0 ≤ M)
    (hP : ∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) (ℓ : ℤ) :
    ‖∑ p ∈ P, (c p*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))*
      heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow T t)
        (Real.log (norm p)-Real.log X₀)‖ ≤
      4*Real.sqrt (720*C)*M*X^(5/6:ℝ)/L^4 := by
  have hT : 0 < T := (pow_pos hL 8).trans_le hTL
  let f := fun t => dispersionModel P (fun p => c p*theta ℓ p) t
  have hf : Continuous f := by
    simpa only [add_zero] using continuous_prime_model_height P c ℓ 0
  have hmean : dyadicHeightMean (fun t => ‖f t‖) T ≤
      2*Real.sqrt (720*C)*M*X^(5/6:ℝ)/L^4 := by
    simpa only [add_zero] using prime_model_height_log_saving hMV hC P c
      hX hL hTX hTL hM hP hc ℓ 0
  have hpiece (Y : ℝ) :
      ‖(T:ℂ)⁻¹*(∫ t : ℝ,
        (localizedEndpointWeight H T t*Complex.exp ((-Real.log Y*t:ℝ)*Complex.I))*f t)‖ ≤
      2*Real.sqrt (720*C)*M*X^(5/6:ℝ)/L^4 := by
    apply (normalized_dyadicWeightIntegral_bound f _ hf hT (by norm_num : (0:ℝ) ≤ 1) ?_ ?_).trans
      (by simpa only [one_mul] using hmean)
    · intro t
      rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
      exact localizedEndpointWeight_norm_le H hT t
    · intro t ht
      rw [localizedEndpointWeight_zero H hT t ht,zero_mul]
  rw [finite_cutoff_window_endpoints P _ H hT hX₀]
  have he (t : ℝ) :
      (∑ p ∈ P, (c p*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))*normTwist t p) = f t := by
    unfold f dispersionModel
    apply Finset.sum_congr rfl
    intro p hp
    ring
  simp_rw [he]
  rw [mul_sub]
  exact (norm_sub_le _ _).trans ((add_le_add (hpiece X₀) (hpiece (2*X₀))).trans_eq (by ring))

theorem prime_model_log_window_sum_bound {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Finset Eisenstein) (c : Eisenstein → ℂ)
      (ℓ : ℤ) (X X₀ T H M : ℝ), 1 ≤ X → 0 < X₀ → 1 ≤ H →
      2*Real.pi*H ≤ X → (1+Real.log X)^8 ≤ T → 0 ≤ M →
      (∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X) → (∀ p ∈ P, ‖c p‖ ≤ M) →
      ‖primeModelWindowSum P c ℓ H T X₀‖ ≤
        K*M*X^(5/6:ℝ)/(1+Real.log X)^3 := by
  obtain ⟨K,hK,hsum⟩ := height_window_sum_bound
  refine ⟨4*K*(Real.sqrt (720*C)+1),by positivity,?_⟩
  intro P c ℓ X X₀ T H M hX hX₀ hH hcap hT hM hP hc
  have hL1 : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hL : 0 < 1+Real.log X := zero_lt_one.trans_le hL1
  have hT1 : 1 ≤ T := (one_le_pow₀ hL1).trans hT
  have hHX : H ≤ X := (le_mul_of_one_le_left (zero_le_one.trans hH)
    (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ 2*Real.pi)).trans hcap
  have hf (t : ℝ) (ht : T ≤ t) (htH : t < 2*Real.pi*H) :
      ‖∑ p ∈ P, (c p*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))*
        heightFourierIntegral (fun s => cutoffHeightMultiplier H s*heightWindow t s)
          (Real.log (norm p)-Real.log X₀)‖ ≤
      4*Real.sqrt (720*C)*M*X^(5/6:ℝ)/(1+Real.log X)^4 :=
    prime_model_cutoff_log_saving hMV hC P c H hX hL hX₀
      (htH.le.trans hcap) (hT.trans ht) hM hP hc ℓ
  have hb := hsum H T _ _ hH hT1 (by positivity) hf
  change ‖primeModelWindowSum P c ℓ H T X₀‖ ≤ _ at hb
  apply hb.trans
  calc
    _ ≤ K*(1+Real.log X)*(4*Real.sqrt (720*C)*M*X^(5/6:ℝ)/(1+Real.log X)^4) := by
      gcongr
    _ = 4*K*Real.sqrt (720*C)*(M*X^(5/6:ℝ)/(1+Real.log X)^3) := by
      field_simp
    _ ≤ (4*K*(Real.sqrt (720*C)+1))*M*X^(5/6:ℝ)/(1+Real.log X)^3 := by
      have hz : 0 ≤ M*X^(5/6:ℝ)/(1+Real.log X)^3 := by positivity
      have hs : 4*K*Real.sqrt (720*C) ≤ 4*K*(Real.sqrt (720*C)+1) := by nlinarith
      convert mul_le_mul_of_nonneg_right hs hz using 1
      all_goals try with_reducible_and_instances rfl
      ring

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma primeProductEnvelope_norm_le (x : ℝ) : ‖primeProductEnvelope x‖ ≤ 1 := by
  rw [primeProductEnvelope,Complex.norm_real,Real.norm_of_nonneg primeProductBump.nonneg]
  exact primeProductBump.le_one

lemma primeProductEnvelope_one {x : ℝ} (hx : x ∈ Icc 1 2) :
    primeProductEnvelope x = 1 := by
  have h : primeProductBump x = 1 := by
    apply primeProductBump.one_of_mem_closedBall
    change |x-3/2| ≤ 1/2
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  simp only [primeProductEnvelope,h,Complex.ofReal_one]

lemma primeProductEnvelope_sharp {X n : ℝ} (hX : 0 < X) :
    primeProductEnvelope (n/X)*(intervalStep X (2*X) n : ℝ) =
      (intervalStep X (2*X) n : ℝ) := by
  by_cases hn : n ∈ Icc X (2*X)
  · have he : primeProductEnvelope (n/X) = 1 := primeProductEnvelope_one
      ⟨(le_div_iff₀ hX).mpr (by simpa using hn.1),
        (div_le_iff₀ hX).mpr hn.2⟩
    simp only [he,one_mul]
  · simp only [intervalStep,ite_eq_right hn,Complex.ofReal_zero,mul_zero]

lemma sharpDyadicPrimeComparison_envelope (ℓ : ℤ) {X : ℝ} (hX : 0 < X) :
    sharpDyadicPrimeComparison ℓ X =
      ∑ p ∈ primeCutoff (4*X),
        (primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p)*
          (intervalStep X (2*X) (norm p) : ℝ) := by
  unfold sharpDyadicPrimeComparison
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_comm (primeProductEnvelope _) _,mul_assoc,primeProductEnvelope_sharp hX]

lemma primeProductComparison_bound (ℓ : ℤ) {p : Eisenstein} (hp : primaryPrime p)
    (X : ℝ) :
    ‖primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p‖ ≤ 1+cStar := by
  rw [norm_mul]
  exact (mul_le_mul (primeProductEnvelope_norm_le _) (primeComparisonCoefficient_bound ℓ hp)
    (_root_.norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CenteredPrimeKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the decomposition kernel with the paper's prime
comparison, including the actual common-height Mellin polynomial. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma centeredGauss_primaryPrime {p : Eisenstein} (hp : primaryPrime p) :
    centeredGauss p = gaussAtPrime p-((cStar*norm p^(-1/6:ℝ):ℝ):ℂ) := by
  rw [centeredGauss,gauss_prime hp,idealMoebius_primaryPrime hp]
  push_cast
  ring

lemma theta_centeredGauss_primaryPrime (ℓ : ℤ) {p : Eisenstein} (hp : primaryPrime p) :
    theta ℓ p*centeredGauss p = primeComparisonCoefficient ℓ p := by
  rw [centeredGauss_primaryPrime hp]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicReconstruction
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact telescoping on contracting dyads. Functions that vanish below
one have a finite, hence unambiguous, dyadic reconstruction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma dyadicDifference_sum (F : ℝ → ℂ) (X : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, dyadicDifference F (X/(2:ℝ)^j)) =
      F X-F (X/(2:ℝ)^N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    unfold dyadicDifference
    have he : X/(2:ℝ)^N/2 = X/(2:ℝ)^(N+1) := by rw [pow_succ,div_div]
    rw [he]
    ring

lemma dyadicDifference_reconstruct (F : ℝ → ℂ)
    (hF : ∀ X : ℝ, X < 1 → F X = 0) (X : ℝ) :
    (∑' j : ℕ, dyadicDifference F (X/(2:ℝ)^j)) = F X := by
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt X (by norm_num : (1:ℝ) < 2)
  have hsmall : X/(2:ℝ)^N < 1 := (div_lt_one (by positivity)).mpr hN
  calc
    _ = ∑ j ∈ Finset.range N, dyadicDifference F (X/(2:ℝ)^j) := by
      apply tsum_eq_sum
      intro j hj
      have hNj : N ≤ j := by simpa only [Finset.mem_range,not_lt] using hj
      have hpow : (2:ℝ)^N ≤ 2^j := pow_le_pow_right₀ (by norm_num) hNj
      have hx : X/(2:ℝ)^j < 1 := (div_lt_one (by positivity)).mpr (hN.trans_le hpow)
      have hx2 : X/(2:ℝ)^j/2 < 1 := by linarith
      simp only [dyadicDifference,hF _ hx,hF _ hx2,sub_self]
    _ = F X := by rw [dyadicDifference_sum,hF _ hsmall,sub_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelPartialSummation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma tendsto_firstMomentScale : Tendsto firstMomentScale atTop atTop := by
  have h : Tendsto (fun X : ℝ => Real.log X / X ^ (5 / 6 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 6)).tendsto_div_nhds_zero
  have hpos : ∀ᶠ X : ℝ in atTop, 0 < Real.log X / X ^ (5 / 6 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact div_pos (Real.log_pos hX) (Real.rpow_pos_of_pos (lt_trans zero_lt_one hX) _)
  have hright : Tendsto (fun X : ℝ => Real.log X / X ^ (5 / 6 : ℝ))
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨h, hpos⟩
  have hi := hright.inv_tendsto_nhdsGT_zero
  change Tendsto (fun X : ℝ => (Real.log X / X ^ (5 / 6 : ℝ))⁻¹) atTop atTop at hi
  change Tendsto (fun X : ℝ => firstMomentScale X) atTop atTop
  simpa only [inv_div, firstMomentScale] using hi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact sharp comparison through a smooth total-product weight.
The model tail and the endpoint error remain negligible uniformly in this
fixed weight, so the remaining integrals are precisely the detector kernels. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma primeProductLowHeight_eq (ℓ : ℤ) (H T X : ℝ) :
    primeProductLowHeight ℓ H T X = finiteHeightLow (primeCutoff (4*X))
      (fun p => primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p) H T X := by
  unfold primeProductLowHeight finiteHeightLow
  apply Finset.sum_congr rfl
  intro p hp
  change (theta ℓ p*centeredGauss p)*primeProductEnvelope (norm p/X)*
      heightFourierIntegral (lowHeightWeight H T) (Real.log (norm p)-Real.log X) =
    (primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p)*
      heightFourierIntegral (lowHeightWeight H T) (Real.log (norm p)-Real.log X)
  rw [theta_centeredGauss_primaryPrime ℓ (mem_primeCutoff.mp hp).1]
  ring

lemma sharp_prime_product_low_tail (ℓ : ℤ) {H T X : ℝ}
    (hH : 0 < H) (hT : 0 < T) (hX : 0 < X) :
    sharpDyadicPrimeComparison ℓ X =
      ((2*Real.pi:ℝ):ℂ)⁻¹*(primeProductLowHeight ℓ H T X +
        primeProductGaussTail ℓ H T X - (cStar:ℂ)*
          primeModelWindowSum (primeCutoff (4*X))
            (fun p => primeProductEnvelope (norm p/X)) ℓ H T X) +
      ∑ p ∈ primeCutoff (4*X),
        (primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p)*
          sharpIntervalError X H (norm p) := by
  have hs : sharpDyadicPrimeComparison ℓ X =
      (∑ p ∈ primeCutoff (4*X),
        (primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p)*smoothLogInterval H (norm p/X)) +
      ∑ p ∈ primeCutoff (4*X),
        (primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p)*sharpIntervalError X H (norm p) := by
    rw [sharpDyadicPrimeComparison_envelope ℓ hX,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    unfold sharpIntervalError
    ring
  have hc : (fun p => primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p) =
      (fun p => primeProductEnvelope (norm p/X)*theta ℓ p*gaussAtPrime p -
        (cStar:ℂ)*(primeProductEnvelope (norm p/X)*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))) := by
    funext p
    unfold primeComparisonCoefficient
    push_cast
    ring
  rw [hs,finite_smooth_low_tail _ _ hH hT hX
    (fun p hp => (mem_primeCutoff.mp hp).1.2.ne_zero),←primeProductLowHeight_eq,hc,
    finiteHeightTail_linear]
  simp only [primeProductGaussTail,primeModelWindowSum,finiteHeightTail]
  ring

theorem prime_product_model_log_tail_isLittleO {C a : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (ha : 0 < a) (ha1 : a < 1)
    (T : ℝ → ℝ) (hT : ∀ᶠ X : ℝ in atTop, (1+Real.log X)^8 ≤ T X) (ℓ : ℤ) :
    (fun X : ℝ => primeModelWindowSum (primeCutoff (4*X))
      (fun p => primeProductEnvelope (norm p/X)) ℓ (X^a) (T X) X)
        =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := prime_model_log_window_sum_bound hMV hC
  apply Asymptotics.IsBigO.trans_isLittleO (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3)
    ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [hT,eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0 < 1-a by linarith)).eventually_ge_atTop (2*Real.pi)] with X hT hX hgrow
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hcap : 2*Real.pi*X^a ≤ X := by
    apply (mul_le_mul_of_nonneg_right hgrow (Real.rpow_nonneg hXp.le a)).trans_eq
    rw [←Real.rpow_add hXp]
    have he : 1-a+a = (1:ℝ) := by ring
    rw [he,Real.rpow_one]
  have hb := hbound (primeCutoff (4*X)) (fun p => primeProductEnvelope (norm p/X))
    ℓ X X (T X) (X^a) 1 hX hXp (Real.one_le_rpow hX ha.le) hcap hT (by norm_num)
    (fun p hp => mem_primeCutoff.mp hp) (fun p _ => primeProductEnvelope_norm_le _)
  have hL : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  rw [Real.norm_of_nonneg (by positivity)]
  simpa only [mul_one,mul_div_assoc] using hb

theorem sharp_prime_product_log_height_remainder {C ρ : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hρ : 0 < ρ) (hρ1 : ρ < 5/6) (T : ℝ → ℝ)
    (hT : ∀ᶠ X : ℝ in atTop, (1+Real.log X)^8 ≤ T X) (ℓ : ℤ) :
    (fun X : ℝ => sharpDyadicPrimeComparison ℓ X -
      ((2*Real.pi:ℝ):ℂ)⁻¹*(primeProductLowHeight ℓ (X^(1/6+ρ:ℝ)) (T X) X +
        primeProductGaussTail ℓ (X^(1/6+ρ:ℝ)) (T X) X))
      =o[atTop] firstMomentScale := by
  have hm := prime_product_model_log_tail_isLittleO hMV hC
    (show 0 < (1/6:ℝ)+ρ by linarith) (show (1/6:ℝ)+ρ < 1 by linarith) T hT ℓ
  have he := prime_sharp_interval_error_isLittleO hρ hρ1.le
    (show 0 ≤ 1+cStar by linarith [cStar_pos])
    (fun X => primeCutoff (4*X))
    (fun X p => primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p)
    (fun X _ p hp => mem_primeCutoff.mp hp)
    (fun X _ p hp => primeProductComparison_bound ℓ (mem_primeCutoff.mp hp).1 X)
  apply (he.sub (hm.const_mul_left (((2*Real.pi:ℝ):ℂ)⁻¹*(cStar:ℂ)))).congr'
    _ Filter.EventuallyEq.rfl
  filter_upwards [hT,eventually_gt_atTop (1:ℝ)] with X hT hX
  have hTp : 0 < T X := (pow_pos (by linarith [Real.log_pos hX]) 8).trans_le hT
  rw [sharp_prime_product_low_tail ℓ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _) hTp (zero_lt_one.trans hX)]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicScaleBounds
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A summable majorant for first-moment scales along contracting dyads. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

lemma regularizedMomentScale_pos {X : ℝ} (hX : 1 ≤ X) :
    0 < regularizedMomentScale X := by
  unfold regularizedMomentScale
  exact div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hX) _)
    (by linarith [Real.log_nonneg hX])

lemma regularized_dyadic_scale {X : ℝ} (hX : 1 < X) (j : ℕ)
    (hY : 1 ≤ X/(2:ℝ)^j) :
    regularizedMomentScale (X/(2:ℝ)^j)/firstMomentScale X ≤ dyadicMomentRatio j := by
  have hXp : 0 < X := zero_lt_one.trans hX
  have hYp : 0 < X/(2:ℝ)^j := div_pos hXp (by positivity)
  have hYL : 0 ≤ Real.log (X/(2:ℝ)^j) := Real.log_nonneg hY
  have hL : 0 < 1+Real.log (X/(2:ℝ)^j) := by linarith
  have hpow : (X/(2:ℝ)^j)^(5/6:ℝ) = X^(5/6:ℝ)*((2:ℝ)^(-(5/6:ℝ)))^j := by
    rw [Real.div_rpow hXp.le (by positivity),←Real.rpow_pow_comm (by norm_num),
      Real.rpow_neg (by norm_num),inv_pow,div_eq_mul_inv]
  have hlog : Real.log X = Real.log (X/(2:ℝ)^j)+(j:ℝ)*Real.log 2 := by
    rw [Real.log_div hXp.ne' (by positivity),Real.log_pow]
    ring
  have hratio : Real.log X/(1+Real.log (X/(2:ℝ)^j)) ≤ 1+(j:ℝ)*Real.log 2 := by
    apply (div_le_iff₀ hL).mpr
    rw [hlog]
    nlinarith [mul_nonneg hYL (mul_nonneg (Nat.cast_nonneg j)
      (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)))]
  calc
    _ = ((2:ℝ)^(-(5/6:ℝ)))^j *
        (Real.log X/(1+Real.log (X/(2:ℝ)^j))) := by
      unfold regularizedMomentScale firstMomentScale
      rw [hpow]
      field_simp
    _ ≤ ((2:ℝ)^(-(5/6:ℝ)))^j * (1+(j:ℝ)*Real.log 2) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by unfold dyadicMomentRatio; ring

lemma dyadicMomentRatio_summable : Summable dyadicMomentRatio := by
  let r := (2:ℝ)^(-(5/6:ℝ))
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hgn : Summable (fun j : ℕ => (j:ℝ)*r^j) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1
      (by simpa only [Real.norm_of_nonneg hr.le] using hr1)
  have hg : Summable (fun j : ℕ => r^j) := summable_geometric_of_lt_one hr.le hr1
  convert hg.add (hgn.mul_left (Real.log 2)) using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  unfold dyadicMomentRatio
  dsimp [r]
  ring

lemma firstMomentScale_le_two_regularized {X : ℝ} (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    firstMomentScale X ≤ 2*regularizedMomentScale X := by
  have hL : 0 < Real.log X := zero_lt_one.trans_le hX
  have hL1 : 0 < 1+Real.log X := by linarith
  unfold firstMomentScale regularizedMomentScale
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ hL hL1).mpr
  nlinarith [Real.rpow_nonneg hXp.le (5/6:ℝ)]

lemma firstMomentScale_dyadic_isBigO (j : ℕ) :
    (fun X : ℝ => firstMomentScale (X/(2:ℝ)^j)) =O[atTop] firstMomentScale := by
  have ht : Tendsto (fun X : ℝ => X/(2:ℝ)^j) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  apply IsBigO.of_bound (2*dyadicMomentRatio j)
  filter_upwards [ht.eventually_ge_atTop (Real.exp 1),eventually_gt_atTop (1:ℝ)] with X hY hX
  have hY1 : 1 < X/(2:ℝ)^j := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)).trans_le hY
  have hYL : 1 ≤ Real.log (X/(2:ℝ)^j) := by
    have hh := Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
      (zero_lt_one.trans hY1) hY
    simpa only [Real.log_exp] using hh
  rw [Real.norm_of_nonneg (firstMomentScale_pos hY1).le,
    Real.norm_of_nonneg (firstMomentScale_pos hX).le]
  have hr := (div_le_iff₀ (firstMomentScale_pos hX)).mp
    (regularized_dyadic_scale hX j hY1.le)
  exact (firstMomentScale_le_two_regularized (zero_lt_one.trans hY1) hYL).trans (by linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicLittleO
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing a dyadic little-oh estimate at the Patterson scale. The
local growth and the vanishing at small arguments are retained explicitly. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators Topology
namespace CubicFirstMoment

lemma dyadicDifference_regularized_bound (F : ℝ → ℂ) {M : ℝ}
    (hM : 0 ≤ M)
    (hlocal : ∀ X : ℝ, 1 ≤ X → ‖dyadicDifference F X‖ ≤ M*X)
    (hsmall : dyadicDifference F =o[atTop] firstMomentScale) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      ‖dyadicDifference F X‖ ≤ K*regularizedMomentScale X := by
  obtain ⟨B₀,hB₀⟩ := eventually_atTop.mp (hsmall.def (by norm_num : (0:ℝ) < 1))
  let B := max B₀ (Real.exp 1)
  have hBexp : Real.exp 1 ≤ B := le_max_right _ _
  have hB : 1 < B := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)).trans_le hBexp
  have hlogB : 0 < Real.log B := Real.log_pos hB
  let K := 2+M*B*(1+Real.log B)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro X hX
  have hXL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  by_cases hBX : B ≤ X
  · have hLX : 1 ≤ Real.log X := by
      have hh := Real.strictMonoOn_log.monotoneOn
        (Real.exp_pos 1) (zero_lt_one.trans_le hX) (hBexp.trans hBX)
      simpa only [Real.log_exp] using hh
    have hscale := firstMomentScale_le_two_regularized (zero_lt_one.trans_le hX) hLX
    have hb := hB₀ X ((le_max_left _ _).trans hBX)
    have hXp : 1 < X := hB.trans_le hBX
    rw [one_mul,Real.norm_of_nonneg (firstMomentScale_pos hXp).le] at hb
    apply (hb.trans hscale).trans
    apply mul_le_mul_of_nonneg_right _ (regularizedMomentScale_pos hX).le
    have hn : 0 ≤ M*B*(1+Real.log B) := by positivity
    dsimp [K]
    linarith
  · have hXB : X ≤ B := (lt_of_not_ge hBX).le
    rw [regularizedMomentScale,←mul_div_assoc]
    apply (le_div_iff₀ hXL).mpr
    calc
      _ ≤ (M*X)*(1+Real.log X) := mul_le_mul_of_nonneg_right (hlocal X hX) hXL.le
      _ ≤ (M*B)*(1+Real.log B) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hXB hM)
          (by linarith [Real.strictMonoOn_log.monotoneOn (zero_lt_one.trans_le hX) (zero_lt_one.trans hB) hXB])
          hXL.le (by positivity)
      _ ≤ K := by dsimp [K]; linarith
      _ ≤ K*X^(5/6:ℝ) := le_mul_of_one_le_right hK.le
        (Real.one_le_rpow hX (by norm_num))

theorem dyadic_littleO_firstMoment (F : ℝ → ℂ)
    (hF : ∀ X : ℝ, X < 1 → F X = 0) {M : ℝ} (hM : 0 ≤ M)
    (hlocal : ∀ X : ℝ, 1 ≤ X → ‖dyadicDifference F X‖ ≤ M*X)
    (hsmall : dyadicDifference F =o[atTop] firstMomentScale) :
    F =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hglobal⟩ := dyadicDifference_regularized_bound F hM hlocal hsmall
  let f (X : ℝ) (j : ℕ) : ℂ :=
    dyadicDifference F (X/(2:ℝ)^j)/(firstMomentScale X:ℂ)
  have hpoint (j : ℕ) : Tendsto (fun X => f X j) atTop (𝓝 0) := by
    have ht : Tendsto (fun X : ℝ => X/(2:ℝ)^j) atTop atTop :=
      tendsto_id.atTop_div_const (by positivity)
    have hg := firstMomentScale_dyadic_isBigO j
    have hc := (hsmall.comp_tendsto ht).trans_isBigO hg
    have hz := hc.tendsto_inv_smul_nhds_zero
    simpa only [f,Function.comp_apply,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm] using hz
  have hbound : ∀ᶠ X : ℝ in atTop, ∀ j : ℕ, ‖f X j‖ ≤ K*dyadicMomentRatio j := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    intro j
    have hXp : 0 < X := zero_lt_one.trans hX
    have hYp : 0 < X/(2:ℝ)^j := div_pos hXp (by positivity)
    by_cases hY : 1 ≤ X/(2:ℝ)^j
    · dsimp only [f]
      rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (firstMomentScale_pos hX).le]
      calc
        _ ≤ (K*regularizedMomentScale (X/(2:ℝ)^j))/firstMomentScale X :=
          div_le_div_of_nonneg_right (hglobal _ hY) (firstMomentScale_pos hX).le
        _ = K*(regularizedMomentScale (X/(2:ℝ)^j)/firstMomentScale X) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (regularized_dyadic_scale hX j hY) hK.le
    · have hY' : X/(2:ℝ)^j < 1 := lt_of_not_ge hY
      have hz : dyadicDifference F (X/(2:ℝ)^j) = 0 := by
        rw [dyadicDifference,hF _ hY',hF _ (by linarith),sub_self]
      dsimp only [f]
      rw [hz,zero_div,norm_zero]
      unfold dyadicMomentRatio
      positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  have ht := tendsto_tsum_of_dominated_convergence (dyadicMomentRatio_summable.mul_left K)
    hpoint hbound
  simp only [tsum_zero] at ht
  have hf : (fun X : ℝ => ∑' j : ℕ, f X j) =
      fun X => F X/(firstMomentScale X:ℂ) := by
    funext X
    rw [show (∑' j : ℕ, f X j) = (∑' j : ℕ, dyadicDifference F (X/(2:ℝ)^j))/
      (firstMomentScale X:ℂ) by exact tsum_div_const,
      dyadicDifference_reconstruct F hF X]
  rw [hf] at ht
  have hc : F =o[atTop] (fun X => (firstMomentScale X:ℂ)) := by
    apply (isLittleO_iff_tendsto' ?_).mpr ht
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    exact fun hz => False.elim ((Complex.ofReal_ne_zero.mpr (firstMomentScale_pos hX).ne') hz)
  apply IsLittleO.of_norm_right
  simpa only [Complex.norm_real] using hc.norm_right

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MeanValueLogSpacing
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic frequency separation for the Dirichlet mean value bound. -/
noncomputable section
namespace CubicFirstMoment

lemma log_frequency_spacing {R x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxR : x ≤ R) (hyR : y ≤ R) :
    |x-y| ≤ R*|Real.log x-Real.log y| := by
  have hordered {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
      (hxy : y ≤ x) (hxR : x ≤ R) :
      x-y ≤ R*(Real.log x-Real.log y) := by
    have hlog : Real.log y-Real.log x ≤ y/x-1 := by
      rw [← Real.log_div hy.ne' hx.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hy hx)
    have hm := mul_le_mul_of_nonneg_left hlog hx.le
    have he : x*(y/x-1) = y-x := by field_simp
    rw [he] at hm
    have hl : 0 ≤ Real.log x-Real.log y :=
      sub_nonneg.mpr (Real.log_le_log hy hxy)
    apply le_trans (b := x*(Real.log x-Real.log y))
    · nlinarith
    · exact mul_le_mul_of_nonneg_right hxR hl
  by_cases hxy : y ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy hxy))]
    exact hordered hx hy hxy hxR
  · have hyx := le_of_not_ge hxy
    rw [abs_sub_comm x y,abs_sub_comm (Real.log x) (Real.log y),
      abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hx hyx))]
    exact hordered hy hx hyx hyR

lemma integer_log_frequency_spacing {Z m n : ℕ} (hm : m ∈ Finset.Icc 1 Z)
    (hn : n ∈ Finset.Icc 1 Z) :
    |(m:ℝ)-(n:ℝ)| ≤ (Z:ℝ)*|Real.log (m:ℝ)-Real.log (n:ℝ)| := by
  obtain ⟨hm1,hmZ⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hn1,hnZ⟩ := Finset.mem_Icc.mp hn
  exact log_frequency_spacing (by exact_mod_cast (zero_lt_one.trans_le hm1))
    (by exact_mod_cast (zero_lt_one.trans_le hn1))
    (by exact_mod_cast hmZ) (by exact_mod_cast hnZ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MeanValueGaussianKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian Fourier kernel for the mean value of the actual integer
norm Dirichlet polynomial. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma meanValueGaussianPhase_scale {L : ℝ} (hL : L ≠ 0) (u t : ℝ) :
    meanValueGaussianPhase L u t = meanValueGaussianPhase 1 (L*u) (t/L) := by
  have he : (L*u)*(t/L) = u*t := by field_simp
  simp only [meanValueGaussianPhase,div_one,he]

lemma meanValueGaussianPhase_one_integrable (u : ℝ) :
    Integrable (meanValueGaussianPhase 1 u) := by
  have he : meanValueGaussianPhase 1 u = fun t : ℝ =>
      Complex.exp (-(1:ℂ)*(t:ℂ)^2+((u:ℂ)*Complex.I)*(t:ℂ)+0) := by
    funext t
    simp only [meanValueGaussianPhase,div_one,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  exact integrable_cexp_quadratic (b := (1:ℂ)) (by norm_num) _ _

lemma meanValueGaussianPhase_integrable {L : ℝ} (hL : 0 < L) (u : ℝ) :
    Integrable (meanValueGaussianPhase L u) := by
  have he : meanValueGaussianPhase L u = fun t => meanValueGaussianPhase 1 (L*u) (t/L) :=
    funext (meanValueGaussianPhase_scale hL.ne' u)
  rw [he]
  exact (meanValueGaussianPhase_one_integrable (L*u)).comp_div hL.ne'

lemma meanValueGaussianPhase_one_integral_norm (u : ℝ) :
    ‖∫ t : ℝ, meanValueGaussianPhase 1 u t‖ =
      Real.sqrt Real.pi*Real.exp (-u^2/4) := by
  have he : (∫ t : ℝ, meanValueGaussianPhase 1 u t) =
      (Real.pi/(1:ℂ))^(1/2:ℂ)*Complex.exp (-(u:ℂ)^2/(4*(1:ℂ))) := by
    convert fourierIntegral_gaussian (b := (1:ℂ)) (by norm_num) (u:ℂ) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext t
    simp only [meanValueGaussianPhase,div_one]
    rw [mul_comm]
    congr 1 <;> push_cast <;> ring_nf
  rw [he,norm_mul]
  have hp : ‖(Real.pi/(1:ℂ))^(1/2:ℂ)‖ = Real.sqrt Real.pi := by
    rw [div_one,show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_real,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
      ← Real.sqrt_eq_rpow]
  have ht : -(u:ℂ)^2/(4*(1:ℂ)) = ((-u^2/4:ℝ):ℂ) := by push_cast; ring
  rw [hp,ht,Complex.norm_exp,Complex.ofReal_re]

lemma meanValueGaussianPhase_integral_norm {L : ℝ} (hL : 0 < L) (u : ℝ) :
    ‖∫ t : ℝ, meanValueGaussianPhase L u t‖ =
      L*Real.sqrt Real.pi*Real.exp (-(L*u)^2/4) := by
  have he : meanValueGaussianPhase L u = fun t => meanValueGaussianPhase 1 (L*u) (t/L) :=
    funext (meanValueGaussianPhase_scale hL.ne' u)
  rw [he,Measure.integral_comp_div,norm_smul,Real.norm_eq_abs,abs_of_pos hL,
    meanValueGaussianPhase_one_integral_norm]
  rw [abs_of_pos hL]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MeanValueGaussianRows
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform row sums for the Gaussian matrix on logarithmic frequencies. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma nat_dist_cast_eq_abs (m n : ℕ) : (Nat.dist m n:ℝ) = |(m:ℝ)-(n:ℝ)| := by
  by_cases h : m ≤ n
  · rw [Nat.dist_eq_sub_of_le h,Nat.cast_sub h,abs_of_nonpos (sub_nonpos.mpr (show (m:ℝ) ≤ n by exact_mod_cast h))]
    ring
  · have h' := le_of_not_ge h
    rw [Nat.dist_eq_sub_of_le_right h',Nat.cast_sub h',abs_of_nonneg (sub_nonneg.mpr (show (n:ℝ) ≤ m by exact_mod_cast h'))]

lemma geometric_nat_distance_sum {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (Z n : ℕ) (hn : n ≤ Z) :
    (∑ m ∈ Finset.Icc 1 Z, q^(Nat.dist n m)) ≤ 2/(1-q) := by
  let S := Finset.Icc 1 Z
  let A := S.filter (fun m => m ≤ n)
  let B := S.filter (fun m => ¬m ≤ n)
  have hgeom : (∑ d ∈ Finset.range (Z+1), q^d) ≤ 1/(1-q) := by
    simpa only [Nat.Ico_zero_eq_range,pow_zero] using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := Z+1) hq hq1)
  have hA : (∑ m ∈ A, q^(Nat.dist n m)) ≤ 1/(1-q) := by
    calc
      _ = ∑ m ∈ A, q^(n-m) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp hm).2]
      _ = ∑ d ∈ A.image (fun m => n-m), q^d := by
        symm
        apply Finset.sum_image
        intro m hm k hk he
        have hm' := (Finset.mem_filter.mp hm).2
        have hk' := (Finset.mem_filter.mp hk).2
        change n-m = n-k at he
        omega
      _ ≤ ∑ d ∈ Finset.range (Z+1), q^d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hd
          exact Finset.mem_range.mpr (by omega)
        · intro d _ _
          exact pow_nonneg hq _
      _ ≤ _ := hgeom
  have hB : (∑ m ∈ B, q^(Nat.dist n m)) ≤ 1/(1-q) := by
    calc
      _ = ∑ m ∈ B, q^(m-n) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Nat.dist_eq_sub_of_le (by have := (Finset.mem_filter.mp hm).2; omega)]
      _ = ∑ d ∈ B.image (fun m => m-n), q^d := by
        symm
        apply Finset.sum_image
        intro m hm k hk he
        have hm' := (Finset.mem_filter.mp hm).2
        have hk' := (Finset.mem_filter.mp hk).2
        change m-n = k-n at he
        omega
      _ ≤ ∑ d ∈ Finset.range (Z+1), q^d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hd
          have hmZ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
          exact Finset.mem_range.mpr (by omega)
        · intro d _ _
          exact pow_nonneg hq _
      _ ≤ _ := hgeom
  have he : (∑ m ∈ S, q^(Nat.dist n m)) =
      (∑ m ∈ A, q^(Nat.dist n m))+(∑ m ∈ B, q^(Nat.dist n m)) := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun m => m ≤ n) _).symm
  change (∑ m ∈ S, q^(Nat.dist n m)) ≤ _
  rw [he]
  calc
    _ ≤ 1/(1-q)+1/(1-q) := add_le_add hA hB
    _ = _ := by ring

lemma gaussian_log_frequency_decay {Z n m : ℕ} (hn : n ∈ Finset.Icc 1 Z)
    (hm : m ∈ Finset.Icc 1 Z) {L : ℝ} (hL : (Z:ℝ) ≤ L) :
    Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4) ≤
      (Real.exp (-(1/4:ℝ)))^(Nat.dist n m) := by
  have hdist : 0 ≤ (Nat.dist n m:ℝ) := by positivity
  have hsep : (Nat.dist n m:ℝ) ≤ L*|Real.log (n:ℝ)-Real.log (m:ℝ)| := by
    rw [nat_dist_cast_eq_abs]
    exact (integer_log_frequency_spacing hn hm).trans
      (mul_le_mul_of_nonneg_right hL (abs_nonneg _))
  have hnat : (Nat.dist n m:ℝ) ≤ (Nat.dist n m:ℝ)^2 := by
    have hn' : Nat.dist n m ≤ Nat.dist n m*Nat.dist n m := by
      generalize Nat.dist n m = d
      by_cases hd : d = 0
      · simp [hd]
      · have : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
        nlinarith
    simpa only [pow_two] using (show (Nat.dist n m:ℝ) ≤ (Nat.dist n m:ℝ)*(Nat.dist n m:ℝ) by exact_mod_cast hn')
  have hL0 : 0 ≤ L := le_trans (Nat.cast_nonneg Z) hL
  have hsquare : (Nat.dist n m:ℝ)^2 ≤ (L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2 := by
    have h := sq_le_sq₀ hdist (mul_nonneg hL0 (abs_nonneg _)) |>.mpr hsep
    simpa only [mul_pow,sq_abs] using h
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma gaussian_log_frequency_row_bound {Z n : ℕ} (hn : n ∈ Finset.Icc 1 Z)
    {L : ℝ} (hL : (Z:ℝ) ≤ L) :
    (∑ m ∈ Finset.Icc 1 Z,
      Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4)) ≤
      2/(1-Real.exp (-(1/4:ℝ))) := by
  apply (Finset.sum_le_sum (fun m hm => gaussian_log_frequency_decay hn hm hL)).trans
  exact geometric_nat_distance_sum (Real.exp_pos _).le
    (by rw [Real.exp_lt_one_iff]; norm_num) Z n (Finset.mem_Icc.mp hn).2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MeanValueGaussianEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian mean square of the actual integer-frequency polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma meanValueGaussian_phase_product (L t x y : ℝ) :
    (meanValueGaussianWeight L t:ℂ)*mellinPhase t x*star (mellinPhase t y) =
      meanValueGaussianPhase L (Real.log x-Real.log y) t := by
  simp only [← starRingEnd_apply]
  simp only [meanValueGaussianWeight,meanValueGaussianPhase,mellinPhase,
    Complex.ofReal_exp,← Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma meanValueGaussian_expansion (Z : ℕ) (v : ℕ → ℂ) (L t : ℝ) :
    ((meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2:ℝ):ℂ) =
      ∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        (v n*star (v m))*meanValueGaussianPhase L
          (Real.log (n:ℝ)-Real.log (m:ℝ)) t := by
  rw [Complex.ofReal_mul,Complex.ofReal_pow,← Complex.mul_conj']
  unfold integerNormPolynomial
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [← meanValueGaussian_phase_product]
  simp only [starRingEnd_apply]
  ring

lemma meanValueGaussian_integrable {L : ℝ} (hL : 0 < L) (Z : ℕ) (v : ℕ → ℂ) :
    Integrable (fun t : ℝ => meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) := by
  have hi : Integrable (fun t : ℝ =>
      ∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        (v n*star (v m))*meanValueGaussianPhase L
          (Real.log (n:ℝ)-Real.log (m:ℝ)) t) := by
    apply integrable_finsetSum
    intro n hn
    apply integrable_finsetSum
    intro m hm
    exact (meanValueGaussianPhase_integrable hL _).const_mul _
  have he : (fun t : ℝ => meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) =
      fun t => (∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        (v n*star (v m))*meanValueGaussianPhase L
          (Real.log (n:ℝ)-Real.log (m:ℝ)) t).re := by
    funext t
    rw [← meanValueGaussian_expansion]
    rfl
  rw [he]
  exact hi.re

lemma meanValueGaussian_integral_bound {L : ℝ} (hL : 0 < L)
    (Z : ℕ) (v : ℕ → ℂ) :
    (∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) ≤
      L*Real.sqrt Real.pi * ∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        ‖v n‖*‖v m‖*Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4) := by
  let S := Finset.Icc 1 Z
  have he : Complex.ofReal (∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) =
      ∑ n ∈ S, ∑ m ∈ S, (v n*star (v m))*
        ∫ t : ℝ, meanValueGaussianPhase L (Real.log (n:ℝ)-Real.log (m:ℝ)) t := by
    rw [← integral_complex_ofReal]
    simp_rw [meanValueGaussian_expansion]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro m hm
        exact integral_const_mul _ _
      · intro m hm
        exact (meanValueGaussianPhase_integrable hL _).const_mul _
    · intro n hn
      apply integrable_finsetSum
      intro m hm
      exact (meanValueGaussianPhase_integrable hL _).const_mul _
  have h0 : 0 ≤ ∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2 :=
    integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  calc
    _ = ‖Complex.ofReal (∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0]
    _ ≤ ∑ n ∈ S, ∑ m ∈ S,
        ‖(v n*star (v m))*∫ t : ℝ,
          meanValueGaussianPhase L (Real.log (n:ℝ)-Real.log (m:ℝ)) t‖ := by
      rw [he]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => norm_sum_le _ _))
    _ = _ := by
      simp only [norm_mul,norm_star,meanValueGaussianPhase_integral_norm hL]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring

lemma gaussian_schur_bound {Z : ℕ} {L : ℝ} (hL : (Z:ℝ) ≤ L) (v : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
      ‖v n‖*‖v m‖*Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4)) ≤
      (2/(1-Real.exp (-(1/4:ℝ))))*∑ n ∈ Finset.Icc 1 Z, ‖v n‖^2 := by
  let S := Finset.Icc 1 Z
  let K := fun n m : ℕ => Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4)
  have hsym : ∀ n m, K n m = K m n := by
    intro n m
    dsimp [K]
    congr 1
    ring
  have hrow : ∀ n ∈ S, ∑ m ∈ S, K n m ≤ 2/(1-Real.exp (-(1/4:ℝ))) :=
    fun n hn => gaussian_log_frequency_row_bound hn hL
  have hcol : (∑ n ∈ S, ∑ m ∈ S, ‖v m‖^2*K n m) =
      ∑ n ∈ S, ∑ m ∈ S, ‖v n‖^2*K n m := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    rw [hsym]
  have he : (∑ n ∈ S, ∑ m ∈ S, (‖v n‖^2+‖v m‖^2)*K n m) =
      2*∑ n ∈ S, ‖v n‖^2*(∑ m ∈ S, K n m) := by
    simp_rw [add_mul,Finset.sum_add_distrib]
    rw [hcol]
    simp_rw [← Finset.mul_sum]
    ring
  have hpair : 2*(∑ n ∈ S, ∑ m ∈ S, ‖v n‖*‖v m‖*K n m) ≤
      ∑ n ∈ S, ∑ m ∈ S, (‖v n‖^2+‖v m‖^2)*K n m := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro m hm
    have hp : 2*‖v n‖*‖v m‖ ≤ ‖v n‖^2+‖v m‖^2 := by nlinarith [sq_nonneg (‖v n‖-‖v m‖)]
    exact (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le)
  have htotal : (∑ n ∈ S, ‖v n‖^2*(∑ m ∈ S, K n m)) ≤
      (2/(1-Real.exp (-(1/4:ℝ))))*∑ n ∈ S, ‖v n‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg ‖v n‖)
  change (∑ n ∈ S, ∑ m ∈ S, ‖v n‖*‖v m‖*K n m) ≤ _
  rw [he] at hpair
  linarith

 theorem integerNormPolynomial_gaussian_meanSquare {Z : ℕ} {L : ℝ}
    (hL : 0 < L) (hZL : (Z:ℝ) ≤ L) (v : ℕ → ℂ) :
    (∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) ≤
      (L*Real.sqrt Real.pi*(2/(1-Real.exp (-(1/4:ℝ)))))*
        ∑ n ∈ Finset.Icc 1 Z, ‖v n‖^2 := by
  exact (meanValueGaussian_integral_bound hL Z v).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (gaussian_schur_bound hZL v)
      (mul_nonneg hL.le (Real.sqrt_nonneg _)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MontgomeryVaughanProof
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The required ordinary mean value bound, proved by a Gaussian majorant. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma integerNormPolynomial_continuous (Z : ℕ) (v : ℕ → ℂ) :
    Continuous (integerNormPolynomial Z v) := by
  unfold integerNormPolynomial mellinPhase
  fun_prop

lemma gaussian_interval_majorant {L a b : ℝ} (hL : 0 < L) (hab : a ≤ b)
    (ha : -L ≤ a) (hb : b ≤ L) (Z : ℕ) (v : ℕ → ℂ) :
    (∫ t in a..b, ‖integerNormPolynomial Z v t‖^2) ≤
      Real.exp 1*(∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) := by
  let f := fun t : ℝ => ‖integerNormPolynomial Z v t‖^2
  let g := fun t : ℝ => meanValueGaussianWeight L t*f t
  have hf : IntervalIntegrable f volume a b :=
    ((integerNormPolynomial_continuous Z v).norm.pow 2).intervalIntegrable _ _
  have hg : Integrable g := meanValueGaussian_integrable hL Z v
  have hgI : IntervalIntegrable g volume a b := hg.intervalIntegrable
  have hbound : ∀ t ∈ Set.Icc a b, f t ≤ Real.exp 1*g t := by
    intro t ht
    have htL : |t| ≤ L := abs_le.mpr ⟨ha.trans ht.1,ht.2.trans hb⟩
    have hratio : |t/L| ≤ 1 := by
      rw [abs_div,abs_of_pos hL]
      exact (div_le_one hL).mpr htL
    have hsq : (t/L)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hratio
    have he : 1 ≤ Real.exp 1*meanValueGaussianWeight L t := by
      rw [meanValueGaussianWeight,← Real.exp_add]
      calc
        1 = Real.exp 0 := Real.exp_zero.symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    calc
      f t = 1*f t := by ring
      _ ≤ (Real.exp 1*meanValueGaussianWeight L t)*f t :=
        mul_le_mul_of_nonneg_right he (sq_nonneg _)
      _ = _ := by dsimp [g]; ring
  calc
    _ ≤ ∫ t in a..b, Real.exp 1*g t :=
      intervalIntegral.integral_mono_on hab hf (hgI.const_mul _) hbound
    _ = Real.exp 1*(∫ t in a..b, g t) := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [intervalIntegral.integral_of_le hab]
      exact setIntegral_le_integral hg (Filter.Eventually.of_forall
        (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))

lemma integerNormPolynomial_translate (Z : ℕ) (v : ℕ → ℂ) (t c : ℝ) :
    integerNormPolynomial Z v (t+c) =
      integerNormPolynomial Z (fun n => v n*mellinPhase c (n:ℝ)) t := by
  unfold integerNormPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [mellinPhase_add]
  ring

lemma ordinaryMeanValueConstant_pos : 0 < ordinaryMeanValueConstant := by
  unfold ordinaryMeanValueConstant
  have he : Real.exp (-(1/4:ℝ)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  positivity

/-- The ordinary Dirichlet-polynomial mean-square bound. -/
theorem montgomeryVaughanBound_proved : MontgomeryVaughanBound ordinaryMeanValueConstant := by
  intro Z v a b hab
  by_cases hZ : Z = 0
  · subst Z
    simp [integerNormPolynomial]
  have hZpos : (0:ℝ) < Z := by exact_mod_cast Nat.pos_of_ne_zero hZ
  let L : ℝ := b-a+Z
  let c : ℝ := (a+b)/2
  let w : ℕ → ℂ := fun n => v n*mellinPhase c (n:ℝ)
  have hL : 0 < L := by dsimp [L]; linarith
  have hZL : (Z:ℝ) ≤ L := by dsimp [L]; linarith
  have he : (∫ t in a..b, ‖integerNormPolynomial Z v t‖^2) =
      ∫ t in a-c..b-c, ‖integerNormPolynomial Z w t‖^2 := by
    have hs := intervalIntegral.integral_comp_add_right
      (a := a-c) (b := b-c) (fun t => ‖integerNormPolynomial Z v t‖^2) c
    simp only [sub_add_cancel] at hs
    rw [← hs]
    apply intervalIntegral.integral_congr
    intro t ht
    change ‖integerNormPolynomial Z v (t+c)‖^2 = ‖integerNormPolynomial Z w t‖^2
    rw [integerNormPolynomial_translate]
  have henergy : (∑ n ∈ Finset.Icc 1 Z, ‖w n‖^2) =
      ∑ n ∈ Finset.Icc 1 Z, ‖v n‖^2 := by
    simp only [w,norm_mul,mellinPhase_norm,mul_one]
  rw [he]
  calc
    _ ≤ Real.exp 1*(∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z w t‖^2) :=
      gaussian_interval_majorant hL (by linarith) (by dsimp [L,c]; linarith)
        (by dsimp [L,c]; linarith) Z w
    _ ≤ Real.exp 1*((L*Real.sqrt Real.pi*(2/(1-Real.exp (-(1/4:ℝ)))))*
        ∑ n ∈ Finset.Icc 1 Z, ‖w n‖^2) :=
      mul_le_mul_of_nonneg_left (integerNormPolynomial_gaussian_meanSquare hL hZL w)
        (Real.exp_pos _).le
    _ = _ := by rw [henergy]; unfold ordinaryMeanValueConstant; dsimp [L]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDyadicReconstruction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual prime sums satisfy the small-argument and local-growth
conditions of dyadic reconstruction; closed interval endpoints cost O(1). -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeCutoffSum_on (c : Eisenstein → ℂ) {X Y : ℝ} (hXY : X ≤ Y) :
    primeCutoffSum c X = ∑ p ∈ primeCutoff Y, if norm p ≤ X then c p else 0 := by
  have hs : primeCutoff X = (primeCutoff Y).filter (fun p => norm p ≤ X) := by
    ext p
    simp only [mem_primeCutoff,Finset.mem_filter]
    constructor
    · intro hp
      exact ⟨⟨hp.1,hp.2.trans hXY⟩,hp.2⟩
    · intro hp
      exact ⟨hp.1.1,hp.2⟩
  rw [primeCutoffSum_eq_sum,hs,Finset.sum_filter]

lemma primeCutoffSum_zero_small (c : Eisenstein → ℂ) {X : ℝ} (hX : X < 1) :
    primeCutoffSum c X = 0 := by
  rw [primeCutoffSum_eq_sum]
  apply Finset.sum_eq_zero
  intro p hp
  have hh := mem_primeCutoff.mp hp
  have hl := one_le_norm hh.1.2.ne_zero
  linarith

lemma primeCutoffSum_norm_le (c : Eisenstein → ℂ) {M X : ℝ} (hM : 0 ≤ M)
    (hc : ∀ p : Eisenstein, primaryPrime p → ‖c p‖ ≤ M) (hX : 0 ≤ X) :
    ‖primeCutoffSum c X‖ ≤ 18*M*X := by
  have hsub : primeCutoff X ⊆ nonzeroNormBall X := by
    intro p hp
    have hh := mem_primeCutoff.mp hp
    exact mem_nonzeroNormBall.mpr ⟨hh.2,hh.1.2.ne_zero⟩
  have hcard := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hX)
  rw [primeCutoffSum_eq_sum]
  calc
    _ ≤ ∑ _p ∈ primeCutoff X, M := (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun p hp => hc p (mem_primeCutoff.mp hp).1))
    _ = ((primeCutoff X).card:ℝ)*M := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (18*X)*M := mul_le_mul_of_nonneg_right hcard hM
    _ = _ := by ring

lemma prime_norm_boundary_sum_le (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (c : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ p ∈ S, ‖c p‖ ≤ M) (Y : ℝ) :
    ‖∑ p ∈ S with norm p = Y, c p‖ ≤ 2*M := by
  have hs : S.filter (fun p => norm p = Y) ⊆
      S.filter (fun p => (normNat p:ℤ) = ⌊Y⌋) := by
    intro p hp
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,?_⟩
    have he : ((normNat p:ℤ):ℝ) = Y := by
      simpa only [Int.cast_natCast,normNat_cast] using (Finset.mem_filter.mp hp).2
    simpa only [Int.floor_intCast] using (congrArg Int.floor he)
  have hcard := (Finset.card_le_card hs).trans (prime_norm_fiber_card_le_two S hS ⌊Y⌋)
  calc
    _ ≤ ∑ p ∈ S with norm p = Y, M := (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun p hp => hc p (Finset.mem_filter.mp hp).1))
    _ = ((S.filter (fun p => norm p = Y)).card:ℝ)*M := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 2*M := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hM

lemma prime_dyadic_endpoint_identity (c : Eisenstein → ℂ) {X : ℝ} (hX : 0 ≤ X) :
    dyadicDifference (primeCutoffSum c) X-primeDyadicSum c (X/2) =
      -(∑ p ∈ primeCutoff (2*X) with norm p = X/2, c p) := by
  rw [dyadicDifference,primeCutoffSum_on c (show X ≤ 2*X by linarith),
    primeCutoffSum_on c (show X/2 ≤ 2*X by linarith)]
  unfold primeDyadicSum
  rw [show 4*(X/2)=2*X by ring,show 2*(X/2)=X by ring,
    ←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,Finset.sum_filter,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  unfold intervalStep
  simp only [Set.mem_Icc]
  by_cases he : norm p = X/2
  · have hle : norm p ≤ X := by linarith
    have hhalf : X/2 ≤ X := by linarith
    simp only [he,hhalf,le_refl,true_and,ite_true, if_true,Complex.ofReal_one,mul_one]
    ring
  · by_cases hlo : norm p ≤ X/2
    · have hn : ¬X/2 ≤ norm p := by intro hh; exact he (le_antisymm hlo hh)
      have hle : norm p ≤ X := by linarith
      simp only [he,hle,hlo,hn,false_and,ite_true, if_true,ite_false, if_false,Complex.ofReal_zero,mul_zero,sub_self,neg_zero]
    · have hl : X/2 ≤ norm p := (lt_of_not_ge hlo).le
      by_cases hhi : norm p ≤ X
      all_goals simp only [he,hlo,hl,hhi,true_and,ite_true, if_true,ite_false, if_false,
        Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,sub_zero,sub_self,neg_zero]

lemma prime_dyadic_endpoint_bound (c : Eisenstein → ℂ) {M X : ℝ} (hM : 0 ≤ M)
    (hc : ∀ p : Eisenstein, primaryPrime p → ‖c p‖ ≤ M) (hX : 0 ≤ X) :
    ‖dyadicDifference (primeCutoffSum c) X-primeDyadicSum c (X/2)‖ ≤ 2*M := by
  rw [prime_dyadic_endpoint_identity c hX,norm_neg]
  exact prime_norm_boundary_sum_le _ (fun p hp => (mem_primeCutoff.mp hp).1) c hM
    (fun p hp => hc p (mem_primeCutoff.mp hp).1) _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDyadicComparison
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing from the literal closed dyadic prime intervals to the full
prime comparison. The endpoint mass is proved negligible explicitly. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

theorem primeCutoffSum_isLittleO_of_dyadic (c : Eisenstein → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hc : ∀ p : Eisenstein, primaryPrime p → ‖c p‖ ≤ M)
    (hd : (fun X => primeDyadicSum c X) =o[atTop] firstMomentScale) :
    primeCutoffSum c =o[atTop] firstMomentScale := by
  apply dyadic_littleO_firstMoment (primeCutoffSum c)
    (fun _ hX => primeCutoffSum_zero_small c hX) (show 0 ≤ 27*M by positivity)
  · intro X hX
    have hXp : 0 ≤ X := (by norm_num : (0:ℝ) ≤ 1).trans hX
    have h1 := primeCutoffSum_norm_le c hM hc hXp
    have h2 := primeCutoffSum_norm_le c (X := X/2) hM hc (div_nonneg hXp (by norm_num))
    apply (norm_sub_le _ _).trans
    change ‖primeCutoffSum c X‖+‖primeCutoffSum c (X/2)‖ ≤ _
    linarith
  · have hhalf : (fun X : ℝ => primeDyadicSum c (X/2)) =o[atTop] firstMomentScale := by
      have hs : (firstMomentScale ∘ (fun X : ℝ => X/2)) =O[atTop] firstMomentScale := by
        change (fun X : ℝ => firstMomentScale (X/2)) =O[atTop] firstMomentScale
        simpa only [pow_one] using firstMomentScale_dyadic_isBigO 1
      exact (hd.comp_tendsto
        (tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2))).trans_isBigO hs
    have he : (fun X : ℝ => dyadicDifference (primeCutoffSum c) X-primeDyadicSum c (X/2))
        =O[atTop] (fun _ : ℝ => (1:ℝ)) := by
      apply IsBigO.of_bound (2*M)
      filter_upwards [eventually_ge_atTop (0:ℝ)] with X hX
      simpa only [norm_one,mul_one] using prime_dyadic_endpoint_bound c hM hc hX
    have hconst : (fun _ : ℝ => (1:ℝ)) =o[atTop] firstMomentScale := by
      apply isLittleO_const_left.mpr
      right
      apply tendsto_firstMomentScale.congr'
      filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
      exact (Real.norm_of_nonneg (firstMomentScale_pos hX).le).symm
    apply ((he.trans_isLittleO hconst).add hhalf).congr' ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall (fun X => by dsimp; ring)

theorem angularPrimeDifference_isLittleO_of_dyadic (ℓ : ℤ)
    (hd : (fun X => sharpDyadicPrimeComparison ℓ X) =o[atTop] firstMomentScale) :
    primeCutoffSum (primeComparisonCoefficient ℓ) =o[atTop] firstMomentScale :=
  primeCutoffSum_isLittleO_of_dyadic (primeComparisonCoefficient ℓ)
    (by linarith [cStar_pos]) (fun _ hp => primeComparisonCoefficient_bound ℓ hp) hd

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered prime comparison from the constructed arithmetic theta
transform, the actual low-height bounds and the actual high-height tails.
No published analytic input is retained as a hypothesis. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

lemma cubicTheta_primeComparison (ℓ : ℤ) :
    primeCutoffSum (primeComparisonCoefficient ℓ)=o[atTop] firstMomentScale := by
  obtain ⟨η,Ct,hη,hηsmall,hCt,htail⟩ := cubicTheta_primeProductGaussTail_isLittleO ℓ
  have hH : ∀ᶠ X : ℝ in atTop,0<X^(1/6+η:ℝ) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    exact Real.rpow_pos_of_pos hX _
  have hT : ∀ᶠ X : ℝ in atTop,(1+Real.log X)^8≤(1+Real.log X)^Ct := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
    exact pow_le_pow_right₀ (by linarith [Real.log_nonneg hX]) hCt
  have hl := cubicTheta_primeProductLowHeight_isLittleO ℓ Ct (fun X => X^(1/6+η:ℝ)) hH
  have hr := sharp_prime_product_log_height_remainder montgomeryVaughanBound_proved
    ordinaryMeanValueConstant_pos.le hη hηsmall (fun X => (1+Real.log X)^Ct) hT ℓ
  have hred : (fun X => sharpDyadicPrimeComparison ℓ X-
      ((2*Real.pi:ℝ):ℂ)⁻¹*primeProductGaussTail ℓ (X^(1/6+η:ℝ))
        ((1+Real.log X)^Ct) X)=o[atTop] firstMomentScale := by
    apply (hr.add (hl.const_mul_left (((2*Real.pi:ℝ):ℂ)⁻¹))).congr' ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall (fun X => by dsimp; ring)
  have hd : (fun X => sharpDyadicPrimeComparison ℓ X)=o[atTop] firstMomentScale := by
    apply (hred.add (htail.const_mul_left (((2*Real.pi:ℝ):ℂ)⁻¹))).congr' ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall (fun X => by dsimp; ring)
  exact angularPrimeDifference_isLittleO_of_dyadic ℓ hd

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact first moment and both fixed-angular main theorems. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

theorem patterson_angularComparison_oai : AngularComparisonStatement :=
  cubicTheta_primeComparison

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.patterson_angularComparison_oai := @OAI.CubicFirstMoment.patterson_angularComparison_oai
