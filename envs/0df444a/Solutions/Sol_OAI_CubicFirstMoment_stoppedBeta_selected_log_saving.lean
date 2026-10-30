-- Prove2me | solution 1 for OAI.CubicFirstMoment.stoppedBeta_selected_log_saving
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:45:15.447473+00:00
-- url     : https://prove2.me/submissions/0502f4ca-2916-485b-85e1-3af4fd96b257

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015

section
-- module Solutions.OAIQ096_CM.CubicGram_Coordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_PrimaryNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeJoin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedRoughness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedAbsoluteMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The absolute, uncollected complementary factorization mass used
after a free prime is cancelled. No cancellation inside beta is used. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rough_pairAbsolute_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) (v f : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ r ∈ R, ‖v r‖ ≤ M)
    (hf : ∀ d ∈ D, ‖f d‖ ≤ 1) {b : Eisenstein}
    (hb : primary b) (hs : Squarefree b) {w : ℝ} (hw : 1 ≤ w)
    (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    {k : ℕ} (hsize : norm b < w^k) : pairAbsolute R D v f b ≤ (2^k:ℕ)*M := by
  calc
    _ ≤ ∑ _p ∈ primaryPairFiber R D b, M := by
      apply Finset.sum_le_sum
      intro p hp
      have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact (mul_le_mul_of_nonneg_left (hf p.2 hmem.2) (_root_.norm_nonneg _)).trans
        ((mul_one _).le.trans (hv p.1 hmem.1))
    _ = ((primaryPairFiber R D b).card:ℝ)*M := by simp
    _ ≤ ((R.filter (fun r => r ∣ b)).card:ℝ)*M :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (primaryPairFiber_card_le R D hR b)) hM
    _ ≤ (2^k:ℕ)*M := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
      (rough_primary_divisor_card R hR hb hs hw hrough hsize)) hM


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedComplementMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary pair mass after a selected-bin prime is removed.
The rough distinguished factor has only a bounded number of choices for
each squarefree product, so the total mass is linear in its norm range. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stopped_complement_mass (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) (hD : ∀ d ∈ D, primary d)
    (v : Eisenstein → ℂ) {M Y w : ℝ} (hM : 0 ≤ M) (hY : 0 ≤ Y)
    (hv : ∀ r ∈ R, ‖v r‖ ≤ M) (hw : 1 ≤ w)
    (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    {k : ℕ} (hsize : Y < w^k) :
    (∑ t ∈ (R ×ˢ D).filter (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y),
      ‖v t.1‖) ≤ 18*Y*((2^k:ℕ)*M) := by
  let U := (R ×ˢ D).filter (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y)
  let B := (primaryElementBall Y).filter Squarefree
  have hmap (t : Eisenstein × Eisenstein) (ht : t ∈ U) : t.1*t.2 ∈ B := by
    obtain ⟨ht,hpred⟩ := Finset.mem_filter.mp ht
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    exact Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr
      ⟨primary_mul (hR _ hr) (hD _ hd),hpred.2⟩,hpred.1⟩
  have hfiber (b : Eisenstein) (hb : b ∈ B) :
      (∑ t ∈ U with t.1*t.2 = b, ‖v t.1‖) ≤ (2^k:ℕ)*M := by
    obtain ⟨hb,hs⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb,hbY⟩ := mem_primaryElementBall.mp hb
    have hsub : U.filter (fun t => t.1*t.2 = b) ⊆ primaryPairFiber R D b := by
      intro t ht
      obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,he⟩
    calc
      _ ≤ ∑ t ∈ primaryPairFiber R D b, ‖v t.1‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => _root_.norm_nonneg _)
      _ = pairAbsolute R D v (fun _ => 1) b := by
        simp only [pairAbsolute,norm_one,mul_one]
      _ ≤ _ := rough_pairAbsolute_bound R D hR v (fun _ => 1) hM hv
        (fun _ _ => by simp) hb hs hw hrough (hbY.trans_lt hsize)
  calc
    _ = ∑ b ∈ B, ∑ t ∈ U with t.1*t.2 = b, ‖v t.1‖ :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ _b ∈ B, (2^k:ℕ)*M := Finset.sum_le_sum hfiber
    _ = (B.card:ℝ)*((2^k:ℕ)*M) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (primaryElementBall_card_le hY))
      (mul_nonneg (Nat.cast_nonneg _) hM)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIntervalGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The stopped crossing tests with one prime left free. A distinguished
prime enters by its actual norm; a selected-bin prime leaves every
surrogate prefix unchanged while its bin is fixed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- A fixed-order tie rule changes the lower norm interval at just the
single norm of the largest complementary prime. -/
lemma largestPrimePredicate_away_tie (code : Eisenstein → ℕ)
    (s : Finset Eisenstein) (p : Eisenstein) (hne : normNat p ≠ s.sup normNat) :
    largestPrimePredicate code s p ↔ s.sup normNat < normNat p := by
  constructor
  · intro h
    have hs : s.sup normNat ≤ normNat p := by
      apply Finset.sup_le
      intro q hq
      rcases h q hq with hlt | he
      · exact hlt.le
      · exact he.1.le
    exact lt_of_le_of_ne hs hne.symm
  · intro h q hq
    exact Or.inl ((Finset.le_sup (f := normNat) hq).trans_lt h)

lemma primeSurrogate_insert_same_bin (s : Finset Eisenstein)
    (b : Eisenstein → ℕ) (ell : ℕ → ℝ) {p q : Eisenstein}
    (hp : p ∉ s) (hq : q ∉ s) (hb : b p = b q) :
    primeSurrogate (insert p s) b ell = primeSurrogate (insert q s) b ell := by
  simp only [primeSurrogate,Finset.prod_insert hp,Finset.prod_insert hq,hb]

lemma primeSurrogate_prefix_insert_same_bin (s : Finset Eisenstein)
    (b : Eisenstein → ℕ) (ell : ℕ → ℝ) {p q : Eisenstein}
    (hp : p ∉ s) (hq : q ∉ s) (hb : b p = b q) (j : ℕ) :
    primeSurrogate (primeBinPrefix (insert p s) b j) b ell =
      primeSurrogate (primeBinPrefix (insert q s) b j) b ell := by
  by_cases hj : b p < j
  · have hqj : b q < j := by simpa only [←hb] using hj
    have hp' : p ∉ primeBinPrefix s b j := fun h => hp (Finset.mem_filter.mp h).1
    have hq' : q ∉ primeBinPrefix s b j := fun h => hq (Finset.mem_filter.mp h).1
    simp only [primeBinPrefix,Finset.filter_insert,hj,hqj,ite_true, if_true]
    exact primeSurrogate_insert_same_bin _ b ell hp' hq' hb
  · have hqj : ¬b q < j := by simpa only [←hb] using hj
    simp only [primeBinPrefix,Finset.filter_insert,hj,hqj,ite_false, if_false]

lemma primeBin_card_insert_same_bin (s : Finset Eisenstein)
    (b : Eisenstein → ℕ) {p q : Eisenstein}
    (hp : p ∉ s) (hq : q ∉ s) (hb : b p = b q) (j : ℕ) :
    (primeBin (insert p s) b j).card = (primeBin (insert q s) b j).card := by
  by_cases hj : b p = j
  · have hqj : b q = j := hb.symm.trans hj
    have hp' : p ∉ s.filter (fun r => b r = j) := fun h => hp (Finset.mem_filter.mp h).1
    have hq' : q ∉ s.filter (fun r => b r = j) := fun h => hq (Finset.mem_filter.mp h).1
    simp only [primeBin,Finset.filter_insert,hj,hqj,ite_true, if_true,
      Finset.card_insert_of_notMem hp',Finset.card_insert_of_notMem hq']
  · have hqj : ¬b q = j := fun h => hj (hb.trans h)
    simp only [primeBin,Finset.filter_insert,hj,hqj,ite_false, if_false]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeMoebiusExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing one prime from the actual unordered cutoff-Mobius product.
The remaining coefficient and character are constant on the free prime;
there is no permutation or divisor multiplicity in this identity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_prime_mul (ψ : ℝ → ℝ) (w : ℝ)
    {p c : Eisenstein} (hp : primaryPrime p) (hc : primary c)
    (hs : Squarefree c) (hpc : ¬p ∣ c) :
    cutoffMoebius ψ w (p*c) = -(ψ (norm p/w):ℂ)*cutoffMoebius ψ w c := by
  have hpnot : p ∉ primaryPrimeFactors c :=
    fun h => hpc (primaryPrimeFactor_spec hc h).2
  have hf : ∀ q ∈ insert p (primaryPrimeFactors c), primaryPrime q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (primaryPrimeFactor_spec hc hq).1
  calc
    _ = cutoffMoebius ψ w (∏ q ∈ insert p (primaryPrimeFactors c), q) := by
      rw [Finset.prod_insert hpnot,primaryPrimeFactors_prod hc hs]
    _ = ∏ q ∈ insert p (primaryPrimeFactors c), -(ψ (norm q/w):ℂ) :=
      cutoffMoebius_prime_product ψ w _ hf
    _ = -(ψ (norm p/w):ℂ)*cutoffMoebius ψ w c := by
      rw [Finset.prod_insert hpnot,←cutoffMoebius_prime_product ψ w (primaryPrimeFactors c)
        (fun q hq => (primaryPrimeFactor_spec hc hq).1),primaryPrimeFactors_prod hc hs]

theorem cutoffMoebius_free_prime_identity (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (ψ : ℝ → ℝ) (w u : ℝ)
    {c : Eisenstein} (hc : primary c) (hs : Squarefree c) (v : Eisenstein) :
    (∑ p ∈ S with ¬p ∣ c,
      cutoffMoebius ψ w (p*c)*normTwist u (p*c)*cubicSymbol (p*c) v) =
    (-cutoffMoebius ψ w c*normTwist u c*cubicSymbol c v)*
      ∑ p ∈ S with ¬p ∣ c, (ψ (norm p/w):ℂ)*normTwist u p*cubicSymbol p v := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpS,hpc⟩ := Finset.mem_filter.mp hp
  have hp' := hS p hpS
  rw [cutoffMoebius_prime_mul ψ w hp' hc hs hpc,
    normTwist_mul u hp'.2.ne_zero (primary_ne_zero hc),
    cubicSymbol_mul_lower hp'.2.ne_zero (primary_ne_zero hc)]
  ring

lemma cutoffMoebius_free_prime_prefactor_bound {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w u : ℝ)
    {c : Eisenstein} (hc : primary c) (v : Eisenstein) :
    ‖-cutoffMoebius ψ w c*normTwist u c*cubicSymbol c v‖ ≤ 1 := by
  rw [norm_mul,norm_mul,norm_neg,norm_normTwist,mul_one]
  exact (mul_le_mul (cutoffMoebius_norm_le_one hψ w c) (norm_cubicSymbol_le_one hc v)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimeIntervals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete selected-side stopping predicates. Replacing one prime
within its fixed bin leaves every selected-bin surrogate test unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrimeFactors_prime_mul {p c : Eisenstein} (hp : primaryPrime p)
    (hc : primary c) (hs : Squarefree c) (hpc : ¬p ∣ c) :
    primaryPrimeFactors (p*c) = insert p (primaryPrimeFactors c) := by
  have hpnot : p ∉ primaryPrimeFactors c :=
    fun h => hpc (primaryPrimeFactor_spec hc h).2
  have hprime : ∀ q ∈ insert p (primaryPrimeFactors c), primaryPrime q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (primaryPrimeFactor_spec hc hq).1
  have h := primaryPrimeFactors_finset_prod (insert p (primaryPrimeFactors c)) hprime
  simpa only [Finset.prod_insert hpnot,primaryPrimeFactors_prod hc hs] using h

lemma stoppingPrimeSetTest_insert_same_bin (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k : ℕ) (Z : ℝ) (r : Eisenstein)
    {p q : Eisenstein} (hp : p ∉ s) (hq : q ∉ s) (hbin : bin p = bin q) :
    stoppingPrimeSetTest (insert p s) bin ell j k Z r ↔
      stoppingPrimeSetTest (insert q s) bin ell j k Z r := by
  have hno : (∀ t ∈ insert p s, bin t ≤ j) ↔ (∀ t ∈ insert q s, bin t ≤ j) := by
    simp only [Finset.forall_mem_insert,hbin]
  simp only [stoppingPrimeSetTest,hno,
    primeSurrogate_insert_same_bin s bin ell hp hq hbin,
    primeBin_card_insert_same_bin s bin hp hq hbin j]

theorem stoppingSideTest_free_prime_same_bin (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (j k : ℕ) (Z : ℝ) (r : Eisenstein)
    {c p q : Eisenstein} (hc : primary c) (hs : Squarefree c)
    (hp : primaryPrime p) (hq : primaryPrime q) (hpc : ¬p ∣ c) (hqc : ¬q ∣ c)
    (hbin : bin p = bin q) :
    stoppingSideTest bin ell j k Z r (p*c) ↔
      stoppingSideTest bin ell j k Z r (q*c) := by
  unfold stoppingSideTest
  rw [primaryPrimeFactors_prime_mul hp hc hs hpc,primaryPrimeFactors_prime_mul hq hc hs hqc]
  exact stoppingPrimeSetTest_insert_same_bin _ bin ell j k Z r
    (fun h => hpc (primaryPrimeFactor_spec hc h).2)
    (fun h => hqc (primaryPrimeFactor_spec hc h).2) hbin

theorem failedStage_free_prime_same_bin (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (h : ℕ) (Q : ℝ) (r : Eisenstein)
    {c p q : Eisenstein} (hc : primary c) (hs : Squarefree c)
    (hp : primaryPrime p) (hq : primaryPrime q) (hpc : ¬p ∣ c) (hqc : ¬q ∣ c)
    (hbin : bin p = bin q) :
    (norm r*primeSurrogate (primeBinPrefix (primaryPrimeFactors (p*c)) bin h) bin ell < Q) ↔
      norm r*primeSurrogate (primeBinPrefix (primaryPrimeFactors (q*c)) bin h) bin ell < Q := by
  rw [primaryPrimeFactors_prime_mul hp hc hs hpc,primaryPrimeFactors_prime_mul hq hc hs hqc,
    primeSurrogate_prefix_insert_same_bin _ bin ell
      (fun hp => hpc (primaryPrimeFactor_spec hc hp).2)
      (fun hq => hqc (primaryPrimeFactor_spec hc hq).2) hbin h]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimePredicate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both actual stopping branches, including failure of the earlier
crossing test. Fixing the selected prime's bin fixes all these tests. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedSideTest_free_prime_same_bin (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (j k h : ℕ) (Z Q : ℝ) (early : Bool) (r : Eisenstein)
    {c p q : Eisenstein} (hc : primary c) (hs : Squarefree c)
    (hp : primaryPrime p) (hq : primaryPrime q) (hpc : ¬p ∣ c) (hqc : ¬q ∣ c)
    (hbin : bin p = bin q) :
    stoppedSideTest bin ell j k h Z Q early r (p*c) ↔
      stoppedSideTest bin ell j k h Z Q early r (q*c) := by
  exact and_congr
    (stoppingSideTest_free_prime_same_bin bin ell j k Z r hc hs hp hq hpc hqc hbin)
    (or_congr Iff.rfl
      (failedStage_free_prime_same_bin bin ell h Q r hc hs hp hq hpc hqc hbin))

theorem sum_stoppedSide_same_bin (S : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r : Eisenstein) {c p₀ : Eisenstein} (hc : primary c) (hsc : Squarefree c)
    (hp₀ : p₀ ∈ S) (hS : ∀ p ∈ S, primaryPrime p)
    (hcop : ∀ p ∈ S, ¬p ∣ c) (hbin : ∀ p ∈ S, bin p = bin p₀)
    (F : Eisenstein → ℂ) :
    (∑ p ∈ S with stoppedSideTest bin ell j k h Z Q early r (p*c), F p) =
      if stoppedSideTest bin ell j k h Z Q early r (p₀*c) then ∑ p ∈ S, F p else 0 := by
  rw [Finset.sum_filter]
  by_cases ht : stoppedSideTest bin ell j k h Z Q early r (p₀*c)
  · rw [ite_eq_left ht]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ite_eq_left ((stoppedSideTest_free_prime_same_bin bin ell j k h Z Q early r hc hsc
      (hS p hp) (hS p₀ hp₀) (hcop p hp) (hcop p₀ hp₀) (hbin p hp)).mpr ht)]
  · rw [ite_eq_right ht]
    apply Finset.sum_eq_zero
    intro p hp
    apply ite_eq_right
    intro h'
    exact ht ((stoppedSideTest_free_prime_same_bin bin ell j k h Z Q early r hc hsc
      (hS p hp) (hS p₀ hp₀) (hcop p hp) (hcop p₀ hp₀) (hbin p hp)).mp h')

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeBinGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeNormEndpoints
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint and largest-prime tie corrections. At most two primary
primes have a prescribed norm, so endpoint choices cost an absolute
constant in a bounded prime sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_eq_or_conjugate_of_norm_eq {p q : Eisenstein}
    (hp : primaryPrime p) (hq : primaryPrime q) (hn : norm p = norm q) :
    p = q ∨ p = conjugate q := by
  have hnr : (normNat p:ℝ) = normNat q := by simpa only [normNat_cast] using hn
  have hn' : normNat p = normNat q := by exact_mod_cast hnr
  have heq : p*conjugate p = q*conjugate q := by
    rw [←normNat_cast_eq_mul_conjugate,←normNat_cast_eq_mul_conjugate,hn']
  have hd : p ∣ q*conjugate q := heq ▸ dvd_mul_right p (conjugate p)
  rcases hp.2.dvd_or_dvd hd with hd | hd
  · exact Or.inl (primary_associated_eq hp.1 hq.1
      ((hp.2.dvd_prime_iff_associated hq.2).mp hd))
  · exact Or.inr (primary_associated_eq hp.1 (primaryPrime_conjugate hq).1
      ((hp.2.dvd_prime_iff_associated (primaryPrime_conjugate hq).2).mp hd))

theorem primaryPrime_norm_fiber_card (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (x : ℝ) :
    (S.filter (fun p => norm p = x)).card ≤ 2 := by
  let T := S.filter (fun p => norm p = x)
  by_cases hT : T.Nonempty
  · obtain ⟨q,hq⟩ := hT
    have hsub : T ⊆ {q,conjugate q} := by
      intro p hp
      have he := primaryPrime_eq_or_conjugate_of_norm_eq
        (hS p (Finset.mem_filter.mp hp).1) (hS q (Finset.mem_filter.mp hq).1)
        ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
      simpa only [Finset.mem_insert,Finset.mem_singleton] using he
    apply (Finset.card_le_card hsub).trans
    calc
      ({q,conjugate q}:Finset Eisenstein).card ≤ ({conjugate q}:Finset Eisenstein).card+1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  · change T.card ≤ 2
    rw [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.card_empty]
    norm_num

lemma primaryPrime_two_norm_card (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (a b : ℝ) :
    (S.filter (fun p => norm p = a ∨ norm p = b)).card ≤ 4 := by
  have he : S.filter (fun p => norm p = a ∨ norm p = b) =
      S.filter (fun p => norm p = a) ∪ S.filter (fun p => norm p = b) := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_union]
    tauto
  rw [he]
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add (primaryPrime_norm_fiber_card S hS a)
      (primaryPrime_norm_fiber_card S hS b)).trans (by norm_num))

/-- This also covers an arbitrary fixed-order selection among equal-norm
largest primes. Away from the two boundary norms the predicates agree. -/
theorem prime_interval_endpoint_difference (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (P Q : Eisenstein → Prop) (a b : ℝ)
    (hPQ : ∀ p ∈ S, norm p ≠ a → norm p ≠ b → (P p ↔ Q p))
    (w : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ p ∈ S, ‖w p‖ ≤ M) :
    ‖(∑ p ∈ S with P p, w p)-(∑ p ∈ S with Q p, w p)‖ ≤ 4*M := by
  let T := S.filter (fun p => norm p = a ∨ norm p = b)
  let f := fun p => (if P p then w p else 0)-(if Q p then w p else 0)
  have he : (∑ p ∈ S, f p) = ∑ p ∈ T, f p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hn : norm p ≠ a ∧ norm p ≠ b := by
      simpa only [T,Finset.mem_filter,hp,true_and,not_or] using hnot
    have he := hPQ p hp hn.1 hn.2
    by_cases h : P p
    · simp [f,h,he.mp h]
    · have hq : ¬Q p := fun hq => h (he.mpr hq)
      simp [f,h,hq]
  have hf (p : Eisenstein) (hp : p ∈ T) : ‖f p‖ ≤ M := by
    have hpS := (Finset.mem_filter.mp hp).1
    by_cases hP : P p <;> by_cases hQ : Q p <;>
      simp [f,hP,hQ,hM,hw p hpS]
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_sub_distrib]
  change ‖∑ p ∈ S, f p‖ ≤ _
  rw [he]
  calc
    _ ≤ ∑ p ∈ T, ‖f p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ T, M := Finset.sum_le_sum hf
    _ = (T.card:ℝ)*M := by simp
    _ ≤ 4*M := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (primaryPrime_two_norm_card S hS a b)) hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GeometricPrimeIntervals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact norm intervals for the concrete bins used by the stopping
construction, including their bounded endpoint convention change. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem geometricPrimeBin_eq_iff {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j : ℕ} (hj : j < geometricBinCount ρ B) {p : Eisenstein}
    (hp : primaryPrime p) (hpB : norm p ≤ B) :
    geometricPrimeBin ρ B p = j ↔
      geometricBinLower ρ B j ≤ norm p ∧ norm p < ρ*geometricBinLower ρ B j := by
  constructor
  · intro he
    simpa only [he] using geometricPrimeBin_cell hρ hρ₂ hp hpB
  · intro hcell
    have hr : 0 < Real.log ρ := Real.log_pos hρ
    have hpn : 0 < norm p := by linarith [primaryPrime_norm_ge_two hp]
    have hn : 0 ≤ Real.log (norm p)/Real.log ρ :=
      div_nonneg (Real.log_nonneg (by linarith [primaryPrime_norm_ge_two hp])) hr.le
    have hlo : ((geometricBinCount ρ B-j:ℕ):ℝ) ≤ Real.log (norm p)/Real.log ρ := by
      apply (le_div_iff₀ hr).mpr
      exact (Real.pow_le_iff_le_log (zero_lt_one.trans hρ) hpn).mp hcell.1
    have hhi : Real.log (norm p)/Real.log ρ < ((geometricBinCount ρ B-j:ℕ):ℝ)+1 := by
      apply (div_lt_iff₀ hr).mpr
      have h : norm p < ρ^(geometricBinCount ρ B-j+1) := by
        simpa only [pow_succ',geometricBinLower] using hcell.2
      simpa only [Nat.cast_add,Nat.cast_one] using
        (Real.lt_pow_iff_log_lt hpn (zero_lt_one.trans hρ)).mp h
    have hf : ⌊Real.log (norm p)/Real.log ρ⌋₊ = geometricBinCount ρ B-j :=
      (Nat.floor_eq_iff hn).mpr ⟨hlo,hhi⟩
    unfold geometricPrimeBin
    rw [hf]
    omega

lemma geometricPrimeBin_away_endpoints {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j : ℕ} (hj : j < geometricBinCount ρ B) {p : Eisenstein}
    (hp : primaryPrime p) (hpB : norm p ≤ B)
    (hlo : norm p ≠ geometricBinLower ρ B j)
    (hhi : norm p ≠ ρ*geometricBinLower ρ B j) :
    (geometricPrimeBin ρ B p = j) ↔
      geometricBinLower ρ B j < norm p ∧ norm p ≤ ρ*geometricBinLower ρ B j := by
  rw [geometricPrimeBin_eq_iff hρ hρ₂ hj hp hpB]
  constructor
  · rintro ⟨hl,hu⟩
    exact ⟨lt_of_le_of_ne hl hlo.symm,hu.le⟩
  · rintro ⟨hl,hu⟩
    exact ⟨hl.le,lt_of_le_of_ne hu hhi⟩

/-- Replacing a half-open bin by the open-closed interval used by prime
partial summation changes only the two endpoint norms. -/
theorem geometricPrimeBin_endpoint_difference {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j : ℕ} (hj : j < geometricBinCount ρ B) (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p ∧ norm p ≤ B)
    (f : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ p ∈ S, ‖f p‖ ≤ M) :
    ‖(∑ p ∈ S with geometricPrimeBin ρ B p = j, f p)-
      (∑ p ∈ S with geometricBinLower ρ B j < norm p ∧
        norm p ≤ ρ*geometricBinLower ρ B j, f p)‖ ≤ 4*M := by
  convert prime_interval_endpoint_difference S (fun p hp => (hS p hp).1)
    (fun p => geometricPrimeBin ρ B p = j)
    (fun p => geometricBinLower ρ B j < norm p ∧ norm p ≤ ρ*geometricBinLower ρ B j)
    (geometricBinLower ρ B j) (ρ*geometricBinLower ρ B j)
    (fun p hp hlo hhi => geometricPrimeBin_away_endpoints hρ hρ₂ hj
      (hS p hp).1 (hS p hp).2 hlo hhi) f hM hf using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  all_goals
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_filter]
    · intro p hp
      rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeSelection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact selection of a largest prime, with a fixed injective tie code.
This is an unordered selection: inserting it into a finite sum introduces
no factor depending on the number of primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeTieCode_injective : Function.Injective primeTieCode := by
  intro p q h
  have hi : Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p =
      Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) q := Encodable.encode_injective h
  have hr := Function.rightInverse_invFun ofCoords_surjective
  calc
    p = ofCoords (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p).1
      (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p).2 := (hr p).symm
    _ = ofCoords (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) q).1
      (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) q).2 := by rw [hi]
    _ = q := hr q

lemma largestPrime_unique {code : Eisenstein → ℕ} (hc : Function.Injective code)
    {s : Finset Eisenstein} {p q : Eisenstein} (hp : p ∈ s) (hq : q ∈ s)
    (hpl : largestPrimePredicate code s p) (hql : largestPrimePredicate code s q) : p = q := by
  rcases hpl q hq with hlt | he
  · rcases hql p hp with hlt' | he'
    · omega
    · omega
  · rcases hql p hp with hlt' | he'
    · omega
    · exact hc (le_antisymm he'.2 he.2)

lemma selectedLargestPrime_spec (s : Finset Eisenstein) (hs : s.Nonempty) :
    selectedLargestPrime s hs ∈ s ∧
      largestPrimePredicate primeTieCode s (selectedLargestPrime s hs) :=
  Classical.choose_spec (exists_largestPrime primeTieCode s hs)

lemma selectedLargestPrime_norm (s : Finset Eisenstein) (hs : s.Nonempty) :
    normNat (selectedLargestPrime s hs) = s.sup normNat := by
  have hp := selectedLargestPrime_spec s hs
  apply le_antisymm (Finset.le_sup (f := normNat) hp.1)
  apply Finset.sup_le
  intro q hq
  rcases hp.2 q hq with hlt | he
  · exact hlt.le
  · exact he.1.le

lemma selectedLargestPrime_product_split (s : Finset Eisenstein) (hs : s.Nonempty) :
    selectedLargestPrime s hs*(∏ q ∈ s.erase (selectedLargestPrime s hs), q) =
      ∏ q ∈ s, q := by
  simpa only [mul_comm] using Finset.prod_erase_mul s (fun q => q)
    (selectedLargestPrime_spec s hs).1

/-- The actual largest prime of a squarefree primary element can be
removed once, leaving a primary squarefree factor coprime to it. -/
theorem primary_largest_prime_split {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) (hne : (primaryPrimeFactors n).Nonempty) :
    ∃ p c : Eisenstein, primaryPrime p ∧ primary c ∧ Squarefree c ∧
      ¬p ∣ c ∧ p*c = n ∧
      largestPrimePredicate primeTieCode (primaryPrimeFactors c) p ∧
      normNat p = (primaryPrimeFactors n).sup normNat := by
  let p := selectedLargestPrime (primaryPrimeFactors n) hne
  let U := (primaryPrimeFactors n).erase p
  let c := ∏ q ∈ U, q
  have hp := selectedLargestPrime_spec (primaryPrimeFactors n) hne
  have hpP : primaryPrime p := (primaryPrimeFactor_spec hn hp.1).1
  have hU (q : Eisenstein) (hq : q ∈ U) : primaryPrime q :=
    (primaryPrimeFactor_spec hn (Finset.mem_of_mem_erase hq)).1
  have hc : primary c := primary_finset_prod U (fun q => q) (fun q hq => (hU q hq).1)
  have hf : primaryPrimeFactors c = U := primaryPrimeFactors_finset_prod U hU
  have hpc : ¬p ∣ c := by
    intro hd
    have hm := (primaryPrime_mem_factors_iff hc).mpr ⟨hpP,hd⟩
    rw [hf] at hm
    exact (Finset.mem_erase.mp hm).1 rfl
  refine ⟨p,c,hpP,hc,primaryPrime_product_squarefree U hU,hpc,?_,?_,?_⟩
  · exact (selectedLargestPrime_product_split (primaryPrimeFactors n) hne).trans
      (primaryPrimeFactors_prod hn hs)
  · rw [hf]
    exact fun q hq => hp.2 q (Finset.mem_of_mem_erase hq)
  · exact selectedLargestPrime_norm (primaryPrimeFactors n) hne

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeWeightVariation
attribute [-instance] _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedKummerPrime
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite cubic prime input including the ramified part.

Thorner–Zaman, Algebra & Number Theory 13 (2019), Theorem 1.4, specialized
to the Kummer extension Q(ω, ∛v)/Q(ω). For v not a cube this is cyclic of
order three; weighting its three Frobenius classes by the cubic character
cancels the principal and possible real exceptional terms. The conductor
divides the modulus 9v supplied by cubic reciprocity (Dunn–Radziwiłł 2024,
§2, supplementary laws). Thus Nv bounded by a fixed log power suffices.
This is the same published finite-order prime input as PublishedHecke,
with units and primes above three retained, not a Gauss-sum conclusion.
Smooth weights, exclusions and convolution estimates are derived below.
-/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory
namespace CubicFirstMoment

theorem weighted_kummer_prime_bound (hSW : KummerPrimeSiegelWalfisz)
    (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ a b : ℝ, X₀ ≤ a → a ≤ b →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log a)^A → ∀ f : ℝ → ℂ,
      (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) →
      IntegrableOn (deriv f) (Set.Icc a b) →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p)*cubicSymbol p v‖ ≤
        (C*b/(Real.log a)^D)*(‖f a‖+‖f b‖+∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  obtain ⟨C,X₀,hC,hX₀,hbound⟩ := hSW A D hA hD
  refine ⟨C,X₀,hC,hX₀,?_⟩
  intro a b ha hab v hv hn hcon f hdiff hderiv
  have ha1 : 1 < a := hX₀.trans_le ha
  have ha0 : 0 < a := zero_lt_one.trans ha1
  apply weighted_prime_bound (fun p => cubicSymbol p v) f ha0.le hab hdiff hderiv
  intro t ht
  have hat := Real.log_le_log ha0 ht.1
  have ht0 : 0 < t := ha0.trans_le ht.1
  have hc : norm v ≤ (Real.log t)^A := hcon.trans
    (Real.rpow_le_rpow (Real.log_pos ha1).le hat hA.le)
  apply (hbound t (ha.trans ht.1) v hv hn hc).trans
  exact div_le_div₀ (mul_nonneg hC.le (ht0.le.trans ht.2))
    (mul_le_mul_of_nonneg_left ht.2 hC.le)
    (Real.rpow_pos_of_pos (Real.log_pos ha1) D)
    (Real.rpow_le_rpow (Real.log_pos ha1).le hat hD.le)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeSW
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime cancellation on the long-prime range used to prove the
stopped sequence condition. The scale T can be log X while the prime
scale is only exp(sqrt(log X)); no positive power of X is required. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

/-- The precise raw Kummer prime input, followed by partial summation,
gives arbitrary T-power saving on every interval above a prime scale P
as soon as T <= (log P)^2. Smooth weights retain their actual variation. -/
theorem long_prime_interval_bound (hSW : KummerPrimeSiegelWalfisz)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C P₀ : ℝ, 0 < C ∧ 1 < P₀ ∧ ∀ (T P R a b : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 → P ≤ a → a ≤ b → b ≤ R*P →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A →
      ∀ f : ℝ → ℂ, (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) →
      IntegrableOn (deriv f) (Set.Icc a b) →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p)*cubicSymbol p v‖ ≤
        (C*(R*P)/T^D)*(‖f a‖+‖f b‖+∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := weighted_kummer_prime_bound hSW
    (2*A) (2*D) (by positivity) (by positivity)
  refine ⟨C,P₀,hC,hP₀,?_⟩
  intro T P R a b hT hP hTP hPa hab hb v hv hnc hcon f hdiff hint
  have hP1 : 1 < P := hP₀.trans_le hP
  have hP0 : 0 < P := zero_lt_one.trans hP1
  have ha0 : 0 < a := hP0.trans_le hPa
  have hb0 : 0 < b := ha0.trans_le hab
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have hloga : Real.log P ≤ Real.log a := Real.log_le_log hP0 hPa
  have hsquare (E : ℝ) : ((Real.log P)^2)^E = (Real.log P)^(2*E) := by
    simpa only [Nat.cast_ofNat] using (Real.rpow_natCast_mul hlogP.le 2 E).symm
  have hcon' : norm v ≤ (Real.log a)^(2*A) := by
    calc
      _ ≤ T^A := hcon
      _ ≤ ((Real.log P)^2)^A := Real.rpow_le_rpow hT0.le hTP hA.le
      _ = (Real.log P)^(2*A) := hsquare A
      _ ≤ (Real.log a)^(2*A) := Real.rpow_le_rpow hlogP.le hloga (by positivity)
  have hden : T^D ≤ (Real.log a)^(2*D) := by
    calc
      _ ≤ ((Real.log P)^2)^D := Real.rpow_le_rpow hT0.le hTP hD.le
      _ = (Real.log P)^(2*D) := hsquare D
      _ ≤ (Real.log a)^(2*D) := Real.rpow_le_rpow hlogP.le hloga (by positivity)
  have hfrac : C*b/(Real.log a)^(2*D) ≤ C*(R*P)/T^D :=
    div_le_div₀ (mul_nonneg hC.le (hb0.le.trans hb)) (mul_le_mul_of_nonneg_left hb hC.le)
      (Real.rpow_pos_of_pos hT0 D) hden
  apply (hbound a b (hP.trans hPa) hab v hv hnc hcon' f hdiff hint).trans
  apply mul_le_mul_of_nonneg_right hfrac
  exact add_nonneg (add_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))
    (integral_nonneg (fun _ => _root_.norm_nonneg _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCutoffDerivative
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete detector has a uniformly bounded radial derivative.
This supplies the actual variation cost when one prime is left free in
the stopped coefficient; it is not a sequence-cancellation assumption. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma primeDetectorCutoff_deriv_zero {x : ℝ} (hx : x ∉ Icc (1:ℝ) 2) :
    deriv primeDetectorCutoff x = 0 := by
  by_cases hlo : x < 1
  · have he : EqOn primeDetectorCutoff (fun _ : ℝ => (1:ℝ)) (Iio 1) :=
      fun y hy => primeDetectorCutoff_one hy.le
    simpa only [deriv_const] using he.deriv isOpen_Iio hlo
  · have hhi : 2 < x := by
      have h := not_and_or.mp hx
      rcases h with h | h
      · exact False.elim (h (le_of_not_gt hlo))
      · exact lt_of_not_ge h
    have he : EqOn primeDetectorCutoff (fun _ : ℝ => (0:ℝ)) (Ioi 2) :=
      fun y hy => primeDetectorCutoff_zero hy.le
    simpa only [deriv_const] using he.deriv isOpen_Ioi hhi

theorem primeDetectorCutoff_radial_deriv_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ D := by
  have hd : Continuous (deriv primeDetectorCutoff) :=
    primeDetectorCutoff_smooth.continuous_deriv (by norm_num)
  obtain ⟨D,hD⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    ((hd.norm.mul continuous_id).continuousOn)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x hx
  by_cases hmem : x ∈ Icc (1:ℝ) 2
  · have h := hD x hmem
    change ‖‖deriv primeDetectorCutoff x‖*x‖ ≤ D at h
    have hn : 0 ≤ ‖deriv primeDetectorCutoff x‖*x := mul_nonneg (_root_.norm_nonneg _) hx.le
    rw [Real.norm_eq_abs,abs_of_nonneg hn] at h
    simpa only [Real.norm_eq_abs] using h.trans (le_max_left D 0)
  · rw [primeDetectorCutoff_deriv_zero hmem,abs_zero,zero_mul]
    exact le_max_right _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cutoff weights on a free long prime. Their variation depends
on its dyadic ratio and Mellin height, not on the cutoff scales. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma radial_mellin_interval_variation {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    {P R a b M D : ℝ} (hP : 0 < P) (_hR : 1 ≤ R) (ha : P ≤ a)
    (hab : a ≤ b) (hb : b ≤ R*P) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hwm : ∀ x, ‖w x‖ ≤ M) (hwd : ∀ x, 0 < x → ‖deriv w x‖*x ≤ D) (u : ℝ) :
    let f := fun t => w t*mellinPhase u t
    (∀ t ∈ Icc a b, DifferentiableAt ℝ f t) ∧
    IntegrableOn (deriv f) (Icc a b) ∧
    ‖f a‖+‖f b‖+(∫ t in Ioc a b, ‖deriv f t‖) ≤
      2*M+(R-1)*(D+M*|u|) := by
  dsimp only
  have hsub : Icc a b ⊆ Ioi (0:ℝ) := fun _ ht => hP.trans_le (ha.trans ht.1)
  have hs : ContDiffOn ℝ ∞ (fun t => w t*mellinPhase u t) (Ioi 0) := by
    simpa only [div_one] using contDiffOn_rescaled_mellin hw 1 u
  have hd : ContinuousOn (deriv (fun t => w t*mellinPhase u t)) (Icc a b) :=
    (hs.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  refine ⟨?_,hd.integrableOn_Icc,?_⟩
  · intro t ht
    exact ((hs t (hsub ht)).contDiffAt (isOpen_Ioi.mem_nhds (hsub ht))).differentiableAt
      (by norm_num)
  have hpoint (t : ℝ) (ht : t ∈ uIoc a b) :
      ‖‖deriv (fun t => w t*mellinPhase u t) t‖‖ ≤ (D+M*|u|)/P := by
    rw [uIoc_of_le hab] at ht
    have htP : P ≤ t := ha.trans ht.1.le
    have ht0 : 0 < t := hP.trans_le htP
    rw [Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]
    have hder := norm_deriv_weighted_mellinPhase
      ((hw.differentiable (by norm_num)).differentiableAt.hasDerivAt) u ht0
    have hdw : ‖deriv w t‖ ≤ D/t := (le_div_iff₀ ht0).mpr (hwd t ht0)
    calc
      _ ≤ D/t+M*(|u|/t) := hder.trans (add_le_add hdw
        (mul_le_mul_of_nonneg_right (hwm t) (div_nonneg (abs_nonneg _) ht0.le)))
      _ = (D+M*|u|)/t := by ring
      _ ≤ (D+M*|u|)/P := div_le_div_of_nonneg_left
        (add_nonneg hD (mul_nonneg hM (abs_nonneg _))) hP htP
  have hint : (∫ t in Ioc a b, ‖deriv (fun t => w t*mellinPhase u t) t‖) ≤
      (R-1)*(D+M*|u|) := by
    rw [←intervalIntegral.integral_of_le hab]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    have hn : 0 ≤ ∫ t in a..b, ‖deriv (fun t => w t*mellinPhase u t) t‖ :=
      intervalIntegral.integral_nonneg_of_forall hab (fun _ => _root_.norm_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_nonneg (sub_nonneg.mpr hab)] at hi
    apply hi.trans
    calc
      (D+M*|u|)/P*(b-a) ≤ (D+M*|u|)/P*((R-1)*P) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (div_nonneg
          (add_nonneg hD (mul_nonneg hM (abs_nonneg _))) hP.le)
      _ = (R-1)*(D+M*|u|) := by field_simp
  have hnorm (x : ℝ) : ‖w x*mellinPhase u x‖ ≤ M := by
    simpa only [norm_mul,mellinPhase_norm,mul_one] using hwm x
  linarith [hnorm a,hnorm b]

lemma primeDetectorCutoff_rescaled_smooth (c : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => (primeDetectorCutoff (t/c):ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (primeDetectorCutoff_smooth.comp (contDiff_id.div_const c))

lemma primeDetectorCutoff_rescaled_norm (c t : ℝ) :
    ‖(primeDetectorCutoff (t/c):ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (primeDetectorCutoff_nonneg _)]
  exact primeDetectorCutoff_le_one _

lemma primeDetectorCutoff_rescaled_deriv {D : ℝ}
    (hD : ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ D)
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    ‖deriv (fun x : ℝ => (primeDetectorCutoff (x/c):ℂ)) t‖*t ≤ D := by
  have hd := (((primeDetectorCutoff_smooth.differentiable (by norm_num)).differentiableAt
    (x := t/c)).hasDerivAt.comp t ((hasDerivAt_id t).div_const c)).ofReal_comp
  change HasDerivAt (fun x : ℝ => (primeDetectorCutoff (x/c):ℂ))
    ((deriv primeDetectorCutoff (t/c)*(1/c):ℝ):ℂ) t at hd
  rw [hd.deriv,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_pos (div_pos zero_lt_one hc)]
  convert hD (t/c) (div_pos ht hc) using 1 <;> first | rfl | ring

/-- The same constant works for every cutoff scale. This is the actual
selected-bin prime weight, including any permitted norm twist. -/
theorem long_prime_cutoff_variation :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (c P R a b u : ℝ), 0 < c → 0 < P → 1 ≤ R →
      P ≤ a → a ≤ b → b ≤ R*P →
      let f := fun t => (primeDetectorCutoff (t/c):ℂ)*mellinPhase u t
      (∀ t ∈ Icc a b, DifferentiableAt ℝ f t) ∧
      IntegrableOn (deriv f) (Icc a b) ∧
      ‖f a‖+‖f b‖+(∫ t in Ioc a b, ‖deriv f t‖) ≤ 2+(R-1)*(D+|u|) := by
  obtain ⟨D,hD,hder⟩ := primeDetectorCutoff_radial_deriv_bound
  refine ⟨D,hD,?_⟩
  intro c P R a b u hc hP hR ha hab hb
  simpa only [mul_one,one_mul] using radial_mellin_interval_variation
    (primeDetectorCutoff_rescaled_smooth c) hP hR ha hab hb zero_le_one hD
    (primeDetectorCutoff_rescaled_norm c) (fun t ht => primeDetectorCutoff_rescaled_deriv
      hder hc ht) u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeExclusionLog
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic, rather than merely subpower, number of prime
exclusions. This is necessary when the free prime is exp(sqrt(log X)). -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primary_prime_divisor_card_log (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (e : Eisenstein) (he : e ≠ 0) :
    ((S.filter (fun p => p ∣ e)).card:ℝ) ≤ Real.log (norm e)/Real.log 2 := by
  let T := S.filter (fun p => p ∣ e)
  have hp (p : Eisenstein) (hp : p ∈ T) : primaryPrime p :=
    hS p (Finset.mem_filter.mp hp).1
  have hd : (∏ p ∈ T, p) ∣ e := by
    apply Finset.prod_dvd_of_coprime
    · intro p hpT q hqT hpq
      exact primaryPrimes_isCoprime (hp p hpT) (hp q hqT) hpq
    · intro p hpT
      exact (Finset.mem_filter.mp hpT).2
  have hprod : (2:ℝ)^T.card ≤ norm e := by
    calc
      _ = ∏ _p ∈ T, (2:ℝ) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ T, norm p := Finset.prod_le_prod (fun _ _ => by norm_num)
        (fun p hpT => primaryPrime_norm_ge_two (hp p hpT))
      _ = norm (∏ p ∈ T, p) := (norm_finset_prod _ _).symm
      _ ≤ norm e := norm_le_of_dvd_nonzero he hd
  have hn : 0 < norm e := zero_lt_one.trans_le (one_le_norm he)
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr
  exact (Real.pow_le_iff_le_log (by norm_num : (0:ℝ) < 2) hn).mp hprod

theorem prime_exclusion_logarithmic (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (e : Eisenstein) (he : e ≠ 0)
    (w : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ p ∈ S, ‖w p‖ ≤ M) :
    ‖(∑ p ∈ S, w p)-(∑ p ∈ S with IsCoprime p e, w p)‖ ≤
      M*(Real.log (norm e)/Real.log 2) := by
  have hsub : S.filter (fun p => ¬IsCoprime p e) ⊆ S.filter (fun p => p ∣ e) := by
    intro p hp
    obtain ⟨hpS,hp⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hpS,?_⟩
    by_contra hn
    exact hp ((hS p hpS).2.irreducible.coprime_iff_not_dvd.mpr hn)
  exact (prime_exclusion_difference S e w hw).trans
    (mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (primary_prime_divisor_card_log S hS e he)) hM)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete free selected-bin prime satisfies the needed prime
cancellation, uniformly in its cutoff scale and interval endpoints. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_prime_cutoff_bound (hSW : KummerPrimeSiegelWalfisz)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C P₀ : ℝ, 0 < C ∧ 1 < P₀ ∧ ∀ (T P a b c u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < c →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p),
        (primeDetectorCutoff (norm p/c):ℂ)*mellinPhase u (norm p)*cubicSymbol p v‖ ≤
        C*P/T^D*(1+|u|) := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := long_prime_interval_bound hSW hA hD
  obtain ⟨V,hV,hvar⟩ := long_prime_cutoff_variation
  refine ⟨2*C*(V+2),P₀,by positivity,hP₀,?_⟩
  intro T P a b c u hT hP hTP ha hab hb hc v hv hnc hNv
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le hP)
  obtain ⟨hdiff,hint,hvariation⟩ := hvar c P 2 a b u hc hP0 (by norm_num) ha hab hb
  have hVbound : 2+(2-1)*(V+|u|) ≤ (V+2)*(1+|u|) := by
    nlinarith [abs_nonneg u,mul_nonneg hV (abs_nonneg u)]
  have hf : 0 ≤ C*(2*P)/T^D := by positivity
  calc
    _ ≤ (C*(2*P)/T^D)*(2+(2-1)*(V+|u|)) :=
      (hbound T P 2 a b hT hP hTP ha hab hb v hv hnc hNv _ hdiff hint).trans
        (mul_le_mul_of_nonneg_left hvariation hf)
    _ ≤ (C*(2*P)/T^D)*((V+2)*(1+|u|)) := mul_le_mul_of_nonneg_left hVbound hf
    _ = _ := by ring

/-- The exact logarithmic deletion error is retained, so this theorem
also applies to the polynomial-norm exclusions in the stopped sequence. -/
theorem long_prime_cutoff_excluded_bound (hSW : KummerPrimeSiegelWalfisz)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C P₀ : ℝ, 0 < C ∧ 1 < P₀ ∧ ∀ (T P a b c u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < c →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter (fun p => IsCoprime p e),
        (primeDetectorCutoff (norm p/c):ℂ)*mellinPhase u (norm p)*cubicSymbol p v‖ ≤
        C*P/T^D*(1+|u|)+Real.log (norm e)/Real.log 2 := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := long_prime_cutoff_bound hSW hA hD
  refine ⟨C,P₀,hC,hP₀,?_⟩
  intro T P a b c u hT hP hTP ha hab hb hc v e hv hnc hNv he
  let S := (primeCutoff b).filter (fun p => a < norm p)
  let f := fun p : Eisenstein =>
    (primeDetectorCutoff (norm p/c):ℂ)*mellinPhase u (norm p)*cubicSymbol p v
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
  have hweight (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ 1 := by
    dsimp [f]
    rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
    exact (mul_le_mul (primeDetectorCutoff_rescaled_norm c (norm p))
      (norm_cubicSymbol_le_one (hS p hp).1 v) (_root_.norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  have herr := prime_exclusion_logarithmic S hS e he f zero_le_one hweight
  have hnorm : ‖∑ p ∈ S with IsCoprime p e, f p‖ ≤
      ‖∑ p ∈ S, f p‖+‖(∑ p ∈ S, f p)-(∑ p ∈ S with IsCoprime p e, f p)‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le (∑ p ∈ S, f p)
      ((∑ p ∈ S, f p)-(∑ p ∈ S with IsCoprime p e, f p))
  exact hnorm.trans (add_le_add (hbound T P a b c u hT hP hTP ha hab hb hc v hv hnc hNv)
    (by simpa only [one_mul] using herr))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free selected-bin prime in the literal cutoff-Mobius coefficient.
All other factors remain fixed, including the coprimality exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_prime_moebius_bound (hSW : KummerPrimeSiegelWalfisz)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w →
      ∀ c v e : Eisenstein, primary c → Squarefree c → v ≠ 0 →
        (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p (c*e)),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*cubicSymbol (p*c) v‖ ≤
        K*P/T^D*(1+|u|)+Real.log (norm (c*e))/Real.log 2 := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_prime_cutoff_excluded_bound hSW hA hD
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T P a b w u hT hP hTP ha hab hb hw c v e hc hs hv hnc hNv he
  let S := ((primeCutoff b).filter (fun p => a < norm p)).filter
    (fun p => IsCoprime p (c*e))
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hfilter : S.filter (fun p => ¬p ∣ c) = S := by
    apply Finset.filter_true_of_mem
    intro p hp hd
    have hpe := (Finset.mem_filter.mp hp).2
    have hpc : IsCoprime p c := hpe.of_isCoprime_of_dvd_right (dvd_mul_right c e)
    exact (hS p hp).2.not_isUnit (hpc.isUnit_of_dvd hd)
  have hid := cutoffMoebius_free_prime_identity S hS primeDetectorCutoff w u hc hs v
  rw [hfilter] at hid
  have hpref := cutoffMoebius_free_prime_prefactor_bound
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) w u hc v
  change ‖∑ p ∈ S, _‖ ≤ _
  rw [hid,norm_mul]
  apply (mul_le_of_le_one_left (_root_.norm_nonneg _) hpref).trans
  simpa only [normTwist_eq_mellinPhase] using
    hbound T P a b w u hT hP hTP ha hab hb hw v (c*e) hv hnc hNv
      (mul_ne_zero (primary_ne_zero hc) he)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimePowers
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial losses in log X are negligible on the actual long-prime
scale exp(sqrt(log X)). This includes logarithmic prime exclusions. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

theorem long_prime_power_absorption {C D E : ℝ} (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∀ᶠ P : ℝ in atTop, ∀ T : ℝ, 1 ≤ T → T ≤ (Real.log P)^2 →
      C*T^E ≤ P/T^D := by
  have hs := ((isLittleO_log_rpow_rpow_atTop (2*(D+E))
    (by norm_num : (0:ℝ) < 1)).const_mul_left C).def zero_lt_one
  filter_upwards [hs,eventually_gt_atTop (1:ℝ)] with P hsmall hP T hT hTP
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hl : 0 < Real.log P := Real.log_pos hP
  have hbound : C*(Real.log P)^(2*(D+E)) ≤ P := by
    simpa only [Real.rpow_one,one_mul,Real.norm_of_nonneg (mul_nonneg hC
      (Real.rpow_nonneg hl.le _)),Real.norm_of_nonneg hP0.le] using hsmall
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hT0 D)).mpr
  calc
    C*T^E*T^D = C*T^(D+E) := by rw [Real.rpow_add hT0]; ring
    _ ≤ C*((Real.log P)^2)^(D+E) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hT0.le hTP (add_nonneg hD hE)) hC
    _ = C*(Real.log P)^(2*(D+E)) := by
      rw [←Real.rpow_natCast_mul hl.le 2 (D+E)]
      norm_num
    _ ≤ P := hbound

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every fixed power saving for the literal free prime, with the
polynomial norm-twist and excluded-prime costs already absorbed. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_prime_moebius_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → |u| ≤ T^H →
      ∀ c v e : Eisenstein, primary c → Squarefree c → v ≠ 0 →
        (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*e)) ≤ T^E →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p (c*e)),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*cubicSymbol (p*c) v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_prime_moebius_bound hSW hA (add_pos_of_pos_of_nonneg hD hH)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := (Real.log 2)⁻¹) (D := D) (E := E)
      (inv_nonneg.mpr hlog2.le) hD.le hE)
  refine ⟨2*K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P a b w u hT hP hTP ha hab hb hw hu c v e hc hs hv hnc hNv he hNe
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  have hTH : 1 ≤ T^H := Real.one_le_rpow hT hH
  have hheight : 1+|u| ≤ 2*T^H := by linarith
  have hmain : K*P/T^(D+H)*(1+|u|) ≤ 2*K*P/T^D := by
    calc
      _ ≤ K*P/T^(D+H)*(2*T^H) :=
        mul_le_mul_of_nonneg_left hheight (by positivity)
      _ = 2*K*P/T^D := by
        rw [Real.rpow_add hT0]
        field_simp
  have herror : Real.log (norm (c*e))/Real.log 2 ≤ P/T^D := by
    calc
      _ ≤ T^E/Real.log 2 := (div_le_div_iff_of_pos_right hlog2).mpr hNe
      _ = (Real.log 2)⁻¹*T^E := by ring
      _ ≤ P/T^D := hP₁ P ((le_max_right _ _).trans hP) T hT hTP
  apply (hbound T P a b w u hT ((le_max_left _ _).trans hP) hTP ha hab hb hw
    c v e hc hs hv hnc hNv he).trans
  calc
    _ ≤ 2*K*P/T^D+P/T^D := add_le_add hmain herror
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeCancellation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual largest-prime restriction costs only the two equal-norm
endpoints. The cancellation is still the published prime input, not a
sequence-condition hypothesis. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrime_endpoint_difference (code : Eisenstein → ℕ)
    (C S : Finset Eisenstein) (hS : ∀ p ∈ S, primaryPrime p)
    (f : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ p ∈ S, ‖f p‖ ≤ M) :
    ‖(∑ p ∈ S with largestPrimePredicate code C p, f p)-
      (∑ p ∈ S with ((C.sup normNat:ℕ):ℝ) < norm p, f p)‖ ≤ 4*M := by
  apply prime_interval_endpoint_difference S hS _ _
    ((C.sup normNat:ℕ):ℝ) ((C.sup normNat:ℕ):ℝ) _ f hM hf
  intro p hp hn _
  have hne : normNat p ≠ C.sup normNat := by
    intro h
    apply hn
    rw [←normNat_cast p,h]
  simpa only [←normNat_cast p,Nat.cast_lt] using
    largestPrimePredicate_away_tie code C p hne

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeContext
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Largest-prime cancellation with the full fixed complementary prime
set. The selected-bin role compares against the primes of both other
factors, rather than just those of its own Möbius complement. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_prime_context_moebius_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → |u| ≤ T^H →
      ∀ (c v e : Eisenstein) (C : Finset Eisenstein), primary c → Squarefree c → v ≠ 0 →
        (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*e)) ≤ T^E →
      ‖∑ p ∈ (((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p (c*e))).filter
          (fun p => largestPrimePredicate primeTieCode C p),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*cubicSymbol (p*c) v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_prime_moebius_saving hSW hA hD hH hE
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := 4) (D := D) (E := 0)
      (by norm_num) hD.le (by norm_num))
  refine ⟨K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P a b w u hT hP hTP ha hab hb hw hu c v e C hc hs hv hnc hNv he hNe
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  let S := ((primeCutoff b).filter (fun p => a < norm p)).filter
    (fun p => IsCoprime p (c*e))
  let f := fun p : Eisenstein => cutoffMoebius primeDetectorCutoff w (p*c)*
    normTwist u (p*c)*cubicSymbol (p*c) v
  let m : ℝ := ((C.sup normNat:ℕ):ℝ)
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ 1 := by
    dsimp [f]
    rw [norm_mul,norm_mul,norm_normTwist,mul_one]
    exact (mul_le_mul (cutoffMoebius_norm_le_one
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) w (p*c))
      (norm_cubicSymbol_le_one (primary_mul (hS p hp).1 hc) v)
      (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hend := largestPrime_endpoint_difference primeTieCode C S hS
    f zero_le_one hf
  have hinterval :
      (∑ p ∈ S with m < norm p, f p) =
      ∑ p ∈ ((primeCutoff b).filter (fun p => max a m < norm p)).filter
        (fun p => IsCoprime p (c*e)), f p := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [S,Finset.mem_filter,max_lt_iff]
    tauto
  have hsum : ‖∑ p ∈ S with m < norm p, f p‖ ≤ K*P/T^D := by
    rw [hinterval]
    by_cases hm : max a m ≤ b
    · exact hbound T P (max a m) b w u hT ((le_max_left _ _).trans hP) hTP
        (ha.trans (le_max_left _ _)) hm hb hw hu c v e hc hs hv hnc hNv he hNe
    · have hempty : ((primeCutoff b).filter (fun p => max a m < norm p)).filter
          (fun p => IsCoprime p (c*e)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hp,_⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp,hl⟩ := Finset.mem_filter.mp hp
        exact hm (hl.le.trans (mem_primeCutoff.mp hp).2)
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have hfour : (4:ℝ) ≤ P/T^D := by
    simpa only [Real.rpow_zero,mul_one] using
      hP₁ P ((le_max_right _ _).trans hP) T hT hTP
  change ‖∑ p ∈ S with largestPrimePredicate primeTieCode C p, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S with m < norm p, f p‖+
        ‖(∑ p ∈ S with largestPrimePredicate primeTieCode C p, f p)-
          (∑ p ∈ S with m < norm p, f p)‖ := by
      exact norm_le_norm_add_norm_sub' _ _
    _ ≤ K*P/T^D+4 := add_le_add hsum (by simpa only [mul_one] using hend)
    _ ≤ K*P/T^D+P/T^D := add_le_add le_rfl hfour
    _ = _ := by ring


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeBox
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual geometric selected-prime bin inherits the published prime
saving. Its endpoint convention and largest-prime tie rule are retained. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_prime_geometric_interval_moebius_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ w u a b : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → |u| ≤ T^H →
      ∀ (c v e : Eisenstein) (C : Finset Eisenstein), primary c → Squarefree c → v ≠ 0 →
        (¬∃ k : Eisenstein, k^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*e)) ≤ T^E →
      ‖∑ p ∈ (((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
          (fun p => largestPrimePredicate primeTieCode C p ∧ geometricPrimeBin ρ B p = j),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*cubicSymbol (p*c) v‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_prime_context_moebius_saving hSW hA hD hH hE
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := 4) (D := D) (E := 0)
      (by norm_num) hD.le (by norm_num))
  refine ⟨K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T B ρ w u a b j hT hρ hρ₂ hj hP hTP hw hu c v e C hc hs hv hnc hNv he hNe
  let P := geometricBinLower ρ B j
  have hP0 : 0 < P := zero_lt_one.trans
    (hP₀.trans_le ((le_max_left _ _).trans hP))
  let S := (((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
    (fun p => largestPrimePredicate primeTieCode C p)
  let f := fun p : Eisenstein => cutoffMoebius primeDetectorCutoff w (p*c)*
    normTwist u (p*c)*cubicSymbol (p*c) v
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p ∧ norm p ≤ B :=
    mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ 1 := by
    dsimp [f]
    rw [norm_mul,norm_mul,norm_normTwist,mul_one]
    exact (mul_le_mul (cutoffMoebius_norm_le_one
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) w (p*c))
      (norm_cubicSymbol_le_one (primary_mul (hS p hp).1.1 hc) v)
      (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hend := geometricPrimeBin_endpoint_difference hρ hρ₂ hj S hS f zero_le_one hf
  have hinterval : (∑ p ∈ S with P < norm p ∧ norm p ≤ ρ*P, f p) =
      ∑ p ∈ (((primeCutoff (min (min B b) (ρ*P))).filter (fun p => max a P < norm p)).filter
        (fun p => IsCoprime p (c*e))).filter
        (fun p => largestPrimePredicate primeTieCode C p), f p := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [S,Finset.mem_filter,mem_primeCutoff,le_min_iff,max_lt_iff]
    tauto
  have hsum : ‖∑ p ∈ S with P < norm p ∧ norm p ≤ ρ*P, f p‖ ≤ K*P/T^D := by
    rw [hinterval]
    by_cases hm : max a P ≤ min (min B b) (ρ*P)
    · exact hbound T P (max a P) (min (min B b) (ρ*P)) w u hT ((le_max_left _ _).trans hP)
        hTP (le_max_right _ _) hm ((min_le_right _ _).trans (mul_le_mul_of_nonneg_right hρ₂ hP0.le))
        hw hu c v e C hc hs hv hnc hNv he hNe
    · have hempty : (((primeCutoff (min (min B b) (ρ*P))).filter (fun p => max a P < norm p)).filter
          (fun p => IsCoprime p (c*e))).filter
          (fun p => largestPrimePredicate primeTieCode C p) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        have hpc := Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        exact hm (hpc.2.le.trans (mem_primeCutoff.mp hpc.1).2)
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have hfour : (4:ℝ) ≤ P/T^D := by
    simpa only [Real.rpow_zero,mul_one] using
      hP₁ P ((le_max_right _ _).trans hP) T hT hTP
  have hset : (((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
      (fun p => largestPrimePredicate primeTieCode C p ∧ geometricPrimeBin ρ B p = j) =
      S.filter (fun p => geometricPrimeBin ρ B p = j) := by
    ext p
    simp only [S,Finset.mem_filter]
    tauto
  rw [hset]
  change ‖∑ p ∈ S with geometricPrimeBin ρ B p = j, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S with P < norm p ∧ norm p ≤ ρ*P, f p‖+
        ‖(∑ p ∈ S with geometricPrimeBin ρ B p = j, f p)-
          (∑ p ∈ S with P < norm p ∧ norm p ≤ ρ*P, f p)‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ K*P/T^D+4 := add_le_add hsum (by simpa only [mul_one] using hend)
    _ ≤ K*P/T^D+P/T^D := add_le_add le_rfl hfour
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimeBox
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cancellation of the actual free selected-bin prime with the complete
two-stage stopping predicate. Only the cited Kummer prime input is used;
the stopping restriction is removed by proved bin invariance. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_stopped_selected_interval_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ w u a b : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → |u| ≤ T^H →
      ∀ (c v e : Eisenstein) (C : Finset Eisenstein), primary c → Squarefree c → v ≠ 0 →
        (¬∃ k : Eisenstein, k^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*e)) ≤ T^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool) (r : Eisenstein),
      ‖∑ p ∈ ((((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
          (fun p => largestPrimePredicate primeTieCode C p ∧ geometricPrimeBin ρ B p = j)).filter
          (fun p => stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
            j₀ k h Z Q early r (p*c)),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*cubicSymbol (p*c) v‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_prime_geometric_interval_moebius_saving hSW hA hD hH hE
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ w u a b j hT hρ hρ₂ hj hP hTP hw hu c v e C hc hs hv hnc hNv he hNe
    j₀ k h Z Q early r
  let S := (((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
    (fun p => largestPrimePredicate primeTieCode C p ∧ geometricPrimeBin ρ B p = j)
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1).1
  have hcop (p : Eisenstein) (hp : p ∈ S) : ¬p ∣ c := by
    have hpe := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hpc : IsCoprime p c := hpe.of_isCoprime_of_dvd_right (dvd_mul_right c e)
    exact fun hd => (hS p hp).2.not_isUnit (hpc.isUnit_of_dvd hd)
  have hfull : ‖∑ p ∈ S, cutoffMoebius primeDetectorCutoff w (p*c)*
      normTwist u (p*c)*cubicSymbol (p*c) v‖ ≤ K*geometricBinLower ρ B j/T^D :=
    hbound T B ρ w u a b j hT hρ hρ₂ hj hP hTP hw hu c v e C hc hs hv hnc hNv he hNe
  change ‖∑ p ∈ S with stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
    j₀ k h Z Q early r (p*c), _‖ ≤ _
  by_cases hne : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hne
    have hbin (p : Eisenstein) (hp : p ∈ S) : geometricPrimeBin ρ B p = geometricPrimeBin ρ B p₀ :=
      (Finset.mem_filter.mp hp).2.2.trans (Finset.mem_filter.mp hp₀).2.2.symm
    rw [sum_stoppedSide_same_bin S (geometricPrimeBin ρ B) (geometricBinLower ρ B)
      j₀ k h Z Q early r hc hs hp₀ hS hcop hbin]
    split_ifs
    · exact hfull
    · rw [norm_zero]
      have hP0 : 0 < geometricBinLower ρ B j := zero_lt_one.trans (hP₀.trans_le hP)
      positivity
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.filter_empty,Finset.sum_empty,norm_zero]
    have hP0 : 0 < geometricBinLower ρ B j := zero_lt_one.trans (hP₀.trans_le hP)
    positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimeFactorization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed complementary primary factor in a free-prime sum is a
constant of norm at most one, even when its cubic symbol vanishes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem fixed_primary_free_prime_sum (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (a : Eisenstein → ℂ)
    (r c v : Eisenstein) (hr : primary r) (hc : primary c) (u : ℝ) :
    (∑ p ∈ S, a p*normTwist u (r*(p*c))*cubicSymbol (r*(p*c)) v) =
      (normTwist u r*cubicSymbol r v)*
        ∑ p ∈ S, a p*normTwist u (p*c)*cubicSymbol (p*c) v := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpc : p*c ≠ 0 := mul_ne_zero (hS p hp).2.ne_zero (primary_ne_zero hc)
  rw [normTwist_mul u (primary_ne_zero hr) hpc,
    cubicSymbol_mul_lower (primary_ne_zero hr) hpc]
  ring

lemma fixed_primary_free_prime_norm (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (a : Eisenstein → ℂ)
    (r c v : Eisenstein) (hr : primary r) (hc : primary c) (u : ℝ) :
    ‖∑ p ∈ S, a p*normTwist u (r*(p*c))*cubicSymbol (r*(p*c)) v‖ ≤
      ‖∑ p ∈ S, a p*normTwist u (p*c)*cubicSymbol (p*c) v‖ := by
  rw [fixed_primary_free_prime_sum S hS a r c v hr hc u,norm_mul,
    norm_mul,norm_normTwist,one_mul]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hr v)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeLogScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long-prime threshold gives the actual logarithmic parameter
range required by the published prime estimate, even after bin dilation. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem long_prime_logarithmic_window {P₀ : ℝ} (hP₀ : 1 < P₀) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ Real.log X/4 ∧
      ∀ P : ℝ, Real.exp (Real.sqrt (Real.log X))/2 ≤ P →
        P₀ ≤ P ∧ Real.log X/4 ≤ (Real.log P)^2 := by
  have ht : Tendsto (fun X : ℝ => Real.sqrt (Real.log X)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop
    (max (2*Real.log 2) (Real.log (2*P₀)))),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4:ℝ))] with X hroot hL
  have hroot₂ : 2*Real.log 2 ≤ Real.sqrt (Real.log X) := (le_max_left _ _).trans hroot
  have hrootP : Real.log (2*P₀) ≤ Real.sqrt (Real.log X) := (le_max_right _ _).trans hroot
  refine ⟨by linarith,?_⟩
  intro P hP
  have hPpos : 0 < P := (div_pos (Real.exp_pos _) (by norm_num)).trans_le hP
  have hP₀pos : 0 < 2*P₀ := by linarith
  refine ⟨?_,?_⟩
  · calc
      P₀ = Real.exp (Real.log (2*P₀))/2 := by rw [Real.exp_log hP₀pos]; ring
      _ ≤ Real.exp (Real.sqrt (Real.log X))/2 :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hrootP) (by norm_num)
      _ ≤ P := hP
  · have hlog : Real.sqrt (Real.log X)-Real.log 2 ≤ Real.log P := by
      have h := Real.log_le_log (div_pos (Real.exp_pos _) (by norm_num)) hP
      rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num),Real.log_exp] at h
      exact h
    have hhalf : Real.sqrt (Real.log X)/2 ≤ Real.log P := by linarith
    have hlog₀ : 0 ≤ Real.log P := (by positivity : 0 ≤ Real.sqrt (Real.log X)/2).trans hhalf
    have hprod := mul_nonneg (sub_nonneg.mpr hhalf)
      (add_nonneg hlog₀ (by positivity : 0 ≤ Real.sqrt (Real.log X)/2))
    have hsqrt := Real.sq_sqrt (show 0 ≤ Real.log X by linarith)
    nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeParameterScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed powers of log X fit the prime parameter log X/4 after a
one-unit exponent enlargement. This is uniform in all arithmetic data. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_log_parameter_power (c A : ℝ) :
    ∀ᶠ X : ℝ in atTop,
      0 < Real.log X/4 ∧ c*(Real.log X)^A ≤ (Real.log X/4)^(A+1) := by
  have ht : Tendsto (fun X : ℝ => Real.log X/4) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const (by norm_num : (0:ℝ) < 4)
  filter_upwards [ht.eventually (eventually_ge_atTop (max 1 (c*4^A)))] with X hX
  have hT : 0 < Real.log X/4 := zero_lt_one.trans_le ((le_max_left _ _).trans hX)
  refine ⟨hT,?_⟩
  have he : Real.log X = 4*(Real.log X/4) := by ring
  calc
    c*(Real.log X)^A = (c*4^A)*(Real.log X/4)^A := by
      conv_lhs => rw [he,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hT.le]
      ring
    _ ≤ (Real.log X/4)*(Real.log X/4)^A :=
      mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hX) (Real.rpow_nonneg hT.le _)
    _ = (Real.log X/4)^(A+1) := by
      rw [Real.rpow_add hT,Real.rpow_one]
      ring

lemma prime_parameter_log_saving {L D b : ℝ} (hL : 0 < L) :
    b/(L/4)^D = 4^D*b/L^D := by
  rw [Real.div_rpow hL.le (by norm_num : (0:ℝ) ≤ 4)]
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimeScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual complementary norm and exclusion bounds needed to put
stopped prime rows on the parameter log X/4. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_complement_power_bound {X C ξ P b : ℝ} {m : ℕ}
    (hX : 1 < X) (hgap : C < ξ*m) (hb : 0 ≤ b) (hbX : b ≤ X^C) (hP : 1 ≤ P) :
    b/P < (X^ξ)^m := by
  calc
    b/P ≤ b := div_le_self hb hP
    _ ≤ X^C := hbX
    _ < X^(ξ*m) := Real.rpow_lt_rpow_of_exponent_lt hX hgap
    _ = (X^ξ)^m := by rw [←Real.rpow_mul_natCast (zero_lt_one.trans hX).le]

lemma stopped_complement_exclusion_log {r d e : Eisenstein} (hr : primary r)
    (hd : primary d) (he : e ≠ 0) {X C E b P : ℝ} (hX : 0 < X)
    (hb : 0 ≤ b) (hbX : b ≤ X^C) (hP : 1 ≤ P)
    (hrd : norm (r*d) ≤ b/P) (heX : norm e ≤ X^E) :
    Real.log (norm (r*(d*e))) ≤ (C+E)*Real.log X := by
  have hrp : 0 < norm (r*d) := zero_lt_one.trans_le
    (one_le_norm (primary_ne_zero (primary_mul hr hd)))
  have hep : 0 < norm e := zero_lt_one.trans_le (one_le_norm he)
  have hrX : norm (r*d) ≤ X^C := hrd.trans ((div_le_self hb hP).trans hbX)
  calc
    Real.log (norm (r*(d*e))) = Real.log (norm (r*d))+Real.log (norm e) := by
      rw [←mul_assoc,norm_mul_eq,Real.log_mul (ne_of_gt hrp) (ne_of_gt hep)]
    _ ≤ Real.log (X^C)+Real.log (X^E) :=
      add_le_add (Real.log_le_log hrp hrX) (Real.log_le_log hep heX)
    _ = (C+E)*Real.log X := by rw [Real.log_rpow hX,Real.log_rpow hX]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected-bin free-prime row with its actual full product,
complementary exclusion and both stopping tests. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedSelectedPrimeSet_primary (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r c e : Eisenstein) {p : Eisenstein}
    (hp : p ∈ stoppedSelectedPrimeSet B ρ a b j j₀ k h Z Q early r c e) : primaryPrime p := by
  exact (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1).1).1

theorem stopped_selected_prime_row_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w u : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → |u| ≤ T^H →
      ∀ r c v e : Eisenstein, primary r → primary c → Squarefree c → v ≠ 0 →
        (¬∃ k : Eisenstein, k^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*(r*e))) ≤ T^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖stoppedSelectedPrimeRow B ρ a b w u j j₀ k h Z Q early r c v e‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_stopped_selected_interval_saving hSW hA hD hH hE
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w u j hT hρ hρ₂ hj hP hTP hw hu r c v e hr hc hs hv hnc hNv he hNe
    j₀ k h Z Q early
  unfold stoppedSelectedPrimeRow
  apply (fixed_primary_free_prime_norm (stoppedSelectedPrimeSet B ρ a b j j₀ k h Z Q early r c e)
    (fun p hp => stoppedSelectedPrimeSet_primary B ρ a b j j₀ k h Z Q early r c e hp)
    (fun p => cutoffMoebius primeDetectorCutoff w (p*c)) r c v hr hc u).trans
  exact hbound T B ρ w u a b j hT hρ hρ₂ hj hP hTP hw hu c v (r*e)
    (primaryPrimeFactors (r*c)) hc hs hv hnc hNv (mul_ne_zero (primary_ne_zero hr) he) hNe
    j₀ k h Z Q early r

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeCanonical
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical functions for the exact largest-prime change of variables.
They allow predicates on the original product to be rewritten after the
finite reindexing, without a choice-dependent coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrimeChoice_spec {n : Eisenstein} (h : (primaryPrimeFactors n).Nonempty) :
    largestPrimeChoice n ∈ primaryPrimeFactors n ∧
      largestPrimePredicate primeTieCode (primaryPrimeFactors n) (largestPrimeChoice n) := by
  simpa only [largestPrimeChoice,dite_eq_left h] using selectedLargestPrime_spec (primaryPrimeFactors n) h

lemma largestPrimeChoice_prime_mul {p c : Eisenstein} (hp : primaryPrime p)
    (hc : primary c) (hs : Squarefree c) (hpc : ¬p ∣ c)
    (hl : largestPrimePredicate primeTieCode (primaryPrimeFactors c) p) :
    largestPrimeChoice (p*c) = p ∧ largestPrimeRemainder (p*c) = c := by
  have hf := primaryPrimeFactors_prime_mul hp hc hs hpc
  have hp_mem : p ∈ primaryPrimeFactors (p*c) := by rw [hf]; exact Finset.mem_insert_self _ _
  have hne : (primaryPrimeFactors (p*c)).Nonempty := ⟨p,hp_mem⟩
  have hlarge : largestPrimePredicate primeTieCode (primaryPrimeFactors (p*c)) p := by
    rw [hf]
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Or.inr ⟨rfl,le_rfl⟩
    · exact hl q hq
  have hchoice : largestPrimeChoice (p*c) = p :=
    largestPrime_unique primeTieCode_injective (largestPrimeChoice_spec hne).1 hp_mem
      (largestPrimeChoice_spec hne).2 hlarge
  refine ⟨hchoice,?_⟩
  have hnot : p ∉ primaryPrimeFactors c := fun h => hpc (primaryPrimeFactor_spec hc h).2
  rw [largestPrimeRemainder,hchoice,hf,Finset.erase_insert hnot,primaryPrimeFactors_prod hc hs]

lemma largestPrimeChoice_mul_eq_iff {p c : Eisenstein} (hp : primaryPrime p)
    (hc : primary c) (hs : Squarefree c) (hpc : ¬p ∣ c) :
    largestPrimeChoice (p*c) = p ↔ largestPrimePredicate primeTieCode (primaryPrimeFactors c) p := by
  constructor
  · intro he q hq
    have hf := primaryPrimeFactors_prime_mul hp hc hs hpc
    have hmem : p ∈ primaryPrimeFactors (p*c) := by rw [hf]; exact Finset.mem_insert_self _ _
    have hl := (largestPrimeChoice_spec (show (primaryPrimeFactors (p*c)).Nonempty from ⟨p,hmem⟩)).2
    rw [he] at hl
    exact hl q (by rw [hf]; exact Finset.mem_insert_of_mem hq)
  · exact fun h => (largestPrimeChoice_prime_mul hp hc hs hpc h).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SelectedPrimeCanonical
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma largestPrimeChoice_dvd_right_iff {r d : Eisenstein}
    (hr : primary r) (hd : primary d) (hne : (primaryPrimeFactors d).Nonempty) :
    largestPrimeChoice (r*d) ∣ d ↔ largestPrimeChoice (r*d) = largestPrimeChoice d := by
  have hsub : primaryPrimeFactors d ⊆ primaryPrimeFactors (r*d) := by
    rw [primaryPrimeFactors_mul_union hr hd]
    exact Finset.subset_union_right
  have hne' : (primaryPrimeFactors (r*d)).Nonempty := hne.mono hsub
  have hfull := largestPrimeChoice_spec hne'
  have hright := largestPrimeChoice_spec hne
  have hp := (primaryPrimeFactor_spec (primary_mul hr hd) hfull.1).1
  constructor
  · intro hdiv
    have hm : largestPrimeChoice (r*d) ∈ primaryPrimeFactors d :=
      (primaryPrime_mem_factors_iff hd).mpr ⟨hp,hdiv⟩
    exact largestPrime_unique primeTieCode_injective hm hright.1
      (fun q hq => hfull.2 q (hsub hq)) hright.2
  · intro he
    rw [he]
    exact (primaryPrimeFactor_spec hd hright.1).2

lemma selected_largest_free_prime_iff {r p c : Eisenstein}
    (hr : primary r) (hp : primaryPrime p) (hc : primary c)
    (hs : Squarefree (r*(p*c)))
    (hl : largestPrimePredicate primeTieCode (primaryPrimeFactors c) p) :
    largestPrimeChoice (r*(p*c)) ∣ p*c ↔
      largestPrimePredicate primeTieCode (primaryPrimeFactors (r*c)) p := by
  have hsd : Squarefree (p*c) := (squarefree_mul_iff.mp hs).2.2
  have hsc : Squarefree c := (squarefree_mul_iff.mp hsd).2.2
  have hpc : ¬p ∣ c := by
    have hcop : IsCoprime p c := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hsd).1
    exact fun h => hp.2.not_isUnit (hcop.isUnit_of_dvd h)
  have he : r*(p*c) = p*(r*c) := by ring
  have hs' : Squarefree (p*(r*c)) := he ▸ hs
  have hsrc : Squarefree (r*c) := (squarefree_mul_iff.mp hs').2.2
  have hprc : ¬p ∣ r*c := by
    have hcop : IsCoprime p (r*c) :=
      isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs').1
    exact fun h => hp.2.not_isUnit (hcop.isUnit_of_dvd h)
  have hchoice := (largestPrimeChoice_prime_mul hp hc hsc hpc hl).1
  have hne : (primaryPrimeFactors (p*c)).Nonempty := by
    rw [primaryPrimeFactors_prime_mul hp hc hsc hpc]
    exact Finset.insert_nonempty _ _
  rw [largestPrimeChoice_dvd_right_iff hr (primary_mul hp.1 hc) hne,hchoice,he]
  exact largestPrimeChoice_mul_eq_iff hp (primary_mul hr hc) hsrc hprc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SelectedPrimeGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arithmetic after removing the selected largest prime. These
identities retain the original squarefreeness, exclusion and norm range. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrimeChoice_decomposition {d : Eisenstein} (hd : primary d)
    (hs : Squarefree d) (hne : (primaryPrimeFactors d).Nonempty) :
    primaryPrime (largestPrimeChoice d) ∧ primary (largestPrimeRemainder d) ∧
      Squarefree (largestPrimeRemainder d) ∧
      ¬largestPrimeChoice d ∣ largestPrimeRemainder d ∧
      largestPrimeChoice d*largestPrimeRemainder d = d ∧
      largestPrimePredicate primeTieCode (primaryPrimeFactors (largestPrimeRemainder d))
        (largestPrimeChoice d) := by
  obtain ⟨p,c,hp,hc,hsc,hpc,he,hl,_⟩ := primary_largest_prime_split hd hs hne
  have hcan := largestPrimeChoice_prime_mul hp hc hsc hpc hl
  rw [he] at hcan
  rw [hcan.1,hcan.2]
  exact ⟨hp,hc,hsc,hpc,he,hl⟩

lemma selectedPrime_product_conditions (r p c e : Eisenstein) (hp : primaryPrime p) :
    (Squarefree (r*(p*c)) ∧ IsCoprime (r*(p*c)) e) ↔
      Squarefree (r*c) ∧ IsCoprime (r*c) e ∧ IsCoprime p (c*(r*e)) := by
  have he : r*(p*c) = p*(r*c) := by ring
  rw [he,squarefree_mul_iff,IsCoprime.mul_left_iff]
  constructor
  · rintro ⟨⟨hpc,_,hsrc⟩,hpe,hrce⟩
    have hpc' : IsCoprime p (r*c) := isRelPrime_iff_isCoprime.mp hpc
    refine ⟨hsrc,hrce,?_⟩
    exact hpc'.of_mul_right_right.mul_right (hpc'.of_mul_right_left.mul_right hpe)
  · rintro ⟨hsrc,hrce,hpcre⟩
    have hpc : IsCoprime p (r*c) :=
      hpcre.of_mul_right_right.of_mul_right_left.mul_right hpcre.of_mul_right_left
    exact ⟨⟨hpc.isRelPrime,hp.2.irreducible.squarefree,hsrc⟩,
      hpcre.of_mul_right_right.of_mul_right_right,hrce⟩

lemma selectedPrime_norm_interval {r c : Eisenstein} (hr : r ≠ 0) (hc : c ≠ 0)
    (p : Eisenstein) (a b : ℝ) :
    (a < norm (r*(p*c)) ∧ norm (r*(p*c)) ≤ b) ↔
      a/norm (r*c) < norm p ∧ norm p ≤ b/norm (r*c) := by
  have hn : 0 < norm (r*c) := norm_pos_of_ne_zero (mul_ne_zero hr hc)
  have he : norm (r*(p*c)) = norm p*norm (r*c) := by
    rw [norm_mul_eq,norm_mul_eq,norm_mul_eq]
    ring
  rw [he]
  exact and_congr (div_lt_iff₀ hn).symm (le_div_iff₀ hn).symm

lemma largestPrimePredicate_complement {r c p : Eisenstein}
    (hr : primary r) (hc : primary c)
    (h : largestPrimePredicate primeTieCode (primaryPrimeFactors (r*c)) p) :
    largestPrimePredicate primeTieCode (primaryPrimeFactors c) p := by
  rw [primaryPrimeFactors_mul_union hr hc] at h
  exact fun q hq => h q (Finset.mem_union_right _ hq)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedReindex
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selected-divisor sum is exactly the finite collection
of free-prime rows. Its squarefree support, global largest-prime choice,
output interval, exclusion and stopping predicates are all retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma selectedStopped_forward (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    {r e d : Eisenstein} (hr : primary r)
    (hd : d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e) :
    (largestPrimeRemainder d,largestPrimeChoice d) ∈
      selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e := by
  obtain ⟨hd,hs,hne,hcop,hint,hrole,hbin,hstop⟩ := Finset.mem_filter.mp hd
  obtain ⟨hd,hdB⟩ := mem_primaryElementBall.mp hd
  obtain ⟨hp,hc,hsc,hpc,he,hl⟩ := largestPrimeChoice_decomposition hd
    (squarefree_mul_iff.mp hs).2.2 hne
  have hfull : largestPrimeChoice (r*d) = largestPrimeChoice d :=
    (largestPrimeChoice_dvd_right_iff hr hd hne).mp hrole
  have hpB : norm (largestPrimeChoice d) ≤ B :=
    (norm_le_of_dvd_nonzero (primary_ne_zero hd) ⟨largestPrimeRemainder d,he.symm⟩).trans hdB
  have hcB : norm (largestPrimeRemainder d) ≤ B :=
    (norm_le_of_dvd_nonzero (primary_ne_zero hd)
      ⟨largestPrimeChoice d,by rw [mul_comm,he]⟩).trans hdB
  have hs' : Squarefree (r*(largestPrimeChoice d*largestPrimeRemainder d)) := by rw [he]; exact hs
  have hcop' : IsCoprime (r*(largestPrimeChoice d*largestPrimeRemainder d)) e := by
    rw [he]; exact hcop
  obtain ⟨hsrc,hrce,hpcre⟩ := (selectedPrime_product_conditions r _ _ e hp).mp ⟨hs',hcop'⟩
  have hlarge := (selected_largest_free_prime_iff hr hp hc hs' hl).mp (by rw [he]; exact hrole)
  have hinterval := (selectedPrime_norm_interval (primary_ne_zero hr) (primary_ne_zero hc)
    (largestPrimeChoice d) a b).mp (by rw [he]; exact hint)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨mem_primaryElementBall.mpr ⟨hc,hcB⟩,
    mem_primeCutoff.mpr ⟨hp,hpB⟩⟩,hsrc,hrce,?_⟩
  unfold stoppedSelectedPrimeSet
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨mem_primeCutoff.mpr ⟨hp,hpB⟩,hinterval⟩,hpcre⟩,
      hlarge,?_⟩,?_⟩
  · simpa only [hfull] using hbin
  · simpa only [he] using hstop

lemma selectedStopped_backward (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    {r e : Eisenstein} (hr : primary r) (hbB : b ≤ B) {t : Eisenstein × Eisenstein}
    (ht : t ∈ selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e) :
    t.2*t.1 ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e ∧
      (largestPrimeRemainder (t.2*t.1),largestPrimeChoice (t.2*t.1)) = t := by
  obtain ⟨ht,hsrc,hrce,hrow⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc,hp⟩ := Finset.mem_product.mp ht
  obtain ⟨hc,_⟩ := mem_primaryElementBall.mp hc
  obtain ⟨hp,hpB⟩ := mem_primeCutoff.mp hp
  obtain ⟨hrow,hstop⟩ := Finset.mem_filter.mp hrow
  obtain ⟨hrow,hlarge,hbin⟩ := Finset.mem_filter.mp hrow
  obtain ⟨hrow,hpc⟩ := Finset.mem_filter.mp hrow
  obtain ⟨_,hint⟩ := Finset.mem_filter.mp hrow
  have hsfull := (selectedPrime_product_conditions r t.2 t.1 e hp).mpr ⟨hsrc,hrce,hpc⟩
  have hsc : Squarefree t.1 := (squarefree_mul_iff.mp hsrc).2.2
  have hpc' : ¬t.2 ∣ t.1 := fun hh => hp.2.not_isUnit (hpc.of_mul_right_left.isUnit_of_dvd hh)
  have hl := largestPrimePredicate_complement hr hc hlarge
  have hcan := largestPrimeChoice_prime_mul hp hc hsc hpc' hl
  have hne : (primaryPrimeFactors (t.2*t.1)).Nonempty := by
    rw [primaryPrimeFactors_prime_mul hp hc hsc hpc']
    exact Finset.insert_nonempty _ _
  have hrole := (selected_largest_free_prime_iff hr hp hc hsfull.1 hl).mpr hlarge
  have hfull : largestPrimeChoice (r*(t.2*t.1)) = t.2 :=
    ((largestPrimeChoice_dvd_right_iff hr (primary_mul hp.1 hc) hne).mp hrole).trans hcan.1
  have hint' := (selectedPrime_norm_interval (primary_ne_zero hr) (primary_ne_zero hc)
    t.2 a b).mpr hint
  have hdB : norm (t.2*t.1) ≤ B :=
    (norm_le_of_dvd_nonzero (primary_ne_zero (primary_mul hr (primary_mul hp.1 hc)))
      ⟨r,by ring⟩).trans (hint'.2.trans hbB)
  refine ⟨Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨primary_mul hp.1 hc,hdB⟩,
    hsfull.1,hne,hsfull.2,hint',hrole,?_,hstop⟩,?_⟩
  · simpa only [hfull] using hbin
  · exact Prod.ext hcan.2 hcan.1

/-- Every original selected-divisor term occurs exactly once. -/
theorem selectedStopped_sum_reindex (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r e : Eisenstein) (hr : primary r) (hbB : b ≤ B)
    (F : Eisenstein → ℂ) :
    (∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e, F d) =
      ∑ t ∈ selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e, F (t.2*t.1) := by
  apply Finset.sum_bij (fun d _ => (largestPrimeRemainder d,largestPrimeChoice d))
  · intro d hd
    exact selectedStopped_forward B ρ a b j j₀ k h Z Q early hr hd
  · intro d hd d' hd' heq
    have hprop := (Finset.mem_filter.mp hd).2
    have hprop' := (Finset.mem_filter.mp hd').2
    have hcan := largestPrimeChoice_decomposition (mem_primaryElementBall.mp (Finset.mem_filter.mp hd).1).1
      (squarefree_mul_iff.mp hprop.1).2.2 hprop.2.1
    have hcan' := largestPrimeChoice_decomposition (mem_primaryElementBall.mp (Finset.mem_filter.mp hd').1).1
      (squarefree_mul_iff.mp hprop'.1).2.2 hprop'.2.1
    have hm := congrArg (fun t : Eisenstein × Eisenstein => t.2*t.1) heq
    exact hcan.2.2.2.2.1.symm.trans (hm.trans hcan'.2.2.2.2.1)
  · intro t ht
    exact ⟨t.2*t.1,(selectedStopped_backward B ρ a b j j₀ k h Z Q early hr hbB ht).1,
      (selectedStopped_backward B ρ a b j j₀ k h Z Q early hr hbB ht).2⟩
  · intro d hd
    have hp := (Finset.mem_filter.mp hd).2
    have hcan := largestPrimeChoice_decomposition (mem_primaryElementBall.mp (Finset.mem_filter.mp hd).1).1
      (squarefree_mul_iff.mp hp.1).2.2 hp.2.1
    exact congrArg F hcan.2.2.2.2.1.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the selected-bin free-prime rows, and the
complementary norm cutoff forced by the lower endpoint of the prime bin. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedSelectedPrimeSet_subset (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r c e : Eisenstein) :
    stoppedSelectedPrimeSet B ρ a b j j₀ k h Z Q early r c e ⊆ primeCutoff B := by
  intro p hp
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
    (Finset.mem_filter.mp hp).1).1).1).1

lemma selectedStopped_row_collection (B ρ a b w u : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r v e : Eisenstein) :
    (∑ t ∈ selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w (t.2*t.1)*normTwist u (r*(t.2*t.1))*
        cubicSymbol (r*(t.2*t.1)) v) =
      ∑ c ∈ (primaryElementBall B).filter (fun c => Squarefree (r*c) ∧ IsCoprime (r*c) e),
        stoppedSelectedPrimeRow B ρ (a/norm (r*c)) (b/norm (r*c)) w u
          j j₀ k h Z Q early r c v e := by
  unfold selectedStoppedRowPairs
  rw [Finset.sum_filter,Finset.sum_product,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hrc : Squarefree (r*c) ∧ IsCoprime (r*c) e
  · simp only [hrc.1,hrc.2,true_and,ite_true, if_true]
    unfold stoppedSelectedPrimeRow
    rw [←Finset.sum_filter,Finset.filter_mem_eq_of_subset
      (stoppedSelectedPrimeSet_subset B ρ (a/norm (r*c)) (b/norm (r*c))
        j j₀ k h Z Q early r c e)]
  · have hzero (p : Eisenstein) :
        ¬(Squarefree (r*c) ∧ IsCoprime (r*c) e ∧
          p ∈ stoppedSelectedPrimeSet B ρ (a/norm (r*c)) (b/norm (r*c))
            j j₀ k h Z Q early r c e) := fun hp => hrc ⟨hp.1,hp.2.1⟩
    simp only [hzero,ite_false, if_false,Finset.sum_const_zero,hrc]

lemma selectedStopped_complement_bound {B ρ a b : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j j₀ k h : ℕ} (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {r c e p : Eisenstein} (hr : primary r) (hc : primary c)
    (hp : p ∈ stoppedSelectedPrimeSet B ρ (a/norm (r*c)) (b/norm (r*c))
      j j₀ k h Z Q early r c e) :
    norm (r*c) ≤ b/geometricBinLower ρ B j := by
  have hpP := stoppedSelectedPrimeSet_primary B ρ _ _ j j₀ k h Z Q early r c e hp
  have hpB := (mem_primeCutoff.mp (stoppedSelectedPrimeSet_subset B ρ _ _ j j₀ k h
    Z Q early r c e hp)).2
  have hrow := (Finset.mem_filter.mp hp).1
  have hbin := (Finset.mem_filter.mp hrow).2.2
  have hint := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hrow).1).1).2
  have hnorm := (geometricPrimeBin_eq_iff hρ hρ₂ hj hpP hpB).mp hbin
  have hnrc : 0 < norm (r*c) := norm_pos_of_ne_zero
    (mul_ne_zero (primary_ne_zero hr) (primary_ne_zero hc))
  have hnb : norm p*norm (r*c) ≤ b := (le_div_iff₀ hnrc).mp hint.2
  apply (le_div_iff₀ (zero_lt_one.trans (geometricBinLower_gt_one hρ hj))).mpr
  calc
    norm (r*c)*geometricBinLower ρ B j ≤ norm (r*c)*norm p :=
      mul_le_mul_of_nonneg_left hnorm.1 hnrc.le
    _ ≤ b := by simpa only [mul_comm] using hnb

lemma selectedStopped_row_eq_zero {B ρ a b w u : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j j₀ k h : ℕ} (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {r c v e : Eisenstein} (hr : primary r) (hc : primary c)
    (hbig : b/geometricBinLower ρ B j < norm (r*c)) :
    stoppedSelectedPrimeRow B ρ (a/norm (r*c)) (b/norm (r*c)) w u
      j j₀ k h Z Q early r c v e = 0 := by
  unfold stoppedSelectedPrimeRow
  apply Finset.sum_eq_zero
  intro p hp
  exact (not_lt_of_ge (selectedStopped_complement_bound hρ hρ₂ hj hr hc hp) hbig).elim

theorem selectedStopped_original_rows (B ρ a b w u : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r v e : Eisenstein) (hr : primary r) (hbB : b ≤ B) :
    (∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*cubicSymbol (r*d) v) =
      ∑ c ∈ (primaryElementBall B).filter (fun c => Squarefree (r*c) ∧ IsCoprime (r*c) e),
        stoppedSelectedPrimeRow B ρ (a/norm (r*c)) (b/norm (r*c)) w u
          j j₀ k h Z Q early r c v e := by
  rw [selectedStopped_sum_reindex B ρ a b j j₀ k h Z Q early r e hr hbB]
  exact selectedStopped_row_collection B ρ a b w u j j₀ k h Z Q early r v e

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original selected-side stopped sums, after their exact free-prime
reindexing. The complementary cutoff is derived from the actual bin. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem selectedStopped_original_collection {B ρ a b w u : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool)
    (R : Finset Eisenstein) (hR : ∀ r ∈ R, primary r)
    (f : Eisenstein → ℂ) (v e : Eisenstein) (hbB : b ≤ B) :
    (∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*cubicSymbol (r*d) v) =
      ∑ t ∈ (R ×ˢ primaryElementBall B).filter
        (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ b/geometricBinLower ρ B j),
        if IsCoprime (t.1*t.2) e then f t.1*
          stoppedSelectedPrimeRow B ρ (a/norm (t.1*t.2)) (b/norm (t.1*t.2)) w u
            j j₀ k h Z Q early t.1 t.2 v e else 0 := by
  rw [Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r hr
  rw [selectedStopped_original_rows B ρ a b w u j j₀ k h Z Q early r v e (hR r hr) hbB,
    Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  have hc' := (mem_primaryElementBall.mp hc).1
  by_cases hs : Squarefree (r*c)
  · by_cases he : IsCoprime (r*c) e
    · by_cases hn : norm (r*c) ≤ b/geometricBinLower ρ B j
      · simp only [hs,he,hn,and_self,ite_true, if_true]
      · have hz := selectedStopped_row_eq_zero hρ hρ₂ hj (hR r hr) hc'
          (lt_of_not_ge hn) (v := v) (e := e) (a := a) (w := w) (u := u)
          (j₀ := j₀) (k := k) (h := h) (Z := Z) (Q := Q) (early := early)
        simp only [hs,he,hn,and_false,ite_false, if_false,and_true,ite_true, if_true,hz,mul_zero]
    · simp only [hs,he,and_false,ite_false, if_false]
      split_ifs <;> rfl
  · simp only [hs,false_and,ite_false, if_false]

theorem stopped_selected_original_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w u : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      b ≤ B → 0 ≤ b → 1 ≤ w → |u| ≤ T^H →
      ∀ (R : Finset Eisenstein) (f : Eisenstein → ℂ) (M : ℝ) (m : ℕ),
      (∀ r ∈ R, primary r) → 0 ≤ M → (∀ r ∈ R, ‖f r‖ ≤ M) →
      (∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p) →
      b/geometricBinLower ρ B j < w^m →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ t ∈ (R ×ˢ primaryElementBall B).filter
        (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ b/geometricBinLower ρ B j),
        Real.log (norm (t.2*(t.1*e))) ≤ T^E) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
        cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*cubicSymbol (r*d) v‖ ≤
        (18*((2^m:ℕ)*M)*K)*b/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hrow⟩ := stopped_selected_prime_row_saving hSW hA hD hH hE
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w u j hT hρ hρ₂ hj hP hTP hbB hb hw hu R f M m hR hM hf hrough hsize
    v e hv hnc hNv he hlog j₀ k h Z Q early
  have hPpos : 0 < geometricBinLower ρ B j := zero_lt_one.trans (hP₀.trans_le hP)
  let U := (R ×ˢ primaryElementBall B).filter
    (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ b/geometricBinLower ρ B j)
  let C := K*geometricBinLower ρ B j/T^D
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (t : Eisenstein × Eisenstein) (ht : t ∈ U) :
      ‖if IsCoprime (t.1*t.2) e then f t.1*
          stoppedSelectedPrimeRow B ρ (a/norm (t.1*t.2)) (b/norm (t.1*t.2)) w u
            j j₀ k h Z Q early t.1 t.2 v e else 0‖ ≤ ‖f t.1‖*C := by
    by_cases hcop : IsCoprime (t.1*t.2) e
    · rw [ite_eq_left hcop,norm_mul]
      obtain ⟨ht,hprop⟩ := Finset.mem_filter.mp ht
      obtain ⟨hr,hc⟩ := Finset.mem_product.mp ht
      exact mul_le_mul_of_nonneg_left
        (hrow T B ρ _ _ w u j hT hρ hρ₂ hj hP hTP (zero_lt_one.trans_le hw) hu
          t.1 t.2 v e (hR _ hr) (mem_primaryElementBall.mp hc).1
          (squarefree_mul_iff.mp hprop.1).2.2 hv hnc hNv he
          (hlog t (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr,hc⟩,hprop⟩))
          j₀ k h Z Q early) (_root_.norm_nonneg _)
    · rw [ite_eq_right hcop,norm_zero]
      exact mul_nonneg (_root_.norm_nonneg _) hC
  rw [selectedStopped_original_collection hρ hρ₂ hj Z Q early R hR f v e hbB]
  change ‖∑ t ∈ U, _‖ ≤ _
  calc
    _ ≤ ∑ t ∈ U, ‖if IsCoprime (t.1*t.2) e then f t.1*
        stoppedSelectedPrimeRow B ρ (a/norm (t.1*t.2)) (b/norm (t.1*t.2)) w u
          j j₀ k h Z Q early t.1 t.2 v e else 0‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ U, ‖f t.1‖*C := Finset.sum_le_sum hbound
    _ = (∑ t ∈ U, ‖f t.1‖)*C := (Finset.sum_mul _ _ _).symm
    _ ≤ (18*(b/geometricBinLower ρ B j)*((2^m:ℕ)*M))*C :=
      mul_le_mul_of_nonneg_right
        (stopped_complement_mass R (primaryElementBall B) hR
          (fun c hc => (mem_primaryElementBall.mp hc).1) f hM
          (div_nonneg hb hPpos.le) hf hw hrough hsize) hC
    _ = _ := by
      dsimp [C]
      field_simp [ne_of_gt hPpos]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedBeta
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selected-side prime cancellation applies to the literal
stoppedBeta coefficient, with its global-largest role selected exactly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma selected_largest_bin_nonempty {B ρ : ℝ} {j : ℕ}
    (hj : j < geometricBinCount ρ B) {r d : Eisenstein} (hr : primary r) (hd : primary d)
    (hrole : largestPrimeChoice (r*d) ∣ d)
    (hbin : geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j) :
    (primaryPrimeFactors d).Nonempty := by
  have hne : (primaryPrimeFactors (r*d)).Nonempty := by
    by_contra hempty
    have hc : largestPrimeChoice (r*d) = 1 := by
      simp only [largestPrimeChoice,dite_eq_right hempty]
    rw [hc] at hbin
    have hone : geometricPrimeBin ρ B (1 : Eisenstein) = geometricBinCount ρ B := by
      simp only [geometricPrimeBin,norm_one_eq,Real.log_one,zero_div,Nat.floor_zero,Nat.sub_zero]
    rw [hone] at hbin
    omega
  have hp := (primaryPrimeFactor_spec (primary_mul hr hd) (largestPrimeChoice_spec hne).1).1
  exact ⟨largestPrimeChoice (r*d),(primaryPrime_mem_factors_iff hd).mpr ⟨hp,hrole⟩⟩

lemma selectedStoppedDivisorSet_eq {B ρ a b : ℝ} {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool) (r e : Eisenstein)
    (hr : primary r) :
    selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e =
      (primaryElementBall B).filter (fun d =>
        (Squarefree (r*d) ∧ IsCoprime (r*d) e ∧ a < norm (r*d) ∧ norm (r*d) ≤ b) ∧
          stoppedSelectedTest B ρ j j₀ k h Z Q early r d) := by
  ext d
  constructor
  · intro hmem
    obtain ⟨hd,hs,_hne,hcop,hint,hrole,hbin,hstop⟩ := Finset.mem_filter.mp hmem
    exact Finset.mem_filter.mpr ⟨hd,⟨hs,hcop,hint.1,hint.2⟩,hstop,hrole,hbin⟩
  · intro hmem
    obtain ⟨hd,⟨hs,hcop,ha,hb⟩,hstop,hrole,hbin⟩ := Finset.mem_filter.mp hmem
    exact Finset.mem_filter.mpr
      ⟨hd,hs,selected_largest_bin_nonempty hj hr (mem_primaryElementBall.mp hd).1 hrole hbin,
        hcop,⟨ha,hb⟩,hrole,hbin,hstop⟩

/-- Exact coefficient collection; all analytic cancellation belongs to
`stopped_selected_original_saving`, already proved from the raw input. -/
theorem stoppedBeta_selected_identity {B ρ a b w u : ℝ} {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool)
    (R : Finset Eisenstein) (hR : ∀ r ∈ R, primary r)
    (f : Eisenstein → ℂ) (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport R (primaryElementBall B),
      stoppedBeta R (primaryElementBall B) f primeDetectorCutoff w
        (stoppedSelectedTest B ρ j j₀ k h Z Q early) n *
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*cubicSymbol n v else 0)) =
      ∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
        cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*cubicSymbol (r*d) v := by
  unfold stoppedBeta
  rw [primaryPairCoefficient_sum,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r hr
  rw [selectedStoppedDivisorSet_eq hj Z Q early r e (hR r hr),Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases ht : stoppedSelectedTest B ρ j j₀ k h Z Q early r d
  · by_cases hc : Squarefree (r*d) ∧ IsCoprime (r*d) e ∧ a < norm (r*d) ∧ norm (r*d) ≤ b
    · simp only [ht,hc,and_self,ite_true, if_true]
      ring
    · simp only [ht,hc,false_and,ite_false, if_false,mul_zero]
  · simp only [ht,and_false,ite_false, if_false,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedDistinguished
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected-divisor role with the actual distinguished-tuple
coefficient. Its roughness and coefficient bound are proved internally. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_selected_distinguished_saving (m : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) {A D H E : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      b ≤ B → 0 ≤ b → 1 ≤ w → w ≤ z → |u| ≤ T^H →
      b/geometricBinLower ρ B j < w^m →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ t ∈ orderedConvolutionSupport (fun _ : ι => primeCutoff B) ×ˢ primaryElementBall B,
        Squarefree (t.1*t.2) → norm (t.1*t.2) ≤ b/geometricBinLower ρ B j →
        Real.log (norm (t.2*(t.1*e))) ≤ T^E) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B))
          (primaryElementBall B),
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) (primaryElementBall B)
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
          (stoppedSelectedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*cubicSymbol n v else 0)‖ ≤ K*b/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := stopped_selected_original_saving hSW hA hD hH hE
  let M : ℝ := ‖((Fintype.card ι).factorial:ℂ)⁻¹‖*
    ((Fintype.card ι)^(Fintype.card ι):ℕ)+1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨18*((2^m:ℕ)*M)*K,P₀,by positivity,hP₀,?_⟩
  intro T B ρ a b w z u j hT hρ hρ₂ hj hP hTP hbB hb hw hwz hu hsize W hW
    v e hv hnc hNv he hNe j₀ k h Z Q early
  let S := fun _ : ι => primeCutoff B
  let R := orderedConvolutionSupport S
  let f := distinguishedTupleCoefficient S (fun l p => W l (norm p)) primeDetectorCutoff w z
  have hS : ∀ l, ∀ p ∈ S l, primaryPrime p := fun _ _ hp => (mem_primeCutoff.mp hp).1
  have hR : ∀ r ∈ R, primary r := fun _ hr =>
    orderedPrimarySupport_primary S (fun l p hp => (hS l p hp).1) hr
  have hf : ∀ r ∈ R, ‖f r‖ ≤ M := by
    intro r _
    apply (distinguishedTupleCoefficient_norm S hS (fun l p => W l (norm p))
      (fun l p _ => hW l _) (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
      w z r).trans
    dsimp [M]
    linarith
  let R₁ := R.filter (fun r => f r ≠ 0)
  have hR₁ : ∀ r ∈ R₁, primary r := fun r hr => hR r (Finset.mem_filter.mp hr).1
  have hrough : ∀ r ∈ R₁, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p := by
    intro r hr p hp
    have hp' := primaryPrimeFactor_spec (hR₁ r hr) hp
    exact (distinguishedTupleCoefficient_prime_support S hS (fun l p => W l (norm p))
      (fun _ _ hx => primeDetectorCutoff_one hx) (fun _ hx => primeDetectorCutoff_zero hx)
      (zero_lt_one.trans_le hw) hwz (Finset.mem_filter.mp hr).2 hp'.1 hp'.2).1.le
  have heq : (∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*cubicSymbol (r*d) v) =
    ∑ r ∈ R₁, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*cubicSymbol (r*d) v := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hz : f r = 0 <;> simp only [hz,ne_eq,not_true_eq_false,not_false_eq_true,
      ite_false, if_false,ite_true, if_true,zero_mul]
  rw [stoppedBeta_selected_identity hj Z Q early R hR f v e,heq]
  exact hbound T B ρ a b w u j hT hρ hρ₂ hj hP hTP hbB hb hw hu R₁ f M m hR₁ hM.le
    (fun r hr => hf r (Finset.mem_filter.mp hr).1) hrough hsize v e hv hnc hNv he
    (by
      intro t ht
      obtain ⟨ht,hs,hn⟩ := Finset.mem_filter.mp ht
      obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
      exact hNe t (Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hr).1,hd⟩) hs hn)
    j₀ k h Z Q early

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedLogSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected-divisor role has the same log-X saving as the
distinguished role, for the literal stopped coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_selected_log_saving_oai (m : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) {A D H E C ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H)
    (hξ : 0 < ξ) (hgap : C < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B ρ a b z u : ℝ) (j : ℕ),
      1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      Real.exp (Real.sqrt (Real.log X))/2 ≤ geometricBinLower ρ B j →
      b ≤ B → 0 ≤ b → b ≤ X^C → X^ξ ≤ z → |u| ≤ (Real.log X)^H →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B))
          (primaryElementBall B),
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) (primaryElementBall B)
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff (X^ξ) z) primeDetectorCutoff (X^ξ)
          (stoppedSelectedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*cubicSymbol n v else 0)‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := stoppedBeta_selected_distinguished_saving (ι := ι) m hSW
    (A := A+1) (D := D) (H := H+1) (E := 2)
    (by linarith) hD (by linarith) (by norm_num)
  refine ⟨K*4^D,by positivity,?_⟩
  filter_upwards [long_prime_logarithmic_window hP₀,
    eventually_log_parameter_power 1 A,eventually_log_parameter_power 1 H,
    eventually_log_parameter_power (C+E) 1,eventually_gt_atTop (1:ℝ)] with
      X hwindow hscaleA hscaleH hscaleE hX
  intro B ρ a b z u j hρ hρ₂ hj hPlong hbB hb hbX hwz hu W hW
    v e hv hnc hNv he heX j₀ k h Z Q early
  have hXp : 0 < X := zero_lt_one.trans hX
  have hLp : 0 < Real.log X := Real.log_pos hX
  have hP := hwindow.2 _ hPlong
  have hw : 1 ≤ X^ξ := Real.one_le_rpow hX.le hξ.le
  have hsize : b/geometricBinLower ρ B j < (X^ξ)^m :=
    stopped_complement_power_bound hX hgap hb hbX (geometricBinLower_gt_one hρ hj).le
  have hNe (t : Eisenstein × Eisenstein)
      (ht : t ∈ orderedConvolutionSupport (fun _ : ι => primeCutoff B) ×ˢ primaryElementBall B)
      (_hs : Squarefree (t.1*t.2)) (hn : norm (t.1*t.2) ≤ b/geometricBinLower ρ B j) :
      Real.log (norm (t.2*(t.1*e))) ≤ (Real.log X/4)^(2:ℝ) := by
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    have hprod := orderedPrimarySupport_primary (fun _ : ι => primeCutoff B)
      (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr
    have heq : t.2*(t.1*e) = t.1*(t.2*e) := by ring
    rw [heq]
    apply (stopped_complement_exclusion_log hprod (mem_primaryElementBall.mp hd).1 he hXp
      hb hbX (geometricBinLower_gt_one hρ hj).le hn heX).trans
    simpa only [Real.rpow_one,show (1:ℝ)+1=2 by norm_num] using hscaleE.2
  have hh := hbound (Real.log X/4) B ρ a b (X^ξ) z u j hwindow.1 hρ hρ₂ hj hP.1 hP.2
    hbB hb hw hwz (hu.trans (by simpa only [one_mul] using hscaleH.2)) hsize W hW
    v e hv hnc (hNv.trans (by simpa only [one_mul] using hscaleA.2)) he hNe
    j₀ k h Z Q early
  apply hh.trans_eq
  rw [prime_parameter_log_saving hLp]
  ring

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.stoppedBeta_selected_log_saving_oai.{u_1} := @OAI.CubicFirstMoment.stoppedBeta_selected_log_saving_oai.{u_1}
