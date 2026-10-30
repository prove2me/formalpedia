-- Prove2me | solution 1 for OAI.CubicFirstMoment.stopped_low_core_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:49:45.520326+00:00
-- url     : https://prove2.me/submissions/e41d4552-bafb-4632-9279-a9814719ecf1

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015
import Theorems.Thm_OAI_CubicFirstMoment_stoppedBeta_selected_log_saving

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primeDetectorCutoff_one {x : ℝ} (hx : x ≤ 1) : primeDetectorCutoff x = 1 := by
  rw [primeDetectorCutoff,Real.smoothTransition.zero_of_nonpos (by linarith),sub_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficientBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primeDetectorCutoff_moebius_norm (w : ℝ) (d : Eisenstein) :
    ‖cutoffMoebius primeDetectorCutoff w d‖ ≤ 1 :=
  cutoffMoebius_norm_le_one (fun x => ⟨primeDetectorCutoff_nonneg x,
    primeDetectorCutoff_le_one x⟩) w d

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedPrimeVariation
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual radial weights when the largest prime lies in a distinguished
tuple coordinate. The detector difference has a uniform scaled derivative,
so the original smooth weight, rather than an arbitrary bounded sequence,
can be used in prime partial summation. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma detector_difference_smooth (w z : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ =>
      (primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ)) :=
  (primeDetectorCutoff_rescaled_smooth w).sub (primeDetectorCutoff_rescaled_smooth z)

lemma detector_difference_norm (w z x : ℝ) :
    ‖(primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ)‖ ≤ 1 := by
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [primeDetectorCutoff_nonneg (x/w),primeDetectorCutoff_le_one (x/w),
    primeDetectorCutoff_nonneg (x/z),primeDetectorCutoff_le_one (x/z)]

lemma detector_difference_deriv {E : ℝ}
    (hE : ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ E)
    {w z x : ℝ} (hw : 0 < w) (hz : 0 < z) (hx : 0 < x) :
    ‖deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)-
      (primeDetectorCutoff (t/z):ℂ)) x‖*x ≤ 2*E := by
  have hdw := ((primeDetectorCutoff_rescaled_smooth w).differentiable
    (by norm_num)).differentiableAt (x := x)
  have hdz := ((primeDetectorCutoff_rescaled_smooth z).differentiable
    (by norm_num)).differentiableAt (x := x)
  have he : deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)-
      (primeDetectorCutoff (t/z):ℂ)) x =
      deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)) x-
        deriv (fun t : ℝ => (primeDetectorCutoff (t/z):ℂ)) x := by
    exact deriv_fun_sub hdw hdz
  rw [he]
  calc
    _ ≤ (‖deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)) x‖+
        ‖deriv (fun t : ℝ => (primeDetectorCutoff (t/z):ℂ)) x‖)*x :=
      mul_le_mul_of_nonneg_right (norm_sub_le _ _) hx.le
    _ = ‖deriv (fun t : ℝ => (primeDetectorCutoff (t/w):ℂ)) x‖*x+
        ‖deriv (fun t : ℝ => (primeDetectorCutoff (t/z):ℂ)) x‖*x := by ring
    _ ≤ E+E := add_le_add (primeDetectorCutoff_rescaled_deriv hE hw hx)
      (primeDetectorCutoff_rescaled_deriv hE hz hx)
    _ = _ := by ring

theorem distinguishedRadialWeight_bounds (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    {M D E w z : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (_hE : 0 ≤ E)
    (hw : 0 < w) (hz : 0 < z) (hWnorm : ∀ x, ‖W x‖ ≤ M)
    (hWderiv : ∀ x, 0 < x → ‖deriv W x‖*x ≤ D)
    (hdet : ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ E) :
    ContDiff ℝ ∞ (distinguishedRadialWeight W w z) ∧
    (∀ x, ‖distinguishedRadialWeight W w z x‖ ≤ M) ∧
    (∀ x, 0 < x → ‖deriv (distinguishedRadialWeight W w z) x‖*x ≤ D+2*E*M) := by
  let φ := fun x : ℝ => (primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ)
  have hφ := detector_difference_smooth w z
  refine ⟨hW.mul hφ,?_,?_⟩
  · intro x
    change ‖W x*((primeDetectorCutoff (x/w):ℂ)-(primeDetectorCutoff (x/z):ℂ))‖ ≤ M
    rw [norm_mul]
    exact (mul_le_mul (hWnorm x) (detector_difference_norm w z x)
      (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
  · intro x hx
    have hdW := (hW.differentiable (by norm_num)).differentiableAt (x := x)
    have hdφ := (hφ.differentiable (by norm_num)).differentiableAt (x := x)
    change ‖deriv (fun x => W x*φ x) x‖*x ≤ _
    have he : deriv (fun t => W t*φ t) x = deriv W x*φ x+W x*deriv φ x := by
      exact deriv_fun_mul hdW hdφ
    rw [he]
    calc
      _ ≤ (‖deriv W x*φ x‖+‖W x*deriv φ x‖)*x :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) hx.le
      _ = (‖deriv W x‖*x)*‖φ x‖+‖W x‖*(‖deriv φ x‖*x) := by
        rw [norm_mul,norm_mul]
        ring
      _ ≤ D*1+M*(2*E) := add_le_add
        (mul_le_mul (hWderiv x hx) (detector_difference_norm w z x)
          (_root_.norm_nonneg _) hD)
        (mul_le_mul (hWnorm x) (detector_difference_deriv hdet hw hz hx)
          (mul_nonneg (_root_.norm_nonneg _) hx.le) hM)
      _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BoundedPrimeTuples
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformly bounded tuple lengths in the manuscript's actual
prime detector. The bound depends on xi, not on the envelope scale. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eventually_prime_tuple_norm_bound {ξ C : ℝ} (hC : 0 < C)
    {k : ℕ} (hk : 1 < ξ*(k:ℝ)) :
    ∀ᶠ X : ℝ in atTop, C*X < (X^ξ)^k := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    eventually_const_mul_rpow_le hk (2*C)] with X hX h
  rw [Real.rpow_one] at h
  rw [←Real.rpow_natCast,←Real.rpow_mul (zero_lt_one.trans hX).le]
  nlinarith [mul_pos hC (zero_lt_one.trans hX)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughDivisorBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

/-- Literal beta has a fixed bound, independent of the number of bin
primes. Only distinguished prime factors are counted in its divisor fibre. -/
theorem stoppedBeta_distinguished_rough_bound
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) (hW : ∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1)
    (R D : Finset Eisenstein) (hR : ∀ r ∈ R, primary r)
    {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 1 ≤ w) (hwz : w ≤ z)
    (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hs : Squarefree b) {k : ℕ}
    (hsize : norm b < w^k) :
    ‖stoppedBeta R D (distinguishedTupleCoefficient S W ψ w z) ψ w selected b‖ ≤
      (2^k:ℕ)*(‖((Fintype.card ι).factorial:ℂ)⁻¹‖ *
        ((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  rw [←stoppedBeta_filter_nonzero]
  apply stoppedBeta_rough_bound _ D
    (fun r hr => hR r (Finset.mem_filter.mp hr).1) hψ w hw
  · intro r hr p hp
    have hpr := primaryPrimeFactor_spec (hR r (Finset.mem_filter.mp hr).1) hp
    exact (distinguishedTupleCoefficient_prime_support S hS W hψone hψzero
      (zero_lt_one.trans_le hw) hwz (Finset.mem_filter.mp hr).2 hpr.1 hpr.2).1.le
  · positivity
  · intro r _
    exact distinguishedTupleCoefficient_norm S hS W hW hψ w z r
  · exact hb
  · exact hs
  · exact hsize

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma crossing_norm_interval {a S ell Z x : ℝ} (ha : 0 < a)
    (hS : 0 < S) (hell : 0 < ell) :
    (a*x*S/ell < Z ∧ Z ≤ a*x*S) ↔
      Z/(a*S) ≤ x ∧ x < Z*ell/(a*S) := by
  have hAS : 0 < a*S := mul_pos ha hS
  have he : a*x*S = x*(a*S) := by ring
  rw [he]
  constructor
  · rintro ⟨hu,hl⟩
    exact ⟨(div_le_iff₀ hAS).mpr (by nlinarith),
      (lt_div_iff₀ hAS).mpr ((div_lt_iff₀ hell).mp hu)⟩
  · rintro ⟨hl,hu⟩
    exact ⟨(div_lt_iff₀ hell).mpr ((lt_div_iff₀ hAS).mp hu),
      (div_le_iff₀ hAS).mp hl⟩

lemma distinguished_prime_crossing_interval {r p : Eisenstein}
    (hr : r ≠ 0) {S ell Z : ℝ} (hS : 0 < S) (hell : 0 < ell) :
    (norm (r*p)*S/ell < Z ∧ Z ≤ norm (r*p)*S) ↔
      Z/(norm r*S) ≤ norm p ∧ norm p < Z*ell/(norm r*S) := by
  rw [norm_mul_eq]
  exact crossing_norm_interval (norm_pos_of_ne_zero hr) hS hell

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeSelection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleCoordinate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing one distinguished coordinate is an exact finite bijection.
On squarefree prime tuples the largest-prime coordinate is unique. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma coordinateComplement_mem (S : ι → Finset Eisenstein) (i : ι) (g : ι → Eisenstein) :
    g ∈ coordinateComplementTuples S i ↔ g i = 1 ∧ ∀ j, j ≠ i → g j ∈ S j := by
  simp only [coordinateComplementTuples,Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · simpa only [Function.update_self,Finset.mem_singleton] using h i
    · intro j hj
      simpa only [Function.update_of_ne hj] using h j
  · rintro ⟨hi,h⟩ j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self,Finset.mem_singleton] using hi
    · simpa only [Function.update_of_ne hj] using h j hj

theorem primeTuple_coordinate_reindex (S : ι → Finset Eisenstein) (i : ι)
    (F : (ι → Eisenstein) → ℂ) :
    (∑ f ∈ Fintype.piFinset S, F f) =
      ∑ p ∈ S i, ∑ g ∈ coordinateComplementTuples S i, F (Function.update g i p) := by
  rw [←Finset.sum_product (S i) (coordinateComplementTuples S i)
    (fun t : Eisenstein × (ι → Eisenstein) => F (Function.update t.2 i t.1))]
  apply Finset.sum_bij (fun f _ => (f i,Function.update f i 1))
  · intro f hf
    refine Finset.mem_product.mpr ⟨(Fintype.mem_piFinset.mp hf) i,?_⟩
    apply (coordinateComplement_mem S i _).mpr
    refine ⟨Function.update_self _ _ _,?_⟩
    intro j hj
    simpa only [Function.update_of_ne hj] using (Fintype.mem_piFinset.mp hf) j
  · intro f hf g hg he
    have hp := congrArg Prod.fst he
    have hc := congrArg Prod.snd he
    dsimp only [Prod.fst] at hp
    dsimp only [Prod.snd] at hc
    calc
      f = Function.update (Function.update f i 1) i (f i) := by simp
      _ = Function.update (Function.update g i 1) i (g i) := by rw [hp,hc]
      _ = g := by simp
  · intro t ht
    obtain ⟨hp,hg⟩ := Finset.mem_product.mp ht
    obtain ⟨hgi,hgj⟩ := (coordinateComplement_mem S i t.2).mp hg
    refine ⟨Function.update t.2 i t.1,?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self] using hp
      · simpa only [Function.update_of_ne hji] using hgj j hji
    · apply Prod.ext
      · exact Function.update_self _ _ _
      · rw [Function.update_idem,←hgi,Function.update_eq_self]
  · intro f hf
    simp only [Function.update_idem,Function.update_eq_self]

lemma primeTuple_update_product (f : ι → Eisenstein) (i : ι) (p : Eisenstein) :
    (∏ j, Function.update f i p j) = p*(∏ j ∈ Finset.univ.erase i, f j) := by
  rw [←Finset.mul_prod_erase Finset.univ (Function.update f i p) (Finset.mem_univ i),
    Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact Function.update_of_ne (Finset.mem_erase.mp hj).1 p f

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeComplementFibers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed multiplicity for the actual tuple remaining after a distinguished
coordinate is removed. The unit coordinate stays explicit. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complementTuple_primary (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    {g : ι → Eisenstein} (hg : g ∈ coordinateComplementTuples S i) :
    primary (∏ j, g j) := by
  obtain ⟨hgi,hg⟩ := (coordinateComplement_mem S i g).mp hg
  apply primary_finset_prod
  intro j _
  by_cases hj : j = i
  · simpa only [hj,hgi] using primary_one
  · exact (hS j (g j) (hg j hj)).1

lemma complementTuple_range_subset (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    {f g : ι → Eisenstein} (hf : f ∈ coordinateComplementTuples S i)
    (hg : g ∈ coordinateComplementTuples S i)
    (hprod : (∏ j, g j) = ∏ j, f j) (j : ι) :
    g j ∈ Finset.univ.image f := by
  obtain ⟨hfi,hf⟩ := (coordinateComplement_mem S i f).mp hf
  obtain ⟨hgi,hg⟩ := (coordinateComplement_mem S i g).mp hg
  by_cases hji : j = i
  · exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simpa only [hji,hgi] using hfi⟩
  · have hp := hS j (g j) (hg j hji)
    have hd : g j ∣ ∏ k, f k := hprod ▸ Finset.dvd_prod_of_mem g (Finset.mem_univ j)
    obtain ⟨k,_,hk⟩ := (hp.2.dvd_finsetProd_iff f).mp hd
    have hki : k ≠ i := by
      intro he
      rw [he,hfi] at hk
      exact hp.2.not_isUnit (isUnit_of_dvd_one hk)
    have hpk := hS k (f k) (hf k hki)
    have he : g j = f k := primary_associated_eq hp.1 hpk.1
      ((hp.2.dvd_prime_iff_associated hpk.2).mp hk)
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,he.symm⟩

theorem complementTuple_fiber_card (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι) (r : Eisenstein) :
    ((coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r)).card ≤
      (Fintype.card ι)^(Fintype.card ι) := by
  let T := (coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r)
  by_cases hT : T.Nonempty
  · obtain ⟨f,hf⟩ := hT
    obtain ⟨hfs,hfr⟩ := Finset.mem_filter.mp hf
    have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.univ.image f) := by
      intro g hg
      obtain ⟨hgs,hgr⟩ := Finset.mem_filter.mp hg
      apply Fintype.mem_piFinset.mpr
      exact complementTuple_range_subset S hS i hfs hgs (hgr.trans hfr.symm)
    calc
      T.card ≤ (Fintype.piFinset (fun _ : ι => Finset.univ.image f)).card := Finset.card_le_card hsub
      _ = ((Finset.univ.image f).card)^(Fintype.card ι) := by simp [Fintype.card_piFinset]
      _ ≤ _ := Nat.pow_le_pow_left (by
        simpa using (Finset.card_image_le (s := (Finset.univ : Finset ι)) (f := f))) _
  · change T.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.card_empty]
    exact Nat.zero_le _

lemma complementTuple_prime_factor (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    {g : ι → Eisenstein} (hg : g ∈ coordinateComplementTuples S i)
    {p : Eisenstein} (hp : primaryPrime p) (hpd : p ∣ ∏ j, g j) :
    ∃ j, j ≠ i ∧ p = g j := by
  obtain ⟨hgi,hg⟩ := (coordinateComplement_mem S i g).mp hg
  obtain ⟨j,_,hj⟩ := (hp.2.dvd_finsetProd_iff g).mp hpd
  have hji : j ≠ i := by
    intro he
    rw [he,hgi] at hj
    exact hp.2.not_isUnit (isUnit_of_dvd_one hj)
  exact ⟨j,hji,primary_associated_eq hp.1 (hS j (g j) (hg j hji)).1
    ((hp.2.dvd_prime_iff_associated (hS j (g j) (hg j hji)).2).mp hj)⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ComplementAbsoluteWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegative uncollected tuple weights. These retain the absolute
complementary mass; no cancellation of collected coefficients is used. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complementAbsoluteWeight_nonneg (S : ι → Finset Eisenstein) (i : ι)
    (W : ι → Eisenstein → ℂ) (r : Eisenstein) :
    0 ≤ complementAbsoluteWeight S i W r :=
  Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => _root_.norm_nonneg _))

lemma complementAbsoluteWeight_bound (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → Eisenstein → ℂ) (hW : ∀ j, ∀ p ∈ S j, ‖W j p‖ ≤ 1) (r : Eisenstein) :
    complementAbsoluteWeight S i W r ≤ ((Fintype.card ι)^(Fintype.card ι):ℕ) := by
  unfold complementAbsoluteWeight
  calc
    _ ≤ ∑ _g ∈ (coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro g hg
      have hgs := (coordinateComplement_mem S i g).mp (Finset.mem_filter.mp hg).1
      apply Finset.prod_le_one (fun _ _ => _root_.norm_nonneg _)
      intro j hj
      exact hW j (g j) (hgs.2 j (Finset.mem_erase.mp hj).1)
    _ = (((coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r)).card:ℝ) := by simp
    _ ≤ _ := Nat.cast_le.mpr (complementTuple_fiber_card S hS i r)

lemma complementAbsoluteWeight_rough (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → Eisenstein → ℂ) {w : ℝ}
    (hrough : ∀ j, j ≠ i → ∀ p ∈ S j, W j p ≠ 0 → w ≤ norm p)
    {r p : Eisenstein} (hr : complementAbsoluteWeight S i W r ≠ 0)
    (hp : primaryPrime p) (hpr : p ∣ r) : w ≤ norm p := by
  obtain ⟨g,hg,hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  obtain ⟨hg,hgr⟩ := Finset.mem_filter.mp hg
  have hpd : p ∣ ∏ j, g j := by rw [hgr]; exact hpr
  obtain ⟨j,hji,hpj⟩ := complementTuple_prime_factor S hS i hg hp hpd
  have hnorm : ‖W j (g j)‖ ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ _⟩)
  have hWj : W j (g j) ≠ 0 := norm_ne_zero_iff.mp hnorm
  rw [hpj]
  exact hrough j hji (g j) (((coordinateComplement_mem S i g).mp hg).2 j hji) hWj

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ComplementAbsoluteMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear complementary mass after a distinguished prime is removed.
The absolute tuple weights are collected before applying rough divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complementProductSupport_primary (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    {r : Eisenstein} (hr : r ∈ complementProductSupport S i) : primary r := by
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hr
  exact complementTuple_primary S hS i hg

theorem complement_absolute_pair_mass (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → Eisenstein → ℂ) (hW : ∀ j, ∀ p ∈ S j, ‖W j p‖ ≤ 1)
    (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d) {Y w : ℝ}
    (hY : 0 ≤ Y) (hw : 1 ≤ w)
    (hrough : ∀ j, j ≠ i → ∀ p ∈ S j, W j p ≠ 0 → w ≤ norm p)
    {m : ℕ} (hsize : Y < w^m) :
    (∑ t ∈ (complementProductSupport S i ×ˢ D).filter
      (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y),
      complementAbsoluteWeight S i W t.1) ≤
      18*Y*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  let R := (complementProductSupport S i).filter
    (fun r => complementAbsoluteWeight S i W r ≠ 0)
  let f : Eisenstein → ℂ := fun r => (complementAbsoluteWeight S i W r : ℂ)
  have hf (r : Eisenstein) : ‖f r‖ = complementAbsoluteWeight S i W r := by
    simp only [f,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (complementAbsoluteWeight_nonneg S i W r)]
  have hbound := stopped_complement_mass R D
    (fun r hr => complementProductSupport_primary S hS i (Finset.mem_filter.mp hr).1) hD f
    (show 0 ≤ (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ) by positivity) hY
    (fun r _ => by rw [hf]; exact complementAbsoluteWeight_bound S hS i W hW r) hw
    (fun r hr p hp => complementAbsoluteWeight_rough S hS i W hrough
      (Finset.mem_filter.mp hr).2
      (primaryPrimeFactor_spec
        (complementProductSupport_primary S hS i (Finset.mem_filter.mp hr).1) hp).1
      (primaryPrimeFactor_spec
        (complementProductSupport_primary S hS i (Finset.mem_filter.mp hr).1) hp).2) hsize
  simp only [hf] at hbound
  apply le_trans ?_ hbound
  apply le_of_eq
  symm
  apply Finset.sum_subset
  · intro t ht
    obtain ⟨ht,hcond⟩ := Finset.mem_filter.mp ht
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hr).1,hd⟩,hcond⟩
  · intro t ht hn
    obtain ⟨ht,hcond⟩ := Finset.mem_filter.mp ht
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    by_contra hne
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hr,hne⟩,hd⟩,hcond⟩)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ComplementAbsoluteCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of absolute tuple weights by their primary product.
This is a finite identity, before any cancellation estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complement_absolute_collection (S : ι → Finset Eisenstein) (i : ι)
    (W : ι → Eisenstein → ℂ) (F : Eisenstein → ℝ) :
    (∑ g ∈ coordinateComplementTuples S i,
      (∏ j ∈ Finset.univ.erase i, ‖W j (g j)‖)*F (∏ j, g j)) =
    ∑ r ∈ complementProductSupport S i, complementAbsoluteWeight S i W r*F r := by
  calc
    _ = ∑ r ∈ complementProductSupport S i,
        ∑ g ∈ (coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r),
          (∏ j ∈ Finset.univ.erase i, ‖W j (g j)‖)*F (∏ j, g j) := by
      exact (Finset.sum_fiberwise_of_maps_to
        (fun g hg => Finset.mem_image.mpr ⟨g,hg,rfl⟩) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      unfold complementAbsoluteWeight
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g hg
      rw [(Finset.mem_filter.mp hg).2]

theorem complement_absolute_tuple_mass (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → Eisenstein → ℂ) (hW : ∀ j, ∀ p ∈ S j, ‖W j p‖ ≤ 1)
    (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d) {Y w : ℝ}
    (hY : 0 ≤ Y) (hw : 1 ≤ w)
    (hrough : ∀ j, j ≠ i → ∀ p ∈ S j, W j p ≠ 0 → w ≤ norm p)
    {m : ℕ} (hsize : Y < w^m) :
    (∑ t ∈ (coordinateComplementTuples S i ×ˢ D).filter
      (fun t => Squarefree ((∏ j, t.1 j)*t.2) ∧ norm ((∏ j, t.1 j)*t.2) ≤ Y),
      ∏ j ∈ Finset.univ.erase i, ‖W j (t.1 j)‖) ≤
      18*Y*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  apply le_trans ?_ (complement_absolute_pair_mass S hS i W hW D hD hY hw hrough hsize)
  apply le_of_eq
  rw [Finset.sum_filter,Finset.sum_product,Finset.sum_filter,Finset.sum_product]
  rw [Finset.sum_comm,Finset.sum_comm (s := complementProductSupport S i)]
  apply Finset.sum_congr rfl
  intro d hd
  have hc := complement_absolute_collection S i W
    (fun r => if Squarefree (r*d) ∧ norm (r*d) ≤ Y then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero] using hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedComplementMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary tuple mass for the literal smooth distinguished
weights. Their rough support is proved from the detector difference. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma distinguishedRadialWeight_eq_primeWeight (W : ℝ → ℂ) (w z : ℝ) (p : Eisenstein) :
    distinguishedRadialWeight W w z (norm p) =
      W (norm p)*distinguishedPrimeWeight primeDetectorCutoff w z p := by
  simp only [distinguishedRadialWeight,distinguishedPrimeWeight,Complex.ofReal_sub]

lemma distinguishedRadialWeight_prime_rough (W : ℝ → ℂ) {w z : ℝ}
    (hw : 0 < w) (hwz : w ≤ z) {p : Eisenstein} (hp : primaryPrime p)
    (hne : distinguishedRadialWeight W w z (norm p) ≠ 0) : w < norm p := by
  rw [distinguishedRadialWeight_eq_primeWeight] at hne
  exact (distinguishedPrimeWeight_support
    (fun _ _ hx => primeDetectorCutoff_one hx) (fun _ hx => primeDetectorCutoff_zero hx)
    hw hwz (norm_pos_of_ne_zero hp.2.ne_zero) (mul_ne_zero_iff.mp hne).2).1

theorem distinguished_complement_tuple_mass (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → ℝ → ℂ) (hW : ∀ j x, ‖W j x‖ ≤ 1)
    (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d) {Y w z : ℝ}
    (hY : 0 ≤ Y) (hw : 1 ≤ w) (hwz : w ≤ z)
    {m : ℕ} (hsize : Y < w^m) :
    (∑ t ∈ (coordinateComplementTuples S i ×ˢ D).filter
      (fun t => Squarefree ((∏ j, t.1 j)*t.2) ∧ norm ((∏ j, t.1 j)*t.2) ≤ Y),
      ∏ j ∈ Finset.univ.erase i,
        ‖distinguishedRadialWeight (W j) w z (norm (t.1 j))‖) ≤
      18*Y*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  apply complement_absolute_tuple_mass S hS i
    (fun j p => distinguishedRadialWeight (W j) w z (norm p)) ?_ D hD hY hw ?_ hsize
  · intro j p hp
    rw [distinguishedRadialWeight,norm_mul]
    exact (mul_le_mul (hW j (norm p)) (detector_difference_norm w z (norm p))
      (_root_.norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  · intro j _ p hp hne
    exact (distinguishedRadialWeight_prime_rough (W j)
      (zero_lt_one.trans_le hw) hwz (hS j p hp) hne).le

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

/-- If the free prime is distinguished, the actual stopping inequalities
are a single norm interval; the selected divisor remains fixed. -/
theorem stoppingSideTest_free_distinguished_interval
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k : ℕ) (Z : ℝ)
    {c : Eisenstein} (hc : c ≠ 0) (d p : Eisenstein)
    (hell : 0 < ell j)
    (hS : 0 < primeSurrogate (primaryPrimeFactors d) bin ell) :
    stoppingSideTest bin ell j k Z (c*p) d ↔
      (∀ q ∈ primaryPrimeFactors d, bin q ≤ j) ∧
      (primeBin (primaryPrimeFactors d) bin j).card = k ∧
      Z/(norm c*primeSurrogate (primaryPrimeFactors d) bin ell) ≤ norm p ∧
      norm p < Z*ell j/(norm c*primeSurrogate (primaryPrimeFactors d) bin ell) := by
  unfold stoppingSideTest stoppingPrimeSetTest
  rw [distinguished_prime_crossing_interval hc hS hell]

lemma failedStage_free_distinguished_interval {c p : Eisenstein} (hc : c ≠ 0)
    {S Q : ℝ} (hS : 0 < S) :
    norm (c*p)*S < Q ↔ norm p < Q/(norm c*S) := by
  rw [norm_mul_eq,lt_div_iff₀ (mul_pos (norm_pos_of_ne_zero hc) hS)]
  ring_nf

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeRoles
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The largest prime of a squarefree stopped product occurs on exactly
one side. This is the exact split into distinguished and selected-bin
roles before reindexing the free prime. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_factor_unique_side {p r d : Eisenstein} (hp : Prime p)
    (hs : Squarefree (r*d)) (hd : p ∣ r*d) :
    (p ∣ r ∧ ¬p ∣ d) ∨ (p ∣ d ∧ ¬p ∣ r) := by
  have hcop : IsCoprime r d :=
    isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
  rcases hp.dvd_or_dvd hd with hr | hd
  · exact Or.inl ⟨hr,fun hd => hp.not_isUnit (hcop.isUnit_of_dvd' hr hd)⟩
  · exact Or.inr ⟨hd,fun hr => hp.not_isUnit (hcop.isUnit_of_dvd' hr hd)⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateRoles
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished largest-prime role splits into the actual tuple
coordinates with multiplicity one, even in the presence of the selected
divisor. No ordering of its prime factors is introduced. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma prime_tuple_divisor_indicator (f : ι → Eisenstein)
    (hf : ∀ i, primaryPrime (f i)) (hi : Function.Injective f)
    {p : Eisenstein} (hp : primaryPrime p) (z : ℂ) :
    (if p ∣ ∏ i, f i then z else 0) = ∑ i, if p = f i then z else 0 := by
  by_cases hdiv : p ∣ ∏ i, f i
  · obtain ⟨i,_,hpi⟩ := (hp.2.dvd_finsetProd_iff f).mp hdiv
    have he : p = f i := primary_associated_eq hp.1 (hf i).1
      ((hp.2.dvd_prime_iff_associated (hf i).2).mp hpi)
    rw [ite_eq_left hdiv]
    symm
    calc
      _ = (if p = f i then z else 0) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          have hne : ¬p = f j := fun hpj => hji (hi (hpj.symm.trans he))
          exact ite_eq_right hne
        · intro hnot
          exact (hnot (Finset.mem_univ i)).elim
      _ = z := ite_eq_left he
  · rw [ite_eq_right hdiv]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply ite_eq_right
    intro he
    apply hdiv
    rw [he]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)

/-- A squarefree full product has exactly one distinguished coordinate
when its canonical largest prime lies on the distinguished side. -/
theorem distinguished_largest_coordinate_roles [Nonempty ι]
    (f : ι → Eisenstein) (hf : ∀ i, primaryPrime (f i))
    {d : Eisenstein} (hd : primary d) (hs : Squarefree ((∏ i, f i)*d)) (z : ℂ) :
    (if largestPrimeChoice ((∏ i, f i)*d) ∣ ∏ i, f i then z else 0) =
      ∑ i, if largestPrimeChoice ((∏ i, f i)*d) = f i then z else 0 := by
  have hr : primary (∏ i, f i) :=
    primary_finset_prod Finset.univ f (fun i _ => (hf i).1)
  have hi := (squarefree_prime_tuple_iff f hf).mp (squarefree_mul_iff.mp hs).2.1
  let i : ι := Classical.arbitrary ι
  have him : f i ∈ primaryPrimeFactors ((∏ j, f j)*d) :=
    (primaryPrime_mem_factors_iff (primary_mul hr hd)).mpr
      ⟨hf i,(Finset.dvd_prod_of_mem f (Finset.mem_univ i)).trans (dvd_mul_right _ _)⟩
  have hne : (primaryPrimeFactors ((∏ j, f j)*d)).Nonempty := ⟨f i,him⟩
  exact prime_tuple_divisor_indicator f hf hi
    (primaryPrimeFactor_spec (primary_mul hr hd) (largestPrimeChoice_spec hne).1).1 z

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedCoordinateReindex
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact free-coordinate expansion of the distinguished largest-prime
role. The global largest prime is retained, including the selected divisor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeTuple_update_weight (f : ι → Eisenstein) (i : ι) (p : Eisenstein)
    (w : ι → Eisenstein → ℂ) :
    (∏ j, w j (Function.update f i p j)) = w i p*(∏ j ∈ Finset.univ.erase i, w j (f j)) := by
  rw [←Finset.mul_prod_erase Finset.univ (fun j => w j (Function.update f i p j))
    (Finset.mem_univ i),Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem distinguished_tuple_largest_reindex [Nonempty ι]
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    {d : Eisenstein} (hd : primary d) (F : (ι → Eisenstein) → ℂ) :
    (∑ f ∈ (Fintype.piFinset S).filter (fun f => Squarefree ((∏ i, f i)*d)),
      if largestPrimeChoice ((∏ i, f i)*d) ∣ ∏ i, f i then F f else 0) =
      ∑ i, ∑ g ∈ coordinateComplementTuples S i, ∑ p ∈ S i,
        if Squarefree ((∏ j, Function.update g i p j)*d) ∧
          largestPrimeChoice ((∏ j, Function.update g i p j)*d) = p
        then F (Function.update g i p) else 0 := by
  rw [Finset.sum_filter]
  calc
    _ = ∑ f ∈ Fintype.piFinset S, ∑ i,
        if Squarefree ((∏ j, f j)*d) ∧ largestPrimeChoice ((∏ j, f j)*d) = f i
        then F f else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hs : Squarefree ((∏ j, f j)*d)
      · simpa only [hs,ite_true, if_true,true_and] using
          distinguished_largest_coordinate_roles f
            (fun i => hS i (f i) ((Fintype.mem_piFinset.mp hf) i)) hd hs (F f)
      · simp only [hs,false_and,ite_false, if_false,Finset.sum_const_zero]
    _ = ∑ i, ∑ f ∈ Fintype.piFinset S,
        if Squarefree ((∏ j, f j)*d) ∧ largestPrimeChoice ((∏ j, f j)*d) = f i
        then F f else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [primeTuple_coordinate_reindex S i]
      rw [Finset.sum_comm]
      simp only [Function.update_self]

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

theorem stoppedSideTest_free_distinguished_interval
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k h : ℕ) (Z Q : ℝ) (early : Bool)
    {c : Eisenstein} (hc : c ≠ 0) (d p : Eisenstein) (hell : 0 < ell j)
    (hS : 0 < primeSurrogate (primaryPrimeFactors d) bin ell)
    (hE : 0 < primeSurrogate (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell) :
    stoppedSideTest bin ell j k h Z Q early (c*p) d ↔
      ((∀ q ∈ primaryPrimeFactors d, bin q ≤ j) ∧
      (primeBin (primaryPrimeFactors d) bin j).card = k ∧
      Z/(norm c*primeSurrogate (primaryPrimeFactors d) bin ell) ≤ norm p ∧
      norm p < Z*ell j/(norm c*primeSurrogate (primaryPrimeFactors d) bin ell)) ∧
      (early = true ∨ norm p < Q/(norm c*
        primeSurrogate (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell)) := by
  unfold stoppedSideTest
  rw [stoppingSideTest_free_distinguished_interval bin ell j k Z hc d p hell hS,
    failedStage_free_distinguished_interval hc hE]

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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SelectedPrimeGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDistinguishedIntervals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distinguished-coordinate stopping region is the
intersection of four norm bounds. All surrogate products here are
computed from the fixed selected divisor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma geometricPrimeSurrogate_pos {ρ B : ℝ} (hρ : 0 < ρ)
    (S : Finset Eisenstein) (bin : Eisenstein → ℕ) :
    0 < primeSurrogate S bin (geometricBinLower ρ B) := by
  unfold primeSurrogate
  exact Finset.prod_pos (fun p _ => pow_pos hρ _)

theorem stopped_distinguished_interval_iff {B ρ a b : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool)
    {c d p : Eisenstein} (hc : primary c) (hd : primary d)
    (hp : primaryPrime p) (hpB : norm p ≤ B) :
    let S := primeSurrogate (primaryPrimeFactors d) (geometricPrimeBin ρ B) (geometricBinLower ρ B)
    let E := primeSurrogate (primeBinPrefix (primaryPrimeFactors d) (geometricPrimeBin ρ B) h)
      (geometricPrimeBin ρ B) (geometricBinLower ρ B)
    let P := geometricBinLower ρ B j
    (geometricPrimeBin ρ B p = j ∧
      (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
      stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early (c*p) d) ↔
    ((∀ q ∈ primaryPrimeFactors d, geometricPrimeBin ρ B q ≤ j₀) ∧
      (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ B) j₀).card = k) ∧
      (a/norm (c*d) < norm p ∧
      max P (Z/(norm c*S)) ≤ norm p ∧
      norm p < min (ρ*P) (min (Z*geometricBinLower ρ B j₀/(norm c*S))
        (if early = true then ρ*P else Q/(norm c*E))) ∧
      norm p ≤ b/norm (c*d)) := by
  dsimp only
  have hS := geometricPrimeSurrogate_pos (B := B) (zero_lt_one.trans hρ)
    (primaryPrimeFactors d) (geometricPrimeBin ρ B)
  have hE := geometricPrimeSurrogate_pos (B := B) (zero_lt_one.trans hρ)
    (primeBinPrefix (primaryPrimeFactors d) (geometricPrimeBin ρ B) h) (geometricPrimeBin ρ B)
  have hnorm : (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ↔
      a/norm (c*d) < norm p ∧ norm p ≤ b/norm (c*d) := by
    rw [mul_assoc]
    exact selectedPrime_norm_interval (primary_ne_zero hc) (primary_ne_zero hd) p a b
  rw [geometricPrimeBin_eq_iff hρ hρ₂ hj hp hpB,hnorm,
    stoppedSideTest_free_distinguished_interval (geometricPrimeBin ρ B) (geometricBinLower ρ B)
      j₀ k h Z Q early (primary_ne_zero hc) d p (pow_pos (zero_lt_one.trans hρ) _) hS hE]
  by_cases hearly : early = true
  · simp only [hearly,true_or,ite_true, if_true,max_le_iff,lt_min_iff]
    tauto
  · simp only [hearly,max_le_iff,lt_min_iff]
    tauto

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongDistinguishedPrime
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distinguished-coordinate prime sum follows from the
published prime input and the derived smooth detector variation. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_distinguished_prime_bound (hSW : KummerPrimeSiegelWalfisz)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v‖ ≤
        K*P/T^D*((M+V)*(1+|u|)) := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := long_prime_interval_bound hSW hA hD
  obtain ⟨E,hE,hdet⟩ := primeDetectorCutoff_radial_deriv_bound
  refine ⟨2*C*(3+2*E),P₀,by positivity,hP₀,?_⟩
  intro T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV W hW hWn hWd v hv hnc hNv
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le hP)
  obtain ⟨hsmooth,hnorm,hder⟩ := distinguishedRadialWeight_bounds W hW hM hV hE hw hz hWn hWd hdet
  obtain ⟨hdiff,hint,hvar⟩ := radial_mellin_interval_variation hsmooth hP0 (by norm_num)
    ha hab hb hM (by positivity) hnorm hder u
  have hU : 0 ≤ |u| := abs_nonneg u
  have hfac : 1 ≤ 2+2*E+|u| := by linarith
  have hfac' : 2+2*E+|u| ≤ (3+2*E)*(1+|u|) := by
    nlinarith [mul_nonneg (show 0 ≤ 2+2*E by positivity) hU]
  have hvar' : 2*M+(2-1)*((V+2*E*M)+M*|u|) ≤
      (3+2*E)*((M+V)*(1+|u|)) := by
    calc
      _ = (2+2*E+|u|)*M+V := by ring
      _ ≤ (2+2*E+|u|)*M+(2+2*E+|u|)*V :=
        add_le_add le_rfl (le_mul_of_one_le_left hV hfac)
      _ = (2+2*E+|u|)*(M+V) := by ring
      _ ≤ ((3+2*E)*(1+|u|))*(M+V) :=
        mul_le_mul_of_nonneg_right hfac' (add_nonneg hM hV)
      _ = _ := by ring
  calc
    _ ≤ (C*(2*P)/T^D)*(2*M+(2-1)*((V+2*E*M)+M*|u|)) :=
      (hbound T P 2 a b hT hP hTP ha hab hb v hv hnc hNv _ hdiff hint).trans
        (mul_le_mul_of_nonneg_left hvar (by positivity))
    _ ≤ (C*(2*P)/T^D)*((3+2*E)*((M+V)*(1+|u|))) :=
      mul_le_mul_of_nonneg_left hvar' (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongDistinguishedSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exclusion and arbitrary logarithmic saving for the actual smooth
weight of a distinguished free prime. The bounds retain the derivative
cost and are uniform in the two detector scales. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_distinguished_prime_excluded_bound (hSW : KummerPrimeSiegelWalfisz)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ T^A → e ≠ 0 →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p e),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v‖ ≤
        K*P/T^D*((M+V)*(1+|u|))+M*(Real.log (norm e)/Real.log 2) := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_distinguished_prime_bound hSW hA hD
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV W hW hWn hWd v e hv hnc hNv he
  let S := (primeCutoff b).filter (fun p => a < norm p)
  let f := fun p : Eisenstein =>
    distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ M := by
    dsimp [f,distinguishedRadialWeight]
    rw [norm_mul,norm_mul,norm_mul,mellinPhase_norm,mul_one]
    have hfirst : ‖W (norm p)‖*
        ‖(primeDetectorCutoff (norm p/w):ℂ)-(primeDetectorCutoff (norm p/z):ℂ)‖ ≤ M := by
      exact (mul_le_mul (hWn _) (detector_difference_norm w z (norm p))
        (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
    exact (mul_le_mul hfirst (norm_cubicSymbol_le_one (hS p hp).1 v)
      (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
  have hex := prime_exclusion_logarithmic S hS e he f hM hf
  change ‖∑ p ∈ S with IsCoprime p e, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S, f p‖+
        ‖(∑ p ∈ S, f p)-(∑ p ∈ S with IsCoprime p e, f p)‖ :=
      norm_le_norm_add_norm_sub _ _
    _ ≤ K*P/T^D*((M+V)*(1+|u|))+M*(Real.log (norm e)/Real.log 2) :=
      add_le_add (hbound T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV W
        hW hWn hWd v hv hnc hNv) hex

theorem long_distinguished_prime_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ T^A → e ≠ 0 → Real.log (norm e) ≤ T^E →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p e),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_distinguished_prime_excluded_bound hSW hA
    (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hD hF) hH)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := (Real.log 2)⁻¹) (D := D) (E := F+E)
      (inv_nonneg.mpr hlog2.le) hD.le (add_nonneg hF hE))
  refine ⟨2*K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV hu hMV W hW hWn hWd
    v e hv hnc hNv he hNe
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  have hheight : 1+|u| ≤ 2*T^H := by
    linarith [Real.one_le_rpow hT hH]
  have hMbound : M ≤ T^F := (le_add_of_nonneg_right hV).trans hMV
  have hmain : K*P/T^(D+F+H)*((M+V)*(1+|u|)) ≤ 2*K*P/T^D := by
    calc
      _ ≤ K*P/T^(D+F+H)*(T^F*(2*T^H)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hMV hheight
          (by positivity) (Real.rpow_nonneg hT0.le _)) (by positivity)
      _ = _ := by
        rw [Real.rpow_add hT0,Real.rpow_add hT0]
        field_simp
  have herror : M*(Real.log (norm e)/Real.log 2) ≤ P/T^D := by
    calc
      _ ≤ T^F*(T^E/Real.log 2) := mul_le_mul hMbound
        ((div_le_div_iff_of_pos_right hlog2).mpr hNe)
        (div_nonneg (Real.log_nonneg (one_le_norm he)) hlog2.le)
        (Real.rpow_nonneg hT0.le _)
      _ = (Real.log 2)⁻¹*T^(F+E) := by rw [Real.rpow_add hT0]; ring
      _ ≤ _ := hP₁ P ((le_max_right _ _).trans hP) T hT hTP
  apply (hbound T P a b w z u M V hT ((le_max_left _ _).trans hP) hTP ha hab hb
    hw hz hM hV W hW hWn hWd v e hv hnc hNv he).trans
  calc
    _ ≤ 2*K*P/T^D+P/T^D := add_le_add hmain herror
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongDistinguishedContext
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A distinguished free prime is cancelled with the actual largest-prime
tie rule relative to the entire fixed complement. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_distinguished_context_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ (v e : Eisenstein) (C : Finset Eisenstein), v ≠ 0 →
      (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
      Real.log (norm e) ≤ T^E →
      ‖∑ p ∈ (((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p e)).filter (fun p => largestPrimePredicate primeTieCode C p),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_distinguished_prime_saving hSW hA hD hH hE hF
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := 4) (D := D) (E := F)
      (by norm_num) hD.le hF)
  refine ⟨K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P a b w z u M V hT hP hTP ha hab hb hw hz hM hV hu hMV W hW hWn hWd
    v e C hv hnc hNv he hNe
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  let S := ((primeCutoff b).filter (fun p => a < norm p)).filter (fun p => IsCoprime p e)
  let f := fun p : Eisenstein =>
    distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v
  let m : ℝ := ((C.sup normNat:ℕ):ℝ)
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ M := by
    dsimp [f,distinguishedRadialWeight]
    rw [norm_mul,norm_mul,norm_mul,mellinPhase_norm,mul_one]
    have hfirst : ‖W (norm p)‖*
        ‖(primeDetectorCutoff (norm p/w):ℂ)-(primeDetectorCutoff (norm p/z):ℂ)‖ ≤ M :=
      (mul_le_mul (hWn _) (detector_difference_norm w z (norm p))
        (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
    exact (mul_le_mul hfirst (norm_cubicSymbol_le_one (hS p hp).1 v)
      (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
  have hend := largestPrime_endpoint_difference primeTieCode C S hS f hM hf
  have hinterval : (∑ p ∈ S with m < norm p, f p) =
      ∑ p ∈ ((primeCutoff b).filter (fun p => max a m < norm p)).filter
        (fun p => IsCoprime p e), f p := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [S,Finset.mem_filter,max_lt_iff]
    tauto
  have hsum : ‖∑ p ∈ S with m < norm p, f p‖ ≤ K*P/T^D := by
    rw [hinterval]
    by_cases hm : max a m ≤ b
    · exact hbound T P (max a m) b w z u M V hT ((le_max_left _ _).trans hP) hTP
        (ha.trans (le_max_left _ _)) hm hb hw hz hM hV hu hMV W hW hWn hWd
        v e hv hnc hNv he hNe
    · have hempty : ((primeCutoff b).filter (fun p => max a m < norm p)).filter
          (fun p => IsCoprime p e) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hp,_⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp,hl⟩ := Finset.mem_filter.mp hp
        exact hm (hl.le.trans (mem_primeCutoff.mp hp).2)
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have hfour : 4*M ≤ P/T^D :=
    (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right hV).trans hMV) (by norm_num)).trans
      (hP₁ P ((le_max_right _ _).trans hP) T hT hTP)
  change ‖∑ p ∈ S with largestPrimePredicate primeTieCode C p, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S with m < norm p, f p‖+
        ‖(∑ p ∈ S with largestPrimePredicate primeTieCode C p, f p)-
          (∑ p ∈ S with m < norm p, f p)‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ K*P/T^D+4*M := add_le_add hsum hend
    _ ≤ K*P/T^D+P/T^D := add_le_add le_rfl hfour
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeMixedInterval
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intersections of the half-open norm restrictions arising from the
crossing test differ from the prime interval convention only at their
two final endpoints. -/
noncomputable section
namespace CubicFirstMoment

lemma mixed_norm_interval_away {a l b h x : ℝ}
    (hlo : x ≠ max a l) (hhi : x ≠ min b h) :
    (a < x ∧ l ≤ x ∧ x < b ∧ x ≤ h) ↔ max a l < x ∧ x ≤ min b h := by
  constructor
  · rintro ⟨ha,hl,hb,hh⟩
    refine ⟨?_,le_min hb.le hh⟩
    have hmx : max a l ≤ x := max_le ha.le hl
    exact lt_of_le_of_ne hmx hlo.symm
  · rintro ⟨hl,hh⟩
    have ha : a < x := (le_max_left _ _).trans_lt hl
    have hle : l ≤ x := ((le_max_right _ _).trans_lt hl).le
    have hb : x ≤ b := hh.trans (min_le_left _ _)
    have hstrict : x < b := by
      by_contra hn
      have hxb : x = b := le_antisymm hb (le_of_not_gt hn)
      have hxh : x ≤ h := hh.trans (min_le_right _ _)
      have hmin : min b h = x := by rw [←hxb,min_eq_left hxh]
      exact hhi hmin.symm
    exact ⟨ha,hle,hstrict,hh.trans (min_le_right _ _)⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongDistinguishedInterval
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The half-open intersections supplied by the actual stopping tests
inherit prime cancellation. Only the two final endpoint norms are lost. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem long_distinguished_mixed_interval_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P B a l b h w z u M V : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ max a l → min b h ≤ 2*P → 0 < w → 0 < z → 0 ≤ M → 0 ≤ V →
      |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, ‖W x‖ ≤ M) → (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ (v e : Eisenstein) (C : Finset Eisenstein), v ≠ 0 →
      (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      Real.log (norm e) ≤ T^E →
      ‖∑ p ∈ (((primeCutoff B).filter (fun p => IsCoprime p e)).filter
          (fun p => largestPrimePredicate primeTieCode C p)).filter
          (fun p => a < norm p ∧ l ≤ norm p ∧ norm p < b ∧ norm p ≤ h),
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_distinguished_context_saving hSW hA hD hH hE hF
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := 4) (D := D) (E := F)
      (by norm_num) hD.le hF)
  refine ⟨K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P B a l b h w z u M V hT hP hTP hlow hupp hw hz hM hV hheight hMV W hW hWn hWd
    v e C hv hnc hNv he hNe
  have hPpos : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  let S := ((primeCutoff B).filter (fun p => IsCoprime p e)).filter
    (fun p => largestPrimePredicate primeTieCode C p)
  let f := fun p : Eisenstein =>
    distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ M := by
    dsimp [f,distinguishedRadialWeight]
    rw [norm_mul,norm_mul,norm_mul,mellinPhase_norm,mul_one]
    have hfirst : ‖W (norm p)‖*
        ‖(primeDetectorCutoff (norm p/w):ℂ)-(primeDetectorCutoff (norm p/z):ℂ)‖ ≤ M :=
      (mul_le_mul (hWn _) (detector_difference_norm w z (norm p))
        (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
    exact (mul_le_mul hfirst (norm_cubicSymbol_le_one (hS p hp).1 v)
      (_root_.norm_nonneg _) hM).trans_eq (mul_one M)
  have hend := prime_interval_endpoint_difference S hS
    (fun p => a < norm p ∧ l ≤ norm p ∧ norm p < b ∧ norm p ≤ h)
    (fun p => max a l < norm p ∧ norm p ≤ min b h) (max a l) (min b h)
    (fun p _ hlo hhi => mixed_norm_interval_away hlo hhi) f hM hf
  have hinterval : (∑ p ∈ S with max a l < norm p ∧ norm p ≤ min b h, f p) =
      ∑ p ∈ (((primeCutoff (min B (min b h))).filter (fun p => max a l < norm p)).filter
        (fun p => IsCoprime p e)).filter
        (fun p => largestPrimePredicate primeTieCode C p), f p := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [S,Finset.mem_filter,mem_primeCutoff,le_min_iff]
    tauto
  have hmain : ‖∑ p ∈ S with max a l < norm p ∧ norm p ≤ min b h, f p‖ ≤ K*P/T^D := by
    rw [hinterval]
    by_cases hab : max a l ≤ min B (min b h)
    · exact hbound T P (max a l) (min B (min b h)) w z u M V hT
        ((le_max_left _ _).trans hP) hTP hlow hab ((min_le_right _ _).trans hupp)
        hw hz hM hV hheight hMV W hW hWn hWd v e C hv hnc hNv he hNe
    · have hempty : (((primeCutoff (min B (min b h))).filter (fun p => max a l < norm p)).filter
          (fun p => IsCoprime p e)).filter (fun p => largestPrimePredicate primeTieCode C p) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        have hm := Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        exact hab (hm.2.le.trans (mem_primeCutoff.mp hm.1).2)
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have herr : 4*M ≤ P/T^D :=
    (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right hV).trans hMV) (by norm_num)).trans
      (hP₁ P ((le_max_right _ _).trans hP) T hT hTP)
  change ‖∑ p ∈ S with a < norm p ∧ l ≤ norm p ∧ norm p < b ∧ norm p ≤ h, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S with max a l < norm p ∧ norm p ≤ min b h, f p‖+
        ‖(∑ p ∈ S with a < norm p ∧ l ≤ norm p ∧ norm p < b ∧ norm p ≤ h, f p)-
          (∑ p ∈ S with max a l < norm p ∧ norm p ≤ min b h, f p)‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ K*P/T^D+4*M := add_le_add hmain (by
      convert hend using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      all_goals
        apply Finset.sum_congr
        · ext p
          simp only [Finset.mem_filter]
        · intro p hp
          rfl)
    _ ≤ K*P/T^D+P/T^D := add_le_add le_rfl herr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDistinguishedRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime cancellation with the literal distinguished-coordinate bin,
output interval and both stopping tests. The interval is derived, not
assumed to describe the stopping support. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stopped_distinguished_prime_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u M V : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → 0 < z → 0 ≤ M → 0 ≤ V → |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → (∀ x, ‖W x‖ ≤ M) →
      (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ c d v e : Eisenstein, primary c → primary d → v ≠ 0 →
      (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 → Real.log (norm e) ≤ T^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e,
        distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := long_distinguished_mixed_interval_saving hSW hA hD hH hE hF
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w z u M V j hT hρ hρ₂ hj hP hTP hw hz hM hV hu hMV W hW hWn hWd
    c d v e hc hd hv hnc hNv he hNe j₀ k h Z Q early
  let P := geometricBinLower ρ B j
  let S := primeSurrogate (primaryPrimeFactors d) (geometricPrimeBin ρ B) (geometricBinLower ρ B)
  let E₀ := primeSurrogate (primeBinPrefix (primaryPrimeFactors d) (geometricPrimeBin ρ B) h)
    (geometricPrimeBin ρ B) (geometricBinLower ρ B)
  let lo := a/norm (c*d)
  let low := max P (Z/(norm c*S))
  let up := min (ρ*P) (min (Z*geometricBinLower ρ B j₀/(norm c*S))
    (if early = true then ρ*P else Q/(norm c*E₀)))
  let hi := b/norm (c*d)
  let C := (∀ q ∈ primaryPrimeFactors d, geometricPrimeBin ρ B q ≤ j₀) ∧
    (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ B) j₀).card = k
  let U := ((primeCutoff B).filter (fun p => IsCoprime p e)).filter
    (fun p => largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p)
  let f := fun p => distinguishedRadialWeight W w z (norm p)*mellinPhase u (norm p)*cubicSymbol p v
  have heq : (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e, f p) =
      if C then ∑ p ∈ U with lo < norm p ∧ low ≤ norm p ∧ norm p < up ∧ norm p ≤ hi, f p else 0 := by
    unfold stoppedDistinguishedPrimeSet
    simp only [U,Finset.sum_filter]
    by_cases hC : C
    · rw [ite_eq_left hC]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hcop : IsCoprime p e
      · by_cases hl : largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p
        · simp only [hcop,hl,ite_true, if_true]
          have hinterval := stopped_distinguished_interval_iff (a := a) (b := b) (j₀ := j₀) (k := k) (h := h) hρ hρ₂ hj Z Q early hc hd
            (mem_primeCutoff.mp hp).1 (mem_primeCutoff.mp hp).2
          have hi' : (geometricPrimeBin ρ B p = j ∧
              (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
              stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
                j₀ k h Z Q early (c*p) d) ↔
              lo < norm p ∧ low ≤ norm p ∧ norm p < up ∧ norm p ≤ hi := by
            constructor
            · intro hpred
              exact (hinterval.mp hpred).2
            · intro hq
              exact hinterval.mpr ⟨hC,hq⟩
          exact if_congr hi' rfl rfl
        · simp only [hcop,hl,ite_true, if_true,ite_false, if_false]
      · simp only [hcop,ite_false, if_false]
    · rw [ite_eq_right hC]
      apply Finset.sum_eq_zero
      intro p hp
      by_cases hcop : IsCoprime p e
      · by_cases hl : largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p
        · simp only [hcop,hl,ite_true, if_true]
          apply ite_eq_right
          intro hpred
          have hinterval := stopped_distinguished_interval_iff (a := a) (b := b) (j₀ := j₀) (k := k) (h := h) hρ hρ₂ hj Z Q early hc hd
            (mem_primeCutoff.mp hp).1 (mem_primeCutoff.mp hp).2
          exact hC (hinterval.mp hpred).1
        · simp only [hcop,hl,ite_true, if_true,ite_false, if_false]
      · simp only [hcop,ite_false, if_false]
  have hPpos : 0 < P := zero_lt_one.trans (geometricBinLower_gt_one hρ hj)
  change ‖∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e, f p‖ ≤ _
  rw [heq]
  by_cases hC : C
  · rw [ite_eq_left hC]
    exact hbound T P B lo low up hi w z u M V hT hP hTP
      ((le_max_left _ _).trans (le_max_right _ _))
      ((min_le_left _ _).trans ((min_le_left _ _).trans
        (mul_le_mul_of_nonneg_right hρ₂ hPpos.le)))
      hw hz hM hV hu hMV W hW hWn hWd v e (primaryPrimeFactors (c*d)) hv hnc hNv he hNe
  · rw [ite_eq_right hC,norm_zero]
    positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDistinguishedFull
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring the fixed complementary cubic character and the original
Möbius coefficient in the distinguished-coordinate prime sum. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedDistinguishedPrimeSet_primary (B ρ a b : ℝ) (j j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (c d e : Eisenstein) {p : Eisenstein}
    (hp : p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e) :
    primaryPrime p :=
  (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
    (Finset.mem_filter.mp hp).1).1).1).1

lemma distinguished_full_prime_norm (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (W : ℝ → ℂ) (w z u : ℝ)
    (c d v : Eisenstein) (hc : primary c) (hd : primary d) :
    ‖∑ p ∈ S, cutoffMoebius primeDetectorCutoff w d*
      distinguishedRadialWeight W w z (norm p)*normTwist u ((c*p)*d)*
        cubicSymbol ((c*p)*d) v‖ ≤
      ‖∑ p ∈ S, distinguishedRadialWeight W w z (norm p)*
        mellinPhase u (norm p)*cubicSymbol p v‖ := by
  have hsplit : (∑ p ∈ S, cutoffMoebius primeDetectorCutoff w d*
      distinguishedRadialWeight W w z (norm p)*normTwist u ((c*p)*d)*
        cubicSymbol ((c*p)*d) v) =
      cutoffMoebius primeDetectorCutoff w d*
        ∑ p ∈ S, distinguishedRadialWeight W w z (norm p)*normTwist u ((c*d)*(p*1))*
          cubicSymbol ((c*d)*(p*1)) v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have he : (c*p)*d = (c*d)*(p*1) := by ring
    rw [he]
    ring
  rw [hsplit,norm_mul]
  calc
    _ ≤ ‖∑ p ∈ S, distinguishedRadialWeight W w z (norm p)*normTwist u ((c*d)*(p*1))*
          cubicSymbol ((c*d)*(p*1)) v‖ :=
      mul_le_of_le_one_left (_root_.norm_nonneg _) (primeDetectorCutoff_moebius_norm w d)
    _ ≤ ‖∑ p ∈ S, distinguishedRadialWeight W w z (norm p)*normTwist u (p*1)*
          cubicSymbol (p*1) v‖ :=
      fixed_primary_free_prime_norm S hS (fun p => distinguishedRadialWeight W w z (norm p))
        (c*d) 1 v (primary_mul hc hd) primary_one u
    _ = _ := by simp only [mul_one,normTwist_eq_mellinPhase]

theorem stopped_distinguished_full_saving (hSW : KummerPrimeSiegelWalfisz)
    {A D H E F : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u M V : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → 0 < z → 0 ≤ M → 0 ≤ V → |u| ≤ T^H → M+V ≤ T^F →
      ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → (∀ x, ‖W x‖ ≤ M) →
      (∀ x, 0 < x → ‖deriv W x‖*x ≤ V) →
      ∀ c d v e : Eisenstein, primary c → primary d → v ≠ 0 →
      (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      Real.log (norm (c*(d*e))) ≤ T^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e)),
        cutoffMoebius primeDetectorCutoff w d*distinguishedRadialWeight W w z (norm p)*
          normTwist u ((c*p)*d)*cubicSymbol ((c*p)*d) v‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := stopped_distinguished_prime_saving hSW hA hD hH hE hF
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w z u M V j hT hρ hρ₂ hj hP hTP hw hz hM hV hu hMV W hW hWn hWd
    c d v e hc hd hv hnc hNv he hNe j₀ k h Z Q early
  apply (distinguished_full_prime_norm
    (stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e)))
    (fun p hp => stoppedDistinguishedPrimeSet_primary B ρ a b j j₀ k h Z Q early c d (c*(d*e)) hp)
    W w z u c d v hc hd).trans
  exact hbound T B ρ a b w z u M V j hT hρ hρ₂ hj hP hTP hw hz hM hV hu hMV W hW hWn hWd
    c d v (c*(d*e)) hc hd hv hnc hNv
    (mul_ne_zero (primary_ne_zero hc) (mul_ne_zero (primary_ne_zero hd) he)) hNe
    j₀ k h Z Q early

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedPrimeGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original distinguished-coordinate conditions are exactly the
free-prime row conditions, including squarefreeness and the exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguished_prime_product_conditions (c p d e : Eisenstein)
    (hp : primaryPrime p) :
    (Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e) ↔
      Squarefree (c*d) ∧ IsCoprime (c*d) e ∧ IsCoprime p (c*(d*e)) := by
  have he : (c*p)*d = c*(p*d) := by ring
  have hf : d*(c*e) = c*(d*e) := by ring
  rw [he]
  simpa only [hf] using selectedPrime_product_conditions c p d e hp

lemma distinguished_largest_prime_iff {c p d : Eisenstein}
    (hc : primary c) (hp : primaryPrime p) (hd : primary d)
    (hs : Squarefree ((c*p)*d)) :
    largestPrimeChoice ((c*p)*d) = p ↔
      largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p := by
  have he : (c*p)*d = p*(c*d) := by ring
  rw [he] at hs ⊢
  have hcop : IsCoprime p (c*d) :=
    isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
  exact largestPrimeChoice_mul_eq_iff hp (primary_mul hc hd)
    (squarefree_mul_iff.mp hs).2.2
    (fun hdiv => hp.2.not_isUnit (hcop.isUnit_of_dvd hdiv))

lemma distinguished_prime_row_conditions {B ρ a b : ℝ} {j j₀ k h : ℕ}
    {Z Q : ℝ} {early : Bool} {c d e p : Eisenstein}
    (hc : primary c) (hd : primary d) (hp : p ∈ primeCutoff B) :
    (Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e ∧
      (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
      stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
        j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B p = j ∧
      largestPrimeChoice ((c*p)*d) = p) ↔
    (Squarefree (c*d) ∧ IsCoprime (c*d) e ∧
      p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e))) := by
  constructor
  · rintro ⟨hs,hcop,hint,hstop,hbin,hlarge⟩
    obtain ⟨hscd,hcde,hpe⟩ := (distinguished_prime_product_conditions c p d e
      (mem_primeCutoff.mp hp).1).mp ⟨hs,hcop⟩
    refine ⟨hscd,hcde,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hp,hpe⟩,?_⟩,hbin,hint,hstop⟩⟩
    exact (distinguished_largest_prime_iff hc (mem_primeCutoff.mp hp).1 hd hs).mp hlarge
  · rintro ⟨hscd,hcde,hrow⟩
    obtain ⟨hp',hbin,hint,hstop⟩ := Finset.mem_filter.mp hrow
    obtain ⟨hp',hl⟩ := Finset.mem_filter.mp hp'
    obtain ⟨_,hpe⟩ := Finset.mem_filter.mp hp'
    obtain ⟨hs,hcop⟩ := (distinguished_prime_product_conditions c p d e
      (mem_primeCutoff.mp hp).1).mpr ⟨hscd,hcde,hpe⟩
    exact ⟨hs,hcop,hint,hstop,hbin,
      (distinguished_largest_prime_iff hc (mem_primeCutoff.mp hp).1 hd hs).mpr hl⟩

lemma stoppedDistinguished_complement_bound {B ρ a b : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {c d e p : Eisenstein} (hc : primary c) (hd : primary d)
    (hp : p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e) :
    norm (c*d) ≤ b/geometricBinLower ρ B j := by
  obtain ⟨hp',hbin,hint,_⟩ := Finset.mem_filter.mp hp
  have hpB := mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp').1).1
  have hnorm := (geometricPrimeBin_eq_iff hρ hρ₂ hj hpB.1 hpB.2).mp hbin
  have hn : 0 < norm (c*d) := norm_pos_of_ne_zero
    (mul_ne_zero (primary_ne_zero hc) (primary_ne_zero hd))
  apply (le_div_iff₀ (zero_lt_one.trans (geometricBinLower_gt_one hρ hj))).mpr
  calc
    norm (c*d)*geometricBinLower ρ B j ≤ norm (c*d)*norm p :=
      mul_le_mul_of_nonneg_left hnorm.1 hn.le
    _ = norm ((c*p)*d) := by simp only [norm_mul_eq]; ring
    _ ≤ b := hint.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedPrimeCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite collection of the distinguished-coordinate conditions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedDistinguishedPrimeSet_subset (B ρ a b : ℝ) (j j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (c d e : Eisenstein) :
    stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e ⊆ primeCutoff B := by
  intro p hp
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1

theorem distinguished_prime_collection (B ρ a b : ℝ) (j j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (c d e : Eisenstein)
    (hc : primary c) (hd : primary d) (F : Eisenstein → ℂ) :
    (∑ p ∈ primeCutoff B,
      if Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e ∧
        (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
        stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
          j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B p = j ∧
        largestPrimeChoice ((c*p)*d) = p then F p else 0) =
    if Squarefree (c*d) ∧ IsCoprime (c*d) e then
      ∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e)), F p
    else 0 := by
  calc
    _ = ∑ p ∈ primeCutoff B,
        if Squarefree (c*d) ∧ IsCoprime (c*d) e ∧
          p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e))
        then F p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact if_congr (distinguished_prime_row_conditions hc hd hp) rfl rfl
    _ = _ := by
      by_cases hcd : Squarefree (c*d) ∧ IsCoprime (c*d) e
      · rw [ite_eq_left hcd]
        have he (p : Eisenstein) :
            (Squarefree (c*d) ∧ IsCoprime (c*d) e ∧
              p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e))) ↔
            p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e)) := by
          constructor
          · exact fun hp => hp.2.2
          · exact fun hp => ⟨hcd.1,hcd.2,hp⟩
        simp_rw [if_congr (he _) rfl rfl]
        rw [←Finset.sum_filter,Finset.filter_mem_eq_of_subset
          (stoppedDistinguishedPrimeSet_subset B ρ a b j j₀ k h Z Q early c d (c*(d*e)))]
      · rw [ite_eq_right hcd]
        apply Finset.sum_eq_zero
        intro p hp
        exact ite_eq_right (fun hpred => hcd ⟨hpred.1,hpred.2.1⟩)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedPrimeZero
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A distinguished prime row is empty outside its forced complementary
norm range. This keeps the later mass sum linear in the output length. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedDistinguished_row_eq_zero {B ρ a b : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j j₀ k h : ℕ} (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {c d e : Eisenstein} (hc : primary c) (hd : primary d)
    (hbig : b/geometricBinLower ρ B j < norm (c*d)) (F : Eisenstein → ℂ) :
    (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e, F p) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  exact (not_lt_of_ge (stoppedDistinguished_complement_bound hρ hρ₂ hj hc hd hp) hbig).elim

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedRowsSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summed distinguished-coordinate cancellation. The total complementary
mass is derived for the actual tuple weights and the actual norm cutoff. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_distinguished_rows_saving (i : ι) (m : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) {A D H E F : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u V : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 ≤ b → 1 ≤ w → w ≤ z → 0 ≤ V → |u| ≤ T^H → 1+V ≤ T^F →
      b/geometricBinLower ρ B j < w^m →
      ∀ (S : ι → Finset Eisenstein) (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l, ∀ p ∈ S l, primaryPrime p) → (∀ l x, ‖W l x‖ ≤ 1) →
      ContDiff ℝ ∞ (W i) → (∀ x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ t ∈ coordinateComplementTuples S i ×ˢ D₀,
        Squarefree ((∏ l, t.1 l)*t.2) → norm ((∏ l, t.1 l)*t.2) ≤ b/geometricBinLower ρ B j →
        Real.log (norm ((∏ l, t.1 l)*(t.2*e))) ≤ T^E) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ t ∈ (coordinateComplementTuples S i ×ˢ D₀).filter
          (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧ IsCoprime ((∏ l, t.1 l)*t.2) e),
        (∏ l ∈ Finset.univ.erase i, distinguishedRadialWeight (W l) w z (norm (t.1 l)))*
        (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
            (∏ l, t.1 l) t.2 ((∏ l, t.1 l)*(t.2*e)),
          cutoffMoebius primeDetectorCutoff w t.2*distinguishedRadialWeight (W i) w z (norm p)*
            normTwist u (((∏ l, t.1 l)*p)*t.2)*cubicSymbol (((∏ l, t.1 l)*p)*t.2) v)‖ ≤
        K*b/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := stopped_distinguished_full_saving hSW hA hD hH hE hF
  let C : ℝ := 18*((2^m:ℕ)*(((Fintype.card ι)^(Fintype.card ι):ℕ)+1))*K
  refine ⟨C,P₀,by dsimp [C]; positivity,hP₀,?_⟩
  intro T B ρ a b w z u V j hT hρ hρ₂ hj hP hTP hb hw hwz hV hu hVF hsize
    S W D₀ hS hW hWi hWd hD₀ v e hv hnc hNv he hNe j₀ k h Z Q early
  let P := geometricBinLower ρ B j
  let U := coordinateComplementTuples S i ×ˢ D₀
  let wt := fun t : (ι → Eisenstein) × Eisenstein =>
    ∏ l ∈ Finset.univ.erase i, distinguishedRadialWeight (W l) w z (norm (t.1 l))
  let row := fun t : (ι → Eisenstein) × Eisenstein =>
    ∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
        (∏ l, t.1 l) t.2 ((∏ l, t.1 l)*(t.2*e)),
      cutoffMoebius primeDetectorCutoff w t.2*distinguishedRadialWeight (W i) w z (norm p)*
        normTwist u (((∏ l, t.1 l)*p)*t.2)*cubicSymbol (((∏ l, t.1 l)*p)*t.2) v
  let U₁ := U.filter (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧ norm ((∏ l, t.1 l)*t.2) ≤ b/P)
  have hPpos : 0 < P := zero_lt_one.trans (geometricBinLower_gt_one hρ hj)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hY : 0 ≤ b/P := div_nonneg hb hPpos.le
  have hrow (t : (ι → Eisenstein) × Eisenstein) (ht : t ∈ U₁) : ‖row t‖ ≤ K*P/T^D := by
    obtain ⟨ht,hs,hn⟩ := Finset.mem_filter.mp ht
    obtain ⟨hg,hd⟩ := Finset.mem_product.mp ht
    exact hbound T B ρ a b w z u 1 V j hT hρ hρ₂ hj hP hTP
      (zero_lt_one.trans_le hw) ((zero_lt_one.trans_le hw).trans_le hwz) (by norm_num)
      hV hu hVF (W i) hWi (hW i) hWd (∏ l, t.1 l) t.2 v e
      (complementTuple_primary S hS i hg) (hD₀ t.2 hd) hv hnc hNv he (hNe t ht hs hn)
      j₀ k h Z Q early
  have heq : (∑ t ∈ U.filter (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧
        IsCoprime ((∏ l, t.1 l)*t.2) e), wt t*row t) =
      ∑ t ∈ U₁, if IsCoprime ((∏ l, t.1 l)*t.2) e then wt t*row t else 0 := by
    simp only [U₁,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨hg,hd⟩ := Finset.mem_product.mp ht
    by_cases hs : Squarefree ((∏ l, t.1 l)*t.2)
    · by_cases hn : norm ((∏ l, t.1 l)*t.2) ≤ b/P
      · by_cases hc : IsCoprime ((∏ l, t.1 l)*t.2) e <;> simp only [hs,hn,hc,and_self,ite_true, if_true,and_false,ite_false, if_false]
      · have hz : row t = 0 := stoppedDistinguished_row_eq_zero hρ hρ₂ hj
          (complementTuple_primary S hS i hg) (hD₀ t.2 hd) (lt_of_not_ge hn) _
        simp only [hs,hn,hz,and_false,mul_zero,ite_self]
    · simp only [hs,false_and,ite_false, if_false]
  change ‖∑ t ∈ U.filter (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧
    IsCoprime ((∏ l, t.1 l)*t.2) e), wt t*row t‖ ≤ _
  rw [heq]
  calc
    _ ≤ ∑ t ∈ U₁, ‖wt t‖*(K*P/T^D) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro t ht
      split_ifs
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hrow t ht) (_root_.norm_nonneg _)
      · rw [norm_zero]
        positivity
    _ = (∑ t ∈ U₁, ‖wt t‖)*(K*P/T^D) := (Finset.sum_mul _ _ _).symm
    _ ≤ (18*(b/P)*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)))*(K*P/T^D) := by
      apply mul_le_mul_of_nonneg_right ?_ (by positivity)
      simpa only [U₁,U,wt,norm_prod] using
        distinguished_complement_tuple_mass S hS i W hW D₀ hD₀ hY hw hwz hsize
    _ ≤ C*b/T^D := by
      have hmono : (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ) ≤
          (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ)+1 := by linarith
      dsimp [C]
      have hscale : (18*(b/P)*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)))*(K*P/T^D) =
          (18*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ))*K)*b/T^D := by
        field_simp
      rw [hscale]
      gcongr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedTupleRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original distinguished-role tuple sum is exactly the sum of the
free-prime rows; the global largest-prime and stopping tests are retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complementTuple_update_product (S : ι → Finset Eisenstein) (i : ι)
    {g : ι → Eisenstein} (hg : g ∈ coordinateComplementTuples S i) (p : Eisenstein) :
    (∏ l, Function.update g i p l) = (∏ l, g l)*p := by
  have hgi := ((coordinateComplement_mem S i g).mp hg).1
  have he : (∏ l, g l) = ∏ l ∈ Finset.univ.erase i, g l := by
    rw [←Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i),hgi,one_mul]
  rw [primeTuple_update_product,he,mul_comm]

theorem distinguished_tuple_stopped_rows [Nonempty ι]
    (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (d e : Eisenstein) (hd : primary d) (w : ι → Eisenstein → ℂ) (G : Eisenstein → ℂ) :
    (∑ f ∈ (Fintype.piFinset (fun _ : ι => primeCutoff B)).filter
        (fun f => Squarefree ((∏ l, f l)*d)),
      if largestPrimeChoice ((∏ l, f l)*d) ∣ ∏ l, f l then
        if IsCoprime ((∏ l, f l)*d) e ∧
          (a < norm ((∏ l, f l)*d) ∧ norm ((∏ l, f l)*d) ≤ b) ∧
          stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
            j₀ k h Z Q early (∏ l, f l) d ∧
          geometricPrimeBin ρ B (largestPrimeChoice ((∏ l, f l)*d)) = j
        then (∏ l, w l (f l))*G ((∏ l, f l)*d) else 0
      else 0) =
    ∑ i, ∑ g ∈ coordinateComplementTuples (fun _ : ι => primeCutoff B) i,
      (∏ l ∈ Finset.univ.erase i, w l (g l))*
      (if Squarefree ((∏ l, g l)*d) ∧ IsCoprime ((∏ l, g l)*d) e then
        ∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
            (∏ l, g l) d ((∏ l, g l)*(d*e)), w i p*G (((∏ l, g l)*p)*d)
      else 0) := by
  rw [distinguished_tuple_largest_reindex (fun _ : ι => primeCutoff B)
    (fun _ _ hp => (mem_primeCutoff.mp hp).1) hd]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro g hg
  let c := ∏ l, g l
  have hc : primary c := complementTuple_primary (fun _ : ι => primeCutoff B)
    (fun _ _ hp => (mem_primeCutoff.mp hp).1) i hg
  calc
    _ = (∏ l ∈ Finset.univ.erase i, w l (g l))*
        ∑ p ∈ primeCutoff B,
          if Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e ∧
            (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B p = j ∧
            largestPrimeChoice ((c*p)*d) = p then w i p*G ((c*p)*d) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [complementTuple_update_product _ i hg p,primeTuple_update_weight]
      change (if Squarefree ((c*p)*d) ∧ largestPrimeChoice ((c*p)*d) = p then
        if IsCoprime ((c*p)*d) e ∧ (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B (largestPrimeChoice ((c*p)*d)) = j
          then (w i p*(∏ l ∈ Finset.univ.erase i, w l (g l)))*G ((c*p)*d) else 0
        else 0) = _
      rw [←ite_and]
      have he : ((Squarefree ((c*p)*d) ∧ largestPrimeChoice ((c*p)*d) = p) ∧
          (IsCoprime ((c*p)*d) e ∧ (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B (largestPrimeChoice ((c*p)*d)) = j)) ↔
          (Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e ∧
            (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B p = j ∧
            largestPrimeChoice ((c*p)*d) = p) := by
        constructor
        · rintro ⟨⟨hs,he⟩,hc,hrange,hstop,hbin⟩
          rw [he] at hbin
          exact ⟨hs,hc,hrange,hstop,hbin,he⟩
        · rintro ⟨hs,hc,hrange,hstop,hbin,he⟩
          exact ⟨⟨hs,he⟩,hc,hrange,hstop,by simpa only [he] using hbin⟩
      have hh := if_congr he
        (Eq.refl ((w i p*(∏ l ∈ Finset.univ.erase i, w l (g l)))*G ((c*p)*d)))
        (Eq.refl (0:ℂ))
      apply hh.trans
      split_ifs <;> ring
    _ = _ := by
      rw [distinguished_prime_collection B ρ a b j j₀ k h Z Q early c d e hc hd]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedUniform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds for the literal stopped distinguished coefficient on
the fixed X-envelope. The bin boundary parameter does not enter them. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_distinguished_uniform {ξ C : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hC : 0 < C)
    {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D : Finset Eisenstein) (selected : Eisenstein → Eisenstein → Prop),
      (∀ i, ∀ p ∈ S i, primaryPrime p) →
      (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) → (∀ r ∈ R, primary r) →
      ∀ b : Eisenstein, primary b → Squarefree b → norm b ≤ C*X →
        ‖stoppedBeta R D (distinguishedTupleCoefficient S W ψ (X^ξ) (X^(2/5:ℝ)))
          ψ (X^ξ) selected b‖ ≤ K := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ξ)
  have hk' : 1 < ξ*(k:ℝ) := by
    have hh := (div_lt_iff₀ hξ).mp hk
    nlinarith
  let M : ℝ := ‖((Fintype.card ι).factorial:ℂ)⁻¹‖ *
    ((Fintype.card ι)^(Fintype.card ι):ℕ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨(2^k:ℕ)*(M+1),by positivity,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_prime_tuple_norm_bound hC hk']
    with X hX hnorm
  intro S W R D selected hS hW hR b hb hs hbX
  apply (stoppedBeta_distinguished_rough_bound S hS W hW R D hR hψ hψone hψzero
    (Real.one_le_rpow hX.le hξ.le) (Real.rpow_le_rpow_of_exponent_le hX.le hξz)
    selected hb hs (hbX.trans_lt hnorm)).trans
  change (2^k:ℕ)*M ≤ (2^k:ℕ)*(M+1)
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedTupleCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the literal stopped beta into its ordered prime
tuples and independent selected divisor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_distinguished_tuple_sum (S : ι → Finset Eisenstein)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ) (D : Finset Eisenstein)
    (selected : Eisenstein → Eisenstein → Prop) (K : Eisenstein → ℂ) :
    (∑ n ∈ primaryPairSupport (orderedConvolutionSupport S) D,
      stoppedBeta (orderedConvolutionSupport S) D (distinguishedTupleCoefficient S W ψ w z)
        ψ w selected n*K n) =
    ((Fintype.card ι).factorial:ℂ)⁻¹ *
      ∑ d ∈ D, ∑ f ∈ Fintype.piFinset S,
        if selected (∏ i, f i) d then
          (∏ i, W i (f i)*distinguishedPrimeWeight ψ w z (f i))*
            cutoffMoebius ψ w d*K ((∏ i, f i)*d) else 0 := by
  unfold stoppedBeta
  rw [primaryPairCoefficient_sum,Finset.sum_product]
  calc
    _ = ((Fintype.card ι).factorial:ℂ)⁻¹ *
        ∑ r ∈ orderedConvolutionSupport S,
          orderedConvolution S (fun i p => W i p*distinguishedPrimeWeight ψ w z p) r *
            ∑ d ∈ D, if selected r d then cutoffMoebius ψ w d*K (r*d) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hs : selected r d
      · simp only [hs,ite_true, if_true,distinguishedTupleCoefficient]
        ring
      · simp only [hs,ite_false, if_false,zero_mul,mul_zero]
    _ = _ := by
      rw [orderedConvolution_sum]
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hs : selected (∏ i, f i) d
      · simp only [hs,ite_true, if_true]
        ring
      · simp only [hs,ite_false, if_false,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDistinguishedIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished largest-prime role of literal stopped beta,
with the ordered-tuple factorial and original full-product twist. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_distinguished_original_tuple (B ρ a b w z u : ℝ)
    (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (W : ι → ℝ → ℂ) (D : Finset Eisenstein) (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D,
      stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D
        (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
          (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
        (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*cubicSymbol n v else 0)) =
    ((Fintype.card ι).factorial:ℂ)⁻¹ * ∑ d ∈ D,
      ∑ f ∈ (Fintype.piFinset (fun _ : ι => primeCutoff B)).filter
          (fun f => Squarefree ((∏ l, f l)*d)),
        if largestPrimeChoice ((∏ l, f l)*d) ∣ ∏ l, f l then
          if IsCoprime ((∏ l, f l)*d) e ∧
            (a < norm ((∏ l, f l)*d) ∧ norm ((∏ l, f l)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (∏ l, f l) d ∧
            geometricPrimeBin ρ B (largestPrimeChoice ((∏ l, f l)*d)) = j
          then (∏ l, distinguishedRadialWeight (W l) w z (norm (f l)))*
            (cutoffMoebius primeDetectorCutoff w d*normTwist u ((∏ l, f l)*d)*
              cubicSymbol ((∏ l, f l)*d) v) else 0
        else 0 := by
  rw [stoppedBeta_distinguished_tuple_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f hf
  have hprod : (∏ l, W l (norm (f l))*distinguishedPrimeWeight primeDetectorCutoff w z (f l)) =
      ∏ l, distinguishedRadialWeight (W l) w z (norm (f l)) := by
    apply Finset.prod_congr rfl
    intro l hl
    exact (distinguishedRadialWeight_eq_primeWeight (W l) w z (f l)).symm
  rw [hprod]
  simp only [stoppedDistinguishedTest,mul_ite,mul_zero]
  rw [←ite_and,←ite_and,←ite_and]
  have he : ((stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
        j₀ k h Z Q early (∏ l, f l) d ∧ largestPrimeChoice ((∏ l, f l)*d) ∣ (∏ l, f l) ∧
        geometricPrimeBin ρ B (largestPrimeChoice ((∏ l, f l)*d)) = j) ∧
      (Squarefree ((∏ l, f l)*d) ∧ IsCoprime ((∏ l, f l)*d) e ∧
        a < norm ((∏ l, f l)*d) ∧ norm ((∏ l, f l)*d) ≤ b)) ↔
    ((Squarefree ((∏ l, f l)*d) ∧
      largestPrimeChoice ((∏ l, f l)*d) ∣ (∏ l, f l)) ∧
        (IsCoprime ((∏ l, f l)*d) e ∧
          (a < norm ((∏ l, f l)*d) ∧ norm ((∏ l, f l)*d) ≤ b) ∧
          stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
            j₀ k h Z Q early (∏ l, f l) d ∧
          geometricPrimeBin ρ B (largestPrimeChoice ((∏ l, f l)*d)) = j)) := by tauto
  apply (if_congr he rfl rfl).trans
  split_ifs <;> ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDistinguishedRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the literal distinguished stopped coefficient into
the prime rows whose cancellation has already been proved. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_distinguished_rows [Nonempty ι] (B ρ a b w z u : ℝ)
    (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (W : ι → ℝ → ℂ) (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d)
    (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D,
      stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D
        (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
          (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
        (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*cubicSymbol n v else 0)) =
    ((Fintype.card ι).factorial:ℂ)⁻¹ *
      ∑ i, stoppedDistinguishedRows B ρ a b w z u j j₀ k h Z Q early W D v e i := by
  rw [stoppedBeta_distinguished_original_tuple]
  congr 1
  calc
    _ = ∑ d ∈ D, ∑ i,
        ∑ g ∈ coordinateComplementTuples (fun _ : ι => primeCutoff B) i,
          if Squarefree ((∏ l, g l)*d) ∧ IsCoprime ((∏ l, g l)*d) e then
            (∏ l ∈ Finset.univ.erase i, distinguishedRadialWeight (W l) w z (norm (g l)))*
              (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
                  (∏ l, g l) d ((∏ l, g l)*(d*e)),
                cutoffMoebius primeDetectorCutoff w d*
                  distinguishedRadialWeight (W i) w z (norm p)*
                  normTwist u (((∏ l, g l)*p)*d)*cubicSymbol (((∏ l, g l)*p)*d) v)
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [distinguished_tuple_stopped_rows B ρ a b j j₀ k h Z Q early d e (hD d hd)
        (fun l p => distinguishedRadialWeight (W l) w z (norm p))
        (fun n => cutoffMoebius primeDetectorCutoff w d*normTwist u n*cubicSymbol n v)]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro g hg
      split_ifs
      · congr 1
        apply Finset.sum_congr rfl
        intro p hp
        ring
      · rw [mul_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      simp only [stoppedDistinguishedRows, Finset.sum_filter, Finset.sum_product]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDistinguishedSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cancellation for the literal distinguished role in the stopped beta
coefficient, with the ordered-tuple factorial retained. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem stoppedBeta_distinguished_saving (m : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) {A D H E F : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u V : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 ≤ b → 1 ≤ w → w ≤ z → 0 ≤ V → |u| ≤ T^H → 1+V ≤ T^F →
      b/geometricBinLower ρ B j < w^m →
      ∀ (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ i, ∀ t ∈ coordinateComplementTuples (fun _ : ι => primeCutoff B) i ×ˢ D₀,
        Squarefree ((∏ l, t.1 l)*t.2) → norm ((∏ l, t.1 l)*t.2) ≤ b/geometricBinLower ρ B j →
        Real.log (norm ((∏ l, t.1 l)*(t.2*e))) ≤ T^E) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀,
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
          (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*cubicSymbol n v else 0)‖ ≤ K*b/T^D := by
  choose C P hC hP hbound using fun i : ι =>
    stopped_distinguished_rows_saving i m hSW hA hD hH hE hF
  let q : ℝ := ‖((Fintype.card ι).factorial:ℂ)⁻¹‖
  let K : ℝ := q*(∑ i, C i)+1
  let P₀ : ℝ := 2+∑ i, |P i|
  have hK : 0 < K := by
    have hs : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => (hC i).le)
    have hq : 0 ≤ q := _root_.norm_nonneg _
    dsimp [K]
    nlinarith [mul_nonneg hq hs]
  have hP₀ : 1 < P₀ := by
    dsimp [P₀]
    have hn : 0 ≤ ∑ i, |P i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w z u V j hT hρ hρ₂ hj hp hTP hb hw hwz hV hu hVF hsize
    W D₀ hW hWi hWd hD₀ v e hv hnc hNv he hNe j₀ k h Z Q early
  have hiP (i : ι) : P i ≤ geometricBinLower ρ B j := by
    apply le_trans ?_ hp
    calc
      P i ≤ |P i| := le_abs_self _
      _ ≤ ∑ l, |P l| := Finset.single_le_sum
        (f := fun l : ι => |P l|) (fun l _ => abs_nonneg (P l)) (Finset.mem_univ i)
      _ ≤ P₀ := by dsimp [P₀]; linarith
  have hrow (i : ι) :
      ‖stoppedDistinguishedRows B ρ a b w z u j j₀ k h Z Q early W D₀ v e i‖ ≤ C i*b/T^D := by
    exact hbound i T B ρ a b w z u V j hT hρ hρ₂ hj (hiP i) hTP hb hw hwz hV hu hVF hsize
      (fun _ : ι => primeCutoff B) W D₀ (fun _ _ h => (mem_primeCutoff.mp h).1)
      hW (hWi i) (hWd i) hD₀ v e hv hnc hNv he (hNe i) j₀ k h Z Q early
  rw [stoppedBeta_distinguished_rows B ρ a b w z u j j₀ k h Z Q early W D₀ hD₀ v e,norm_mul]
  change q*‖∑ i, stoppedDistinguishedRows B ρ a b w z u j j₀ k h Z Q early W D₀ v e i‖ ≤ _
  calc
    _ ≤ q*∑ i, ‖stoppedDistinguishedRows B ρ a b w z u j j₀ k h Z Q early W D₀ v e i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (_root_.norm_nonneg _)
    _ ≤ q*∑ i, C i*b/T^D :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hrow i)) (_root_.norm_nonneg _)
    _ = (q*∑ i, C i)*b/T^D := by rw [←Finset.sum_div,←Finset.sum_mul]; ring
    _ ≤ K*b/T^D := by
      apply div_le_div_of_nonneg_right ?_ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hT) _).le
      apply mul_le_mul_of_nonneg_right ?_ hb
      dsimp [K]
      linarith

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NarrowPrimeBinCount
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bin counts when the geometric ratio is allowed to approach
one. The width loss is explicit, as required for logarithmic stopping bins. -/
noncomputable section
namespace CubicFirstMoment

lemma logarithm_one_add_lower {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    δ/2 ≤ Real.log (1+δ) := by
  apply le_trans ?_ (Real.le_log_one_add_of_nonneg hδ.le)
  apply (le_div_iff₀ (by positivity : 0 < δ+2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hδone hδ.le]

theorem geometricBinCount_width_bound {δ B : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hB : 1 ≤ B) :
    (geometricBinCount (1+δ) B:ℝ) ≤ 2*Real.log B/δ+1 := by
  have hlogδ := logarithm_one_add_lower hδ hδone
  have hlogpos : 0 < Real.log (1+δ) := (by positivity : 0 < δ/2).trans_le hlogδ
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hcount := (Nat.ceil_lt_add_one (div_nonneg hlogB hlogpos.le)).le
  change (geometricBinCount (1+δ) B:ℝ) ≤ _ at hcount
  apply hcount.trans
  refine add_le_add ?_ le_rfl
  calc
    Real.log B/Real.log (1+δ) ≤ Real.log B/(δ/2) :=
      div_le_div_of_nonneg_left hlogB (by positivity) hlogδ
    _ = 2*Real.log B/δ := by ring

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

lemma geometricBinCount_logarithmic_width {X B δ C H : ℝ}
    (hX : 0 < X) (hL : 1 ≤ Real.log X) (hB : 1 ≤ B) (hBX : B ≤ X^C)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hwidth : (Real.log X)^(-H) ≤ δ) :
    (geometricBinCount (1+δ) B:ℝ) ≤ (2*C+1)*(Real.log X)^(H+1) := by
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL
  have hlogB : Real.log B ≤ C*Real.log X := by
    have he := Real.log_le_log (zero_lt_one.trans_le hB) hBX
    rwa [Real.log_rpow hX] at he
  have hinv : δ⁻¹ ≤ (Real.log X)^H := by
    have hi := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLp (-H)) hwidth
    simpa only [one_div,Real.rpow_neg hLp.le,inv_inv] using hi
  have hone : 1 ≤ (Real.log X)^(H+1) := Real.one_le_rpow hL (by linarith)
  apply (geometricBinCount_width_bound hδ hδone hB).trans
  calc
    2*Real.log B/δ+1 ≤ (2*(C*Real.log X))*(Real.log X)^H+1 := by
      rw [div_eq_mul_inv]
      gcongr
    _ = 2*C*(Real.log X)^(H+1)+1 := by
      rw [Real.rpow_add hLp,Real.rpow_one]
      ring
    _ ≤ (2*C+1)*(Real.log X)^(H+1) := by nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDistinguishedLogSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform log-X saving for the literal distinguished role. Polynomial
exclusions and the complementary roughness condition are derived from
their actual norm bounds, rather than added prime-row assumptions. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem stoppedBeta_distinguished_log_saving (m : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) {A D H E F C ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F)
    (hξ : 0 < ξ) (hgap : C < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B ρ a b z u V : ℝ) (j : ℕ),
      1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      Real.exp (Real.sqrt (Real.log X))/2 ≤ geometricBinLower ρ B j →
      0 ≤ b → b ≤ X^C → X^ξ ≤ z → 0 ≤ V →
      |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀,
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff (X^ξ) z) primeDetectorCutoff (X^ξ)
          (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*cubicSymbol n v else 0)‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := stoppedBeta_distinguished_saving (ι := ι) m hSW
    (A := A+1) (D := D) (H := H+1) (E := 2) (F := F+1)
    (by linarith) hD (by linarith) (by norm_num) (by linarith)
  refine ⟨K*4^D,by positivity,?_⟩
  filter_upwards [long_prime_logarithmic_window hP₀,
    eventually_log_parameter_power 1 A,eventually_log_parameter_power 1 H,
    eventually_log_parameter_power 1 F,eventually_log_parameter_power (C+E) 1,
    eventually_gt_atTop (1:ℝ)] with X hwindow hscaleA hscaleH hscaleF hscaleE hX
  intro B ρ a b z u V j hρ hρ₂ hj hPlong hb hbX hwz hV hu hVF
    W D₀ hW hWi hWd hD₀ v e hv hnc hNv he heX j₀ k h Z Q early
  have hXp : 0 < X := zero_lt_one.trans hX
  have hLp : 0 < Real.log X := Real.log_pos hX
  have hP := hwindow.2 _ hPlong
  have hw : 1 ≤ X^ξ := Real.one_le_rpow hX.le hξ.le
  have hsize : b/geometricBinLower ρ B j < (X^ξ)^m :=
    stopped_complement_power_bound hX hgap hb hbX (geometricBinLower_gt_one hρ hj).le
  have hNe (i : ι) (t : (ι → Eisenstein) × Eisenstein)
      (ht : t ∈ coordinateComplementTuples (fun _ : ι => primeCutoff B) i ×ˢ D₀)
      (_hs : Squarefree ((∏ l, t.1 l)*t.2))
      (hn : norm ((∏ l, t.1 l)*t.2) ≤ b/geometricBinLower ρ B j) :
      Real.log (norm ((∏ l, t.1 l)*(t.2*e))) ≤ (Real.log X/4)^(2:ℝ) := by
    obtain ⟨hg,hd⟩ := Finset.mem_product.mp ht
    have hprod := complementTuple_primary (fun _ : ι => primeCutoff B)
      (fun _ _ hp => (mem_primeCutoff.mp hp).1) i hg
    apply (stopped_complement_exclusion_log hprod (hD₀ _ hd) he hXp hb hbX
      (geometricBinLower_gt_one hρ hj).le hn heX).trans
    simpa only [Real.rpow_one,show (1:ℝ)+1=2 by norm_num] using hscaleE.2
  have hh := hbound (Real.log X/4) B ρ a b (X^ξ) z u V j hwindow.1 hρ hρ₂ hj
    hP.1 hP.2 hb hw hwz hV (hu.trans (by simpa only [one_mul] using hscaleH.2))
    (hVF.trans (by simpa only [one_mul] using hscaleF.2)) hsize W D₀ hW hWi hWd hD₀
    v e hv hnc (hNv.trans (by simpa only [one_mul] using hscaleA.2)) he hNe
    j₀ k h Z Q early
  apply hh.trans_eq
  rw [prime_parameter_log_saving hLp]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedLargestRoles
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact splitting of a valid largest-prime bin into its distinguished
and selected-divisor roles. The source stopping test is unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrimeChoice_prime_of_bin {B ρ : ℝ} {j : ℕ}
    (hj : j < geometricBinCount ρ B) {n : Eisenstein} (hn : primary n)
    (hbin : geometricPrimeBin ρ B (largestPrimeChoice n) = j) :
    primaryPrime (largestPrimeChoice n) ∧ largestPrimeChoice n ∣ n := by
  have hne : (primaryPrimeFactors n).Nonempty := by
    by_contra hempty
    have hchoice : largestPrimeChoice n = 1 := by
      simp only [largestPrimeChoice,dite_eq_right hempty]
    have hone : geometricPrimeBin ρ B (1 : Eisenstein) = geometricBinCount ρ B := by
      simp only [geometricPrimeBin,norm_one_eq,Real.log_one,zero_div,Nat.floor_zero,Nat.sub_zero]
    rw [hchoice,hone] at hbin
    omega
  exact primaryPrimeFactor_spec hn (largestPrimeChoice_spec hne).1

theorem stoppedBeta_largest_bin_roles (R D : Finset Eisenstein) (f : Eisenstein → ℂ)
    (w B ρ : ℝ) {j : ℕ} (hj : j < geometricBinCount ρ B)
    (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    stoppedBeta R D f primeDetectorCutoff w (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n =
      stoppedBeta R D f primeDetectorCutoff w (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n+
      stoppedBeta R D f primeDetectorCutoff w (stoppedSelectedTest B ρ j j₀ k h Z Q early) n := by
  unfold stoppedBeta primaryPairCoefficient
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have he : t.1*t.2 = n := (Finset.mem_filter.mp ht).2
  by_cases htest : stoppedLargestBinTest B ρ j j₀ k h Z Q early t.1 t.2
  · obtain ⟨hstop,hbin⟩ := htest
    have hp := largestPrimeChoice_prime_of_bin hj hn (he ▸ hbin)
    have hsf : Squarefree (t.1*t.2) := he.symm ▸ hs
    have hdiv : largestPrimeChoice (t.1*t.2) ∣ t.1*t.2 := by simpa only [he] using hp.2
    have hp' : Prime (largestPrimeChoice (t.1*t.2)) := by simpa only [he] using hp.1.2
    rcases prime_factor_unique_side hp' hsf hdiv with ⟨hr,hnd⟩ | ⟨hd,hnr⟩
    · simp only [stoppedLargestBinTest,stoppedDistinguishedTest,stoppedSelectedTest,
        hstop,hbin,hr,hnd,and_self,and_false,and_true,ite_true, if_true,ite_false, if_false,add_zero]
    · simp only [stoppedLargestBinTest,stoppedDistinguishedTest,stoppedSelectedTest,
        hstop,hbin,hd,hnr,and_self,and_false,and_true,ite_true, if_true,ite_false, if_false,zero_add]
  · have hd : ¬stoppedDistinguishedTest B ρ j j₀ k h Z Q early t.1 t.2 := by
      rintro ⟨ha,_,hb⟩
      exact htest ⟨ha,hb⟩
    have hc : ¬stoppedSelectedTest B ρ j j₀ k h Z Q early t.1 t.2 := by
      rintro ⟨ha,_,hb⟩
      exact htest ⟨ha,hb⟩
    simp only [htest,hd,hc,ite_false, if_false,add_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedEmptyTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! With no distinguished prime coordinates, the largest prime can only
occur in the selected divisor. This removes an artificial nonempty-tuple
restriction from the stopped-coefficient sequence estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι]

theorem stopped_distinguished_empty (B ρ a b w z u : ℝ)
    {j : ℕ} (hj : j < geometricBinCount ρ B) (j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (W : ι → ℝ → ℂ)
    (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d) (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D,
      stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D
        (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
          (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
        (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*cubicSymbol n v else 0)) = 0 := by
  rw [stoppedBeta_distinguished_original_tuple]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro f hf
  simp only [Finset.prod_of_isEmpty,one_mul]
  split_ifs with hdiv htest
  · have hp := largestPrimeChoice_prime_of_bin hj (hD d hd) htest.2.2.2
    exact (hp.1.2.not_isUnit (isUnit_of_dvd_one hdiv)).elim
  · rfl
  · rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedAllTuples
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished-role estimate for every finite tuple, including
zero distinguished primes. The empty case is an exact vanishing identity. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_distinguished_log_saving_all (m : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) {A D H E F C ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F)
    (hξ : 0 < ξ) (hgap : C < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B ρ a b z u V : ℝ) (j : ℕ),
      1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      Real.exp (Real.sqrt (Real.log X))/2 ≤ geometricBinLower ρ B j →
      0 ≤ b → b ≤ X^C → X^ξ ≤ z → 0 ≤ V →
      |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀,
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff (X^ξ) z) primeDetectorCutoff (X^ξ)
          (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*cubicSymbol n v else 0)‖ ≤ K*b/(Real.log X)^D := by
  rcases isEmpty_or_nonempty ι with he | hn
  · have := he
    refine ⟨1,zero_lt_one,?_⟩
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    intro B ρ a b z u V j _hρ _hρ₂ hj _hPlong hb _hbX _hwz _hV _hu _hVF
      W D₀ _hW _hWi _hWd hD₀ v e _hv _hnc _hNv _he _heX j₀ k h Z Q early
    rw [stopped_distinguished_empty B ρ a b (X^ξ) z u hj j₀ k h Z Q early W D₀ hD₀ v e,
      norm_zero,one_mul]
    exact div_nonneg hb (Real.rpow_nonneg (Real.log_nonneg hX.le) _)
  · have := hn
    exact stoppedBeta_distinguished_log_saving m hSW hA hD hH hF hξ hgap

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact long-bin decomposition of a stopped coefficient. The
complementary short-bin part is supported on genuinely smooth integers. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedBeta_product_predicate (R D : Finset Eisenstein) (f : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected : Eisenstein → Eisenstein → Prop)
    (P : Eisenstein → Prop) (n : Eisenstein) :
    stoppedBeta R D f ψ w (fun r d => selected r d ∧ P (r*d)) n =
      if P n then stoppedBeta R D f ψ w selected n else 0 := by
  unfold stoppedBeta primaryPairCoefficient
  by_cases hP : P n
  · rw [ite_eq_left hP]
    apply Finset.sum_congr rfl
    intro t ht
    have he := (Finset.mem_filter.mp ht).2
    simp only [he,hP,and_true]
  · rw [ite_eq_right hP]
    apply Finset.sum_eq_zero
    intro t ht
    have he := (Finset.mem_filter.mp ht).2
    simp only [he,hP,and_false,ite_false, if_false]

lemma largestPrimeChoice_valid_bin {B ρ : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) (hnorm : 1 < norm n)
    (hnB : norm n ≤ B) :
    primaryPrime (largestPrimeChoice n) ∧
      geometricPrimeBin ρ B (largestPrimeChoice n) < geometricBinCount ρ B := by
  have hne : (primaryPrimeFactors n).Nonempty := by
    by_contra hempty
    have he := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hp := primaryPrimeFactors_prod hn hs
    rw [he,Finset.prod_empty] at hp
    have hnormone : norm n = 1 := by rw [←hp,norm_one_eq]
    linarith
  have hp := primaryPrimeFactor_spec hn (largestPrimeChoice_spec hne).1
  exact ⟨hp.1,geometricPrimeBin_index hρ hρ₂ hp.1
    ((norm_le_of_dvd_nonzero (primary_ne_zero hn) hp.2).trans hnB)⟩

theorem stoppedBeta_long_bin_decomposition (R D : Finset Eisenstein) (f : Eisenstein → ℂ)
    (w B ρ y : ℝ) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (hnorm : 1 < norm n) (hnB : norm n ≤ B) :
    stoppedBeta R D f primeDetectorCutoff w
        (stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early) n =
      stoppedBeta R D f primeDetectorCutoff w (stoppedShortBinTest B ρ y j₀ k h Z Q early) n+
      ∑ j ∈ stoppedLongBins B ρ y,
        stoppedBeta R D f primeDetectorCutoff w (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n := by
  let s := stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early
  let c := geometricPrimeBin ρ B (largestPrimeChoice n)
  let z := stoppedBeta R D f primeDetectorCutoff w s n
  have hc : c < geometricBinCount ρ B := (largestPrimeChoice_valid_bin hρ hρ₂ hn hs hnorm hnB).2
  have heq (j : ℕ) :
      stoppedBeta R D f primeDetectorCutoff w (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n =
        if c = j then z else 0 := by
    have hpred : stoppedLargestBinTest B ρ j j₀ k h Z Q early =
        (fun r d => s r d ∧ geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j) := by
      funext r d
      rfl
    rw [hpred]
    have hb := stoppedBeta_product_predicate R D f primeDetectorCutoff w s
      (fun x => geometricPrimeBin ρ B (largestPrimeChoice x) = j) n
    by_cases hh : geometricPrimeBin ρ B (largestPrimeChoice n) = j
    · simpa only [stoppedLargestBinTest,s,c,z,hh,ite_true, if_true] using hb
    · simpa only [stoppedLargestBinTest,s,c,z,hh,ite_false, if_false] using hb
  have hshort : stoppedBeta R D f primeDetectorCutoff w (stoppedShortBinTest B ρ y j₀ k h Z Q early) n =
      if geometricBinLower ρ B c < y/2 then z else 0 :=
    stoppedBeta_product_predicate R D f primeDetectorCutoff w s
      (fun x => geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice x)) < y/2) n
  simp_rw [heq]
  rw [hshort]
  have hsum : (∑ j ∈ stoppedLongBins B ρ y, if c = j then z else 0) =
      if c ∈ stoppedLongBins B ρ y then z else 0 := by simp
  rw [hsum]
  have hmem : c ∈ stoppedLongBins B ρ y ↔ y/2 ≤ geometricBinLower ρ B c := by
    simp only [stoppedLongBins,Finset.mem_filter,Finset.mem_range,hc,true_and]
  rw [if_congr hmem rfl rfl]
  by_cases hsmall : geometricBinLower ρ B c < y/2
  · simp only [hsmall,not_le_of_gt hsmall,ite_true, if_true,ite_false, if_false,add_zero]
    rfl
  · simp only [hsmall,le_of_not_gt hsmall,ite_true, if_true,ite_false, if_false,zero_add]
    rfl

theorem stopped_short_bin_smooth {B ρ y : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) (hnorm : 1 < norm n)
    (hnB : norm n ≤ B)
    (hshort : geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice n)) < y/2) :
    ∀ p ∈ primaryPrimeFactors n, norm p ≤ y := by
  have hp := (largestPrimeChoice_valid_bin hρ hρ₂ hn hs hnorm hnB).1
  have hd := (largestPrimeChoice_prime_of_bin
    (largestPrimeChoice_valid_bin hρ hρ₂ hn hs hnorm hnB).2 hn rfl).2
  have hcell := (geometricPrimeBin_cell hρ hρ₂ hp
    ((norm_le_of_dvd_nonzero (primary_ne_zero hn) hd).trans hnB)).2
  have hlast : norm (largestPrimeChoice n) < y := by
    have hlower : 0 < geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice n)) := by
      exact zero_lt_one.trans (geometricBinLower_gt_one hρ
        (largestPrimeChoice_valid_bin hρ hρ₂ hn hs hnorm hnB).2)
    nlinarith
  intro p hp
  have hne : (primaryPrimeFactors n).Nonempty := ⟨p,hp⟩
  have hlarge := (largestPrimeChoice_spec hne).2 p hp
  have hnat : normNat p ≤ normNat (largestPrimeChoice n) := by
    rcases hlarge with hl | he
    · exact hl.le
    · exact he.1.le
  have hnormle : norm p ≤ norm (largestPrimeChoice n) := by
    rw [←normNat_cast,←normNat_cast]
    exact_mod_cast hnat
  exact hnormle.trans hlast.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma stopped_largest_bin_moment_roles (U R D : Finset Eisenstein)
    (hU : ∀ n ∈ U, primary n) (f K : Eisenstein → ℂ)
    (hK : ∀ n, ¬Squarefree n → K n = 0) (w B ρ : ℝ) {j : ℕ}
    (hj : j < geometricBinCount ρ B) (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool) :
    (∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
        (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n*K n) =
      (∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
        (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n*K n)+
      ∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
        (stoppedSelectedTest B ρ j j₀ k h Z Q early) n*K n := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hs : Squarefree n
  · rw [stoppedBeta_largest_bin_roles R D f w B ρ hj j₀ k h Z Q early (hU n hn) hs,add_mul]
  · simp only [hK n hs,mul_zero,add_zero]

theorem stopped_long_bin_moment_decomposition (U R D : Finset Eisenstein)
    (hU : ∀ n ∈ U, primary n) (f K : Eisenstein → ℂ) (B ρ y w : ℝ)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hK : ∀ n, ¬(Squarefree n ∧ 1 < norm n ∧ norm n ≤ B) → K n = 0)
    (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool) :
    (∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
      (stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early) n*K n) =
    (∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
      (stoppedShortBinTest B ρ y j₀ k h Z Q early) n*K n)+
    ∑ j ∈ stoppedLongBins B ρ y, ∑ n ∈ U,
      stoppedBeta R D f primeDetectorCutoff w
        (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n*K n := by
  calc
    _ = ∑ n ∈ U,
        (stoppedBeta R D f primeDetectorCutoff w
          (stoppedShortBinTest B ρ y j₀ k h Z Q early) n+
          ∑ j ∈ stoppedLongBins B ρ y, stoppedBeta R D f primeDetectorCutoff w
            (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n)*K n := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hp : Squarefree n ∧ 1 < norm n ∧ norm n ≤ B
      · rw [stoppedBeta_long_bin_decomposition R D f w B ρ y hρ hρ₂ j₀ k h Z Q early
          (hU n hn) hp.1 hp.2.1 hp.2.2]
      · simp only [hK n hp,mul_zero]
    _ = _ := by
      simp_rw [add_mul,Finset.sum_mul]
      rw [Finset.sum_add_distrib,Finset.sum_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinSaving
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual geometric-bin complexity consumes only its
explicit logarithmic power. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem geometric_bin_log_saving {X B δ C H D K b : ℝ}
    (hX : 0 < X) (hL : 1 ≤ Real.log X) (hB : 1 ≤ B) (hBX : B ≤ X^C)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hwidth : (Real.log X)^(-H) ≤ δ) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (S : Finset ℕ) (hS : S ⊆ Finset.range (geometricBinCount (1+δ) B))
    (f : ℕ → ℂ) (hf : ∀ j ∈ S, ‖f j‖ ≤ K*b/(Real.log X)^(D+H+1)) :
    ‖∑ j ∈ S, f j‖ ≤ ((2*C+1)*K)*b/(Real.log X)^D := by
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL
  have hcount : (S.card:ℝ) ≤ (2*C+1)*(Real.log X)^(H+1) := by
    apply le_trans (Nat.cast_le.mpr (Finset.card_le_card hS))
    simpa only [Finset.card_range] using
      geometricBinCount_logarithmic_width hX hL hB hBX hC hH hδ hδone hwidth
  calc
    _ ≤ ∑ _j ∈ S, K*b/(Real.log X)^(D+H+1) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hf)
    _ = (S.card:ℝ)*(K*b/(Real.log X)^(D+H+1)) := by simp
    _ ≤ ((2*C+1)*(Real.log X)^(H+1))*(K*b/(Real.log X)^(D+H+1)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by
      have he : (Real.log X)^(D+H+1) =
          (Real.log X)^D*(Real.log X)^(H+1) := by
        rw [show D+H+1 = D+(H+1) by ring,Real.rpow_add hLp]
      rw [he]
      field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedLongBinSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All long bins of the literal stopped coefficient have arbitrary
logarithmic saving. The number of bins is accounted for explicitly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedCharacterSum_largest_roles (B ρ w z a b u : ℝ) (W : ι → ℝ → ℂ)
    {j : ℕ} (hj : j < geometricBinCount ρ B) (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (v e : Eisenstein) :
    stoppedCharacterSum B w z a b u W (stoppedLargestBinTest B ρ j j₀ k h Z Q early) v e =
      stoppedCharacterSum B w z a b u W (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) v e+
      stoppedCharacterSum B w z a b u W (stoppedSelectedTest B ρ j j₀ k h Z Q early) v e := by
  apply stopped_largest_bin_moment_roles
  · intro n hn
    exact primaryPairSupport_primary _ _
      (fun r hr => orderedPrimarySupport_primary _ (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr)
      (fun d hd => (mem_primaryElementBall.mp hd).1) hn
  · intro n hn
    simp only [hn,false_and,ite_false, if_false]
  · exact hj

theorem stoppedBeta_long_bins_log_saving (m : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) {A D H E F J ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hgap : 1 < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ a b u V : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      0 ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ j ∈ stoppedLongBins X (1+δ) (Real.exp (Real.sqrt (Real.log X))),
        stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) a b u W
          (stoppedLargestBinTest X (1+δ) j j₀ k h Z Q early) v e‖ ≤ K*b/(Real.log X)^D := by
  have hD' : 0 < D+J+1 := by linarith
  obtain ⟨Kd,hKd,hd⟩ := stoppedBeta_distinguished_log_saving_all (ι := ι) m hSW
    (C := 1) (D := D+J+1) (E := E) hA hD' hH hF hξ hgap
  obtain ⟨Ks,hKs,hs⟩ := stoppedBeta_selected_log_saving (ι := ι) m hSW
    (C := 1) (D := D+J+1) (E := E) hA hD' hH hξ hgap
  refine ⟨3*(Kd+Ks),by positivity,?_⟩
  filter_upwards [hd,hs,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with X hd hs hX hL
  intro δ a b u V hδ hδone hwidth hb hbX hV hu hVF W hW hWi hWd
    v e hv hnc hNv he heX j₀ k h Z Q early
  have hXp : 0 < X := zero_lt_one.trans hX
  have hρ : 1 < 1+δ := by linarith
  have hρ₂ : 1+δ ≤ 2 := by linarith
  have hwz : X^ξ ≤ X^(2/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hX.le hξz
  let S := stoppedLongBins X (1+δ) (Real.exp (Real.sqrt (Real.log X)))
  let f := fun j => stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) a b u W
    (stoppedLargestBinTest X (1+δ) j j₀ k h Z Q early) v e
  have hS : S ⊆ Finset.range (geometricBinCount (1+δ) X) := Finset.filter_subset _ _
  have hf (j : ℕ) (hj : j ∈ S) : ‖f j‖ ≤ (Kd+Ks)*b/(Real.log X)^(D+J+1) := by
    obtain ⟨hj,hP⟩ := Finset.mem_filter.mp hj
    have hj' := Finset.mem_range.mp hj
    have hdist := hd X (1+δ) a b (X^(2/5:ℝ)) u V j hρ hρ₂ hj' hP hb
      (by simpa only [Real.rpow_one] using hbX) hwz hV hu hVF W (primaryElementBall X)
      hW hWi hWd (fun d hd => (mem_primaryElementBall.mp hd).1)
      v e hv hnc hNv he heX j₀ k h Z Q early
    have hsel := hs X (1+δ) a b (X^(2/5:ℝ)) u j hρ hρ₂ hj' hP hbX hb
      (by simpa only [Real.rpow_one] using hbX) hwz hu W hW v e hv hnc hNv he heX
      j₀ k h Z Q early
    change ‖stoppedCharacterSum _ _ _ _ _ _ _ _ _ _‖ ≤ _
    rw [stoppedCharacterSum_largest_roles X (1+δ) (X^ξ) (X^(2/5:ℝ)) a b u W
      hj' j₀ k h Z Q early v e]
    apply (norm_add_le _ _).trans
    apply (add_le_add hdist hsel).trans_eq
    ring
  simpa only [mul_one, show (2:ℝ)+1=3 by norm_num] using geometric_bin_log_saving hXp hL hX.le
    (by rw [Real.rpow_one]) (by norm_num : (0:ℝ) ≤ 1) hJ hδ hδone hwidth
    (add_nonneg hKd.le hKs.le) hb S hS f hf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelPartialSummation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimeUpper
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeRankin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Rankin bounds for the actual primary squarefree elements.
The map to their prime-factor subsets is injective; no ideal-counting
or smooth-number estimate is assumed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_supported_rankin_sum (S U : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hU : ∀ b ∈ S, primaryPrimeFactors b ⊆ U) (σ : ℝ) :
    (∑ b ∈ S, norm b^(-σ)) ≤ ∏ p ∈ U, (1+norm p^(-σ)) := by
  rw [Finset.prod_one_add]
  apply OAI.sum_le_sum_of_injOn primaryPrimeFactors
  · intro b hb c hc he
    calc
      b = ∏ p ∈ primaryPrimeFactors b, p := (primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2).symm
      _ = ∏ p ∈ primaryPrimeFactors c, p := by rw [he]
      _ = c := primaryPrimeFactors_prod (hS c hc).1 (hS c hc).2
  · intro s hs
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_powerset.mpr (hU b hb)
  · intro b hb
    have hn : norm b = ∏ p ∈ primaryPrimeFactors b, norm p := by
      rw [←norm_finset_prod,primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2]
    rw [hn,Real.finsetProd_rpow _ _ (fun p _ => norm_nonneg p)]
  · intro s hs hnot
    exact Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (norm_nonneg p) _)

lemma squarefree_supported_rankin_card (S U : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hU : ∀ b ∈ S, primaryPrimeFactors b ⊆ U)
    {B σ : ℝ} (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hsize : ∀ b ∈ S, norm b ≤ B) :
    (S.card:ℝ) ≤ B^σ*∏ p ∈ U, (1+norm p^(-σ)) := by
  calc
    _ = ∑ _b ∈ S, (1:ℝ) := by simp
    _ ≤ ∑ b ∈ S, B^σ*norm b^(-σ) := by
      apply Finset.sum_le_sum
      intro b hb
      have hb0 := norm_pos_of_ne_zero (primary_ne_zero (hS b hb).1)
      calc
        1 = norm b^σ*norm b^(-σ) := by
          rw [←Real.rpow_add hb0,add_neg_cancel,Real.rpow_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hb0.le (hsize b hb) hσ) (Real.rpow_nonneg hb0.le _)
    _ = B^σ*∑ b ∈ S, norm b^(-σ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (squarefree_supported_rankin_sum S U hS hU σ)
      (Real.rpow_nonneg hB _)

lemma finite_euler_product_le_exp (U : Finset Eisenstein) (σ : ℝ) :
    (∏ p ∈ U, (1+norm p^(-σ))) ≤ Real.exp (∑ p ∈ U, norm p^(-σ)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    exact add_nonneg zero_le_one (Real.rpow_nonneg (norm_nonneg p) _)
  · intro p hp
    simpa only [add_comm] using Real.add_one_le_exp (norm p^(-σ))

lemma shifted_prime_reciprocal_le {y : ℝ} (hy : 1 < y)
    {p : Eisenstein} (hp : primaryPrime p) (hpy : norm p ≤ y) :
    norm p^(-1+(Real.log y)⁻¹) ≤ Real.exp 1*(norm p)⁻¹ := by
  have hp0 := norm_pos_of_ne_zero hp.2.ne_zero
  have hl : 0 < Real.log y := Real.log_pos hy
  have hpower : y^((Real.log y)⁻¹) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hy),mul_inv_cancel₀ hl.ne']
  rw [Real.rpow_add hp0,Real.rpow_neg_one]
  calc
    _ ≤ (norm p)⁻¹*y^((Real.log y)⁻¹) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hp0.le hpy (inv_nonneg.mpr hl.le)) (inv_nonneg.mpr hp0.le)
    _ = _ := by rw [hpower,mul_comm]

theorem smooth_squarefree_rankin_bound (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b) {B y : ℝ}
    (hB : 0 ≤ B) (hy : Real.exp 1 ≤ y) (hsize : ∀ b ∈ S, norm b ≤ B)
    (hsmooth : ∀ b ∈ S, ∀ p ∈ primaryPrimeFactors b, norm p ≤ y) :
    (S.card:ℝ) ≤ B^(1-(Real.log y)⁻¹)*
      Real.exp (Real.exp 1*∑ p ∈ primeCutoff y, (norm p)⁻¹) := by
  have hy1 : 1 < y := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)).trans_le hy
  have hl : 1 ≤ Real.log y := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hy
  have hσ : 0 ≤ 1-(Real.log y)⁻¹ := sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr hl)
  have hsub : ∀ b ∈ S, primaryPrimeFactors b ⊆ primeCutoff y := by
    intro b hb p hp
    exact mem_primeCutoff.mpr ⟨(primaryPrimeFactor_spec (hS b hb).1 hp).1,hsmooth b hb p hp⟩
  apply (squarefree_supported_rankin_card S (primeCutoff y) hS hsub hB hσ hsize).trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hB _)
  apply (finite_euler_product_le_exp (primeCutoff y) (1-(Real.log y)⁻¹)).trans
  apply Real.exp_le_exp.mpr
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  convert shifted_prime_reciprocal_le hy1 (mem_primeCutoff.mp hp).1
    (mem_primeCutoff.mp hp).2 using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothRankinSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

private lemma exp_rankin_absorption {κ C D : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧
      Real.exp (-κ*T)*Real.exp (C*(1+Real.log T)) ≤ T^(-D) := by
  have hsmall := ((isLittleO_rpow_exp_pos_mul_atTop (C+D) hκ).const_mul_left
    (Real.exp C)).def zero_lt_one
  filter_upwards [hsmall,eventually_ge_atTop (1:ℝ)] with T ht hT
  refine ⟨hT,?_⟩
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have ht' : Real.exp C*T^(C+D) ≤ Real.exp (κ*T) := by
    simpa only [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _)
      (Real.rpow_nonneg hT0.le _)),Real.norm_of_nonneg (Real.exp_nonneg _),one_mul] using ht
  have heq : Real.exp (-κ*T)*Real.exp (C*(1+Real.log T)) =
      (Real.exp C*T^C)/Real.exp (κ*T) := by
    have he : Real.exp (C*(1+Real.log T)) = Real.exp C*T^C := by
      rw [Real.rpow_def_of_pos hT0,←Real.exp_add]
      congr 1
      ring
    rw [he,show -κ*T = -(κ*T) by ring,Real.exp_neg,div_eq_mul_inv]
    ring
  rw [heq,Real.rpow_neg hT0.le,←one_div]
  apply (div_le_div_iff₀ (Real.exp_pos _) (Real.rpow_pos_of_pos hT0 D)).mpr
  rw [one_mul]
  rw [mul_assoc,←Real.rpow_add hT0]
  exact ht'

theorem smooth_squarefree_log_saving (hpnt : PrimaryPrimePNT)
    {κ D : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, ∀ (B : ℝ) (S : Finset Eisenstein),
      Real.exp (κ*T^2) ≤ B →
      (∀ b ∈ S, primary b ∧ Squarefree b) →
      (∀ b ∈ S, norm b ≤ B) →
      (∀ b ∈ S, ∀ p ∈ primaryPrimeFactors b, norm p ≤ Real.exp T) →
      (S.card:ℝ) ≤ B*T^(-D) := by
  obtain ⟨C,hC,hprime⟩ := primaryPrime_reciprocal_exp_bound hpnt
  filter_upwards [exp_rankin_absorption (C := Real.exp 1*C) (D := D) hκ]
    with T hT
  intro B S hB hS hsize hsmooth
  have hT0 : 0 < T := zero_lt_one.trans_le hT.1
  have hB0 : 0 < B := (Real.exp_pos _).trans_le hB
  have hlogB : κ*T^2 ≤ Real.log B := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hB
  have hlogdiv : κ*T ≤ Real.log B/T := by
    apply (le_div_iff₀ hT0).mpr
    nlinarith [hlogB]
  have hpower : B^(1-T⁻¹) ≤ B*Real.exp (-κ*T) := by
    calc
      _ = B*Real.exp (-(Real.log B/T)) := by
        calc
          _ = Real.exp (Real.log B*(1-T⁻¹)) := Real.rpow_def_of_pos hB0 _
          _ = Real.exp (Real.log B)*Real.exp (-(Real.log B/T)) := by
            rw [←Real.exp_add]
            congr 1
            ring
          _ = _ := by rw [Real.exp_log hB0]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) hB0.le
  have hraw := smooth_squarefree_rankin_bound S hS hB0.le
    (Real.exp_le_exp.mpr hT.1) hsize hsmooth
  simp only [Real.log_exp] at hraw
  calc
    _ ≤ B^(1-T⁻¹)*Real.exp (Real.exp 1*
        ∑ p ∈ primeCutoff (Real.exp T), (norm p)⁻¹) := hraw
    _ ≤ (B*Real.exp (-κ*T))*Real.exp (Real.exp 1*C*(1+Real.log T)) := by
      apply mul_le_mul hpower
      · apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left (hprime T hT.1) (Real.exp_nonneg 1)
        simpa only [mul_assoc] using h
      · exact Real.exp_nonneg _
      · positivity
    _ = B*(Real.exp (-κ*T)*Real.exp (Real.exp 1*C*(1+Real.log T))) := by ring
    _ ≤ B*T^(-D) := mul_le_mul_of_nonneg_left hT.2 hB0.le

/-- The manuscript's actual long-prime cutoff. The exponent D is
arbitrary, so this discards the terms having no prime above exp(sqrt(log X)). -/
theorem smooth_squarefree_discard (hpnt : PrimaryPrimePNT)
    {κ D : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ (B : ℝ) (S : Finset Eisenstein),
      X^κ ≤ B →
      (∀ b ∈ S, primary b ∧ Squarefree b) →
      (∀ b ∈ S, norm b ≤ B) →
      (∀ b ∈ S, ∀ p ∈ primaryPrimeFactors b,
        norm p ≤ Real.exp (Real.sqrt (Real.log X))) →
      (S.card:ℝ) ≤ B*(Real.log X)^(-D) := by
  have ht : Tendsto (fun X : ℝ => Real.sqrt (Real.log X)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (smooth_squarefree_log_saving (D := 2*D) hpnt hκ),
    eventually_gt_atTop (1:ℝ)] with X hsave hX
  intro B S hB hS hsize hsmooth
  have hlog : 0 < Real.log X := Real.log_pos hX
  have he : Real.exp (κ*(Real.sqrt (Real.log X))^2) = X^κ := by
    rw [Real.sq_sqrt hlog.le,Real.rpow_def_of_pos (zero_lt_one.trans hX)]
    congr 1
    ring
  have h := hsave B S (he.symm ▸ hB) hS hsize hsmooth
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hlog.le]
  congr 2
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSmoothDiscard
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth-number removal for the literal stopped coefficient family.
The uniform coefficient bound is already proved from its distinguished
rough-prime construction. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_smooth_discard (hpnt : PrimaryPrimePNT)
    {ξ C κ A : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hC : 0 < C) (hκ : 0 < κ)
    {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0) :
    ∀ᶠ X : ℝ in atTop, ∀ (B : ℝ)
      (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
      (R D U : Finset Eisenstein) (selected : Eisenstein → Eisenstein → Prop),
      X^κ ≤ B → B ≤ C*X →
      (∀ i, ∀ p ∈ S i, primaryPrime p) →
      (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) → (∀ r ∈ R, primary r) →
      (∀ b ∈ U, primary b ∧ Squarefree b) → (∀ b ∈ U, norm b ≤ B) →
      (∀ b ∈ U, ∀ p ∈ primaryPrimeFactors b,
        norm p ≤ Real.exp (Real.sqrt (Real.log X))) →
      (∑ b ∈ U, ‖stoppedBeta R D
        (distinguishedTupleCoefficient S W ψ (X^ξ) (X^(2/5:ℝ)))
        ψ (X^ξ) selected b‖) ≤ B*(Real.log X)^(-A) := by
  obtain ⟨K,hK,hcoef⟩ := stoppedBeta_distinguished_uniform (ι := ι) hξ hξz hC
    hψ hψone hψzero
  have hlogK : ∀ᶠ X : ℝ in atTop, K ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop K)
  filter_upwards [hcoef,smooth_squarefree_discard (D := A+1) hpnt hκ,
    hlogK,eventually_gt_atTop (1:ℝ)] with X hcoef hcount hlogK hX
  intro B S W R D U selected hXB hBX hS hW hR hU hsize hsmooth
  have hB : 0 < B := (Real.rpow_pos_of_pos (zero_lt_one.trans hX) κ).trans_le hXB
  have hlog : 0 < Real.log X := Real.log_pos hX
  calc
    _ ≤ ∑ _b ∈ U, K := by
      apply Finset.sum_le_sum
      intro b hb
      exact hcoef S W R D selected hS hW hR b (hU b hb).1 (hU b hb).2
        ((hsize b hb).trans hBX)
    _ = K*(U.card:ℝ) := by simp [mul_comm]
    _ ≤ K*(B*(Real.log X)^(-(A+1))) :=
      mul_le_mul_of_nonneg_left (hcount B U hXB hU hsize hsmooth) hK.le
    _ ≤ (Real.log X)*(B*(Real.log X)^(-(A+1))) :=
      mul_le_mul_of_nonneg_right hlogK (by positivity)
    _ = B*(Real.log X)^(-A) := by
      have hp : Real.log X*(Real.log X)^(-(A+1)) = (Real.log X)^(-A) := by
        calc
          _ = (Real.log X)^1*(Real.log X)^(-(A+1)) := by rw [Real.rpow_one]
          _ = (Real.log X)^(1+(-(A+1))) := (Real.rpow_add hlog _ _).symm
          _ = _ := by congr 1; ring
      rw [mul_left_comm,hp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedShortBinSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The discarded short bins of the literal stopped coefficient have
arbitrary logarithmic saving, by their proved smooth support. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_short_bin_log_saving (hpnt : PrimaryPrimePNT)
    {ξ κ D : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ (B ρ a b u : ℝ),
      1 < ρ → ρ ≤ 2 → 1 ≤ a → b ≤ B → X^κ ≤ b → b ≤ X →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D₀ : Finset Eisenstein),
      (∀ l, ∀ p ∈ S l, primaryPrime p) → (∀ l, ∀ p ∈ S l, ‖W l p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ D₀, primary d) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool) (v e : Eisenstein),
      ‖∑ n ∈ primaryPairSupport R D₀,
        stoppedBeta R D₀ (distinguishedTupleCoefficient S W primeDetectorCutoff
          (X^ξ) (X^(2/5:ℝ))) primeDetectorCutoff (X^ξ)
          (stoppedShortBinTest B ρ (Real.exp (Real.sqrt (Real.log X))) j₀ k h Z Q early) n*
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*cubicSymbol n v else 0)‖ ≤ b/(Real.log X)^D := by
  filter_upwards [stoppedBeta_smooth_discard (ι := ι) (A := D) hpnt hξ hξz
      (C := 1) (by norm_num) hκ
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
      (fun _ _ hx => primeDetectorCutoff_one hx) (fun _ hx => primeDetectorCutoff_zero hx),
    eventually_gt_atTop (1:ℝ)] with X hdiscard hX
  intro B ρ a b u hρ hρ₂ ha hbB hbX hb S W R D₀ hS hW hR hD₀ j₀ k h Z Q early v e
  let y := Real.exp (Real.sqrt (Real.log X))
  let small := fun n : Eisenstein =>
    geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice n)) < y/2
  let U := (primaryPairSupport R D₀).filter (fun n =>
    (Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b) ∧ small n)
  let f := distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ))
  let selected := stoppedShortBinTest B ρ y j₀ k h Z Q early
  let beta := stoppedBeta R D₀ f primeDetectorCutoff (X^ξ) selected
  have hprimary {n : Eisenstein} (hn : n ∈ primaryPairSupport R D₀) : primary n :=
    primaryPairSupport_primary R D₀ hR hD₀ hn
  have hzero (n : Eisenstein) (hn : ¬small n) : beta n = 0 := by
    change stoppedBeta R D₀ f primeDetectorCutoff (X^ξ)
      (fun r d => stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
        j₀ k h Z Q early r d ∧ small (r*d)) n = 0
    rw [stoppedBeta_product_predicate,ite_eq_right hn]
  have heq : (∑ n ∈ primaryPairSupport R D₀, beta n*
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*cubicSymbol n v else 0)) =
      ∑ n ∈ U, beta n*(normTwist u n*cubicSymbol n v) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
    · by_cases hs : small n
      · simp only [hc,hs,and_self,ite_true, if_true]
      · simp only [hc,hs,hzero n hs,and_false,ite_false, if_false,zero_mul]
    · simp only [hc,false_and,ite_false, if_false,mul_zero]
  have hU (n : Eisenstein) (hn : n ∈ U) : primary n ∧ Squarefree n := by
    obtain ⟨hn,hc,_⟩ := Finset.mem_filter.mp hn
    exact ⟨hprimary hn,hc.1⟩
  have hmass : (∑ n ∈ U, ‖beta n‖) ≤ b*(Real.log X)^(-D) := by
    apply hdiscard b S W R D₀ U selected hbX (by simpa only [one_mul] using hb)
      hS hW hR hU
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.1.2.2.2
    · intro n hn
      obtain ⟨hn,hc,hs⟩ := Finset.mem_filter.mp hn
      exact stopped_short_bin_smooth hρ hρ₂ (hprimary hn) hc.1
        (ha.trans_lt hc.2.2.1) (hc.2.2.2.trans hbB) hs
  change ‖∑ n ∈ primaryPairSupport R D₀, beta n*_‖ ≤ _
  rw [heq]
  calc
    _ ≤ ∑ n ∈ U, ‖beta n‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul,norm_mul,norm_normTwist,one_mul]
      exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hU n hn).1 v)
    _ ≤ b*(Real.log X)^(-D) := hmass
    _ = _ := by rw [Real.rpow_neg (Real.log_pos hX).le,div_eq_mul_inv]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSequenceSW
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete Kummer sequence condition for the literal stopped
coefficient: exact long/short splitting, both largest-prime roles,
all bin costs, and the smooth remainder are derived. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_sequence_kummer_sw (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {ξ κ A D H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ a b u V : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ a → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) a b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k h Z Q early) v e‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨m,hm⟩ := exists_nat_gt (1/ξ)
  have hgap : 1 < ξ*m := by
    have ht := (div_lt_iff₀ hξ).mp hm
    simpa only [mul_comm] using ht
  obtain ⟨K,hK,hlong⟩ := stoppedBeta_long_bins_log_saving (ι := ι) m hSW
    (E := E) hA hD hH hF hJ hξ hξz hgap
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [hlong,stoppedBeta_short_bin_log_saving (ι := ι) (D := D)
    hpnt hξ hξz hκ,eventually_gt_atTop (1:ℝ)] with X hlong hshort hX
  intro δ a b u V hδ hδone hwidth ha hblow hbX hV hu hVF W hW hWi hWd
    v e hv hnc hNv he heX j₀ k h Z Q early
  have hρ : 1 < 1+δ := by linarith
  have hρ₂ : 1+δ ≤ 2 := by linarith
  have hb : 0 ≤ b := (Real.rpow_pos_of_pos (zero_lt_one.trans hX) κ).le.trans hblow
  let S := fun _ : ι => primeCutoff X
  let R := orderedConvolutionSupport S
  let T := primaryElementBall X
  let f := distinguishedTupleCoefficient S (fun l p => W l (norm p))
    primeDetectorCutoff (X^ξ) (X^(2/5:ℝ))
  let U := primaryPairSupport R T
  let F := fun n : Eisenstein =>
    if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
      then normTwist u n*cubicSymbol n v else 0
  have hS : ∀ l, ∀ p ∈ S l, primaryPrime p := fun _ _ hp => (mem_primeCutoff.mp hp).1
  have hR : ∀ r ∈ R, primary r := fun r hr =>
    orderedPrimarySupport_primary S (fun l p hp => (hS l p hp).1) hr
  have hT : ∀ t ∈ T, primary t := fun _ ht => (mem_primaryElementBall.mp ht).1
  have hU : ∀ n ∈ U, primary n := fun _ hn => primaryPairSupport_primary R T hR hT hn
  have hF : ∀ n, ¬(Squarefree n ∧ 1 < norm n ∧ norm n ≤ X) → F n = 0 := by
    intro n hn
    dsimp [F]
    split_ifs with hc
    · exact (hn ⟨hc.1,ha.trans_lt hc.2.2.1,hc.2.2.2.trans hbX⟩).elim
    · rfl
  have heq := stopped_long_bin_moment_decomposition U R T hU f F X (1+δ)
    (Real.exp (Real.sqrt (Real.log X))) (X^ξ) hρ hρ₂ hF j₀ k h Z Q early
  have hs : ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) a b u W
      (stoppedShortBinTest X (1+δ) (Real.exp (Real.sqrt (Real.log X))) j₀ k h Z Q early) v e‖ ≤
      b/(Real.log X)^D :=
    hshort X (1+δ) a b u hρ hρ₂ ha hbX hblow hbX S (fun l p => W l (norm p)) R T
      hS (fun l p _ => hW l _) hR hT j₀ k h Z Q early v e
  have hl := hlong δ a b u V hδ hδone hwidth hb hbX hV hu hVF
    W hW hWi hWd v e hv hnc hNv he heX j₀ k h Z Q early
  change ‖∑ n ∈ U, stoppedBeta R T f primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k h Z Q early) n*F n‖ ≤ _
  rw [heq]
  apply (norm_add_le _ _).trans
  apply (add_le_add hs hl).trans_eq
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredResidualFrequencies
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCubeExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cube factors in the frequency are exact exclusions for the literal
stopped coefficient. Its established Kummer sequence bound therefore
applies to a small noncube core times an arbitrary bounded cube. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedCharacterSum_cube (B w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (v j e : Eisenstein) :
    stoppedCharacterSum B w z a b u W selected (v*j^3) e =
      stoppedCharacterSum B w z a b u W selected v (e*j) := by
  unfold stoppedCharacterSum
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : primary n := primaryPairSupport_primary _ _
    (fun r hr => orderedPrimarySupport_primary _
      (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr)
    (fun d hd => (mem_primaryElementBall.mp hd).1) hn
  have hcop : IsCoprime n (e*j) ↔ IsCoprime n e ∧ IsCoprime n j :=
    ⟨fun h => ⟨h.of_mul_right_left,h.of_mul_right_right⟩,fun h => h.1.mul_right h.2⟩
  rw [cubicSymbol_mul_upper hnp,cubicSymbol_cube_indicator hnp j]
  by_cases he : IsCoprime n e <;> by_cases hj : IsCoprime n j <;>
    simp [hcop,he,hj]

theorem stopped_sequence_cube_sw (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {ξ κ A D H E F J d : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ a b u V : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ a → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      ∀ v j e : Eisenstein, v ≠ 0 → j ≠ 0 → (¬∃ n : Eisenstein, n^3 = v*j^3) →
      norm v ≤ (Real.log X)^A → norm j ≤ X^d → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) a b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k h Z Q early) (v*j^3) e‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨K,hK,hbound⟩ := stopped_sequence_kummer_sw (ι := ι)
    (E := E+d) hpnt hSW hξ hξz hκ hA hD hH hF hJ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ)] with X hbound hX
  intro δ a b u V hδ hδone hwidth ha hb hbX hV hu hVF W hW hWi hWd
    v j e hv hj hnc hNv hNj he hNe j₀ k h Z Q early
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hncv : ¬∃ n : Eisenstein, n^3 = v := by
    rintro ⟨n,hn⟩
    exact hnc ⟨n*j,by rw [mul_pow,hn]⟩
  have hNej : norm (e*j) ≤ X^(E+d) := by
    rw [norm_mul_eq,Real.rpow_add hXpos]
    exact mul_le_mul hNe hNj (norm_nonneg _) (Real.rpow_nonneg hXpos.le _)
  rw [stoppedCharacterSum_cube]
  exact hbound δ a b u V hδ hδone hwidth ha hb hbX hV hu hVF W hW hWi hWd
    v (e*j) hv hncv hNv (mul_ne_zero he hj) hNej j₀ k h Z Q early

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedLowCoreMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine small-core noncube mass bound for the stopped coefficient,
deduced from its proved Kummer cancellation and exact cube exclusion. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_low_core_mass_oai (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {ξ κ H E F J d : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (a k : ℕ) (ha : 0 < a) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V C : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      0 ≤ C → C ≤ X^d →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S : Finset Eisenstein), S ⊆ lowNoncubeSupport ((Real.log X)^a) C →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool),
      (∑ v ∈ S, ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤ K*C*b^2/(Real.log X)^k := by
  have ha' : (0:ℝ) < (a:ℝ) := Nat.cast_pos.mpr ha
  have hD : (0:ℝ) < (a+k+1:ℕ) := by positivity
  obtain ⟨K,hK,hbound⟩ := stopped_sequence_cube_sw (ι := ι)
    (A := (a:ℝ)) (D := (a+k+1:ℕ)) (d := d) (E := E)
    hpnt hSW hξ hξz hκ ha' hD hH hF hJ
  refine ⟨324*K^2,by positivity,?_⟩
  filter_upwards [hbound,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with X hbound hlog
  intro δ l b u V C hδ hδone hwidth hl hb hbX hV hu hVF hC hCX W hW hWi hWd
    S hS e he hNe j₀ k₀ h Z Q early
  have hterm (v : Eisenstein) (hv : v ∈ S) :
      ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖ ≤ K*b/(Real.log X)^(a+k+1) := by
    obtain ⟨hnc,v₀,j,hv₀,hj,hNv₀,hNj,heq⟩ := mem_lowNoncubeSupport (hS hv)
    have hvreal : norm v₀ ≤ (Real.log X)^(a:ℝ) := by
      simpa only [Real.rpow_natCast] using hNv₀
    have ht := hbound δ l b u V hδ hδone hwidth hl hb hbX hV hu hVF
      W hW hWi hWd v₀ j e hv₀ hj (by rwa [←heq]) hvreal
      (hNj.trans hCX) he hNe j₀ k₀ h Z Q early
    rw [heq]
    simpa only [Real.rpow_natCast] using ht
  have hcard : (S.card:ℝ) ≤ 324*(Real.log X)^a*C :=
    (Nat.cast_le.mpr (Finset.card_le_card hS)).trans
      (lowNoncubeSupport_card (pow_nonneg (zero_le_one.trans hlog) _) hC)
  have hmass :
      (∑ v ∈ S, ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤
      (S.card:ℝ)*(K*b/(Real.log X)^(a+k+1))^2 := by
    calc
      _ ≤ ∑ _v ∈ S, (K*b/(Real.log X)^(a+k+1))^2 := by
        apply Finset.sum_le_sum
        intro v hv
        gcongr
        exact hterm v hv
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
  exact low_core_mass_bound (a := a) (k := k) hC hlog hcard hmass

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.stopped_low_core_mass_oai.{u_1} := @OAI.CubicFirstMoment.stopped_low_core_mass_oai.{u_1}
