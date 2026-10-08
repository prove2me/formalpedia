-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_typical_short_mean_sharp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:18:26.285983+00:00
-- url     : https://prove2.me/submissions/49a0ff68-2370-4a9d-8d7b-e9a206ab1fc9

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_typical_kernel_bound_sharp
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_literal_short_energy_dyadic
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_log_energy_partition_bound

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Sieve.AlignedPrimeCongruence
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SievePartition

open scoped _root_.BigOperators

variable {α ι : Type*} [DecidableEq α] [LinearOrder ι]



omit [DecidableEq α] [LinearOrder ι] in
@[simp] theorem mem_survivors {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {x : α} :
    x ∈ survivors C P bad ↔ x ∈ C ∧ ∀ p ∈ P, ¬ bad p x := by
  classical
  simp [survivors]











instance decidableResidueBad (a : ℕ → ℕ) (p n : ℕ) : Decidable (residueBad a p n) :=
  inferInstanceAs (Decidable (n % p = a p % p))






end NumberTheoryLean.SievePartition

end

section

namespace NumberTheoryLean.SieveTree

open scoped _root_.BigOperators

variable {V : Type*} [DecidableEq V]








end NumberTheoryLean.SieveTree

end

section

namespace NumberTheoryLean.ResidueSieveTree

open scoped _root_.BigOperators
open _root_.OAI.Erdos970.NumberTheoryLean.SievePartition

















end NumberTheoryLean.ResidueSieveTree

end

section

namespace ErdosInverseCounts
open _root_.OAI.Erdos970.NumberTheoryLean _root_.OAI.Erdos970.NumberTheoryLean.SievePartition









end ErdosInverseCounts

end

section

namespace ErdosAlignedProgression






end ErdosAlignedProgression

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.LargePrimeDeletion
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LargePrimeDeletion

open scoped _root_.BigOperators






@[simp] theorem mem_deletionCell {C : Finset ℕ} {a : ℤ} {q i : ℕ} :
    i ∈ deletionCell C a q ↔ i ∈ C ∧ (q : ℤ) ∣ a + i := by
  classical
  simp [deletionCell]







@[simp] theorem mem_cutoffSurvivors {Y z i : ℕ} {residue : ℕ → ℕ} :
    i ∈ cutoffSurvivors Y z residue ↔
      i < Y ∧ ∀ p, p.Prime → p ≤ z → i % p ≠ residue p % p := by
  classical
  simp only [cutoffSurvivors, SievePartition.mem_survivors, Finset.mem_range,
    mem_cutoffPrimes, SievePartition.residueBad]
  tauto





@[simp] theorem mem_coprimeOffsets {Y n i : ℕ} {a : ℤ} :
    i ∈ coprimeOffsets Y n a ↔ i < Y ∧ (a + i).natAbs.Coprime n := by
  classical
  simp [coprimeOffsets]









end NumberTheoryLean.LargePrimeDeletion

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Sieve.IntervalBoundingSieve
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.IntervalBoundingSieve

open scoped _root_.BigOperators
















@[simp] theorem cutoffProduct_primeFactors (z : ℕ) :
    (cutoffProduct z).primeFactors = LargePrimeDeletion.cutoffPrimes z := by
  apply Nat.primeFactors_prod
  intro p hp
  exact (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1


end NumberTheoryLean.IntervalBoundingSieve

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Analysis.BonferroniDensity
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BonferroniDensity

open scoped _root_.BigOperators


@[simp] theorem elementarySum_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    elementarySum P g 0 = 1 := by simp [elementarySum]











@[simp] theorem densityPolynomial_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    densityPolynomial 0 P g = 1 := by simp [densityPolynomial]









end NumberTheoryLean.BonferroniDensity

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Estimates.DisjointBlockExpansion
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DisjointBlockExpansion

open scoped _root_.BigOperators


@[simp] theorem mem_blockChoices {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {choice : ∀ j ∈ B, Finset ℕ} :
    choice ∈ blockChoices B blocks ↔ ∀ j (hj : j ∈ B), choice j hj ⊆ blocks j := by
  classical
  simp only [blockChoices, Finset.mem_pi, Finset.mem_powerset]






















@[simp] theorem truncatedCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    truncatedCoefficient m T ≠ 0 ↔ T.card ≤ m := by
  unfold truncatedCoefficient
  split_ifs <;> simp_all

@[simp] theorem layerCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    layerCoefficient m T ≠ 0 ↔ T.card = m := by
  unfold layerCoefficient
  split_ifs <;> simp_all


























end NumberTheoryLean.DisjointBlockExpansion

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Estimates.SquarefreeHarmonic
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SelbergOptimization

open scoped _root_.BigOperators _root_.ArithmeticFunction.Moebius




























end NumberTheoryLean.SelbergOptimization

end

section

namespace NumberTheoryLean.SquarefreeHarmonic

open scoped _root_.BigOperators


@[simp] theorem mem_squarefreeUpTo {R d : ℕ} :
    d ∈ squarefreeUpTo R ↔ 1 ≤ d ∧ d ≤ R ∧ Squarefree d := by
  classical
  simp only [squarefreeUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto
















end NumberTheoryLean.SquarefreeHarmonic

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.PrimeDensityBlocks
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeDensityBlocks

open scoped _root_.BigOperators


@[simp] theorem mem_dyadicPrimes {n p : ℕ} :
    p ∈ dyadicPrimes n ↔ n ≤ p ∧ p < 2 * n ∧ p.Prime := by
  simp only [dyadicPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto






@[simp] theorem mem_geometricPrimes {j p : ℕ} :
    p ∈ geometricPrimes j ↔ 2 ^ (2 ^ j) ≤ p ∧ p < 2 ^ (2 ^ (j + 1)) ∧ p.Prime := by
  simp only [geometricPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto





















end NumberTheoryLean.PrimeDensityBlocks

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LocalFactors
namespace OAI

/-!
# Multiplicative functions from local prime-power factors

The finite local expansions in Part III of the manuscript replace values at
primes dividing a fixed dilation. The resulting functions are ordinary
multiplicative functions; complete multiplicativity is not required.
-/

namespace TwoPointCorrelations


@[simp] theorem fromPrimePowers_one (F : ℕ → ℕ → ℂ) : fromPrimePowers F 1 = 1 := by
  simp [fromPrimePowers]



@[simp] theorem fromPrimePowers_prime (F : ℕ → ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    fromPrimePowers F p = F p 1 := by
  simp [fromPrimePowers, hp.factorization, Finsupp.prod]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MertensScale
namespace OAI

/-! The exact classical reciprocal-prime input and its sole required scale.

Published source: J. B. Rosser and L. Schoenfeld, *Approximate formulas for
some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94,
Theorem 5, (3.17)–(3.18), bounded-error consequence of Mertens' second
theorem. DOI: https://doi.org/10.1215/ijm/1255631807.
The formal proof uses the bounded-error statement
`RS_prime.mertens_second_theorem'`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma sievePrimesUpTo_prime (y : ℝ) (p : ℕ) (hp : p ∈ sievePrimesUpTo y) :
    Nat.Prime p := (mem_filter.mp hp).2

lemma sievePrimesUpTo_le (y : ℝ) (hy : 0 ≤ y) (p : ℕ)
    (hp : p ∈ sievePrimesUpTo y) : (p : ℝ) ≤ y := by
  exact (Nat.le_floor_iff hy).mp (mem_Iic.mp (mem_filter.mp hp).1)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveLFunctions
namespace OAI

/-! The three analytic functions needed for the fixed modulus-five input.

Every nonprincipal character modulo five is determined here by its value at
two, which is one of `-1`, `I`, or `-I`. Its L-function is an explicit finite
linear combination of the existing Hurwitz zeta functions. The final
identity identifies the corresponding Mangoldt Dirichlet series with the
negative logarithmic derivative on the half-plane of absolute convergence.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.HurwitzZeta
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveCharacterSums
namespace OAI

/-! Bounded character sums and the exact Abel integral for modulus five.

Periodicity and the vanishing sum over one period give an absolute bound
four, independent of the character and of the cutoff. This is the first
analytic estimate for the three nonprincipal L-functions.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.Asymptotics _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical _root_.Topology

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CharacterTwists
namespace OAI

/-!
# Dirichlet character twists preserve uniform nonpretentiousness

Characters with different moduli are multiplied after changing both levels
to the product modulus. The resulting character equals the pointwise product
on every natural number, including the nonunit classes. This gives an exact
identity of pretentious distances and preserves the original height cutoff.
-/

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate
open _root_.Filter



@[simp] lemma conjugateCharacter_apply {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    conjugateCharacter χ n = conj (χ n) := rfl








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.Dilation
namespace OAI

/-!
# Finite multiplicative expansion of a dilation

This is the arithmetic content of manuscript Lemma `lem:affine-dilation`.
The equality is asserted for positive arguments, the domain relevant to
ordinary multiplicative functions. No complete multiplicativity is used.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations










@[simp] theorem dilationComponent_one (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    dilationComponent a f E 1 = 1 := by
  simp [dilationComponent, localComponent]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueExpansion
namespace OAI

/-!
# Residue classes as finite multiplicative expansions

The character identity in manuscript Lemma `lem:affine-residue` includes
nonunit residue classes. Dividing by the gcd reduces to a unit class, so the
standard character orthogonality relation applies even when the reduced
modulus is one. Each resulting dilation has the finite expansion already
proved in `Dilation`.
-/

open scoped _root_.BigOperators _root_.ComplexConjugate

namespace TwoPointCorrelations




@[simp] lemma naturalCharacter_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    naturalCharacter χ 1 = 1 := by simp [naturalCharacter]














end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling
namespace OAI

/-!
# Sampling the published short-interval estimate

For integral short lengths, a moving short sum is constant on each unit
cell of its origin. Thus its published integral controls the actual finite
sum of integer origins, with outer cutoff `Y+1`. The progression restriction
is an average of fixed frequencies and has total coefficient mass one.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma shortExponentialSum_on_unit_cell (b : ℕ → ℂ) (D : ℕ) (α : ℝ)
    (v : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (v : ℝ) (v + 1)) :
    shortExponentialSum b D α y = shortExponentialSum b D α v := by
  have hy0 : 0 ≤ y := (Nat.cast_nonneg v).trans hy.1
  have hf := Nat.floor_eq_on_Ico v y hy
  unfold shortExponentialSum
  rw [Nat.floor_add_natCast hy0, hf, Nat.floor_natCast,
    Nat.floor_add_natCast (Nat.cast_nonneg v) D, Nat.floor_natCast]

lemma shortExponentialSum_unit_integrable (b : ℕ → ℂ) (D : ℕ) (α : ℝ) (v : ℕ) :
    IntervalIntegrable (fun y => ‖shortExponentialSum b D α y‖)
      volume (v : ℝ) (v + 1) := by
  apply (intervalIntegrable_const : IntervalIntegrable
    (fun _ : ℝ => ‖shortExponentialSum b D α v‖) volume (v : ℝ) (v + 1)).congr_uIoo
  intro y hy
  rw [Set.uIoo_of_le (by linarith : (v : ℝ) ≤ v + 1)] at hy
  exact congrArg norm (shortExponentialSum_on_unit_cell b D α v ⟨hy.1.le, hy.2⟩).symm

lemma integral_shortExponentialSum_unit (b : ℕ → ℂ) (D : ℕ) (α : ℝ) (v : ℕ) :
    (∫ y in (v : ℝ)..(v + 1), ‖shortExponentialSum b D α y‖) =
      ‖shortExponentialSum b D α v‖ := by
  calc
    _ = ∫ _y in (v : ℝ)..(v + 1), ‖shortExponentialSum b D α v‖ := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
      intro y hy
      exact congrArg norm (shortExponentialSum_on_unit_cell b D α v ⟨hy.1.le, hy.2⟩)
    _ = _ := by simp












end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquareKernel
namespace OAI

/-!
# Exponential majorant for Dirichlet-polynomial mean squares

This is the elementary kernel behind the mean-value estimate used at the
start of corrected MRT, Appendix A, Proposition A.3.  Its Fourier transform
has quadratic decay, so the ensuing row sum loses no logarithm.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Set


lemma mrtMeanSquareKernel_right {T : ℝ} (ω : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    mrtMeanSquareKernel T ω t =
      Complex.exp ((((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
  simp only [mrtMeanSquareKernel, abs_of_nonneg ht,
    Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_one]
  congr 1
  ring

lemma mrtMeanSquareKernel_left {T : ℝ} (ω : ℝ) {t : ℝ} (ht : t ≤ 0) :
    mrtMeanSquareKernel T ω t =
      Complex.exp ((((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
  simp only [mrtMeanSquareKernel, abs_of_nonpos ht, neg_neg,
    Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_one]
  congr 1
  ring

lemma mrtMeanSquareKernel_integrable {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    Integrable (mrtMeanSquareKernel T ω) := by
  have hr : IntegrableOn (mrtMeanSquareKernel T ω) (Ioi 0) := by
    apply (integrableOn_exp_mul_complex_Ioi
      (a := ((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
      (by simpa using neg_lt_zero.mpr (one_div_pos.mpr hT)) 0).congr_fun
        (fun t ht => ?_) measurableSet_Ioi
    simpa using (mrtMeanSquareKernel_right ω ht.le).symm
  have hl : IntegrableOn (mrtMeanSquareKernel T ω) (Iic 0) := by
    apply (integrableOn_exp_mul_complex_Iic
      (a := ((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
      (by simpa using one_div_pos.mpr hT) 0).congr_fun
        (fun t ht => ?_) measurableSet_Iic
    exact (mrtMeanSquareKernel_left ω ht).symm
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hr

/-- Exact quadratic-decay Fourier transform, without an asymptotic constant. -/
theorem integral_mrtMeanSquareKernel {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    (∫ t : ℝ, mrtMeanSquareKernel T ω t) =
      ((2 * T / (1 + T ^ 2 * ω ^ 2) : ℝ) : ℂ) := by
  have hi := mrtMeanSquareKernel_integrable hT ω
  have hr : (∫ t in Ioi (0 : ℝ), mrtMeanSquareKernel T ω t) =
      -1 / (((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), Complex.exp
          ((((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simpa using mrtMeanSquareKernel_right ω ht.le
      _ = _ := by
        simpa using integral_exp_mul_complex_Ioi
          (a := ((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
          (by simpa using neg_lt_zero.mpr (one_div_pos.mpr hT)) 0
  have hl : (∫ t in Iic (0 : ℝ), mrtMeanSquareKernel T ω t) =
      1 / (((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) := by
    calc
      _ = ∫ t in Iic (0 : ℝ), Complex.exp
          ((((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t ht
        exact mrtMeanSquareKernel_left ω ht
      _ = _ := by
        simpa using integral_exp_mul_complex_Iic
          (a := ((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
          (by simpa using one_div_pos.mpr hT) 0
  rw [← integral_add_compl measurableSet_Iic hi, compl_Iic, hl, hr]
  have hTp : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hp : (((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    have he : (1 / T : ℝ) = 0 := by simpa using this
    exact (one_div_pos.mpr hT).ne' he
  have hm : (((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    have he : -(1 / T : ℝ) = 0 := by simpa using this
    exact (neg_lt_zero.mpr (one_div_pos.mpr hT)).ne he
  have hp1 : (1 + (T : ℂ) * (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hm1 : (-1 + (T : ℂ) * (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hd : (1 + T ^ 2 * ω ^ 2 : ℝ) ≠ 0 := by positivity
  have hdc : (1 + (T : ℂ) ^ 2 * (ω : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
  ring_nf
  field_simp [hp1, hm1, hdc]
  ring_nf
  simp only [Complex.I_sq]
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquareRows
namespace OAI

/-! Summable quadratic-gap bounds for the MRT Dirichlet mean-value estimate. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.BigOperators

lemma mrt_log_gap {x y N : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyN : y ≤ N) :
    (y - x) / N ≤ Real.log y - Real.log x := by
  have hy : 0 < y := hx.trans_le hxy
  have hN : 0 < N := hy.trans_le hyN
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne', inv_div] at hlog
  calc
    (y - x) / N ≤ (y - x) / y :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hy hyN
    _ = 1 - x / y := by field_simp
    _ ≤ _ := hlog

lemma mrt_quadratic_gap_sum {R : ℝ} (hR : 0 < R) (N : ℕ) :
    (∑ k ∈ Ioc 0 N, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ 2 * R + 1 := by
  let K := Nat.ceil R
  let M := max K N
  have hK : 0 < K := Nat.ceil_pos.mpr hR
  have hRK : R ≤ (K : ℝ) := Nat.le_ceil R
  have hKR : (K : ℝ) < R + 1 := Nat.ceil_lt_add_one hR.le
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hKM : K ≤ M := le_max_left _ _
  have hsplit : Ioc 0 M = Ioc 0 K ∪ Ioc K M := by
    ext k
    simp only [mem_Ioc, mem_union]
    omega
  have hd : Disjoint (Ioc 0 K) (Ioc K M) := by
    rw [disjoint_left]
    simp only [mem_Ioc]
    omega
  have hnear : (∑ k ∈ Ioc 0 K, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ (K : ℝ) := by
    calc
      _ ≤ ∑ _k ∈ Ioc 0 K, (1 : ℝ) := by
        apply sum_le_sum
        intro k _
        exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((k : ℝ) / R)])
      _ = _ := by simp
  have hfar : (∑ k ∈ Ioc K M, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ R := by
    calc
      _ ≤ ∑ k ∈ Ioc K M, R ^ 2 * ((k : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro k hk
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (hK.trans (mem_Ioc.mp hk).1)
        calc
          _ ≤ (((k : ℝ) / R) ^ 2)⁻¹ := by
            apply inv_anti₀ (sq_pos_of_pos (div_pos hk0 hR))
            linarith
          _ = _ := by field_simp
      _ = R ^ 2 * ∑ k ∈ Ioc K M, ((k : ℝ) ^ 2)⁻¹ := (mul_sum _ _ _).symm
      _ ≤ R ^ 2 * ((K : ℝ)⁻¹ - (M : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (α := ℝ) hK.ne' hKM)
          (sq_nonneg R)
      _ ≤ R ^ 2 * (K : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg R)
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg M))
      _ ≤ R := by
        rw [← div_eq_mul_inv, div_le_iff₀ hK0]
        nlinarith
  calc
    _ ≤ ∑ k ∈ Ioc 0 M, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [mem_Ioc] at hk ⊢
        exact ⟨hk.1, hk.2.trans (le_max_right _ _)⟩
      · intro k _ _
        positivity
    _ = (∑ k ∈ Ioc 0 K, (1 + ((k : ℝ) / R) ^ 2)⁻¹) +
        ∑ k ∈ Ioc K M, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by rw [hsplit, sum_union hd]
    _ ≤ (K : ℝ) + R := add_le_add hnear hfar
    _ ≤ 2 * R + 1 := by linarith

lemma mrt_nat_distance_sum (φ : ℕ → ℝ) (hφ : ∀ k, 0 ≤ φ k)
    {m N : ℕ} (hm : m ∈ Ioc 0 N) :
    (∑ n ∈ Ioc 0 N, φ (Nat.dist n m)) ≤
      φ 0 + 2 * ∑ k ∈ Ioc 0 N, φ k := by
  have hm' := mem_Ioc.mp hm
  have hsplit : Ioc 0 N = Ioc 0 m ∪ Ioc m N := by
    ext n
    simp only [mem_Ioc, mem_union]
    omega
  have hd : Disjoint (Ioc 0 m) (Ioc m N) := by
    rw [disjoint_left]
    simp only [mem_Ioc]
    omega
  have hleft : (∑ n ∈ Ioc 0 m, φ (Nat.dist n m)) = ∑ k ∈ range m, φ k := by
    apply sum_bij (fun n _ => m - n)
    · intro n hn
      have hn' := mem_Ioc.mp hn
      simp only [mem_range]
      omega
    · intro n hn n' hn' he
      have h1 := mem_Ioc.mp hn
      have h2 := mem_Ioc.mp hn'
      omega
    · intro k hk
      have hk' := mem_range.mp hk
      refine ⟨m - k, mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro n hn
      rw [Nat.dist_eq_sub_of_le (mem_Ioc.mp hn).2]
  have hright : (∑ n ∈ Ioc m N, φ (Nat.dist n m)) = ∑ k ∈ Ioc 0 (N - m), φ k := by
    apply sum_bij (fun n _ => n - m)
    · intro n hn
      have hn' := mem_Ioc.mp hn
      simp only [mem_Ioc]
      omega
    · intro n hn n' hn' he
      have h1 := mem_Ioc.mp hn
      have h2 := mem_Ioc.mp hn'
      omega
    · intro k hk
      have hk' := mem_Ioc.mp hk
      refine ⟨m + k, mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro n hn
      rw [Nat.dist_eq_sub_of_le_right (mem_Ioc.mp hn).1.le]
  have hrange : range m = insert 0 (Ioc 0 (m - 1)) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  have hzero : 0 ∉ Ioc 0 (m - 1) := by simp
  conv_lhs => rw [hsplit, sum_union hd, hleft, hright, hrange, sum_insert hzero]
  have hL : (∑ k ∈ Ioc 0 (m - 1), φ k) ≤ ∑ k ∈ Ioc 0 N, φ k := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have hk' := mem_Ioc.mp hk
      exact mem_Ioc.mpr ⟨hk'.1, by omega⟩
    · intro k _ _
      exact hφ k
  have hR : (∑ k ∈ Ioc 0 (N - m), φ k) ≤ ∑ k ∈ Ioc 0 N, φ k := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have hk' := mem_Ioc.mp hk
      exact mem_Ioc.mpr ⟨hk'.1, by omega⟩
    · intro k _ _
      exact hφ k
  linarith

lemma mrt_log_nat_gap {m n N : ℕ} (hm : m ∈ Ioc 0 N) (hn : n ∈ Ioc 0 N) :
    (Nat.dist m n : ℝ) / (N : ℝ) ≤ |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  have hm' := mem_Ioc.mp hm
  have hn' := mem_Ioc.mp hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm'.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'.1
  rcases le_total m n with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
      abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hm0 (by exact_mod_cast h)))]
    exact mrt_log_gap hm0 (by exact_mod_cast h) (by exact_mod_cast hn'.2)
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 (by exact_mod_cast h)))]
    exact mrt_log_gap hn0 (by exact_mod_cast h) (by exact_mod_cast hm'.2)

/-- The actual logarithmic-frequency kernel has row sum `O(T+N)`. -/
theorem mrt_logarithmic_kernel_row {T : ℝ} (hT : 0 < T) {N m : ℕ}
    (hm : m ∈ Ioc 0 N) :
    (∑ n ∈ Ioc 0 N,
      2 * T / (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2)) ≤
      8 * (T + (N : ℝ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (mem_Ioc.mp hm).1.trans_le (mem_Ioc.mp hm).2
  let R := (N : ℝ) / T
  have hR : 0 < R := div_pos hN hT
  have hterm (n : ℕ) (hn : n ∈ Ioc 0 N) :
      2 * T / (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2) ≤
      2 * T * (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹ := by
    have hgap := mrt_log_nat_gap hn hm
    rw [abs_sub_comm] at hgap
    have hsq : ((Nat.dist n m : ℝ) / (N : ℝ)) ^ 2 ≤
        (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (by positivity) hgap 2
    have he : ((Nat.dist n m : ℝ) / R) ^ 2 =
        T ^ 2 * ((Nat.dist n m : ℝ) / (N : ℝ)) ^ 2 := by
      dsimp only [R]
      field_simp
    rw [he, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply inv_anti₀ (by positivity)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (sq_nonneg T))
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, 2 * T * (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹ :=
      sum_le_sum hterm
    _ = 2 * T * ∑ n ∈ Ioc 0 N, (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹ :=
      (mul_sum _ _ _).symm
    _ ≤ 2 * T * (1 + 2 * (2 * R + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hd := mrt_nat_distance_sum (fun k => (1 + ((k : ℝ) / R) ^ 2)⁻¹)
        (fun _ => by positivity) hm
      have hd' : (∑ n ∈ Ioc 0 N, (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹) ≤
          1 + 2 * ∑ k ∈ Ioc 0 N, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by
        simpa only [Nat.cast_zero, zero_div, zero_pow (by decide : 2 ≠ 0), add_zero,
          inv_one] using hd
      exact hd'.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (mrt_quadratic_gap_sum hR N)
          (by norm_num : (0 : ℝ) ≤ 2)))
    _ ≤ 8 * (T + (N : ℝ)) := by
      dsimp only [R]
      have hc : T * ((N : ℝ) / T) = N := mul_div_cancel₀ _ hT.ne'
      nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquare
namespace OAI

/-! Finite Dirichlet-polynomial mean squares, using the integrable
exponential majorant and its exact quadratic-decay Fourier transform. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.BigOperators _root_.ComplexConjugate


lemma mrt_phase_pair (x y : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) *
        conj (Complex.exp ((y : ℂ) * Complex.I)) =
      Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I, ofReal_sub]
  ring

lemma mrt_weighted_square_expansion {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (T t : ℝ) :
    ((Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S,
        (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t := by
  rw [ofReal_mul, ofReal_pow, ← Complex.mul_conj']
  simp only [mrtExponentialPolynomial, map_sum, sum_mul, mul_sum]
  rw [sum_comm (s := S) (t := S)]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [map_mul]
  have hp := mrt_phase_pair (freq i * t) (freq j * t)
  have he : (((freq i - freq j) * t : ℝ) : ℂ) * Complex.I =
      ((freq i * t - freq j * t : ℝ) : ℂ) * Complex.I := by congr 1; push_cast; ring
  dsimp only [mrtMeanSquareKernel]
  rw [he, ← hp]
  ring

lemma mrt_weighted_square_integrable {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2) := by
  have hi : Integrable (fun t : ℝ => ∑ i ∈ S, ∑ j ∈ S,
      (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
  have he : (fun t : ℝ => ∑ i ∈ S, ∑ j ∈ S,
      (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t) =
      fun t => ((Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    exact (mrt_weighted_square_expansion S a freq T t).symm
  rw [he] at hi
  simpa only [RCLike.re_to_complex, ofReal_re] using hi.re

/-- Exact finite mean-square formula.  This identity is valid for arbitrary
real frequencies; separation is needed only for the subsequent bound. -/
theorem mrt_weighted_mean_square {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)).re *
        (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) := by
  have he : (∫ t : ℝ, ((Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ)) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)) *
        ((2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2) : ℝ) : ℂ) := by
    simp_rw [mrt_weighted_square_expansion]
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply sum_congr rfl
        intro j _
        rw [integral_const_mul, integral_mrtMeanSquareKernel hT]
      · intro j _
        exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
    · intro i _
      apply integrable_finsetSum
      intro j _
      exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
  rw [integral_complex_ofReal] at he
  have hr := congrArg Complex.re he
  simpa only [ofReal_re, Complex.re_sum, mul_re, ofReal_im, mul_zero, sub_zero] using hr

/-- The exact integral is bounded by the positive kernel quadratic form. -/
lemma mrt_weighted_mean_square_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) ≤
      ∑ i ∈ S, ∑ j ∈ S, ‖a i‖ * ‖a j‖ *
        (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) := by
  rw [mrt_weighted_mean_square S a freq hT]
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  simpa only [norm_mul, norm_conj] using Complex.re_le_norm (a i * conj (a j))

/-- A symmetric positive kernel is bounded on the squared norm by its
largest row sum.  The numerical row estimate is proved separately. -/
lemma mrt_symmetric_row_bound {ι : Type*} (S : Finset ι) (K : ι → ι → ℝ)
    (v : ι → ℝ) (C : ℝ) (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, K i j ≤ C) :
    (∑ i ∈ S, ∑ j ∈ S, v i * v j * K i j) ≤ C * ∑ i ∈ S, (v i) ^ 2 := by
  have he : (∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j) =
      ∑ i ∈ S, (v i) ^ 2 * ∑ j ∈ S, K i j := by
    simp only [add_div, add_mul, sum_add_distrib]
    rw [sum_comm (s := S) (t := S) (f := fun i j => (v j) ^ 2 / 2 * K i j)]
    simp only [← mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hk : (∑ j ∈ S, K j i) = ∑ j ∈ S, K i j :=
      sum_congr rfl fun j hj => hsymm j hj i hi
    rw [hk]
    ring
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hK i hi j hj)
      nlinarith [sq_nonneg (v i - v j)]
    _ = _ := he
    _ ≤ ∑ i ∈ S, (v i) ^ 2 * C := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

theorem mrt_weighted_mean_square_of_rows {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T C : ℝ} (hT : 0 < T)
    (hrow : ∀ i ∈ S, (∑ j ∈ S, 2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) ≤ C) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) ≤
      C * ∑ i ∈ S, ‖a i‖ ^ 2 := by
  apply (mrt_weighted_mean_square_le S a freq hT).trans
  apply mrt_symmetric_row_bound S _ (fun i => ‖a i‖) C
    (fun _ _ _ _ => by positivity) _ hrow
  intro i _ j _
  rw [show (freq i - freq j) ^ 2 = (freq j - freq i) ^ 2 by ring]

lemma mrtExponentialPolynomial_continuous {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) : Continuous (mrtExponentialPolynomial S a freq) := by
  unfold mrtExponentialPolynomial
  fun_prop

lemma mrt_unweighted_mean_square_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial S a freq t‖ ^ 2) ≤
      Real.exp 1 * ∫ t : ℝ, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2 := by
  have hf := (mrtExponentialPolynomial_continuous S a freq).norm.pow 2
  have hi := mrt_weighted_square_integrable S a freq hT
  have hc : Continuous (fun t : ℝ => Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2) := by
    exact (Real.continuous_exp.comp (continuous_abs.neg.div_const T)).mul hf
  have hb : -T ≤ T := by linarith
  calc
    _ ≤ ∫ t in -T..T, Real.exp 1 * (Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on hb (hf.intervalIntegrable (-T) T)
        ((continuous_const.mul hc).intervalIntegrable (-T) T)
      intro t ht
      have hat : |t| ≤ T := abs_le.mpr ht
      have hh : 0 ≤ 1 + -|t| / T := by
        have := (div_le_one hT).mpr hat
        rw [neg_div]
        linarith
      have he : 1 ≤ Real.exp 1 * Real.exp (-|t| / T) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp hh
      change ‖mrtExponentialPolynomial S a freq t‖ ^ 2 ≤
        Real.exp 1 * (Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2)
      nlinarith [sq_nonneg ‖mrtExponentialPolynomial S a freq t‖]
    _ = Real.exp 1 * ∫ t in -T..T, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2 := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [intervalIntegral.integral_of_le hb]
      exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun t => by positivity)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDyadicMeanSquare
namespace OAI

/-! The normalized dyadic Dirichlet-polynomial mean-value estimate used in
corrected MRT Appendix A.  The coefficient bound is completely arbitrary. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open scoped _root_.BigOperators

theorem mrt_dirichlet_mean_square_subset (S : Finset ℕ) {N : ℕ}
    (hS : S ⊆ Ioc 0 N) (a : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtExponentialPolynomial S a (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      8 * Real.exp 1 * (T + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hrow : ∀ m ∈ S,
      (∑ n ∈ S, 2 * T /
        (1 + T ^ 2 * (-Real.log (m : ℝ) - -Real.log (n : ℝ)) ^ 2)) ≤
          8 * (T + (N : ℝ)) := by
    intro m hm
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, 2 * T /
          (1 + T ^ 2 * (-Real.log (m : ℝ) - -Real.log (n : ℝ)) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
      _ = ∑ n ∈ Ioc 0 N, 2 * T /
          (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2) := by
        apply sum_congr rfl
        intro n _
        have he (a b : ℝ) : (-a - -b) ^ 2 = (a - b) ^ 2 := by ring
        simp only [he]
      _ ≤ _ := mrt_logarithmic_kernel_row hT (hS hm)
  calc
    _ ≤ Real.exp 1 * ∫ t : ℝ, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a (fun n => -Real.log (n : ℝ)) t‖ ^ 2 :=
      mrt_unweighted_mean_square_le _ _ _ hT
    _ ≤ Real.exp 1 * (8 * (T + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mrt_weighted_mean_square_of_rows _ _ _ hT hrow)
        (Real.exp_pos _).le
    _ = _ := by ring




/-- On the line `Re(s)=1`, a one-bounded dyadic polynomial has mean square
`O(T/N+1)`, with the absolute constant `16e`. -/
theorem mrt_dyadic_mean_square (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (2 * N), ‖b n‖ ≤ 1) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial b N t‖ ^ 2) ≤
      16 * Real.exp 1 * (T / (N : ℝ) + 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : (∑ n ∈ Ioc N (2 * N), ‖b n / (n : ℂ)‖ ^ 2) ≤ (N : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ n ∈ Ioc N (2 * N), ((n : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hN.trans (mem_Ioc.mp hn).1
        rw [norm_div, Complex.norm_natCast]
        calc
          _ ≤ (1 / (n : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (hb n hn) hn0.le) 2
          _ = _ := by simp
      _ ≤ (N : ℝ)⁻¹ - ((2 * N : ℕ) : ℝ)⁻¹ :=
        sum_Ioc_inv_sq_le_sub (α := ℝ) hN.ne' (by omega)
      _ ≤ _ := sub_le_self _ (by positivity)
  have hbound := mrt_dirichlet_mean_square_subset (Ioc N (2 * N))
    (N := 2 * N) (by
      intro n hn
      have hn' := mem_Ioc.mp hn
      exact mem_Ioc.mpr ⟨by omega, hn'.2⟩)
    (fun n => b n / (n : ℂ)) hT
  change (∫ t in -T..T, ‖mrtDyadicPolynomial b N t‖ ^ 2) ≤ _ at hbound
  apply hbound.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + ((2 * N : ℕ) : ℝ)) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 8 * Real.exp 1 * (T / (N : ℝ) + 2) := by
      push_cast
      field_simp
    _ ≤ _ := by nlinarith [div_nonneg hT.le hNr.le, Real.exp_pos 1]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMultiplicativeReduction
namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical








@[simp] lemma mrtCorrectionLocal_zero (f : ℕ → ℂ) (p : ℕ) :
    mrtCorrectionLocal f p 0 = 1 := by
  simp [mrtCorrectionLocal]

@[simp] lemma mrtCorrectionLocal_one (f : ℕ → ℂ) (h1 : f 1 = 1) (p : ℕ) :
    mrtCorrectionLocal f p 1 = 0 := by
  simp [mrtCorrectionLocal, h1]






@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := if_neg hn.ne'




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitCorrection
namespace OAI

/-! The exact convolution with the constant-one function used for the
near-twist renormalization. Its prime coefficients are the actual deviation
from one, including missing-prime masks. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



@[simp] lemma halaszUnitCorrectionLocal_zero (F : ℕ → ℂ) (p : ℕ) :
    halaszUnitCorrectionLocal F p 0 = 1 := by simp [halaszUnitCorrectionLocal]









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowKernel
namespace OAI

/-! A uniform Fourier kernel for all relative windows up to a given size.
No multiplicativity assumptions enter this finite analytic estimate. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.Classical


lemma mrt_log_dirichlet_norm (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖mrtLogDirichlet S a t‖ ≤
      ∑ n ∈ S, ‖a n‖ * Real.exp (-Real.log (n:ℝ)) := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.one_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, mul_one, neg_one_mul, le_refl]









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortEnergy
namespace OAI

/-! The normalized fixed-h Fourier estimate, in the usual low/high
frequency kernel, and its exact finite Dirichlet-polynomial form. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.Classical





lemma mrt_log_dirichlet_polynomial (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) (t : ℝ) :
    mrtLogDirichlet S a t =
      mrtExponentialPolynomial S (fun n => a n/(n:ℂ))
        (fun n => -Real.log (n:ℝ)) t := by
  unfold mrtLogDirichlet mrtExponentialPolynomial
  apply sum_congr rfl
  intro n hnS
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn n hnS
  have he : -((1:ℂ)+(t:ℂ)*Complex.I)*(Real.log (n:ℝ):ℂ) =
      ((-Real.log (n:ℝ):ℝ):ℂ) + ((-Real.log (n:ℝ)*t:ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hn0]
  push_cast
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFrequencyTail
namespace OAI

/-! Partial summation of a frequency mean square. This elementary tail
estimate allows the finite-height MRT bounds to be used with the full
fixed-window Fourier kernel. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Set _root_.Filter

lemma mrt_symmetric_prefix (F : ℝ → ℝ) (hF : Continuous F) (x : ℝ) :
    (∫ t in (0:ℝ)..x, F t + F (-t)) = ∫ t in -x..x, F t := by
  rw [intervalIntegral.integral_add (hF.intervalIntegrable _ _)
    (show IntervalIntegrable (fun t => F (-t)) volume 0 x from
      (hF.comp continuous_neg).intervalIntegrable _ _), intervalIntegral.integral_comp_neg]
  simp only [neg_zero]
  rw [add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)

theorem mrt_frequency_tail_finite (F : ℝ → ℝ) (hF : Continuous F)
    (hFn : ∀ t, 0 ≤ F t) {N R U A : ℝ} (hN : 0 < N) (hNR : N ≤ R)
    (hRU : R ≤ U) (hA : 0 ≤ A)
    (hmean : ∀ t, N ≤ t → t ≤ U → (∫ v in -t..t, F v) ≤ A * (t/N+1)) :
    (∫ t in R..U, (F t+F (-t))/t^2) ≤ 4*A/(N*R) := by
  let B : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, F t+F (-t)
  have hfc : Continuous (fun t => F t+F (-t)) := hF.add (hF.comp continuous_neg)
  have hB : Continuous B :=
    (intervalIntegral.differentiable_integral_of_continuous hfc).continuous
  have hB' (x : ℝ) : HasDerivAt B (F x+F (-x)) x :=
    intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable _ _)
      hfc.aestronglyMeasurable.stronglyMeasurableAtFilter hfc.continuousAt
  have hR : 0 < R := lt_of_lt_of_le hN hNR
  have hU : 0 < U := lt_of_lt_of_le hR hRU
  have hx0 (x : ℝ) (hx : x ∈ uIcc R U) : 0 < x := by
    rw [uIcc_of_le hRU] at hx
    exact lt_of_lt_of_le hR hx.1
  have hui : ContinuousOn (fun x : ℝ => (x^2)⁻¹) (uIcc R U) :=
    (continuous_id.pow 2).continuousOn.inv₀ (fun x hx => pow_ne_zero 2 (hx0 x hx).ne')
  have hu' : ContinuousOn (fun x : ℝ => -2/x^3) (uIcc R U) :=
    continuousOn_const.div (continuous_id.pow 3).continuousOn
      (fun x hx => pow_ne_zero 3 (hx0 x hx).ne')
  have huid (x : ℝ) (hx : x ∈ Ioo (min R U) (max R U)) :
      HasDerivAt (fun x : ℝ => (x^2)⁻¹) (-2/x^3) x := by
    have hxp : 0 < x := lt_of_lt_of_le hR (by
      simpa only [min_eq_left hRU] using hx.1.le)
    have hd := ((hasDerivAt_id x).pow 2).inv (pow_ne_zero 2 hxp.ne')
    change HasDerivAt (fun y : ℝ => (y^2)⁻¹) (-(2*x^(2-1)*1)/(x^2)^2) x at hd
    convert (preTransparency := .instances) hd using 1
    field_simp
    ring
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hui hB.continuousOn huid (fun x _ => hB' x)
    hu'.intervalIntegrable (hfc.intervalIntegrable R U)
  have hBp (x : ℝ) (hx : N ≤ x) (hxU : x ≤ U) : B x ≤ 2*A*x/N := by
    have hbound := hmean x hx hxU
    rw [← mrt_symmetric_prefix F hF x] at hbound
    change B x ≤ A*(x/N+1) at hbound
    have hn : 1 ≤ x/N := (le_div_iff₀ hN).mpr (by simpa using hx)
    have := mul_nonneg hA (sub_nonneg.mpr hn)
    have he : 2*A*x/N = 2*A*(x/N) := by ring
    rw [he]
    nlinarith
  have hBn (x : ℝ) (hx : 0 ≤ x) : 0 ≤ B x :=
    intervalIntegral.integral_nonneg hx (fun t _ => add_nonneg (hFn t) (hFn (-t)))
  have hratio : (∫ t in R..U, 2*B t/t^3) ≤
      (4*A/N) * (R⁻¹-U⁻¹) := by
    have hle := intervalIntegral.integral_mono_on (μ := volume) hRU
      ((hB.continuousOn.const_mul 2).div (continuous_id.pow 3).continuousOn
        (fun x hx => pow_ne_zero 3 (hx0 x hx).ne')).intervalIntegrable
      ((hui.const_mul (4*A/N)).intervalIntegrable) (fun t ht => by
        have htp : 0 < t := lt_of_lt_of_le hR ht.1
        have hBt := hBp t (hNR.trans ht.1) ht.2
        calc
          _ ≤ 2*(2*A*t/N)/t^3 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hBt (by norm_num))
              (pow_nonneg htp.le 3)
          _ = _ := by field_simp; ring)
    rw [intervalIntegral.integral_const_mul] at hle
    have hint : (∫ t in R..U, (t^2)⁻¹) = R⁻¹-U⁻¹ := by
      have hh := integral_zpow (a := R) (b := U) (n := (-2:ℤ))
        (Or.inr ⟨by norm_num, notMem_uIcc_of_lt hR hU⟩)
      norm_num at hh
      simpa only [div_neg, div_one, neg_sub] using hh
    rwa [hint] at hle
  have he : (∫ t in R..U, (F t+F (-t))/t^2) =
      B U/U^2-B R/R^2 + ∫ t in R..U, 2*B t/t^3 := by
    convert (preTransparency := .instances) hparts using 1
    · apply intervalIntegral.integral_congr
      intro t _
      simp only [div_eq_mul_inv]
      ring
    · have hi : (∫ t in R..U, -2/t^3*B t) = -(∫ t in R..U, 2*B t/t^3) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro t _
        ring
      rw [hi]
      simp only [div_eq_mul_inv]
      ring
  rw [he]
  have htop : B U/U^2 ≤ 2*A/(N*U) := by
    apply (div_le_div_of_nonneg_right (hBp U (hNR.trans hRU) le_rfl) (sq_nonneg U)).trans_eq
    field_simp
  have hbot : 0 ≤ B R/R^2 := div_nonneg (hBn R hR.le) (sq_nonneg R)
  calc
    _ ≤ 2*A/(N*U) + (4*A/N)*(R⁻¹-U⁻¹) := by linarith
    _ = 4*A/(N*R)-2*A/(N*U) := by ring
    _ ≤ _ := sub_le_self _ (by positivity)

theorem mrt_frequency_tail_infinite (F : ℝ → ℝ) (hF : Continuous F)
    (hFn : ∀ t, 0 ≤ F t) {N R A : ℝ} (hN : 0 < N) (hNR : N ≤ R)
    (hA : 0 ≤ A)
    (hmean : ∀ t, N ≤ t → (∫ v in -t..t, F v) ≤ A*(t/N+1))
    (htail : IntegrableOn (fun t => (F t+F (-t))/t^2) (Ioi R)) :
    (∫ t in Ioi R, (F t+F (-t))/t^2) ≤ 4*A/(N*R) := by
  apply le_of_tendsto
    (intervalIntegral_tendsto_integral_Ioi R htail (tendsto_id :
      Filter.Tendsto (fun U : ℝ => U) Filter.atTop Filter.atTop))
  filter_upwards [Filter.eventually_ge_atTop R] with U hRU
  exact mrt_frequency_tail_finite F hF hFn hN hNR hRU hA
    (fun t ht _ => hmean t ht)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTKernelTail
namespace OAI

/-! Finite-height mean-square estimates control the entire short-window
kernel. The frequencies beyond the polynomial length cost only `(T/N)^2`. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Set

lemma mrt_short_kernel_continuous (T : ℝ) : Continuous (mrtShortKernel T) := by
  exact continuous_const.min (continuous_const.div
    (continuous_const.add (continuous_id.pow 2)) (fun t => by positivity))

lemma mrt_bounded_square_tail_integrable (F : ℝ → ℝ) (hF : Continuous F)
    (hFn : ∀ t, 0 ≤ F t) {C R : ℝ} (hC : ∀ t, F t ≤ C) (hR : 0 < R) :
    IntegrableOn (fun t => (F t+F (-t))/t^2) (Ioi R) := by
  have hi : IntegrableOn (fun t : ℝ => (t^2)⁻¹) (Ioi R) := by
    apply (integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) hR).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    rw [Real.rpow_neg (hR.trans ht).le, Real.rpow_two]
  have hm : Measurable (fun t : ℝ => (F t+F (-t))/t^2) := by fun_prop
  apply (hi.const_mul (2*C)).mono' hm.aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (add_nonneg (hFn _) (hFn _))
    (sq_nonneg _))]
  calc
    _ ≤ (2*C)/t^2 := div_le_div_of_nonneg_right (by linarith [hC t, hC (-t)])
      (sq_nonneg _)
    _ = _ := by ring

lemma mrt_bounded_kernel_integrable (F : ℝ → ℝ) (hF : Continuous F)
    (hFn : ∀ t, 0 ≤ F t) {C : ℝ} (hC : ∀ t, F t ≤ C) (T : ℝ) :
    Integrable (fun t => mrtShortKernel T t * F t) := by
  apply (integrable_inv_one_add_sq.const_mul (T^2*C)).mono'
    ((mrt_short_kernel_continuous T).mul hF).aestronglyMeasurable
  filter_upwards with t
  have hk : 0 ≤ mrtShortKernel T t := le_min (by norm_num) (by positivity)
  change ‖mrtShortKernel T t * F t‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk (hFn t))]
  calc
    _ ≤ (T^2/(1+t^2))*C := mul_le_mul (min_le_right _ _) (hC t) (hFn t)
      (by positivity)
    _ = _ := by ring

lemma mrt_integral_symmetric_halves (G : ℝ → ℝ) (hG : Integrable G) :
    (∫ t : ℝ, G t) = ∫ t in Ioi (0:ℝ), G t+G (-t) := by
  have hGn : Integrable (fun t => G (-t)) := hG.comp_neg
  rw [integral_add hG.integrableOn hGn.integrableOn,
    integral_comp_neg_Ioi, neg_zero]
  exact (intervalIntegral.integral_Iic_add_Ioi hG.integrableOn hG.integrableOn).symm.trans
    (add_comm _ _)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLinearKernel
namespace OAI

/-! A finite-height kernel bound measured at the natural short-window
frequency scale. It preserves the linear first-prime-band cost. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Set

theorem mrt_short_kernel_linear_height (F : ℝ → ℝ) (hF : Continuous F)
    (hFn : ∀ t, 0 ≤ F t) {C N T ε A : ℝ} (hC : ∀ t, F t ≤ C)
    (hN : 0 < N) (hT : 0 < T) (hTN : T ≤ N) (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hsmall : ∀ v, T ≤ v → v ≤ N →
      (∫ t in -v..v, F t) ≤ ε*(v/T+1))
    (hglobal : ∀ v, N ≤ v → (∫ t in -v..v, F t) ≤ A*(v/N+1)) :
    (∫ t : ℝ, mrtShortKernel T t * F t) ≤ 6*ε+4*A*(T/N)^2 := by
  let G : ℝ → ℝ := fun t => mrtShortKernel T t * (F t+F (-t))
  have hKi := mrt_bounded_kernel_integrable F hF hFn hC T
  have hGi : Integrable G := by
    have he : G = fun t => mrtShortKernel T t*F t +
        (fun t => mrtShortKernel T t*F t) (-t) := by
      funext t
      simp only [G, mrtShortKernel, neg_sq]
      ring
    rw [he]
    exact hKi.add hKi.comp_neg
  have hGe : (∫ t : ℝ, mrtShortKernel T t * F t) = ∫ t in Ioi (0:ℝ), G t := by
    rw [mrt_integral_symmetric_halves _ hKi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [G, mrtShortKernel, neg_sq]
    ring
  have hGcont : Continuous G := (mrt_short_kernel_continuous T).mul
    (hF.add (hF.comp continuous_neg))
  have hlow : (∫ t in (0:ℝ)..T, G t) ≤ 2*ε := by
    have hfi : IntervalIntegrable (fun t => F t+F (-t)) volume 0 T :=
      (hF.add (hF.comp continuous_neg)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on (μ := volume) hT.le
      (hGcont.intervalIntegrable _ _) hfi
      (fun t _ => mul_le_of_le_one_left (add_nonneg (hFn _) (hFn _)) (min_le_left _ _))
    rw [mrt_symmetric_prefix F hF T] at hm
    apply hm.trans ((hsmall T le_rfl hTN).trans _)
    rw [div_self hT.ne']
    ring_nf
    exact le_rfl
  have hmid : (∫ t in T..N, G t) ≤ 4*ε := by
    have hratio := mrt_frequency_tail_finite F hF hFn hT le_rfl hTN hε hsmall
    have hct : ContinuousOn (fun t => (F t+F (-t))/t^2) (uIcc T N) := by
      apply (hF.add (hF.comp continuous_neg)).continuousOn.div
        (continuous_id.pow 2).continuousOn
      intro t ht
      rw [uIcc_of_le hTN] at ht
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hT ht.1))
    have hwi : IntervalIntegrable (fun t => T^2*((F t+F (-t))/t^2)) volume T N :=
      (hct.const_mul (T^2)).intervalIntegrable
    have hm := intervalIntegral.integral_mono_on (μ := volume) hTN
      (hGcont.intervalIntegrable _ _) hwi (fun t ht => by
          have ht0 := hT.trans_le ht.1
          have hk : mrtShortKernel T t ≤ T^2/t^2 :=
            (min_le_right _ _).trans (div_le_div_of_nonneg_left (sq_nonneg T)
              (sq_pos_of_pos ht0) (by linarith))
          calc
            G t ≤ (T^2/t^2)*(F t+F (-t)) :=
              mul_le_mul_of_nonneg_right hk (add_nonneg (hFn t) (hFn (-t)))
            _ = _ := by ring)
    rw [intervalIntegral.integral_const_mul] at hm
    calc
      _ ≤ T^2*(4*ε/(T*T)) := hm.trans
        (mul_le_mul_of_nonneg_left hratio (sq_nonneg _))
      _ = _ := by field_simp
  have htaili := mrt_bounded_square_tail_integrable F hF hFn hC hN
  have htail := mrt_frequency_tail_infinite F hF hFn hN le_rfl hA hglobal htaili
  have hhigh : (∫ t in Ioi N, G t) ≤ 4*A*(T/N)^2 := by
    have hm := setIntegral_mono_on hGi.integrableOn (htaili.const_mul (T^2))
      measurableSet_Ioi (fun t ht => by
        have ht0 := hN.trans ht
        have hk : mrtShortKernel T t ≤ T^2/t^2 :=
          (min_le_right _ _).trans (div_le_div_of_nonneg_left (sq_nonneg T)
            (sq_pos_of_pos ht0) (by linarith))
        calc
          G t ≤ (T^2/t^2)*(F t+F (-t)) :=
            mul_le_mul_of_nonneg_right hk (add_nonneg (hFn t) (hFn (-t)))
          _ = _ := by ring)
    rw [integral_const_mul] at hm
    calc
      _ ≤ T^2*(4*A/(N*N)) := hm.trans (mul_le_mul_of_nonneg_left htail (sq_nonneg _))
      _ = _ := by ring
  rw [hGe, ← intervalIntegral.integral_interval_add_Ioi (a := 0) (b := N)
    hGi.integrableOn hGi.integrableOn,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hGcont.intervalIntegrable 0 T) (hGcont.intervalIntegrable T N)]
  linarith

lemma mrt_linear_prefix_two_slopes {N T Q v A B : ℝ}
    (hN : 0 < N) (hT : 0 < T) (hTN : T ≤ N) (hQ : 0 ≤ Q)
    (hv : 0 ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A*(v/N+1)+B*(v*Q/N+1) ≤
      (A+B*(1+T*Q/N))*(v/T+1) := by
  have hdiv : v/N ≤ v/T := div_le_div_of_nonneg_left hv hT hTN
  have he : (1+T*Q/N)*(v/T+1)-(v*Q/N+1) = v/T+T*Q/N := by
    field_simp
    ring
  have hlin : v*Q/N+1 ≤ (1+T*Q/N)*(v/T+1) := by
    have hn : 0 ≤ v/T+T*Q/N := by positivity
    linarith
  calc
    _ ≤ A*(v/T+1)+B*((1+T*Q/N)*(v/T+1)) :=
      add_le_add (mul_le_mul_of_nonneg_left (by linarith) hA)
        (mul_le_mul_of_nonneg_left hlin hB)
    _ = _ := by ring



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse
namespace OAI

/-! Coarse Ramaré factorization on the actual typical-factorization set.
Removing a prime from the selected band leaves precisely the other-band
mask; the square and endpoint errors retain their uniform finite bounds. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrtTypicalCoefficient_oneBounded {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F) :
    OneBounded (mrtTypicalCoefficient J P F) := by
  intro n hn
  unfold mrtTypicalCoefficient
  split_ifs
  · exact hF n hn
  · simp





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MellinCalculus
namespace Erdos970

open scoped _root_.ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory _root_.Set _root_.Function



variable {𝕂 : Type*} [RCLike 𝕂]








@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

















local notation (name := mellintransform) "𝓜" => mellin















@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le


























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log













































attribute [fun_prop] measurable_from_top












section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeBands
namespace OAI

/-! Prime-band reciprocal masses used in MRT's typical-factorization sieve.
The reciprocal-mass bounds follow from Mertens’ theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma mrtPrimeBand_prime {P Q : ℝ} {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : p.Prime :=
  sievePrimesUpTo_prime Q p (mem_sdiff.mp hp).1

lemma mrtPrimeBand_bounds {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : P < p ∧ (p : ℝ) ≤ Q := by
  have hpQ := (mem_sdiff.mp hp).1
  have hpP := (mem_sdiff.mp hp).2
  refine ⟨?_, sievePrimesUpTo_le Q hQ p hpQ⟩
  by_contra hnot
  have hple : (p : ℝ) ≤ P := le_of_not_gt hnot
  exact hpP (mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff hP).mpr hple),
    mrtPrimeBand_prime hp⟩)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandParameters
namespace OAI

/-! The explicit prime-band endpoints from MRT, Definition 2.1. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical






lemma mrt_band_endpoints (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogQ : 1 ≤ Real.log Q) :
    2 ≤ mrtBandLower P Q j ∧ mrtBandLower P Q j ≤ mrtBandUpper Q j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp0 : 0 < P := by linarith
  have hq0 : 0 < Q := hp0.trans_le hPQ
  have hlp : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  have hlpq : Real.log P ≤ Real.log Q := Real.log_le_log hp0 hPQ
  have hc : 1 ≤ (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj1) (one_le_pow₀ hlogQ)
  constructor
  · calc
      2 ≤ P := hP
      _ = Real.exp (Real.log P) := (Real.exp_log hp0).symm
      _ ≤ mrtBandLower P Q j := by
        apply Real.exp_le_exp.mpr
        nlinarith
  · apply Real.exp_le_exp.mpr
    have hpow : (Real.log Q) ^ j = (Real.log Q) ^ (j - 1) * Real.log Q := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) * Real.log P ≤
          (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) * Real.log Q :=
        mul_le_mul_of_nonneg_left hlpq (by positivity)
      _ = (j : ℝ) ^ (4 * j) * Real.log Q ^ j := by rw [hpow]; ring
      _ ≤ (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hj1 (by omega)) (by positivity)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandSeparation
namespace OAI

/-! The actual MRT bands are disjoint, as required by the corrected
Ramaré decomposition; no disjointness hypothesis on those bands remains. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_adjacent_band_gap (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandUpper Q j < mrtBandLower P Q (j + 1) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hpow : (j : ℝ) ^ (4 * j + 2) ≤ ((j : ℝ) + 1) ^ (4 * (j + 1)) := by
    calc
      _ ≤ ((j : ℝ) + 1) ^ (4 * j + 2) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  apply Real.exp_lt_exp.mpr
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hmul := mul_le_mul_of_nonneg_right hpow (pow_nonneg hlogQ.le j)
  have hp : 0 < (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j := by positivity
  nlinarith

lemma mrt_band_lower_monotone (P Q : ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandLower P Q i ≤ mrtBandLower P Q j := by
  have hlogQ : 1 ≤ Real.log Q :=
    hlogP.le.trans (Real.log_le_log (by linarith) hPQ)
  refine Nat.le_induction le_rfl (fun k hk ih => ?_) j hij
  exact ih.trans (((mrt_band_endpoints P Q k (hi.trans hk) hP hPQ hlogQ).2).trans
    (mrt_adjacent_band_gap P Q k (hi.trans hk) hP hPQ hlogP).le)

lemma mrt_band_gap (P Q : ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i < j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandUpper Q i < mrtBandLower P Q j :=
  (mrt_adjacent_band_gap P Q i hi hP hPQ hlogP).trans_le
    (mrt_band_lower_monotone P Q (i + 1) j (by omega) (by omega) hP hPQ hlogP)

theorem mrt_actual_bands_pairwise_disjoint (P Q : ℝ) (J : ℕ)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    Set.PairwiseDisjoint (Set.univ : Set {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)})
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) := by
  intro i _ j _ hij
  apply disjoint_left.mpr
  intro p hpi hpj
  have hi := mem_Icc.mp i.property
  have hj := mem_Icc.mp j.property
  have hn : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have hlogQ : 1 ≤ Real.log Q :=
    hlogP.le.trans (Real.log_le_log (by linarith) hPQ)
  have hip := mrtPrimeBand_bounds
    ((mrt_band_endpoints P Q i hi.1 hP hPQ hlogQ).1.trans' (by norm_num))
    (Real.exp_pos _).le hpi
  have hjp := mrtPrimeBand_bounds
    ((mrt_band_endpoints P Q j hj.1 hP hPQ hlogQ).1.trans' (by norm_num))
    (Real.exp_pos _).le hpj
  change mrtBandLower P Q i < (p : ℝ) ∧ (p : ℝ) ≤ mrtBandUpper Q i at hip
  change mrtBandLower P Q j < (p : ℝ) ∧ (p : ℝ) ≤ mrtBandUpper Q j at hjp
  rcases lt_or_gt_of_ne hn with hij' | hji'
  · have hgap := mrt_band_gap P Q i j hi.1 hij' hP hPQ hlogP
    linarith
  · have hgap := mrt_band_gap P Q j i hj.1 hji' hP hPQ hlogP
    linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrincipalPsi
namespace OAI

/-! The principal character only removes powers of five.  For the required
error bound it is enough to charge the prime 5 once, and all remaining
terms to the already proved elementary prime-power error. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeNumberTheorem
namespace OAI

/-! The fixed modulus-five prime number theorem follows from the three
nonprincipal contour estimates, the zeta prime number theorem, and finite
character orthogonality. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseCells
namespace OAI

/-! Unit cells for the elementary power-sum approximation. Centering the
cells cancels the linear phase error, leaving a summable quadratic error. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset


@[simp] lemma halasz_power_phase_norm (t x : ℝ) : ‖halaszPowerPhase t x‖ = 1 := by
  simp [halaszPowerPhase, Complex.norm_exp, Complex.mul_re]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszBandDensity
namespace OAI

/-! Literal natural-indexed MRT bands in the dyadic density and
pairwise-disjointness interfaces used by the energy estimates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma halasz_actual_bands_disjoint (P Q : ℝ) (J : ℕ)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    Set.PairwiseDisjoint (Icc 1 J : Set ℕ)
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) := by
  have hh := mrt_actual_bands_pairwise_disjoint P Q J hP hPQ hlogP
  intro i hi j hj hij
  exact @hh ⟨i, hi⟩ (Set.mem_univ _) ⟨j, hj⟩ (Set.mem_univ _)
    (fun he => hij (congrArg Subtype.val he))


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszShortL1
namespace OAI

/-! The typical-set error is linear in its density in the published L1
norm. No square root of the discarded density is introduced. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_short_integral_cells (F : ℕ → ℂ) (A N H : ℕ) (α : ℝ) :
    (∫ x in (A:ℝ)..(A+N:ℕ), ‖shortExponentialSum F H α x‖) =
      ∑ v ∈ range N, ‖shortExponentialSum F H α (A+v:ℕ)‖ := by
  symm
  calc
    _ = ∑ v ∈ range N, ∫ x in (A+v:ℕ)..(A+v+1:ℕ),
        ‖shortExponentialSum F H α x‖ := by
      apply sum_congr rfl
      intro v _
      simpa only [Nat.cast_add, Nat.cast_one] using
        (integral_shortExponentialSum_unit F H α (A+v)).symm
    _ = _ := by
      simpa only [Nat.add_zero, Nat.add_assoc] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun n : ℕ => ((A+n:ℕ):ℝ)) (n := N)
          (fun v _ => by simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, add_assoc] using
            shortExponentialSum_unit_integrable F H α (A+v)))




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszShortMean
namespace OAI

/-! Convert the actual typical short-sum energy to the published L1
quantity while retaining the linear error from discarded integers. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_short_square_cells (F : ℕ → ℂ) (A N H : ℕ) (α : ℝ) :
    (∫ x in (A:ℝ)..(A+N:ℕ), ‖shortExponentialSum F H α x‖^2) =
      ∑ v ∈ range N, ‖shortExponentialSum F H α (A+v:ℕ)‖^2 := by
  have hi (v : ℕ) : IntervalIntegrable (fun x => ‖shortExponentialSum F H α x‖^2)
      volume (v:ℝ) (v+1) := by
    apply (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => ‖shortExponentialSum F H α v‖^2) volume (v:ℝ) (v+1)).congr_uIoo
    intro x hx
    rw [Set.uIoo_of_le (by linarith : (v:ℝ) ≤ v+1)] at hx
    dsimp only
    rw [shortExponentialSum_on_unit_cell F H α v ⟨hx.1.le, hx.2⟩]
  have he (v : ℕ) : (∫ x in (v:ℝ)..(v+1), ‖shortExponentialSum F H α x‖^2) =
      ‖shortExponentialSum F H α v‖^2 := by
    calc
      _ = ∫ _x in (v:ℝ)..(v+1), ‖shortExponentialSum F H α v‖^2 := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro x hx
        dsimp only
        rw [shortExponentialSum_on_unit_cell F H α v ⟨hx.1.le, hx.2⟩]
      _ = _ := by simp
  symm
  calc
    _ = ∑ v ∈ range N, ∫ x in (A+v:ℕ)..(A+v+1:ℕ),
        ‖shortExponentialSum F H α x‖^2 := by
      apply sum_congr rfl
      intro v _
      simpa only [Nat.cast_add, Nat.cast_one] using (he (A+v)).symm
    _ = _ := by
      simpa only [Nat.add_zero, Nat.add_assoc] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun n : ℕ => ((A+n:ℕ):ℝ)) (n := N)
          (fun v _ => by simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, add_assoc] using hi (A+v)))

lemma halasz_short_mean_square (F : ℕ → ℂ) {N H : ℕ}
    (hN : 0 < N) (hH : 0 < H) (α : ℝ) :
    ((∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum F H α x‖) / ((N:ℝ)*H))^2 ≤
      (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum F H α x‖^2) / ((N:ℝ)*(H:ℝ)^2) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hs := sum_mul_sq_le_sq_mul_sq (range N) (fun _ => (1:ℝ))
    (fun v => ‖shortExponentialSum F H α (N+v:ℕ)‖)
  simp only [one_mul, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at hs
  have he : (2*(N:ℝ)) = ((N+N:ℕ):ℝ) := by push_cast; ring
  rw [he, halasz_short_integral_cells, halasz_short_square_cells]
  calc
    _ = (∑ v ∈ range N, ‖shortExponentialSum F H α (N+v:ℕ)‖)^2 /
        ((N:ℝ)^2*(H:ℝ)^2) := by rw [div_pow, mul_pow]
    _ ≤ ((N:ℝ)*(∑ v ∈ range N, ‖shortExponentialSum F H α (N+v:ℕ)‖^2)) /
        ((N:ℝ)^2*(H:ℝ)^2) := div_le_div_of_nonneg_right hs (by positivity)
    _ = _ := by field_simp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogKernelQuarter
namespace OAI

/-! The short-window kernel needs spectral information only below one quarter
of the polynomial length. The rest uses the unconditional mean square. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical

theorem mrt_dyadic_kernel_quarter_height (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Finset.Ioc N (2*N), ‖b n‖ ≤ 1)
    {T ε : ℝ} (hT : 0 < T) (hTN : T ≤ (N:ℝ)/4) (hε : 0 ≤ ε)
    (hsmall : ∀ v, T ≤ v → v ≤ (N:ℝ)/4 →
      (∫ t in -v..v, ‖mrtDyadicPolynomial b N t‖^2) ≤ ε*(v/T+1)) :
    (∫ t : ℝ, mrtShortKernel T t * ‖mrtDyadicPolynomial b N t‖^2) ≤
      6*ε+1024*Real.exp 1*(T/N)^2 := by
  let C : ℝ := (∑ n ∈ Finset.Ioc N (2*N), ‖b n‖*Real.exp (-Real.log (n:ℝ)))^2
  have he (t : ℝ) : mrtLogDirichlet (Finset.Ioc N (2*N)) b t =
      mrtDyadicPolynomial b N t :=
    mrt_log_dirichlet_polynomial _ (fun n hn =>
      lt_trans hN (Finset.mem_Ioc.mp hn).1) b t
  have hFc : Continuous (fun t => ‖mrtDyadicPolynomial b N t‖^2) :=
    (mrtExponentialPolynomial_continuous _ _ _).norm.pow 2
  have hbound (t : ℝ) : ‖mrtDyadicPolynomial b N t‖^2 ≤ C := by
    rw [← he]
    exact pow_le_pow_left₀ (norm_nonneg _) (mrt_log_dirichlet_norm _ _ t) 2
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hquarter : 0 < (N:ℝ)/4 := by positivity
  have hglobal (v : ℝ) (hv : (N:ℝ)/4 ≤ v) :
      (∫ t in -v..v, ‖mrtDyadicPolynomial b N t‖^2) ≤
        (16*Real.exp 1)*(v/((N:ℝ)/4)+1) := by
    have hh := mrt_dyadic_mean_square b hN hb (hquarter.trans_le hv)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (div_le_div_of_nonneg_left (hquarter.trans_le hv).le hquarter
      (by linarith)) le_rfl
  have hm := mrt_short_kernel_linear_height _ hFc (fun _ => sq_nonneg _)
    hbound hquarter hT hTN hε (by positivity : 0 ≤ 16*Real.exp 1) hsmall hglobal
  apply hm.trans_eq
  field_simp [hNr.ne']
  ring

theorem mrt_log_kernel_quarter_bound (V : ℕ → Finset ℕ) (J : ℕ)
    (hprime : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (Finset.Icc 1 J : Set ℕ) V)
    {P Q η : ℝ} (hP0 : 0 < P) (hQ0 : 0 < Q)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q) (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j)
    {N : ℕ} (hN : 0 < N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T δ : ℝ} (hT : 0 < T) (hTN : T ≤ (N:ℝ)/4) (hδ : 0 ≤ δ)
    (hnone : ∀ v : ℝ, T ≤ v → v ≤ (N:ℝ)/4 →
      (∫ t in Ioc (-v) v ∩ mrtNoSmallBand (mrtLogFamilyBins P Q η)
        (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
          δ*(v/N+1)) :
    (∫ t : ℝ, mrtShortKernel T t *
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
      6*(δ + 33792*Real.exp 1*(mrtBaseResolution P Q η)⁻¹ + 2*P⁻¹ +
        1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+T*Q/N)) +
        1024*Real.exp 1*(T/N)^2 := by
  let A := δ + 33792*Real.exp 1*(mrtBaseResolution P Q η)⁻¹ + 2*P⁻¹
  let B := 1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hε : 0 ≤ A+B*(1+T*Q/N) := by positivity
  have hs (v : ℝ) (hv : T ≤ v) (hvN : v ≤ (N:ℝ)/4) :
      (∫ t in -v..v,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
        (A+B*(1+T*Q/N))*(v/T+1) := by
    have hv0 : 0 < v := hT.trans_le hv
    have he := mrt_log_energy_partition_bound V J hprime hdis hP0 hQ0 hP hQ hPQ
      hη hη' hbudget hH hrange hN hsize F hF hFb hv0
    calc
      _ ≤ δ*(v/N+1) +
          (33792*Real.exp 1*(v/N+1)*(mrtBaseResolution P Q η)⁻¹ +
          1024*Real.exp 2*(v*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ +
          2*(v/N+1)*P⁻¹) := he.trans (add_le_add (hnone v hv hvN) le_rfl)
      _ = A*(v/N+1)+B*(v*Q/N+1) := by dsimp [A, B]; ring
      _ ≤ _ := mrt_linear_prefix_two_slopes (by exact_mod_cast hN) hT (by linarith : T ≤ (N:ℝ)) hQ0.le
        hv0.le hA hB
  exact mrt_dyadic_kernel_quarter_height _ hN
    (fun n hn => mrtTypicalCoefficient_oneBounded _ _ _ hFb n
      (hN.trans (Finset.mem_Ioc.mp hn).1)) hT hTN hε hs

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogShortQuarter
namespace OAI

/-! The literal short sum from quarter-height spectral information for both
dyadic polynomials. The omitted frequencies use only generic mean square. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical

theorem mrt_log_short_energy_quarter (V : ℕ → Finset ℕ) (J : ℕ)
    (hprime : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (Finset.Icc 1 J : Set ℕ) V)
    {P Q η : ℝ} (hP0 : 0 < P) (hQ0 : 0 < Q)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q) (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hres : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j)
    {N H : ℕ} (hH4 : 4 ≤ H) (hHN : H ≤ N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnone : ∀ k ∈ ({N, 2*N} : Finset ℕ), ∀ v : ℝ, (N:ℝ)/H ≤ v → v ≤ (k:ℝ)/4 →
      (∫ t in Ioc (-v) v ∩ mrtNoSmallBand (mrtLogFamilyBins P Q η)
        (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) k t‖^2) ≤
          δ*(v/k+1)) :
    (∫ x in (N:ℝ)..(2*N),
      ‖shortExponentialSum (mrtTypicalCoefficient (Finset.Icc 1 J) V F) H 0 x‖^2) /
        ((N:ℝ)*(H:ℝ)^2) ≤
      (139968/(2*Real.pi)) *
        (12*(δ + 33792*Real.exp 1*(mrtBaseResolution P Q η)⁻¹ + 2*P⁻¹ +
          1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+Q/H)) +
          2048*Real.exp 1/(H:ℝ)^2) := by
  have hH : 0 < H := by omega
  have hN : 0 < N := hH.trans_le hHN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hH1 : (4:ℝ) ≤ H := by exact_mod_cast hH4
  have hTN : (N:ℝ)/H ≤ (N:ℝ)/4 := (div_le_iff₀ hHr).mpr (by nlinarith)
  let ε := δ + 33792*Real.exp 1*(mrtBaseResolution P Q η)⁻¹ + 2*P⁻¹ +
    1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+Q/H)
  have hk (k : ℕ) (hkm : k ∈ ({N, 2*N} : Finset ℕ)) :
      (∫ t : ℝ, mrtShortKernel ((N:ℝ)/H) t *
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) k t‖^2) ≤
        6*ε+1024*Real.exp 1/(H:ℝ)^2 := by
    have hNk : N ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hkm
      omega
    have hNkr : (N:ℝ) ≤ k := by exact_mod_cast hNk
    have hkp : 0 < k := hN.trans_le hNk
    have hb := mrt_log_kernel_quarter_bound V J hprime hdis hP0 hQ0 hP hQ hPQ hη hη'
      hbudget hres hrange hkp (hsize.trans hNkr) F hF hFb (div_pos hNr hHr)
      (hTN.trans (by linarith : (N:ℝ)/4 ≤ (k:ℝ)/4)) hδ (hnone k hkm)
    have hq : ((N:ℝ)/H)*Q/k ≤ Q/H := by
      calc
        _ ≤ ((N:ℝ)/H)*Q/N :=
          div_le_div_of_nonneg_left (by positivity) hNr hNkr
        _ = _ := by field_simp
    have hratio : (((N:ℝ)/H)/k)^2 ≤ 1/(H:ℝ)^2 := by
      have hd : ((N:ℝ)/H)/k ≤ ((N:ℝ)/H)/N :=
        div_le_div_of_nonneg_left (by positivity) hNr hNkr
      have he : (((N:ℝ)/H)/N)^2 = 1/(H:ℝ)^2 := by field_simp
      exact (pow_le_pow_left₀ (by positivity) hd 2).trans_eq he
    have hc : 0 ≤ 1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹ := by positivity
    have he := mul_le_mul_of_nonneg_left hq hc
    have ht := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 1024*Real.exp 1 by positivity)
    have hterm :
        1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+(N:ℝ)/H*Q/k) ≤
        1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+Q/H) := by
      nlinarith only [he]
    apply hb.trans
    calc
      _ ≤ 6*(δ + 33792*Real.exp 1*(mrtBaseResolution P Q η)⁻¹ + 2*P⁻¹ +
          1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+Q/H)) +
          1024*Real.exp 1*(1/(H:ℝ)^2) :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hterm) (by norm_num)) ht
      _ = _ := by dsimp [ε]; ring
  have hs := add_le_add (hk N (by simp)) (hk (2*N) (by simp))
  have hb := mrt_literal_short_energy_dyadic
    (mrtTypicalCoefficient (Finset.Icc 1 J) V F) hH hHN
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change _ ≤ 12*ε+2048*Real.exp 1/(H:ℝ)^2
  calc
    _ ≤ 6*ε+1024*Real.exp 1/(H:ℝ)^2 + (6*ε+1024*Real.exp 1/(H:ℝ)^2) := hs
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalShortEnergySharp
namespace OAI

/-! The short-window energy of the literal typical coefficient, before
any exceptional integers are removed. The original distance scale and
frequency height are unchanged. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory
open scoped _root_.Classical

theorem halasz_typical_short_energy_sharp
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) →
      ∀ J : ℕ, 1 ≤ J →
      (∀ k ∈ ({N,2*N}:Finset ℕ),
        200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log k))) →
      ∀ X : ℕ, N ≤ X → X ≤ N^3 → ∀ H : ℕ, 4 ≤ H → H ≤ N → 2*Q ≤ (N:ℝ) →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u : ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) H 0 x‖^2)/
        ((N:ℝ)*(H:ℝ)^2)  ≤
      (139968/(2*Real.pi))*(12*(C*(Real.exp (-4*M/5)+
        Real.log (Real.log N)/(Real.log N)^(1/80:ℝ))+
        33792*Real.exp 1*(mrtBaseResolution P Q (1/100))⁻¹+2*P⁻¹+
        1024*Real.exp 2*(mrtBaseResolution P Q (1/100))⁻¹*(1+Q/H))+
        2048*Real.exp 1/(H:ℝ)^2) := by
  obtain ⟨C,hC,hkernel⟩ := halasz_typical_kernel_bound_sharp hprime hhigh
  refine ⟨C,hC,?_⟩
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hkernel,hl] with N hkernel hL
  intro P Q hP hPQ hlP hlQ hbudget hres J hJ hbands X hNX hXN H hH hHN hsize F hF1 hFc hFb M hM hd
  have hFm : Multiplicative F := fun a b ha hb _ => hFc a b ha hb
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  let δ := C*(Real.exp (-4*M/5)+Real.log (Real.log N)/(Real.log N)^(1/80:ℝ))
  have hδ : 0 ≤ δ := by
    have hLL : 0 ≤ Real.log (Real.log (N:ℝ)) := Real.log_nonneg hL
    dsimp [δ]
    positivity
  have hk := hkernel F hF1 hFc hFb P Q hP hPQ (by linarith) hlQ hres J hJ
    (fun k hk => ⟨(hbands k hk).1,(hbands k hk).2 J (mem_Icc.mpr ⟨hJ,le_rfl⟩)⟩)
    X hNX hXN M hM hd
  have hprimeV : ∀ j ∈ Icc 1 J, ∀ p ∈ V j, p.Prime := fun _ _ _ hp => mrtPrimeBand_prime hp
  have hdis : Set.PairwiseDisjoint (Icc 1 J : Set ℕ) V :=
    halasz_actual_bands_disjoint P Q J hP hPQ (by linarith)
  have hrange : ∀ j ∈ Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j := by
    intro j _ p hp
    have hh := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp
    exact ⟨hh.1.le,hh.2⟩
  exact mrt_log_short_energy_quarter V J hprimeV hdis (by linarith) (by linarith)
    hlP hlQ (Real.log_le_log (by linarith) hPQ) (by norm_num : (0:ℝ) < 1/100)
    (by norm_num : (1/100:ℝ) ≤ 1/12) hbudget hres hrange hH hHN hsize F hFm hFb hδ
    (fun k hk' v hv hvk => hk k hk' v
      ((div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg H)).trans hv) hvk)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcEnergyRoot
namespace OAI

/-! Taking the square root of the literal typical short energy. The
first-band resolution losses are paid before character summation. -/
namespace TwoPointCorrelations

lemma major_arc_three_term_root {B s t r : ℝ}
    (hB : 0 ≤ B) (hs : 0 ≤ s) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    Real.sqrt (B*(s^2+t^2+r^2)) ≤ (B+1)*(s+t+r) := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hcoef : B ≤ (B+1)^2 := by nlinarith [sq_nonneg B]
  have hsum : s^2+t^2+r^2 ≤ (s+t+r)^2 := by
    nlinarith [mul_nonneg hs ht,mul_nonneg hs hr,mul_nonneg ht hr]
  calc
    _ ≤ (B+1)^2*(s^2+t^2+r^2) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ (B+1)^2*(s+t+r)^2 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring


lemma major_arc_energy_constant_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < majorArcEnergyConstant C := by
  unfold majorArcEnergyConstant
  positivity

lemma major_arc_short_energy_root {C W R P H Q M δ : ℝ}
    (hC : 0 ≤ C) (hW : 1 ≤ W) (hR : W^9 ≤ R) (hP : W^2 ≤ P)
    (hH : W ≤ H) (hQ : Q/H ≤ W^7) (hδ : 0 ≤ δ) :
    Real.sqrt ((139968/(2*Real.pi))*(12*(C*(Real.exp (-4*M/5)+δ)+
      33792*Real.exp 1*R⁻¹+2*P⁻¹+1024*Real.exp 2*R⁻¹*(1+Q/H))+
      2048*Real.exp 1/H^2)) ≤
      majorArcEnergyConstant C*(Real.exp (-2*M/5)+Real.sqrt δ+W⁻¹) := by
  have hW0 : 0 < W := by linarith
  have hR0 : 0 < R := (pow_pos hW0 9).trans_le hR
  have hP0 : 0 < P := (pow_pos hW0 2).trans_le hP
  have hH0 : 0 < H := hW0.trans_le hH
  have hW5 : 1 ≤ W^7 := one_le_pow₀ hW
  have hRR : R⁻¹ ≤ (W^2)⁻¹ := by
    apply inv_anti₀ (pow_pos hW0 2)
    exact (pow_le_pow_right₀ hW (by omega : 2 ≤ 9)).trans hR
  have hPP : P⁻¹ ≤ (W^2)⁻¹ := inv_anti₀ (pow_pos hW0 2) hP
  have hHH : 1/H^2 ≤ (W^2)⁻¹ := by
    simpa only [one_div] using inv_anti₀ (pow_pos hW0 2) (pow_le_pow_left₀ hW0.le hH 2)
  have hRQ : R⁻¹*(1+Q/H) ≤ 2*(W^2)⁻¹ := by
    have hi : R⁻¹ ≤ (W^9)⁻¹ := inv_anti₀ (pow_pos hW0 9) hR
    calc
      _ ≤ R⁻¹*(2*W^7) := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hR0.le)
      _ ≤ (W^9)⁻¹*(2*W^7) := mul_le_mul_of_nonneg_right hi (by positivity)
      _ = _ := by field_simp
  let B := (139968/(2*Real.pi))*(12*(C+33792*Real.exp 1+2+2048*Real.exp 2)+2048*Real.exp 1)
  let S := Real.exp (-4*M/5)+δ+(W^2)⁻¹
  have hterm : Real.exp (-4*M/5)+δ ≤ S := by
    dsimp only [S]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (sq_nonneg W))
  have hinv : (W^2)⁻¹ ≤ S := by
    dsimp only [S]
    exact le_add_of_nonneg_left (add_nonneg (Real.exp_pos _).le hδ)
  have hbounds :
      C*(Real.exp (-4*M/5)+δ)+33792*Real.exp 1*R⁻¹+2*P⁻¹+
        1024*Real.exp 2*R⁻¹*(1+Q/H) ≤
      (C+33792*Real.exp 1+2+2048*Real.exp 2)*S := by
    have ha := mul_le_mul_of_nonneg_left hterm hC
    have hb := mul_le_mul_of_nonneg_left (hRR.trans hinv) (show 0 ≤ 33792*Real.exp 1 by positivity)
    have hc := mul_le_mul_of_nonneg_left (hPP.trans hinv) (show (0:ℝ) ≤ 2 by norm_num)
    have hd := mul_le_mul_of_nonneg_left (hRQ.trans (mul_le_mul_of_nonneg_left hinv (by norm_num : (0:ℝ)≤2)))
      (show 0 ≤ 1024*Real.exp 2 by positivity)
    nlinarith only [ha,hb,hc,hd]
  have he : (139968/(2*Real.pi))*(12*(C*(Real.exp (-4*M/5)+δ)+
      33792*Real.exp 1*R⁻¹+2*P⁻¹+1024*Real.exp 2*R⁻¹*(1+Q/H))+
      2048*Real.exp 1/H^2) ≤ B*S := by
    have ht := mul_le_mul_of_nonneg_left (hHH.trans hinv) (show 0 ≤ 2048*Real.exp 1 by positivity)
    have hi : 12*(C*(Real.exp (-4*M/5)+δ)+33792*Real.exp 1*R⁻¹+2*P⁻¹+
        1024*Real.exp 2*R⁻¹*(1+Q/H))+2048*Real.exp 1/H^2 ≤
      (12*(C+33792*Real.exp 1+2+2048*Real.exp 2)+2048*Real.exp 1)*S := by
      calc
        _ = 12*(C*(Real.exp (-4*M/5)+δ)+33792*Real.exp 1*R⁻¹+2*P⁻¹+
            1024*Real.exp 2*R⁻¹*(1+Q/H))+2048*Real.exp 1*(1/H^2) := by ring
        _ ≤ 12*((C+33792*Real.exp 1+2+2048*Real.exp 2)*S)+2048*Real.exp 1*S :=
          add_le_add (mul_le_mul_of_nonneg_left hbounds (by norm_num)) ht
        _ = _ := by ring
    simpa only [B,mul_assoc] using mul_le_mul_of_nonneg_left hi (show 0 ≤ 139968/(2*Real.pi) by positivity)
  have hs : S=(Real.exp (-2*M/5))^2+(Real.sqrt δ)^2+(W⁻¹)^2 := by
    dsimp [S]
    rw [Real.sq_sqrt hδ,inv_pow]
    have hx : (Real.exp (-2*M/5))^2=Real.exp (-4*M/5) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hx]
  calc
    _ ≤ Real.sqrt (B*S) := Real.sqrt_le_sqrt he
    _ ≤ (B+1)*(Real.exp (-2*M/5)+Real.sqrt δ+W⁻¹) := by
      rw [hs]
      exact major_arc_three_term_root (by dsimp [B]; positivity)
        (Real.exp_pos _).le (Real.sqrt_nonneg _) (inv_nonneg.mpr hW0.le)
    _ = _ := rfl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalShortMeanSharp
namespace OAI

/-! The literal typical L1 short mean with the refined off-center error.
The original pretentious distance cutoff and height are preserved. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory

theorem halasz_typical_short_mean_sharp_oai
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) →
      ∀ J : ℕ, 1 ≤ J →
      (∀ k ∈ ({N,2*N}:Finset ℕ),
        200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log k))) →
      ∀ X : ℕ, N ≤ X → X ≤ N^3 → ∀ H : ℕ, 4 ≤ H → H ≤ N → 2*Q ≤ (N:ℝ) →
      ∀ W : ℝ, 1 ≤ W → W^9 ≤ mrtBaseResolution P Q (1/100) →
        W^2 ≤ P → W ≤ (H:ℝ) → Q/(H:ℝ) ≤ W^7 →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u : ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) H 0 x‖)/((N:ℝ)*H) ≤
      K*(Real.exp (-2*M/5)+Real.sqrt
        (Real.log (Real.log N)/(Real.log N)^(1/80:ℝ))+W⁻¹) := by
  obtain ⟨C,hC,henergy⟩ := halasz_typical_short_energy_sharp hprime hhigh
  refine ⟨majorArcEnergyConstant C,major_arc_energy_constant_pos hC.le,?_⟩
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [henergy,hl,eventually_ge_atTop 1] with N henergy hl hN
  intro P Q hP hPQ hlP hlQ hbudget hres J hJ hbands X hNX hXN H hH hHN hsize
    W hW hWR hWP hWH hWQ F hF1 hFc hFb M hM hd
  have he := henergy P Q hP hPQ hlP hlQ hbudget hres J hJ hbands
    X hNX hXN H hH hHN hsize F hF1 hFc hFb M hM hd
  have hs := halasz_short_mean_square (mrtTypicalCoefficient (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F)
    (show 0 < N by omega) (show 0 < H by omega) 0
  have hmean := Real.le_sqrt_of_sq_le (hs.trans he)
  apply hmean.trans
  exact major_arc_short_energy_root hC.le hW hWR hWP hWH hWQ
    (div_nonneg (Real.log_nonneg hl) (Real.rpow_nonneg (by linarith) _))

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_typical_short_mean_sharp_oai := @OAI.TwoPointCorrelations.halasz_typical_short_mean_sharp_oai
